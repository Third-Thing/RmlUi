#include "RmlUi_Platform_Wayland.h"
#include <RmlUi/Core/Log.h>
#include <RmlUi/Core/StringUtilities.h>
#include <cerrno>
#include <cstring>
#include <fcntl.h>
#include <linux/input-event-codes.h>
#include <signal.h>
#include <unistd.h>

static constexpr const char* MimeTextUtf8 = "text/plain;charset=utf-8";
static constexpr const char* MimeTextPlain = "text/plain";
static constexpr size_t MaxClipboardTextBytes = 16 * 1024 * 1024;

static int GetTextMimeTypeRank(const char* mime_type)
{
	if (!mime_type)
		return 0;

	const Rml::String mime_type_lower = Rml::StringUtilities::ToLower(mime_type);
	if (mime_type_lower == MimeTextUtf8)
		return 5;
	if (mime_type_lower == MimeTextPlain)
		return 4;
	if (Rml::StringUtilities::StartsWith(mime_type_lower, "text/plain;"))
		return 3;
	if (mime_type_lower == "utf8_string" || mime_type_lower == "text" || mime_type_lower == "string")
		return 2;
	if (Rml::StringUtilities::StartsWith(mime_type_lower, "text/"))
		return 1;

	return 0;
}

static bool IsTextMimeType(const char* mime_type)
{
	return GetTextMimeTypeRank(mime_type) > 0;
}

static void CloseFd(int& fd)
{
	if (fd >= 0)
	{
		close(fd);
		fd = -1;
	}
}

static void SetCloseOnExec(int fd)
{
	const int flags = fcntl(fd, F_GETFD);
	if (flags >= 0)
		fcntl(fd, F_SETFD, flags | FD_CLOEXEC);
}

static void SetNonBlocking(int fd)
{
	const int flags = fcntl(fd, F_GETFL);
	if (flags >= 0)
		fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}

static void WriteAll(int fd, const Rml::String& text)
{
	sigset_t sigpipe_set;
	sigset_t old_signal_mask;
	sigset_t pending_signals;
	sigemptyset(&sigpipe_set);
	sigaddset(&sigpipe_set, SIGPIPE);
	const bool had_pending_sigpipe = (sigpending(&pending_signals) == 0 && sigismember(&pending_signals, SIGPIPE) == 1);
	const bool blocked_sigpipe = (sigprocmask(SIG_BLOCK, &sigpipe_set, &old_signal_mask) == 0);

	const char* data = text.data();
	size_t remaining = text.size();

	while (remaining > 0)
	{
		const ssize_t bytes_written = write(fd, data, remaining);
		if (bytes_written > 0)
		{
			data += bytes_written;
			remaining -= size_t(bytes_written);
		}
		else if (bytes_written < 0 && errno == EINTR)
		{
			continue;
		}
		else
		{
			break;
		}
	}

	if (blocked_sigpipe)
	{
		if (!had_pending_sigpipe)
		{
			timespec timeout {};
			sigtimedwait(&sigpipe_set, nullptr, &timeout);
		}
		sigprocmask(SIG_SETMASK, &old_signal_mask, nullptr);
	}
}

struct ClipboardOffer_Wayland {
	explicit ClipboardOffer_Wayland(wl_data_offer* offer) : offer(offer) {}
	~ClipboardOffer_Wayland()
	{
		if (offer)
			wl_data_offer_destroy(offer);
	}

	wl_data_offer* offer = nullptr;
	Rml::String text_mime_type;
	int text_mime_rank = 0;

	void OfferMimeType(const char* mime_type)
	{
		const int mime_rank = GetTextMimeTypeRank(mime_type);
		if (mime_rank > text_mime_rank)
		{
			text_mime_type = mime_type;
			text_mime_rank = mime_rank;
		}
	}

	const char* GetPreferredMimeType() const
	{
		return text_mime_type.empty() ? nullptr : text_mime_type.c_str();
	}
};

class ClipboardManager_Wayland {
public:
	ClipboardManager_Wayland(wl_display* display, wl_data_device_manager* data_device_manager) : display(display), data_device_manager(data_device_manager) {}
	~ClipboardManager_Wayland()
	{
		CancelRead();
		pending_read_callback = nullptr;
		current_offer = nullptr;
		offers.clear();
		DestroyActiveSource();
		DestroyDataDevice();
	}

	void SetSeat(wl_seat* seat)
	{
		DestroyDataDevice();

		if (!data_device_manager || !seat)
			return;

		data_device = wl_data_device_manager_get_data_device(data_device_manager, seat);
		if (!data_device)
			return;

		wl_data_device_add_listener(data_device, &data_device_listener, this);
	}

	void SetSeatSerial(uint32_t serial)
	{
		selection_serial = serial;
		has_selection_serial = true;
	}

	void SetText(const Rml::String& text)
	{
		owned_text = text;
		owns_selection = true;

		if (!data_device_manager || !data_device || !has_selection_serial)
			return;

		DestroyActiveSource();

		wl_data_source* source = wl_data_device_manager_create_data_source(data_device_manager);
		if (!source)
			return;

		active_source = source;
		wl_data_source_add_listener(active_source, &data_source_listener, this);
		wl_data_source_offer(active_source, MimeTextUtf8);
		wl_data_source_offer(active_source, MimeTextPlain);
		wl_data_device_set_selection(data_device, active_source, selection_serial);
		wl_display_flush(display);
	}

	void RequestText(Rml::Function<void(Rml::String)> callback)
	{
		if (owns_selection)
		{
			if (callback)
				callback(owned_text);
			return;
		}

		CancelRead();
		pending_read_callback = nullptr;

		if (!current_offer)
		{
			if (callback)
				callback(Rml::String());
			return;
		}

		if (!current_offer->GetPreferredMimeType())
		{
			pending_read_callback = std::move(callback);
			return;
		}

		StartRead(std::move(callback));
	}

	void StartRead(Rml::Function<void(Rml::String)> callback)
	{
		const char* mime_type = current_offer ? current_offer->GetPreferredMimeType() : nullptr;
		if (!mime_type)
		{
			if (callback)
				callback(Rml::String());
			return;
		}

		int pipe_fd[2] = {-1, -1};
		if (pipe(pipe_fd) != 0)
		{
			if (callback)
				callback(Rml::String());
			return;
		}

		SetCloseOnExec(pipe_fd[0]);
		SetCloseOnExec(pipe_fd[1]);
		SetNonBlocking(pipe_fd[0]);

		read_fd = pipe_fd[0];
		read_callback = std::move(callback);
		read_text.clear();

		wl_data_offer_accept(current_offer->offer, selection_serial, mime_type);
		wl_data_offer_receive(current_offer->offer, mime_type, pipe_fd[1]);
		CloseFd(pipe_fd[1]);
		wl_display_flush(display);

		ProcessRead();
	}

	void GetText(Rml::String& text) const
	{
		if (owns_selection)
			text = owned_text;
		else
			text.clear();
	}

	int GetReadFd() const
	{
		return read_fd;
	}

	void ProcessRead()
	{
		if (read_fd < 0)
			return;

		char buffer[4096];
		while (true)
		{
			const ssize_t bytes_read = read(read_fd, buffer, sizeof(buffer));
			if (bytes_read > 0)
			{
				if (read_text.size() + size_t(bytes_read) > MaxClipboardTextBytes)
				{
					FinishRead(Rml::String());
					return;
				}

				read_text.append(buffer, size_t(bytes_read));
			}
			else if (bytes_read == 0)
			{
				FinishRead(std::move(read_text));
				return;
			}
			else if (errno == EINTR)
			{
				continue;
			}
			else if (errno == EAGAIN || errno == EWOULDBLOCK)
			{
				return;
			}
			else
			{
				FinishRead(Rml::String());
				return;
			}
		}
	}

private:
	void DestroyDataDevice()
	{
		CancelRead();
		pending_read_callback = nullptr;
		current_offer = nullptr;
		offers.clear();

		if (data_device)
		{
			if (wl_data_device_get_version(data_device) >= WL_DATA_DEVICE_RELEASE_SINCE_VERSION)
				wl_data_device_release(data_device);
			else
				wl_data_device_destroy(data_device);
			data_device = nullptr;
		}
	}

	void DestroyActiveSource()
	{
		if (active_source)
		{
			wl_data_source_destroy(active_source);
			active_source = nullptr;
		}
	}

	void CancelRead()
	{
		CloseFd(read_fd);
		read_text.clear();
		read_callback = nullptr;
	}

	void FinishRead(Rml::String text)
	{
		CloseFd(read_fd);
		read_text.clear();

		Rml::Function<void(Rml::String)> callback = std::move(read_callback);
		read_callback = nullptr;
		if (callback)
			callback(std::move(text));
	}

	void SetPendingOffer(wl_data_offer* offer)
	{
		auto offer_data = Rml::MakeUnique<ClipboardOffer_Wayland>(offer);
		wl_data_offer_add_listener(offer, &data_offer_listener, this);
		offers[offer] = std::move(offer_data);
	}

	void SetSelectionOffer(wl_data_offer* offer)
	{
		if (read_fd >= 0)
			FinishRead(Rml::String());
		if (pending_read_callback)
		{
			Rml::Function<void(Rml::String)> callback = std::move(pending_read_callback);
			pending_read_callback = nullptr;
			callback(Rml::String());
		}

		for (auto it = offers.begin(); it != offers.end();)
		{
			if (it->first != offer)
				it = offers.erase(it);
			else
				++it;
		}

		current_offer = nullptr;

		if (!offer)
			return;

		auto it = offers.find(offer);
		if (it != offers.end())
			current_offer = it->second.get();
	}

	static void DataOfferHandleOffer(void* data, wl_data_offer* offer, const char* mime_type)
	{
		auto* manager = static_cast<ClipboardManager_Wayland*>(data);
		auto it = manager->offers.find(offer);
		if (it == manager->offers.end() || !mime_type)
			return;

		ClipboardOffer_Wayland* offer_data = it->second.get();
		const bool had_text_mime_type = (offer_data->GetPreferredMimeType() != nullptr);
		offer_data->OfferMimeType(mime_type);

		if (!had_text_mime_type && offer_data == manager->current_offer && manager->pending_read_callback)
		{
			Rml::Function<void(Rml::String)> callback = std::move(manager->pending_read_callback);
			manager->pending_read_callback = nullptr;
			manager->StartRead(std::move(callback));
		}
	}

	static void DataOfferHandleSourceActions(void*, wl_data_offer*, uint32_t) {}
	static void DataOfferHandleAction(void*, wl_data_offer*, uint32_t) {}

	static void DataDeviceHandleDataOffer(void* data, wl_data_device*, wl_data_offer* offer)
	{
		static_cast<ClipboardManager_Wayland*>(data)->SetPendingOffer(offer);
	}

	static void DataDeviceHandleEnter(void* data, wl_data_device*, uint32_t, wl_surface*, wl_fixed_t, wl_fixed_t, wl_data_offer* offer)
	{
		auto* manager = static_cast<ClipboardManager_Wayland*>(data);
		manager->offers.erase(offer);
	}

	static void DataDeviceHandleLeave(void*, wl_data_device*) {}
	static void DataDeviceHandleMotion(void*, wl_data_device*, uint32_t, wl_fixed_t, wl_fixed_t) {}
	static void DataDeviceHandleDrop(void*, wl_data_device*) {}

	static void DataDeviceHandleSelection(void* data, wl_data_device*, wl_data_offer* offer)
	{
		static_cast<ClipboardManager_Wayland*>(data)->SetSelectionOffer(offer);
	}

	static void DataSourceHandleTarget(void*, wl_data_source*, const char*) {}

	static void DataSourceHandleSend(void* data, wl_data_source*, const char* mime_type, int32_t fd)
	{
		auto* manager = static_cast<ClipboardManager_Wayland*>(data);
		if (IsTextMimeType(mime_type))
			WriteAll(fd, manager->owned_text);
		close(fd);
	}

	static void DataSourceHandleCancelled(void* data, wl_data_source* source)
	{
		auto* manager = static_cast<ClipboardManager_Wayland*>(data);
		if (manager->active_source == source)
		{
			manager->active_source = nullptr;
			wl_data_source_destroy(source);
			manager->owns_selection = false;
		}
	}

	static void DataSourceHandleDndDropPerformed(void*, wl_data_source*) {}
	static void DataSourceHandleDndFinished(void*, wl_data_source*) {}
	static void DataSourceHandleAction(void*, wl_data_source*, uint32_t) {}

	wl_display* display = nullptr;
	wl_data_device_manager* data_device_manager = nullptr;
	wl_data_device* data_device = nullptr;
	wl_data_source* active_source = nullptr;
	Rml::UnorderedMap<wl_data_offer*, Rml::UniquePtr<ClipboardOffer_Wayland>> offers;
	ClipboardOffer_Wayland* current_offer = nullptr;

	uint32_t selection_serial = 0;
	bool has_selection_serial = false;
	bool owns_selection = false;
	Rml::String owned_text;

	int read_fd = -1;
	Rml::String read_text;
	Rml::Function<void(Rml::String)> read_callback;
	Rml::Function<void(Rml::String)> pending_read_callback;

	static const wl_data_offer_listener data_offer_listener;
	static const wl_data_device_listener data_device_listener;
	static const wl_data_source_listener data_source_listener;
};

const wl_data_offer_listener ClipboardManager_Wayland::data_offer_listener = {
	ClipboardManager_Wayland::DataOfferHandleOffer,
	ClipboardManager_Wayland::DataOfferHandleSourceActions,
	ClipboardManager_Wayland::DataOfferHandleAction,
};

const wl_data_device_listener ClipboardManager_Wayland::data_device_listener = {
	ClipboardManager_Wayland::DataDeviceHandleDataOffer,
	ClipboardManager_Wayland::DataDeviceHandleEnter,
	ClipboardManager_Wayland::DataDeviceHandleLeave,
	ClipboardManager_Wayland::DataDeviceHandleMotion,
	ClipboardManager_Wayland::DataDeviceHandleDrop,
	ClipboardManager_Wayland::DataDeviceHandleSelection,
};

const wl_data_source_listener ClipboardManager_Wayland::data_source_listener = {
	ClipboardManager_Wayland::DataSourceHandleTarget,
	ClipboardManager_Wayland::DataSourceHandleSend,
	ClipboardManager_Wayland::DataSourceHandleCancelled,
	ClipboardManager_Wayland::DataSourceHandleDndDropPerformed,
	ClipboardManager_Wayland::DataSourceHandleDndFinished,
	ClipboardManager_Wayland::DataSourceHandleAction,
};

SystemInterface_Wayland::SystemInterface_Wayland(wl_display* display, wl_shm* shm, wl_data_device_manager* data_device_manager) :
	display(display), shm(shm), clipboard_manager(Rml::MakeUnique<ClipboardManager_Wayland>(display, data_device_manager))
{
	gettimeofday(&start_time, nullptr);
}

SystemInterface_Wayland::~SystemInterface_Wayland()
{
	if (cursor_theme)
		wl_cursor_theme_destroy(cursor_theme);
}

void SystemInterface_Wayland::SetPointer(wl_pointer* in_pointer)
{
	pointer = in_pointer;
}

void SystemInterface_Wayland::SetSeat(wl_seat* seat)
{
	clipboard_manager->SetSeat(seat);
}

void SystemInterface_Wayland::SetCursorSurface(wl_surface* surface)
{
	cursor_surface = surface;
}

void SystemInterface_Wayland::SetPointerSerial(uint32_t serial)
{
	pointer_serial = serial;
	has_pointer_serial = true;
}

void SystemInterface_Wayland::ClearPointerSerial()
{
	has_pointer_serial = false;
}

void SystemInterface_Wayland::SetSeatSerial(uint32_t serial)
{
	clipboard_manager->SetSeatSerial(serial);
}

int SystemInterface_Wayland::GetClipboardReadFd() const
{
	return clipboard_manager->GetReadFd();
}

void SystemInterface_Wayland::ProcessClipboardRead()
{
	clipboard_manager->ProcessRead();
}

double SystemInterface_Wayland::GetElapsedTime()
{
	timeval now {};
	gettimeofday(&now, nullptr);

	const double sec = now.tv_sec - start_time.tv_sec;
	const double usec = now.tv_usec - start_time.tv_usec;
	return sec + (usec / 1000000.0);
}

void SystemInterface_Wayland::LoadCursorTheme()
{
	if (!cursor_theme && shm)
		cursor_theme = wl_cursor_theme_load(nullptr, 24, shm);
}

void SystemInterface_Wayland::ApplyCursor(const char* cursor_name)
{
	if (!pointer || !cursor_surface || !has_pointer_serial)
		return;

	LoadCursorTheme();
	if (!cursor_theme)
		return;

	wl_cursor* cursor = wl_cursor_theme_get_cursor(cursor_theme, cursor_name);
	if (!cursor || cursor->image_count == 0)
	{
		cursor = wl_cursor_theme_get_cursor(cursor_theme, "default");
		if (!cursor || cursor->image_count == 0)
			return;
	}

	wl_cursor_image* image = cursor->images[0];
	wl_buffer* buffer = wl_cursor_image_get_buffer(image);
	if (!buffer)
		return;

	wl_pointer_set_cursor(pointer, pointer_serial, cursor_surface, int32_t(image->hotspot_x), int32_t(image->hotspot_y));
	wl_surface_attach(cursor_surface, buffer, 0, 0);
	wl_surface_damage(cursor_surface, 0, 0, int32_t(image->width), int32_t(image->height));
	wl_surface_commit(cursor_surface);
	wl_display_flush(display);
}

void SystemInterface_Wayland::SetMouseCursor(const Rml::String& cursor_name)
{
	if (cursor_name.empty() || cursor_name == "arrow")
		ApplyCursor("default");
	else if (cursor_name == "move" || Rml::StringUtilities::StartsWith(cursor_name, "rmlui-scroll"))
		ApplyCursor("move");
	else if (cursor_name == "pointer")
		ApplyCursor("pointer");
	else if (cursor_name == "resize")
		ApplyCursor("se-resize");
	else if (cursor_name == "cross")
		ApplyCursor("crosshair");
	else if (cursor_name == "text")
		ApplyCursor("text");
	else if (cursor_name == "unavailable")
		ApplyCursor("not-allowed");
}

void SystemInterface_Wayland::SetClipboardText(const Rml::String& text)
{
	clipboard_manager->SetText(text);
}

void SystemInterface_Wayland::RequestClipboardText(Rml::Function<void(Rml::String)> callback)
{
	clipboard_manager->RequestText(std::move(callback));
}

void SystemInterface_Wayland::GetClipboardText(Rml::String& text)
{
	clipboard_manager->GetText(text);
}

namespace RmlWayland {

KeyboardState::KeyboardState()
{
	context = xkb_context_new(XKB_CONTEXT_NO_FLAGS);
}

KeyboardState::~KeyboardState()
{
	if (state)
		xkb_state_unref(state);
	if (keymap)
		xkb_keymap_unref(keymap);
	if (context)
		xkb_context_unref(context);
}

void KeyboardState::SetKeymapFromString(const char* keymap_string)
{
	if (!context || !keymap_string)
		return;

	xkb_keymap* new_keymap = xkb_keymap_new_from_string(context, keymap_string, XKB_KEYMAP_FORMAT_TEXT_V1, XKB_KEYMAP_COMPILE_NO_FLAGS);
	if (!new_keymap)
	{
		Rml::Log::Message(Rml::Log::LT_WARNING, "Failed to load Wayland keyboard map.");
		return;
	}

	xkb_state* new_state = xkb_state_new(new_keymap);
	if (!new_state)
	{
		xkb_keymap_unref(new_keymap);
		Rml::Log::Message(Rml::Log::LT_WARNING, "Failed to create Wayland keyboard state.");
		return;
	}

	if (state)
		xkb_state_unref(state);
	if (keymap)
		xkb_keymap_unref(keymap);

	keymap = new_keymap;
	state = new_state;
	modifiers = 0;
}

void KeyboardState::Reset()
{
	modifiers = 0;

	xkb_state* new_state = nullptr;
	if (keymap)
		new_state = xkb_state_new(keymap);

	if (state)
		xkb_state_unref(state);
	state = new_state;

	if (keymap && !state)
		Rml::Log::Message(Rml::Log::LT_WARNING, "Failed to reset Wayland keyboard state.");
}

void KeyboardState::UpdateModifiers(uint32_t depressed, uint32_t latched, uint32_t locked, uint32_t group)
{
	if (!state)
		return;

	xkb_state_update_mask(state, depressed, latched, locked, 0, 0, group);
	modifiers = ConvertKeyModifiers(state);
}

int ConvertKeyModifiers(xkb_state* state)
{
	int result = 0;
	if (!state)
		return result;

	if (xkb_state_mod_name_is_active(state, XKB_MOD_NAME_SHIFT, XKB_STATE_MODS_EFFECTIVE))
		result |= Rml::Input::KM_SHIFT;
	if (xkb_state_mod_name_is_active(state, XKB_MOD_NAME_CAPS, XKB_STATE_MODS_EFFECTIVE))
		result |= Rml::Input::KM_CAPSLOCK;
	if (xkb_state_mod_name_is_active(state, XKB_MOD_NAME_CTRL, XKB_STATE_MODS_EFFECTIVE))
		result |= Rml::Input::KM_CTRL;
	if (xkb_state_mod_name_is_active(state, XKB_MOD_NAME_ALT, XKB_STATE_MODS_EFFECTIVE))
		result |= Rml::Input::KM_ALT;
	if (xkb_state_mod_name_is_active(state, XKB_MOD_NAME_NUM, XKB_STATE_MODS_EFFECTIVE))
		result |= Rml::Input::KM_NUMLOCK;

	return result;
}

int ConvertMouseButton(uint32_t button)
{
	switch (button)
	{
	case BTN_LEFT: return 0;
	case BTN_RIGHT: return 1;
	case BTN_MIDDLE: return 2;
	default: return -1;
	}
}

Rml::Input::KeyIdentifier ConvertKeySym(xkb_keysym_t sym)
{
	// clang-format off
	switch (sym)
	{
	case XKB_KEY_BackSpace: return Rml::Input::KI_BACK;
	case XKB_KEY_Tab: return Rml::Input::KI_TAB;
	case XKB_KEY_Clear: return Rml::Input::KI_CLEAR;
	case XKB_KEY_Return: return Rml::Input::KI_RETURN;
	case XKB_KEY_Pause: return Rml::Input::KI_PAUSE;
	case XKB_KEY_Scroll_Lock: return Rml::Input::KI_SCROLL;
	case XKB_KEY_Escape: return Rml::Input::KI_ESCAPE;
	case XKB_KEY_Delete: return Rml::Input::KI_DELETE;
	case XKB_KEY_Home: return Rml::Input::KI_HOME;
	case XKB_KEY_Left: return Rml::Input::KI_LEFT;
	case XKB_KEY_Up: return Rml::Input::KI_UP;
	case XKB_KEY_Right: return Rml::Input::KI_RIGHT;
	case XKB_KEY_Down: return Rml::Input::KI_DOWN;
	case XKB_KEY_Page_Up: return Rml::Input::KI_PRIOR;
	case XKB_KEY_Page_Down: return Rml::Input::KI_NEXT;
	case XKB_KEY_End: return Rml::Input::KI_END;
	case XKB_KEY_Insert: return Rml::Input::KI_INSERT;
	case XKB_KEY_Num_Lock: return Rml::Input::KI_NUMLOCK;

	case XKB_KEY_KP_Space: return Rml::Input::KI_SPACE;
	case XKB_KEY_KP_Tab: return Rml::Input::KI_TAB;
	case XKB_KEY_KP_Enter: return Rml::Input::KI_NUMPADENTER;
	case XKB_KEY_KP_Home: return Rml::Input::KI_NUMPAD7;
	case XKB_KEY_KP_Left: return Rml::Input::KI_NUMPAD4;
	case XKB_KEY_KP_Up: return Rml::Input::KI_NUMPAD8;
	case XKB_KEY_KP_Right: return Rml::Input::KI_NUMPAD6;
	case XKB_KEY_KP_Down: return Rml::Input::KI_NUMPAD2;
	case XKB_KEY_KP_Page_Up: return Rml::Input::KI_NUMPAD9;
	case XKB_KEY_KP_Page_Down: return Rml::Input::KI_NUMPAD3;
	case XKB_KEY_KP_End: return Rml::Input::KI_NUMPAD1;
	case XKB_KEY_KP_Begin: return Rml::Input::KI_NUMPAD5;
	case XKB_KEY_KP_Insert: return Rml::Input::KI_NUMPAD0;
	case XKB_KEY_KP_Delete: return Rml::Input::KI_DECIMAL;
	case XKB_KEY_KP_Multiply: return Rml::Input::KI_MULTIPLY;
	case XKB_KEY_KP_Add: return Rml::Input::KI_ADD;
	case XKB_KEY_KP_Separator: return Rml::Input::KI_SEPARATOR;
	case XKB_KEY_KP_Subtract: return Rml::Input::KI_SUBTRACT;
	case XKB_KEY_KP_Decimal: return Rml::Input::KI_DECIMAL;
	case XKB_KEY_KP_Divide: return Rml::Input::KI_DIVIDE;

	case XKB_KEY_F1: return Rml::Input::KI_F1;
	case XKB_KEY_F2: return Rml::Input::KI_F2;
	case XKB_KEY_F3: return Rml::Input::KI_F3;
	case XKB_KEY_F4: return Rml::Input::KI_F4;
	case XKB_KEY_F5: return Rml::Input::KI_F5;
	case XKB_KEY_F6: return Rml::Input::KI_F6;
	case XKB_KEY_F7: return Rml::Input::KI_F7;
	case XKB_KEY_F8: return Rml::Input::KI_F8;
	case XKB_KEY_F9: return Rml::Input::KI_F9;
	case XKB_KEY_F10: return Rml::Input::KI_F10;
	case XKB_KEY_F11: return Rml::Input::KI_F11;
	case XKB_KEY_F12: return Rml::Input::KI_F12;
	case XKB_KEY_F13: return Rml::Input::KI_F13;
	case XKB_KEY_F14: return Rml::Input::KI_F14;
	case XKB_KEY_F15: return Rml::Input::KI_F15;
	case XKB_KEY_F16: return Rml::Input::KI_F16;
	case XKB_KEY_F17: return Rml::Input::KI_F17;
	case XKB_KEY_F18: return Rml::Input::KI_F18;
	case XKB_KEY_F19: return Rml::Input::KI_F19;
	case XKB_KEY_F20: return Rml::Input::KI_F20;
	case XKB_KEY_F21: return Rml::Input::KI_F21;
	case XKB_KEY_F22: return Rml::Input::KI_F22;
	case XKB_KEY_F23: return Rml::Input::KI_F23;
	case XKB_KEY_F24: return Rml::Input::KI_F24;

	case XKB_KEY_Shift_L: return Rml::Input::KI_LSHIFT;
	case XKB_KEY_Shift_R: return Rml::Input::KI_RSHIFT;
	case XKB_KEY_Control_L: return Rml::Input::KI_LCONTROL;
	case XKB_KEY_Control_R: return Rml::Input::KI_RCONTROL;
	case XKB_KEY_Caps_Lock: return Rml::Input::KI_CAPITAL;
	case XKB_KEY_Alt_L: return Rml::Input::KI_LMENU;
	case XKB_KEY_Alt_R: return Rml::Input::KI_RMENU;
	case XKB_KEY_Super_L: return Rml::Input::KI_LWIN;
	case XKB_KEY_Super_R: return Rml::Input::KI_RWIN;

	case XKB_KEY_space: return Rml::Input::KI_SPACE;
	case XKB_KEY_apostrophe: return Rml::Input::KI_OEM_7;
	case XKB_KEY_comma: return Rml::Input::KI_OEM_COMMA;
	case XKB_KEY_minus: return Rml::Input::KI_OEM_MINUS;
	case XKB_KEY_period: return Rml::Input::KI_OEM_PERIOD;
	case XKB_KEY_slash: return Rml::Input::KI_OEM_2;
	case XKB_KEY_0: return Rml::Input::KI_0;
	case XKB_KEY_1: return Rml::Input::KI_1;
	case XKB_KEY_2: return Rml::Input::KI_2;
	case XKB_KEY_3: return Rml::Input::KI_3;
	case XKB_KEY_4: return Rml::Input::KI_4;
	case XKB_KEY_5: return Rml::Input::KI_5;
	case XKB_KEY_6: return Rml::Input::KI_6;
	case XKB_KEY_7: return Rml::Input::KI_7;
	case XKB_KEY_8: return Rml::Input::KI_8;
	case XKB_KEY_9: return Rml::Input::KI_9;
	case XKB_KEY_semicolon: return Rml::Input::KI_OEM_1;
	case XKB_KEY_equal: return Rml::Input::KI_OEM_PLUS;
	case XKB_KEY_bracketleft: return Rml::Input::KI_OEM_4;
	case XKB_KEY_backslash: return Rml::Input::KI_OEM_5;
	case XKB_KEY_bracketright: return Rml::Input::KI_OEM_6;
	case XKB_KEY_grave: return Rml::Input::KI_OEM_3;
	case XKB_KEY_a: case XKB_KEY_A: return Rml::Input::KI_A;
	case XKB_KEY_b: case XKB_KEY_B: return Rml::Input::KI_B;
	case XKB_KEY_c: case XKB_KEY_C: return Rml::Input::KI_C;
	case XKB_KEY_d: case XKB_KEY_D: return Rml::Input::KI_D;
	case XKB_KEY_e: case XKB_KEY_E: return Rml::Input::KI_E;
	case XKB_KEY_f: case XKB_KEY_F: return Rml::Input::KI_F;
	case XKB_KEY_g: case XKB_KEY_G: return Rml::Input::KI_G;
	case XKB_KEY_h: case XKB_KEY_H: return Rml::Input::KI_H;
	case XKB_KEY_i: case XKB_KEY_I: return Rml::Input::KI_I;
	case XKB_KEY_j: case XKB_KEY_J: return Rml::Input::KI_J;
	case XKB_KEY_k: case XKB_KEY_K: return Rml::Input::KI_K;
	case XKB_KEY_l: case XKB_KEY_L: return Rml::Input::KI_L;
	case XKB_KEY_m: case XKB_KEY_M: return Rml::Input::KI_M;
	case XKB_KEY_n: case XKB_KEY_N: return Rml::Input::KI_N;
	case XKB_KEY_o: case XKB_KEY_O: return Rml::Input::KI_O;
	case XKB_KEY_p: case XKB_KEY_P: return Rml::Input::KI_P;
	case XKB_KEY_q: case XKB_KEY_Q: return Rml::Input::KI_Q;
	case XKB_KEY_r: case XKB_KEY_R: return Rml::Input::KI_R;
	case XKB_KEY_s: case XKB_KEY_S: return Rml::Input::KI_S;
	case XKB_KEY_t: case XKB_KEY_T: return Rml::Input::KI_T;
	case XKB_KEY_u: case XKB_KEY_U: return Rml::Input::KI_U;
	case XKB_KEY_v: case XKB_KEY_V: return Rml::Input::KI_V;
	case XKB_KEY_w: case XKB_KEY_W: return Rml::Input::KI_W;
	case XKB_KEY_x: case XKB_KEY_X: return Rml::Input::KI_X;
	case XKB_KEY_y: case XKB_KEY_Y: return Rml::Input::KI_Y;
	case XKB_KEY_z: case XKB_KEY_Z: return Rml::Input::KI_Z;
	default: break;
	}
	// clang-format on

	return Rml::Input::KI_UNKNOWN;
}

} // namespace RmlWayland
