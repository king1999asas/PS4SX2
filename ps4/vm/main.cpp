// SPDX-License-Identifier: GPL-3.0+
// (AI-assisted) Boot the full PCSX2 VM on PS4, bypassing the incremental probe methodology.
#include "Config.h"
#include "PhysicalDisc.h"
#include "VMManager.h"
#include "Host.h"
#include "MTGS.h"
#include "GS/GS.h"
#include "GS/Renderers/Vulkan/GSDeviceVK.h"
#include "GS/Renderers/Vulkan/VKShaderCache.h"
#include "common/Console.h"
#include "common/Threading.h"
#include "common/HostSys.h"
#include "common/Error.h"
#include "common/FileSystem.h"
#include "Memory.h"
#include "common/MemorySettingsInterface.h"
#include "common/Timer.h"
#include "ps2/BiosTools.h"
#include "R5900.h"
#include "R3000A.h"
#include "IPU/IPU.h"
#include "IPU/IPU_MultiISA.h"
#include "SIO/Pad/Pad.h"
#include "SIO/Pad/PadBase.h"
#include "SIO/Pad/PadDualshock2.h"
#include <sys/stat.h>
#include "CDVD/CDVD.h"
#include "ps4/core/VulkanVideoOut.h"
#include "ps4/core/ThreadCPUMetricsPS4.h"
#include "ps4/core/ThreadAffinityPS4.h"
#include "ps4/core/AudioStreamPS4.h"
#include "ps4/core/ProbeLoggerPS4.h"
#include "ps4/core/TelemetryPS4.h"
#include "ps4/core/IPUProfilePS4.h"
#include "ps4/core/EEEventProfilePS4.h"
#include "ps4/core/EEHotspotsPS4.h"
#include "ps4/core/GSProfilePS4.h"
#include "HostPollGate.h"
#include "GameMenu.h"
#include "SessionLogs.h"
#include "ps4/core/WorkerProfilePS4.h"

#include <orbis/Pad.h>
#include <orbis/Sysmodule.h>
#include <orbis/SystemService.h>
#include <orbis/UserService.h>
#include <orbis/VideoOut.h>
#include <orbis/libkernel.h>
#include <string>
#include <string_view>
#include <cstdio>
#include <cerrno>
#include <fcntl.h>
#include <unistd.h>
#include <atomic>
#include <algorithm>
#include <cctype>
#include <cmath>
#include <dirent.h>
#include <vector>
#include <mutex>
#include <condition_variable>
#include <cstring>
#include <ctime>
#include <pthread.h>

static int s_log = -1;
// pcsx2/CDVD/CDVDcommon.cpp: called with each 2048-byte sector the game reads.
extern void (*g_ps4_disc_read_hook)(u8* buffer, u32 lsn);

#if defined(PCSX2_PS4_VM_BOOT_JIT)
extern std::atomic<u32> g_orbis_rec_compiles, g_orbis_rec_discards, g_orbis_rec_page_resets, g_orbis_rec_full_resets;
extern bool g_ps4_vtlb_register_cache;
extern bool g_ps4_vtlb_bulk_register_cache;
extern bool g_ps4_skip_smc_checks;
extern bool g_ps4_bytecopy_fusion;
extern bool g_ps4_bytefill_fusion;
extern u64 g_ps4_bytefill_blocks, g_ps4_bytefill_runs, g_ps4_bytefill_bytes, g_ps4_bytefill_declined;
extern std::atomic<int> g_orbis_waitloop_ext;
extern u64 g_ps4_vtlb_cached_quad_reads, g_ps4_vtlb_cached_writes;
extern u64 g_ps4_multiblock_wait_blocks, g_ps4_multiblock_wait_runs, g_ps4_multiblock_wait_iterations;
extern u64 g_ps4_bytecopy_blocks, g_ps4_bytecopy_runs, g_ps4_bytecopy_bytes;
extern u64 g_ps4_bytecopy_short, g_ps4_bytecopy_deadline, g_ps4_bytecopy_mapping, g_ps4_bytecopy_state, g_ps4_bytecopy_scratch;
extern u32 g_ps4_bytecopy_last_source, g_ps4_bytecopy_last_destination;
#endif

void ProbeLog(const char* format, ...)
{
	char text[4096];
	va_list args;
	va_start(args, format);
	const int length = std::vsnprintf(text, sizeof(text), format, args);
	va_end(args);
	if (length <= 0)
		return;
	const auto bytes = std::min(static_cast<std::size_t>(length), sizeof(text) - 1);
	PS4ProbeLogger::Write(text, bytes);
}

static int MigrateLegacyLogs()
{
	static constexpr const char* names[] = {
		"PCSX2-vm-boot.log", "PCSX2-vm-stdout.log", "PCSX2-vm-stderr.log",
		"emulog.txt", "xmb-trace.log", "crash.log"};
	int migrated = 0;
	mkdir("/data/PS4SX2/logs", 0777);
	for (const char* name : names)
	{
		char old_path[128];
		char new_path[128];
		snprintf(old_path, sizeof(old_path), "/data/PS4SX2/%s", name);
		snprintf(new_path, sizeof(new_path), "/data/PS4SX2/logs/%s", name);
		if (access(old_path, F_OK) != 0)
			continue;
		if (access(new_path, F_OK) == 0)
			snprintf(new_path, sizeof(new_path), "/data/PS4SX2/logs/legacy-%s", name);
		if (rename(old_path, new_path) == 0)
		{
			migrated++;
			if (s_log >= 0)
				ProbeLog("Log migration: %s -> %s\n", old_path, new_path);
		}
	}
	return migrated;
}

static void ConsoleMessage(LOGLEVEL level, ConsoleColors, std::string_view message)
{
	// (AI-assisted) Preserve errors and lifecycle logs; omit successful shader plumbing.
	if (level > LOGLEVEL_WARNING &&
		(message.starts_with("PS4 shaderc:") || message.starts_with("PS4 shader cache:") ||
			message.starts_with("PS4 Vulkan shader module:")))
		return;
	ProbeLog("%.*s\n", static_cast<int>(message.size()), message.data());
}

// (AI-assisted) All control callbacks execute on the CPU thread, including interpreter polling.
extern void VMHostSetCPUThread();
extern void VMHostDrainCPUQueue();
extern u64 VMHostGetCPUQueueLockCount();
static int s_pad = -1;
static std::string s_selected_game;
static bool s_use_vulkan_selector = false;
static u32 s_previous_pad_buttons = 0;
static u32 s_previous_host_buttons = 0;
static u32 s_blocked_pad_buttons = 0;
static bool s_menu_chord_latched = false;
static bool s_game_menu_open = false;
static unsigned s_game_menu_selection = 0;
static unsigned s_game_upscale = 1;
static unsigned s_max_game_upscale = 1;
static unsigned s_game_aspect = 1;
static bool s_game_show_performance_overlay = true;
static u32 s_game_menu_direction = 0;
static double s_game_menu_next_repeat = 0.0;
static std::atomic<bool> s_return_to_main_menu{false};
static Common::Timer s_run_timer;
static double s_last_log = -5.0;
static double s_last_input = -1.0;
static double s_last_pause_log = -5.0;

// (fork) One file on the USB drive to review play sessions on a PC without FTP:
// /mnt/usbN/logs/PS4SX2-registro.txt. It starts with a short summary of the last
// game sessions (game, settings, speed, FPS and what held it back), so several
// setting combinations can be compared, and then holds the full log of the most
// recent session. It is rewritten every 30 s by a worker thread while a game runs
// and once more on exit (a crash or a forced close keeps the last copy, and its
// summary is kept on the next start). The old copies of the separate log files
// in that folder are deleted, so only this file remains. Menu-only sessions never
// touch the USB.
static bool s_game_session = false;
static double s_last_usb_copy = 0.0;

namespace SessionSummary
{
	constexpr const char* HistoryPath = "/data/PS4SX2/session-history.txt";
	constexpr const char* CurrentPath = "/data/PS4SX2/session-current.txt";
	constexpr const char* Separator = "------------------------------------------------------------\n";
	constexpr size_t MaxHistory = 10;

	struct Sample
	{
		float t, speed, fps, ee, gs, vu1, gpu;
	};
	static std::mutex s_mutex;
	static std::vector<Sample> s_samples;
	static std::vector<float> s_marks;
	static Common::Timer::Value s_start = 0;
	static std::string s_title, s_serial, s_date;
	static std::string s_settings = "Ajustes: no registrados\n";
	static bool s_active = false;

	static float Elapsed() // caller holds s_mutex
	{
		return s_start ? static_cast<float>(Common::Timer::ConvertValueToSeconds(Common::Timer::GetCurrentValue() - s_start)) : 0.0f;
	}

	static std::string ReadFile(const char* path)
	{
		std::string text;
		const int fd = open(path, O_RDONLY);
		if (fd < 0)
			return text;
		char buffer[4096];
		ssize_t n;
		while ((n = read(fd, buffer, sizeof(buffer))) > 0)
			text.append(buffer, static_cast<size_t>(n));
		close(fd);
		return text;
	}

	static void WriteFile(const char* path, const std::string& text)
	{
		const int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0666);
		if (fd < 0)
			return;
		if (!text.empty())
			(void)!write(fd, text.data(), text.size());
		close(fd);
	}

	// Keeps the last MaxHistory entries, each followed by Separator.
	static void AppendHistory(const std::string& entry)
	{
		if (entry.empty())
			return;
		const std::string history = ReadFile(HistoryPath);
		std::vector<std::string> entries;
		for (size_t begin = 0; begin < history.size();)
		{
			const size_t end = history.find(Separator, begin);
			if (end == std::string::npos)
				break;
			entries.push_back(history.substr(begin, end - begin));
			begin = end + std::strlen(Separator);
		}
		entries.push_back(entry);
		const size_t first = entries.size() > MaxHistory ? entries.size() - MaxHistory : 0;
		std::string text;
		for (size_t i = first; i < entries.size(); ++i)
			text += entries[i] + Separator;
		WriteFile(HistoryPath, text);
	}

	// A session that ended without going through the menu (PS button, crash) left
	// its last snapshot behind; keep it in the history.
	static void KeepLeftover()
	{
		const std::string leftover = ReadFile(CurrentPath);
		if (!leftover.empty())
			AppendHistory(leftover);
		unlink(CurrentPath);
	}

	static void Begin()
	{
		std::lock_guard lock(s_mutex);
		s_samples.clear();
		s_marks.clear();
		s_start = Common::Timer::GetCurrentValue();
		const time_t now = time(nullptr);
		struct tm local{};
		char date[32] = "";
		if (localtime_r(&now, &local))
			strftime(date, sizeof(date), "%d/%m/%Y %H:%M", &local);
		s_date = date;
		s_active = true;
	}

	static void RefreshGame()
	{
		std::string title = VMManager::GetTitle(true);
		std::string serial = VMManager::GetDiscSerial();
		std::lock_guard lock(s_mutex);
		if (!title.empty())
			s_title = std::move(title);
		if (!serial.empty())
			s_serial = std::move(serial);
	}

	static void Mark()
	{
		std::lock_guard lock(s_mutex);
		if (s_active && s_marks.size() < 64)
			s_marks.push_back(Elapsed());
	}

	static void Add(double speed, double fps, double ee, double gs, double vu1, double gpu)
	{
		std::lock_guard lock(s_mutex);
		if (!s_active || speed < 1.0 || s_samples.size() >= 8192)
			return; // paused, or more than 11 hours
		s_samples.push_back({Elapsed(), static_cast<float>(speed), static_cast<float>(fps), static_cast<float>(ee),
			static_cast<float>(gs), static_cast<float>(vu1), static_cast<float>(gpu)});
	}

	static void SetSettings(int ee_rate, int ee_skip, bool fast_cdvd, bool fast_boot, bool audio, int download_mode,
		bool min_blend, bool fast_math, const std::vector<std::string>& patches, const std::vector<std::string>& cheats)
	{
		const auto marker = [](const char* name) {
			return access((std::string("/data/PS4SX2/") + name).c_str(), F_OK) == 0;
		};
		const bool fast_jit = marker("vm-skip-smc");
		const unsigned readback = download_mode == static_cast<int>(GSHardwareDownloadMode::Disabled) ? 2u :
		                          download_mode == static_cast<int>(GSHardwareDownloadMode::Unsynchronized) ? 1u : 0u;
		// Same rule as the launcher's "Perfil de rendimiento".
		const unsigned values[7] = {marker("vm-ee-cycle-normal") ? 0u : marker("vm-ee-cycle-minimum") ? 3u :
		                            marker("vm-ee-cycle-underclock") ? 2u : 1u,
			static_cast<unsigned>(ee_skip), fast_cdvd ? 1u : 0u, fast_jit ? 1u : 0u, readback, min_blend ? 1u : 0u,
			fast_math ? 1u : 0u};
		static constexpr unsigned profiles[3][7] = {{0, 0, 0, 0, 0, 0, 0}, {1, 0, 0, 0, 0, 0, 0}, {2, 1, 0, 0, 0, 0, 0}};
		static constexpr const char* profile_names[4] = {"Compatible", "Recomendado", "Máximo rendimiento", "Personalizado"};
		unsigned profile = 3;
		for (unsigned p = 0; p < 3 && profile == 3; ++p)
			profile = std::equal(values, values + 7, profiles[p]) ? p : 3;
		const char* ee = ee_rate == 0 ? "100%" : ee_rate == -1 ? "75%" : ee_rate == -2 ? "60%" : ee_rate == -3 ? "50%" : "?";
		static constexpr const char* readback_names[3] = {"precisas", "sin sincronizar", "desactivadas"};
		const auto join = [](const std::vector<std::string>& list) {
			std::string text;
			for (const std::string& item : list)
				text += (text.empty() ? "" : ", ") + item;
			return text.empty() ? std::string("ninguno") : text;
		};
		char line[512];
		std::snprintf(line, sizeof(line),
			"Ajustes: perfil %s · CPU EE %s · saltar ciclos %s · carga rápida %s · JIT rápido %s · lecturas GPU %s · "
			"mezcla %s · matemáticas %s · sonido %s · intro BIOS %s\n",
			profile_names[profile], ee, ee_skip == 0 ? "no" : ee_skip == 1 ? "nivel 1" : ee_skip == 2 ? "nivel 2" : "nivel 3",
			fast_cdvd ? "sí" : "no", fast_jit ? "sí" : "no", readback_names[readback], min_blend ? "mínima" : "básica",
			fast_math ? "rápida" : "normal", audio ? "sí" : "no", fast_boot ? "saltar" : "mostrar");
		std::string text = line;
		text += "Parches: " + join(patches) + " · Trucos: " + join(cheats) + "\n";
		std::lock_guard lock(s_mutex);
		s_settings = std::move(text);
	}

	static std::string Build(const char* status) // caller holds s_mutex
	{
		std::string out;
		char line[640];
		const int seconds = static_cast<int>(Elapsed());
		std::snprintf(line, sizeof(line), "Partida: %s (%s) · %s · %d min %02d s · %s\n",
			s_title.empty() ? "juego desconocido" : s_title.c_str(), s_serial.empty() ? "?" : s_serial.c_str(),
			s_date.c_str(), seconds / 60, seconds % 60, status);
		out += line;
		out += s_settings;
		if (s_samples.empty())
			out += "Rendimiento: sin datos todavía\n";
		else
		{
			double speed = 0, fps = 0, ee = 0, gs = 0, vu1 = 0, gpu = 0;
			float min_speed = 1000.0f;
			size_t full = 0, slow = 0, limits[3] = {0, 0, 0};
			for (const Sample& s : s_samples)
			{
				speed += s.speed;
				fps += s.fps;
				ee += s.ee;
				gs += s.gs;
				vu1 += s.vu1;
				gpu += s.gpu;
				min_speed = std::min(min_speed, s.speed);
				full += s.speed >= 97.0f;
				if (s.speed < 95.0f)
				{
					++slow;
					const float busiest = std::max({s.ee, s.gs, s.vu1});
					if (busiest >= 85.0f)
						++limits[busiest == s.ee ? 0 : busiest == s.gs ? 1 : 2];
				}
			}
			const double n = static_cast<double>(s_samples.size());
			std::snprintf(line, sizeof(line),
				"Resultado: velocidad media %.0f%% (mínima %.0f%%, a velocidad completa el %.0f%% del tiempo) · FPS medios %.0f\n"
				"Uso medio: procesador EE %.0f%% · gráficos GS %.0f%% · VU1 %.0f%% · GPU %.0f%%\n",
				speed / n, static_cast<double>(min_speed), 100.0 * full / n, fps / n, ee / n, gs / n, vu1 / n, gpu / n);
			out += line;
			if (slow == 0)
				out += "Freno: ninguno, no baja del 95%\n";
			else
			{
				static constexpr const char* limit_names[3] = {"procesador (EE)", "gráficos (GS)", "gráficos (VU1)"};
				const size_t worst = static_cast<size_t>(std::max_element(limits, limits + 3) - limits);
				if (limits[worst] == 0)
					std::snprintf(line, sizeof(line), "Freno cuando va lento (%.0f%% del tiempo): ningún hilo al límite\n", 100.0 * slow / n);
				else
					std::snprintf(line, sizeof(line), "Freno cuando va lento (%.0f%% del tiempo): %s, en el %.0f%% de esos momentos\n",
						100.0 * slow / n, limit_names[worst], 100.0 * limits[worst] / slow);
				out += line;
			}
			// Speed and FPS per minute (per few minutes in long sessions), to tell menus,
			// videos and gameplay apart.
			const int step = std::max(1, (seconds + 40 * 60 - 1) / (40 * 60));
			std::snprintf(line, sizeof(line), "Cada %d min (minuto: velocidad%%/FPS):", step);
			out += line;
			const int buckets = s_samples.back().t / (60.0f * step) + 1;
			size_t index = 0;
			for (int bucket = 0; bucket < buckets; ++bucket)
			{
				double bucket_speed = 0, bucket_fps = 0;
				size_t count = 0;
				for (; index < s_samples.size() && s_samples[index].t < (bucket + 1) * 60.0f * step; ++index, ++count)
				{
					bucket_speed += s_samples[index].speed;
					bucket_fps += s_samples[index].fps;
				}
				if (count == 0)
					continue;
				std::snprintf(line, sizeof(line), " %d:%.0f/%.0f", bucket * step + 1, bucket_speed / count, bucket_fps / count);
				out += line;
			}
			out += "\n";
		}
		if (!s_marks.empty())
		{
			out += "Menú L3+R3 abierto en (min:seg):";
			for (const float mark : s_marks)
			{
				std::snprintf(line, sizeof(line), " %d:%02d", static_cast<int>(mark) / 60, static_cast<int>(mark) % 60);
				out += line;
			}
			out += "\n";
		}
		return out;
	}
} // namespace SessionSummary

void PS4SessionStatsAdd(double speed, double fps, double ee, double gs, double vu1, double gpu)
{
	SessionSummary::Add(speed, fps, ee, gs, vu1, gpu);
}

namespace UsbLog
{
	constexpr const char* FileName = "PS4SX2-registro.txt";
	constexpr const char* SourcePath = "/data/PS4SX2/logs/PCSX2-vm-boot.log";
	static std::mutex s_copy_mutex; // held while the USB file is written
	static std::mutex s_request_mutex;
	static std::condition_variable s_request_cv;
	static bool s_requested = false;
	static std::string s_requested_entry, s_requested_leftover;
	static std::atomic<bool> s_closing{false};
	static bool s_thread_tried = false;
	static int s_thread_result = -1;
	static bool s_cleaned = false;
	static int s_last_state = 0;
	static char s_buffer[64 * 1024]; // used only under s_copy_mutex

	// First writable /mnt/usbN/logs; otherwise empty, with what was found in why.
	static std::string FindTargetDir(std::string& why)
	{
		for (int i = 0; i < 8; ++i)
		{
			char root[32];
			std::snprintf(root, sizeof(root), "/mnt/usb%d", i);
			struct stat st{};
			if (stat(root, &st) != 0 || !S_ISDIR(st.st_mode))
			{
				if (i == 0 || errno != ENOENT)
					why += std::string(" ") + root + " errno=" + std::to_string(errno);
				continue;
			}
			const std::string dir = std::string(root) + "/logs";
			mkdir(dir.c_str(), 0777);
			if (stat(dir.c_str(), &st) == 0 && S_ISDIR(st.st_mode) && access(dir.c_str(), W_OK) == 0)
				return dir;
			why += " " + dir + " errno=" + std::to_string(errno);
		}
		return {};
	}

	static void RemoveOldCopies(const std::string& dir)
	{
		static constexpr const char* files[] = {"PCSX2-vm-boot.log", "PCSX2-vm-stdout.log", "PCSX2-vm-stderr.log",
			"emulog.txt", "session-platform.txt", "xmb-trace.log", "legacy-xmb-trace.log"};
		for (const char* sub : {"", "/last-game-PS2", "/last-game-PS1", "/previous-menu"})
		{
			const std::string folder = dir + sub;
			for (const char* file : files)
				unlink((folder + "/" + file).c_str());
			if (*sub)
				rmdir(folder.c_str()); // only succeeds if nothing else is left in it
		}
	}

	// Summary of the last sessions (and of the current one, if given), then the
	// full log. Caller holds s_copy_mutex. Returns 1 on success, or <0 on failure.
	static int CopyNow(const std::string& current_entry, std::string& why)
	{
		const std::string dir = FindTargetDir(why);
		if (dir.empty())
			return -1;
		const int in = open(SourcePath, O_RDONLY);
		if (in < 0)
		{
			why = " " + std::string(SourcePath) + " errno=" + std::to_string(errno);
			return -2;
		}
		const std::string target = dir + "/" + FileName;
		const int out = open(target.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0666);
		if (out < 0)
		{
			why = " " + target + " errno=" + std::to_string(errno);
			close(in);
			return -3;
		}
		std::string header = "\xEF\xBB\xBFPS4SX2 · registro para revisar en el PC\n\n"
		                     "RESUMEN DE LAS ÚLTIMAS PARTIDAS (la más reciente al final)\n";
		header += SessionSummary::Separator;
		header += SessionSummary::ReadFile(SessionSummary::HistoryPath);
		if (!current_entry.empty())
			header += current_entry + SessionSummary::Separator;
		header += "\nREGISTRO COMPLETO DE LA PARTIDA MÁS RECIENTE\n";
		header += SessionSummary::Separator;
		int result = write(out, header.data(), header.size()) == static_cast<ssize_t>(header.size()) ? 1 : -4;
		ssize_t n;
		while (result > 0 && (n = read(in, s_buffer, sizeof(s_buffer))) > 0)
		{
			if (write(out, s_buffer, static_cast<size_t>(n)) != n)
				result = -4;
		}
		if (result < 0)
			why = " " + target + " write errno=" + std::to_string(errno);
		close(in);
		fsync(out);
		close(out);
		if (!s_cleaned)
		{
			RemoveOldCopies(dir);
			s_cleaned = true;
		}
		if (result > 0)
			why = target;
		return result;
	}

	// Logs the outcome when it changes (first copy, USB plugged or removed).
	static void Report(int state, const std::string& why)
	{
		if (state == s_last_state)
			return;
		s_last_state = state;
		if (state > 0)
			ProbeLog("USB log: summary and log copied to %s every 30 s\n", why.c_str());
		else if (state == -1)
			ProbeLog("USB log: no writable USB drive found (/mnt/usb0-7):%s\n", why.c_str());
		else
			ProbeLog("USB log: copy failed (%d):%s\n", state, why.c_str());
	}

	static void* Worker(void*)
	{
		for (;;)
		{
			std::string entry, leftover;
			{
				std::unique_lock lock(s_request_mutex);
				s_request_cv.wait(lock, [] { return s_requested; });
				s_requested = false;
				entry.swap(s_requested_entry);
				leftover.swap(s_requested_leftover);
			}
			std::lock_guard copy_lock(s_copy_mutex);
			if (s_closing.load(std::memory_order_acquire))
				continue;
			SessionSummary::WriteFile(SessionSummary::CurrentPath, leftover);
			std::string why;
			Report(CopyNow(entry, why), why);
		}
		return nullptr;
	}

	// From the EE thread: snapshot the current session and copy it in the background.
	static void Request()
	{
		std::string entry, leftover;
		{
			std::lock_guard lock(SessionSummary::s_mutex);
			entry = SessionSummary::Build("en curso");
			leftover = SessionSummary::Build("cerrada sin salir desde el menú (botón PS o cuelgue)");
		}
		if (!s_thread_tried)
		{
			s_thread_tried = true;
			pthread_attr_t attr;
			s_thread_result = pthread_attr_init(&attr);
			if (s_thread_result == 0)
			{
				s_thread_result = pthread_attr_setstacksize(&attr, 256 * 1024);
				pthread_t thread;
				if (s_thread_result == 0)
					s_thread_result = pthread_create(&thread, &attr, Worker, nullptr);
				pthread_attr_destroy(&attr);
			}
			if (s_thread_result != 0)
				ProbeLog("USB log: copy thread failed to start (error %d); the USB copy is made on exit only\n", s_thread_result);
		}
		if (s_thread_result != 0)
		{
			SessionSummary::WriteFile(SessionSummary::CurrentPath, leftover);
			return;
		}
		{
			std::lock_guard lock(s_request_mutex);
			s_requested_entry = std::move(entry);
			s_requested_leftover = std::move(leftover);
			s_requested = true;
		}
		s_request_cv.notify_one();
	}

	// On exit, after the log file is complete and closed: the finished session joins
	// the history and the USB file is written one last time.
	static void Final()
	{
		std::string entry;
		{
			std::lock_guard lock(SessionSummary::s_mutex);
			entry = SessionSummary::Build("cerrada desde el menú");
		}
		s_closing.store(true, std::memory_order_release);
		bool locked = false;
		for (int waited = 0; waited < 3000 && !(locked = s_copy_mutex.try_lock()); waited += 20)
			usleep(20 * 1000);
		SessionSummary::AppendHistory(entry);
		unlink(SessionSummary::CurrentPath);
		if (!locked)
			return; // a USB write is stuck; the history is kept for the next copy
		std::string why;
		CopyNow(std::string(), why);
		s_copy_mutex.unlock();
	}
} // namespace UsbLog
static u32 s_last_ee_cycle = 0;
static u64 s_host_poll_calls = 0;
static u64 s_last_host_poll_calls = 0;
static HostPollGate s_host_poll_gate;
static u64 s_host_clock_checks = 0;
static u64 s_last_host_clock_checks = 0;
static bool s_verbose_diag = false;

// (AI-assisted) Convert the DS4's 0..255 axis to DS2's range and absorb stick-center noise.
static u8 MapStickAxis(u8 value)
{
	constexpr int center = 128;
	constexpr int deadzone = 8;
	const int delta = static_cast<int>(value) - center;
	if (std::abs(delta) <= deadzone)
		return Pad::ANALOG_NEUTRAL_POSITION;
	if (delta < 0)
		return static_cast<u8>(center - 1 - ((-delta - deadzone) * 127 / (center - deadzone)));
	return static_cast<u8>(center - 1 + ((delta - deadzone) * 128 / (127 - deadzone)));
}

// (AI-assisted) Forward the PS4 controller to the first emulated DualShock 2.
static void VMHostUpdateController(const OrbisPadData& data)
{
	struct ButtonMapping
	{
		u32 host_mask;
		u32 ps2_button;
	};
	static constexpr ButtonMapping mappings[] = {
		{ORBIS_PAD_BUTTON_UP, PadDualshock2::Inputs::PAD_UP},
		{ORBIS_PAD_BUTTON_RIGHT, PadDualshock2::Inputs::PAD_RIGHT},
		{ORBIS_PAD_BUTTON_DOWN, PadDualshock2::Inputs::PAD_DOWN},
		{ORBIS_PAD_BUTTON_LEFT, PadDualshock2::Inputs::PAD_LEFT},
		{ORBIS_PAD_BUTTON_TRIANGLE, PadDualshock2::Inputs::PAD_TRIANGLE},
		{ORBIS_PAD_BUTTON_CIRCLE, PadDualshock2::Inputs::PAD_CIRCLE},
		{ORBIS_PAD_BUTTON_CROSS, PadDualshock2::Inputs::PAD_CROSS},
		{ORBIS_PAD_BUTTON_SQUARE, PadDualshock2::Inputs::PAD_SQUARE},
		{ORBIS_PAD_BUTTON_L1, PadDualshock2::Inputs::PAD_L1},
		{ORBIS_PAD_BUTTON_R1, PadDualshock2::Inputs::PAD_R1},
		{ORBIS_PAD_BUTTON_L3, PadDualshock2::Inputs::PAD_L3},
		{ORBIS_PAD_BUTTON_R3, PadDualshock2::Inputs::PAD_R3},
		{ORBIS_PAD_BUTTON_OPTIONS, PadDualshock2::Inputs::PAD_START},
		{ORBIS_PAD_BUTTON_TOUCH_PAD, PadDualshock2::Inputs::PAD_SELECT},
	};
	for (const ButtonMapping& mapping : mappings)
	{
		const bool was_pressed = (s_previous_pad_buttons & mapping.host_mask) != 0;
		const bool is_pressed = (data.buttons & mapping.host_mask) != 0;
		if (was_pressed != is_pressed)
			Pad::SetControllerState(0, mapping.ps2_button, is_pressed ? 1.0f : 0.0f);
	}
	s_previous_pad_buttons = data.buttons;

	if (PadBase* pad = Pad::GetPad(0))
	{
		pad->SetRawAnalogs(
			{MapStickAxis(data.leftStick.x), MapStickAxis(data.leftStick.y)},
			{MapStickAxis(data.rightStick.x), MapStickAxis(data.rightStick.y)});
		Pad::SetControllerState(0, PadDualshock2::Inputs::PAD_L2, data.analogButtons.l2 / 255.0f);
		Pad::SetControllerState(0, PadDualshock2::Inputs::PAD_R2, data.analogButtons.r2 / 255.0f);
	}
}

// (AI-assisted) Called only with the VM paused. Device limits and GSConfig belong
// to the GS thread; wait for that snapshot before showing the applied value.
static void ReadGameResolution()
{
	MTGS::RunOnGSThread([]() {
		s_max_game_upscale = (g_gs_device && GSIsHardwareRenderer()) ?
			std::clamp(GSGetMaxUpscaleMultiplier(g_gs_device->GetMaxTextureSize()), 1u, 4u) : 1u;
		const float configured = GSConfig.UpscaleMultiplier;
		// A corrupted/uninitialized value must never be exposed as a 68x or 20x
		// menu choice. The launcher intentionally exposes only 1x..4x.
		s_game_upscale = (std::isfinite(configured) && configured >= 1.0f && configured <= 4.0f) ?
			static_cast<unsigned>(configured + 0.5f) : 1u;
		s_game_upscale = std::min(s_game_upscale, s_max_game_upscale);
		s_game_aspect = std::clamp(static_cast<unsigned>(GSConfig.AspectRatio), 0u, 4u);
	});
	if (s_verbose_diag)
	{
		if (!MTGS::TimedWaitGS(2000, false, false, false))
			ProbeLog("pause step: ReadGameResolution TIMEOUT vsyncq=%d\n", MTGS::GetCurrentVsyncQueueSize());
	}
	else
		MTGS::WaitGS(false, false, false);
}

static void PublishGameMenu()
{
	PS4GameMenu::SetInGameMenu(s_game_menu_open, s_game_menu_selection, s_game_upscale, s_max_game_upscale,
		s_game_aspect, s_game_show_performance_overlay);
}

namespace ImGuiManager
{
	void SetPerformanceHUDVisible(bool visible);
}

static void ApplyPerformanceOverlay()
{
	const bool visible = s_game_show_performance_overlay;
	MTGS::RunOnGSThread([visible]() { ImGuiManager::SetPerformanceHUDVisible(visible); });
	MTGS::WaitGS(false, false, false);
	ProbeLog("Performance overlay: %s (session only)\n", visible ? "shown" : "hidden");
}

static void ApplyGameAspect(unsigned aspect)
{
	const auto value = static_cast<AspectRatioType>(std::clamp(aspect, 0u, 4u));
	// ApplySettings copies the CPU-side EmuConfig into GSConfig on the GS
	// thread. Calling ApplySettings from inside a GS callback queues a nested
	// callback and leaves the displayed aspect unchanged.
	EmuConfig.GS.AspectRatio = value;
	EmuConfig.CurrentAspectRatio = value;
	MTGS::ApplySettings();
	MTGS::WaitGS(false, false, false);
	ProbeLog("Aspect ratio applied: index=%u\n", aspect);
}

void VMHostPoll()
{
	++s_host_poll_calls;
	// (AI-assisted) Paused/menu input must not be gated by EE cycles - otherwise
	// the 16 ms paused loop (62 Hz) is throttled to one pad poll per 1024 calls
	// ~16 seconds, appearing as a hang on L3+R3. Needs proper testing.
	const VMState vm_state_early = VMManager::GetState();
	const bool is_paused_menu = (vm_state_early == VMState::Paused) || s_game_menu_open;
	if (!is_paused_menu)
	{
		// Fast path: gate clock query and CPU queue draining first to avoid
		// atomic memory fences and state queries on ~600k events/s during FMV/DMA.
		// Needs proper testing across games.
		if (!s_host_poll_gate.ShouldCheckClock(cpuRegs.cycle))
			return;
	}
	VMHostDrainCPUQueue();
	const VMState vm_state = VMManager::GetState();
	if (vm_state != VMState::Running && vm_state != VMState::Paused)
		return;
	++s_host_clock_checks;
	const double elapsed = s_run_timer.GetTimeSeconds();
	// (AI-assisted) Avoid a Pad syscall on every EE event; poll at most 100 times/s.
	// While paused/menu we still respect this 10 ms throttle for 100 Hz pad polling.
	if (elapsed - s_last_input < 0.01)
		return;
	s_last_input = elapsed;
	PS4ThreadCPUMetrics::Sample(PS4ThreadCPUMetrics::Role::EE);
	// (AI-assisted) Verbose 1s heartbeat when paused/menu open, 5s otherwise. Needs proper testing.
	const bool should_log_heartbeat = s_verbose_diag ?
		(s_game_menu_open || vm_state == VMState::Paused ? (elapsed - s_last_log >= 1.0) : (elapsed - s_last_log >= 2.0)) :
		(elapsed - s_last_log >= 5.0);
	if (should_log_heartbeat)
	{
		// Late loader logs still need migration, but never at EE event frequency.
		// Filesystem calls here are bounded by the heartbeat (normally 5 seconds).
		MigrateLegacyLogs();
		const double interval = elapsed - s_last_log;
		const double ee_mcycles = static_cast<u32>(cpuRegs.cycle - s_last_ee_cycle) / (interval * 1000000.0);
		const double host_polls_per_second = (s_host_poll_calls - s_last_host_poll_calls) / interval;
		const double host_clock_checks_per_second = (s_host_clock_checks - s_last_host_clock_checks) / interval;
		s_last_host_clock_checks = s_host_clock_checks;
		s_last_host_poll_calls = s_host_poll_calls;
		s_last_log = elapsed;
		s_last_ee_cycle = cpuRegs.cycle;
		if (s_game_session && elapsed - s_last_usb_copy >= 30.0)
		{
			s_last_usb_copy = elapsed;
			SessionSummary::RefreshGame();
			UsbLog::Request();
		}
			ProbeLog("VM heartbeat: seconds=%.1f EE_PC=%08x IOP_PC=%08x EE_cycles=%u EE_Mcycles_per_second=%.2f "
				 "Host_polls_per_second=%.0f Host_clock_checks_per_second=%.0f CPU_queue_drain_locks=%llu verbose=%d paused=%d menu=%d vsyncq=%d\n",
			elapsed, cpuRegs.pc, psxRegs.pc,
			cpuRegs.cycle, ee_mcycles, host_polls_per_second, host_clock_checks_per_second,
			static_cast<unsigned long long>(VMHostGetCPUQueueLockCount()), s_verbose_diag ? 1 : 0,
			vm_state == VMState::Paused ? 1 : 0, s_game_menu_open ? 1 : 0, MTGS::GetCurrentVsyncQueueSize());
		// Live telemetry heartbeat (PC debug server). Needs proper testing.
		{
			const double boot_s = PS4Telemetry::GetBootSeconds();
			const char* game = s_selected_game.empty() ? "" : s_selected_game.c_str();
			PS4Telemetry::Heartbeat(boot_s, elapsed, cpuRegs.pc, psxRegs.pc,
				ee_mcycles, host_polls_per_second, host_clock_checks_per_second,
				static_cast<int>(vm_state), s_game_menu_open, MTGS::GetCurrentVsyncQueueSize(), game);
		}
		if (s_verbose_diag && g_gs_device)
		{
			if (auto* vkdev = dynamic_cast<GSDeviceVK*>(g_gs_device.get()))
				ProbeLog("GS verbose: completed_fence=%llu current_fence=%llu deferred_flip=%d\n",
					(unsigned long long)vkdev->GetCompletedFenceCounter(), (unsigned long long)vkdev->GetCurrentFenceCounter(),
					vkdev->PS4HasDeferredFlip() ? 1 : 0);
		}
		PS4EEHotspots::LogInterval(interval);
		if (PS4EEHotspots::enabled && (psxRegs.pc & 0x1fffffffu) < 0x200000u)
		{
			// Where the IOP sits when it hands control back to the EE (diagnostics only).
			extern u32 iopMemRead32(u32 mem);
			const u32 start = (psxRegs.pc & ~3u) - ((psxRegs.pc & 0x1fffffffu) >= 16 ? 16u : 0u);
			ProbeLog("IOP code: pc=%08x start=%08x words=%08x %08x %08x %08x %08x %08x %08x %08x\n", psxRegs.pc, start,
				iopMemRead32(start), iopMemRead32(start + 4), iopMemRead32(start + 8), iopMemRead32(start + 12),
				iopMemRead32(start + 16), iopMemRead32(start + 20), iopMemRead32(start + 24), iopMemRead32(start + 28));
		}
		// Read on the owning EE thread, once per heartbeat. No MMIO reads or
		// worker calls here: observing a stalled IPU must not advance it.
		ProbeLog("IPU state: ctrl=%08x cmd=%08x index=%d pos=%d,%d,%d,%d,%d,%d "
			"IFC=%u OFC=%u BP=%u FP=%u wait_to=%d wait_from=%d requested=%d "
			"dma_to_qwc=%u dma_to_str=%u dma_from_qwc=%u dma_from_str=%u\n",
			ipuRegs.ctrl._u32, ipu_cmd.current, ipu_cmd.index,
			ipu_cmd.pos[0], ipu_cmd.pos[1], ipu_cmd.pos[2], ipu_cmd.pos[3], ipu_cmd.pos[4], ipu_cmd.pos[5],
			g_BP.IFC, static_cast<u32>(ipuRegs.ctrl.OFC), g_BP.BP, g_BP.FP,
			IPUCoreStatus.WaitingOnIPUTo, IPUCoreStatus.WaitingOnIPUFrom, IPUCoreStatus.DataRequested,
			ipu1ch.qwc, static_cast<u32>(ipu1ch.chcr.STR), ipu0ch.qwc, static_cast<u32>(ipu0ch.chcr.STR));
		PS4Audio::LogStatus();
		PS4ProbeLogger::LogStatus();
		// Do not attribute host logging/control work to the following guest gap.
		PS4EEEventProfile::s_sampling.gap_pending = false;
		PS4EEEventProfile::LogGaps(interval);
#if defined(PCSX2_PS4_VM_BOOT_JIT)
		ProbeLog("EE JIT cumulative: compiles=%u discards=%u page_resets=%u full_resets=%u\n",
			g_orbis_rec_compiles.load(std::memory_order_relaxed), g_orbis_rec_discards.load(std::memory_order_relaxed),
			g_orbis_rec_page_resets.load(std::memory_order_relaxed), g_orbis_rec_full_resets.load(std::memory_order_relaxed));
		ProbeLog("VTLB cached access sites compiled: quad_reads=%llu writes=%llu (not runtime calls)\n",
			static_cast<unsigned long long>(g_ps4_vtlb_cached_quad_reads),
			static_cast<unsigned long long>(g_ps4_vtlb_cached_writes));
		ProbeLog("EE multi-block wait cumulative: blocks=%llu fast_forwards=%llu skipped_iterations=%llu\n",
			static_cast<unsigned long long>(g_ps4_multiblock_wait_blocks),
			static_cast<unsigned long long>(g_ps4_multiblock_wait_runs),
			static_cast<unsigned long long>(g_ps4_multiblock_wait_iterations));
		ProbeLog("EE byte-copy fusion cumulative: blocks=%llu runs=%llu bytes=%llu\n",
			static_cast<unsigned long long>(g_ps4_bytecopy_blocks),
			static_cast<unsigned long long>(g_ps4_bytecopy_runs),
			static_cast<unsigned long long>(g_ps4_bytecopy_bytes));
		ProbeLog("EE byte-copy native fallback: short=%llu deadline=%llu mapping=%llu state=%llu scratch_batches=%llu last_declined_source=%08x last_declined_destination=%08x\n",
			static_cast<unsigned long long>(g_ps4_bytecopy_short),
			static_cast<unsigned long long>(g_ps4_bytecopy_deadline),
			static_cast<unsigned long long>(g_ps4_bytecopy_mapping),
			static_cast<unsigned long long>(g_ps4_bytecopy_state),
			static_cast<unsigned long long>(g_ps4_bytecopy_scratch),
			g_ps4_bytecopy_last_source, g_ps4_bytecopy_last_destination);
		ProbeLog("EE byte-fill fusion cumulative: blocks=%llu runs=%llu bytes=%llu declined=%llu\n",
			static_cast<unsigned long long>(g_ps4_bytefill_blocks),
			static_cast<unsigned long long>(g_ps4_bytefill_runs),
			static_cast<unsigned long long>(g_ps4_bytefill_bytes),
			static_cast<unsigned long long>(g_ps4_bytefill_declined));
#endif
	}
	// (AI-assisted) Even when heartbeat throttled, keep a 1s paused tick visible. Needs proper testing.
	if (s_verbose_diag && (s_game_menu_open || vm_state == VMState::Paused) && elapsed - s_last_pause_log >= 1.0)
	{
		s_last_pause_log = elapsed;
		ProbeLog("VM paused heartbeat: seconds=%.1f EE_PC=%08x IOP_PC=%08x vsyncq=%d\n",
			elapsed, cpuRegs.pc, psxRegs.pc, MTGS::GetCurrentVsyncQueueSize());
		PS4ProbeLogger::LogStatus();
	}
	OrbisPadData buttons{};
	const bool pad_read = s_pad >= 0 && scePadReadState(s_pad, &buttons) == 0 && buttons.connected;
	if (!pad_read)
		buttons = {};
	const u32 raw = buttons.buttons;
	const u32 pressed = raw & ~s_previous_host_buttons;
	s_previous_host_buttons = raw;
	s_blocked_pad_buttons &= raw;
	constexpr u32 menu_chord = ORBIS_PAD_BUTTON_L3 | ORBIS_PAD_BUTTON_R3;
	const bool chord_edge = (raw & menu_chord) == menu_chord && !s_menu_chord_latched;
	const bool analog_left = pad_read && buttons.leftStick.x < 72;
	const bool analog_right = pad_read && buttons.leftStick.x > 184;
	const bool analog_up = pad_read && buttons.leftStick.y < 72;
	const bool analog_down = pad_read && buttons.leftStick.y > 184;
	if ((raw & menu_chord) == 0)
		s_menu_chord_latched = false;
	else if (chord_edge)
		s_menu_chord_latched = true;

	// (AI-assisted) Keep raw edges separate from guest buttons. Release all guest
	// controls on pause; consume held menu buttons until released on resume.
	const bool menu_was_open = s_game_menu_open;
	if (chord_edge && !s_game_menu_open && vm_state == VMState::Running)
	{
		s_game_menu_open = true;
		s_game_menu_selection = 0;
		s_game_menu_direction = 0;
		s_game_menu_next_repeat = elapsed;
	}
	if (!pad_read || s_game_menu_open || vm_state == VMState::Paused)
	{
		buttons = {};
		buttons.leftStick.x = buttons.leftStick.y = 128;
		buttons.rightStick.x = buttons.rightStick.y = 128;
	}
	else
		buttons.buttons &= ~s_blocked_pad_buttons;
	VMHostUpdateController(buttons);
	if (!menu_was_open && s_game_menu_open)
	{
		// (AI-assisted) Verbose bracket to isolate which pause step hangs. Needs proper testing.
		const auto pause_t0 = Common::Timer::GetCurrentValue();
		ProbeLog("pause chord: raw=%08x pressed=%08x vm_state=%d EE_PC=%08x IOP_PC=%08x vsyncq=%d\n",
			raw, pressed, static_cast<int>(vm_state), cpuRegs.pc, psxRegs.pc, MTGS::GetCurrentVsyncQueueSize());
		ProbeLog("pause step: SetPaused(true) begin\n");
		const auto setpause_t0 = Common::Timer::GetCurrentValue();
		if (s_verbose_diag)
		{
			// Diagnostic: try timed VU+GS drain, log on timeout instead of infinite hang.
			const bool vu_ok = true; // VMManager::SetPaused does vu1Thread.WaitVU internally; we bracket around full SetPaused
			if (!MTGS::TimedWaitGS(0, false, false, false))
			{
				// Probe: GS not idle before pause - this is informational, real drain is inside SetPaused
			}
			VMManager::SetPaused(true);
			(void)vu_ok;
		}
		else
		{
			VMManager::SetPaused(true);
		}
		ProbeLog("pause step: SetPaused done dur_ms=%.2f state=%d\n",
			Common::Timer::ConvertValueToMilliseconds(Common::Timer::GetCurrentValue() - setpause_t0),
			static_cast<int>(VMManager::GetState()));
		ProbeLog("pause step: FlushPipelineCache queue begin vsyncq=%d\n", MTGS::GetCurrentVsyncQueueSize());
		MTGS::RunOnGSThread([]() {
			ProbeLog("GS: FlushPipelineCache begin\n");
			if (g_vulkan_shader_cache)
				g_vulkan_shader_cache->FlushPipelineCache();
			ProbeLog("GS: FlushPipelineCache end\n");
		});
		ProbeLog("pause step: ReadGameResolution begin\n");
		const auto readres_t0 = Common::Timer::GetCurrentValue();
		ReadGameResolution();
		ProbeLog("pause step: ReadGameResolution done dur_ms=%.2f vsyncq=%d\n",
			Common::Timer::ConvertValueToMilliseconds(Common::Timer::GetCurrentValue() - readres_t0),
			MTGS::GetCurrentVsyncQueueSize());
		ProbeLog("pause step: PublishGameMenu begin\n");
		PublishGameMenu();
		SessionSummary::Mark();
		ProbeLog("Emulator menu: opened with L3+R3 total_ms=%.2f verbose=%d\n",
			Common::Timer::ConvertValueToMilliseconds(Common::Timer::GetCurrentValue() - pause_t0), s_verbose_diag ? 1 : 0);
		return;
	}
	if (!s_game_menu_open)
		return;

	const bool cancel = (pressed & ORBIS_PAD_BUTTON_CIRCLE) != 0 || chord_edge;
	const bool confirm = (pressed & ORBIS_PAD_BUTTON_CROSS) != 0;
	if (cancel || (confirm && s_game_menu_selection != 1 && s_game_menu_selection != 2 && s_game_menu_selection != 3))
	{
		s_game_menu_open = false;
		s_blocked_pad_buttons |= raw;
		PS4GameMenu::SetInGameMenu(false, 0);
		if (!cancel && s_game_menu_selection == 4)
		{
			s_return_to_main_menu.store(true, std::memory_order_release);
			ProbeLog("VM stop request: return to main menu\n");
			VMManager::SetState(VMState::Stopping);
		}
		else if (!cancel && s_game_menu_selection == 5)
		{
			ProbeLog("VM stop request: exit application\n");
			VMManager::SetState(VMState::Stopping);
		}
		else
		{
			ProbeLog("Emulator menu: resume\n");
			VMManager::SetPaused(false);
		}
	}
	else
	{
		if (confirm && s_game_menu_selection == 3)
		{
			s_game_show_performance_overlay = !s_game_show_performance_overlay;
			ApplyPerformanceOverlay();
			PublishGameMenu();
			s_game_menu_direction = 0;
			return;
		}
		u32 navigation = 0;
		if (raw & ORBIS_PAD_BUTTON_UP || analog_up)
			navigation = ORBIS_PAD_BUTTON_UP;
		else if (raw & ORBIS_PAD_BUTTON_DOWN || analog_down)
			navigation = ORBIS_PAD_BUTTON_DOWN;
		else if (raw & ORBIS_PAD_BUTTON_LEFT || analog_left)
			navigation = ORBIS_PAD_BUTTON_LEFT;
		else if (raw & ORBIS_PAD_BUTTON_RIGHT || analog_right)
			navigation = ORBIS_PAD_BUTTON_RIGHT;
		if (navigation && (navigation != s_game_menu_direction || elapsed >= s_game_menu_next_repeat))
		{
			s_game_menu_next_repeat = elapsed + (navigation == s_game_menu_direction ? 0.12 : 0.35);
			if (navigation == ORBIS_PAD_BUTTON_UP)
				s_game_menu_selection = s_game_menu_selection == 0 ? 5 : s_game_menu_selection - 1;
			else if (navigation == ORBIS_PAD_BUTTON_DOWN)
				s_game_menu_selection = (s_game_menu_selection + 1) % 6;
			else if (s_game_menu_selection == 1 || s_game_menu_selection == 2 || s_game_menu_selection == 3)
			{
				const int delta = navigation == ORBIS_PAD_BUTTON_LEFT ? -1 : 1;
				if (s_game_menu_selection == 1)
				{
					const unsigned requested = static_cast<unsigned>(std::clamp(static_cast<int>(s_game_upscale) + delta,
						1, static_cast<int>(s_max_game_upscale)));
					if (requested != s_game_upscale)
					{
						EmuConfig.GS.UpscaleMultiplier = static_cast<float>(requested);
						MTGS::ApplySettings();
						ReadGameResolution();
						EmuConfig.GS.UpscaleMultiplier = static_cast<float>(s_game_upscale);
						ProbeLog("Internal resolution: requested=%ux applied=%ux menu_limit=%ux (session only)\n",
							requested, s_game_upscale, s_max_game_upscale);
					}
				}
				else if (s_game_menu_selection == 2)
				{
					s_game_aspect = static_cast<unsigned>((static_cast<int>(s_game_aspect) + delta + 5) % 5);
					ApplyGameAspect(s_game_aspect);
					ProbeLog("Aspect ratio: index=%u (session only)\n", s_game_aspect);
				}
				else if (delta != 0)
				{
					s_game_show_performance_overlay = !s_game_show_performance_overlay;
					ApplyPerformanceOverlay();
				}
			}
			PublishGameMenu();
		}
		s_game_menu_direction = navigation;
	}
}

static void PrepareEmulatorFolders(SettingsInterface& settings)
{
	// (AI-assisted) Initialize the same paths before the launcher and the VM.
	// Settings must be absolute before LoadConfig derives its debugger paths.
	EmuFolders::AppRoot = "/app0";
	EmuFolders::DataRoot = "/data/PS4SX2";
	EmuFolders::Resources = "/app0/resources";
	EmuFolders::Settings = "/data/PS4SX2/inis";
	EmuFolders::LoadConfig(settings);
	EmuFolders::Bios = "/data/PS4SX2/bios";
	EmuFolders::Logs = "/data/PS4SX2/logs";
	EmuFolders::Cache = "/data/PS4SX2/cache/vm-boot";
	const char* paths[] = {
		EmuFolders::DataRoot.c_str(), EmuFolders::Settings.c_str(),
		EmuFolders::Bios.c_str(), "/data/PS4SX2/roms",
		EmuFolders::MemoryCards.c_str(), EmuFolders::Savestates.c_str(),
		EmuFolders::Snapshots.c_str(), EmuFolders::Logs.c_str(),
		EmuFolders::Cheats.c_str(), EmuFolders::Patches.c_str(),
		EmuFolders::Covers.c_str(), EmuFolders::GameSettings.c_str(),
		EmuFolders::UserResources.c_str(), EmuFolders::Cache.c_str(),
		EmuFolders::Textures.c_str(), EmuFolders::InputProfiles.c_str(),
		EmuFolders::Videos.c_str(), EmuFolders::DebuggerLayouts.c_str(),
		EmuFolders::DebuggerSettings.c_str()};
	for (const char* path : paths)
	{
		Error error;
		if (FileSystem::CreateDirectoryPath(path, true, &error))
			ProbeLog("Emulator directory ready: %s\n", path);
		else
			ProbeLog("Emulator directory FAILED: %s: %s\n", path, error.GetDescription().c_str());
	}
}

// (fork) Re-read the launcher Settings markers after the game menu closes, so a
// change made in Settings applies to the game started now. Fastmem stays as set
// before CPUThreadInitialize (its VTLB mappings already exist).
// (fork) Bee Movie Game (PAL, SLES-55016): no car engine or horn sounds. Every sound
// object in the game's data keeps its base volume in dB, and the game itself uses
// -96 dB for sounds it silences. With the patch "Sonido: sin motores de coches" on,
// the disc reader rewrites the base volume of the engine loops (traffic and player
// cars, scooter, race cars, drifts) and of the horns to -96 dB as the sectors are
// read. Each value is checked against the original and against the 0x3ed record
// tag 0x14 bytes before it, so another disc or version is never touched.
namespace BeeCarMute
{
	constexpr const char* Serial = "SLES-55016";
	constexpr const char* PatchName = "Sonido: sin motores de coches";
	struct Fix
	{
		u32 offset; // byte offset of the volume in the disc image
		u32 original;
		const char* name;
	};
	constexpr Fix Fixes[] = {
		{49261920, 0xc1900000, "CarIdle"},
		{49262276, 0xc0800000, "BeeHiveCar_Drift_Lp"},
		{49262744, 0xc1180000, "Beehivescooter01_Lp"},
		{49264872, 0xc2480000, "BeeHiveCar02_Lp"},
		{49266900, 0xc1500000, "HiveCar01_Lp"},
		{49267256, 0xc1100000, "HiveCar02_Lp"},
		{49267612, 0xc1500000, "HiveCar03_Lp"},
		{49267968, 0xc1c80000, "BonusCar03_Lp"},
		{49268324, 0xc1500000, "BonusCar04_Lp"},
		{49268680, 0xc1b80000, "BonusCar05_Lp"},
		{49269036, 0xc1600000, "HiveCar04_Lp"},
		{49269392, 0xc1a80000, "HiveCar05_Lp"},
		{49269748, 0xc0c00000, "HiveCab_Lp"},
		{49270104, 0xc1a00000, "honexCar_Lp"},
		{49270460, 0xc1ac0000, "BonusCar02_Lp"},
		{49270816, 0xc1900000, "BonusCar01_Lp"},
		{49271512, 0x00000000, "Npc_honexCar_Lp"},
		{49271868, 0xc0c00000, "Npc_HiveCar05_Lp"},
		{49272224, 0xc0800000, "Npc_HiveCar04_Lp"},
		{49272580, 0xc0900000, "Npc_HiveCar03_Lp"},
		{49272936, 0xbfc00000, "Npc_HiveCar02_Lp"},
		{49273292, 0xc0400000, "Npc_HiveCar01_Lp"},
		{49273648, 0xc0a00000, "Npc_HiveCab_Lp"},
		{49274004, 0xc1200000, "RaceCar01"},
		{49274360, 0xc1200000, "RaceCar02"},
		{49274716, 0xc1980000, "HiveSuperCab_Lp"},
		{49275072, 0x00000000, "Horn_HiveCar01"},
		{49275412, 0x00000000, "Horn_HiveCar02"},
		{49275752, 0x00000000, "Horn_HiveCar03"},
		{49276092, 0x00000000, "Horn_HiveCar04"},
		{49276432, 0x00000000, "Horn_HiveCar05"},
		{49276772, 0x00000000, "Horn_BonusCar01"},
		{49277112, 0x00000000, "Horn_BonusCar02"},
		{49277452, 0x00000000, "Horn_BonusCar03"},
		{49277792, 0x00000000, "Horn_BonusCar04"},
		{49278132, 0x00000000, "Horn_BonusCar05"},
		{69596652, 0xc1200000, "BeeUnderCar_Lp"},
		{69599032, 0x00000000, "RainCarEngine_3D_Lp"},
		{208582344, 0x00000000, "Race_Npc_Car_Drift_3D_Lp"},
		{336736704, 0xc0200000, "Random_CityHornAmb"},
		{343362268, 0xc0200000, "Random_CityHornAmb"},
	};
	constexpr u32 Silent = 0xc2c00000; // -96.0f
	static std::atomic<u32> s_applied{0};

	static void Hook(u8* buffer, u32 lsn)
	{
		const u64 begin = static_cast<u64>(lsn) * 2048;
		const u64 end = begin + 2048;
		if (end <= Fixes[0].offset || begin > std::end(Fixes)[-1].offset)
			return;
		const Fix* fix = std::lower_bound(std::begin(Fixes), std::end(Fixes), begin,
			[](const Fix& f, u64 value) { return f.offset < value; });
		for (; fix != std::end(Fixes) && fix->offset < end; ++fix)
		{
			const u32 pos = static_cast<u32>(fix->offset - begin);
			u32 value, tag = 0x3ed;
			std::memcpy(&value, buffer + pos, sizeof(value));
			if (pos >= 0x14)
				std::memcpy(&tag, buffer + pos - 0x14, sizeof(tag));
			if (value != fix->original || tag != 0x3ed)
				continue;
			std::memcpy(buffer + pos, &Silent, sizeof(Silent));
			const u32 count = s_applied.fetch_add(1, std::memory_order_relaxed) + 1;
			if (count <= 128)
				ProbeLog("Bee Movie: car sound muted: %s (disc offset %u, applied %u)\n", fix->name, fix->offset, count);
		}
	}
} // namespace BeeCarMute

// (fork) Which parts of the disc a game reads, and when: contiguous runs of 256 KB
// or more are logged when the next non-contiguous read starts, so the log shows
// level loads, streamed videos and audio next to the performance lines.
namespace DiscReadLog
{
	static bool s_bee_car_mute = false;
	static u32 s_first = 0, s_next = 0, s_sectors = 0;

	static void Flush()
	{
		if (s_sectors >= 128)
			ProbeLog("Disc read: %.2f-%.2f MB (%u KB, sectors %u-%u)\n", s_first * 2048.0 / 1048576.0,
				(s_first + s_sectors) * 2048.0 / 1048576.0, s_sectors * 2, s_first, s_first + s_sectors - 1);
		s_sectors = 0;
	}

	static void Hook(u8* buffer, u32 lsn)
	{
		if (s_sectors == 0 || lsn != s_next)
		{
			// Repeated reads of the same sector (retries, buffered re-reads) do not split a run.
			if (s_sectors != 0 && lsn == s_next - 1)
				return s_bee_car_mute ? BeeCarMute::Hook(buffer, lsn) : void();
			Flush();
			s_first = lsn;
		}
		s_next = lsn + 1;
		++s_sectors;
		if (s_bee_car_mute)
			BeeCarMute::Hook(buffer, lsn);
	}
} // namespace DiscReadLog

static void ApplyLauncherSettings(SettingsInterface* settings, bool& fast_boot)
{
	int ee_cycle_rate = -1;
	if (access("/data/PS4SX2/vm-ee-cycle-normal", F_OK) == 0)
		ee_cycle_rate = 0;
	else if (access("/data/PS4SX2/vm-ee-cycle-minimum", F_OK) == 0)
		ee_cycle_rate = -3;
	else if (access("/data/PS4SX2/vm-ee-cycle-underclock", F_OK) == 0)
		ee_cycle_rate = -2;
	settings->SetIntValue("EmuCore/Speedhacks", "EECycleRate", ee_cycle_rate);
	const int ee_cycle_skip = access("/data/PS4SX2/vm-ee-cycle-skip3", F_OK) == 0 ? 3 :
	                          access("/data/PS4SX2/vm-ee-cycle-skip2", F_OK) == 0 ? 2 :
	                          access("/data/PS4SX2/vm-ee-cycle-skip", F_OK) == 0 ? 1 : 0;
	settings->SetIntValue("EmuCore/Speedhacks", "EECycleSkip", ee_cycle_skip);
	const bool fast_cdvd = access("/data/PS4SX2/vm-fast-cdvd", F_OK) == 0 &&
	                       access("/data/PS4SX2/vm-no-fast-cdvd", F_OK) != 0;
	settings->SetBoolValue("EmuCore/Speedhacks", "fastCDVD", fast_cdvd);
	fast_boot = access("/data/PS4SX2/vm-no-fast-boot", F_OK) != 0;
	settings->SetBoolValue("EmuCore", "EnableFastBoot", fast_boot);
	settings->SetBoolValue("EmuCore", "EnableFastBootFastForward", fast_boot);
	const bool audio_enabled = access("/data/PS4SX2/vm-no-audio", F_OK) != 0;
	settings->SetStringValue("SPU2/Output", "Backend", audio_enabled ? "Cubeb" : "Null");
	// GPU readbacks stall the EE thread while the GPU finishes; unsynchronized or
	// disabled readbacks trade some effects for fewer hitches.
	const int download_mode = access("/data/PS4SX2/vm-gpu-readback-off", F_OK) == 0 ?
	                              static_cast<int>(GSHardwareDownloadMode::Disabled) :
	                          access("/data/PS4SX2/vm-gpu-readback-unsync", F_OK) == 0 ?
	                              static_cast<int>(GSHardwareDownloadMode::Unsynchronized) : -1;
	if (download_mode >= 0)
		settings->SetIntValue("EmuCore/GS", "HWDownloadMode", download_mode);
	else
		settings->DeleteValue("EmuCore/GS", "HWDownloadMode");
	const bool minimum_blending = access("/data/PS4SX2/vm-blend-minimum", F_OK) == 0;
	if (minimum_blending)
		settings->SetIntValue("EmuCore/GS", "accurate_blending_unit", static_cast<int>(AccBlendLevel::Minimum));
	else
		settings->DeleteValue("EmuCore/GS", "accurate_blending_unit");
	// Fast math: no overflow/underflow clamping in the EE FPU and VU recompilers,
	// like PCSX2's "None" clamping mode. Fewer instructions per FPU/VU op.
	const bool fast_math = access("/data/PS4SX2/vm-fast-math", F_OK) == 0;
	for (const char* key : {"vu0Overflow", "vu0ExtraOverflow", "vu0SignOverflow", "vu0Underflow", "vu1Overflow",
			 "vu1ExtraOverflow", "vu1SignOverflow", "vu1Underflow", "fpuOverflow", "fpuExtraOverflow", "fpuFullMode"})
	{
		if (fast_math)
			settings->SetBoolValue("EmuCore/CPU/Recompiler", key, false);
		else
			settings->DeleteValue("EmuCore/CPU/Recompiler", key);
	}
	// Cheats and patches enabled for this game in the launcher's Trucos view
	// (game-settings/SERIAL.cheats: "C|name" = cheat, "P|name" = patch).
	std::vector<std::string> enabled_cheats, enabled_patches;
	std::string game_serial;
	{
		const auto read_line = [](FILE* file, std::string& out) {
			char line[512];
			if (!std::fgets(line, sizeof(line), file))
				return false;
			out = line;
			while (!out.empty() && (out.back() == '\n' || out.back() == '\r'))
				out.pop_back();
			return true;
		};
		std::string serial;
		if (FILE* file = std::fopen("/data/PS4SX2/game-settings/current.txt", "rb"))
		{
			read_line(file, serial);
			std::fclose(file);
		}
		FILE* file = serial.empty() ? nullptr : std::fopen(("/data/PS4SX2/game-settings/" + serial + ".cheats").c_str(), "rb");
		for (std::string line; file && read_line(file, line);)
		{
			if (line.size() > 2 && line[1] == '|')
				(line[0] == 'P' ? enabled_patches : enabled_cheats).push_back(line.substr(2));
		}
		if (file)
			std::fclose(file);
		game_serial = serial;
	}
	const bool bee_car_mute = game_serial == BeeCarMute::Serial &&
		std::find(enabled_patches.begin(), enabled_patches.end(), BeeCarMute::PatchName) != enabled_patches.end();
	DiscReadLog::s_bee_car_mute = bee_car_mute;
	g_ps4_disc_read_hook = DiscReadLog::Hook;
	settings->SetBoolValue("EmuCore", "EnableCheats", !enabled_cheats.empty());
	if (enabled_cheats.empty())
		settings->DeleteValue("Cheats", "Enable");
	else
		settings->SetStringList("Cheats", "Enable", enabled_cheats);
	if (enabled_patches.empty())
		settings->DeleteValue("Patches", "Enable");
	else
		settings->SetStringList("Patches", "Enable", enabled_patches);
#if defined(PCSX2_PS4_VM_BOOT_JIT)
	g_ps4_skip_smc_checks = access("/data/PS4SX2/vm-skip-smc", F_OK) == 0;
	g_ps4_bytecopy_fusion = g_ps4_skip_smc_checks && access("/data/PS4SX2/vm-no-bytecopy-fusion", F_OK) != 0;
	g_ps4_bytefill_fusion = access("/data/PS4SX2/vm-no-bytefill-fusion", F_OK) != 0;
#endif
	VMManager::ApplySettings();
	ProbeLog("Launcher settings applied: EE rate=%d skip=%d fastCDVD=%d fastBoot=%d audio=%d readback=%d minBlend=%d fastMath=%d\n",
		ee_cycle_rate, ee_cycle_skip, fast_cdvd ? 1 : 0, fast_boot ? 1 : 0, audio_enabled ? 1 : 0, download_mode,
		minimum_blending ? 1 : 0, fast_math ? 1 : 0);
	for (const std::string& name : enabled_cheats)
		ProbeLog("Launcher cheat enabled: %s\n", name.c_str());
	for (const std::string& name : enabled_patches)
		ProbeLog("Launcher patch enabled: %s\n", name.c_str());
	if (bee_car_mute)
		ProbeLog("Bee Movie: car engine and horn sounds muted from disc data (%zu sounds)\n", std::size(BeeCarMute::Fixes));
	SessionSummary::SetSettings(ee_cycle_rate, ee_cycle_skip, fast_cdvd, fast_boot, audio_enabled, download_mode,
		minimum_blending, fast_math, enabled_patches, enabled_cheats);
}

static void* RunVM(void*)
{
	PS4ThreadAffinity::PinCurrentThread("EE", 2);
	VMHostSetCPUThread();
	PS4ThreadCPUMetrics::Sample(PS4ThreadCPUMetrics::Role::EE);
	PS4IPUProfile::s_sampling.enabled = access("/data/PS4SX2/vm-profile-ipu", F_OK) == 0 &&
	                                    access("/data/PS4SX2/vm-no-ipu-profile", F_OK) != 0;
	PS4IPUProfile::s_access_sampling.enabled = PS4IPUProfile::s_sampling.enabled;
	ProbeLog("IPU profiling: %s (sampled duration, nominal ratio 1/%u)\n",
		PS4IPUProfile::s_sampling.enabled ? "enabled by opt-in marker with inclusive access sampling 1/1024" : "disabled for performance",
		PS4IPUProfile::SAMPLE_WEIGHT);
	static MemorySettingsInterface settings_storage;
	static MemorySettingsInterface secrets_storage;
	auto* settings = &settings_storage;
	Host::Internal::SetBaseSettingsLayer(settings);
	Host::Internal::SetSecretsSettingsLayer(&secrets_storage);
	VMManager::SetDefaultSettings(*settings, true, true, false, false, false);
	// (AI-assisted) Fase 1: EE is 30-38ms bottleneck on Jaguar (Speed 48-55% in GTA/GoW FMV, GPU 1-2ms).
	// Default to mild underclock (-1 = 75% cycles) for headroom; exact cycle accuracy costs ~25%
	// EE time on this CPU. Original 100% stays via marker for sensitive titles. Needs proper testing.
	int ee_cycle_rate = -1;
	if (access("/data/PS4SX2/vm-ee-cycle-normal", F_OK) == 0)
		ee_cycle_rate = 0;
	else if (access("/data/PS4SX2/vm-ee-cycle-underclock", F_OK) == 0)
		ee_cycle_rate = -2;
	else if (access("/data/PS4SX2/vm-ee-cycle-mild", F_OK) == 0)
		ee_cycle_rate = -1;
	settings->SetIntValue("EmuCore/Speedhacks", "EECycleRate", ee_cycle_rate);
	// (AI-assisted) Fase 3-A reverted: EECycleSkip=1 gave -1.2pp on GoW FMV (32.8ms vs 31.4ms) and no gain on GTA.
	// Reverted to 0 (opt-in via /data/PS4SX2/vm-ee-cycle-skip only). Needs proper testing.
	int ee_cycle_skip = 0;
	if (access("/data/PS4SX2/vm-ee-cycle-skip2", F_OK) == 0)
		ee_cycle_skip = 2;
	else if (access("/data/PS4SX2/vm-ee-cycle-skip", F_OK) == 0)
		ee_cycle_skip = 1;
	settings->SetIntValue("EmuCore/Speedhacks", "EECycleSkip", ee_cycle_skip);
	ProbeLog("EE cycle profile requested: rate=%d skip=%d (underclock marker=%s, mild marker=%s, normal marker=%s, skip marker=%s)\n",
		ee_cycle_rate, ee_cycle_skip,
		access("/data/PS4SX2/vm-ee-cycle-underclock", F_OK) == 0 ? "present" : "absent",
		access("/data/PS4SX2/vm-ee-cycle-mild", F_OK) == 0 ? "present" : "absent",
		access("/data/PS4SX2/vm-ee-cycle-normal", F_OK) == 0 ? "present" : "absent",
		access("/data/PS4SX2/vm-ee-cycle-skip", F_OK) == 0 ? "present" : "absent");

	// (AI-assisted) Recommended speedhacks: vuFlagHack eliminates VU1 status flag overhead,
	// IntcStat and WaitLoop bypass guest idle loops. Keep normal disc timing by default.
	// Needs proper testing per game.
	settings->SetBoolValue("EmuCore/Speedhacks", "vuFlagHack", true);
	settings->SetBoolValue("EmuCore/Speedhacks", "IntcStat", true);
	settings->SetBoolValue("EmuCore/Speedhacks", "WaitLoop", true);
	const bool fast_cdvd = access("/data/PS4SX2/vm-fast-cdvd", F_OK) == 0 &&
	                       access("/data/PS4SX2/vm-no-fast-cdvd", F_OK) != 0;
	settings->SetBoolValue("EmuCore/Speedhacks", "fastCDVD", fast_cdvd);
	ProbeLog("CDVD timing: %s\n", fast_cdvd ? "accelerated by opt-in marker" : "normal (compatibility default)");
	// (AI-assisted) Let the backend choose the compiled renderer; on this PS4 build that is Vulkan.
	settings->SetIntValue("EmuCore/GS", "Renderer", static_cast<int>(GSRendererType::VK));
	settings->SetFloatValue("EmuCore/GS", "upscale_multiplier", 1.0f);
	const bool disable_shader_cache = access("/data/PS4SX2/vm-no-shader-cache", F_OK) == 0;
	settings->SetBoolValue("EmuCore/GS", "DisableShaderCache", disable_shader_cache);
	settings->SetBoolValue("EmuCore/GS", "HWSpinGPUForReadbacks", false);
	settings->SetBoolValue("EmuCore/GS", "HWSpinCPUForReadbacks", false);
	// (AI-assisted) Hardware palette conversion, frame preloading, and partial invalidation bypass
	// reduce CPU stalls in 1x/2x upscale; needs proper testing.
	settings->SetBoolValue("EmuCore/GS", "paltex", true);
	settings->SetBoolValue("EmuCore/GS", "preload_frame_with_gs_data", true);
	// (AI-assisted) Let per-game GameDB HW fixes apply (autoFlush, halfPixelOffset, etc) to fix
	// shadows/post-processing without forcing manual overrides. GTA SA (SLUS-20946) needs
	// autoFlush=1 + halfPixelOffset=5. DisablePartialInvalidation=true stays as PS4 perf
	// default when GameDB has no entry. Needs proper testing across titles.
	settings->SetBoolValue("EmuCore/GS", "UserHacks", false);
	settings->SetBoolValue("EmuCore/GS", "UserHacks_DisablePartialInvalidation", true);
	// (AI-assisted) Triple VideoOut (ImageCount=3) with VsyncQueueSize=3 queues 2 extra frames
	// and can show stale buffers as ghosting. Use 2 (upstream default) to reduce latency
	// and present stalls; vsyncq was 0..1 in baseline. Needs proper testing.
	settings->SetIntValue("EmuCore/GS", "VsyncQueueSize", 2);
	// (AI-assisted) Skip the PS2 BIOS animation and fast-forward only the
	// emulator's boot phase. The game's own logos and loading still run normally.
	bool fast_boot = access("/data/PS4SX2/vm-no-fast-boot", F_OK) != 0;
	settings->SetBoolValue("EmuCore", "EnableFastBoot", fast_boot);
	settings->SetBoolValue("EmuCore", "EnableFastBootFastForward", fast_boot);
	settings->SetBoolValue("EmuCore", "EnablePINE", false);
	settings->SetBoolValue("EmuCore", "EnableThreadPinning", false);
	// (AI-assisted) Respect the PS4 build option; release scripts enable MTVU.
#if defined(PCSX2_PS4_VM_BOOT_MTVU)
	settings->SetBoolValue("EmuCore/Speedhacks", "vuThread", true);
#else
	settings->SetBoolValue("EmuCore/Speedhacks", "vuThread", false);
#endif
#if defined(PCSX2_PS4_VM_BOOT_JIT)
	settings->SetBoolValue("EmuCore/CPU/Recompiler", "EnableEE", true);
	settings->SetBoolValue("EmuCore/CPU/Recompiler", "EnableIOP", true);
	settings->SetBoolValue("EmuCore/CPU/Recompiler", "EnableVU0", true);
	settings->SetBoolValue("EmuCore/CPU/Recompiler", "EnableVU1", true);
#if defined(PCSX2_PS4_VM_BOOT_FASTMEM)
	// (AI-assisted) Fastmem is compiled in for performance, but keep a
	// console-side escape hatch for page-fault diagnosis. The marker must be
	// checked before CPUThreadInitialize creates the VTLB mappings.
	const bool fastmem_disabled_by_marker = access("/data/PS4SX2/vm-no-fastmem", F_OK) == 0;
	settings->SetBoolValue("EmuCore/CPU/Recompiler", "EnableFastmem", !fastmem_disabled_by_marker);
	ProbeLog("Fastmem runtime override: %s\n",
		fastmem_disabled_by_marker ? "disabled by /data/PS4SX2/vm-no-fastmem" : "enabled");
#else
	settings->SetBoolValue("EmuCore/CPU/Recompiler", "EnableFastmem", false);
#endif
#endif
	settings->SetBoolValue("Achievements", "Enabled", false);
	// (AI-assisted) Both library and VM poll scePad directly on PS4.
	settings->SetBoolValue("InputSources", "SDL", false);
	// (AI-assisted) The Orbis Cubeb slot routes to native PS4 AudioOut.
	const bool audio_enabled = access("/data/PS4SX2/vm-no-audio", F_OK) != 0;
	settings->SetStringValue("SPU2/Output", "Backend", audio_enabled ? "Cubeb" : "Null");
	settings->SetStringValue("SPU2/Output", "SyncMode", "TimeStretch");
	// (AI-assisted) Longer sequences suit slowed audio and need fewer overlap
	// searches. Leave enough queued audio for the resulting larger bursts.
	// Needs proper testing with speech, transitions and pause on the console.
	// (AI-assisted) Optimize audio buffer and time-stretching window for PS4.
	// 70 ms buffer with 35 ms sequences avoids audio buffer underruns (input_short)
	// while keeping speech and sound effects responsive and glitch-free.
	// Needs proper testing across games on the console.
	const bool legacy_audio = access("/data/PS4SX2/vm-audio-legacy-stretch", F_OK) == 0;
	settings->SetIntValue("SPU2/Output", "BufferMS", legacy_audio ? 50 : 70);
	settings->SetIntValue("SPU2/Output", "StretchSequenceLengthMS", legacy_audio ? 30 : 35);
	settings->SetIntValue("SPU2/Output", "StretchSeekWindowMS", legacy_audio ? 20 : 15);
	settings->SetIntValue("SPU2/Output", "StretchOverlapMS", legacy_audio ? 10 : 8);
	settings->SetBoolValue("SPU2/Output", "StretchUseQuickSeek", false);
	settings->SetIntValue("SPU2/Output", "StandardVolume", 100);
	settings->SetBoolValue("SPU2/Output", "OutputMuted", false);
	ProbeLog("PS4 audio configuration: %s (stereo PCM16 48 kHz, main port, explicit 0 dB; disable with /data/PS4SX2/vm-no-audio)\n",
		audio_enabled ? "native AudioOut with TimeStretch" : "Null by marker");
	PrepareEmulatorFolders(*settings);
	const bool performance_profile_opt_in = access("/data/PS4SX2/vm-profile-perf", F_OK) == 0 &&
	                                        access("/data/PS4SX2/vm-no-perf-profile", F_OK) != 0;
	const bool gs_profile_opt_in = access("/data/PS4SX2/vm-profile-gs", F_OK) == 0 ||
	                               performance_profile_opt_in;
	PS4GSProfile::enabled = gs_profile_opt_in && access("/data/PS4SX2/vm-no-gs-profile", F_OK) != 0;
	ProbeLog("GS profiling: %s (hot calls sampled 1/64; inclusive wall time)\n",
		PS4GSProfile::enabled ? "enabled by opt-in marker" : "disabled for performance");
	ProbeLog("VM configuration: observation=unlimited renderer=vulkan mtvu=%s fastmem-build=%s shader_cache=%s directory=%s\n",
#if defined(PCSX2_PS4_VM_BOOT_MTVU)
		"on",
#else
		"off",
#endif
#if defined(PCSX2_PS4_VM_BOOT_FASTMEM)
		"on",
#else
		"off",
#endif
		disable_shader_cache ? "disabled by marker" : "enabled", EmuFolders::Cache.c_str());
	ProbeLog("STAGE: CPUThreadInitialize (real VM, JIT, optional user disc)\n");
	PS4Telemetry::Stage("cpu-init");
	if (!VMManager::Internal::CPUThreadInitialize())
	{
		ProbeLog("CPUThreadInitialize FAILED\n");
		PS4Telemetry::Stage("cpu-init-failed");
		return nullptr;
	}
	ProbeLog("VM settings loaded: MTVU=%s Fastmem=%s; awaiting initial VTLB mappings\n",
		EmuConfig.Speedhacks.vuThread ? "on" : "off",
		EmuConfig.Cpu.Recompiler.EnableFastmem ? "on" : "off");
	ProbeLog("VM runtime EE cycle profile: rate=%d skip=%u\n",
		static_cast<int>(EmuConfig.Speedhacks.EECycleRate),
		static_cast<unsigned>(EmuConfig.Speedhacks.EECycleSkip));
	VMBootParameters boot{};
	GamePlatform platform = GamePlatform::Unknown;
	g_ps4_ipu_csc_reuse = access("/data/PS4SX2/vm-no-ipu-csc-reuse", F_OK) != 0;
	ProbeLog("IPU CSC output reuse: %s (partial FIFO drain; timing unchanged)\n",
		g_ps4_ipu_csc_reuse ? "enabled" : "disabled by marker");
	g_ps4_ipu0_burst = access("/data/PS4SX2/vm-no-ipu-burst", F_OK) != 0;
	ProbeLog("IPU output burst: %s (up to 32 FIFO fills per DMA event, cycles preserved; disable with /data/PS4SX2/vm-no-ipu-burst)\n",
		g_ps4_ipu0_burst ? "enabled" : "disabled by marker");
#if defined(PCSX2_PS4_VM_BOOT_JIT)
	g_ps4_vtlb_register_cache = access("/data/PS4SX2/vm-no-vtlb-register-cache", F_OK) != 0;
	ProbeLog("VTLB scalar read register cache: %s (device handlers retained; Fastmem unchanged)\n",
		g_ps4_vtlb_register_cache ? "enabled" : "disabled by marker");
	g_ps4_vtlb_bulk_register_cache = g_ps4_vtlb_register_cache &&
	                                 access("/data/PS4SX2/vm-no-vtlb-bulk-cache", F_OK) != 0;
	g_ps4_vtlb_cached_quad_reads = g_ps4_vtlb_cached_writes = 0;
	ProbeLog("VTLB quad read/store register cache: %s (disable with /data/PS4SX2/vm-no-vtlb-bulk-cache)\n",
		g_ps4_vtlb_bulk_register_cache ? "enabled (default since v0.87)" : "disabled by marker");
	// (AI-assisted) Fase 3-B REVERTED 2026-10-12: SMC skip default ON broke GTA SLUS-20946
	// (Unknown SPECIAL 00000001 at 00eaa1c4, Trap 00eaa1d4, stuck at 8000fe74 100% unavailable).
	// GoW gained +18pp but GTA unbootable -> revert to exact SMC. Opt-in via /data/PS4SX2/vm-skip-smc. Needs proper testing.
	g_ps4_skip_smc_checks = access("/data/PS4SX2/vm-skip-smc", F_OK) == 0;
	ProbeLog("EE JIT manual SMC validation: %s (%s)\n",
		g_ps4_skip_smc_checks ? "relaxed (skip per-block checks, manual protection only)" : "enabled for all games (exact block checks)",
		g_ps4_skip_smc_checks ? "enabled by /data/PS4SX2/vm-skip-smc" : "exact (reverted Fase 3-B)");
	// (AI-assisted) Exact SMC mode must inspect code on every loop iteration.
	g_ps4_bytecopy_fusion = g_ps4_skip_smc_checks && access("/data/PS4SX2/vm-no-bytecopy-fusion", F_OK) != 0;
	g_ps4_bytecopy_blocks = g_ps4_bytecopy_runs = g_ps4_bytecopy_bytes = 0;
	g_ps4_bytecopy_short = g_ps4_bytecopy_deadline = g_ps4_bytecopy_mapping = g_ps4_bytecopy_state = g_ps4_bytecopy_scratch = 0;
	g_ps4_bytecopy_last_source = g_ps4_bytecopy_last_destination = 0;
	ProbeLog("EE byte-copy fusion: %s (disable with /data/PS4SX2/vm-no-bytecopy-fusion)\n",
		g_ps4_bytecopy_fusion ? "enabled with inline deadline gate, mapped RAM batches and native fallback" : "disabled by marker or exact SMC checks");
	g_ps4_bytefill_fusion = access("/data/PS4SX2/vm-no-bytefill-fusion", F_OK) != 0;
	g_ps4_bytefill_blocks = g_ps4_bytefill_runs = g_ps4_bytefill_bytes = g_ps4_bytefill_declined = 0;
	ProbeLog("EE byte-fill fusion: %s (disable with /data/PS4SX2/vm-no-bytefill-fusion)\n",
		g_ps4_bytefill_fusion ? "enabled (memset byte loops run natively, page and event bounded)" : "disabled by marker");
#endif
	// (AI-assisted) This process has never initialized Piglet. The recovery
	// selector and the VM share only the Vulkan backend on the GS thread.
	if (s_use_vulkan_selector)
	{
		ProbeLog("STAGE: Vulkan game library\n");
		if (!PS4GameMenu::Select(s_pad, s_selected_game, platform))
		{
			ProbeLog("Vulkan selector ended without a selection\n");
			VMManager::Internal::CPUThreadShutdown();
			return nullptr;
		}
	}
	ApplyLauncherSettings(settings, fast_boot);
	if (platform == GamePlatform::PS1)
	{
		// (AI-assisted) PS1DRV takes over the EE after the BIOS. Do not carry the
		// experimental PS2 FMV shortcuts into its boot/code replacement sequence.
		// This compatibility profile needs proper testing on the console.
		fast_boot = false;
		settings->SetBoolValue("EmuCore", "EnableFastBoot", false);
		settings->SetBoolValue("EmuCore", "EnableFastBootFastForward", false);
		settings->SetBoolValue("EmuCore/Speedhacks", "fastCDVD", false);
		// Restore the core's conservative idle-loop detection. Keep the port's
		// wider loop rule disabled for PS1, and retain exact code validation.
		settings->SetBoolValue("EmuCore/Speedhacks", "WaitLoop", true);
		settings->SetBoolValue("EmuCore/Speedhacks", "IntcStat", false);
		settings->SetBoolValue("EmuCore/Speedhacks", "vuThread", false);
		settings->SetIntValue("EmuCore/Speedhacks", "EECycleRate", 0);
		settings->SetIntValue("EmuCore/Speedhacks", "EECycleSkip", 0);
#if defined(PCSX2_PS4_VM_BOOT_JIT)
		g_ps4_skip_smc_checks = false;
		g_ps4_bytecopy_fusion = false;
		g_ps4_bytefill_fusion = false;
		g_ps4_vtlb_register_cache = false;
		g_ps4_vtlb_bulk_register_cache = false;
		g_orbis_waitloop_ext.store(0, std::memory_order_relaxed);
#endif
		// Still before VM reset and the first guest instruction. Updating the base
		// layer also preserves the profile when menu settings are reapplied later.
		VMManager::ApplySettings();
		ProbeLog("PS1 compatibility profile: full BIOS boot; exact SMC checks; byte-copy fusion and VTLB register caches OFF; WaitLoop=upstream; IntcStat/fastCDVD/MTVU OFF; EE rate=0 skip=0\n");
	}
	boot.filename = s_selected_game;
	ProbeLog("Session archive: platform marker saved=%d platform=%s\n",
		PS4SessionLogs::MarkGame(platform) ? 1 : 0,
		platform == GamePlatform::PS1 ? "PS1" : platform == GamePlatform::PS2 ? "PS2" : "Other");
	PS4Telemetry::GameSelect(boot.filename.c_str(),
		platform == GamePlatform::PS1 ? "PS1" : platform == GamePlatform::PS2 ? "PS2" : "Other");
	PS4Telemetry::Stage(boot.filename.empty() ? "game-bios" : "game-selected");
	if (s_use_vulkan_selector)
		PS4GameMenu::ShowLoading(24, boot.filename.empty() ? "Preparing PS2 BIOS..." :
			boot.filename == PS4Disc::DevicePath ? "Opening physical DVD..." : "Mounting game image...");
	ProbeLog("Disc selection: library returned %s\n", boot.filename.empty() ? "BIOS (no disc)" : boot.filename.c_str());
	if (boot.filename.empty())
	{
		boot.source_type = CDVD_SourceType::NoDisc;
		ProbeLog("Disc selection: BIOS without a disc selected in menu.\n");
	}
	else
	{
		boot.source_type = boot.filename == PS4Disc::DevicePath ? CDVD_SourceType::Disc : CDVD_SourceType::Iso;
		ProbeLog("Disc selection: mounting %s\n", boot.filename.c_str());
	}
	boot.fast_boot = fast_boot;
	ProbeLog("Fast boot: %s (PS1 always uses full BIOS boot; PS2 override: /data/PS4SX2/vm-no-fast-boot)\n", fast_boot ? "enabled" : "disabled");
	Error error;
	if (s_use_vulkan_selector)
		PS4GameMenu::ShowLoading(45, "Initializing virtual machine...");
	ProbeLog("STAGE: VMManager::Initialize\n");
	PS4Telemetry::Stage("vm-init");
	const auto result = VMManager::Initialize(boot, &error);
	if (result == VMBootResult::StartupSuccess)
	{
		if (s_use_vulkan_selector)
			PS4GameMenu::ShowLoading(92, "Starting PlayStation 2...");
		ProbeLog("VM runtime Fastmem=%s (after initial VTLB mappings)\n",
			EmuConfig.Cpu.Recompiler.EnableFastmem ? "on" : "off");
		ProbeLog("VM initialized: executing BIOS; no probe MMIO shadows\n");
		PS4Telemetry::Stage("vm-running");
		// (AI-assisted) A DS4 has no dedicated analog-mode switch; start the emulated DS2 in analog mode.
		Pad::SetControllerState(0, PadDualshock2::Inputs::PAD_ANALOG, 1.0f);
		Pad::SetControllerState(0, PadDualshock2::Inputs::PAD_ANALOG, 0.0f);
		ProbeLog("Controller: DualShock 2 analog mode enabled; both sticks and analog triggers forwarded.\n");
		s_verbose_diag = access("/data/PS4SX2/vm-verbose-log", F_OK) == 0;
		ProbeLog("Verbose diagnostics: %s (single marker /data/PS4SX2/vm-verbose-log forces 1s heartbeat, TimedWaitGS, and GS/EE hotspot sampling)\n",
			s_verbose_diag ? "ENABLED" : "disabled");
		s_run_timer.Reset();
		const bool hotspot_marker = access("/data/PS4SX2/vm-ee-hotspots", F_OK) == 0 && access("/data/PS4SX2/vm-no-ee-hotspots", F_OK) != 0;
		PS4EEHotspots::Reset(hotspot_marker || s_verbose_diag);
		ProbeLog("EE hotspots: %s; event and IPU-call frequencies, not CPU-time shares (disable with /data/PS4SX2/vm-no-ee-hotspots)\n",
			PS4EEHotspots::enabled ? "enabled" : "disabled");
#if defined(PCSX2_PS4_VM_EE_BLOCK_PROFILE)
		PS4EEHotspots::ResetBlockSampling(true);
		ProbeLog("EE JIT block sampling: enabled by diagnostic build; randomized interval 2048-4095 block entries\n");
#else
		PS4EEHotspots::ResetBlockSampling(hotspot_marker || s_verbose_diag);
		ProbeLog("EE JIT block sampling: %s\n", (hotspot_marker || s_verbose_diag) ? "enabled (verbose forces on)" : "disabled in performance build");
#endif
		PS4EEEventProfile::s_sampling = {};
		// (AI-assisted) Keep deep profiling opt-in: PS1 can reach over a million
		// event polls per second. Normal FPS/CPU metrics and heartbeat stay active.
		const bool performance_profile = access("/data/PS4SX2/vm-profile-perf", F_OK) == 0 &&
		                                 access("/data/PS4SX2/vm-no-perf-profile", F_OK) != 0;
		PS4WorkerProfile::enabled.store(performance_profile, std::memory_order_relaxed);
		PS4EEEventProfile::s_sampling.enabled = ((performance_profile || access("/data/PS4SX2/vm-profile-ee", F_OK) == 0) && access("/data/PS4SX2/vm-no-ee-profile", F_OK) != 0) || s_verbose_diag;
		PS4EEEventProfile::s_sampling.gaps_only = false;
		PS4EEEventProfile::s_sampling.gap_observer = PS4EEEventProfile::RecordGap;
		ProbeLog("Performance diagnosis: workers=%d EE_phases=%d sample_ratio=1/1024; opt-in with /data/PS4SX2/vm-profile-perf\n",
			performance_profile ? 1 : 0, PS4EEEventProfile::s_sampling.enabled ? 1 : 0);
		// The performance-diagnostics toggle predates the separate GS marker.
		// Keep profiles saved by older builds useful, unless GS profiling is explicitly disabled.
		const bool gs_profile_opt_in = access("/data/PS4SX2/vm-profile-gs", F_OK) == 0 || performance_profile;
		PS4GSProfile::enabled = s_verbose_diag ||
		                        (gs_profile_opt_in && access("/data/PS4SX2/vm-no-gs-profile", F_OK) != 0);
		ProbeLog("GS profiling: %s (hot calls sampled 1/64; inclusive wall time)\n",
			PS4GSProfile::enabled ? "enabled" : "disabled");
		s_host_poll_gate.Reset();
		ProbeLog("Host clock gate runtime: max_calls=%u cycle_interval=%u input_interval_ms=10\n",
			s_host_poll_gate.GetMaxCalls(), s_host_poll_gate.GetCycleInterval());
		s_host_poll_calls = s_last_host_poll_calls = 0;
		s_host_clock_checks = s_last_host_clock_checks = 0;
		s_last_log = 0.0;
		s_last_pause_log = 0.0;
		s_last_input = -1.0;
		s_last_ee_cycle = cpuRegs.cycle;
		s_previous_pad_buttons = s_previous_host_buttons = 0;
		s_blocked_pad_buttons = ~u32{0}; // Consume any launcher button still held.
		s_menu_chord_latched = s_game_menu_open = false;
		s_game_menu_selection = 0;
		ProbeLog("Controller: OPTIONS=PS2 Start, touchpad=PS2 Select, L3+R3=emulator menu\n");
		if (s_use_vulkan_selector)
		{
			PS4GameMenu::ShowLoading(100, "Ready");
			Threading::Sleep(50);
			PS4GameMenu::HideLoading();
		}
		VMManager::SetPaused(false);
		s_game_session = true;
		SessionSummary::Begin();
		SessionSummary::RefreshGame();
		while (VMManager::GetState() != VMState::Stopping && VMManager::GetState() != VMState::Shutdown)
		{
			if (VMManager::GetState() == VMState::Paused)
			{
				// Keep reading menu controls while the EE is paused.
				VMHostPoll();
				Threading::Sleep(16);
			}
			else
			{
				VMManager::Execute();
			}
		}
		PS4EEEventProfile::s_sampling.enabled = false;
		PS4EEHotspots::Reset(false);
		PS4EEHotspots::ResetBlockSampling(false);
		PS4EEEventProfile::s_sampling.gap_pending = false;
		ProbeLog("STAGE: VMManager::Shutdown\n");
		PS4Telemetry::Stage("vm-shutdown");
		VMManager::Shutdown(false);
	}
	else
	{
		if (s_use_vulkan_selector)
			PS4GameMenu::HideLoading();
		ProbeLog("VM initialization failed: %s\n", error.GetDescription().c_str());
		PS4Telemetry::Stage("vm-init-failed");
		// A failed mount is not an exit request. Reuse the clean-process return
		// path, since Initialize may already have shut down the shared GS device.
		s_return_to_main_menu.store(true, std::memory_order_release);
	}
	VMManager::Internal::CPUThreadShutdown();
	ProbeLog("VM lifecycle finished\n");
	return nullptr;
}

int main()
{
	mkdir("/data/PS4SX2", 0777);
	// (AI-assisted) Keep all runtime diagnostics together for FTP collection.
	mkdir("/data/PS4SX2/logs", 0777);
	const int migrated_logs = MigrateLegacyLogs();
	const auto archived_logs = PS4SessionLogs::ArchivePrevious();
	SessionSummary::KeepLeftover();
	// If archiving fails, append rather than destroying the remaining evidence.
	const int log_flags = O_WRONLY | O_CREAT | (archived_logs.error ? O_APPEND : O_TRUNC);
	// (AI-assisted) Redirect descriptors without reopening or altering libc FILE
	// objects. The GS diagnostics use ProbeLog directly; needs proper testing.
	const char* stream_paths[] = {"/data/PS4SX2/logs/PCSX2-vm-stdout.log", "/data/PS4SX2/logs/PCSX2-vm-stderr.log"};
	for (int stream = 0; stream < 2; stream++)
	{
		const int fd = open(stream_paths[stream], log_flags, 0666);
		if (fd >= 0)
		{
			if (fd != stream + 1)
			{
				dup2(fd, stream + 1);
				close(fd);
			}
		}
	}
	s_log = open("/data/PS4SX2/logs/PCSX2-vm-boot.log", log_flags, 0666);
	s_verbose_diag = access("/data/PS4SX2/vm-verbose-log", F_OK) == 0;
	const bool synchronous_log = access("/data/PS4SX2/vm-sync-log", F_OK) == 0 || s_verbose_diag;
	const bool kernel_log = access("/data/PS4SX2/vm-kernel-log", F_OK) == 0 || s_verbose_diag;
	const int log_thread_result = PS4ProbeLogger::Start(s_log, synchronous_log, kernel_log);
	// Live telemetry to PC debug server (reads /data/PS4SX2/telemetry.conf). Needs proper testing.
	const bool telemetry_started = PS4Telemetry::Start();
	// Record entry before module loading, so a stalled re-launch still has a startup marker.
	ProbeLog("PS4SX2 Emu 1.00 CHD (AI-assisted) BUILD: PS4SX2-EMU-1.00-CHD-SMC-TELEMETRY\n");
	ProbeLog("Telemetry: start=%d\n", telemetry_started ? 1 : 0);
	PS4Telemetry::Stage("boot");
	ProbeLog("Telemetry: PC debug server target from /data/PS4SX2/telemetry.conf (create with 'host=PC_IP port=19423')\n");
	ProbeLog("Log directory: /data/PS4SX2/logs migrated=%d\n", migrated_logs);
	ProbeLog("Session archive: directory=%s moved=%d errno=%d\n",
		archived_logs.directory, archived_logs.moved, archived_logs.error);
	ProbeLog("PS4 log startup: fd=%d synchronous_marker=%d kernel_mirror=%d thread_result=%d verbose=%d\n", s_log, synchronous_log, kernel_log, log_thread_result, s_verbose_diag ? 1 : 0);
	PS4ProbeLogger::LogStatus();
	PS4Telemetry::Stage("loading-modules");
	ProbeLog("STAGE: loading system modules\n");
	const int system_service_result = sceSysmoduleLoadModuleInternal(ORBIS_SYSMODULE_INTERNAL_SYSTEM_SERVICE);
	// (AI-assisted) Load VideoOut before the shared Vulkan menu/game device.
	const int video_out_result = sceSysmoduleLoadModuleInternal(ORBIS_SYSMODULE_INTERNAL_VIDEO_OUT);
	Log::SetHostOutputLevel(LOGLEVEL_DEV, ConsoleMessage);
	// (AI-assisted) v0.72 still queried the host clock 17–19k times/s in GoW FMV.
	// At the measured ~240M EE cycles/s, 131072 cycles span ~0.55 ms. The
	// call limit also allows progress without guest cycles; input latency on
	// much slower titles needs proper console testing. Paused VMs bypass this gate.
	// v0.86: 512/262144 halves that again and reduces per-event overhead in FMV.
	// v0.87: 1024/524288 halves Host_clock_checks again (FMV ~1.2k -> ~0.6k/s)
	// and benefits all games during busy loops. Needs proper testing on input latency and slow titles.
	// (AI-assisted) Fase 2: HostPollGate 1024/524288 -> 2048/1M. FMV loops hit VMHostPoll ~600k/s;
	// doubling the gate halves Host_clock_checks and CPU queue fences; input stays 100 Hz via 10ms throttle. Needs proper testing.
	const bool legacy_host_poll = access("/data/PS4SX2/vm-legacy-host-poll", F_OK) == 0;
	const u32 host_poll_calls = legacy_host_poll ? 64 : 2048;
	const u32 host_poll_cycles = legacy_host_poll ? 32768 : 1048576;
	s_host_poll_gate = HostPollGate(host_poll_calls, host_poll_cycles);
	ProbeLog("Host clock gate: max_calls=%u cycle_interval=%u input_interval_ms=10 legacy_marker=%d\n",
		host_poll_calls, host_poll_cycles, legacy_host_poll);
	ProbeLog("Launch profile: PAID=0x3800000000000011 APP_TYPE=1 ATTRIBUTE=0 CATEGORY=gd\n");
	ProbeLog("Vulkan preflight: SystemService=%#x VideoOut=%#x\n", system_service_result, video_out_result);
	{
		MemorySettingsInterface folder_settings;
		ProbeLog("STAGE: emulator directories before launcher\n");
		PrepareEmulatorFolders(folder_settings);
	}
	// (AI-assisted) Never initialize RADV under the mini-app memory profile
	// observed in v0.49. This guard runs before CPUThreadInitialize or any GPU map.
	const size_t direct_memory = sceKernelGetDirectMemorySize();
	ProbeLog("Vulkan preflight: direct memory pool=%zu MiB\n", direct_memory / (1024 * 1024));
	if (direct_memory < 1024ULL * 1024 * 1024)
	{
		ProbeLog("Vulkan startup BLOCKED: application memory profile is too small; no GPU initialized\n");
		Log::SetHostOutputLevel(LOGLEVEL_NONE, nullptr);
		PS4ProbeLogger::Stop();
		if (s_log >= 0)
			fsync(s_log);
		sceSystemServiceLoadExec("exit", nullptr);
		return 1;
	}
	// Old one-shot files must not bypass the library after this package update.
	unlink("/data/PS4SX2/vm-launch-request");
	unlink("/data/PS4SX2/vm-launch-request.tmp");
	s_use_vulkan_selector = true;
	ProbeLog("STAGE: unified Vulkan library and VM; SDL/Piglet disabled\n");
	{
		// A new process must reopen both services and its own controller handle.
		sceSysmoduleLoadModuleInternal(ORBIS_SYSMODULE_INTERNAL_USER_SERVICE);
		sceSysmoduleLoadModuleInternal(ORBIS_SYSMODULE_INTERNAL_PAD);
		OrbisUserServiceUserId user = 0;
		int user_result = sceUserServiceGetInitialUser(&user);
		if (user_result != 0)
		{
			OrbisUserServiceInitializeParams params{};
			params.priority = ORBIS_KERNEL_PRIO_FIFO_LOWEST;
			const int init_result = sceUserServiceInitialize(&params);
			ProbeLog("Vulkan input: UserService init=%#x\n", init_result);
			user_result = sceUserServiceGetInitialUser(&user);
		}
		if (s_pad < 0)
		{
			const int pad_result = scePadInit();
			if (user_result == 0)
				s_pad = scePadOpen(user, 0, 0, nullptr);
			ProbeLog("Vulkan input: pad init=%#x user=%#x handle=%d\n", pad_result, user_result, s_pad);
		}
	}
	int rc = 0;
	s_return_to_main_menu.store(false, std::memory_order_release);
	pthread_attr_t attr;
	pthread_t cpu_thread;
	rc = pthread_attr_init(&attr);
	if (rc == 0)
	{
		rc = pthread_attr_setstacksize(&attr, 16 * 1024 * 1024);
		if (rc == 0)
			rc = pthread_create(&cpu_thread, &attr, RunVM, nullptr);
		pthread_attr_destroy(&attr);
		if (rc == 0)
			pthread_join(cpu_thread, nullptr);
	}
	if (rc != 0)
		ProbeLog("CPU thread failed: %d\n", rc);
	if (s_pad >= 0)
		scePadClose(s_pad);
	const bool relaunch_main_menu = rc == 0 && s_return_to_main_menu.load(std::memory_order_acquire);
	Log::SetHostOutputLevel(LOGLEVEL_NONE, nullptr);
	PS4Telemetry::Stage(relaunch_main_menu ? "exit-relaunch" : "exit");
	PS4Telemetry::Stop();
	PS4ProbeLogger::Stop();
	if (s_log >= 0)
	{
		fsync(s_log);
		close(s_log);
	}
	if (s_game_session)
		UsbLog::Final();
	if (relaunch_main_menu)
	{
		// VM teardown closes Vulkan/VideoOut resources. Reinitializing them in the
		// same process was the source of the return-to-menu crash; ask the shell to
		// start a clean selector process instead.
		sceSystemServiceLoadExec("/app0/eboot.bin", nullptr);
	}
	sceSystemServiceLoadExec("exit", nullptr);
	return rc == 0 ? 0 : 1;
}
