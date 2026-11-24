// SPDX-License-Identifier: GPL-3.0+
// (AI-assisted) Keep every completed or interrupted session in an unbounded archive.
#pragma once

#include "GamePlatform.h"
#include <cerrno>
#include <cstdio>
#include <cstring>
#include <ctime>
#include <dirent.h>
#include <fcntl.h>
#include <string>
#include <sys/stat.h>
#include <unistd.h>

namespace PS4SessionLogs
{
	constexpr const char* MarkerPath = "/data/PS4SX2/logs/session-platform.txt";
	constexpr const char* LogsPath = "/data/PS4SX2/logs";
	constexpr const char* SessionsPath = "/data/PS4SX2/logs/sessions";

	struct Metadata
	{
		char platform[16] = "menu";
		char started[32]{};
		char pid[24]{};
		char serial[64]{};
		char title[128]{};
		char archive_directory[256]{};
	};

	struct ArchiveResult
	{
		char directory[384]{};
		int moved = 0;
		int error = 0;
	};

	inline void CopyText(char* destination, size_t capacity, const char* source)
	{
		if (!capacity)
			return;
		std::snprintf(destination, capacity, "%s", source ? source : "");
	}

	inline void CopyField(char* destination, size_t capacity, const char* source)
	{
		if (!capacity)
			return;
		size_t written = 0;
		for (const char* current = source ? source : ""; *current && written + 1 < capacity; ++current)
		{
			if (*current != '\n' && *current != '\r')
				destination[written++] = *current;
		}
		destination[written] = '\0';
	}

	inline std::string SafeComponent(const char* value, const char* fallback, size_t max_length)
	{
		std::string result;
		bool previous_separator = true;
		for (const unsigned char* current = reinterpret_cast<const unsigned char*>(value ? value : "");
		     *current && result.size() < max_length; ++current)
		{
			const unsigned char c = *current;
			const bool safe = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
			                  (c >= '0' && c <= '9') || c == '-' || c == '_';
			if (safe)
			{
				result.push_back(static_cast<char>(c));
				previous_separator = false;
			}
			else if (!previous_separator && result.size() < max_length)
			{
				result.push_back('_');
				previous_separator = true;
			}
		}
		while (!result.empty() && result.back() == '_')
			result.pop_back();
		if (result.empty())
			result = fallback;
		return result;
	}

	inline std::string CurrentTimestamp()
	{
		const time_t now = time(nullptr);
		tm local{};
		char timestamp[32] = "unknown-time";
		if (localtime_r(&now, &local))
			strftime(timestamp, sizeof(timestamp), "%Y%m%d-%H%M%S", &local);
		return timestamp;
	}

	inline bool ReadMetadata(Metadata& metadata)
	{
		FILE* file = std::fopen(MarkerPath, "rb");
		if (!file)
			return false;

		bool has_data = false;
		char line[256];
		while (std::fgets(line, sizeof(line), file))
		{
			size_t length = std::strlen(line);
			while (length && (line[length - 1] == '\n' || line[length - 1] == '\r'))
				line[--length] = '\0';
			if (!length)
				continue;
			has_data = true;
			char* separator = std::strchr(line, '=');
			if (!separator)
			{
				// Backward compatibility with the old marker containing only "PS1"/"PS2".
				if (metadata.platform[0] == '\0' || std::strcmp(metadata.platform, "menu") == 0)
					CopyText(metadata.platform, sizeof(metadata.platform), line);
				continue;
			}
			*separator++ = '\0';
			if (std::strcmp(line, "platform") == 0)
				CopyText(metadata.platform, sizeof(metadata.platform), separator);
			else if (std::strcmp(line, "started") == 0)
				CopyText(metadata.started, sizeof(metadata.started), separator);
			else if (std::strcmp(line, "pid") == 0)
				CopyText(metadata.pid, sizeof(metadata.pid), separator);
			else if (std::strcmp(line, "serial") == 0)
				CopyText(metadata.serial, sizeof(metadata.serial), separator);
			else if (std::strcmp(line, "title") == 0)
				CopyText(metadata.title, sizeof(metadata.title), separator);
			else if (std::strcmp(line, "archive") == 0)
				CopyText(metadata.archive_directory, sizeof(metadata.archive_directory), separator);
		}
		std::fclose(file);
		return has_data;
	}

	inline bool WriteAll(int fd, const char* data, size_t size)
	{
		size_t written = 0;
		while (written < size)
		{
			const ssize_t count = write(fd, data + written, size - written);
			if (count < 0 && errno == EINTR)
				continue;
			if (count <= 0)
				return false;
			written += static_cast<size_t>(count);
		}
		return true;
	}

	inline bool WriteMetadata(const Metadata& metadata)
	{
		if (mkdir(LogsPath, 0777) != 0 && errno != EEXIST)
			return false;
		char contents[768];
		const int length = std::snprintf(contents, sizeof(contents),
			"platform=%s\nstarted=%s\npid=%s\nserial=%s\ntitle=%s\narchive=%s\n",
			metadata.platform, metadata.started, metadata.pid, metadata.serial, metadata.title, metadata.archive_directory);
		if (length <= 0 || static_cast<size_t>(length) >= sizeof(contents))
			return false;
		char temporary[160];
		std::snprintf(temporary, sizeof(temporary), "%s.tmp", MarkerPath);
		const int fd = open(temporary, O_WRONLY | O_CREAT | O_TRUNC, 0666);
		if (fd < 0)
			return false;
		const bool written = WriteAll(fd, contents, static_cast<size_t>(length));
		const bool synced = fsync(fd) == 0;
		close(fd);
		if (written && synced && rename(temporary, MarkerPath) == 0)
			return true;
		unlink(temporary);
		return false;
	}

	inline std::string DirectoryName(const Metadata& metadata, unsigned collision = 0)
	{
		const std::string started = SafeComponent(metadata.started, "unknown-time", 24);
		const std::string pid = SafeComponent(metadata.pid, "pid-unknown", 16);
		const std::string platform = SafeComponent(metadata.platform, "other", 12);
		const std::string serial = SafeComponent(metadata.serial, "unknown-game", 40);
		const std::string title = SafeComponent(metadata.title, "untitled", 48);
		std::string result = started + "_" + pid + "_" + platform + "_" + serial + "_" + title;
		if (collision)
			result += "_" + std::to_string(collision + 1);
		return result;
	}

	inline std::string CurrentDirectoryName()
	{
		Metadata metadata;
		if (!ReadMetadata(metadata))
			return {};
		if (metadata.archive_directory[0])
			return SafeComponent(metadata.archive_directory, "invalid-archive", 240);
		if (!metadata.started[0])
			CopyText(metadata.started, sizeof(metadata.started), CurrentTimestamp().c_str());
		if (!metadata.pid[0])
		{
			char pid[24];
			std::snprintf(pid, sizeof(pid), "%d", static_cast<int>(getpid()));
			CopyText(metadata.pid, sizeof(metadata.pid), pid);
		}
		return DirectoryName(metadata);
	}

	inline bool MarkGame(GamePlatform platform)
	{
		Metadata metadata;
		const bool marker_exists = ReadMetadata(metadata);
		const char* value = platform == GamePlatform::PS1 ? "PS1" :
		                    platform == GamePlatform::PS2 ? "PS2" : "Other";
		char pid[24];
		std::snprintf(pid, sizeof(pid), "%d", static_cast<int>(getpid()));
		// If a previous archive is incomplete, keep its marker so the next boot can finish it.
		if (marker_exists && metadata.archive_directory[0])
			return false;
		if (marker_exists && (!metadata.pid[0] || std::strcmp(metadata.pid, pid) != 0))
			return false;
		if (!marker_exists || metadata.started[0] == '\0' || std::strcmp(metadata.platform, value) != 0)
		{
			metadata = {};
			CopyText(metadata.started, sizeof(metadata.started), CurrentTimestamp().c_str());
			CopyText(metadata.pid, sizeof(metadata.pid), pid);
		}
		CopyText(metadata.platform, sizeof(metadata.platform), value);
		return WriteMetadata(metadata);
	}

	inline bool UpdateGameMetadata(const char* started, const char* serial, const char* title)
	{
		Metadata metadata;
		if (!ReadMetadata(metadata))
			return false;
		if (started && *started)
			CopyText(metadata.started, sizeof(metadata.started), started);
		if (serial && *serial)
			CopyField(metadata.serial, sizeof(metadata.serial), serial);
		if (title && *title)
			CopyField(metadata.title, sizeof(metadata.title), title);
		return WriteMetadata(metadata);
	}

	inline bool WriteTextFileAtomic(const char* path, const char* text)
	{
		char temporary[512];
		std::snprintf(temporary, sizeof(temporary), "%s.tmp", path);
		const int fd = open(temporary, O_WRONLY | O_CREAT | O_TRUNC, 0666);
		if (fd < 0)
			return false;
		const size_t length = text ? std::strlen(text) : 0;
		const bool ok = WriteAll(fd, text ? text : "", length);
		const bool synced = fsync(fd) == 0;
		close(fd);
		if (ok && synced && rename(temporary, path) == 0)
			return true;
		unlink(temporary);
		return false;
	}

	inline bool WriteSessionInfo(const char* directory, const Metadata& metadata, const char* summary)
	{
		char path[512], info[512];
		std::snprintf(path, sizeof(path), "%s/session-info.txt", directory);
		const int length = std::snprintf(info, sizeof(info),
			"Platform: %s\nStarted: %s\nProcess ID: %s\nDisc serial: %s\nGame title: %s\n",
			metadata.platform, metadata.started, metadata.pid, metadata.serial, metadata.title);
		if (length <= 0 || static_cast<size_t>(length) >= sizeof(info) || !WriteTextFileAtomic(path, info))
			return false;
		if (summary && *summary)
		{
			std::snprintf(path, sizeof(path), "%s/session-summary.txt", directory);
			if (!WriteTextFileAtomic(path, summary))
				return false;
		}
		return true;
	}

	inline bool AppendSourceAndRemove(const char* source, const char* target)
	{
		const int in = open(source, O_RDONLY);
		if (in < 0)
			return errno == ENOENT;
		const int out = open(target, O_WRONLY | O_CREAT | O_APPEND, 0666);
		if (out < 0)
		{
			close(in);
			return false;
		}
		static constexpr const char* separator = "\n--- additional log data after a prior archive attempt ---\n";
		bool ok = WriteAll(out, separator, std::strlen(separator));
		char buffer[32 * 1024];
		while (ok)
		{
			const ssize_t count = read(in, buffer, sizeof(buffer));
			if (count == 0)
				break;
			if (count < 0)
			{
				if (errno == EINTR)
					continue;
				ok = false;
				break;
			}
			ok = WriteAll(out, buffer, static_cast<size_t>(count));
		}
		ok = fsync(out) == 0 && ok;
		close(in);
		close(out);
		if (ok)
			return unlink(source) == 0 || errno == ENOENT;
		return false;
	}

	inline ArchiveResult ArchivePrevious(const char* summary = nullptr)
	{
		ArchiveResult result;
		Metadata metadata;
		const bool has_marker = ReadMetadata(metadata);
		if (!has_marker)
		{
			metadata = {};
			CopyText(metadata.platform, sizeof(metadata.platform), "menu");
			CopyText(metadata.started, sizeof(metadata.started), CurrentTimestamp().c_str());
			char pid[24];
			std::snprintf(pid, sizeof(pid), "%d", static_cast<int>(getpid()));
			CopyText(metadata.pid, sizeof(metadata.pid), pid);
		}
		if (!metadata.started[0])
			CopyText(metadata.started, sizeof(metadata.started), CurrentTimestamp().c_str());

		bool has_logs = false;
		DIR* logs = opendir(LogsPath);
		if (!logs && errno != ENOENT)
		{
			result.error = errno;
			return result;
		}
		if (logs)
		{
			while (dirent* entry = readdir(logs))
			{
				if (entry->d_name[0] == '.' && (!entry->d_name[1] ||
				    (entry->d_name[1] == '.' && !entry->d_name[2])))
					continue;
				if (std::strcmp(entry->d_name, "session-platform.txt") == 0)
					continue;
				char source[384];
				std::snprintf(source, sizeof(source), "%s/%s", LogsPath, entry->d_name);
				struct stat st{};
				if (stat(source, &st) == 0 && S_ISREG(st.st_mode))
					has_logs = true;
			}
			closedir(logs);
		}
		if (!has_logs && !has_marker && (!summary || !*summary))
			return result;

		if (mkdir(SessionsPath, 0777) != 0 && errno != EEXIST)
		{
			result.error = errno;
			return result;
		}
		struct stat sessions_stat{};
		if (stat(SessionsPath, &sessions_stat) != 0 || !S_ISDIR(sessions_stat.st_mode))
		{
			result.error = errno ? errno : ENOTDIR;
			return result;
		}
		if (metadata.archive_directory[0])
		{
			const std::string safe_archive = SafeComponent(metadata.archive_directory, "invalid-archive", 240);
			CopyText(metadata.archive_directory, sizeof(metadata.archive_directory), safe_archive.c_str());
			std::snprintf(result.directory, sizeof(result.directory), "%s/%s", SessionsPath, metadata.archive_directory);
			if (mkdir(result.directory, 0777) != 0 && errno != EEXIST)
			{
				result.error = errno;
				result.directory[0] = '\0';
				return result;
			}
			struct stat archive_stat{};
			if (stat(result.directory, &archive_stat) != 0 || !S_ISDIR(archive_stat.st_mode))
			{
				result.error = errno ? errno : ENOTDIR;
				result.directory[0] = '\0';
				return result;
			}
		}
		else
		{
			bool created = false;
			for (unsigned collision = 0; collision < 10000; ++collision)
			{
				const std::string name = DirectoryName(metadata, collision);
				std::snprintf(result.directory, sizeof(result.directory), "%s/%s", SessionsPath, name.c_str());
				if (mkdir(result.directory, 0777) == 0)
				{
					CopyText(metadata.archive_directory, sizeof(metadata.archive_directory), name.c_str());
					if (!WriteMetadata(metadata))
					{
						result.error = errno ? errno : EIO;
						rmdir(result.directory);
						result.directory[0] = '\0';
						return result;
					}
					created = true;
					break;
				}
				if (errno != EEXIST)
				{
					result.error = errno;
					result.directory[0] = '\0';
					return result;
				}
				result.directory[0] = '\0';
			}
			if (!created)
			{
				result.error = EEXIST;
				return result;
			}
		}

		logs = opendir(LogsPath);
		if (!logs && errno != ENOENT && !result.error)
			result.error = errno;
		if (logs)
		{
			while (dirent* entry = readdir(logs))
			{
				if (entry->d_name[0] == '.' && (!entry->d_name[1] ||
				    (entry->d_name[1] == '.' && !entry->d_name[2])))
					continue;
				if (std::strcmp(entry->d_name, "session-platform.txt") == 0)
					continue; // Keep retry metadata until every log and summary is archived.
				char source[384], target[768];
				std::snprintf(source, sizeof(source), "%s/%s", LogsPath, entry->d_name);
				std::snprintf(target, sizeof(target), "%s/%s", result.directory, entry->d_name);
				struct stat st{};
				if (stat(source, &st) != 0)
				{
					if (errno != ENOENT && !result.error)
						result.error = errno;
					continue;
				}
				if (!S_ISREG(st.st_mode))
					continue;
				if (access(target, F_OK) == 0)
				{
					if (AppendSourceAndRemove(source, target))
						++result.moved;
					else if (!result.error)
						result.error = errno ? errno : EIO;
				}
				else if (rename(source, target) == 0)
					++result.moved;
				else if (errno != ENOENT && !result.error)
					result.error = errno;
			}
			closedir(logs);
		}
		if (!WriteSessionInfo(result.directory, metadata, summary) && !result.error)
			result.error = errno ? errno : EIO;
		if (!result.error)
			unlink(MarkerPath);
		return result;
	}
} // namespace PS4SessionLogs
