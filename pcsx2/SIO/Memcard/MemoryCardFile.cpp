// SPDX-FileCopyrightText: 2002-2026 PCSX2 Dev Team
// SPDX-License-Identifier: GPL-3.0+

#include "SIO/Memcard/MemoryCardFile.h"

#include "SIO/Memcard/MemoryCardFolder.h"
#include "SIO/Sio.h"
#include <SIO/SioTypes.h>

#include "common/Assertions.h"
#include "common/Console.h"
#include "common/Error.h"
#include "common/FileSystem.h"
#include "common/Path.h"
#include "common/StringUtil.h"

#include <array>
#include <chrono>

#include "Config.h"
#include "Host.h"
#include "VMManager.h"
#include "IconsPromptFont.h"

#include "fmt/format.h"

#include <algorithm>
#include <cstring>
#include <map>

#include <atomic>
#include <unistd.h>
#if !defined(PCSX2_PS4)
#include "OrbisPaths.h" // vk-285-33 (the port's include-orbis)
#endif

static constexpr int MCD_SIZE = 1024 * 8 * 16; // Legacy PSX card default size

static constexpr int MC2_MBSIZE = 1024 * 528 * 2; // Size of a single megabyte of card data

static constexpr int MC2_ERASE_SIZE = 528 * 16;

static const char* s_folder_mem_card_id_file = "_pcsx2_superblock";

// PS5 port (vk-285-31): memory card activity for the [mcd] line (GSRenderer.cpp's OrbisPrintLoad):
// page reads, page writes, block erases, host time spent in them (TSC ticks) and KiB written back.
// Each call used to seek and read/write the card file on /data, where one write costs ~0.7 ms, so a
// game's autosave (hundreds of page writes, each read back to verify) held the EE thread for seconds.
std::atomic<u32> g_orbis_mcd_reads{0}, g_orbis_mcd_writes{0}, g_orbis_mcd_erases{0}, g_orbis_mcd_flush_kib{0};
std::atomic<unsigned long long> g_orbis_mcd_ticks{0};
std::atomic<int> g_orbis_mcd_cached{0}; // a bit per slot whose image is in RAM

namespace
{
	struct OrbisMcdTimer
	{
		const unsigned long long t0 = __builtin_ia32_rdtsc();
		~OrbisMcdTimer() { g_orbis_mcd_ticks.fetch_add(__builtin_ia32_rdtsc() - t0, std::memory_order_relaxed); }
	};
} // namespace

bool FileMcd_Open = false;

// ECC code ported from mymc
// https://sourceforge.net/p/mymc-opl/code/ci/master/tree/ps2mc_ecc.py
// Public domain license

static u32 CalculateECC(u8* buf)
{
	const u8 parity_table[256] = {0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1,
		0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0,
		1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1,
		0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
		1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1,
		0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0,
		1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0,
		1, 0, 1, 1, 0};

	const u8 column_parity_mask[256] = {0, 7, 22, 17, 37, 34, 51, 52, 52, 51, 34, 37, 17, 22,
		7, 0, 67, 68, 85, 82, 102, 97, 112, 119, 119, 112, 97, 102, 82, 85, 68, 67, 82, 85, 68, 67, 119, 112,
		97, 102, 102, 97, 112, 119, 67, 68, 85, 82, 17, 22, 7, 0, 52, 51, 34, 37, 37, 34, 51, 52, 0, 7, 22, 17,
		97, 102, 119, 112, 68, 67, 82, 85, 85, 82, 67, 68, 112, 119, 102, 97, 34, 37, 52, 51, 7, 0, 17, 22,
		22, 17, 0, 7, 51, 52, 37, 34, 51, 52, 37, 34, 22, 17, 0, 7, 7, 0, 17, 22, 34, 37, 52, 51, 112, 119, 102,
		97, 85, 82, 67, 68, 68, 67, 82, 85, 97, 102, 119, 112, 112, 119, 102, 97, 85, 82, 67, 68, 68, 67, 82,
		85, 97, 102, 119, 112, 51, 52, 37, 34, 22, 17, 0, 7, 7, 0, 17, 22, 34, 37, 52, 51, 34, 37, 52, 51, 7, 0,
		17, 22, 22, 17, 0, 7, 51, 52, 37, 34, 97, 102, 119, 112, 68, 67, 82, 85, 85, 82, 67, 68, 112, 119, 102,
		97, 17, 22, 7, 0, 52, 51, 34, 37, 37, 34, 51, 52, 0, 7, 22, 17, 82, 85, 68, 67, 119, 112, 97, 102, 102,
		97, 112, 119, 67, 68, 85, 82, 67, 68, 85, 82, 102, 97, 112, 119, 119, 112, 97, 102, 82, 85, 68, 67,
		0, 7, 22, 17, 37, 34, 51, 52, 52, 51, 34, 37, 17, 22, 7, 0};

	u8 column_parity = 0x77;
	u8 line_parity_0 = 0x7F;
	u8 line_parity_1 = 0x7F;

	for (int i = 0; i < 128; i++)
	{
		u8 b = buf[i];
		column_parity ^= column_parity_mask[b];
		if (parity_table[b])
		{
			line_parity_0 ^= ~i;
			line_parity_1 ^= i;
		}
	}

	return column_parity | (line_parity_0 << 8) | (line_parity_1 << 16);
}

static bool ConvertNoECCtoRAW(const char* file_in, const char* file_out)
{
	auto fin = FileSystem::OpenManagedCFile(file_in, "rb");
	if (!fin)
		return false;

	auto fout = FileSystem::OpenManagedCFile(file_out, "wb");
	if (!fout)
		return false;

	const s64 size = FileSystem::FSize64(fin.get());
	u8 buffer[512];

	for (s64 i = 0; i < (size / 512); i++)
	{
		if (std::fread(buffer, sizeof(buffer), 1, fin.get()) != 1 ||
			std::fwrite(buffer, sizeof(buffer), 1, fout.get()) != 1)
		{
			return false;
		}

		for (int j = 0; j < 4; j++)
		{
			u32 checksum = CalculateECC(&buffer[j * 128]);
			if (std::fwrite(&checksum, 3, 1, fout.get()) != 1)
				return false;
		}

		u32 nullbytes = 0;
		if (std::fwrite(&nullbytes, sizeof(nullbytes), 1, fout.get()) != 1)
			return false;
	}

	if (std::fflush(fout.get()) != 0)
		return false;

	return true;
}

static bool ConvertRAWtoNoECC(const char* file_in, const char* file_out)
{
	auto fin = FileSystem::OpenManagedCFile(file_in, "rb");
	if (!fin)
		return false;

	auto fout = FileSystem::OpenManagedCFile(file_out, "wb");
	if (!fout)
		return false;

	const s64 size = FileSystem::FSize64(fin.get());
	u8 buffer[512];
	u8 checksum[16];

	for (s64 i = 0; i < (size / 528); i++)
	{
		if (std::fread(buffer, sizeof(buffer), 1, fin.get()) != 1 ||
			std::fwrite(buffer, sizeof(buffer), 1, fout.get()) != 1 ||
			std::fread(checksum, sizeof(checksum), 1, fin.get()) != 1)
		{
			return false;
		}
	}

	if (std::fflush(fout.get()) != 0)
		return false;

	return true;
}

// --------------------------------------------------------------------------------------
//  FileMemoryCard
// --------------------------------------------------------------------------------------
// Provides thread-safe direct file IO mapping.
//
class FileMemoryCard
{
protected:
	std::FILE* m_file[8] = {};
	s64 m_fileSize[8] = {};
	std::string m_filenames[8] = {};
	std::vector<u8> m_currentdata;
	u64 m_chksum[8] = {};
	bool m_ispsx[8] = {};
	u32 m_chkaddr = 0;

	// PS5 port (vk-285-31): a PS2 card's image in RAM. Reads, writes and erases work on it; the
	// erase blocks they touch are written back to the file in a few large writes once the card has
	// been idle for a second (NextFrame runs once an emulated second, cdvdVsync -> sioNextFrame),
	// every 5 s while it stays busy, and when the card closes. Formatted cards load at open, others
	// on their first write. /data/PCSX2/mcd_nocache turns the cache off.
	std::vector<u8> m_cache[8];
	std::vector<u8> m_dirty[8]; // a flag per erase block
	bool m_dirty_any[8] = {};
	bool m_cache_ok[8] = {};
	u32 m_idle_seconds[8] = {};
	u32 m_dirty_seconds[8] = {};
	struct IoStats
	{
		u64 read_calls = 0;
		u64 read_failures = 0;
		u64 write_calls = 0;
		u64 write_failures = 0;
		u64 erase_calls = 0;
		u64 erase_failures = 0;
		u64 flush_calls = 0;
		u64 flush_failures = 0;
	};
	IoStats m_io_stats[8] = {};

public:
	FileMemoryCard();
	~FileMemoryCard();

	void Lock();
	void Unlock();

	void Open();
	void Close();

	s32 IsPresent(uint slot);
	void GetSizeInfo(uint slot, McdSizeInfo& outways);
	bool IsPSX(uint slot);
	s32 Read(uint slot, u8* dest, u32 adr, int size);
	s32 Save(uint slot, const u8* src, u32 adr, int size);
	s32 EraseBlock(uint slot, u32 adr);
	u64 GetCRC(uint slot);
	void NextFrame(uint slot); // vk-285-31

protected:
	bool Seek(std::FILE* f, u32 adr);
	bool Create(const char* mcdFile, uint sizeInMB);
	bool LoadCache(uint slot); // vk-285-31
	bool FlushCache(uint slot, const char* why);
	void MarkDirty(uint slot, u32 adr, u32 size);
};

uint FileMcd_GetMtapPort(uint slot)
{
	switch (slot)
	{
		case 0:
		case 2:
		case 3:
		case 4:
			return 0;
		case 1:
		case 5:
		case 6:
		case 7:
			return 1;

			jNO_DEFAULT
	}

	return 0; // technically unreachable.
}

// Returns the multitap slot number, range 1 to 3 (slot 0 refers to the standard
// 1st and 2nd player slots).
uint FileMcd_GetMtapSlot(uint slot)
{
	switch (slot)
	{
		case 0:
		case 1:
			pxFail("Invalid parameter in call to GetMtapSlot -- specified slot is one of the base slots, not a Multitap slot.");
			break;

		case 2:
		case 3:
		case 4:
			return slot - 1;
		case 5:
		case 6:
		case 7:
			return slot - 4;

			jNO_DEFAULT
	}

	return 0; // technically unreachable.
}

bool FileMcd_IsMultitapSlot(uint slot)
{
	return (slot > 1);
}

std::string FileMcd_GetDefaultName(uint slot)
{
	if (FileMcd_IsMultitapSlot(slot))
		return StringUtil::StdStringFromFormat("Mcd-Multitap%u-Slot%02u.ps2", FileMcd_GetMtapPort(slot) + 1, FileMcd_GetMtapSlot(slot) + 1);
	else
		return StringUtil::StdStringFromFormat("Mcd%03u.ps2", slot + 1);
}

FileMemoryCard::FileMemoryCard()
{
	for (u8 slot = 0; slot < 8; slot++)
	{
		m_fileSize[slot] = -1;
	}
}

FileMemoryCard::~FileMemoryCard() = default;

static void LogCardContents(uint slot, const std::vector<u8>& image, const char* when);

void FileMemoryCard::Open()
{
	for (int slot = 0; slot < 8; ++slot)
	{
		m_filenames[slot] = {};
		m_io_stats[slot] = {};

		if (EmuConfig.Mcd[slot].Type != MemoryCardType::File)
			continue;

		if (FileMcd_IsMultitapSlot(slot))
		{
			if (!EmuConfig.Pad.MultitapPort0_Enabled && (FileMcd_GetMtapPort(slot) == 0))
				continue;
			if (!EmuConfig.Pad.MultitapPort1_Enabled && (FileMcd_GetMtapPort(slot) == 1))
				continue;
		}

		const std::string fname = EmuConfig.FullpathToMcd(slot);

		if (!EmuConfig.Mcd[slot].Enabled || fname.empty())
		{
			Console.WriteLnFmt("McdSlot {} [File]: [disabled/empty filename]", slot);
			continue;
		}

		if (FileSystem::GetPathFileSize(fname.c_str()) <= 0)
		{
			if (!Create(fname.c_str(), 8))
			{
				Host::ReportErrorAsync(TRANSLATE_SV("MemoryCard", "Memory Card Creation Failed"),
					fmt::format(TRANSLATE_FS("MemoryCard", "Could not create the memory card:\n{}"),
						fname));
			}
		}

		if (fname.ends_with(".bin") || fname.ends_with(".mc2"))
		{
			std::string newname(fname + "x");
			if (!ConvertNoECCtoRAW(fname.c_str(), newname.c_str()))
			{
				Console.Error("Could convert memory card: %s", fname.c_str());
				FileSystem::DeleteFilePath(newname.c_str());
				continue;
			}

			// store the original filename
			m_file[slot] = FileSystem::OpenSharedCFile(newname.c_str(), "r+b", FileSystem::FileShareMode::DenyWrite);
		}
		else
		{
			m_file[slot] = FileSystem::OpenSharedCFile(fname.c_str(), "r+b", FileSystem::FileShareMode::DenyWrite);
		}

		if (!m_file[slot])
		{
			Host::ReportErrorAsync(TRANSLATE_SV("MemoryCard", "Memory Card Read Failed"),
				fmt::format(TRANSLATE_FS("MemoryCard", "Unable to access memory card:\n\n{}\n\n"
													   "Another instance of PCSX2 may be using this memory card "
													   "or the memory card is stored in a write-protected folder.\n"
													   "Close any other instances of PCSX2, or restart your computer.\n"),
					fname));
		}
		else // Load checksum
		{
			m_fileSize[slot] = FileSystem::FSize64(m_file[slot]);

			Console.WriteLnFmt(Color_Green, "McdSlot {} [File]: {} [{} MB, {}]", slot, Path::GetFileName(fname),
				(m_fileSize[slot] + (MCD_SIZE + 1)) / MC2_MBSIZE,
				FileMcd_IsMemoryCardFormatted(m_file[slot]) ? "Formatted" : "UNFORMATTED");

			m_filenames[slot] = std::move(fname);
			m_ispsx[slot] = m_fileSize[slot] == 0x20000;
			m_chkaddr = 0x210;

			if (!m_ispsx[slot] && FileSystem::FSeek64(m_file[slot], m_chkaddr, SEEK_SET) == 0)
			{
				const size_t read_result = std::fread(&m_chksum[slot], sizeof(m_chksum[slot]), 1, m_file[slot]);
				if (read_result == 0)
					Host::ReportErrorAsync("Memory Card Read Failed", "Error reading memory card.");
			}

			// Keep the RAM image for non-PS1 cards. The PS4 build has no OrbisFlag file adapter.
			#if defined(PCSX2_PS4)
			m_cache_ok[slot] = !m_ispsx[slot];
			#else
			m_cache_ok[slot] = !m_ispsx[slot] && !OrbisFlag("mcd_nocache");
			#endif
			if (m_cache_ok[slot] && FileMcd_IsMemoryCardFormatted(m_file[slot]))
			{
				if (LoadCache(slot))
					LogCardContents(slot, m_cache[slot], "start");
			}
			else
				std::printf("[mcd] slot %d: %s\n", slot,
					!m_cache_ok[slot] ? (m_ispsx[slot] ? "PS1 card, not cached" : "mcd_nocache: not cached") :
										"unformatted, cached at its first write");
		}
	}
}

// vk-285-31: the whole card image into RAM.
bool FileMemoryCard::LoadCache(uint slot)
{
	std::FILE* f = m_file[slot];
	const s64 size = m_fileSize[slot];
	if (!f || size <= 0 || size > (72 << 20)) // vk-285-113: a 64 MB card is 66 MiB with its ECC bytes
	{
		m_cache_ok[slot] = false;
		return false;
	}
	const unsigned long long t0 = __builtin_ia32_rdtsc();
	const auto c0 = std::chrono::steady_clock::now();
	std::vector<u8> image(static_cast<size_t>(size));
	if (FileSystem::FSeek64(f, 0, SEEK_SET) != 0 || std::fread(image.data(), image.size(), 1, f) != 1)
	{
		std::printf("[mcd] slot %u: reading the card into RAM failed, not cached\n", slot);
		m_cache_ok[slot] = false;
		return false;
	}
	m_cache[slot] = std::move(image);
	m_dirty[slot].assign((m_cache[slot].size() + MC2_ERASE_SIZE - 1) / MC2_ERASE_SIZE, 0);
	m_dirty_any[slot] = false;
	g_orbis_mcd_cached.fetch_or(1 << slot, std::memory_order_relaxed);
	g_orbis_mcd_ticks.fetch_add(__builtin_ia32_rdtsc() - t0, std::memory_order_relaxed);
	std::printf("[mcd] slot %u: %s in RAM (%lld bytes, read in %.1f ms)\n", slot,
		std::string(Path::GetFileName(m_filenames[slot])).c_str(), static_cast<long long>(size),
		std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - c0).count());
	return true;
}

// PS4 port: what the card holds, read from its RAM image (the PS2 memory card file
// system: superblock, indirect FAT, directory entries). Logged when the game starts
// and when it closes, so a session log shows the free space and every save with its
// size and date, and flags a save whose cluster chain is broken.
static void LogCardContents(uint slot, const std::vector<u8>& image, const char* when)
{
	static constexpr char Magic[] = "Sony PS2 Memory Card Format ";
	if (image.size() < 0x200 || std::memcmp(image.data(), Magic, sizeof(Magic) - 1) != 0)
	{
		std::printf("[mcd] card %u (%s): no PS2 file system\n", slot, when);
		return;
	}
	const auto rd16 = [](const u8* p) { return static_cast<u32>(p[0] | (p[1] << 8)); };
	const auto rd32 = [](const u8* p) { return static_cast<u32>(p[0] | (p[1] << 8) | (p[2] << 16) | (static_cast<u32>(p[3]) << 24)); };
	const u8* sb = image.data();
	const u32 page_len = rd16(sb + 0x28), ppc = rd16(sb + 0x2A), clusters = rd32(sb + 0x30);
	const u32 alloc_offset = rd32(sb + 0x34), alloc_end = rd32(sb + 0x38), root = rd32(sb + 0x3C);
	if (page_len == 0 || page_len > 2048 || ppc == 0 || ppc > 16 || clusters == 0 || alloc_end == 0 || alloc_end > clusters)
	{
		std::printf("[mcd] card %u (%s): superblock not valid (page %u, cluster %u pages, %u clusters, end %u)\n", slot, when,
			page_len, ppc, clusters, alloc_end);
		return;
	}
	const size_t raw_page = image.size() >= static_cast<size_t>(clusters) * ppc * (page_len + 16) ? page_len + 16 : page_len;
	const u32 cluster_size = page_len * ppc, per_cluster = cluster_size / 4;
	std::vector<u8> buffer(cluster_size);
	u32 buffer_cluster = ~0u;
	const auto read_cluster = [&](u32 absolute) -> const u8* {
		if (absolute == buffer_cluster)
			return buffer.data();
		for (u32 p = 0; p < ppc; p++)
		{
			const size_t offset = (static_cast<size_t>(absolute) * ppc + p) * raw_page;
			if (offset + page_len > image.size())
				return nullptr;
			std::memcpy(&buffer[p * page_len], &image[offset], page_len);
		}
		buffer_cluster = absolute;
		return buffer.data();
	};
	// FAT entry of a cluster relative to alloc_offset: bit 31 = in use, 0xFFFFFFFF = last one.
	const auto fat = [&](u32 relative, u32* out) -> bool {
		const u32 fat_index = relative / per_cluster, indirect_index = fat_index / per_cluster;
		if (indirect_index >= 32)
			return false;
		const u8* ifc = read_cluster(rd32(sb + 0x50 + indirect_index * 4));
		if (!ifc)
			return false;
		const u32 fat_cluster = rd32(ifc + (fat_index % per_cluster) * 4);
		const u8* table = read_cluster(fat_cluster);
		if (!table)
			return false;
		*out = rd32(table + (relative % per_cluster) * 4);
		return true;
	};
	u32 free_clusters = 0;
	bool fat_ok = true;
	for (u32 c = 0; c < alloc_end && fat_ok; c++)
	{
		u32 e = 0;
		fat_ok = fat(c, &e);
		free_clusters += fat_ok && !(e & 0x80000000u);
	}
	// A file's clusters, following the FAT from its first one.
	const auto chain = [&](u32 start, std::vector<u32>* out) -> bool {
		out->clear();
		u32 c = start;
		while (out->size() <= alloc_end)
		{
			if (c >= alloc_end)
				return false;
			out->push_back(c);
			u32 e = 0;
			if (!fat(c, &e) || !(e & 0x80000000u))
				return false;
			if (e == 0xFFFFFFFFu)
				return true;
			c = e & 0x7FFFFFFFu;
		}
		return false; // a loop
	};
	struct DirEntry
	{
		u32 mode = 0, length = 0, cluster = 0;
		u8 modified[8] = {};
		char name[33] = {};
	};
	const auto entry_at = [&](const std::vector<u32>& clusters_of_dir, u32 index, DirEntry* out) -> bool {
		const u32 byte = index * 512;
		if (byte / cluster_size >= clusters_of_dir.size())
			return false;
		const u8* data = read_cluster(alloc_offset + clusters_of_dir[byte / cluster_size]);
		if (!data)
			return false;
		const u8* e = data + byte % cluster_size;
		out->mode = rd16(e);
		out->length = rd32(e + 4);
		out->cluster = rd32(e + 0x10);
		std::memcpy(out->modified, e + 0x18, 8);
		std::memcpy(out->name, e + 0x40, 32);
		out->name[32] = 0;
		for (char* c = out->name; *c; c++)
			if (static_cast<u8>(*c) < 0x20 || static_cast<u8>(*c) > 0x7e)
				*c = '?';
		return true;
	};
	std::vector<u32> root_clusters;
	DirEntry dot;
	if (!chain(root, &root_clusters) || !entry_at(root_clusters, 0, &dot))
	{
		std::printf("[mcd] card %u (%s): root directory unreadable (cluster %u)\n", slot, when, root);
		return;
	}
	struct Save
	{
		DirEntry dir;
		u32 files = 0, bytes = 0, broken = 0;
		std::string first_broken;
	};
	std::vector<Save> saves;
	u32 bad_root = 0;
	for (u32 i = 2; i < dot.length && i < 4096; i++)
	{
		Save save;
		if (!entry_at(root_clusters, i, &save.dir))
		{
			bad_root++;
			break;
		}
		if (!(save.dir.mode & 0x8000) || !(save.dir.mode & 0x20))
			continue;
		std::vector<u32> dir_clusters, file_clusters;
		if (!chain(save.dir.cluster, &dir_clusters))
		{
			save.broken++;
			save.first_broken = "(its directory)";
		}
		else
		{
			for (u32 j = 2; j < save.dir.length && j < 512; j++)
			{
				DirEntry file;
				if (!entry_at(dir_clusters, j, &file))
				{
					save.broken++;
					if (save.first_broken.empty())
						save.first_broken = "(its directory)";
					break;
				}
				if (!(file.mode & 0x8000) || !(file.mode & 0x10))
					continue;
				save.files++;
				save.bytes += file.length;
				const u32 needed = (file.length + cluster_size - 1) / cluster_size;
				if (needed && (!chain(file.cluster, &file_clusters) || file_clusters.size() < needed))
				{
					save.broken++;
					if (save.first_broken.empty())
						save.first_broken = file.name;
				}
			}
		}
		saves.push_back(std::move(save));
	}
	std::printf("[mcd] card %u (%s): %u KiB free of %u KiB, %zu save(s)%s%s\n", slot, when,
		free_clusters * cluster_size / 1024, alloc_end * cluster_size / 1024, saves.size(),
		fat_ok ? "" : ", FAT unreadable", bad_root ? ", root directory cut short" : "");
	// Newest first.
	const auto when_key = [&](const Save& save) {
		const u8* t = save.dir.modified;
		return (static_cast<u64>(rd16(t + 6)) << 40) | (static_cast<u64>(t[5]) << 32) | (static_cast<u64>(t[4]) << 24) |
		       (static_cast<u64>(t[3]) << 16) | (static_cast<u64>(t[2]) << 8) | t[1];
	};
	std::sort(saves.begin(), saves.end(), [&](const Save& a, const Save& b) { return when_key(a) > when_key(b); });
	for (size_t i = 0; i < saves.size() && i < 64; i++)
	{
		const Save& save = saves[i];
		const u8* t = save.dir.modified; // PS2 time (JST): sec, min, hour, day, month, year
		std::printf("[mcd]   %-32s %2u file(s) %5u KiB  %04u-%02u-%02u %02u:%02u%s%s\n", save.dir.name, save.files,
			(save.bytes + 1023) / 1024, rd16(t + 6), t[5], t[4], t[3], t[2], save.broken ? "  BROKEN: " : "",
			save.broken ? save.first_broken.c_str() : "");
	}
	if (saves.size() > 64)
		std::printf("[mcd]   ... %zu more\n", saves.size() - 64);
	std::fflush(stdout);
}

void FileMemoryCard::MarkDirty(uint slot, u32 adr, u32 size)
{
	if (size == 0)
		return;
	const u32 first = adr / MC2_ERASE_SIZE, last = (adr + size - 1) / MC2_ERASE_SIZE;
	for (u32 b = first; b <= last && b < m_dirty[slot].size(); b++)
		m_dirty[slot][b] = 1;
	if (!m_dirty_any[slot])
		m_dirty_seconds[slot] = 0;
	m_dirty_any[slot] = true;
	m_idle_seconds[slot] = 0;
}

// Writes the dirty erase blocks back: one seek and one write per run of neighbouring blocks.
bool FileMemoryCard::FlushCache(uint slot, const char* why)
{
	if (!m_dirty_any[slot] || m_cache[slot].empty() || !m_file[slot])
		return true;
	OrbisMcdTimer timer;
	m_io_stats[slot].flush_calls++;
	const auto c0 = std::chrono::steady_clock::now();
	std::FILE* f = m_file[slot];
	std::vector<u8>& dirty = m_dirty[slot];
	const std::vector<u8>& image = m_cache[slot];
	u32 blocks = 0, runs = 0;
	size_t bytes = 0;
	bool ok = true;
	for (size_t b = 0; b < dirty.size();)
	{
		if (!dirty[b])
		{
			b++;
			continue;
		}
		size_t e = b;
		while (e < dirty.size() && dirty[e])
			e++;
		const size_t off = b * MC2_ERASE_SIZE;
		const size_t len = std::min(e * MC2_ERASE_SIZE, image.size()) - off;
		const bool seek_ok = FileSystem::FSeek64(f, static_cast<s64>(off), SEEK_SET) == 0;
		const bool write_ok = seek_ok && std::fwrite(&image[off], len, 1, f) == 1;
		if (!write_ok)
		{
			ok = false;
			std::printf("[mcd] slot %u: writeback failed at offset 0x%zx (%zu bytes), seek=%s\n", slot, off, len,
				seek_ok ? "ok" : "failed");
		}
		blocks += static_cast<u32>(e - b);
		runs++;
		bytes += len;
		b = e;
	}
	const bool flush_ok = std::fflush(f) == 0;
	if (!flush_ok)
	{
		ok = false;
		std::printf("[mcd] slot %u: fflush failed during writeback\n", slot);
	}
	if (ok)
	{
		std::fill(dirty.begin(), dirty.end(), 0);
		m_dirty_any[slot] = false;
	}
	else
	{
		// Keep all blocks dirty. Some writes may have reached the file before another failed;
		// replaying those blocks is safe and avoids losing the only RAM copy of the new data.
		m_dirty_any[slot] = true;
		m_idle_seconds[slot] = 0;
		m_dirty_seconds[slot] = 0;
		m_io_stats[slot].flush_failures++;
	}
	g_orbis_mcd_flush_kib.fetch_add(static_cast<u32>(bytes >> 10), std::memory_order_relaxed);
	std::printf("[mcd] slot %u: wrote back %u block(s) (%zu KiB) in %u write(s), %.1f ms (%s)%s\n", slot, blocks,
		bytes >> 10, runs, std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - c0).count(), why,
		ok ? "" : " -- WRITE FAILED");
	if (!ok)
		Host::ReportErrorAsync("Memory Card Write Failed", "Error writing the memory card file.");
	return ok;
}

// vk-285-31: once an emulated second (sioNextFrame). The first call after a write sees the second
// the write happened in, so two calls without writes in between mean a whole idle second.
void FileMemoryCard::NextFrame(uint slot)
{
	if (!m_dirty_any[slot])
		return;
	m_idle_seconds[slot]++;
	m_dirty_seconds[slot]++;
	if (m_idle_seconds[slot] >= 2)
		FlushCache(slot, "idle");
	else if (m_dirty_seconds[slot] >= 5)
		FlushCache(slot, "busy");
}

void FileMemoryCard::Close()
{
	for (int slot = 0; slot < 8; ++slot)
	{
		if (!m_file[slot])
			continue;

		// vk-285-31: the RAM image's changes first.
		const bool cache_flushed = FlushCache(slot, "close");
		u32 dirty_blocks = 0;
		for (const u8 dirty : m_dirty[slot])
			dirty_blocks += dirty != 0;
		Console.WriteLnFmt("[mcd] slot {} summary: {} size={} formatted={} cached={} reads={} read_failures={} writes={} write_failures={} erases={} erase_failures={} flushes={} flush_failures={} dirty_blocks={}",
			slot, Path::GetFileName(m_filenames[slot]), m_fileSize[slot], FileMcd_IsMemoryCardFormatted(m_file[slot]),
			!m_cache[slot].empty(), m_io_stats[slot].read_calls, m_io_stats[slot].read_failures,
			m_io_stats[slot].write_calls, m_io_stats[slot].write_failures, m_io_stats[slot].erase_calls,
			m_io_stats[slot].erase_failures, m_io_stats[slot].flush_calls, m_io_stats[slot].flush_failures, dirty_blocks);
		if (!cache_flushed)
			Console.Error("[mcd] slot %u: checksum sector left unchanged because dirty data did not flush", slot);
		if (!m_cache[slot].empty())
			LogCardContents(slot, m_cache[slot], "end");
		m_cache[slot] = {};
		m_dirty[slot] = {};
		m_cache_ok[slot] = false;
		g_orbis_mcd_cached.fetch_and(~(1 << slot), std::memory_order_relaxed);

		// Store checksum only when all changed cache blocks reached the file.
		if (!m_ispsx[slot] && cache_flushed)
		{
			if (FileSystem::FSeek64(m_file[slot], m_chkaddr, SEEK_SET) != 0 ||
				std::fwrite(&m_chksum[slot], sizeof(m_chksum[slot]), 1, m_file[slot]) != 1 || std::fflush(m_file[slot]) != 0)
			{
				Console.Error("[mcd] slot %u: checksum sector write failed", slot);
			}
		}
		m_io_stats[slot] = {};

		std::fclose(m_file[slot]);
		m_file[slot] = nullptr;

		if (m_filenames[slot].ends_with(".bin") || m_filenames[slot].ends_with(".mc2"))
		{
			const std::string name_in(m_filenames[slot] + 'x');
			if (ConvertRAWtoNoECC(name_in.c_str(), m_filenames[slot].c_str()))
				FileSystem::DeleteFilePath(name_in.c_str());
		}

		m_filenames[slot] = {};
		m_fileSize[slot] = -1;
	}
}

// Returns FALSE if the seek failed (is outside the bounds of the file).
bool FileMemoryCard::Seek(std::FILE* f, u32 adr)
{
	return (FileSystem::FSeek64(f, adr, SEEK_SET) == 0);
}

// returns FALSE if an error occurred (either permission denied or disk full)
bool FileMemoryCard::Create(const char* mcdFile, uint sizeInMB)
{
	//int enc[16] = {0x77,0x7f,0x7f,0x77,0x7f,0x7f,0x77,0x7f,0x7f,0x77,0x7f,0x7f,0,0,0,0};

	Console.WriteLn("(FileMcd) Creating new %uMB memory card: %s", sizeInMB, mcdFile);

	auto fp = FileSystem::OpenManagedCFile(mcdFile, "wb");
	if (!fp)
		return false;

	u8 buf[MC2_ERASE_SIZE];
	std::memset(buf, 0xff, sizeof(buf));

	for (uint i = 0; i < (MC2_MBSIZE * sizeInMB) / sizeof(buf); i++)
	{
		if (std::fwrite(buf, sizeof(buf), 1, fp.get()) != 1)
			return false;
	}
	return true;
}

s32 FileMemoryCard::IsPresent(uint slot)
{
	return m_file[slot] != nullptr;
}

void FileMemoryCard::GetSizeInfo(uint slot, McdSizeInfo& outways)
{
	outways.SectorSize = 512; // 0x0200
	outways.EraseBlockSizeInSectors = 16; // 0x0010
	outways.Xor = 18; // 0x12, XOR 02 00 00 10

	pxAssert(m_file[slot]);
	if (m_file[slot])
		outways.McdSizeInSectors = static_cast<u32>(m_fileSize[slot]) / (outways.SectorSize + outways.EraseBlockSizeInSectors);
	else
		outways.McdSizeInSectors = 0x4000;

	u8* pdata = (u8*)&outways.McdSizeInSectors;
	outways.Xor ^= pdata[0] ^ pdata[1] ^ pdata[2] ^ pdata[3];
}

bool FileMemoryCard::IsPSX(uint slot)
{
	return m_ispsx[slot];
}

s32 FileMemoryCard::Read(uint slot, u8* dest, u32 adr, int size)
{
	std::FILE* mcfp = m_file[slot];
	if (!mcfp)
	{
		DevCon.Error("(FileMcd) Ignoring attempted read from disabled slot.");
		memset(dest, 0, size);
		return 1;
	}
	OrbisMcdTimer timer; // vk-285-31
	g_orbis_mcd_reads.fetch_add(1, std::memory_order_relaxed);
	m_io_stats[slot].read_calls++;
	if (!m_cache[slot].empty())
	{
		if (size < 0 || static_cast<size_t>(adr) + static_cast<size_t>(size) > m_cache[slot].size())
		{
			m_io_stats[slot].read_failures++;
			Console.Error("[mcd] slot %u: cached read out of range address=0x%08X size=%d card_size=%zu", slot, adr, size,
				m_cache[slot].size());
			return 0;
		}
		std::memcpy(dest, &m_cache[slot][adr], size);
		return 1;
	}
	if (!Seek(mcfp, adr))
	{
		m_io_stats[slot].read_failures++;
		Console.Error("[mcd] slot %u: read seek failed address=0x%08X size=%d", slot, adr, size);
		return 0;
	}
	if (std::fread(dest, size, 1, mcfp) != 1)
	{
		m_io_stats[slot].read_failures++;
		Console.Error("[mcd] slot %u: file read failed address=0x%08X size=%d", slot, adr, size);
		return 0;
	}
	return 1;
}

s32 FileMemoryCard::Save(uint slot, const u8* src, u32 adr, int size)
{
	std::FILE* mcfp = m_file[slot];

	if (!mcfp)
	{
		DevCon.Error("(FileMcd) Ignoring attempted save/write to disabled slot.");
		return 1;
	}

	// vk-285-31: on the RAM image (loaded now if this card waited for its first write).
	OrbisMcdTimer timer;
	g_orbis_mcd_writes.fetch_add(1, std::memory_order_relaxed);
	m_io_stats[slot].write_calls++;
	if (m_cache[slot].empty() && m_cache_ok[slot])
		LoadCache(slot);
	if (!m_cache[slot].empty())
	{
		std::vector<u8>& image = m_cache[slot];
		if (size < 0 || static_cast<size_t>(adr) + static_cast<size_t>(size) > image.size())
		{
			m_io_stats[slot].write_failures++;
			Console.Error("[mcd] slot %u: cached write out of range address=0x%08X size=%d card_size=%zu", slot, adr, size,
				image.size());
			return 0;
		}
		if (static_cast<int>(m_currentdata.size()) < size)
			m_currentdata.resize(size);
		for (int i = 0; i < size; i++)
		{
			const u8 cur = image[adr + i];
			if ((cur & src[i]) != src[i])
				Console.Warning("(FileMcd) Warning: writing to uncleared data. (%d) [%08X]", slot, adr);
			m_currentdata[i] = cur & src[i];
		}
		if (adr == m_chkaddr)
			Console.Warning("(FileMcd) Warning: checksum sector overwritten. (%d)", slot);
		const u64* pdata = reinterpret_cast<const u64*>(m_currentdata.data());
		for (int i = 0; i < size / 8; i++)
			m_chksum[slot] ^= pdata[i];
		std::memcpy(&image[adr], m_currentdata.data(), size);
		MarkDirty(slot, adr, static_cast<u32>(size));
		return 1;
	}

	if (m_ispsx[slot])
	{
		if (static_cast<int>(m_currentdata.size()) < size)
			m_currentdata.resize(size);
		for (int i = 0; i < size; i++)
			m_currentdata[i] = src[i];
	}
	else
	{
		if (!Seek(mcfp, adr))
		{
			m_io_stats[slot].write_failures++;
			Console.Error("[mcd] slot %u: write readback seek failed address=0x%08X size=%d", slot, adr, size);
			return 0;
		}
		if (static_cast<int>(m_currentdata.size()) < size)
			m_currentdata.resize(size);

		const size_t read_result = std::fread(m_currentdata.data(), size, 1, mcfp);
		if (read_result == 0)
		{
			m_io_stats[slot].read_failures++;
			m_io_stats[slot].write_failures++;
			Console.Error("[mcd] slot %u: read-modify-write read failed address=0x%08X size=%d", slot, adr, size);
			Host::ReportErrorAsync("Memory Card Read Failed", "Error reading memory card.");
			return 0;
		}

		for (int i = 0; i < size; i++)
		{
			if ((m_currentdata[i] & src[i]) != src[i])
				Console.Warning("(FileMcd) Warning: writing to uncleared data. (%d) [%08X]", slot, adr);
			m_currentdata[i] &= src[i];
		}

		// Checksumness
		{
			if (adr == m_chkaddr)
				Console.Warning("(FileMcd) Warning: checksum sector overwritten. (%d)", slot);

			u64* pdata = (u64*)&m_currentdata[0];
			u32 loops = size / 8;

			for (u32 i = 0; i < loops; i++)
				m_chksum[slot] ^= pdata[i];
		}
	}

	if (!Seek(mcfp, adr))
	{
		m_io_stats[slot].write_failures++;
		Console.Error("[mcd] slot %u: write seek failed address=0x%08X size=%d", slot, adr, size);
		return 0;
	}

	if (std::fwrite(m_currentdata.data(), size, 1, mcfp) == 1)
	{
		static auto last = std::chrono::time_point<std::chrono::system_clock>();

		std::chrono::duration<float> elapsed = std::chrono::system_clock::now() - last;
		if (elapsed > std::chrono::seconds(5))
		{
			Host::AddIconOSDMessage(fmt::format("MemoryCardSave{}", slot), ICON_PF_MEMORY_CARD,
				fmt::format(TRANSLATE_FS("MemoryCard", "Memory Card '{}' was saved to storage."),
					Path::GetFileName(m_filenames[slot])),
				Host::OSD_INFO_DURATION);
			last = std::chrono::system_clock::now();
		}
		return 1;
	}

	m_io_stats[slot].write_failures++;
	Console.Error("[mcd] slot %u: file write failed address=0x%08X size=%d", slot, adr, size);
	return 0;
}

s32 FileMemoryCard::EraseBlock(uint slot, u32 adr)
{
	std::FILE* mcfp = m_file[slot];
	if (!mcfp)
	{
		DevCon.Error("MemoryCard: Ignoring erase for disabled slot.");
		return 1;
	}

	// vk-285-31: on the RAM image.
	OrbisMcdTimer timer;
	g_orbis_mcd_erases.fetch_add(1, std::memory_order_relaxed);
	m_io_stats[slot].erase_calls++;
	if (m_cache[slot].empty() && m_cache_ok[slot])
		LoadCache(slot);
	if (!m_cache[slot].empty())
	{
		if (static_cast<size_t>(adr) + MC2_ERASE_SIZE > m_cache[slot].size())
		{
			m_io_stats[slot].erase_failures++;
			Console.Error("[mcd] slot %u: cached erase out of range address=0x%08X card_size=%zu", slot, adr,
				m_cache[slot].size());
			return 0;
		}
		std::memset(&m_cache[slot][adr], 0xff, MC2_ERASE_SIZE);
		MarkDirty(slot, adr, MC2_ERASE_SIZE);
		return 1;
	}

	if (!Seek(mcfp, adr))
	{
		m_io_stats[slot].erase_failures++;
		Console.Error("[mcd] slot %u: erase seek failed address=0x%08X", slot, adr);
		return 0;
	}

	u8 buf[MC2_ERASE_SIZE];
	std::memset(buf, 0xff, sizeof(buf));
	if (std::fwrite(buf, sizeof(buf), 1, mcfp) == 1)
		return 1;

	m_io_stats[slot].erase_failures++;
	Console.Error("[mcd] slot %u: file erase write failed address=0x%08X", slot, adr);
	return 0;
}

u64 FileMemoryCard::GetCRC(uint slot)
{
	std::FILE* mcfp = m_file[slot];
	if (!mcfp)
		return 0;

	u64 retval = 0;

	if (m_ispsx[slot])
	{
		if (!Seek(mcfp, 0))
			return 0;

		const s64 mcfpsize = m_fileSize[slot];
		if (mcfpsize < 0)
			return 0;

		// Process the file in 4k chunks.  Speeds things up significantly.

		u64 buffer[528 * 8]; // use 528 (sector size), ensures even divisibility

		const uint filesize = static_cast<uint>(mcfpsize) / sizeof(buffer);
		for (uint i = filesize; i; --i)
		{
			if (std::fread(buffer, sizeof(buffer), 1, mcfp) != 1)
				return 0;

			for (uint t = 0; t < std::size(buffer); ++t)
				retval ^= buffer[t];
		}
	}
	else
	{
		retval = m_chksum[slot];
	}

	return retval;
}

// --------------------------------------------------------------------------------------
//  MemoryCard Component API Bindings
// --------------------------------------------------------------------------------------
namespace Mcd
{
	FileMemoryCard impl; // class-based implementations we refer to when API is invoked
	FolderMemoryCardAggregator implFolder;
}; // namespace Mcd

uint FileMcd_ConvertToSlot(uint port, uint slot)
{
	if (slot == 0)
		return port;
	if (port == 0)
		return slot + 1; // multitap 1
	return slot + 4; // multitap 2
}

void FileMcd_SetType()
{
	// detect inserted memory card types
	for (uint slot = 0; slot < 8; ++slot)
	{
		if (EmuConfig.Mcd[slot].Filename.empty())
		{
			EmuConfig.Mcd[slot].Type = MemoryCardType::Empty;
		}
		else if (EmuConfig.Mcd[slot].Enabled)
		{
			MemoryCardType type = MemoryCardType::File; // default to file if we can't find anything at the path so it gets auto-generated

			const std::string path(EmuConfig.FullpathToMcd(slot));
			if (FileSystem::DirectoryExists(path.c_str()))
				type = MemoryCardType::Folder;

			EmuConfig.Mcd[slot].Type = type;
		}
	}
}

void FileMcd_EmuOpen()
{
	if (FileMcd_Open)
		return;
	FileMcd_Open = true;


	Mcd::impl.Open();
	Mcd::implFolder.SetFiltering(true);
	Mcd::implFolder.Open();
}

void FileMcd_EmuClose()
{
	if (!FileMcd_Open)
		return;
	FileMcd_Open = false;
	Mcd::implFolder.Close();
	Mcd::impl.Close();
}

void FileMcd_CancelEject()
{
	AutoEject::ClearAll();
}

void FileMcd_Reopen(std::string new_serial)
{
	Console.WriteLn("Reopening memory cards...");
	FileMcd_EmuClose();
	FileMcd_SetType();
	sioSetGameSerial(new_serial);
	FileMcd_EmuOpen();
}

static bool FileMcd_IsAutoEjecting()
{
	for (size_t port = 0; port < SIO::PORTS; ++port)
	{
		for (size_t slot = 0; slot < SIO::SLOTS; ++slot)
		{
			if (mcds[port][slot].autoEjectTicks > 0)
			{
				return true; // Auto-eject is active
			}
		}
	}
	return false; // No auto-eject active
}

void FileMcd_Swap()
{
	if (MemcardBusy::IsBusy())
	{
		Host::AddIconOSDMessage("MemoryCardSwap_Busy", ICON_PF_MEMORY_CARD, TRANSLATE_SV("MemoryCardSwap_Busy", "Memory cards are busy. Can't swap right now."));
		return;
	}

	// Check if auto-eject is active
	if (FileMcd_IsAutoEjecting())
	{
		Host::AddIconOSDMessage("MemoryCardSwap_AutoEject", ICON_PF_MEMORY_CARD, TRANSLATE_SV("MemoryCardSwap_AutoEject", "Memory cards are being auto-ejected. Can't swap right now."));
		return;
	}

	const std::string card1Filename = Host::GetStringSettingValue("MemoryCards", "Slot1_Filename");
	const std::string card2Filename = Host::GetStringSettingValue("MemoryCards", "Slot2_Filename");

	// Copy each McdOptions to local memory
	Pcsx2Config::McdOptions firstSlot = EmuConfig.Mcd[0];
	Pcsx2Config::McdOptions secondSlot = EmuConfig.Mcd[1];

	if (!firstSlot.Enabled || !secondSlot.Enabled || card1Filename.empty() || card2Filename.empty())
	{
		Host::AddIconOSDMessage("MemoryCardSwap_EmptySlot", ICON_PF_MEMORY_CARD, TRANSLATE_SV("MemoryCard_EmptySlot", "Both slots must have a card selected to swap."));
		return;
	}

	// Swap them
	Host::SetBaseStringSettingValue("MemoryCards", "Slot1_Filename", card2Filename.c_str());
	Host::SetBaseStringSettingValue("MemoryCards", "Slot2_Filename", card1Filename.c_str());
	Host::CommitBaseSettingChanges();
	VMManager::ApplySettings();
	EmuConfig.Mcd[0] = secondSlot;
	EmuConfig.Mcd[1] = firstSlot;

	// Reopen them
	FileMcd_EmuClose();
	FileMcd_SetType();
	FileMcd_EmuOpen();
	AutoEject::SetAll();
	Host::AddIconOSDMessage("MemoryCardSwap", ICON_PF_MEMORY_CARD, fmt::format(TRANSLATE_FS("MemoryCardSwap", "Memory Cards have been swapped.\nSlot 1: {}\nSlot 2: {}"), EmuConfig.Mcd[0].Filename, EmuConfig.Mcd[1].Filename), Host::OSD_INFO_DURATION);
}

s32 FileMcd_IsPresent(uint port, uint slot)
{
	const uint combinedSlot = FileMcd_ConvertToSlot(port, slot);
	switch (EmuConfig.Mcd[combinedSlot].Type)
	{
		case MemoryCardType::File:
			return Mcd::impl.IsPresent(combinedSlot);
		case MemoryCardType::Folder:
			return Mcd::implFolder.IsPresent(combinedSlot);
		default:
			return false;
	}
}

void FileMcd_GetSizeInfo(uint port, uint slot, McdSizeInfo* outways)
{
	const uint combinedSlot = FileMcd_ConvertToSlot(port, slot);
	switch (EmuConfig.Mcd[combinedSlot].Type)
	{
		case MemoryCardType::File:
			Mcd::impl.GetSizeInfo(combinedSlot, *outways);
			break;
		case MemoryCardType::Folder:
			Mcd::implFolder.GetSizeInfo(combinedSlot, *outways);
			break;
		default:
			return;
	}
}

bool FileMcd_IsPSX(uint port, uint slot)
{
	const uint combinedSlot = FileMcd_ConvertToSlot(port, slot);
	switch (EmuConfig.Mcd[combinedSlot].Type)
	{
		case MemoryCardType::File:
			return Mcd::impl.IsPSX(combinedSlot);
		case MemoryCardType::Folder:
			return Mcd::implFolder.IsPSX(combinedSlot);
		default:
			return false;
	}
}

s32 FileMcd_Read(uint port, uint slot, u8* dest, u32 adr, int size)
{
	const uint combinedSlot = FileMcd_ConvertToSlot(port, slot);
	switch (EmuConfig.Mcd[combinedSlot].Type)
	{
		case MemoryCardType::File:
			return Mcd::impl.Read(combinedSlot, dest, adr, size);
		case MemoryCardType::Folder:
			return Mcd::implFolder.Read(combinedSlot, dest, adr, size);
		default:
			return 0;
	}
}

s32 FileMcd_Save(uint port, uint slot, const u8* src, u32 adr, int size)
{
	const uint combinedSlot = FileMcd_ConvertToSlot(port, slot);
	switch (EmuConfig.Mcd[combinedSlot].Type)
	{
		case MemoryCardType::File:
			return Mcd::impl.Save(combinedSlot, src, adr, size);
		case MemoryCardType::Folder:
			return Mcd::implFolder.Save(combinedSlot, src, adr, size);
		default:
			return 0;
	}
}

s32 FileMcd_EraseBlock(uint port, uint slot, u32 adr)
{
	const uint combinedSlot = FileMcd_ConvertToSlot(port, slot);
	switch (EmuConfig.Mcd[combinedSlot].Type)
	{
		case MemoryCardType::File:
			return Mcd::impl.EraseBlock(combinedSlot, adr);
		case MemoryCardType::Folder:
			return Mcd::implFolder.EraseBlock(combinedSlot, adr);
		default:
			return 0;
	}
}

u64 FileMcd_GetCRC(uint port, uint slot)
{
	const uint combinedSlot = FileMcd_ConvertToSlot(port, slot);
	switch (EmuConfig.Mcd[combinedSlot].Type)
	{
		case MemoryCardType::File:
			return Mcd::impl.GetCRC(combinedSlot);
		case MemoryCardType::Folder:
			return Mcd::implFolder.GetCRC(combinedSlot);
		default:
			return 0;
	}
}

void FileMcd_NextFrame(uint port, uint slot)
{
	const uint combinedSlot = FileMcd_ConvertToSlot(port, slot);
	switch (EmuConfig.Mcd[combinedSlot].Type)
	{
		case MemoryCardType::File: // vk-285-31: writes the RAM image back once the card is idle (once a second)
			Mcd::impl.NextFrame(combinedSlot);
			break;
		case MemoryCardType::Folder:
			Mcd::implFolder.NextFrame(combinedSlot);
			break;
		default:
			return;
	}
}

int FileMcd_ReIndex(uint port, uint slot, const std::string& filter)
{
	const int combinedSlot = FileMcd_ConvertToSlot(port, slot);

	switch (EmuConfig.Mcd[combinedSlot].Type)
	{
		//case MemoryCardType::File:
		//	return Mcd::impl.ReIndex( combinedSlot, filter );
		//	break;
		case MemoryCardType::Folder:
			if (!Mcd::implFolder.ReIndex(combinedSlot, true, filter))
				return -1;
			break;
		default:
			return -1;
			break;
	}

	return combinedSlot;
}

// --------------------------------------------------------------------------------------
//  Library API Implementations
// --------------------------------------------------------------------------------------

static MemoryCardFileType GetMemoryCardFileTypeFromSize(s64 size)
{
	// Handle both ecc and non ecc versions
	if (size == (8 * MC2_MBSIZE) || size == _8mb)
		return MemoryCardFileType::PS2_8MB;
	else if (size == (16 * MC2_MBSIZE) || size == _16mb)
		return MemoryCardFileType::PS2_16MB;
	else if (size == (32 * MC2_MBSIZE) || size == _32mb)
		return MemoryCardFileType::PS2_32MB;
	else if (size == (64 * MC2_MBSIZE) || size == _64mb)
		return MemoryCardFileType::PS2_64MB;
	else if (size == MCD_SIZE)
		return MemoryCardFileType::PS1;
	else
		return MemoryCardFileType::Unknown;
}

static bool FileMcd_IsFolder(const std::string& path)
{
	const std::string superblock_path(Path::Combine(path, s_folder_mem_card_id_file));
	return FileSystem::FileExists(superblock_path.c_str());
}

bool FileMcd_IsMemoryCardFormatted(const std::string& path)
{
	auto fp = FileSystem::OpenManagedSharedCFile(path.c_str(), "rb", FileSystem::FileShareMode::DenyNone);
	if (!fp)
		return false;

	return FileMcd_IsMemoryCardFormatted(fp.get());
}

bool FileMcd_IsMemoryCardFormatted(std::FILE* fp)
{
	static const char formatted_psx[] = "MC";
	static const char formatted_string[] = "Sony PS2 Memory Card Format";
	static constexpr size_t read_length = sizeof(formatted_string) - 1;

	const s64 pos = FileSystem::FTell64(fp);

	u8 data[read_length];
	const bool okay = (FileSystem::FSeek64(fp, 0, SEEK_SET) == 0 && std::fread(data, read_length, 1, fp) == 1);
	FileSystem::FSeek64(fp, pos, SEEK_SET);
	if (!okay)
		return false;

	return (std::memcmp(data, formatted_string, sizeof(formatted_string) - 1) == 0 ||
			std::memcmp(data, formatted_psx, sizeof(formatted_psx) - 1) == 0);
}

std::vector<AvailableMcdInfo> FileMcd_GetAvailableCards(bool include_in_use_cards)
{
	std::vector<FILESYSTEM_FIND_DATA> files;
	FileSystem::FindFiles(EmuFolders::MemoryCards.c_str(), "*",
		FILESYSTEM_FIND_FILES | FILESYSTEM_FIND_FOLDERS | FILESYSTEM_FIND_HIDDEN_FILES, &files);

	std::vector<AvailableMcdInfo> mcds;
	mcds.reserve(files.size());

	for (FILESYSTEM_FIND_DATA& fd : files)
	{
		std::string basename(Path::GetFileName(fd.FileName));
		if (!include_in_use_cards)
		{
			bool in_use = false;
			for (size_t i = 0; i < std::size(EmuConfig.Mcd); i++)
			{
				if (EmuConfig.Mcd[i].Filename == basename)
				{
					in_use = true;
					break;
				}
			}
			if (in_use)
				continue;
		}

		// We only want relevant file types.
		if (!(fd.FileName.ends_with(".ps2") || fd.FileName.ends_with(".mcr") ||
				fd.FileName.ends_with(".mcd") || fd.FileName.ends_with(".bin") ||
				fd.FileName.ends_with(".mc2")))
			continue;

		if (fd.Attributes & FILESYSTEM_FILE_ATTRIBUTE_DIRECTORY)
		{
			if (!FileMcd_IsFolder(fd.FileName))
				continue;

			FolderMemoryCard sourceFolderMemoryCard;
			Pcsx2Config::McdOptions config;
			config.Enabled = true;
			config.Type = MemoryCardType::Folder;
			sourceFolderMemoryCard.Open(fd.FileName, config, (8 * 1024 * 1024) / FolderMemoryCard::ClusterSize, true, "");

			mcds.push_back({std::move(basename), std::move(fd.FileName), fd.ModificationTime,
				MemoryCardType::Folder, MemoryCardFileType::Unknown, 0u, sourceFolderMemoryCard.IsFormatted()});
			sourceFolderMemoryCard.Close(false);
		}
		else
		{
			if (fd.Size < MCD_SIZE)
				continue;

			const bool formatted = FileMcd_IsMemoryCardFormatted(fd.FileName);
			mcds.push_back({std::move(basename), std::move(fd.FileName), fd.ModificationTime,
				MemoryCardType::File, GetMemoryCardFileTypeFromSize(fd.Size),
				static_cast<u32>(fd.Size), formatted});
		}
	}

	std::sort(mcds.begin(), mcds.end(), [](auto& a, auto& b) { return a.name < b.name; });
	return mcds;
}

std::optional<AvailableMcdInfo> FileMcd_GetCardInfo(const std::string_view name)
{
	std::optional<AvailableMcdInfo> ret;

	std::string basename(name);
	std::string path(Path::Combine(EmuFolders::MemoryCards, basename));

	FILESYSTEM_STAT_DATA sd;
	if (!FileSystem::StatFile(path.c_str(), &sd))
		return ret;

	if (sd.Attributes & FILESYSTEM_FILE_ATTRIBUTE_DIRECTORY)
	{
		if (FileMcd_IsFolder(path))
		{
			ret = {std::move(basename), std::move(path), sd.ModificationTime,
				MemoryCardType::Folder, MemoryCardFileType::Unknown, 0u, true};
		}
	}
	else
	{
		if (sd.Size >= MCD_SIZE)
		{
			const bool formatted = FileMcd_IsMemoryCardFormatted(path);
			ret = {std::move(basename), std::move(path), sd.ModificationTime,
				MemoryCardType::File, GetMemoryCardFileTypeFromSize(sd.Size),
				static_cast<u32>(sd.Size), formatted};
		}
	}

	return ret;
}

bool FileMcd_CreateNewCard(const std::string_view name, MemoryCardType type, MemoryCardFileType file_type)
{
	const std::string full_path(Path::Combine(EmuFolders::MemoryCards, name));

	if (type == MemoryCardType::Folder)
	{
		Console.WriteLn("(FileMcd) Creating new PS2 folder memory card: '%.*s'", static_cast<int>(name.size()), name.data());

		Error error;
		if (!FileSystem::CreateDirectoryPath(full_path.c_str(), false, &error))
		{
			Host::ReportErrorAsync("Memory Card Creation Failed",
				fmt::format("Failed to create directory. The error was:\n{}", error.GetDescription()));
			return false;
		}

		// write the superblock
		auto fp = FileSystem::OpenManagedCFile(Path::Combine(full_path, s_folder_mem_card_id_file).c_str(), "wb", &error);
		if (!fp)
		{
			Host::ReportErrorAsync("Memory Card Creation Failed", fmt::format("Failed to create superblock. The error was:\n{}", error.GetDescription()));
			return false;
		}

		return true;
	}

	if (type == MemoryCardType::File)
	{
		if (file_type <= MemoryCardFileType::Unknown || file_type >= MemoryCardFileType::MaxCount)
			return false;

		static constexpr std::array<u32, static_cast<size_t>(MemoryCardFileType::MaxCount)> sizes = {{0, 8 * MC2_MBSIZE, 16 * MC2_MBSIZE, 32 * MC2_MBSIZE, 64 * MC2_MBSIZE, MCD_SIZE}};

		const bool isPSX = (type == MemoryCardType::File && file_type == MemoryCardFileType::PS1);
		const u32 size = sizes[static_cast<u32>(file_type)];
		if (!isPSX && size == 0)
			return false;

		Error error;
		auto fp = FileSystem::OpenManagedCFile(full_path.c_str(), "wb", &error);
		if (!fp)
		{
			Host::ReportErrorAsync(TRANSLATE_SV("MemoryCard", "Memory Card Creation Failed"),
				fmt::format(TRANSLATE_FS("MemoryCard", "Failed to create memory card. The error was:\n{}"), error.GetDescription()));
			return false;
		}

		if (!isPSX)
		{
			Console.WriteLn("(FileMcd) Creating new PS2 %uMB memory card: '%s'", size / MC2_MBSIZE, full_path.c_str());

			// PS2 Memory Card
			u8 buf[MC2_ERASE_SIZE];
			std::memset(buf, 0xff, sizeof(buf));

			const u32 count = size / sizeof(buf);
			for (uint i = 0; i < count; i++)
			{
				if (std::fwrite(buf, sizeof(buf), 1, fp.get()) != 1)
				{
					Host::ReportErrorAsync("Memory Card Creation Failed",
						fmt::format("Failed to write memory card file:\n{}", full_path));
					return false;
				}
			}

			return true;
		}
		else
		{
			Console.WriteLn("(FileMcd) Creating new PSX 128 KiB memory card: '%s'", full_path.c_str());

			// PSX Memory Card; 8192 is the size in bytes of a single block of a PSX memory card (8 KiB).
			u8 buf[8192];
			std::memset(buf, 0xff, sizeof(buf));

			// PSX cards consist of 16 blocks, each 8 KiB in size.
			for (uint i = 0; i < 16; i++)
			{
				if (std::fwrite(buf, sizeof(buf), 1, fp.get()) != 1)
				{
					Host::ReportErrorAsync("Memory Card Creation Failed",
						fmt::format("Failed to write memory card file:\n{}", full_path));
					return false;
				}
			}

			return true;
		}
	}

	return false;
}

bool FileMcd_RenameCard(const std::string_view name, const std::string_view new_name)
{
	const std::string name_path(Path::Combine(EmuFolders::MemoryCards, name));
	const std::string new_name_path(Path::Combine(EmuFolders::MemoryCards, new_name));

	FILESYSTEM_STAT_DATA sd, new_sd;
	if (!FileSystem::StatFile(name_path.c_str(), &sd) || FileSystem::StatFile(new_name_path.c_str(), &new_sd))
	{
		Console.Error("(FileMcd) New name already exists, or old name does not");
		return false;
	}

	Console.WriteLn("(FileMcd) Renaming memory card '%.*s' to '%.*s'",
		static_cast<int>(name.size()), name.data(),
		static_cast<int>(new_name.size()), new_name.data());

	if (!FileSystem::RenamePath(name_path.c_str(), new_name_path.c_str()))
	{
		Console.Error("(FileMcd) Failed to rename '%s' to '%s'", name_path.c_str(), new_name_path.c_str());
		return false;
	}

	return true;
}

bool FileMcd_DeleteCard(const std::string_view name)
{
	const std::string name_path(Path::Combine(EmuFolders::MemoryCards, name));

	FILESYSTEM_STAT_DATA sd;
	if (!FileSystem::StatFile(name_path.c_str(), &sd))
	{
		Console.Error("(FileMcd) Can't stat '%s' for deletion", name_path.c_str());
		return false;
	}

	Console.WriteLn("(FileMcd) Deleting memory card '%.*s'", static_cast<int>(name.size()), name.data());

	if (sd.Attributes & FILESYSTEM_FILE_ATTRIBUTE_DIRECTORY)
	{
		// must be a folder memcard, so do a recursive delete (scary)
		if (!FileSystem::RecursiveDeleteDirectory(name_path.c_str()))
		{
			Console.Error("(FileMcd) Failed to recursively delete '%s'", name_path.c_str());
			return false;
		}
	}
	else
	{
		if (!FileSystem::DeleteFilePath(name_path.c_str()))
		{
			Console.Error("(FileMcd) Failed to delete file '%s'", name_path.c_str());
			return false;
		}
	}

	return true;
}
