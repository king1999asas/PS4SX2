// SPDX-License-Identifier: GPL-3.0+
#pragma once
// Cheats from gamehacking.org for the "Buscar trucos en internet" menu entry.
//
// The site exports a game's codes as a PCSX2 .pnach (POST /inc/sub.exportCodes.php
// with the site's own game id). Games are looked up by serial in a table taken from
// the site's PS2 list (GameHackingPS2Table.h), so no search page has to be parsed.
//
// Some exported codes are not usable as they are: codes typed into the site as
// Action Replay v1 are often still encrypted after the export (type 9 hooks, E codes
// with a size nibble of E, D codes with a non-zero top byte). Every section is checked
// against the CodeBreaker raw code types PCSX2's "extended" patches run; a section with
// any malformed line is left out whole, so a half-decoded code never reaches the game.

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <set>
#include <string>
#include <vector>

namespace PS4GameHacking
{
	struct Entry
	{
		const char* serial; // as the site lists it, e.g. "SLES-55016"
		uint32_t game_id;   // gamehacking.org/game/<id>
		uint32_t crc;       // 0 when the site gives none
	};
} // namespace PS4GameHacking

#include "GameHackingPS2Table.h"

namespace PS4GameHacking
{
	constexpr const char* ExportUrl = "https://gamehacking.org/inc/sub.exportCodes.php";
	constexpr unsigned PS2SystemId = 16;

	// The entry for this disc: one whose CRC matches, else the one without a CRC (the table
	// keeps one per serial). Entries tied to another CRC are another version of the game.
	inline const Entry* Find(const std::string& serial, uint32_t crc)
	{
		const Entry* best = nullptr;
		bool best_crc = false;
		for (const Entry& entry : Table)
		{
			if (serial != entry.serial)
				continue;
			const bool crc_match = entry.crc != 0 && entry.crc == crc;
			if (entry.crc != 0 && !crc_match)
				continue;
			if (!best || (crc_match && !best_crc))
			{
				best = &entry;
				best_crc = crc_match;
			}
		}
		return best;
	}

	inline std::string FormEscape(const std::string& value)
	{
		static const char hex[] = "0123456789ABCDEF";
		std::string out;
		for (const unsigned char c : value)
		{
			if (std::isalnum(c) || c == '-' || c == '_' || c == '.' || c == '~')
				out += static_cast<char>(c);
			else
			{
				out += '%';
				out += hex[c >> 4];
				out += hex[c & 15];
			}
		}
		return out;
	}

	inline std::string ExportBody(const Entry& entry, const std::string& file_stem)
	{
		return "format=PCSX2&codID=&filename=" + FormEscape(file_stem) + "&sysID=" + std::to_string(PS2SystemId) +
		       "&gamID=" + std::to_string(entry.game_id) + "&download=true";
	}

	namespace Detail
	{
		struct Code
		{
			uint32_t address, value;
		};

		inline bool EeAddress(uint32_t word)
		{
			return (word & 0x0FFFFFFFu) < 0x02000000u; // 32 MB of EE RAM
		}

		// CodeBreaker raw types, as PCSX2 runs "extended" patches.
		inline bool ValidCodes(const std::vector<Code>& codes)
		{
			size_t i = 0;
			while (i < codes.size())
			{
				const Code& c = codes[i];
				const uint32_t type = c.address >> 28;
				const uint32_t address = c.address & 0x0FFFFFFFu;
				const auto next = [&](size_t n) { return i + n < codes.size(); };
				switch (type)
				{
					case 0x0: // 8-bit write
						if (!EeAddress(address) || (c.value & ~0xFFu))
							return false;
						i++;
						break;
					case 0x1: // 16-bit write
						if (!EeAddress(address) || (address & 1) || (c.value & ~0xFFFFu))
							return false;
						i++;
						break;
					case 0x2: // 32-bit write
						if (!EeAddress(address) || (address & 3))
							return false;
						i++;
						break;
					case 0x3: // increment / decrement: 30s0vvvv 0aaaaaaa [+ vvvvvvvv for 32-bit]
					{
						const uint32_t sub = (c.address >> 20) & 0xF;
						if ((c.address & 0x0F000000u) || !EeAddress(c.value) || (c.value >> 28))
							return false;
						if (sub <= 3)
							i++;
						else if ((sub == 4 || sub == 5) && next(1))
							i += 2;
						else
							return false;
						break;
					}
					case 0x4: // serial write: 4aaaaaaa nnnnssss / vvvvvvvv iiiiiiii
						if (!EeAddress(address) || (address & 3) || !next(1) || (c.value >> 16) == 0)
							return false;
						i += 2;
						break;
					case 0x5: // copy: 5aaaaaaa nnnnnnnn / 0bbbbbbb 00000000
						if (!EeAddress(address) || !next(1) || (codes[i + 1].address >> 28) || !EeAddress(codes[i + 1].address))
							return false;
						i += 2;
						break;
					case 0x6: // pointer write: 6aaaaaaa vvvvvvvv / 000tnnnn iiiiiiii / [iiiiiiii iiiiiiii]...
					{
						if (!EeAddress(address) || !next(1))
							return false;
						const uint32_t info = codes[i + 1].address;
						const uint32_t levels = info & 0xFFFF;
						if ((info & 0xFFF00000u) || ((info >> 16) & 0xF) > 2 || levels == 0 || levels > 16)
							return false;
						const size_t lines = 2 + levels / 2;
						if (i + lines > codes.size())
							return false;
						i += lines;
						break;
					}
					case 0x7: // boolean: 7aaaaaaa 00tyvvvv
						if (!EeAddress(address) || (c.value >> 24))
							return false;
						i++;
						break;
					case 0xC: // all-following condition: Caaaaaaa vvvvvvvv
						if (!EeAddress(address) || (address & 3))
							return false;
						i++;
						break;
					case 0xD: // joker: Daaaaaaa 00tyvvvv
						if (!EeAddress(address) || (c.value >> 24) || ((c.value >> 16) & 0xF) > 1)
							return false;
						i++;
						break;
					case 0xE: // multi-line condition: Ezyyvvvv taaaaaaa
						if (((c.address >> 24) & 0xF) > 1 || (c.value >> 28) > 7 || !EeAddress(c.value) ||
							((c.address >> 16) & 0xFF) == 0)
							return false;
						i++;
						break;
					default: // 8, 9 (hook), A, B, F (master): not run by PCSX2 or still encrypted
						return false;
				}
			}
			return !codes.empty();
		}

		inline bool ParseHex(const std::string& text, uint32_t* out)
		{
			if (text.empty() || text.size() > 8)
				return false;
			char* end = nullptr;
			const unsigned long value = std::strtoul(text.c_str(), &end, 16);
			if (!end || *end)
				return false;
			*out = static_cast<uint32_t>(value);
			return true;
		}

		inline std::string Trim(std::string value)
		{
			while (!value.empty() && (value.back() == '\r' || value.back() == ' ' || value.back() == '\t'))
				value.pop_back();
			size_t start = 0;
			while (start < value.size() && (value[start] == ' ' || value[start] == '\t'))
				start++;
			return value.substr(start);
		}

		struct Section
		{
			std::string name, author, description;
			std::vector<std::string> lines; // normalized patch= lines
			std::vector<Code> codes;
			bool valid = true;
		};
	} // namespace Detail

	struct CleanResult
	{
		std::string pnach;
		unsigned kept = 0, dropped = 0;
	};

	// Rewrites the site's export as a pnach with only well-formed sections. Names already
	// used by another cheat file of the game get " (gamehacking)", and a repeated name with
	// other codes gets " (2)", " (3)"..., because PCSX2 enables every group of a given name.
	inline CleanResult Clean(const std::string& text, const std::string& title, const std::set<std::string>& taken)
	{
		using namespace Detail;
		std::vector<Section> sections;
		size_t pos = 0;
		while (pos <= text.size())
		{
			size_t end = text.find('\n', pos);
			if (end == std::string::npos)
				end = text.size();
			const std::string line = Trim(text.substr(pos, end - pos));
			pos = end + 1;
			if (line.empty() || line.rfind("//", 0) == 0)
				continue;
			if (line.front() == '[' && line.back() == ']')
			{
				sections.emplace_back();
				sections.back().name = Trim(line.substr(1, line.size() - 2));
				continue;
			}
			if (sections.empty())
				continue;
			Section& section = sections.back();
			if (line.rfind("author=", 0) == 0)
				section.author = line.substr(7);
			else if (line.rfind("description=", 0) == 0)
				section.description = line.substr(12);
			else if (line.rfind("patch=", 0) == 0)
			{
				// patch=1,EE,ADDRESS,extended,VALUE
				std::vector<std::string> fields;
				size_t start = 6;
				for (;;)
				{
					const size_t comma = line.find(',', start);
					fields.push_back(Trim(line.substr(start, comma == std::string::npos ? std::string::npos : comma - start)));
					if (comma == std::string::npos)
						break;
					start = comma + 1;
				}
				uint32_t address = 0, value = 0;
				if (fields.size() != 5 || (fields[0] != "0" && fields[0] != "1") || fields[1] != "EE" ||
					fields[3] != "extended" || !ParseHex(fields[2], &address) || !ParseHex(fields[4], &value))
				{
					section.valid = false;
					continue;
				}
				char normalized[64];
				std::snprintf(normalized, sizeof(normalized), "patch=%s,EE,%08X,extended,%08X", fields[0].c_str(), address,
					value);
				section.lines.emplace_back(normalized);
				section.codes.push_back({address, value});
			}
		}

		CleanResult result;
		std::set<std::string> used = taken;
		std::vector<const Section*> written;
		std::string body;
		for (const Section& section : sections)
		{
			std::string lower = section.name;
			std::transform(lower.begin(), lower.end(), lower.begin(), [](unsigned char c) { return std::tolower(c); });
			const bool master = lower.find("must be on") != std::string::npos || lower.rfind("(m)", 0) == 0 ||
			                    lower.find("master code") != std::string::npos;
			if (section.name.empty() || master || !section.valid || !ValidCodes(section.codes))
			{
				result.dropped++;
				continue;
			}
			// The same codes under the same name twice (one per device format): keep one.
			if (std::any_of(written.begin(), written.end(), [&](const Section* other) {
					return other->name == section.name && other->lines == section.lines;
				}))
				continue;
			std::string name = section.name;
			if (taken.count(name))
				name += " (gamehacking)";
			for (int n = 2; used.count(name); ++n)
				name = section.name + (taken.count(section.name) ? " (gamehacking " : " (") + std::to_string(n) + ")";
			used.insert(name);
			written.push_back(&section);
			body += "\n[" + name + "]\n";
			if (!section.author.empty())
				body += "author=" + section.author + "\n";
			body += "description=gamehacking.org" + (section.description.empty() ? std::string() : ": " + section.description) + "\n";
			for (const std::string& patch : section.lines)
				body += patch + "\n";
			result.kept++;
		}
		if (result.kept)
			result.pnach = "gametitle=" + title + "\n" + body;
		return result;
	}

	// Cheat names in a pnach text ("[name]" lines), to avoid reusing them.
	inline std::set<std::string> SectionNames(const std::string& text)
	{
		std::set<std::string> names;
		size_t pos = 0;
		while (pos < text.size())
		{
			size_t end = text.find('\n', pos);
			if (end == std::string::npos)
				end = text.size();
			const std::string line = Detail::Trim(text.substr(pos, end - pos));
			if (line.size() > 2 && line.front() == '[' && line.back() == ']')
				names.insert(Detail::Trim(line.substr(1, line.size() - 2)));
			pos = end + 1;
		}
		return names;
	}
} // namespace PS4GameHacking
