// SPDX-License-Identifier: GPL-3.0+
// (AI-assisted) Atomic CPU-to-GS menu snapshot, independent of renderer headers.
#pragma once

#include <algorithm>
#include <cstdint>

namespace PS4GameMenu
{
	// Rows of the L3+R3 pause panel. The CPU thread (input) and the GS thread
	// (drawing) both use these, so the two always agree on what each row is.
	enum InGameMenuRow : unsigned
	{
		InGameRowResume = 0,
		InGameRowQuickSave,
		InGameRowQuickLoad,
		InGameRowResolution,
		InGameRowAspect,
		InGameRowOverlay,
		InGameRowMainMenu,
		InGameRowExit,
		InGameRowCount,
	};

	// Colour of a quick save/load status line drawn under its row.
	enum InGameMenuTone : unsigned
	{
		InGameToneNormal = 0,
		InGameToneBusy,
		InGameToneGood,
		InGameToneError,
	};

	struct InGameMenuState
	{
		bool visible;
		unsigned selected;
		unsigned upscale;
		unsigned max_upscale;
		unsigned aspect;
		bool show_overlay;
	};

	constexpr std::uint32_t PackInGameMenuState(InGameMenuState value)
	{
		if (!value.visible)
			return 0;
		const unsigned limit = std::clamp(value.max_upscale, 1u, 4u);
		return (std::min(value.selected, InGameRowCount - 1u) + 1u) |
			(std::clamp(value.upscale, 1u, limit) << 8) |
			(limit << 12) |
			(std::min(value.aspect, 4u) << 16) |
			(value.show_overlay ? (1u << 20) : 0u);
	}

	constexpr InGameMenuState UnpackInGameMenuState(std::uint32_t value)
	{
		// These fields occupy FOUR bits, not eight. Reading 0xff here mixed the
		// resolution with its limit (1 became 65), and aspect with overlay (0 became 16).
		const unsigned selection = value & 0xffu;
		const unsigned limit = std::clamp((value >> 12) & 0x0fu, 1u, 4u);
		return {selection != 0, selection ? std::min(selection - 1u, InGameRowCount - 1u) : 0u,
			std::clamp((value >> 8) & 0x0fu, 1u, limit), limit,
			std::min((value >> 16) & 0x0fu, 4u), (value & (1u << 20)) != 0};
	}
} // namespace PS4GameMenu
