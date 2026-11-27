// SPDX-License-Identifier: GPL-3.0+
#pragma once
// PS4 port: a trace of how a memory card is used, for the "error al guardar" hunt.
// Every card command is summed up per selected sector (one line per sector: what was
// read, written, erased), and the SIF DMA tags in both directions are listed while the
// card is in use, so a session log shows whether a save's data reached the card.
#include "common/Pcsx2Defs.h"

namespace PS4McdTrace
{
	// After a memory card command has been handled by Sio2::Memcard.
	void Command(u32 port, u32 slot, u8 command, u8 first_byte, u32 sector, bool ejected);
	// A SIF DMA tag: what ("sif1 ee", "sif1 iop", "sif0 iop"...), its address and its size in bytes.
	void Sif(const char* what, u32 address, u32 bytes, u32 id);
} // namespace PS4McdTrace
