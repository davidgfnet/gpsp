/* gameplaySP
 *
 * Copyright (C) 2006 Exophase <exophase@gmail.com>
 * Copyright (C) 2024 David Guillen Fandos <david@davidgf.net>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of
 * the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

#ifndef CPU_DYNAREC_HH
#define CPU_DYNAREC_HH

#include "decoder.h"

class ThumbInst : public ThumbInstDec {
public:
  ThumbInst(u32 pc, u16 opcode, u16 flag_status)
   : ThumbInstDec(opcode), flag_status(flag_status), pc(pc) {}

  bool gen_flag_n() const { return flag_status & 0x8; }
  bool gen_flag_z() const { return flag_status & 0x4; }
  bool gen_flag_c() const { return flag_status & 0x2; }
  bool gen_flag_v() const { return flag_status & 0x1; }

  u16 flag_status;
  u32 pc;
};

class CodeEmitter {
public:
  CodeEmitter(u8 *emit_ptr, u8 *emit_end, u32 pc)
   : emit_ptr(emit_ptr), emit_end(emit_end), block_pc(pc) {}

  u8 *emit_ptr;              // Points to the JIT buffer, so we can emit code.
  u8 *emit_end;              // Points to the "end" of the JIT buffer
  u32 block_pc;              // PC address for the block base
};

#endif

