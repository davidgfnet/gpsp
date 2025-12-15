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

// Whether the CPU flags are updated or no.
typedef enum { NoFlags, SetFlags } FlagOperation;
// Memory access type
typedef enum { AccLoad, AccStore } AccMode;
// PSR register
typedef enum { RegCPSR, RegSPSR } PSReg;
// Operand type
typedef enum { OpReg, OpImm } OpType;


class BaseInst {
public:
  BaseInst(u32 pc, u16 flgst)
   : pc(pc), flag_status(flgst) {}

  bool gen_flag_n() const { return flag_status & 0x8; }
  bool gen_flag_z() const { return flag_status & 0x4; }
  bool gen_flag_c() const { return flag_status & 0x2; }
  bool gen_flag_v() const { return flag_status & 0x1; }

  u32 pc;
  u16 flag_status;
};

class ThumbInst : public ThumbInstDec, public BaseInst {
public:
  ThumbInst(u32 pc, u16 opcode, u16 flag_status)
   : ThumbInstDec(opcode), BaseInst(pc, flag_status) {}

};

class ARMInst : public ARMInstDec, public BaseInst {
public:
  ARMInst(u32 pc, u32 opcode, u16 flag_status)
   : ARMInstDec(opcode), BaseInst(pc, flag_status) {}

};

class CodeEmitterBase {
public:
  CodeEmitterBase(u8 *emit_ptr, u8 *emit_end)
   : emit_ptr(emit_ptr), emit_end(emit_end) {}

  u8 *emit_ptr;              // Points to the JIT buffer, so we can emit code.
  u8 *emit_end;              // Points to the "end" of the JIT buffer
};

#ifdef __cplusplus
extern "C" {
#endif

u8 function_cc *block_lookup_address_arm(u32 pc);
u8 function_cc *block_lookup_address_thumb(u32 pc);
u8 function_cc *block_lookup_address_dual(u32 pc);

u32 function_cc process_cpsr_write(u32 new_cpsr, u32 pc);

#ifdef __cplusplus
}
#endif

#endif

