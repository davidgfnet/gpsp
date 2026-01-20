/* gameplaySP
 *
 * Copyright (C) 2026 David Guillen Fandos <david@davidgf.net>
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

#ifndef __CODEGEN__HH__
#define __CODEGEN__HH__

#include <stdint.h>

// Whether the CPU is running in ARM or Thumb mode
typedef enum { ModeARM, ModeThumb } CPUInstMode;
// Whether the CPU flags are updated or no.
typedef enum { NoFlags, SetFlags } FlagOperation;
// ARM shift/rotation type (matches ARM encoding)
typedef enum { ShiftLSL = 0, ShiftLSR = 1, ShiftASR = 2, ShiftROR = 3 } ShiftType;
// ARM operation type (matches ARM encoding)
typedef enum {
  OpAnd = 0x0,
  OpXor = 0x1,
  OpSub = 0x2,
  OpRsb = 0x3,
  OpAdd = 0x4,
  OpAdc = 0x5,
  OpSbc = 0x6,
  OpRsc = 0x7,
  OpTst = 0x8,
  OpTeq = 0x9,
  OpCmp = 0xA,
  OpCmn = 0xB,
  OpOrr = 0xC,
  OpMov = 0xD,
  OpBic = 0xE,
  OpMvn = 0xF,

  // Extended opcodes (for convenience)
  OpNeg,
  OpMul,
} ARMOp;

/*typedef enum {
  armop_and = 0x0,
  armop_eor = 0x1,
  armop_sub = 0x2,
  armop_rsb = 0x3,
  armop_add = 0x4,
  armop_adc = 0x5,
  armop_sbc = 0x6,
  armop_rsc = 0x7,
  armop_tst = 0x8,
  armop_teq = 0x9,
  armop_cmp = 0xA,
  armop_cmn = 0xB,
  armop_orr = 0xC,
  armop_mov = 0xD,
  armop_bic = 0xE,
  armop_mvn = 0xF,
} armcg_op;*/



class CodeEmitterBase {
public:
  CodeEmitterBase(uint8_t *emit_ptr, uint8_t *emit_end)
   : emit_ptr(emit_ptr), emit_end(emit_end), cyc_cnt(0) {}

  uint8_t *emit_ptr;              // Points to the JIT buffer, so we can emit code.
  uint8_t *emit_end;              // Points to the "end" of the JIT buffer

  uint32_t cyc_cnt;               // Cycle counter
};

#endif

