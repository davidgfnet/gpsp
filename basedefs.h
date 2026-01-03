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

class CodeEmitterBase {
public:
  CodeEmitterBase(uint8_t *emit_ptr, uint8_t *emit_end)
   : emit_ptr(emit_ptr), emit_end(emit_end) {}

  uint8_t *emit_ptr;              // Points to the JIT buffer, so we can emit code.
  uint8_t *emit_end;              // Points to the "end" of the JIT buffer
};

#endif

