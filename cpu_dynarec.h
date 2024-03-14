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
  ThumbInst(u16 opcode, u16 flag_status)
   : ThumbInstDec(opcode), flag_status(flag_status) {}

  bool gen_flag_n() const { return flag_status & 0x8; }
  bool gen_flag_z() const { return flag_status & 0x4; }
  bool gen_flag_c() const { return flag_status & 0x2; }
  bool gen_flag_v() const { return flag_status & 0x1; }

  u16 flag_status;
};

#endif

