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

#include <stdio.h>
#include <stdint.h>
#include "basedefs.h"
#include "arm64_codegen.h"

int main() {
  uint8_t buffer[8*1024];
  ARM64Emitter ce(&buffer[0], &buffer[1024]);

  ce.aa64_emit_branch(16);
  ce.aa64_emit_brlink(16);

  ce.aa64_emit_brcond(ccode_eq, 16);
  ce.aa64_emit_brcond(ccode_ne, 16);
  ce.aa64_emit_brcond(ccode_hs, 16);
  ce.aa64_emit_brcond(ccode_lo, 16);
  ce.aa64_emit_brcond(ccode_mi, 16);
  ce.aa64_emit_brcond(ccode_pl, 16);
  ce.aa64_emit_brcond(ccode_vs, 16);
  ce.aa64_emit_brcond(ccode_vc, 16);
  ce.aa64_emit_brcond(ccode_hi, 16);
  ce.aa64_emit_brcond(ccode_ls, 16);
  ce.aa64_emit_brcond(ccode_ge, 16);
  ce.aa64_emit_brcond(ccode_lt, 16);
  ce.aa64_emit_brcond(ccode_gt, 16);
  ce.aa64_emit_brcond(ccode_le, 16);
  ce.aa64_emit_brcond(ccode_al, 16);
  ce.aa64_emit_brcond(ccode_nv, 16);

  ce.aa64_emit_ldr(arm64_reg_x1, arm64_reg_x2, 16);
  ce.aa64_emit_ldr(arm64_reg_x29, arm64_reg_x30, 16);
  ce.aa64_emit_str(arm64_reg_x1, arm64_reg_x2, 16);
  ce.aa64_emit_str(arm64_reg_x29, arm64_reg_x30, 16);

  ce.aa64_emit_movlo(arm64_reg_x0,  0x1234);
  ce.aa64_emit_movlo(arm64_reg_x12, 0x5656);
  ce.aa64_emit_movlo(arm64_reg_x12, ~0);

  ce.aa64_emit_movhi(arm64_reg_x13, 0x9876);
  ce.aa64_emit_movhi(arm64_reg_x13, ~0);

  ce.aa64_emit_movhiz(arm64_reg_x13, 0xabcd);

  ce.aa64_emit_movne(arm64_reg_x14, 0xAAAA);

  ce.aa64_emit_addi<NoFlags>(arm64_reg_x1, arm64_reg_x29, 0x123);
  ce.aa64_emit_addi<NoFlags>(arm64_reg_x1, arm64_reg_x29, 0xFFF);
  ce.aa64_emit_subi<NoFlags>(arm64_reg_x1, arm64_reg_x29, 0x123);
  ce.aa64_emit_subi<NoFlags>(arm64_reg_x1, arm64_reg_x29, 0xFFF);

  ce.aa64_emit_addi12<NoFlags>(arm64_reg_x3, arm64_reg_x30, 0x123);
  ce.aa64_emit_addi12<NoFlags>(arm64_reg_x3, arm64_reg_x30, 0xFFF);
  ce.aa64_emit_subi12<NoFlags>(arm64_reg_x3, arm64_reg_x30, 0x123);
  ce.aa64_emit_subi12<NoFlags>(arm64_reg_x3, arm64_reg_x30, 0xFFF);

  ce.aa64_emit_addi<SetFlags>(arm64_reg_x29, arm64_reg_x30, 0x123);
  ce.aa64_emit_addi<SetFlags>(arm64_reg_x29, arm64_reg_x30, 0xFFF);
  ce.aa64_emit_subi<SetFlags>(arm64_reg_x29, arm64_reg_x30, 0x123);
  ce.aa64_emit_subi<SetFlags>(arm64_reg_x29, arm64_reg_x30, 0xFFF);

  ce.aa64_emit_addi12<SetFlags>(arm64_reg_x29, arm64_reg_x30, 0x123);
  ce.aa64_emit_addi12<SetFlags>(arm64_reg_x29, arm64_reg_x30, 0xFFF);
  ce.aa64_emit_subi12<SetFlags>(arm64_reg_x29, arm64_reg_x30, 0x123);
  ce.aa64_emit_subi12<SetFlags>(arm64_reg_x29, arm64_reg_x30, 0xFFF);

  ce.aa64_emit_madd(arm64_reg_x2, arm64_reg_x5, arm64_reg_x3, arm64_reg_x4);
  ce.aa64_emit_madd(arm64_reg_x25, arm64_reg_x28, arm64_reg_x26, arm64_reg_x27);
  ce.aa64_emit_msub(arm64_reg_x2, arm64_reg_x5, arm64_reg_x3, arm64_reg_x4);
  ce.aa64_emit_msub(arm64_reg_x25, arm64_reg_x28, arm64_reg_x26, arm64_reg_x27);

  ce.aa64_emit_smaddl(arm64_reg_x2, arm64_reg_x5, arm64_reg_x3, arm64_reg_x4);
  ce.aa64_emit_smaddl(arm64_reg_x25, arm64_reg_x28, arm64_reg_x26, arm64_reg_x27);
  ce.aa64_emit_umaddl(arm64_reg_x2, arm64_reg_x5, arm64_reg_x3, arm64_reg_x4);
  ce.aa64_emit_umaddl(arm64_reg_x25, arm64_reg_x28, arm64_reg_x26, arm64_reg_x27);

  ce.aa64_emit_mul(arm64_reg_x1, arm64_reg_x2, arm64_reg_x3);
  ce.aa64_emit_mul(arm64_reg_x27, arm64_reg_x28, arm64_reg_x29);

  ce.aa64_emit_ror(arm64_reg_x1, arm64_reg_x2, 1);
  ce.aa64_emit_ror(arm64_reg_x1, arm64_reg_x2, 31);
  ce.aa64_emit_ror(arm64_reg_x30, arm64_reg_x29, 1);
  ce.aa64_emit_ror(arm64_reg_x30, arm64_reg_x29, 31);

  ce.aa64_emit_lsr(arm64_reg_x1, arm64_reg_x2, 1);
  ce.aa64_emit_lsr(arm64_reg_x1, arm64_reg_x2, 31);
  ce.aa64_emit_lsr(arm64_reg_x30, arm64_reg_x29, 1);
  ce.aa64_emit_lsr(arm64_reg_x30, arm64_reg_x29, 31);

  ce.aa64_emit_lsl(arm64_reg_x1, arm64_reg_x2, 1);
  ce.aa64_emit_lsl(arm64_reg_x1, arm64_reg_x2, 31);
  ce.aa64_emit_lsl(arm64_reg_x30, arm64_reg_x29, 1);
  ce.aa64_emit_lsl(arm64_reg_x30, arm64_reg_x29, 31);

  ce.aa64_emit_asr(arm64_reg_x1, arm64_reg_x2, 1);
  ce.aa64_emit_asr(arm64_reg_x1, arm64_reg_x2, 31);
  ce.aa64_emit_asr(arm64_reg_x30, arm64_reg_x29, 1);
  ce.aa64_emit_asr(arm64_reg_x30, arm64_reg_x29, 31);

  ce.aa64_emit_lsr64(arm64_reg_x1, arm64_reg_x2, 1);
  ce.aa64_emit_lsr64(arm64_reg_x1, arm64_reg_x2, 2);
  ce.aa64_emit_lsr64(arm64_reg_x1, arm64_reg_x2, 62);
  ce.aa64_emit_lsr64(arm64_reg_x1, arm64_reg_x2, 63);
  ce.aa64_emit_lsr64(arm64_reg_x30, arm64_reg_x29, 1);
  ce.aa64_emit_lsr64(arm64_reg_x30, arm64_reg_x29, 62);

  ce.aa64_emit_eori(arm64_reg_x3, arm64_reg_x4, 0, 0);
  ce.aa64_emit_eori(arm64_reg_x3, arm64_reg_x4, 31, 30);  // ~1
  ce.aa64_emit_orri(arm64_reg_x3, arm64_reg_x4, 0, 0);
  ce.aa64_emit_orri(arm64_reg_x3, arm64_reg_x4, 31, 30);
  ce.aa64_emit_andi(arm64_reg_x3, arm64_reg_x4, 0, 0);
  ce.aa64_emit_andi(arm64_reg_x3, arm64_reg_x4, 30, 29);  // ~3

  ce.aa64_emit_andi64(arm64_reg_x3, arm64_reg_x4, 0, 31);
  ce.aa64_emit_andi64(arm64_reg_x3, arm64_reg_x4, 0, 0);
  ce.aa64_emit_andi64(arm64_reg_x1, arm64_reg_x2, 0, 0);     // & 1
  ce.aa64_emit_andi64(arm64_reg_x1, arm64_reg_x2, 63, 62);   // & ~1
  ce.aa64_emit_andi64(arm64_reg_x1, arm64_reg_x2, 0, 31);    // & 0xffffffff

  ce.aa64_emit_mov(arm64_reg_x1, arm64_reg_x2);
  ce.aa64_emit_mov(arm64_reg_x30, arm64_reg_x31);

  ce.aa64_emit_orr(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_orr(arm64_reg_x29, arm64_reg_x30, arm64_reg_x31);
  ce.aa64_emit_xor(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_xor(arm64_reg_x29, arm64_reg_x30, arm64_reg_x31);
  ce.aa64_emit_orn(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_orn(arm64_reg_x29, arm64_reg_x30, arm64_reg_x31);
  ce.aa64_emit_and(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_and(arm64_reg_x29, arm64_reg_x30, arm64_reg_x31);
  ce.aa64_emit_bic(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_bic(arm64_reg_x29, arm64_reg_x30, arm64_reg_x31);
  ce.aa64_emit_ands(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_ands(arm64_reg_x29, arm64_reg_x30, arm64_reg_x31);

  ce.aa64_emit_tst(arm64_reg_x1,  arm64_reg_x2);
  ce.aa64_emit_tst(arm64_reg_x25, arm64_reg_x31);

  ce.aa64_emit_cmpi(arm64_reg_x1,  0);
  ce.aa64_emit_cmpi(arm64_reg_x30, 0);
  ce.aa64_emit_cmpi(arm64_reg_x1,  32);
  ce.aa64_emit_cmpi(arm64_reg_x30, 32);
  ce.aa64_emit_cmpi(arm64_reg_x1,  200);
  ce.aa64_emit_cmpi(arm64_reg_x30, 200);

  ce.aa64_emit_add<NoFlags>(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_add<NoFlags>(arm64_reg_x29, arm64_reg_x30, arm64_reg_x28);
  ce.aa64_emit_sub<NoFlags>(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_sub<NoFlags>(arm64_reg_x29, arm64_reg_x30, arm64_reg_x28);
  ce.aa64_emit_adc<NoFlags>(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_adc<NoFlags>(arm64_reg_x29, arm64_reg_x30, arm64_reg_x28);
  ce.aa64_emit_sbc<NoFlags>(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_sbc<NoFlags>(arm64_reg_x29, arm64_reg_x30, arm64_reg_x28);
  ce.aa64_emit_add<SetFlags>(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_add<SetFlags>(arm64_reg_x29, arm64_reg_x30, arm64_reg_x28);
  ce.aa64_emit_sub<SetFlags>(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_sub<SetFlags>(arm64_reg_x29, arm64_reg_x30, arm64_reg_x28);
  ce.aa64_emit_adc<SetFlags>(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_adc<SetFlags>(arm64_reg_x29, arm64_reg_x30, arm64_reg_x28);
  ce.aa64_emit_sbc<SetFlags>(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_sbc<SetFlags>(arm64_reg_x29, arm64_reg_x30, arm64_reg_x28);

  ce.aa64_emit_tbz(arm64_reg_x20, 1, 63);
  ce.aa64_emit_tbnz(arm64_reg_x20, 1, 63);
  ce.aa64_emit_tbz(arm64_reg_x20, 0, 2);
  ce.aa64_emit_tbnz(arm64_reg_x20, 7, 2);

  ce.aa64_emit_cbz(arm64_reg_x20, 63);
  ce.aa64_emit_cbnz(arm64_reg_x20, 63);
  ce.aa64_emit_cbz(arm64_reg_x20, 2);
  ce.aa64_emit_cbnz(arm64_reg_x20, 2);

  ce.aa64_emit_csel(arm64_reg_x20, arm64_reg_x24, arm64_reg_x25, ccode_ne);
  ce.aa64_emit_csel(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3,  ccode_eq);
  ce.aa64_emit_csel(arm64_reg_x1,  arm64_reg_x20, arm64_reg_x31, ccode_lt);
  ce.aa64_emit_csel(arm64_reg_x1,  arm64_reg_x31, arm64_reg_x31, ccode_gt);

  ce.aa64_emit_csinc(arm64_reg_x20, arm64_reg_x24, arm64_reg_x25, ccode_ne);
  ce.aa64_emit_csinc(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3,  ccode_eq);
  ce.aa64_emit_csinc(arm64_reg_x1,  arm64_reg_x20, arm64_reg_x31, ccode_lt);
  ce.aa64_emit_csinc(arm64_reg_x1,  arm64_reg_x31, arm64_reg_x31, ccode_gt);

  ce.aa64_emit_csinv(arm64_reg_x20, arm64_reg_x24, arm64_reg_x25, ccode_ne);
  ce.aa64_emit_csinv(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3,  ccode_eq);
  ce.aa64_emit_csinv(arm64_reg_x1,  arm64_reg_x20, arm64_reg_x31, ccode_lt);
  ce.aa64_emit_csinv(arm64_reg_x1,  arm64_reg_x31, arm64_reg_x31, ccode_gt);

  ce.aa64_emit_csneg(arm64_reg_x20, arm64_reg_x24, arm64_reg_x25, ccode_ne);
  ce.aa64_emit_csneg(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3,  ccode_eq);
  ce.aa64_emit_csneg(arm64_reg_x1,  arm64_reg_x20, arm64_reg_x31, ccode_lt);
  ce.aa64_emit_csneg(arm64_reg_x1,  arm64_reg_x31, arm64_reg_x31, ccode_gt);

  ce.aa64_emit_cset(arm64_reg_x1,  ccode_eq);
  ce.aa64_emit_cset(arm64_reg_x1,  ccode_hs);
  ce.aa64_emit_cset(arm64_reg_x20, ccode_lo);
  ce.aa64_emit_csetm(arm64_reg_x1,  ccode_hs);
  ce.aa64_emit_csetm(arm64_reg_x20, ccode_lo);

  ce.aa64_emit_ubfx(arm64_reg_x1,  arm64_reg_x2,  8,  8);
  ce.aa64_emit_ubfx(arm64_reg_x1,  arm64_reg_x2, 16, 16);
  ce.aa64_emit_ubfx(arm64_reg_x1,  arm64_reg_x31, 8, 24);
  ce.aa64_emit_ubfx(arm64_reg_x1,  arm64_reg_x31, 16, 16);

  ce.aa64_emit_rorv(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_rorv(arm64_reg_x28, arm64_reg_x29, arm64_reg_x30);
  ce.aa64_emit_lslv(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_lslv(arm64_reg_x28, arm64_reg_x29, arm64_reg_x30);
  ce.aa64_emit_lsrv(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_lsrv(arm64_reg_x28, arm64_reg_x29, arm64_reg_x30);
  ce.aa64_emit_asrv(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_asrv(arm64_reg_x28, arm64_reg_x29, arm64_reg_x30);

  ce.aa64_emit_merge_regs(arm64_reg_x1,  arm64_reg_x3,  arm64_reg_x2);   // hi, lo
  ce.aa64_emit_merge_regs(arm64_reg_x25, arm64_reg_x27, arm64_reg_x26);

  ce.aa64_emit_sdiv(arm64_reg_x1,  arm64_reg_x2,  arm64_reg_x3);
  ce.aa64_emit_sdiv(arm64_reg_x28, arm64_reg_x29, arm64_reg_x30);

  fwrite(buffer, 1, ce.emit_ptr-buffer, stdout);
}

