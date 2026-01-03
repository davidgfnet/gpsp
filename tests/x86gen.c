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
#include "x86_codegen.h"

int main() {
  uint8_t buffer[8*1024];
  X86Emitter ce(&buffer[0], &buffer[1024]);

  //ce.x86_emit_reg_mov(x86_reg_ecx, x86_reg_edx);
  //ce.x86_emit_reg_mov(x86_reg_eax, x86_reg_edi);

  ce.x86_emit_reg_load(x86_reg_ebx, x86_reg_edi, 4);
  ce.x86_emit_reg_load(x86_reg_ebx, x86_reg_ebx, 7);
  ce.x86_emit_reg_load(x86_reg_esi, x86_reg_edi, 0x10111213);
  ce.x86_emit_reg_store(x86_reg_ebx, x86_reg_edi, 4);
  ce.x86_emit_reg_store(x86_reg_ebx, x86_reg_ebx, 7);
  ce.x86_emit_reg_store(x86_reg_esi, x86_reg_edi, 0x10111213);
  ce.x86_emit_reg_loadub(x86_reg_ebx, x86_reg_edi, 4);
  ce.x86_emit_reg_loadub(x86_reg_ebx, x86_reg_ebx, 7);
  ce.x86_emit_reg_loadub(x86_reg_esi, x86_reg_edi, 0x10111213);

  ce.x86_emit_load_imm(x86_reg_ebx, 0x123);
  ce.x86_emit_load_imm(x86_reg_edx, 0x12366);

  ce.x86_emit_store_imm32(0x12345, x86_reg_esi, 0x15);
  ce.x86_emit_store_imm32(0x3333, x86_reg_edi, 0x151617);

  //ce.x86_emit_reg_and(x86_reg_ebx, x86_reg_ecx);
  //ce.x86_emit_reg_xor(x86_reg_ebx, x86_reg_ecx);
  //ce.x86_emit_reg_or(x86_reg_ebx, x86_reg_ecx);

  ce.x86_emit_mem_and(x86_reg_ebx, x86_reg_ecx, 0x12);
  ce.x86_emit_mem_xor(x86_reg_ebx, x86_reg_ecx, 0x12);
  ce.x86_emit_mem_or(x86_reg_ebx, x86_reg_ecx, 0x12);
  ce.x86_emit_mem_and(x86_reg_ebx, x86_reg_ecx, 0x1234);
  ce.x86_emit_mem_xor(x86_reg_ebx, x86_reg_ecx, 0x1234);
  ce.x86_emit_mem_or(x86_reg_ebx, x86_reg_ecx, 0x1234);

  ce.x86_emit_imm_and(x86_reg_ebx, 0x1213);
  ce.x86_emit_imm_xor(x86_reg_ebx, 0x1213);
  ce.x86_emit_imm_or(x86_reg_ebx, 0x1213);

  ce.x86_emit_mem_imm_and(0x12345, x86_reg_ebx, 0xaa);
  ce.x86_emit_mem_imm_and(0x12345, x86_reg_ebx, 0xaabb);

  ce.x86_emit_reg_shr(x86_reg_ebx);
  ce.x86_emit_reg_sar(x86_reg_ebx);
  ce.x86_emit_reg_shl(x86_reg_ebx);
  ce.x86_emit_reg_ror(x86_reg_ebx);
  ce.x86_emit_reg_shr_imm(x86_reg_ebx, 2);
  ce.x86_emit_reg_sar_imm(x86_reg_ebx, 3);
  ce.x86_emit_reg_shl_imm(x86_reg_ebx, 4);
  ce.x86_emit_reg_ror_imm(x86_reg_ebx, 5);

  //ce.x86_emit_reg_add(x86_reg_ebx, x86_reg_ecx);
  //ce.x86_emit_reg_sub(x86_reg_ebx, x86_reg_ecx);
  //ce.x86_emit_reg_adc(x86_reg_ebx, x86_reg_ecx);
  //ce.x86_emit_reg_sbb(x86_reg_ebx, x86_reg_ecx);
  //ce.x86_emit_reg_cmp(x86_reg_ebx, x86_reg_ecx);
  //ce.x86_emit_reg_test(x86_reg_ebx, x86_reg_ecx);

  ce.x86_emit_mem_add(x86_reg_ebx, x86_reg_edi, 0x10);
  ce.x86_emit_mem_sub(x86_reg_ebx, x86_reg_edi, 0x20);
//  ce.x86_emit_mem_cmp(x86_reg_ebx, x86_reg_edi, 0x30);

  ce.x86_emit_imm_add(x86_reg_ebx, 0x1234);
  ce.x86_emit_imm_sub(x86_reg_ebx, 0x5678);
  ce.x86_emit_imm_adc(x86_reg_ebx, 0x9abc);
  ce.x86_emit_imm_sbb(x86_reg_ebx, 0xdef0);
  ce.x86_emit_imm_cmp(x86_reg_ebx, 0x1111);
  ce.x86_emit_imm_test(x86_reg_ebx, 0x2222);

  ce.x86_emit_mem_imm_add(0x12345678, x86_reg_edi, 0x10);
  ce.x86_emit_mem_imm_sub(0x9abcdef0, x86_reg_edi, 0x80);
  ce.x86_emit_mem_imm_add(0x12345678, x86_reg_edi, 0x10101010);
  ce.x86_emit_mem_imm_sub(0x9abcdef0, x86_reg_edi, 0x20202020);

  ce.x86_emit_mul_eax(x86_reg_ebx);
  ce.x86_emit_imul_eax(x86_reg_ebx);
  ce.x86_emit_idiv_eax(x86_reg_ebx);

  ce.x86_emit_reg_neg(x86_reg_ebx);
  ce.x86_emit_reg_not(x86_reg_ebx);

  ce.x86_emit_setcc_mem(x86_condition_code_c, x86_reg_edi, 0x10);
  ce.x86_emit_setcc_mem(x86_condition_code_nc, x86_reg_edi, 0x1010);
  ce.x86_emit_reg_cmov(x86_condition_code_c, x86_reg_ebx, x86_reg_ecx);
  ce.x86_emit_reg_cmov(x86_condition_code_nc, x86_reg_ebx, x86_reg_ecx);

  ce.x86_emit_reg_bittest(x86_reg_ebx, 3);
  ce.x86_emit_reg_bittest(x86_reg_ecx, 7);
  ce.x86_emit_mem_bittest(x86_reg_edi, 0x10, 2);
  ce.x86_emit_mem_bittest(x86_reg_edi, 0x1010, 5);

  //ce.x86_emit_call(0x12345678);

  ce.x86_emit_lea(x86_reg_ebx, x86_reg_edi, 0x10);
  ce.x86_emit_lea(x86_reg_esi, x86_reg_edi, 0x10101010);

  ce.x86_emit_cdq();
  ce.x86_emit_cmc();

  fwrite(buffer, 1, ce.emit_ptr-buffer, stdout);
}

