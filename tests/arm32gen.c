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
#include "arm32_codegen.h"

int main() {
  uint8_t buffer[8*1024];
  ARMEmitter ce(&buffer[0], &buffer[1024]);

  ce.emit_alu_reg_immshift<OpAdd, NoFlags>(armcg_reg5, armcg_reg6, armcg_reg7, ShiftLSL, 0);
  ce.emit_alu_reg_immshift<OpAdd, SetFlags>(armcg_reg3, armcg_reg9, armcg_reg10, ShiftLSL, 0);

  ce.emit_alu_reg_immshift<OpAdd, NoFlags>(armcg_reg1, armcg_reg2, armcg_reg3, ShiftLSL, 2);
  ce.emit_alu_reg_immshift<OpAdd, SetFlags>(armcg_reg4, armcg_reg5, armcg_reg6, ShiftLSR, 1);
  ce.emit_alu_reg_immshift<OpAdc, NoFlags>(armcg_reg7, armcg_reg8, armcg_reg9, ShiftASR, 3);
  ce.emit_alu_reg_immshift<OpAdc, SetFlags>(armcg_reg10, armcg_reg11, armcg_reg12, ShiftROR, 4);
  ce.emit_alu_reg_immshift<OpSub, NoFlags>(armcg_reg3, armcg_reg4, armcg_reg5, ShiftLSL, 0);
  ce.emit_alu_reg_immshift<OpSub, SetFlags>(armcg_reg6, armcg_reg7, armcg_reg8, ShiftLSR, 5);
  ce.emit_alu_reg_immshift<OpSbc, NoFlags>(armcg_reg9, armcg_reg10, armcg_reg11, ShiftASR, 2);
  ce.emit_alu_reg_immshift<OpSbc, SetFlags>(armcg_reg12, armcg_reg1, armcg_reg2, ShiftROR, 7);
  ce.emit_alu_reg_immshift<OpAnd, NoFlags>(armcg_reg5, armcg_reg6, armcg_reg7, ShiftLSL, 1);
  ce.emit_alu_reg_immshift<OpAnd, SetFlags>(armcg_reg8, armcg_reg9, armcg_reg10, ShiftLSR, 3);
  ce.emit_alu_reg_immshift<OpXor, NoFlags>(armcg_reg11, armcg_reg12, armcg_reg1, ShiftASR, 4);
  ce.emit_alu_reg_immshift<OpXor, SetFlags>(armcg_reg2, armcg_reg3, armcg_reg4, ShiftROR, 6);
  ce.emit_alu_reg_immshift<OpOrr, NoFlags>(armcg_reg6, armcg_reg7, armcg_reg8, ShiftLSL, 8);
  ce.emit_alu_reg_immshift<OpOrr, SetFlags>(armcg_reg9, armcg_reg10, armcg_reg11, ShiftLSR, 2);
  ce.emit_alu_reg_immshift<OpBic, NoFlags>(armcg_reg12, armcg_reg2, armcg_reg3, ShiftASR, 1);
  ce.emit_alu_reg_immshift<OpBic, SetFlags>(armcg_reg4, armcg_reg5, armcg_reg6, ShiftROR, 5);
  ce.emit_alu_reg_immshift<OpRsb, NoFlags>(armcg_reg1, armcg_reg2, armcg_reg3, ShiftLSL, 1);
  ce.emit_alu_reg_immshift<OpRsb, SetFlags>(armcg_reg4, armcg_reg5, armcg_reg6, ShiftLSR, 2);
  ce.emit_alu_reg_immshift<OpRsc, NoFlags>(armcg_reg7, armcg_reg8, armcg_reg9, ShiftASR, 3);
  ce.emit_alu_reg_immshift<OpRsc, SetFlags>(armcg_reg10, armcg_reg11, armcg_reg12, ShiftROR, 4);

  ce.emit_alu_reg_regshift<OpAdd, NoFlags>(armcg_reg1, armcg_reg2, armcg_reg3, ShiftLSL, armcg_reg4);
  ce.emit_alu_reg_regshift<OpAdd, SetFlags>(armcg_reg5, armcg_reg6, armcg_reg7, ShiftLSR, armcg_reg8);
  ce.emit_alu_reg_regshift<OpAdc, NoFlags>(armcg_reg9, armcg_reg10, armcg_reg11, ShiftASR, armcg_reg12);
  ce.emit_alu_reg_regshift<OpAdc, SetFlags>(armcg_reg2, armcg_reg3, armcg_reg4, ShiftROR, armcg_reg5);
  ce.emit_alu_reg_regshift<OpSub, NoFlags>(armcg_reg6, armcg_reg7, armcg_reg8, ShiftLSL, armcg_reg9);
  ce.emit_alu_reg_regshift<OpSub, SetFlags>(armcg_reg10, armcg_reg11, armcg_reg12, ShiftLSR, armcg_reg1);
  ce.emit_alu_reg_regshift<OpSbc, NoFlags>(armcg_reg3, armcg_reg4, armcg_reg5, ShiftASR, armcg_reg6);
  ce.emit_alu_reg_regshift<OpSbc, SetFlags>(armcg_reg7, armcg_reg8, armcg_reg9, ShiftROR, armcg_reg10);
  ce.emit_alu_reg_regshift<OpAnd, NoFlags>(armcg_reg11, armcg_reg12, armcg_reg1, ShiftLSL, armcg_reg2);
  ce.emit_alu_reg_regshift<OpAnd, SetFlags>(armcg_reg3, armcg_reg4, armcg_reg5, ShiftLSR, armcg_reg6);
  ce.emit_alu_reg_regshift<OpXor, NoFlags>(armcg_reg7, armcg_reg8, armcg_reg9, ShiftASR, armcg_reg10);
  ce.emit_alu_reg_regshift<OpXor, SetFlags>(armcg_reg11, armcg_reg12, armcg_reg1, ShiftROR, armcg_reg2);
  ce.emit_alu_reg_regshift<OpOrr, NoFlags>(armcg_reg3, armcg_reg4, armcg_reg5, ShiftLSL, armcg_reg6);
  ce.emit_alu_reg_regshift<OpOrr, SetFlags>(armcg_reg7, armcg_reg8, armcg_reg9, ShiftLSR, armcg_reg10);
  ce.emit_alu_reg_regshift<OpBic, NoFlags>(armcg_reg11, armcg_reg12, armcg_reg1, ShiftASR, armcg_reg2);
  ce.emit_alu_reg_regshift<OpBic, SetFlags>(armcg_reg3, armcg_reg4, armcg_reg5, ShiftROR, armcg_reg6);
  ce.emit_alu_reg_regshift<OpRsb, NoFlags>(armcg_reg7, armcg_reg8, armcg_reg9, ShiftLSL, armcg_reg10);
  ce.emit_alu_reg_regshift<OpRsb, SetFlags>(armcg_reg11, armcg_reg12, armcg_reg1, ShiftLSR, armcg_reg2);
  ce.emit_alu_reg_regshift<OpRsc, NoFlags>(armcg_reg3, armcg_reg4, armcg_reg5, ShiftASR, armcg_reg6);
  ce.emit_alu_reg_regshift<OpRsc, SetFlags>(armcg_reg7, armcg_reg8, armcg_reg9, ShiftROR, armcg_reg10);

  ce.emit_alu_imm<OpAdd, NoFlags>(armcg_reg1, armcg_reg2, 0, 0x12);
  ce.emit_alu_imm<OpAdd, SetFlags>(armcg_reg3, armcg_reg4, 4, 0x85);
  ce.emit_alu_imm<OpAdc, NoFlags>(armcg_reg5, armcg_reg6, 2, 0x56);
  ce.emit_alu_imm<OpAdc, SetFlags>(armcg_reg7, armcg_reg8, 6, 0x79);
  ce.emit_alu_imm<OpSub, NoFlags>(armcg_reg9, armcg_reg10, 0, 0x9A);
  ce.emit_alu_imm<OpSub, SetFlags>(armcg_reg11, armcg_reg12, 8, 0xBD);
  ce.emit_alu_imm<OpSbc, NoFlags>(armcg_reg2, armcg_reg3, 2, 0xDE);
  ce.emit_alu_imm<OpSbc, SetFlags>(armcg_reg4, armcg_reg5, 12, 0xF1);
  ce.emit_alu_imm<OpAnd, NoFlags>(armcg_reg6, armcg_reg7, 0, 0x11);
  ce.emit_alu_imm<OpAnd, SetFlags>(armcg_reg8, armcg_reg9, 4, 0x22);
  ce.emit_alu_imm<OpXor, NoFlags>(armcg_reg10, armcg_reg11, 2, 0x33);
  ce.emit_alu_imm<OpXor, SetFlags>(armcg_reg12, armcg_reg1, 6, 0xEE);
  ce.emit_alu_imm<OpOrr, NoFlags>(armcg_reg2, armcg_reg3, 0, 0x55);
  ce.emit_alu_imm<OpOrr, SetFlags>(armcg_reg4, armcg_reg5, 8, 0x66);
  ce.emit_alu_imm<OpBic, NoFlags>(armcg_reg6, armcg_reg7, 2, 0x77);
  ce.emit_alu_imm<OpBic, SetFlags>(armcg_reg8, armcg_reg9, 12, 0x89);
  ce.emit_alu_imm<OpRsb, NoFlags>(armcg_reg10, armcg_reg11, 0, 0x99);
  ce.emit_alu_imm<OpRsb, SetFlags>(armcg_reg12, armcg_reg1, 4, 0xAA);
  ce.emit_alu_imm<OpRsc, NoFlags>(armcg_reg2, armcg_reg3, 2, 0xBB);
  ce.emit_alu_imm<OpRsc, SetFlags>(armcg_reg4, armcg_reg5, 8, 0xCF);

  ce.emit_test_reg_immshift<OpTst>(armcg_reg1, armcg_reg2, ShiftLSL, 0);
  ce.emit_test_reg_immshift<OpTeq>(armcg_reg3, armcg_reg4, ShiftLSR, 4);
  ce.emit_test_reg_immshift<OpCmp>(armcg_reg5, armcg_reg6, ShiftASR, 8);
  ce.emit_test_reg_immshift<OpCmn>(armcg_reg7, armcg_reg8, ShiftROR, 12);

  ce.emit_test_reg_regshift<OpTst>(armcg_reg2, armcg_reg1, ShiftLSL, armcg_reg3);
  ce.emit_test_reg_regshift<OpTeq>(armcg_reg4, armcg_reg3, ShiftLSR, armcg_reg5);
  ce.emit_test_reg_regshift<OpCmp>(armcg_reg6, armcg_reg5, ShiftASR, armcg_reg7);
  ce.emit_test_reg_regshift<OpCmn>(armcg_reg8, armcg_reg7, ShiftROR, armcg_reg9);

  ce.emit_test_imm<OpTst>(armcg_reg1, 0, 0x12);
  ce.emit_test_imm<OpTeq>(armcg_reg3, 4, 0xAA);
  ce.emit_test_imm<OpCmp>(armcg_reg5, 8, 0x56);
  ce.emit_test_imm<OpCmn>(armcg_reg7, 12, 0x79);

  ce.emit_alus_reg<OpAdd>(armcg_reg1, armcg_reg2, armcg_reg3);
  ce.emit_alus_reg<OpAdc>(armcg_reg4, armcg_reg5, armcg_reg6);
  ce.emit_alus_reg<OpSub>(armcg_reg7, armcg_reg8, armcg_reg9);
  ce.emit_alus_reg<OpSbc>(armcg_reg10, armcg_reg11, armcg_reg12);
  ce.emit_alus_reg<OpAnd>(armcg_reg1, armcg_reg3, armcg_reg5);
  ce.emit_alus_reg<OpXor>(armcg_reg2, armcg_reg4, armcg_reg6);
  ce.emit_alus_reg<OpOrr>(armcg_reg7, armcg_reg9, armcg_reg11);
  ce.emit_alus_reg<OpBic>(armcg_reg8, armcg_reg10, armcg_reg12);
  ce.emit_alus_reg<OpRsb>(armcg_reg1, armcg_reg2, armcg_reg4);
  ce.emit_alus_reg<OpRsc>(armcg_reg3, armcg_reg5, armcg_reg7);

  ce.emit_alus_imm<OpAdd>(armcg_reg1, armcg_reg2, 0x12);
  ce.emit_alus_imm<OpAdc>(armcg_reg3, armcg_reg4, 0x99, 4);
  ce.emit_alus_imm<OpSub>(armcg_reg5, armcg_reg6, 0x56, 8);
  ce.emit_alus_imm<OpSbc>(armcg_reg7, armcg_reg8, 0x79, 12);
  ce.emit_alus_imm<OpAnd>(armcg_reg9, armcg_reg10, 0x9A, 0);
  ce.emit_alus_imm<OpXor>(armcg_reg11, armcg_reg12, 0xBD, 4);
  ce.emit_alus_imm<OpOrr>(armcg_reg1, armcg_reg3, 0xDE, 8);
  ce.emit_alus_imm<OpBic>(armcg_reg4, armcg_reg5, 0xF1, 12);
  ce.emit_alus_imm<OpRsb>(armcg_reg6, armcg_reg7, 0x81);
  ce.emit_alus_imm<OpRsc>(armcg_reg8, armcg_reg9, 0x83, 4);

  ce.emit_mov_reg_immshift<OpMov, NoFlags>(armcg_reg1, armcg_reg2, ShiftLSL, 0);
  ce.emit_mov_reg_immshift<OpMov, SetFlags>(armcg_reg3, armcg_reg4, ShiftLSR, 8);
  ce.emit_mov_reg_immshift<OpMvn, NoFlags>(armcg_reg5, armcg_reg6, ShiftASR, 16);
  ce.emit_mov_reg_immshift<OpMvn, SetFlags>(armcg_reg7, armcg_reg8, ShiftROR, 24);

  ce.emit_mov_reg_regshift<OpMov, NoFlags>(armcg_reg9, armcg_reg10, ShiftLSL, armcg_reg1);
  ce.emit_mov_reg_regshift<OpMov, SetFlags>(armcg_reg11, armcg_reg12, ShiftLSR, armcg_reg3);
  ce.emit_mov_reg_regshift<OpMvn, NoFlags>(armcg_reg1, armcg_reg2, ShiftASR, armcg_reg5);
  ce.emit_mov_reg_regshift<OpMvn, SetFlags>(armcg_reg3, armcg_reg4, ShiftROR, armcg_reg7);

  ce.emit_mov_imm<OpMov, NoFlags>(armcg_reg1, 0, 0x81);
  ce.emit_mov_imm<OpMov, SetFlags>(armcg_reg3, 4, 0xC1);
  ce.emit_mov_imm<OpMvn, NoFlags>(armcg_reg5, 8, 0xF1);
  ce.emit_mov_imm<OpMvn, SetFlags>(armcg_reg7, 12, 0xE1);
  ce.emit_mov_imm<OpMov, NoFlags>(armcg_reg9, 2, 0x91);
  ce.emit_mov_imm<OpMov, SetFlags>(armcg_reg11, 6, 0xA1);
  ce.emit_mov_imm<OpMvn, NoFlags>(armcg_reg1, 10, 0xB1);
  ce.emit_mov_imm<OpMvn, SetFlags>(armcg_reg3, 14, 0xD1);

  ce.emit_ldr_imm(armcg_reg1, armcg_reg2, 0x000);
  ce.emit_ldr_imm(armcg_reg3, armcg_reg4, 0x034);
  ce.emit_ldr_imm(armcg_reg5, armcg_reg6, 0x7FC);
  ce.emit_str_imm(armcg_reg7, armcg_reg8, 0x000);
  ce.emit_str_imm(armcg_reg9, armcg_reg10, 0x020);
  ce.emit_str_imm(armcg_reg11, armcg_reg12, 0xABC);

  ce.emit_ldr_reg(armcg_reg0, armcg_reg1, armcg_reg2, ShiftLSL, 0);
  ce.emit_ldr_reg(armcg_reg3, armcg_reg4, armcg_reg5, ShiftLSL, 2);
  ce.emit_ldr_reg(armcg_reg6, armcg_reg7, armcg_reg8, ShiftLSR, 3);
  ce.emit_ldr_reg(armcg_reg9, armcg_reg10, armcg_reg11, ShiftASR, 1);
  ce.emit_ldr_reg(armcg_reg12, armcg_reg13, armcg_reg14, ShiftROR, 4);
  ce.emit_str_reg(armcg_reg2, armcg_reg3, armcg_reg4, ShiftLSL, 0);
  ce.emit_str_reg(armcg_reg5, armcg_reg6, armcg_reg7, ShiftLSL, 1);
  ce.emit_str_reg(armcg_reg8, armcg_reg9, armcg_reg10, ShiftLSR, 2);
  ce.emit_str_reg(armcg_reg11, armcg_reg12, armcg_reg13, ShiftASR, 3);
  ce.emit_str_reg(armcg_reg14, armcg_reg15, armcg_reg0, ShiftROR, 1);

  fwrite(buffer, 1, ce.emit_ptr-buffer, stdout);
}

