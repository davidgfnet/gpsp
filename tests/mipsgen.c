
#define u32 uint32_t
#define u8  uint8_t

#include <stdio.h>
#include <stdint.h>
#include "basedefs.h"
#include "mips_codegen.h"

int main() {
  u8 buffer[8*1024];
  MIPSEmitter ce(&buffer[0], &buffer[1024]);

  ce.emit_nop();
  ce.emit_nop();

  ce.emit_addu(mips_reg_a0, mips_reg_a1, mips_reg_a2);
  ce.emit_addu(mips_reg_sp, mips_reg_ra, mips_reg_s4);
  ce.emit_subu(mips_reg_a0, mips_reg_a1, mips_reg_a2);
  ce.emit_subu(mips_reg_sp, mips_reg_ra, mips_reg_s4);
  ce.emit_xor(mips_reg_a0, mips_reg_a1, mips_reg_a2);
  ce.emit_xor(mips_reg_sp, mips_reg_ra, mips_reg_s4);
  ce.emit_and(mips_reg_a0, mips_reg_a1, mips_reg_a2);
  ce.emit_and(mips_reg_sp, mips_reg_ra, mips_reg_s4);
  ce.emit_or(mips_reg_a0, mips_reg_a1, mips_reg_a2);
  ce.emit_or(mips_reg_sp, mips_reg_ra, mips_reg_s4);
  ce.emit_nor(mips_reg_a0, mips_reg_a1, mips_reg_a2);
  ce.emit_nor(mips_reg_sp, mips_reg_ra, mips_reg_s4);

  ce.emit_slt(mips_reg_a0, mips_reg_a1, mips_reg_a2);
  ce.emit_slt(mips_reg_sp, mips_reg_ra, mips_reg_s4);
  ce.emit_sltu(mips_reg_a0, mips_reg_a1, mips_reg_a2);
  ce.emit_sltu(mips_reg_sp, mips_reg_ra, mips_reg_s4);

  ce.emit_sllv(mips_reg_a0, mips_reg_a1, mips_reg_a2);
  ce.emit_sllv(mips_reg_sp, mips_reg_ra, mips_reg_s4);
  ce.emit_srlv(mips_reg_a0, mips_reg_a1, mips_reg_a2);
  ce.emit_srlv(mips_reg_sp, mips_reg_ra, mips_reg_s4);
  ce.emit_srav(mips_reg_a0, mips_reg_a1, mips_reg_a2);
  ce.emit_srav(mips_reg_sp, mips_reg_ra, mips_reg_s4);
  ce.emit_rotrv(mips_reg_a0, mips_reg_a1, mips_reg_a2);
  ce.emit_rotrv(mips_reg_sp, mips_reg_ra, mips_reg_s4);

  for (unsigned i = 0; i < 4; i++) {
    ce.emit_sll(mips_reg_a0, mips_reg_a1, (i & 1) + (i >> 1) * 30);
    ce.emit_srl(mips_reg_a0, mips_reg_a1, (i & 1) + (i >> 1) * 30);
    ce.emit_sra(mips_reg_a0, mips_reg_a1, (i & 1) + (i >> 1) * 30);
    ce.emit_rotr(mips_reg_a0, mips_reg_a1, (i & 1) + (i >> 1) * 30);
  }

  ce.emit_lui(mips_reg_a0, 0xFFFF);
  ce.emit_lui(mips_reg_a0, 0x8000);
  ce.emit_lui(mips_reg_a0, 0);
  ce.emit_lui(mips_reg_a0, 1);

  const int imm[] = {-1, 0, 1, 0x8000, 0x7FFF};
  for (unsigned i = 0; i < 5; i++) {
    ce.emit_addiu(mips_reg_a0, mips_reg_s6, imm[i]);
    ce.emit_xori(mips_reg_a0, mips_reg_s6, imm[i]);
    ce.emit_ori(mips_reg_a0, mips_reg_s6, imm[i]);
    ce.emit_andi(mips_reg_a0, mips_reg_s6, imm[i]);
    ce.emit_slti(mips_reg_a0, mips_reg_s6, imm[i]);
    ce.emit_sltiu(mips_reg_a0, mips_reg_s6, imm[i]);
  }

  ce.emit_mflo(mips_reg_a3);
  ce.emit_mflo(mips_reg_fp);
  ce.emit_mfhi(mips_reg_a3);
  ce.emit_mfhi(mips_reg_fp);
  ce.emit_mtlo(mips_reg_a3);
  ce.emit_mtlo(mips_reg_fp);
  ce.emit_mthi(mips_reg_a3);
  ce.emit_mthi(mips_reg_fp);

  ce.emit_mult(mips_reg_a2, mips_reg_a3);
  ce.emit_mult(mips_reg_s2, mips_reg_s4);
  ce.emit_multu(mips_reg_a2, mips_reg_a3);
  ce.emit_multu(mips_reg_s2, mips_reg_s4);
  ce.emit_div(mips_reg_a2, mips_reg_a3);
  ce.emit_div(mips_reg_s2, mips_reg_s4);
  ce.emit_divu(mips_reg_a2, mips_reg_a3);
  ce.emit_divu(mips_reg_s2, mips_reg_s4);

  ce.emit_jr(mips_reg_a1);
  ce.emit_jr(mips_reg_ra);
  ce.emit_jalr(mips_reg_a1);
  ce.emit_jalr(mips_reg_s4);

  ce.emit_bltzal(mips_reg_a0, 5);
  ce.emit_bltzal(mips_reg_s4, 4);
  ce.emit_bgezal(mips_reg_a0, 3);
  ce.emit_bgezal(mips_reg_s4, 2);
  ce.emit_bltz(mips_reg_a0, 1);
  ce.emit_bltz(mips_reg_s4, 0);

  const int off[] = {0, 1, -1, 0x7FFF, -0x8000};
  for (unsigned i = 0; i < 5; i++) {
    ce.emit_lb(mips_reg_a0, mips_reg_a1, off[i]);
    ce.emit_lbu(mips_reg_a0, mips_reg_a1, off[i]);
    ce.emit_lh(mips_reg_a0, mips_reg_a1, off[i]);
    ce.emit_lhu(mips_reg_a0, mips_reg_a1, off[i]);
    ce.emit_lw(mips_reg_a0, mips_reg_a1, off[i]);
  }
  for (unsigned i = 0; i < 5; i++) {
    ce.emit_sb(mips_reg_a0, mips_reg_a1, off[i]);
    ce.emit_sh(mips_reg_a0, mips_reg_a1, off[i]);
    ce.emit_sw(mips_reg_a0, mips_reg_a1, off[i]);
  }

  // MIPS32r2/PSP instructions
  ce.emit_ext(mips_reg_v0, mips_reg_a1, 20, 4);
  ce.emit_ext(mips_reg_t7, mips_reg_s4, 3, 9);
  ce.emit_ins(mips_reg_v0, mips_reg_a1, 20, 4);
  ce.emit_ins(mips_reg_t7, mips_reg_s4, 3, 9);

  ce.emit_seb(mips_reg_a3, mips_reg_t1);
  ce.emit_seh(mips_reg_a3, mips_reg_t1);

  fwrite(buffer, 1, ce.emit_ptr-buffer, stdout);
}


