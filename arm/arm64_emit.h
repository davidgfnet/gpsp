/* gameplaySP
 *
 * Copyright (C) 2021 David Guillen Fandos <david@davidgf.net>
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

#ifndef ARM64_EMIT_H
#define ARM64_EMIT_H

#include "arm64_codegen.h"

/* This is a fork of the MIPS dynarec, since A64 has 32 regs as well and
   does not map great to the armv4 instruction set. Also flexible operand
   is fairly limited and cannot map to armv4 well.
   All flags are kept in registers and loaded/restored as needed. */

extern "C" {
  u32 a64_update_gba(u32 pc);

  // Although these are defined as a function, don't call them as
  // such (jump to it instead)
  void a64_indirect_branch_arm(u32 address);
  void a64_indirect_branch_thumb(u32 address);
  void a64_indirect_branch_dual(u32 address);

  u32 execute_read_cpsr();
  u32 execute_read_spsr();
  void execute_swi(u32 pc);
  void a64_cheat_hook(void);

  u32 execute_spsr_restore(u32 address);
  void execute_store_cpsr(u32 new_cpsr, u32 store_mask);
  void execute_store_spsr(u32 new_spsr, u32 store_mask);
  u32 execute_store_cpsr_body(u32 _cpsr, u32 address, u32 store_mask);
  u32 execute_spsr_restore_body(u32 address);

  void execute_aligned_store32(u32 addr, u32 data);
  u32 execute_aligned_load32(u32 addr);

  u32 execute_arm_translate_internal(u32 cycles, void *regptr);
}

typedef enum
{
  arm64_reg_x0,    // arg0
  arm64_reg_x1,    // arg1
  arm64_reg_x2,    // arg2
  arm64_reg_x3,    // temporary reg
  arm64_reg_x4,    // temporary reg
  arm64_reg_x5,    // temporary reg
  arm64_reg_x6,    // ARM reg 0 (temporary)
  arm64_reg_x7,    // ARM reg 1 (temporary)
  arm64_reg_x8,    // ARM reg 2 (temporary)
  arm64_reg_x9,    // ARM reg 3 (temporary)
  arm64_reg_x10,   // ARM reg 4 (temporary)
  arm64_reg_x11,   // ARM reg 5 (temporary)
  arm64_reg_x12,   // ARM reg 6 (temporary)
  arm64_reg_x13,   // ARM reg 7 (temporary)
  arm64_reg_x14,   // ARM reg 8 (temporary)
  arm64_reg_x15,   // ARM reg 9 (temporary)
  arm64_reg_x16,   // ARM reg 10 (temporary)
  arm64_reg_x17,   // ARM reg 11 (temporary)
  arm64_reg_x18,   
  arm64_reg_x19,   // save0 (mem-scratch) (saved)
  arm64_reg_x20,   // base pointer (saved)
  arm64_reg_x21,   // cycle counter (saved)
  arm64_reg_x22,   // C-flag (contains 0 or 1, carry bit)
  arm64_reg_x23,   // V-flag (contains 0 or 1, overflow bit)
  arm64_reg_x24,   // Z-flag (contains 0 or 1, zero bit)
  arm64_reg_x25,   // N-flag (contains 0 or 1, sign bit)
  arm64_reg_x26,   // ARM reg 12 (saved)
  arm64_reg_x27,   // ARM reg 13 (saved)
  arm64_reg_x28,   // ARM reg 14 (saved)
  arm64_reg_x29,   // ARM reg 15 (block start ~ PC) (saved)
  arm64_reg_lr,
  arm64_reg_sp,
} arm64_reg_number;


#define reg_save0   arm64_reg_x19
#define reg_base    arm64_reg_x20
#define reg_cycles  arm64_reg_x21
#define reg_res     arm64_reg_x0
#define reg_a0      arm64_reg_x0
#define reg_a1      arm64_reg_x1
#define reg_a2      arm64_reg_x2
#define reg_temp    arm64_reg_x3
#define reg_temp2   arm64_reg_x4
#define reg_pc      arm64_reg_x29
#define reg_c_cache arm64_reg_x22
#define reg_v_cache arm64_reg_x23
#define reg_z_cache arm64_reg_x24
#define reg_n_cache arm64_reg_x25

#define reg_r0      arm64_reg_x6
#define reg_r1      arm64_reg_x7
#define reg_r2      arm64_reg_x8
#define reg_r3      arm64_reg_x9
#define reg_r4      arm64_reg_x10
#define reg_r5      arm64_reg_x11
#define reg_r6      arm64_reg_x12
#define reg_r7      arm64_reg_x13
#define reg_r8      arm64_reg_x14
#define reg_r9      arm64_reg_x15
#define reg_r10     arm64_reg_x16
#define reg_r11     arm64_reg_x17
#define reg_r12     arm64_reg_x26
#define reg_r13     arm64_reg_x27
#define reg_r14     arm64_reg_x28

#define reg_zero    arm64_reg_sp  // Careful it's also SP

// Writing to r15 goes straight to a0, to be chained with other ops

const u32 arm_to_a64_reg[] =
{
  reg_r0,
  reg_r1,
  reg_r2,
  reg_r3,
  reg_r4,
  reg_r5,
  reg_r6,
  reg_r7,
  reg_r8,
  reg_r9,
  reg_r10,
  reg_r11,
  reg_r12,
  reg_r13,
  reg_r14,
  reg_a0,
  reg_a1,
  reg_a2
};

#define arm_reg_a0   15
#define arm_reg_a1   16
#define arm_reg_a2   17

#define generate_save_reg(regnum)                                             \
  aa64_emit_str(arm_to_a64_reg[regnum], reg_base, regnum)                     \

#define generate_restore_reg(regnum)                                          \
  aa64_emit_ldr(arm_to_a64_reg[regnum], reg_base, regnum)                     \

#define emit_save_regs()                                                      \
{                                                                             \
  unsigned i;                                                                 \
  for (i = 0; i < 15; i++) {                                                  \
    generate_save_reg(i);                                                     \
  }                                                                           \
}

#define emit_restore_regs()                                                   \
{                                                                             \
  unsigned i;                                                                 \
  for (i = 0; i < 15; i++) {                                                  \
    generate_restore_reg(i);                                                  \
  }                                                                           \
}

#define generate_load_reg(ireg, reg_index)                                    \
  aa64_emit_mov(ireg, arm_to_a64_reg[reg_index])                              \

#define generate_load_imm(ireg, imm)                                          \
  if ((s32)(imm) < 0 && (s32)(imm) >= -65536) {                               \
    /* immediate like 0xffffxxxx */                                           \
    aa64_emit_movne(ireg, (~(imm)));                                          \
  } else if (((imm) & 0xffff) == 0) {                                         \
    /* immediate like 0xxxxx0000 */                                           \
    aa64_emit_movhiz(ireg, ((imm) >> 16));                                    \
  } else {                                                                    \
    aa64_emit_movlo(ireg, imm);                                               \
    if ((imm) >= (1 << 16)) {                                                 \
      aa64_emit_movhi(ireg, ((imm) >> 16));                                   \
    }                                                                         \
  }

#define generate_load_pc_2inst(ireg, new_pc)                                  \
{                                                                             \
  aa64_emit_movlo(ireg, new_pc);                                              \
  aa64_emit_movhi(ireg, ((new_pc) >> 16));                                    \
}

#define generate_load_pc(ireg, new_pc)                                        \
{                                                                             \
  s32 pc_delta = (new_pc) - (stored_pc);                                      \
  if (pc_delta >= 0) {                                                        \
    if (pc_delta < 4096) {                                                    \
      aa64_emit_addi(ireg, reg_pc, pc_delta);                                 \
    } else {                                                                  \
      generate_load_imm(ireg, new_pc);                                        \
    }                                                                         \
  } else {                                                                    \
    if (pc_delta >= -4096) {                                                  \
      aa64_emit_subi(ireg, reg_pc, -pc_delta);                                \
    } else {                                                                  \
      generate_load_imm(ireg, new_pc);                                        \
    }                                                                         \
  }                                                                           \
}                                                                             \

#define generate_store_reg(ireg, reg_index)                                   \
  aa64_emit_mov(arm_to_a64_reg[reg_index], ireg)                              \

/* TODO Use addi12 if the immediate is <24 bits ? */
#define generate_alu_imm(imm_type, reg_type, ireg_dest, ireg_src, imm)        \
  if((u32)(imm) < 4096)                                                       \
  {                                                                           \
    aa64_emit_##imm_type(ireg_dest, ireg_src, imm);                           \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_load_imm(reg_temp, imm);                                         \
    aa64_emit_##reg_type(ireg_dest, ireg_src, reg_temp);                      \
  }                                                                           \

#define generate_mov(ireg_dest, ireg_src)                                     \
  aa64_emit_mov(arm_to_a64_reg[ireg_dest], arm_to_a64_reg[ireg_src])          \

#define generate_function_call(function_location)                             \
  aa64_emit_brlink(aa64_br_offset(function_location));                        \

#define generate_cycle_update()                                               \
  if(cycle_count != 0)                                                        \
  {                                                                           \
    unsigned hicycle = cycle_count >> 12;                                     \
    if (hicycle) {                                                            \
      aa64_emit_subi12(reg_cycles, reg_cycles, hicycle);                      \
    }                                                                         \
    aa64_emit_subi(reg_cycles, reg_cycles, (cycle_count & 0xfff));            \
    cycle_count = 0;                                                          \
  }                                                                           \

/* Patches ARM-mode conditional branches */
#define generate_branch_patch_conditional(dest, label)                        \
  aa64_emit_brcond_patch(((u32*)dest), aa64_br_offset_from(label, dest))

#define emit_branch_filler(writeback_location)                                \
  (writeback_location) = translation_ptr;                                     \
  aa64_emit_branch(0);                                                        \

#define generate_branch_patch_unconditional(dest, target)                     \
  aa64_emit_branch_patch((u32*)dest, aa64_br_offset_from(target, dest))       \

#define generate_branch_no_cycle_update(writeback_location, new_pc)           \
  if(pc == idle_loop_target_pc)                                               \
  {                                                                           \
    generate_load_imm(reg_cycles, 0);                                         \
    generate_load_pc(reg_a0, new_pc);                                         \
    generate_function_call(a64_update_gba);                                   \
    emit_branch_filler(writeback_location);                                   \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    aa64_emit_tbnz(reg_cycles, 31, 2);                                        \
    emit_branch_filler(writeback_location);                                   \
    generate_load_pc_2inst(reg_a0, new_pc);                                   \
    generate_function_call(a64_update_gba);                                   \
    aa64_emit_branch(-4);                                                     \
  }                                                                           \

#define generate_branch_cycle_update(writeback_location, new_pc)              \
  generate_cycle_update();                                                    \
  generate_branch_no_cycle_update(writeback_location, new_pc)                 \

// a0 holds the destination

#define generate_indirect_branch_cycle_update(type)                           \
  generate_cycle_update()                                                     \
  generate_indirect_branch_no_cycle_update(type)                              \

#define generate_indirect_branch_no_cycle_update(type)                        \
  aa64_emit_branch(aa64_br_offset(a64_indirect_branch_##type));               \

#define block_prologue_size 0
#define generate_block_prologue()                                             \
  generate_load_imm(reg_pc, stored_pc)                                        \

#define check_generate_n_flag                                                 \
  (flag_status & 0x08)                                                        \

#define check_generate_z_flag                                                 \
  (flag_status & 0x04)                                                        \

#define check_generate_c_flag                                                 \
  (flag_status & 0x02)                                                        \

#define check_generate_v_flag                                                 \
  (flag_status & 0x01)                                                        \

#define generate_load_reg_pc(ireg, reg_index, pc_offset)                      \
  if(reg_index == REG_PC)                                                     \
  {                                                                           \
    generate_load_pc(ireg, (pc + pc_offset));                                 \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_load_reg(ireg, reg_index);                                       \
  }                                                                           \

/* Loads the lowest byte of the specified register */
#define generate_load_reg_pc_lsb(ireg, reg_index, pc_offset)                  \
  if(reg_index == REG_PC)                                                     \
  {                                                                           \
    aa64_emit_movlo(ireg, ((pc + pc_offset) & 0xFF));                         \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    aa64_emit_andi(ireg, arm_to_a64_reg[reg_index], 0, 7); /* 0xFF */         \
  }                                                                           \

#define check_load_reg_pc(arm_reg, reg_index, pc_offset)                      \
  if(reg_index == REG_PC)                                                     \
  {                                                                           \
    reg_index = arm_reg;                                                      \
    generate_load_pc(arm_to_a64_reg[arm_reg], (pc + pc_offset));              \
  }                                                                           \

#define check_store_reg_pc_no_flags(reg_index)                                \
  if(reg_index == REG_PC)                                                     \
  {                                                                           \
    generate_indirect_branch_arm();                                           \
  }                                                                           \

#define check_store_reg_pc_flags(reg_index)                                   \
  if(reg_index == REG_PC)                                                     \
  {                                                                           \
    generate_function_call(execute_spsr_restore);                             \
    generate_indirect_branch_dual();                                          \
  }                                                                           \

#define generate_shift_imm_lsl_no_flags(arm_reg, _rm, _shift)                 \
  check_load_reg_pc(arm_reg, _rm, 8);                                         \
  if(_shift != 0)                                                             \
  {                                                                           \
    aa64_emit_lsl(arm_to_a64_reg[arm_reg], arm_to_a64_reg[_rm], _shift);      \
    _rm = arm_reg;                                                            \
  }                                                                           \

#define generate_shift_imm_lsr_no_flags(arm_reg, _rm, _shift)                 \
  if(_shift != 0)                                                             \
  {                                                                           \
    check_load_reg_pc(arm_reg, _rm, 8);                                       \
    aa64_emit_lsr(arm_to_a64_reg[arm_reg], arm_to_a64_reg[_rm], _shift);      \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    aa64_emit_movlo(arm_to_a64_reg[arm_reg], 0);                              \
  }                                                                           \
  _rm = arm_reg                                                               \

#define generate_shift_imm_asr_no_flags(arm_reg, _rm, _shift)                 \
  check_load_reg_pc(arm_reg, _rm, 8);                                         \
  aa64_emit_asr(arm_to_a64_reg[arm_reg], arm_to_a64_reg[_rm],                 \
                                             _shift ? _shift : 31);           \
  _rm = arm_reg                                                               \

#define generate_shift_imm_ror_no_flags(arm_reg, _rm, _shift)                 \
  check_load_reg_pc(arm_reg, _rm, 8);                                         \
  if(_shift != 0)                                                             \
  {                                                                           \
    aa64_emit_ror(arm_to_a64_reg[arm_reg], arm_to_a64_reg[_rm], _shift);      \
  }                                                                           \
  else                                                                        \
  { /* Special case: RRX (no carry update) */                                 \
    aa64_emit_extr(arm_to_a64_reg[arm_reg],                                   \
                       reg_c_cache, arm_to_a64_reg[_rm], 1);                  \
  }                                                                           \
  _rm = arm_reg                                                               \

#define generate_shift_imm_lsl_flags(arm_reg, _rm, _shift)                    \
  check_load_reg_pc(arm_reg, _rm, 8);                                         \
  if(_shift != 0)                                                             \
  {                                                                           \
    aa64_emit_ubfx(reg_c_cache, arm_to_a64_reg[_rm], (32 - _shift), 1);       \
    aa64_emit_lsl(arm_to_a64_reg[arm_reg], arm_to_a64_reg[_rm], _shift);      \
    _rm = arm_reg;                                                            \
  }                                                                           \

#define generate_shift_imm_lsr_flags(arm_reg, _rm, _shift)                    \
  check_load_reg_pc(arm_reg, _rm, 8);                                         \
  if(_shift != 0)                                                             \
  {                                                                           \
    aa64_emit_ubfx(reg_c_cache, arm_to_a64_reg[_rm], (_shift - 1), 1);        \
    aa64_emit_lsr(arm_to_a64_reg[arm_reg], arm_to_a64_reg[_rm], _shift);      \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    aa64_emit_lsr(reg_c_cache, arm_to_a64_reg[_rm], 31);                      \
    aa64_emit_movlo(arm_to_a64_reg[arm_reg], 0);                              \
  }                                                                           \
  _rm = arm_reg                                                               \

#define generate_shift_imm_asr_flags(arm_reg, _rm, _shift)                    \
  check_load_reg_pc(arm_reg, _rm, 8);                                         \
  if(_shift != 0)                                                             \
  {                                                                           \
    aa64_emit_ubfx(reg_c_cache, arm_to_a64_reg[_rm], (_shift - 1), 1);        \
    aa64_emit_asr(arm_to_a64_reg[arm_reg], arm_to_a64_reg[_rm], _shift);      \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    aa64_emit_lsr(reg_c_cache, arm_to_a64_reg[_rm], 31);                      \
    aa64_emit_asr(arm_to_a64_reg[arm_reg], arm_to_a64_reg[_rm], 31);          \
  }                                                                           \
  _rm = arm_reg                                                               \

#define generate_shift_imm_ror_flags(arm_reg, _rm, _shift)                    \
  check_load_reg_pc(arm_reg, _rm, 8);                                         \
  if(_shift != 0)                                                             \
  {                                                                           \
    aa64_emit_ubfx(reg_c_cache, arm_to_a64_reg[_rm], (_shift - 1), 1);        \
    aa64_emit_ror(arm_to_a64_reg[arm_reg], arm_to_a64_reg[_rm], _shift);      \
  }                                                                           \
  else                                                                        \
  { /* Special case: RRX (carry update) */                                    \
    aa64_emit_extr(reg_temp, reg_c_cache, arm_to_a64_reg[_rm], 1);            \
    aa64_emit_ubfx(reg_c_cache, arm_to_a64_reg[_rm], 0, 1);                   \
    aa64_emit_mov(arm_to_a64_reg[arm_reg], reg_temp);                         \
  }                                                                           \
  _rm = arm_reg                                                               \

#define generate_shift_reg_lsl_no_flags(_rm, _rs)                             \
  generate_load_reg_pc_lsb(reg_temp, _rs, 12);                                \
  aa64_emit_cmpi(reg_temp, 32);                                               \
  aa64_emit_lslv(reg_temp, arm_to_a64_reg[_rm], reg_temp);                    \
  aa64_emit_csel(reg_a0, reg_zero, reg_temp, ccode_hs);                       \

#define generate_shift_reg_lsr_no_flags(_rm, _rs)                             \
  generate_load_reg_pc_lsb(reg_temp, _rs, 12);                                \
  aa64_emit_cmpi(reg_temp, 32);                                               \
  aa64_emit_lsrv(reg_temp, arm_to_a64_reg[_rm], reg_temp);                    \
  aa64_emit_csel(reg_a0, reg_zero, reg_temp, ccode_hs);                       \

#define generate_shift_reg_asr_no_flags(_rm, _rs)                             \
  generate_load_reg_pc_lsb(reg_temp, _rs, 12);                                \
  aa64_emit_cmpi(reg_temp, 31);                                               \
  aa64_emit_asrv(reg_a0, arm_to_a64_reg[_rm], reg_temp);                      \
  aa64_emit_asr(reg_temp, arm_to_a64_reg[_rm], 31);                           \
  aa64_emit_csel(reg_a0, reg_a0, reg_temp, ccode_lo);                         \

#define generate_shift_reg_ror_no_flags(_rm, _rs)                             \
  generate_load_reg_pc_lsb(reg_temp, _rs, 12);                                \
  aa64_emit_rorv(reg_a0, arm_to_a64_reg[_rm], reg_temp)                       \

#define generate_shift_reg_lsl_flags(_rm, _rs)                                \
{                                                                             \
  generate_load_reg_pc_lsb(reg_a1, _rs, 12);                                  \
  generate_load_reg_pc(reg_a0, _rm, 12);                                      \
  /* Only load the result on zero, no shift */                                \
  aa64_emit_cbz(reg_a1, 8);                                                   \
  aa64_emit_subi(reg_temp, reg_a1, 1);                                        \
  aa64_emit_lslv(reg_a0, reg_a0, reg_temp);                                   \
  aa64_emit_lsr(reg_c_cache, reg_a0, 31);                                     \
  aa64_emit_cmpi(reg_a1, 33);                                                 \
  aa64_emit_lsl(reg_a0, reg_a0, 1);                                           \
  /* Result and flag to be zero if shift is > 32 */                           \
  aa64_emit_csel(reg_c_cache, reg_zero, reg_c_cache, ccode_hs);               \
  aa64_emit_csel(reg_a0,      reg_zero, reg_a0,      ccode_hs);               \
}                                                                             \

#define generate_shift_reg_lsr_flags(_rm, _rs)                                \
{                                                                             \
  generate_load_reg_pc_lsb(reg_a1, _rs, 12);                                  \
  generate_load_reg_pc(reg_a0, _rm, 12);                                      \
  /* Only load the result on zero, no shift */                                \
  aa64_emit_cbz(reg_a1, 8);                                                   \
  aa64_emit_subi(reg_temp, reg_a1, 1);                                        \
  aa64_emit_lsrv(reg_a0, reg_a0, reg_temp);                                   \
  aa64_emit_andi(reg_c_cache, reg_a0, 0, 0);  /* imm=1 */                     \
  aa64_emit_cmpi(reg_a1, 33);                                                 \
  aa64_emit_lsr(reg_a0, reg_a0, 1);                                           \
  /* Result and flag to be zero if shift is > 32 */                           \
  aa64_emit_csel(reg_c_cache, reg_zero, reg_c_cache, ccode_hs);               \
  aa64_emit_csel(reg_a0,      reg_zero, reg_a0,      ccode_hs);               \
}                                                                             \

#define generate_shift_reg_asr_flags(_rm, _rs)                                \
  generate_load_reg_pc_lsb(reg_a1, _rs, 12);                                  \
  generate_load_reg_pc(reg_a0, _rm, 12);                                      \
  /* Only load the result on zero, no shift */                                \
  aa64_emit_cbz(reg_a1, 8);                                                   \
  /* Cap shift at 32, since it's equivalent */                                \
  aa64_emit_movlo(reg_temp, 32);                                              \
  aa64_emit_cmpi(reg_a1, 32);                                                 \
  aa64_emit_csel(reg_a1, reg_a1, reg_temp, ccode_ls);                         \
  aa64_emit_subi(reg_temp, reg_a1, 1);                                        \
  aa64_emit_asrv(reg_a0, reg_a0, reg_temp);                                   \
  aa64_emit_andi(reg_c_cache, reg_a0, 0, 0);  /* imm=1 */                     \
  aa64_emit_asr(reg_a0, reg_a0, 1);                                           \

#define generate_shift_reg_ror_flags(_rm, _rs)                                \
  generate_load_reg_pc_lsb(reg_a1, _rs, 12);                                  \
  aa64_emit_cbz(reg_a1, 4);                                                   \
  aa64_emit_subi(reg_temp, reg_a1, 1);                                        \
  aa64_emit_lsrv(reg_temp, arm_to_a64_reg[_rm], reg_temp);                    \
  aa64_emit_andi(reg_c_cache, reg_temp, 0, 0);  /* imm=1 */                   \
  aa64_emit_rorv(reg_a0, arm_to_a64_reg[_rm], reg_a1)                         \

#define generate_shift_imm(arm_reg, name, flags_op)                           \
  u32 shift = (opcode >> 7) & 0x1F;                                           \
  generate_shift_imm_##name##_##flags_op(arm_reg, rm, shift)                  \

#define generate_shift_reg(arm_reg, name, flags_op)                           \
  u32 rs = ((opcode >> 8) & 0x0F);                                            \
  generate_shift_reg_##name##_##flags_op(rm, rs);                             \
  rm = arm_reg                                                                \

// Made functions due to the macro expansion getting too large.
// Returns a new rm if it redirects it (which will happen on most of these
// cases)

#define generate_load_rm_sh(flags_op)                                         \
{                                                                             \
  switch((opcode >> 4) & 0x07)                                                \
  {                                                                           \
    /* LSL imm */                                                             \
    case 0x0:                                                                 \
    {                                                                         \
      generate_shift_imm(arm_reg_a0, lsl, flags_op);                          \
      break;                                                                  \
    }                                                                         \
                                                                              \
    /* LSL reg */                                                             \
    case 0x1:                                                                 \
    {                                                                         \
      generate_shift_reg(arm_reg_a0, lsl, flags_op);                          \
      break;                                                                  \
    }                                                                         \
                                                                              \
    /* LSR imm */                                                             \
    case 0x2:                                                                 \
    {                                                                         \
      generate_shift_imm(arm_reg_a0, lsr, flags_op);                          \
      break;                                                                  \
    }                                                                         \
                                                                              \
    /* LSR reg */                                                             \
    case 0x3:                                                                 \
    {                                                                         \
      generate_shift_reg(arm_reg_a0, lsr, flags_op);                          \
      break;                                                                  \
    }                                                                         \
                                                                              \
    /* ASR imm */                                                             \
    case 0x4:                                                                 \
    {                                                                         \
      generate_shift_imm(arm_reg_a0, asr, flags_op);                          \
      break;                                                                  \
    }                                                                         \
                                                                              \
    /* ASR reg */                                                             \
    case 0x5:                                                                 \
    {                                                                         \
      generate_shift_reg(arm_reg_a0, asr, flags_op);                          \
      break;                                                                  \
    }                                                                         \
                                                                              \
    /* ROR imm */                                                             \
    case 0x6:                                                                 \
    {                                                                         \
      generate_shift_imm(arm_reg_a0, ror, flags_op);                          \
      break;                                                                  \
    }                                                                         \
                                                                              \
    /* ROR reg */                                                             \
    case 0x7:                                                                 \
    {                                                                         \
      generate_shift_reg(arm_reg_a0, ror, flags_op);                          \
      break;                                                                  \
    }                                                                         \
  }                                                                           \
}                                                                             \

#define generate_block_extra_vars()                                           \
  u32 stored_pc = pc;                                                         \

#define generate_block_extra_vars_arm()                                       \
  generate_block_extra_vars();                                                \

#define generate_load_offset_sh()                                             \
  {                                                                           \
    switch((opcode >> 5) & 0x03)                                              \
    {                                                                         \
      /* LSL imm */                                                           \
      case 0x0:                                                               \
      {                                                                       \
        generate_shift_imm(arm_reg_a1, lsl, no_flags);                        \
        break;                                                                \
      }                                                                       \
                                                                              \
      /* LSR imm */                                                           \
      case 0x1:                                                               \
      {                                                                       \
        generate_shift_imm(arm_reg_a1, lsr, no_flags);                        \
        break;                                                                \
      }                                                                       \
                                                                              \
      /* ASR imm */                                                           \
      case 0x2:                                                               \
      {                                                                       \
        generate_shift_imm(arm_reg_a1, asr, no_flags);                        \
        break;                                                                \
      }                                                                       \
                                                                              \
      /* ROR imm */                                                           \
      case 0x3:                                                               \
      {                                                                       \
        generate_shift_imm(arm_reg_a1, ror, no_flags);                        \
        break;                                                                \
      }                                                                       \
    }                                                                         \
  }                                                                           \

#define generate_indirect_branch_arm()                                        \
{                                                                             \
  if(condition == 0x0E)                                                       \
  {                                                                           \
    generate_indirect_branch_cycle_update(arm);                               \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_indirect_branch_no_cycle_update(arm);                            \
  }                                                                           \
}                                                                             \

#define generate_indirect_branch_dual()                                       \
{                                                                             \
  if(condition == 0x0E)                                                       \
  {                                                                           \
    generate_indirect_branch_cycle_update(dual);                              \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_indirect_branch_no_cycle_update(dual);                           \
  }                                                                           \
}                                                                             \

#define generate_block_extra_vars_thumb()                                     \
  generate_block_extra_vars()                                                 \

// It should be okay to still generate result flags, spsr will overwrite them.
// This is pretty infrequent (returning from interrupt handlers, et al) so
// probably not worth optimizing for.

u32 execute_spsr_restore_body(u32 address)
{
  set_cpu_mode(cpu_modes[reg[REG_CPSR] & 0xF]);
  if((io_registers[REG_IE] & io_registers[REG_IF]) &&
   io_registers[REG_IME] && ((reg[REG_CPSR] & 0x80) == 0))
  {
    REG_MODE(MODE_IRQ)[6] = address + 4;
    REG_SPSR(MODE_IRQ) = reg[REG_CPSR];
    reg[REG_CPSR] = 0xD2;
    address = 0x00000018;
    set_cpu_mode(MODE_IRQ);
  }

  if(reg[REG_CPSR] & 0x20)
    address |= 0x01;

  return address;
}

/* Generate the opposite condition to skip the block */
#define generate_condition_eq()                                               \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbz(reg_z_cache, 0);                                              \

#define generate_condition_ne()                                               \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbnz(reg_z_cache, 0);                                             \

#define generate_condition_cs()                                               \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbz(reg_c_cache, 0);                                              \

#define generate_condition_cc()                                               \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbnz(reg_c_cache, 0);                                             \

#define generate_condition_mi()                                               \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbz(reg_n_cache, 0);                                              \

#define generate_condition_pl()                                               \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbnz(reg_n_cache, 0);                                             \

#define generate_condition_vs()                                               \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbz(reg_v_cache, 0);                                              \

#define generate_condition_vc()                                               \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbnz(reg_v_cache, 0);                                             \

#define generate_condition_hi()                                               \
  aa64_emit_eori(reg_temp, reg_c_cache, 0, 0);  /* imm=1 */                   \
  aa64_emit_orr(reg_temp, reg_temp, reg_z_cache);                             \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbnz(reg_temp, 0);                                                \

#define generate_condition_ls()                                               \
  aa64_emit_eori(reg_temp, reg_c_cache, 0, 0);  /* imm=1 */                   \
  aa64_emit_orr(reg_temp, reg_temp, reg_z_cache);                             \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbz(reg_temp, 0);                                                 \

#define generate_condition_ge()                                               \
  aa64_emit_sub(reg_temp, reg_n_cache, reg_v_cache);                          \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbnz(reg_temp, 0);                                                \

#define generate_condition_lt()                                               \
  aa64_emit_sub(reg_temp, reg_n_cache, reg_v_cache);                          \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbz(reg_temp, 0);                                                 \

#define generate_condition_gt()                                               \
  aa64_emit_xor(reg_temp, reg_n_cache, reg_v_cache);                          \
  aa64_emit_orr(reg_temp, reg_temp, reg_z_cache);                             \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbnz(reg_temp, 0);                                                \

#define generate_condition_le()                                               \
  aa64_emit_xor(reg_temp, reg_n_cache, reg_v_cache);                          \
  aa64_emit_orr(reg_temp, reg_temp, reg_z_cache);                             \
  (backpatch_address) = translation_ptr;                                      \
  aa64_emit_cbz(reg_temp, 0);                                                 \

#define generate_condition()                                                  \
  switch(condition)                                                           \
  {                                                                           \
    case 0x0:                                                                 \
      generate_condition_eq();                                                \
      break;                                                                  \
                                                                              \
    case 0x1:                                                                 \
      generate_condition_ne();                                                \
      break;                                                                  \
                                                                              \
    case 0x2:                                                                 \
      generate_condition_cs();                                                \
      break;                                                                  \
                                                                              \
    case 0x3:                                                                 \
      generate_condition_cc();                                                \
      break;                                                                  \
                                                                              \
    case 0x4:                                                                 \
      generate_condition_mi();                                                \
      break;                                                                  \
                                                                              \
    case 0x5:                                                                 \
      generate_condition_pl();                                                \
      break;                                                                  \
                                                                              \
    case 0x6:                                                                 \
      generate_condition_vs();                                                \
      break;                                                                  \
                                                                              \
    case 0x7:                                                                 \
      generate_condition_vc();                                                \
      break;                                                                  \
                                                                              \
    case 0x8:                                                                 \
      generate_condition_hi();                                                \
      break;                                                                  \
                                                                              \
    case 0x9:                                                                 \
      generate_condition_ls();                                                \
      break;                                                                  \
                                                                              \
    case 0xA:                                                                 \
      generate_condition_ge();                                                \
      break;                                                                  \
                                                                              \
    case 0xB:                                                                 \
      generate_condition_lt();                                                \
      break;                                                                  \
                                                                              \
    case 0xC:                                                                 \
      generate_condition_gt();                                                \
      break;                                                                  \
                                                                              \
    case 0xD:                                                                 \
      generate_condition_le();                                                \
      break;                                                                  \
                                                                              \
    case 0xE:                                                                 \
      break;                                                                  \
                                                                              \
    case 0xF:                                                                 \
      break;                                                                  \
  }                                                                           \

#define generate_branch()                                                     \
{                                                                             \
  if(condition == 0x0E)                                                       \
  {                                                                           \
    generate_branch_cycle_update(                                             \
     block_exits[block_exit_position].branch_source,                          \
     block_exits[block_exit_position].branch_target);                         \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_branch_no_cycle_update(                                          \
     block_exits[block_exit_position].branch_source,                          \
     block_exits[block_exit_position].branch_target);                         \
  }                                                                           \
  block_exit_position++;                                                      \
}                  

// Flag generation, using the native CPU ALU flags
#define generate_op_logic_flags(_reg)                                         \
  if(check_generate_n_flag)                                                   \
  {                                                                           \
    aa64_emit_lsr(reg_n_cache, _reg, 31);                                     \
  }                                                                           \
  if(check_generate_z_flag)                                                   \
  {                                                                           \
    aa64_emit_cmpi(_reg, 0);                                                  \
    aa64_emit_cset(reg_z_cache, ccode_eq);                                    \
  }                                                                           \

#define generate_op_arith_flags()                                             \
  /* Assumes that state is in the flags */                                    \
  if(check_generate_c_flag) {                                                 \
    aa64_emit_cset(reg_c_cache, ccode_hs);                                    \
  }                                                                           \
  if(check_generate_v_flag) {                                                 \
    aa64_emit_cset(reg_v_cache, ccode_vs);                                    \
  }                                                                           \
  if(check_generate_n_flag) {                                                 \
    aa64_emit_cset(reg_n_cache, ccode_mi);                                    \
  }                                                                           \
  if(check_generate_z_flag) {                                                 \
    aa64_emit_cset(reg_z_cache, ccode_eq);                                    \
  }                                                                           \

#define load_c_flag()                                                         \
  aa64_emit_movne(reg_temp, 0);                                               \
  aa64_emit_adds(reg_temp, reg_temp, reg_c_cache);                            \

// Muls instruction
#define generate_op_muls_reg(_rd, _rn, _rm)                                   \
  aa64_emit_mul(_rd, _rn, _rm);                                               \
  generate_op_logic_flags(_rd)                                                \


// Register logical operations. Uses also native flags.
#define generate_op_and_reg(_rd, _rn, _rm)                                    \
  aa64_emit_and(_rd, _rn, _rm)                                                \

#define generate_op_orr_reg(_rd, _rn, _rm)                                    \
  aa64_emit_orr(_rd, _rn, _rm)                                                \

#define generate_op_eor_reg(_rd, _rn, _rm)                                    \
  aa64_emit_xor(_rd, _rn, _rm)                                                \

#define generate_op_bic_reg(_rd, _rn, _rm)                                    \
  aa64_emit_bic(_rd, _rn, _rm)                                                \

#define generate_op_ands_reg(_rd, _rn, _rm)                                   \
  aa64_emit_and(_rd, _rn, _rm);                                               \
  generate_op_logic_flags(_rd)                                                \

#define generate_op_orrs_reg(_rd, _rn, _rm)                                   \
  aa64_emit_orr(_rd, _rn, _rm);                                               \
  generate_op_logic_flags(_rd)                                                \

#define generate_op_eors_reg(_rd, _rn, _rm)                                   \
  aa64_emit_xor(_rd, _rn, _rm);                                               \
  generate_op_logic_flags(_rd)                                                \

#define generate_op_bics_reg(_rd, _rn, _rm)                                   \
  aa64_emit_bic(_rd, _rn, _rm);                                               \
  generate_op_logic_flags(_rd)                                                \

// Arithmetic reg-reg operations.

#define generate_op_add_reg(_rd, _rn, _rm)                                    \
  aa64_emit_add(_rd, _rn, _rm)                                                \

#define generate_op_sub_reg(_rd, _rn, _rm)                                    \
  aa64_emit_sub(_rd, _rn, _rm)                                                \

#define generate_op_rsb_reg(_rd, _rn, _rm)                                    \
  aa64_emit_sub(_rd, _rm, _rn)                                                \

#define generate_op_adds_reg(_rd, _rn, _rm)                                   \
  aa64_emit_adds(_rd, _rn, _rm)                                               \
  generate_op_arith_flags()                                                   \

#define generate_op_subs_reg(_rd, _rn, _rm)                                   \
  aa64_emit_subs(_rd, _rn, _rm)                                               \
  generate_op_arith_flags()                                                   \

#define generate_op_rsbs_reg(_rd, _rn, _rm)                                   \
  aa64_emit_subs(_rd, _rm, _rn)                                               \
  generate_op_arith_flags()                                                   \

#define generate_op_adc_reg(_rd, _rn, _rm)                                    \
  aa64_emit_add(_rd, _rn, _rm);  /* Two adds is faster */                     \
  aa64_emit_add(_rd, _rd, reg_c_cache);                                       \

#define generate_op_sbc_reg(_rd, _rn, _rm)                                    \
  /* Rd = Rn - Rm + (C - 1) */                                                \
  aa64_emit_sub(_rd, _rn, _rm);                                               \
  aa64_emit_subi(reg_temp, reg_c_cache, 1);                                   \
  aa64_emit_add(_rd, _rd, reg_temp);                                          \

#define generate_op_rsc_reg(_rd, _rn, _rm)                                    \
  aa64_emit_sub(_rd, _rm, _rn);                                               \
  aa64_emit_subi(reg_temp, reg_c_cache, 1);                                   \
  aa64_emit_add(_rd, _rd, reg_temp);                                          \

/* Must use native instruction to accurately calculate C/V flags */
#define generate_op_adcs_reg(_rd, _rn, _rm)                                   \
  load_c_flag();                                                              \
  aa64_emit_adcs(_rd, _rn, _rm);                                              \
  generate_op_arith_flags()                                                   \

#define generate_op_sbcs_reg(_rd, _rn, _rm)                                   \
  load_c_flag();                                                              \
  aa64_emit_sbcs(_rd, _rn, _rm);                                              \
  generate_op_arith_flags()                                                   \

#define generate_op_rscs_reg(_rd, _rn, _rm)                                   \
  load_c_flag();                                                              \
  aa64_emit_sbcs(_rd, _rm, _rn);                                              \
  generate_op_arith_flags()                                                   \


#define arm_op_check_yes()                                                    \
  check_load_reg_pc(arm_reg_a1, rn, 8)                                        \

#define arm_op_check_no()                                                     \

#define arm_generate_op_reg_flags(name, load_op)                              \
  arm_decode_data_proc_reg(opcode);                                           \
  if(check_generate_c_flag)                                                   \
  {                                                                           \
    generate_load_rm_sh(flags);                                               \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_load_rm_sh(no_flags);                                            \
  }                                                                           \
                                                                              \
  arm_op_check_##load_op();                                                   \
  generate_op_##name##_reg(arm_to_a64_reg[rd], arm_to_a64_reg[rn],            \
                              arm_to_a64_reg[rm])                             \

#define arm_generate_op_reg(name, load_op)                                    \
  arm_decode_data_proc_reg(opcode);                                           \
  generate_load_rm_sh(no_flags);                                              \
  arm_op_check_##load_op();                                                   \
  generate_op_##name##_reg(arm_to_a64_reg[rd], arm_to_a64_reg[rn],            \
                              arm_to_a64_reg[rm])                             \

#define arm_data_proc(name, type, flags_op)                                   \
{                                                                             \
  arm_generate_op_##type(name, yes);                                          \
  check_store_reg_pc_##flags_op(rd);                                          \
}                                                                             \

// 32 bit multiplication

#define arm_multiply_flags_yes(_rd)                                           \
  generate_op_logic_flags(_rd)                                                \

#define arm_multiply_flags_no(_rd)                                            \

#define arm_multiply_add_no()                                                 \
  aa64_emit_mul(arm_to_a64_reg[rd], arm_to_a64_reg[rm], arm_to_a64_reg[rs]);  \

#define arm_multiply_add_yes()                                                \
  aa64_emit_madd(arm_to_a64_reg[rd], arm_to_a64_reg[rn],                      \
                 arm_to_a64_reg[rm], arm_to_a64_reg[rs]);                     \

#define arm_multiply(add_op, flags)                                           \
{                                                                             \
  arm_decode_multiply();                                                      \
  arm_multiply_add_##add_op();                                                \
  arm_multiply_flags_##flags(arm_to_a64_reg[rd]);                             \
}                                                                             \

// 32x32 -> 64 multiplication (long mul/muladd)

#define generate_multiply_s64()                                               \
  aa64_emit_smaddl(reg_temp, reg_zero, arm_to_a64_reg[rm], arm_to_a64_reg[rs])

#define generate_multiply_u64()                                               \
  aa64_emit_umaddl(reg_temp, reg_zero, arm_to_a64_reg[rm], arm_to_a64_reg[rs])

#define generate_multiply_s64_add()                                           \
  aa64_emit_smaddl(reg_temp, reg_temp, arm_to_a64_reg[rm], arm_to_a64_reg[rs])

#define generate_multiply_u64_add()                                           \
  aa64_emit_umaddl(reg_temp, reg_temp, arm_to_a64_reg[rm], arm_to_a64_reg[rs])

#define arm_multiply_long_flags_yes(_rdlo, _rdhi)                             \
  aa64_emit_orr(reg_z_cache, _rdlo, _rdhi);                                   \
  aa64_emit_cmpi(reg_z_cache, 0);                                             \
  aa64_emit_cset(reg_z_cache, ccode_eq);                                      \
  aa64_emit_lsr(reg_n_cache, _rdhi, 31);                                      \

#define arm_multiply_long_flags_no(_rdlo, _rdhi)                              \

#define arm_multiply_long_add_yes(name)                                       \
  aa64_emit_merge_regs(reg_temp, arm_to_a64_reg[rdhi], arm_to_a64_reg[rdlo]); \
  generate_multiply_##name()                                                  \

#define arm_multiply_long_add_no(name)                                        \
  generate_multiply_##name()                                                  \

#define arm_multiply_long(name, add_op, flags)                                \
{                                                                             \
  arm_decode_multiply_long();                                                 \
  arm_multiply_long_add_##add_op(name);                                       \
  aa64_emit_andi64(arm_to_a64_reg[rdlo], reg_temp, 0, 31);                    \
  aa64_emit_lsr64(arm_to_a64_reg[rdhi], reg_temp, 32);                        \
  arm_multiply_long_flags_##flags(arm_to_a64_reg[rdlo], arm_to_a64_reg[rdhi]);\
}                                                                             \

#define arm_psr_read(op_type, psr_reg)                                        \
  generate_function_call(execute_read_##psr_reg);                             \
  generate_store_reg(reg_res, rd)                                             \

u32 execute_store_cpsr_body(u32 _cpsr, u32 address, u32 store_mask)
{
  reg[REG_CPSR] = _cpsr;
  if(store_mask & 0xFF)
  {
    set_cpu_mode(cpu_modes[_cpsr & 0xF]);
    if((io_registers[REG_IE] & io_registers[REG_IF]) &&
     io_registers[REG_IME] && ((_cpsr & 0x80) == 0))
    {
      REG_MODE(MODE_IRQ)[6] = address + 4;
      REG_SPSR(MODE_IRQ) = _cpsr;
      reg[REG_CPSR] = 0xD2;
      set_cpu_mode(MODE_IRQ);
      return 0x00000018;
    }
  }

  return 0;
}

#define arm_psr_load_new_reg()                                                \
  generate_load_reg(reg_a0, rm)                                               \

#define arm_psr_load_new_imm()                                                \
  generate_load_imm(reg_a0, imm)                                              \

#define arm_psr_store_cpsr(op_type)                                           \
  generate_load_pc(reg_a1, (pc));                                             \
  generate_load_imm(reg_a2, cpsr_masks[psr_pfield][0]);                       \
  generate_load_imm(reg_temp, cpsr_masks[psr_pfield][1]);                     \
  generate_function_call(execute_store_cpsr)                                  \

#define arm_psr_store_spsr(op_type)                                           \
  generate_load_imm(reg_a1, spsr_masks[psr_pfield]);                          \
  generate_function_call(execute_store_spsr)                                  \

#define arm_psr_store(op_type, psr_reg)                                       \
  arm_psr_load_new_##op_type();                                               \
  arm_psr_store_##psr_reg(op_type)

#define arm_psr(op_type, transfer_type, psr_reg)                              \
{                                                                             \
  arm_decode_psr_##op_type(opcode);                                           \
  arm_psr_##transfer_type(op_type, psr_reg);                                  \
}                                                                             \

#define thumb_load_pc_pool_const(rd, value)                                   \
  generate_load_imm(arm_to_a64_reg[rd], (value));                             \

#define arm_access_memory_load(mem_type)                                      \
  cycle_count += 2;                                                           \
  generate_load_pc(reg_a1, (pc));                                             \
  generate_function_call(execute_load_##mem_type);                            \
  generate_store_reg(reg_res, rd);                                            \
  check_store_reg_pc_no_flags(rd)                                             \

#define arm_access_memory_store(mem_type)                                     \
  cycle_count++;                                                              \
  generate_load_pc(reg_a2, (pc + 4));                                         \
  generate_load_reg_pc(reg_a1, rd, 12);                                       \
  generate_function_call(execute_store_##mem_type)                            \

#define arm_access_memory_reg_pre_up()                                        \
  aa64_emit_add(reg_a0, arm_to_a64_reg[rn], arm_to_a64_reg[rm])               \

#define arm_access_memory_reg_pre_down()                                      \
  aa64_emit_sub(reg_a0, arm_to_a64_reg[rn], arm_to_a64_reg[rm])               \

#define arm_access_memory_reg_pre(adjust_dir)                                 \
  check_load_reg_pc(arm_reg_a0, rn, 8);                                       \
  arm_access_memory_reg_pre_##adjust_dir()                                    \

#define arm_access_memory_reg_pre_wb(adjust_dir)                              \
  arm_access_memory_reg_pre(adjust_dir);                                      \
  generate_store_reg(reg_a0, rn)                                              \

#define arm_access_memory_reg_post_up()                                       \
  aa64_emit_add(arm_to_a64_reg[rn], arm_to_a64_reg[rn], arm_to_a64_reg[rm])   \

#define arm_access_memory_reg_post_down()                                     \
  aa64_emit_sub(arm_to_a64_reg[rn], arm_to_a64_reg[rn], arm_to_a64_reg[rm])   \

#define arm_access_memory_reg_post(adjust_dir)                                \
  generate_load_reg(reg_a0, rn);                                              \
  arm_access_memory_reg_post_##adjust_dir()                                   \

#define arm_access_memory_imm_pre_up()                                        \
  aa64_emit_addi(reg_a0, arm_to_a64_reg[rn], offset)                          \

#define arm_access_memory_imm_pre_down()                                      \
  aa64_emit_subi(reg_a0, arm_to_a64_reg[rn], offset)                          \

#define arm_access_memory_imm_pre(adjust_dir)                                 \
  check_load_reg_pc(arm_reg_a0, rn, 8);                                       \
  arm_access_memory_imm_pre_##adjust_dir()                                    \

#define arm_access_memory_imm_pre_wb(adjust_dir)                              \
  arm_access_memory_imm_pre(adjust_dir);                                      \
  generate_store_reg(reg_a0, rn)                                              \

#define arm_access_memory_imm_post_up()                                       \
  aa64_emit_addi(arm_to_a64_reg[rn], arm_to_a64_reg[rn], offset)              \

#define arm_access_memory_imm_post_down()                                     \
  aa64_emit_subi(arm_to_a64_reg[rn], arm_to_a64_reg[rn], offset)              \

#define arm_access_memory_imm_post(adjust_dir)                                \
  generate_load_reg(reg_a0, rn);                                              \
  arm_access_memory_imm_post_##adjust_dir()                                   \

#define arm_data_trans_reg(adjust_op, adjust_dir)                             \
  arm_decode_data_trans_reg();                                                \
  generate_load_offset_sh();                                                  \
  arm_access_memory_reg_##adjust_op(adjust_dir)                               \

#define arm_data_trans_imm(adjust_op, adjust_dir)                             \
  arm_decode_data_trans_imm();                                                \
  arm_access_memory_imm_##adjust_op(adjust_dir)                               \

#define arm_data_trans_half_reg(adjust_op, adjust_dir)                        \
  arm_decode_half_trans_r();                                                  \
  arm_access_memory_reg_##adjust_op(adjust_dir)                               \

#define arm_data_trans_half_imm(adjust_op, adjust_dir)                        \
  arm_decode_half_trans_of();                                                 \
  arm_access_memory_imm_##adjust_op(adjust_dir)                               \

#define arm_access_memory(access_type, direction, adjust_op, mem_type,        \
 offset_type)                                                                 \
{                                                                             \
  arm_data_trans_##offset_type(adjust_op, direction);                         \
  arm_access_memory_##access_type(mem_type);                                  \
}                                                                             \

#define word_bit_count(word)                                                  \
  (bit_count[word >> 8] + bit_count[word & 0xFF])                             \

#define arm_block_memory_load()                                               \
  generate_function_call(execute_aligned_load32);                             \
  generate_store_reg(reg_res, i)                                              \

#define arm_block_memory_store()                                              \
  generate_load_reg_pc(reg_a1, i, 8);                                         \
  generate_function_call(execute_aligned_store32)                             \

#define arm_block_memory_final_load(writeback_type)                           \
  arm_block_memory_load()                                                     \

#define arm_block_memory_final_store(writeback_type)                          \
  generate_load_pc(reg_a2, (pc + 4));                                         \
  generate_load_reg(reg_a1, i)                                                \
  arm_block_memory_writeback_post_store(writeback_type);                      \
  generate_function_call(execute_store_u32);                                  \

#define arm_block_memory_adjust_pc_store()                                    \

#define arm_block_memory_adjust_pc_load()                                     \
  if(reg_list & 0x8000)                                                       \
  {                                                                           \
    generate_indirect_branch_arm();                                           \
  }                                                                           \

#define arm_block_memory_offset_down_a()                                      \
  aa64_emit_subi(reg_save0, base_reg, ((word_bit_count(reg_list)-1) * 4))     \

#define arm_block_memory_offset_down_b()                                      \
  aa64_emit_subi(reg_save0, base_reg, (word_bit_count(reg_list) * 4))         \

#define arm_block_memory_offset_no()                                          \
  aa64_emit_addi(reg_save0, base_reg, 0)                                      \

#define arm_block_memory_offset_up()                                          \
  aa64_emit_addi(reg_save0, base_reg, 4)                                      \

#define arm_block_memory_writeback_down()                                     \
  aa64_emit_subi(base_reg, base_reg, (word_bit_count(reg_list) * 4))          \

#define arm_block_memory_writeback_up()                                       \
  aa64_emit_addi(base_reg, base_reg, (word_bit_count(reg_list) * 4))          \

#define arm_block_memory_writeback_no()

// Only emit writeback if the register is not in the list

#define arm_block_memory_writeback_pre_load(writeback_type)                   \
  if(!((reg_list >> rn) & 0x01))                                              \
  {                                                                           \
    arm_block_memory_writeback_##writeback_type();                            \
  }                                                                           \

#define arm_block_memory_writeback_pre_store(writeback_type)
#define arm_block_memory_writeback_post_store(writeback_type)                 \
  arm_block_memory_writeback_##writeback_type()                               \

#define arm_block_memory(access_type, offset_type, writeback_type, s_bit)     \
{                                                                             \
  arm_decode_block_trans();                                                   \
  u32 i;                                                                      \
  u32 offset = 0;                                                             \
  u32 base_reg = arm_to_a64_reg[rn];                                          \
                                                                              \
  arm_block_memory_offset_##offset_type();                                    \
  arm_block_memory_writeback_pre_##access_type(writeback_type);               \
                                                                              \
  {                                                                           \
    aa64_emit_andi(reg_save0, reg_save0, 30, 29);  /* clear 2 LSB */          \
                                                                              \
    for(i = 0; i < 16; i++)                                                   \
    {                                                                         \
      if((reg_list >> i) & 0x01)                                              \
      {                                                                       \
        cycle_count++;                                                        \
        aa64_emit_addi(reg_a0, reg_save0, offset);                            \
        if(reg_list & ~((2 << i) - 1))                                        \
        {                                                                     \
          arm_block_memory_##access_type();                                   \
          offset += 4;                                                        \
        }                                                                     \
        else                                                                  \
        {                                                                     \
          arm_block_memory_final_##access_type(writeback_type);               \
          break;                                                              \
        }                                                                     \
      }                                                                       \
    }                                                                         \
                                                                              \
    arm_block_memory_adjust_pc_##access_type();                               \
  }                                                                           \
}                                                                             \


// ARM: rn *must* be different from rm and rd. rm *can* be the same as rd.

#define arm_swap(type)                                                        \
{                                                                             \
  arm_decode_swap();                                                          \
  cycle_count += 3;                                                           \
  generate_load_reg(reg_a0, rn);                                              \
  generate_function_call(execute_load_##type);                                \
  generate_load_reg(reg_a1, rm);                                              \
  generate_store_reg(reg_res, rd);                                            \
  generate_load_reg(reg_a0, rn);                                              \
  generate_function_call(execute_store_##type);                               \
}                                                                             \

#define check_store_reg_pc_thumb(_rd)                                         \
  if(_rd == REG_PC)                                                           \
  {                                                                           \
    generate_indirect_branch_cycle_update(thumb);                             \
  }                                                                           \

// Decode types: shift, alu_op
// Operation types: lsl, lsr, asr, ror
// Affects N/Z/C flags

#define thumb_generate_shift_imm(name)                                        \
  if(check_generate_c_flag)                                                   \
  {                                                                           \
    generate_shift_imm_##name##_flags(rd, rs, imm);                           \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_shift_imm_##name##_no_flags(rd, rs, imm);                        \
  }                                                                           \
  if(rs != rd)                                                                \
  {                                                                           \
    generate_mov(rd, rs);                                                     \
  }                                                                           \

#define thumb_generate_shift_reg(name)                                        \
{                                                                             \
  u32 original_rd = rd;                                                       \
  if(check_generate_c_flag)                                                   \
  {                                                                           \
    generate_shift_reg_##name##_flags(rd, rs);                                \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_shift_reg_##name##_no_flags(rd, rs);                             \
  }                                                                           \
  aa64_emit_addi(arm_to_a64_reg[original_rd], reg_a0, 0);                     \
}                                                                             \

#define thumb_shift(decode_type, op_type, value_type)                         \
{                                                                             \
  thumb_decode_##decode_type();                                               \
  thumb_generate_shift_##value_type(op_type);                                 \
  generate_op_logic_flags(arm_to_a64_reg[rd]);                                \
}                                                                             \

// Operation types: imm, mem_reg, mem_imm

#define thumb_access_memory_load(mem_type, reg_rd)                            \
  cycle_count += 2;                                                           \
  generate_load_pc(reg_a1, (pc));                                             \
  generate_function_call(execute_load_##mem_type);                            \
  generate_store_reg(reg_res, reg_rd)                                         \

#define thumb_access_memory_store(mem_type, reg_rd)                           \
  cycle_count++;                                                              \
  generate_load_reg(reg_a1, reg_rd)                                           \
  generate_load_pc(reg_a2, (pc + 2));                                         \
  generate_function_call(execute_store_##mem_type);                           \

#define thumb_access_memory_generate_address_pc_relative(offset, reg_rb,      \
 reg_ro)                                                                      \
  generate_load_pc(reg_a0, (offset))                                          \

#define thumb_access_memory_generate_address_reg_imm(offset, reg_rb, reg_ro)  \
  aa64_emit_addi(reg_a0, arm_to_a64_reg[reg_rb], (offset))                    \

#define thumb_access_memory_generate_address_reg_imm_sp(offset, reg_rb, reg_ro) \
  aa64_emit_addi(reg_a0, arm_to_a64_reg[reg_rb], (offset * 4))                \

#define thumb_access_memory_generate_address_reg_reg(offset, reg_rb, reg_ro)  \
  aa64_emit_add(reg_a0, arm_to_a64_reg[reg_rb], arm_to_a64_reg[reg_ro])       \

#define thumb_access_memory(access_type, op_type, reg_rd, reg_rb, reg_ro,     \
 address_type, offset, mem_type)                                              \
{                                                                             \
  thumb_decode_##op_type();                                                   \
  thumb_access_memory_generate_address_##address_type(offset, reg_rb,         \
   reg_ro);                                                                   \
  thumb_access_memory_##access_type(mem_type, reg_rd);                        \
}                                                                             \


#define thumb_block_address_preadjust_no(base_reg)                            \
  aa64_emit_addi(reg_save0, base_reg, 0)                                      \

#define thumb_block_address_preadjust_down(base_reg)                          \
  aa64_emit_subi(reg_save0, base_reg, (bit_count[reg_list] * 4));             \
  aa64_emit_addi(base_reg, reg_save0, 0);                                     \

#define thumb_block_address_preadjust_push_lr(base_reg)                       \
  aa64_emit_subi(reg_save0, base_reg, ((bit_count[reg_list] + 1) * 4));       \
  aa64_emit_addi(base_reg, reg_save0, 0);                                     \

#define thumb_block_address_postadjust_no(base_reg)                           \

#define thumb_block_address_postadjust_up(base_reg)                           \
  aa64_emit_addi(base_reg, reg_save0, (bit_count[reg_list] * 4));             \

#define thumb_block_address_postadjust_pop_pc(base_reg)                       \
  aa64_emit_addi(base_reg, reg_save0, ((bit_count[reg_list] + 1) * 4));       \

#define thumb_block_address_postadjust_push_lr(base_reg)                      \

#define thumb_block_memory_load()                                             \
  generate_function_call(execute_aligned_load32);                             \
  generate_store_reg(reg_res, i)                                              \

#define thumb_block_memory_store()                                            \
  generate_load_reg(reg_a1, i)                                                \
  generate_function_call(execute_aligned_store32);                            \

#define thumb_block_memory_final_load()                                       \
  thumb_block_memory_load()                                                   \

#define thumb_block_memory_final_store()                                      \
  generate_load_pc(reg_a2, (pc + 2));                                         \
  generate_load_reg(reg_a1, i)                                                \
  generate_function_call(execute_store_u32);                                  \

#define thumb_block_memory_final_no(access_type)                              \
  thumb_block_memory_final_##access_type()                                    \

#define thumb_block_memory_final_up(access_type)                              \
  thumb_block_memory_final_##access_type()                                    \

#define thumb_block_memory_final_down(access_type)                            \
  thumb_block_memory_final_##access_type()                                    \

#define thumb_block_memory_final_push_lr(access_type)                         \
  thumb_block_memory_##access_type()                                          \

#define thumb_block_memory_final_pop_pc(access_type)                          \
  thumb_block_memory_##access_type()                                          \

#define thumb_block_memory_extra_no()                                         \

#define thumb_block_memory_extra_up()                                         \

#define thumb_block_memory_extra_down()                                       \

#define thumb_block_memory_extra_push_lr()                                    \
  aa64_emit_addi(reg_a0, reg_save0, (bit_count[reg_list] * 4));               \
  generate_load_reg(reg_a1, REG_LR)                                           \
  generate_function_call(execute_aligned_store32);                            \

#define thumb_block_memory_extra_pop_pc()                                     \
  aa64_emit_addi(reg_a0, reg_save0, (bit_count[reg_list] * 4));               \
  generate_function_call(execute_aligned_load32);                             \
  generate_indirect_branch_cycle_update(thumb)                                \

#define thumb_block_memory(access_type, pre_op, post_op, arm_base_reg)        \
{                                                                             \
  thumb_decode_rlist();                                                       \
  u32 i;                                                                      \
  u32 offset = 0;                                                             \
  u32 base_reg = arm_to_a64_reg[arm_base_reg];                                \
                                                                              \
  thumb_block_address_preadjust_##pre_op(base_reg);                           \
  thumb_block_address_postadjust_##post_op(base_reg);                         \
                                                                              \
  {                                                                           \
    aa64_emit_andi(reg_save0, reg_save0, 30, 29);  /* clear 2 LSB */          \
                                                                              \
    for(i = 0; i < 8; i++)                                                    \
    {                                                                         \
      if((reg_list >> i) & 0x01)                                              \
      {                                                                       \
        cycle_count++;                                                        \
        aa64_emit_addi(reg_a0, reg_save0, offset);                            \
        if(reg_list & ~((2 << i) - 1))                                        \
        {                                                                     \
          thumb_block_memory_##access_type();                                 \
          offset += 4;                                                        \
        }                                                                     \
        else                                                                  \
        {                                                                     \
          thumb_block_memory_final_##post_op(access_type);                    \
          break;                                                              \
        }                                                                     \
      }                                                                       \
    }                                                                         \
                                                                              \
    thumb_block_memory_extra_##post_op();                                     \
  }                                                                           \
}

#define generate_branch_filler(condition_code, writeback_location)            \
  (writeback_location) = translation_ptr;                                     \
  aa64_emit_brcond(condition_code, 0);                                        \


#define thumb_conditional_branch(condition)                                   \
{                                                                             \
  generate_cycle_update();                                                    \
  generate_condition_##condition();                                           \
  generate_branch_no_cycle_update(                                            \
   block_exits[block_exit_position].branch_source,                            \
   block_exits[block_exit_position].branch_target);                           \
  generate_branch_patch_conditional(backpatch_address, translation_ptr);      \
  block_exit_position++;                                                      \
}                                                                             \

#define update_nzcv_flags()                                                   \
  /* Assumes that state is in the flags */                                    \
  if (it.gen_flag_c()) {                                                      \
    aa64_emit_cset(reg_c_cache, ccode_hs);                                    \
  }                                                                           \
  if (it.gen_flag_v()) {                                                      \
    aa64_emit_cset(reg_v_cache, ccode_vs);                                    \
  }                                                                           \
  if (it.gen_flag_n()) {                                                      \
    aa64_emit_cset(reg_n_cache, ccode_mi);                                    \
  }                                                                           \
  if (it.gen_flag_z()) {                                                      \
    aa64_emit_cset(reg_z_cache, ccode_eq);                                    \
  }                                                                           \

inline bool isimm12(u32 imm) {
  return (imm & 0xFFFFF000) == 0;
}

inline bool isimm24(u32 imm) {
  return (imm & 0xFF000000) == 0;
}

inline bool isimmhi12(u32 imm) {
  return (imm & 0xFF000FFF) == 0;
}

class CodeEmitter : public CodeEmitterBase {
public:
  CodeEmitter(u8 *emit_ptr, u8 *emit_end, u32 pc)
   : CodeEmitterBase(emit_ptr, emit_end), block_pc(pc) {}

  u32 block_pc;              // PC address for the block base

  // Register allocation (for registers that could contain PC)
  inline u32 load_alloc_reg(u32 regn, u32 tmp_reg, u32 pcvalue) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this
    if (regn == REG_PC) {
      generate_load_pc(tmp_reg, pcvalue);
      return tmp_reg;
    }
    return arm_to_a64_reg[regn];
  }

  // Forces a register load!
  inline void force_load_reg(u32 regn, u32 outreg, u32 pcvalue) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this
    if (regn == REG_PC) {
      generate_load_pc(outreg, pcvalue);
    } else {
      generate_load_reg(outreg, regn);
    }
  }

  inline u32 store_alloc_reg(u32 regn, u32 tmp_reg) {
    if (regn == REG_PC)
      return tmp_reg;
    return arm_to_a64_reg[regn];
  }

  inline void load_alloc_reg_lsb(u32 regn, u32 native_reg, u32 pcvalue) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    if (regn == REG_PC) {
      aa64_emit_movlo(native_reg, (pcvalue & 0xFF));
    } else {
      aa64_emit_andi(native_reg, arm_to_a64_reg[regn], 0, 7); /* 0xFF */
    }
  }

  template <FlagOperation flgmode>
  inline void update_nz_flags(const ARMInst & it, u32 reg) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    if (flgmode == SetFlags) {
      if (it.gen_flag_n()) {
        aa64_emit_lsr(reg_n_cache, reg, 31);
      }
      if (it.gen_flag_z()) {
        aa64_emit_cmpi(reg, 0);
        aa64_emit_cset(reg_z_cache, ccode_eq);
      }
    }
  }

  inline void update_nz_flags(const ThumbInst & it, u32 reg) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    if (it.gen_flag_n()) {
      aa64_emit_lsr(reg_n_cache, reg, 31);
    }
    if (it.gen_flag_z()) {
      aa64_emit_cmpi(reg, 0);
      aa64_emit_cset(reg_z_cache, ccode_eq);
    }
  }

  template <FlagOperation flgmode>
  inline void upd_nz_flags_imm(const ARMInst & it, u32 imm) {
    if (flgmode == SetFlags) {
      u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
      if (it.gen_flag_z()) {
        aa64_emit_movlo(reg_z_cache, (imm ? 0 : 1));
      }
      if (it.gen_flag_n()) {
        aa64_emit_movlo(reg_n_cache, (imm >> 31));
      }
    }
  }

  // ======== Thumb instructions ======================================
  template <AluOperation aluop>
  inline void thumb_aluop3(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rs = arm_to_a64_reg[it.rs()];
    u32 rn = arm_to_a64_reg[it.rn()];
    u32 rd = arm_to_a64_reg[it.rd()];

    switch (aluop) {
    case OpAdd:
      aa64_emit_adds(rd, rs, rn);
      break;
    case OpSub:
      aa64_emit_subs(rd, rs, rn);
      break;
    };

    update_nzcv_flags();
  }

  template <AluOperation aluop>
  inline void thumb_aluop2(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rs = arm_to_a64_reg[it.rs()];
    u32 rd = arm_to_a64_reg[it.rd()];

    switch (aluop) {
    case OpOrr:
      aa64_emit_orr(rd, rd, rs);
      update_nz_flags(it, rd);
      break;
    case OpAnd:
      aa64_emit_and(rd, rd, rs);
      update_nz_flags(it, rd);
      break;
    case OpXor:
      aa64_emit_xor(rd, rd, rs);
      update_nz_flags(it, rd);
      break;
    case OpBic:
      aa64_emit_bic(rd, rd, rs);
      update_nz_flags(it, rd);
      break;
    case OpMul:
      aa64_emit_mul(rd, rd, rs);
      update_nz_flags(it, rd);
      break;
    case OpAdd:
      aa64_emit_adds(rd, rd, rs);
      update_nzcv_flags();
      break;
    case OpSub:
      aa64_emit_subs(rd, rd, rs);
      update_nzcv_flags();
      break;
    case OpAdc:
      load_c_flag();
      aa64_emit_adcs(rd, rd, rs);
      update_nzcv_flags();
      break;
    case OpSbc:
      load_c_flag();
      aa64_emit_sbcs(rd, rd, rs);
      update_nzcv_flags();
      break;
    };
  }

  template <AluOperation aluop>
  inline void thumb_aluop1(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rs = arm_to_a64_reg[it.rs()];
    u32 rd = arm_to_a64_reg[it.rd()];

    switch (aluop) {
    case OpNeg:
      aa64_emit_subs(rd, reg_zero, rs);
      update_nzcv_flags();
      break;
    case OpMvn:
      aa64_emit_orn(rd, reg_zero, rs);
      update_nz_flags(it, rd);
      break;
    };
  }

  template <AluOperation testop>
  inline void thumb_testop(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rs = arm_to_a64_reg[it.rs()];
    u32 rd = arm_to_a64_reg[it.rd()];

    switch (testop) {
    case OpTst:
      aa64_emit_and(reg_temp, rd, rs);
      update_nz_flags(it, reg_temp);
      break;
    case OpCmp:
      aa64_emit_subs(reg_zero, rd, rs);
      update_nzcv_flags();
      break;
    case OpCmn:
      aa64_emit_adds(reg_zero, rd, rs);
      update_nzcv_flags();
      break;
    };
  }

  template <AluOperation aluop>
  inline void thumb_aluimm2(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 rd = arm_to_a64_reg[it.rd8()];

    switch (aluop) {
    case OpMov:
      aa64_emit_movlo(rd, it.imm8());
      aa64_emit_movlo(reg_n_cache, 0);
      aa64_emit_movlo(reg_z_cache, it.imm8() ? 0 : 1);
      break;
    case OpAdd:
      aa64_emit_addis(rd, rd, it.imm8());
      update_nzcv_flags();
      break;
    case OpSub:
      aa64_emit_subis(rd, rd, it.imm8());
      update_nzcv_flags();
      break;
    case OpCmp:
      aa64_emit_subis(reg_temp, rd, it.imm8());
      update_nzcv_flags();
      break;
    };
  }

  template <AluOperation aluop>
  inline void thumb_aluimm3(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rs = arm_to_a64_reg[it.rs()];
    u32 rd = arm_to_a64_reg[it.rd()];

    switch (aluop) {
    case OpAdd:
      aa64_emit_addis(rd, rs, it.imm3());
      break;
    case OpSub:
      aa64_emit_subis(rd, rs, it.imm3());
      break;
    };

    update_nzcv_flags();
  }

  template <AluOperation aluop>
  inline void thumb_aluhi(const ThumbInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rs = load_alloc_reg(it.rs_hi(), reg_a1, it.pc + 4);

    // TODO: Improve PC writes (reg_a0 *must* contain the new PC, which is not clear).
    if (aluop == OpAdd) {
      u32 rd = load_alloc_reg(it.rd_hi(), reg_a0, it.pc + 4);
      aa64_emit_add(rd, rd, rs);
      check_store_reg_pc_thumb(it.rd_hi());
    } else if (aluop == OpCmp) {
      u32 rd = load_alloc_reg(it.rd_hi(), reg_a0, it.pc + 4);
      aa64_emit_subs(reg_temp, rd, rs);
      update_nzcv_flags();
    } else if (aluop == OpMov) {
      u32 rd = store_alloc_reg(it.rd_hi(), reg_a0);
      aa64_emit_mov(rd, rs);
      check_store_reg_pc_thumb(it.rd_hi());
    }
  }

  template <u32 ref_reg>
  inline void thumb_regoff(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this
    if (ref_reg == REG_PC) {
      generate_load_pc(arm_to_a64_reg[it.rd8()], (it.pc & ~2) + 4 + 4 * it.imm8());
    } else {
      aa64_emit_addi(arm_to_a64_reg[it.rd8()], arm_to_a64_reg[ref_reg], 4 * it.imm8());
    }
  }

  inline void thumb_spadj(s8 offset) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    if (offset >= 0) {
      aa64_emit_addi(reg_r13, reg_r13,  offset * 4);
    } else {
      aa64_emit_subi(reg_r13, reg_r13, -offset * 4);
    }
  }


  // ======== ARM instructions ======================================
  template <AluOperation aluop, FlagOperation flg>
  inline void arm_aluimm3(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rn = load_alloc_reg(it.rn(), reg_a1, it.pc + 8);
    u32 rd = store_alloc_reg(it.rd(), reg_a0);

    // Immediate is a 8 bit rotated immediate
    const u32 sa = it.rot4() * 2;   // TODO remove this absurd scaling here
    const u32 imm = rotr32(it.imm8(), sa);

    // Set/Clear carry flag if appropriate (rotation result)
    if (aluop == OpAnd || aluop == OpOrr || aluop == OpXor || aluop == OpBic) {
      if (flg == SetFlags && it.rot4() != 0 && it.gen_flag_c()) {
        aa64_emit_movlo(reg_c_cache, ((imm) >> 31));
      }
    }

    // TODO: Implement arm64 immediates for logic operations.
    // Should be easy for 8 bit rotated immediates.
    switch (aluop) {
    case OpAnd:
      generate_load_imm(reg_temp, imm);
      aa64_emit_and(rd, rn, reg_temp);
      update_nz_flags<flg>(it, rd);
      break;
    case OpOrr:
      generate_load_imm(reg_temp, imm);
      aa64_emit_orr(rd, rn, reg_temp);
      update_nz_flags<flg>(it, rd);
      break;
    case OpXor:
      generate_load_imm(reg_temp, imm);
      aa64_emit_xor(rd, rn, reg_temp);
      update_nz_flags<flg>(it, rd);
      break;
    case OpBic:
      generate_load_imm(reg_temp, imm);
      aa64_emit_bic(rd, rn, reg_temp);
      update_nz_flags<flg>(it, rd);
      break;
    case OpAdd:
      if (flg == NoFlags) {
        if (isimm12(imm)) {
          aa64_emit_addi(rd, rn, imm);
        } else if (isimmhi12(imm)) {
          aa64_emit_addi12(rd, rn, (imm >> 12));
        } else if (isimm24(imm)) {
          aa64_emit_addi(rd, rn, (imm & 0xFFF));
          aa64_emit_addi12(rd, rd, ((imm >> 12) & 0xFFF));
        } else {
          generate_load_imm(reg_temp, imm);
          aa64_emit_add(rd, rn, reg_temp);
        }
      } else {
        if (isimm12(imm)) {
          aa64_emit_addis(rd, rn, imm);
        } else if (isimmhi12(imm)) {
          aa64_emit_addis12(rd, rn, (imm >> 12));
        } else {
          generate_load_imm(reg_temp, imm);
          aa64_emit_adds(rd, rn, reg_temp);
        }
        update_nzcv_flags();
      }
      break;
    case OpAdc:
      load_c_flag();
      generate_load_imm(reg_temp, imm);
      if (flg == NoFlags) {
        aa64_emit_adc(rd, rn, reg_temp);
      } else {
        aa64_emit_adcs(rd, rn, reg_temp);
        update_nzcv_flags();
      }
      break;
    case OpSub:
      if (flg == NoFlags) {
        if (isimm12(imm)) {
          aa64_emit_subi(rd, rn, imm);
        } else if (isimmhi12(imm)) {
          aa64_emit_subi12(rd, rn, (imm >> 12));
        } else if (isimm24(imm)) {
          aa64_emit_subi(rd, rn, (imm & 0xFFF));
          aa64_emit_subi12(rd, rd, ((imm >> 12) & 0xFFF));
        } else {
          generate_load_imm(reg_temp, imm);
          aa64_emit_sub(rd, rn, reg_temp);
        }
      } else {
        if (isimm12(imm)) {
          aa64_emit_subis(rd, rn, imm);
        } else if (isimmhi12(imm)) {
          aa64_emit_subis12(rd, rn, (imm >> 12));
        } else {
          generate_load_imm(reg_temp, imm);
          aa64_emit_subs(rd, rn, reg_temp);
        }
        update_nzcv_flags();
      }
      break;
    case OpRsb:
      generate_load_imm(reg_temp, imm);
      if (flg == NoFlags) {
        aa64_emit_sub(rd, reg_temp, rn);
      } else {
        aa64_emit_subs(rd, reg_temp, rn);
        update_nzcv_flags();
      }
      break;
    case OpSbc:
      load_c_flag();
      generate_load_imm(reg_temp, imm);
      if (flg == NoFlags) {
        aa64_emit_sbc(rd, rn, reg_temp);
      } else {
        aa64_emit_sbcs(rd, rn, reg_temp);
        update_nzcv_flags();
      }
      break;
    case OpRsc:
      load_c_flag();
      generate_load_imm(reg_temp, imm);
      if (flg == NoFlags) {
        aa64_emit_sbc(rd, reg_temp, rn);
      } else {
        aa64_emit_sbcs(rd, reg_temp, rn);
        update_nzcv_flags();
      }
      break;
    };

    const u8 condition = it.cond();        // TODO remove this
    if (flg == NoFlags) {
      check_store_reg_pc_no_flags(it.rd());
    } else {
      check_store_reg_pc_flags(it.rd());
    }
  }

  template <AluOperation aluop>
  inline void arm_aluimm2(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rn = load_alloc_reg(it.rn(), reg_a1, it.pc + 8);

    // Immediate is a 8 bit rotated immediate
    const u32 sa = it.rot4() * 2;   // TODO remove this absurd scaling here
    const u32 imm = rotr32(it.imm8(), sa);

    // Set/Clear carry flag if appropriate (rotation result)
    if (it.rot4() != 0 && it.gen_flag_c()) {
      aa64_emit_movlo(reg_c_cache, ((imm) >> 31));
    }

    switch (aluop) {
    case OpTst:
      generate_load_imm(reg_temp, imm);
      aa64_emit_and(reg_temp, rn, reg_temp);
      update_nz_flags<SetFlags>(it, reg_temp);
      break;
    case OpTeq:
      generate_load_imm(reg_temp, imm);
      aa64_emit_xor(reg_temp, rn, reg_temp);
      update_nz_flags<SetFlags>(it, reg_temp);
      break;
    case OpCmp:
      if (isimm12(imm)) {
        aa64_emit_subis(reg_temp, rn, imm);
      } else if (isimmhi12(imm)) {
        aa64_emit_subis12(reg_temp, rn, (imm >> 12));
      } else {
        generate_load_imm(reg_temp, imm);
        aa64_emit_subs(reg_temp, rn, reg_temp);
      }
      update_nzcv_flags();
      break;
    case OpCmn:
      if (isimm12(imm)) {
        aa64_emit_addis(reg_temp, rn, imm);
      } else if (isimmhi12(imm)) {
        aa64_emit_addis12(reg_temp, rn, (imm >> 12));
      } else {
        generate_load_imm(reg_temp, imm);
        aa64_emit_adds(reg_temp, rn, reg_temp);
      }
      update_nzcv_flags();
      break;
    };
  }

  template <AluOperation aluop, FlagOperation flg>
  inline void arm_aluimm1(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rd = store_alloc_reg(it.rd(), reg_a0);

    // Immediate is a 8 bit rotated immediate
    const u32 sa = it.rot4() * 2;   // TODO remove this absurd scaling here
    u32 imm = rotr32(it.imm8(), sa);

    // Set/Clear carry flag if appropriate (rotation result)
    if (flg == SetFlags && it.rot4() != 0 && it.gen_flag_c()) {
      aa64_emit_movlo(reg_c_cache, ((imm) >> 31));
    }

    if (aluop == OpMvn)
      imm = ~imm;

    generate_load_imm(rd, imm);
    upd_nz_flags_imm<flg>(it, imm);

    const u8 condition = it.cond();        // TODO remove this
    if (flg == NoFlags) {
      check_store_reg_pc_no_flags(it.rd());
    } else {
      check_store_reg_pc_flags(it.rd());
    }
  }

  // Calculates operand 2 when register is shifted/rotated by an immediate.
  template<FlagOperation flg>
  inline void emit_op2_shimm(const ARMInst &it) {
    u32 imm = it.op2sa();      // Shift amount [0..31]
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rm;

    switch (it.op2smode()) {
    case 0:      /* LSL */
      rm = load_alloc_reg(it.rm(), reg_a0, it.pc + 8);
      if (flg == SetFlags && imm) {
        aa64_emit_ubfx(reg_c_cache, rm, (32 - imm), 1);
      }
      aa64_emit_lsl(reg_a0, rm, imm);
      break;

    case 1:      /* LSR (0 means shift by 32) */
      if (imm) {
        rm = load_alloc_reg(it.rm(), reg_a0, it.pc + 8);
        if (flg == SetFlags) {
          aa64_emit_ubfx(reg_c_cache, rm, (imm - 1), 1);
        }
        aa64_emit_lsr(reg_a0, rm, imm);
      } else {
        if (flg == SetFlags) {
          rm = load_alloc_reg(it.rm(), reg_a0, it.pc + 8);
          aa64_emit_lsr(reg_c_cache, rm, 31);
        }
        aa64_emit_movlo(reg_a0, 0);
      }
      break;

    case 2:      /* ASR (0 is also shift by 32) */
      rm = load_alloc_reg(it.rm(), reg_a0, it.pc + 8);
      if (flg == SetFlags) {
        aa64_emit_ubfx(reg_c_cache, rm, ((imm ? imm : 32) - 1), 1);
      }
      aa64_emit_asr(reg_a0, rm, (imm ? imm : 31));
      break;

    case 3:      /* ROR */
      rm = load_alloc_reg(it.rm(), reg_a1, it.pc + 8);
      if (imm) {
        if (flg == SetFlags) {
          aa64_emit_ubfx(reg_c_cache, rm, (imm - 1), 1);
        }
        aa64_emit_ror(reg_a0, rm, imm);
      } else {
        aa64_emit_extr(reg_a0, reg_c_cache, rm, 1);
        if (flg == SetFlags) {
          aa64_emit_ubfx(reg_c_cache, rm, 0, 1);
        }
      }
      break;
    };
  }

  // Calculates operand 2 when register is shifted/rotated by another register.
  template<FlagOperation flg>
  inline void emit_op2_shreg(const ARMInst &it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    load_alloc_reg_lsb(it.rs(), reg_a1, it.pc + 12);  // Loads the LSB byte only!

    if (flg == SetFlags) {
      force_load_reg(it.rm(), reg_a0, it.pc + 12);    // Load reg into a0
      switch (it.op2smode()) {
        case 0:     /* LSL */
          aa64_emit_cbz(reg_a1, 8);           // Skip it all on shift = 0
          // This code works if shift <= 32.
          aa64_emit_subi(reg_temp, reg_a1, 1);
          aa64_emit_lslv(reg_a0, reg_a0, reg_temp);
          aa64_emit_lsr(reg_c_cache, reg_a0, 31);
          aa64_emit_cmpi(reg_a1, 33);
          aa64_emit_lsl(reg_a0, reg_a0, 1);
          // If shift > 32 we just clear both reg and C flag
          aa64_emit_csel(reg_c_cache, reg_zero, reg_c_cache, ccode_hs);
          aa64_emit_csel(reg_a0,      reg_zero, reg_a0,      ccode_hs);
          break;
        case 1:     /* LSR */
          aa64_emit_cbz(reg_a1, 8);           // Skip it all on shift = 0
          aa64_emit_subi(reg_temp, reg_a1, 1);
          aa64_emit_lsrv(reg_a0, reg_a0, reg_temp);
          aa64_emit_andi(reg_c_cache, reg_a0, 0, 0);  /* imm=1 */
          aa64_emit_cmpi(reg_a1, 33);
          aa64_emit_lsr(reg_a0, reg_a0, 1);
          // If shift > 32 we just clear both reg and C flag
          aa64_emit_csel(reg_c_cache, reg_zero, reg_c_cache, ccode_hs);
          aa64_emit_csel(reg_a0,      reg_zero, reg_a0,      ccode_hs);
          break;
        case 2:     /* ASR */
          aa64_emit_cbz(reg_a1, 8);           // Skip it all on shift = 0
          aa64_emit_movlo(reg_temp, 32);      // Cap amount to 32.
          aa64_emit_cmpi(reg_a1, 32);
          aa64_emit_csel(reg_a1, reg_a1, reg_temp, ccode_ls);
          aa64_emit_subi(reg_temp, reg_a1, 1);
          aa64_emit_asrv(reg_a0, reg_a0, reg_temp);
          aa64_emit_andi(reg_c_cache, reg_a0, 0, 0);  /* imm=1 */
          aa64_emit_asr(reg_a0, reg_a0, 1);
          break;
        case 3:     /* ROR */
          // ror/lsrv only use the 5 LSB in aarch64
          aa64_emit_rorv(reg_a0, reg_a0, reg_a1);
          aa64_emit_cbz(reg_a1, 2);
          aa64_emit_lsr(reg_c_cache, reg_a0, 31);
          break;
      };
    } else {
      u32 rm = load_alloc_reg(it.rm(), reg_a0, it.pc + 12);
      switch (it.op2smode()) {
        case 0:     /* LSL */
          aa64_emit_cmpi(reg_a1, 32);
          aa64_emit_lslv(reg_temp, rm, reg_a1);
          aa64_emit_csel(reg_a0, reg_zero, reg_temp, ccode_hs);
          break;
        case 1:     /* LSR */
          aa64_emit_cmpi(reg_a1, 32);
          aa64_emit_lsrv(reg_temp, rm, reg_a1);
          aa64_emit_csel(reg_a0, reg_zero, reg_temp, ccode_hs);
          break;
        case 2:     /* ASR */
          aa64_emit_cmpi(reg_a1, 31);
          aa64_emit_asr(reg_temp, rm, 31);
          aa64_emit_asrv(reg_a0, rm, reg_a1);
          aa64_emit_csel(reg_a0, reg_a0, reg_temp, ccode_lo);
          break;
        case 3:     /* ROR */
          aa64_emit_rorv(reg_a0, rm, reg_a1);
          break;
      };
    }
  }

  // Calculates the flex operand, honoring flag (CF) generation and returns the
  // native register where the value is placed (either reg_a0 or some ARM reg).
  template <FlagOperation flg>
  inline u32 emit_arm_aluop2(const ARMInst & it) {
    // Calculates the Op2 part and writes it to a0
    if (it.op2imm()) {
      // Special case: LSL with imm = 0 means unmodified register (and Cflag).
      // Just return the register directly (or scratch to a0 for PC)
      // Saves one instruction (it is relatively common)
      if (it.op2sa() == 0 && it.op2smode() == 0 /* LSL */)
        return load_alloc_reg(it.rm(), reg_a0, it.pc + 8);

      if (flg == SetFlags && it.gen_flag_c())
        emit_op2_shimm<SetFlags>(it);
      else
        emit_op2_shimm<NoFlags>(it);
    } else {
      if (flg == SetFlags && it.gen_flag_c())
        emit_op2_shreg<SetFlags>(it);
      else
        emit_op2_shreg<NoFlags>(it);
    }
    return reg_a0;
  }

  // 3 regs (with op2) instructions
  template <AluOperation aluop, FlagOperation flg>
  inline void arm_alureg3(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    // Generate op2 to a0, op1 to a1
    u32 regop2 = emit_arm_aluop2<flg>(it);
    u32 rn = load_alloc_reg(it.rn(), reg_a1, it.pc + (it.op2imm() ? 8 : 12));
    u32 rd = store_alloc_reg(it.rd(), reg_a0);

    switch (aluop) {
    case OpAnd:
      aa64_emit_and(rd, rn, regop2);
      break;
    case OpOrr:
      aa64_emit_orr(rd, rn, regop2);
      break;
    case OpXor:
      aa64_emit_xor(rd, rn, regop2);
      break;
    case OpBic:
      aa64_emit_bic(rd, rn, regop2);
      break;
    };

    update_nz_flags<flg>(it, rd);

    const u8 condition = it.cond();        // TODO remove this
    if (flg == NoFlags) {
      check_store_reg_pc_no_flags(it.rd());
    } else {
      check_store_reg_pc_flags(it.rd());
    }
  }

  template <AluOperation aluop, FlagOperation flg>
  inline void arm_alureg1(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    u32 regop2 = emit_arm_aluop2<flg>(it);   // Generate op2 to a0
    u32 rd = store_alloc_reg(it.rd(), reg_a0);

    switch (aluop) {
    case OpMvn:
      aa64_emit_orn(rd, reg_zero, regop2);
      break;
    case OpMov:
      aa64_emit_mov(rd, regop2);
      break;
    };

    update_nz_flags<flg>(it, rd);

    const u8 condition = it.cond();        // TODO remove this
    if (flg == NoFlags) {
      check_store_reg_pc_no_flags(it.rd());
    } else {
      check_store_reg_pc_flags(it.rd());
    }
  }

  // compare/test instructions
  template <AluOperation aluop, FlagOperation c_flag>
  inline void arm_alureg2(const ARMInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    u32 regop2 = emit_arm_aluop2<c_flag>(it);   // Generate op2 to a0 (with/without C flag)
    u32 rn = load_alloc_reg(it.rn(), reg_a1, it.pc + (it.op2imm() ? 8 : 12));

    switch (aluop) {
    case OpAnd:
       aa64_emit_and(reg_temp, rn, regop2);
       update_nz_flags<SetFlags>(it, reg_temp);
       break;
    case OpXor:
       aa64_emit_xor(reg_temp, rn, regop2);
       update_nz_flags<SetFlags>(it, reg_temp);
       break;
    case OpCmp:
      aa64_emit_subs(reg_zero, rn, regop2);
      update_nzcv_flags();
      break;
    case OpCmn:
      aa64_emit_adds(reg_zero, rn, regop2);
      update_nzcv_flags();
      break;
    };
  }

};


#define arm_conditional_block_header()                                        \
  generate_cycle_update();                                                    \
  generate_condition();                                                       \

#define arm_b()                                                               \
  generate_branch()                                                           \

#define arm_bl()                                                              \
  generate_load_pc(reg_r14, (pc + 4));                                        \
  generate_branch()                                                           \

#define arm_bx()                                                              \
  arm_decode_branchx(opcode);                                                 \
  generate_load_reg(reg_a0, rn);                                              \
  generate_indirect_branch_dual()                                             \

#define arm_swi()                                                             \
  generate_load_pc(reg_a0, (pc + 4));                                         \
  generate_function_call(execute_swi);                                        \
  generate_branch()                                                           \

#define thumb_b()                                                             \
  generate_branch_cycle_update(                                               \
   block_exits[block_exit_position].branch_source,                            \
   block_exits[block_exit_position].branch_target);                           \
  block_exit_position++                                                       \

#define thumb_bl()                                                            \
  generate_load_pc(reg_r14, ((pc + 2) | 0x01));                               \
  generate_branch_cycle_update(                                               \
   block_exits[block_exit_position].branch_source,                            \
   block_exits[block_exit_position].branch_target);                           \
  block_exit_position++                                                       \

#define thumb_blh()                                                           \
{                                                                             \
  thumb_decode_branch();                                                      \
  generate_alu_imm(addi, add, reg_a0, reg_r14, (offset * 2));                 \
  generate_load_pc(reg_r14, ((pc + 2) | 0x01));                               \
  generate_indirect_branch_cycle_update(thumb);                               \
  break;                                                                      \
}                                                                             \

#define thumb_bx()                                                            \
{                                                                             \
  thumb_decode_hireg_op();                                                    \
  generate_load_reg_pc(reg_a0, rs, 4);                                        \
  generate_indirect_branch_cycle_update(dual);                                \
}                                                                             \

#define thumb_process_cheats()                                                \
  generate_function_call(a64_cheat_hook);

#define arm_process_cheats()                                                  \
  generate_function_call(a64_cheat_hook);

#ifdef TRACE_INSTRUCTIONS
  void trace_instruction(u32 pc, u32 mode)
  {
    if (mode)
      printf("Executed arm %x\n", pc);
    else
      printf("Executed thumb %x\n", pc);
    #ifdef TRACE_REGISTERS
    print_regs();
    #endif
  }

  #define emit_trace_instruction(pc, mode)                                      \
    emit_save_regs();                                                           \
    generate_load_imm(reg_a0, pc);                                              \
    generate_load_imm(reg_a1, mode);                                            \
    generate_function_call(trace_instruction);                                  \
    emit_restore_regs()
  #define emit_trace_thumb_instruction(pc) emit_trace_instruction(pc, 0)
  #define emit_trace_arm_instruction(pc)   emit_trace_instruction(pc, 1)
#else
  #define emit_trace_thumb_instruction(pc)
  #define emit_trace_arm_instruction(pc)
#endif

#define thumb_swi()                                                           \
  generate_load_pc(reg_a0, (pc + 2));                                         \
  generate_function_call(execute_swi);                                        \
  generate_branch_cycle_update(                                               \
   block_exits[block_exit_position].branch_source,                            \
   block_exits[block_exit_position].branch_target);                           \
  block_exit_position++                                                       \

#define arm_hle_div(cpu_mode)                                                 \
  aa64_emit_sdiv(reg_r3, reg_r0, reg_r1);                                     \
  aa64_emit_msub(reg_r1, reg_r0, reg_r1, reg_r3);                             \
  aa64_emit_mov(reg_r0, reg_r3);                                              \
  aa64_emit_cmpi(reg_r3, 0);                                                  \
  aa64_emit_csneg(reg_r3, reg_r3, reg_r3, ccode_ge);                          \

#define arm_hle_div_arm(cpu_mode)                                             \
  aa64_emit_sdiv(reg_r3, reg_r1, reg_r0);                                     \
  aa64_emit_msub(reg_r1, reg_r1, reg_r0, reg_r3);                             \
  aa64_emit_mov(reg_r0, reg_r3);                                              \
  aa64_emit_cmpi(reg_r3, 0);                                                  \
  aa64_emit_csneg(reg_r3, reg_r3, reg_r3, ccode_ge);                          \

#define generate_translation_gate(type)                                       \
  generate_load_pc(reg_a0, pc);                                               \
  generate_indirect_branch_no_cycle_update(type)                              \


extern void* ldst_handler_functions[16*4 + 17*6];
extern void* ldst_lookup_tables[16*4 + 17*6];


void init_emitter(bool must_swap) {
  rom_cache_watermark = INITIAL_ROM_WATERMARK;
  init_bios_hooks();

  // Generate handler table
  memcpy(ldst_lookup_tables, ldst_handler_functions, sizeof(ldst_lookup_tables));
}


u32 execute_arm_translate(u32 cycles) {
  return execute_arm_translate_internal(cycles, &reg[0]);
}

#endif


