/* gameplaySP
 *
 * Copyright (C) 2006 Exophase <exophase@gmail.com>
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

#ifndef X86_EMIT_H
#define X86_EMIT_H

#include "x86/x86_codegen.h"

extern "C" {

  u32 x86_update_gba(u32 pc);

  // Although these are defined as a function, don't call them as
  // such (jump to it instead)
  void x86_indirect_branch_arm(u32 address);
  void x86_indirect_branch_thumb(u32 address);
  void x86_indirect_branch_dual(u32 address);

  void function_cc execute_store_cpsr(u32 new_cpsr, u32 store_mask);
  u32 execute_store_cpsr_body();

  u32 function_cc execute_arm_translate_internal(u32 cycles, void *regptr);
}

#define reg_base    x86_reg_ebx        // Saved register
#define reg_cycles  x86_reg_ebp        // Saved register
#define reg_a0      x86_reg_eax
#define reg_a1      x86_reg_edx
#define reg_a2      x86_reg_ecx
#define reg_t0      x86_reg_esi
#define reg_rv      x86_reg_eax

#if defined(_WIN64)
  #define reg_arg0  x86_reg_ecx
  #define reg_arg1  x86_reg_edx
#elif defined(__x86_64__) || defined(__amd64__)
  #define reg_arg0  x86_reg_edi
  #define reg_arg1  x86_reg_esi
#else
  #define reg_arg0  x86_reg_eax
  #define reg_arg1  x86_reg_edx
#endif

/* Offsets from reg_base, see stub.S */
#define SPSR_BASE_OFF   0xA9100

#define generate_test_imm(ireg, imm)                                          \
  x86_emit_test_reg_imm(reg_##ireg, imm);                                     \

#define generate_test_memreg(ireg_ref, arm_reg_src)                           \
  x86_emit_test_reg_mem(reg_##ireg_ref, reg_base, arm_reg_src * 4)            \

#define generate_cmp_memreg(ireg_ref, arm_reg_src)                            \
  x86_emit_cmp_reg_mem(reg_##ireg_ref, reg_base, arm_reg_src * 4)             \

#define generate_cmp_imm(ireg, imm)                                           \
  x86_emit_cmp_reg_imm(reg_##ireg, imm)                                       \

#define generate_cmp_reg(ireg, ireg2)                                         \
  x86_emit_cmp_reg_reg(reg_##ireg, reg_##ireg2)                               \

#define generate_update_flag(condcode, regnum)                                \
  x86_emit_setcc_mem(condcode, reg_base, regnum * 4)                          \

#define generate_load_spsr(ireg, idxr)                                        \
  x86_emit_mov_reg_mem_idx(reg_##ireg, reg_base, 2, reg_##idxr, SPSR_BASE_OFF);

#define generate_store_spsr(ireg, idxr)                                       \
  x86_emit_mov_mem_idx_reg(reg_##ireg, reg_base, 2, reg_##idxr, SPSR_BASE_OFF);

#define generate_load_reg(ireg, reg_index)                                    \
  x86_emit_mov_reg_mem(reg_##ireg, reg_base, reg_index * 4);                  \

#define generate_load_pc(ireg, new_pc)                                        \
  x86_emit_mov_reg_imm(reg_##ireg, (new_pc))                                  \

#define generate_load_imm(ireg, imm)                                          \
  x86_emit_mov_reg_imm(reg_##ireg, imm)                                       \

#define generate_store_reg(ireg, reg_index)                                   \
  x86_emit_mov_mem_reg(reg_##ireg, reg_base, (reg_index) * 4)                 \

#define generate_store_reg_i32(imm32, reg_index)                              \
  x86_emit_mov_mem_imm((imm32), reg_base, (reg_index) * 4)                    \

#define generate_shift_left(ireg, imm)                                        \
  x86_emit_shl_reg_imm(reg_##ireg, imm)                                       \

#define generate_shift_left_var(ireg)                                         \
  x86_emit_shl_reg_reg(reg_##ireg)                                            \

#define generate_shift_right(ireg, imm)                                       \
  x86_emit_shr_reg_imm(reg_##ireg, imm)                                       \

#define generate_shift_right_var(ireg)                                        \
  x86_emit_shr_reg_reg(reg_##ireg)                                            \

#define generate_shift_right_arithmetic(ireg, imm)                            \
  x86_emit_sar_reg_imm(reg_##ireg, imm)                                       \

#define generate_shift_right_arithmetic_var(ireg)                             \
  x86_emit_sar_reg_reg(reg_##ireg)                                            \

#define generate_rotate_right(ireg, imm)                                      \
  x86_emit_ror_reg_imm(reg_##ireg, imm)                                       \

#define generate_rotate_right_var(ireg)                                       \
  x86_emit_rot_reg_reg(ror, reg_##ireg)                                       \

#define generate_rcr(ireg)                                                    \
  x86_emit_rot_reg_reg(rcr, reg_##ireg)                                       \

#define generate_rcr1(ireg)                                                   \
  x86_emit_rot_reg1(rcr, reg_##ireg)                                          \

#define generate_and_mem(imm, ireg_base, offset)                              \
  x86_emit_and_mem_imm(imm, reg_##ireg_base, (offset))                        \

#define generate_and(ireg_dest, ireg_src)                                     \
  x86_emit_and_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_add(ireg_dest, ireg_src)                                     \
  x86_emit_add_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_adc(ireg_dest, ireg_src)                                     \
  x86_emit_adc_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_add_memreg(ireg_dest, arm_reg_src)                           \
  x86_emit_add_reg_mem(reg_##ireg_dest, reg_base, arm_reg_src * 4)            \

#define generate_sub(ireg_dest, ireg_src)                                     \
  x86_emit_sub_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_sbb(ireg_dest, ireg_src)                                     \
  x86_emit_sbb_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_or(ireg_dest, ireg_src)                                      \
  x86_emit_or_reg_reg(reg_##ireg_dest, reg_##ireg_src)                        \

#define generate_or_mem(ireg_dest, arm_reg_src)                               \
  x86_emit_or_reg_mem(reg_##ireg_dest, reg_base, arm_reg_src * 4)             \

#define generate_xor(ireg_dest, ireg_src)                                     \
  x86_emit_xor_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_xor_mem(ireg_dest, arm_reg_src)                              \
  x86_emit_xor_reg_mem(reg_##ireg_dest, reg_base, arm_reg_src * 4)            \

#define generate_add_imm(ireg, imm)                                           \
  if ((imm) != 0) {                                                           \
    x86_emit_add_reg_imm(reg_##ireg, imm)                                     \
  }                                                                           \

#define generate_sub_imm(ireg, imm)                                           \
  if ((imm) != 0) {                                                           \
    x86_emit_sub_reg_imm(reg_##ireg, imm)                                     \
  }                                                                           \

#define generate_xor_imm(ireg, imm)                                           \
  x86_emit_xor_reg_imm(reg_##ireg, imm)                                       \

#define generate_add_reg_reg_imm(ireg_dest, ireg_src, imm)                    \
  x86_emit_lea_reg_mem(reg_##ireg_dest, reg_##ireg_src, imm)                  \

#define generate_and_imm(ireg, imm)                                           \
  x86_emit_and_reg_imm(reg_##ireg, imm)                                       \

#define generate_or_imm(ireg, imm)                                            \
  x86_emit_or_reg_imm(reg_##ireg, imm)                                        \

#define generate_mov(ireg_dest, ireg_src)                                     \
  x86_emit_mov_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_not(ireg)                                                    \
  x86_emit_not_reg(reg_##ireg)                                                \

#define generate_multiply(ireg)                                               \
  x86_emit_imul_eax_reg(reg_##ireg)                                           \

#define generate_multiply_s64(ireg)                                           \
  x86_emit_imul_eax_reg(reg_##ireg)                                           \

#define generate_multiply_u64(ireg)                                           \
  x86_emit_mul_eax_reg(reg_##ireg)                                            \

#define generate_multiply_s64_add(ireg_src, ireg_lo, ireg_hi)                 \
  x86_emit_imul_eax_reg(reg_##ireg_src);                                      \
  x86_emit_add_reg_reg(reg_a0, reg_##ireg_lo);                                \
  x86_emit_adc_reg_reg(reg_a1, reg_##ireg_hi)                                 \

#define generate_multiply_u64_add(ireg_src, ireg_lo, ireg_hi)                 \
  x86_emit_mul_eax_reg(reg_##ireg_src);                                       \
  x86_emit_add_reg_reg(reg_a0, reg_##ireg_lo);                                \
  x86_emit_adc_reg_reg(reg_a1, reg_##ireg_hi)                                 \


#define generate_function_call(function_location)                             \
  x86_emit_call_offset(x86_relative_offset(translation_ptr,                   \
   function_location, 4));                                                    \

#define generate_exit_block()                                                 \
  x86_emit_ret();                                                             \

#define generate_cycle_update()                                               \
  generate_sub_imm(cycles, cycle_count);                                      \
  cycle_count = 0                                                             \

#define generate_branch_patch_conditional(dest, offset)                       \
  *((u32 *)(dest)) = x86_relative_offset(dest, offset, 4)                     \

#define generate_branch_patch_unconditional(dest, offset)                     \
  *((u32 *)(dest)) = x86_relative_offset(dest, offset, 4)                     \

#define generate_branch_no_cycle_update(writeback_location, new_pc)           \
  if(pc == idle_loop_target_pc)                                               \
  {                                                                           \
    generate_load_imm(cycles, 0);                                             \
    x86_emit_mov_reg_imm(reg_a0, new_pc);                                     \
    generate_function_call(x86_update_gba);                                   \
    x86_emit_jmp_filler(writeback_location);                                  \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    x86_emit_test_reg_reg(reg_cycles, reg_cycles);                            \
    x86_emit_j_offset(x86_condition_code_ns, 10);                             \
    x86_emit_mov_reg_imm(reg_a0, new_pc);                                     \
    generate_function_call(x86_update_gba);                                   \
    x86_emit_jmp_filler(writeback_location);                                  \
  }                                                                           \

#define generate_branch_cycle_update(writeback_location, new_pc)              \
  generate_cycle_update();                                                    \
  generate_branch_no_cycle_update(writeback_location, new_pc)                 \

// a0 holds the destination

#define generate_indirect_branch_cycle_update(type)                           \
  generate_cycle_update();                                                    \
  x86_emit_call_offset(x86_relative_offset(translation_ptr,                   \
   x86_indirect_branch_##type, 4))                                            \

#define generate_indirect_branch_no_cycle_update(type)                        \
  x86_emit_call_offset(x86_relative_offset(translation_ptr,                   \
   x86_indirect_branch_##type, 4))                                            \

#define block_prologue_size 0
#define generate_block_prologue()
#define generate_block_extra_vars_arm()
#define generate_block_extra_vars_thumb()

#define generate_indirect_branch_arm()                                        \
  {                                                                           \
    if(condition == 0x0E)                                                     \
    {                                                                         \
      generate_indirect_branch_cycle_update(arm);                             \
    }                                                                         \
    else                                                                      \
    {                                                                         \
      generate_indirect_branch_no_cycle_update(arm);                          \
    }                                                                         \
  }                                                                           \

#define generate_indirect_branch_dual()                                       \
  {                                                                           \
    if(condition == 0x0E)                                                     \
    {                                                                         \
      generate_indirect_branch_cycle_update(dual);                            \
    }                                                                         \
    else                                                                      \
    {                                                                         \
      generate_indirect_branch_no_cycle_update(dual);                         \
    }                                                                         \
  }                                                                           \


#define get_shift_imm()                                                       \
  u32 shift = (opcode >> 7) & 0x1F                                            \

#define generate_shift_reg(ireg, name, flags_op)                              \
  generate_load_reg_pc(ireg, rm, 12);                                         \
  generate_load_reg(a1, ((opcode >> 8) & 0x0F));                              \
  generate_##name##_##flags_op##_reg(ireg);                                   \

#ifdef TRACE_INSTRUCTIONS
  void function_cc trace_instruction(u32 pc, u32 mode)
  {
    if (mode)
      printf("Executed arm %x\n", pc);
    else
      printf("Executed thumb %x\n", pc);
    #ifdef TRACE_REGISTERS
    print_regs();
    #endif
  }

  #define emit_trace_instruction(pc, mode)         \
    x86_emit_mov_reg_imm(reg_arg0, pc);            \
    x86_emit_mov_reg_imm(reg_arg1, mode);          \
    generate_function_call(trace_instruction);
  #define emit_trace_arm_instruction(pc)           \
    emit_trace_instruction(pc, 1)
  #define emit_trace_thumb_instruction(pc)         \
    emit_trace_instruction(pc, 0)
#else
  #define emit_trace_thumb_instruction(pc)
  #define emit_trace_arm_instruction(pc)
#endif

#define check_generate_n_flag   (flag_status & 0x08)
#define check_generate_z_flag   (flag_status & 0x04)
#define check_generate_c_flag   (flag_status & 0x02)
#define check_generate_v_flag   (flag_status & 0x01)

#define generate_asr_flags_reg(ireg)                                          \
{                                                                             \
  u8 *jmpinst1, *jmpinst2;                                                    \
  x86_emit_movzxb(reg_a2, reg_a1);                                            \
  x86_emit_jecxz_filler(jmpinst1);                                            \
  generate_shift_right_arithmetic_var(a0);                                    \
  generate_update_flag(c, REG_C_FLAG)                                         \
  generate_cmp_imm(a2, 32);                                                   \
  x86_emit_j_filler(x86_condition_code_l, jmpinst2);                          \
  generate_shift_right_arithmetic(a0, 16);                                    \
  generate_shift_right_arithmetic(a0, 16);                                    \
  generate_update_flag(c, REG_C_FLAG)                                         \
  generate_branch_patch_jecxz(jmpinst1, translation_ptr);                     \
  generate_branch_patch_conditional(jmpinst2, translation_ptr);               \
  generate_mov(ireg, a0);                                                     \
}

#define generate_lsl_flags_reg(ireg)                                          \
{                                                                             \
  u8 *jmpinst1, *jmpinst2;                                                    \
  x86_emit_movzxb(reg_a2, reg_a1);                                            \
  x86_emit_jecxz_filler(jmpinst1);                                            \
  generate_sub_imm(a2, 1);                                                    \
  generate_shift_left_var(a0);                                                \
  generate_or(a0, a0);                                                        \
  generate_update_flag(s, REG_C_FLAG)                                         \
  generate_shift_left(a0, 1);                                                 \
  generate_cmp_imm(a2, 32);                                                   \
  x86_emit_j_filler(x86_condition_code_l, jmpinst2);                          \
  generate_load_imm(a0, 0);                                                   \
  generate_store_reg_i32(0, REG_C_FLAG);                                      \
  generate_branch_patch_jecxz(jmpinst1, translation_ptr);                     \
  generate_branch_patch_conditional(jmpinst2, translation_ptr);               \
  generate_mov(ireg, a0);                                                     \
}

#define generate_lsr_flags_reg(ireg)                                          \
{                                                                             \
  u8 *jmpinst1, *jmpinst2;                                                    \
  x86_emit_movzxb(reg_a2, reg_a1);                                            \
  x86_emit_jecxz_filler(jmpinst1);                                            \
  generate_sub_imm(a2, 1);                                                    \
  generate_shift_right_var(a0);                                               \
  generate_test_imm(a0, 1);                                                   \
  generate_update_flag(nz, REG_C_FLAG)                                        \
  generate_shift_right(a0, 1);                                                \
  generate_cmp_imm(a2, 32);                                                   \
  x86_emit_j_filler(x86_condition_code_l, jmpinst2);                          \
  generate_load_imm(a0, 0);                                                   \
  generate_store_reg_i32(0, REG_C_FLAG);                                      \
  generate_branch_patch_jecxz(jmpinst1, translation_ptr);                     \
  generate_branch_patch_conditional(jmpinst2, translation_ptr);               \
  generate_mov(ireg, a0);                                                     \
}

#define generate_ror_flags_reg(ireg)                                          \
{                                                                             \
  u8 *jmpinst;                                                                \
  x86_emit_movzxb(reg_a2, reg_a1);                                            \
  x86_emit_jecxz_filler(jmpinst);                                             \
  generate_rotate_right_var(a0);                                              \
  x86_emit_bittest(reg_a0, 31);                                               \
  generate_update_flag(c, REG_C_FLAG);                                        \
  generate_branch_patch_jecxz(jmpinst, translation_ptr);                      \
  generate_mov(ireg, a0);                                                     \
}

// Shift right sets the CF of the shifted-out bit, use it with setc
#define generate_rrx_flags(ireg)                                              \
  generate_load_imm(a2, 0xffffffff);                                          \
  generate_add_memreg(a2, REG_C_FLAG);                                        \
  generate_rcr1(a0);                                                          \
  generate_update_flag(c, REG_C_FLAG)                                         \
  generate_mov(ireg, a0);

#define generate_rrx(ireg)                                                    \
  generate_load_reg(a2, REG_C_FLAG);                                          \
  generate_shift_right(ireg, 1);                                              \
  generate_shift_left(a2, 31);                                                \
  generate_or(ireg, a2);                                                      \

#define generate_shift_imm_lsl_no_flags(ireg)                                 \
  generate_load_reg_pc(ireg, rm, 8);                                          \
  if(shift != 0)                                                              \
  {                                                                           \
    generate_shift_left(ireg, shift);                                         \
  }                                                                           \

#define generate_shift_imm_lsr_no_flags(ireg)                                 \
  if(shift != 0)                                                              \
  {                                                                           \
    generate_load_reg_pc(ireg, rm, 8);                                        \
    generate_shift_right(ireg, shift);                                        \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_load_imm(ireg, 0);                                               \
  }                                                                           \

#define generate_shift_imm_asr_no_flags(ireg)                                 \
  generate_load_reg_pc(ireg, rm, 8);                                          \
  if(shift != 0)                                                              \
  {                                                                           \
    generate_shift_right_arithmetic(ireg, shift);                             \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_shift_right_arithmetic(ireg, 31);                                \
  }                                                                           \

#define generate_shift_imm_ror_no_flags(ireg)                                 \
  if(shift != 0)                                                              \
  {                                                                           \
    generate_load_reg_pc(ireg, rm, 8);                                        \
    generate_rotate_right(ireg, shift);                                       \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_load_reg_pc(ireg, rm, 8);                                        \
    generate_rrx(ireg);                                                       \
  }                                                                           \

#define generate_shift_imm_lsl_flags(ireg)                                    \
  generate_load_reg_pc(ireg, rm, 8);                                          \
  if(shift != 0)                                                              \
  {                                                                           \
    generate_shift_left(ireg, shift);                                         \
    generate_update_flag(c, REG_C_FLAG);                                      \
  }                                                                           \

#define generate_shift_imm_lsr_flags(ireg)                                    \
  generate_load_reg_pc(ireg, rm, 8);                                          \
  if(shift != 0)                                                              \
  {                                                                           \
    generate_shift_right(ireg, shift);                                        \
    generate_update_flag(c, REG_C_FLAG);                                      \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_shift_right(ireg, 31);                                           \
    generate_store_reg(ireg, REG_C_FLAG);                                     \
    generate_load_imm(ireg, 0);                                               \
  }                                                                           \

#define generate_shift_imm_asr_flags(ireg)                                    \
  generate_load_reg_pc(ireg, rm, 8);                                          \
  if(shift != 0)                                                              \
  {                                                                           \
    generate_shift_right_arithmetic(ireg, shift);                             \
    generate_update_flag(c, REG_C_FLAG);                                      \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_shift_right_arithmetic(ireg, 31);                                \
    generate_update_flag(nz, REG_C_FLAG);                                     \
  }                                                                           \

#define generate_shift_imm_ror_flags(ireg)                                    \
  generate_load_reg_pc(ireg, rm, 8);                                          \
  if(shift != 0)                                                              \
  {                                                                           \
    generate_rotate_right(ireg, shift);                                       \
    generate_update_flag(c, REG_C_FLAG)                                       \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_rrx_flags(ireg);                                                 \
  }                                                                           \

#define generate_shift_imm(ireg, name, flags_op)                              \
  get_shift_imm();                                                            \
  generate_shift_imm_##name##_##flags_op(ireg)                                \

#define generate_load_offset_sh()                                             \
  switch((opcode >> 5) & 0x03)                                                \
  {                                                                           \
    /* LSL imm */                                                             \
    case 0x0:                                                                 \
    {                                                                         \
      generate_shift_imm(a1, lsl, no_flags);                                  \
      break;                                                                  \
    }                                                                         \
                                                                              \
    /* LSR imm */                                                             \
    case 0x1:                                                                 \
    {                                                                         \
      generate_shift_imm(a1, lsr, no_flags);                                  \
      break;                                                                  \
    }                                                                         \
                                                                              \
    /* ASR imm */                                                             \
    case 0x2:                                                                 \
    {                                                                         \
      generate_shift_imm(a1, asr, no_flags);                                  \
      break;                                                                  \
    }                                                                         \
                                                                              \
    /* ROR imm */                                                             \
    case 0x3:                                                                 \
    {                                                                         \
      generate_shift_imm(a1, ror, no_flags);                                  \
      break;                                                                  \
    }                                                                         \
  }                                                                           \

#define extract_flags()                                                       \
  reg[REG_N_FLAG] = reg[REG_CPSR] >> 31;                                      \
  reg[REG_Z_FLAG] = (reg[REG_CPSR] >> 30) & 0x01;                             \
  reg[REG_C_FLAG] = (reg[REG_CPSR] >> 29) & 0x01;                             \
  reg[REG_V_FLAG] = (reg[REG_CPSR] >> 28) & 0x01;                             \

#define collapse_flags(ireg, tmpreg)                                          \
  generate_load_reg(ireg, REG_V_FLAG);                                        \
  generate_load_reg(tmpreg, REG_C_FLAG);                                      \
  generate_shift_left(tmpreg, 1);                                             \
  generate_or(ireg, tmpreg);                                                  \
  generate_load_reg(tmpreg, REG_Z_FLAG);                                      \
  generate_shift_left(tmpreg, 2);                                             \
  generate_or(ireg, tmpreg);                                                  \
  generate_load_reg(tmpreg, REG_N_FLAG);                                      \
  generate_shift_left(tmpreg, 3);                                             \
  generate_or(ireg, tmpreg);                                                  \
  generate_load_reg(tmpreg, REG_CPSR);                                        \
  generate_shift_left(ireg, 28);                                              \
  generate_and_imm(tmpreg, 0xFF);                                             \
  generate_or(ireg, tmpreg);                                                  \
  generate_store_reg(ireg, REG_CPSR);                                         \

// It should be okay to still generate result flags, spsr will overwrite them.
// This is pretty infrequent (returning from interrupt handlers, et al) so
// probably not worth optimizing for.

#define generate_load_reg_pc(ireg, reg_index, pc_offset)                      \
  if(reg_index == 15)                                                         \
  {                                                                           \
    generate_load_pc(ireg, pc + pc_offset);                                   \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    generate_load_reg(ireg, reg_index);                                       \
  }                                                                           \

#define generate_store_reg_pc_no_flags(ireg, reg_index)                       \
  generate_store_reg(ireg, reg_index);                                        \
  if(reg_index == 15)                                                         \
  {                                                                           \
    generate_mov(a0, ireg);                                                   \
    generate_indirect_branch_arm();                                           \
  }                                                                           \

u32 function_cc execute_spsr_restore(u32 address)
{
  if(reg[CPU_MODE] != MODE_USER && reg[CPU_MODE] != MODE_SYSTEM)
  {
    reg[REG_CPSR] = REG_SPSR(reg[CPU_MODE]);
    extract_flags();
    set_cpu_mode(cpu_modes[reg[REG_CPSR] & 0xF]);

    if((io_registers[REG_IE] & io_registers[REG_IF]) &&
     io_registers[REG_IME] && ((reg[REG_CPSR] & 0x80) == 0))
    {
      REG_MODE(MODE_IRQ)[6] = reg[REG_PC] + 4;
      REG_SPSR(MODE_IRQ) = reg[REG_CPSR];
      reg[REG_CPSR] = 0xD2;
      address = 0x00000018;
      set_cpu_mode(MODE_IRQ);
    }

    if(reg[REG_CPSR] & 0x20)
      address |= 0x01;
  }

  return address;
}

#define generate_store_reg_pc_flags(ireg, reg_index)                          \
  generate_store_reg(ireg, reg_index);                                        \
  if(reg_index == 15)                                                         \
  {                                                                           \
    generate_mov(arg0, ireg);                                                 \
    generate_function_call(execute_spsr_restore);                             \
    generate_indirect_branch_dual();                                          \
  }                                                                           \

// These generate a branch on the opposite condition on purpose.
// For ARM mode we aim to skip instructions (therefore opposite)
// In Thumb mode we skip the conditional branch in a similar way
#define generate_condition_eq(ireg)                                           \
  generate_and_mem(1, base, REG_Z_FLAG * 4);                                  \
  x86_emit_j_filler(x86_condition_code_z, backpatch_address)                  \

#define generate_condition_ne(ireg)                                           \
  generate_and_mem(1, base, REG_Z_FLAG * 4);                                  \
  x86_emit_j_filler(x86_condition_code_nz, backpatch_address)                 \

#define generate_condition_cs(ireg)                                           \
  generate_and_mem(1, base, REG_C_FLAG * 4);                                  \
  x86_emit_j_filler(x86_condition_code_z, backpatch_address)                  \

#define generate_condition_cc(ireg)                                           \
  generate_and_mem(1, base, REG_C_FLAG * 4);                                  \
  x86_emit_j_filler(x86_condition_code_nz, backpatch_address)                 \

#define generate_condition_mi(ireg)                                           \
  generate_and_mem(1, base, REG_N_FLAG * 4);                                  \
  x86_emit_j_filler(x86_condition_code_z, backpatch_address)                  \

#define generate_condition_pl(ireg)                                           \
  generate_and_mem(1, base, REG_N_FLAG * 4);                                  \
  x86_emit_j_filler(x86_condition_code_nz, backpatch_address)                 \

#define generate_condition_vs(ireg)                                           \
  generate_and_mem(1, base, REG_V_FLAG * 4);                                  \
  x86_emit_j_filler(x86_condition_code_z, backpatch_address)                  \

#define generate_condition_vc(ireg)                                           \
  generate_and_mem(1, base, REG_V_FLAG * 4);                                  \
  x86_emit_j_filler(x86_condition_code_nz, backpatch_address)                 \

#define generate_condition_hi(ireg)                                           \
  generate_load_reg(ireg, REG_C_FLAG);                                        \
  generate_xor_imm(ireg, 1);                                                  \
  generate_or_mem(ireg, REG_Z_FLAG);                                          \
  x86_emit_j_filler(x86_condition_code_nz, backpatch_address)                 \

#define generate_condition_ls(ireg)                                           \
  generate_load_reg(ireg, REG_C_FLAG);                                        \
  generate_xor_imm(ireg, 1);                                                  \
  generate_or_mem(ireg, REG_Z_FLAG);                                          \
  x86_emit_j_filler(x86_condition_code_z, backpatch_address)                  \

#define generate_condition_ge(ireg)                                           \
  generate_load_reg(ireg, REG_N_FLAG);                                        \
  generate_cmp_memreg(ireg, REG_V_FLAG);                                      \
  x86_emit_j_filler(x86_condition_code_nz, backpatch_address)                 \

#define generate_condition_lt(ireg)                                           \
  generate_load_reg(ireg, REG_N_FLAG);                                        \
  generate_cmp_memreg(ireg, REG_V_FLAG);                                      \
  x86_emit_j_filler(x86_condition_code_z, backpatch_address)                  \

#define generate_condition_gt(ireg)                                           \
  generate_load_reg(ireg, REG_N_FLAG);                                        \
  generate_xor_mem(ireg, REG_V_FLAG);                                         \
  generate_or_mem(ireg, REG_Z_FLAG);                                          \
  x86_emit_j_filler(x86_condition_code_nz, backpatch_address)                 \

#define generate_condition_le(ireg)                                           \
  generate_load_reg(ireg, REG_N_FLAG);                                        \
  generate_xor_mem(ireg, REG_V_FLAG);                                         \
  generate_or_mem(ireg, REG_Z_FLAG);                                          \
  x86_emit_j_filler(x86_condition_code_z, backpatch_address)                  \


#define generate_condition(ireg)                                              \
  switch(condition)                                                           \
  {                                                                           \
    case 0x0:                                                                 \
      generate_condition_eq(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0x1:                                                                 \
      generate_condition_ne(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0x2:                                                                 \
      generate_condition_cs(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0x3:                                                                 \
      generate_condition_cc(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0x4:                                                                 \
      generate_condition_mi(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0x5:                                                                 \
      generate_condition_pl(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0x6:                                                                 \
      generate_condition_vs(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0x7:                                                                 \
      generate_condition_vc(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0x8:                                                                 \
      generate_condition_hi(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0x9:                                                                 \
      generate_condition_ls(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0xA:                                                                 \
      generate_condition_ge(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0xB:                                                                 \
      generate_condition_lt(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0xC:                                                                 \
      generate_condition_gt(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0xD:                                                                 \
      generate_condition_le(ireg);                                            \
      break;                                                                  \
                                                                              \
    case 0xE:                                                                 \
      /* AL       */                                                          \
      break;                                                                  \
                                                                              \
    case 0xF:                                                                 \
      /* Reserved */                                                          \
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
}                                                                             \

#define arm_multiply_flags_yes()                                              \
  generate_and(a0, a0);                                                       \
  generate_update_flag(z, REG_Z_FLAG)                                         \
  generate_update_flag(s, REG_N_FLAG)

#define arm_multiply_flags_no(_dest)                                          \

#define arm_multiply_add_no()                                                 \

#define arm_multiply_add_yes()                                                \
  generate_load_reg(a1, rn);                                                  \
  generate_add(a0, a1)                                                        \

#define arm_multiply(add_op, flags)                                           \
{                                                                             \
  arm_decode_multiply();                                                      \
  generate_load_reg(a0, rm);                                                  \
  generate_load_reg(a1, rs);                                                  \
  generate_multiply(a1);                                                      \
  arm_multiply_add_##add_op();                                                \
  arm_multiply_flags_##flags();                                               \
  generate_store_reg(a0, rd);                                                 \
}                                                                             \

#define arm_multiply_long_flags_yes()                                         \
  generate_mov(t0, a1);                                                       \
  generate_and(t0, t0);                                                       \
  generate_update_flag(s, REG_N_FLAG)                                         \
  generate_or(t0, a0);                                                        \
  generate_update_flag(z, REG_Z_FLAG)                                         \

#define arm_multiply_long_flags_no(_dest)                                     \

#define arm_multiply_long_add_yes(name)                                       \
  generate_load_reg(a2, rdlo);                                                \
  generate_load_reg(t0, rdhi);                                                \
  generate_multiply_##name(a1, a2, t0)                                        \

#define arm_multiply_long_add_no(name)                                        \
  generate_multiply_##name(a1)                                                \

#define arm_multiply_long(name, add_op, flags)                                \
{                                                                             \
  arm_decode_multiply_long();                                                 \
  generate_load_reg(a0, rm);                                                  \
  generate_load_reg(a1, rs);                                                  \
  arm_multiply_long_add_##add_op(name);                                       \
  generate_store_reg(a0, rdlo);                                               \
  generate_store_reg(a1, rdhi);                                               \
  arm_multiply_long_flags_##flags();                                          \
}                                                                             \

#define execute_read_cpsr(oreg)                                               \
  collapse_flags(oreg, a2)

#define execute_read_spsr(oreg)                                               \
  collapse_flags(oreg, a2);                                                   \
  generate_load_reg(oreg, CPU_MODE);                                          \
  generate_and_imm(oreg, 0xF);                                                \
  generate_load_spsr(oreg, oreg);                                             \

#define arm_psr_read(op_type, psr_reg)                                        \
  execute_read_##psr_reg(rv);                                                 \
  generate_store_reg(rv, rd)                                                  \

// Does mode-change magic (including IRQ checks)
u32 execute_store_cpsr_body()
{
  set_cpu_mode(cpu_modes[reg[REG_CPSR] & 0xF]);
  if((io_registers[REG_IE] & io_registers[REG_IF]) &&
      io_registers[REG_IME] && ((reg[REG_CPSR] & 0x80) == 0))
  {
    REG_MODE(MODE_IRQ)[6] = reg[REG_PC] + 4;
    REG_SPSR(MODE_IRQ) = reg[REG_CPSR];
    reg[REG_CPSR] = (reg[REG_CPSR] & 0xFFFFFF00) | 0xD2;
    set_cpu_mode(MODE_IRQ);
    return 0x00000018;
  }

  return 0;
}


#define arm_psr_load_new_reg()                                                \
  generate_load_reg(a0, rm)                                                   \

#define arm_psr_load_new_imm()                                                \
  ror(imm, imm, imm_ror);                                                     \
  generate_load_imm(a0, imm)                                                  \

#define execute_store_cpsr()                                                  \
  generate_load_imm(a1, cpsr_masks[psr_pfield][0]);                           \
  generate_load_imm(a2, cpsr_masks[psr_pfield][1]);                           \
  generate_store_reg_i32(pc, REG_PC);                                         \
  generate_function_call(execute_store_cpsr)                                  \

/* REG_SPSR(reg[CPU_MODE]) = (new_spsr & store_mask) | (old_spsr & (~store_mask))*/
#define execute_store_spsr()                                                  \
  generate_load_reg(a2, CPU_MODE);                                            \
  generate_and_imm(a2, 0xF);                                                  \
  generate_load_spsr(a1, a2);                                                 \
  generate_and_imm(a0,  spsr_masks[psr_pfield]);                              \
  generate_and_imm(a1, ~spsr_masks[psr_pfield]);                              \
  generate_or(a0, a1);                                                        \
  generate_store_spsr(a0, a2);                                                \

#define arm_psr_store(op_type, psr_reg)                                       \
  arm_psr_load_new_##op_type();                                               \
  execute_store_##psr_reg();                                                  \

#define arm_psr(op_type, transfer_type, psr_reg)                              \
{                                                                             \
  arm_decode_psr_##op_type(opcode);                                           \
  arm_psr_##transfer_type(op_type, psr_reg);                                  \
}                                                                             \

#define arm_access_memory_load(mem_type)                                      \
  cycle_count += 2;                                                           \
  generate_load_pc(a1, pc);                                                   \
  generate_function_call(execute_load_##mem_type);                            \
  generate_store_reg_pc_no_flags(rv, rd)                                      \

#define arm_access_memory_store(mem_type)                                     \
  cycle_count++;                                                              \
  generate_load_reg_pc(a1, rd, 12);                                           \
  generate_store_reg_i32(pc + 4, REG_PC);                                     \
  generate_function_call(execute_store_##mem_type)                            \

#define no_op                                                                 \

#define arm_access_memory_writeback_yes(off_op)                               \
  reg[rn] = address off_op                                                    \

#define arm_access_memory_writeback_no(off_op)                                \

#define load_reg_op reg[rd]                                                   \

#define store_reg_op reg_op                                                   \

#define arm_access_memory_adjust_op_up      add
#define arm_access_memory_adjust_op_down    sub
#define arm_access_memory_reverse_op_up     sub
#define arm_access_memory_reverse_op_down   add

#define arm_access_memory_reg_pre(adjust_dir_op, reverse_dir_op)              \
  generate_load_reg_pc(a0, rn, 8);                                            \
  generate_##adjust_dir_op(a0, a1)                                            \

#define arm_access_memory_reg_pre_wb(adjust_dir_op, reverse_dir_op)           \
  arm_access_memory_reg_pre(adjust_dir_op, reverse_dir_op);                   \
  generate_store_reg(a0, rn)                                                  \

#define arm_access_memory_reg_post(adjust_dir_op, reverse_dir_op)             \
  generate_load_reg(a0, rn);                                                  \
  generate_##adjust_dir_op(a0, a1);                                           \
  generate_store_reg(a0, rn);                                                 \
  generate_##reverse_dir_op(a0, a1)                                           \

#define arm_access_memory_imm_pre(adjust_dir_op, reverse_dir_op)              \
  generate_load_reg_pc(a0, rn, 8);                                            \
  generate_##adjust_dir_op##_imm(a0, offset)                                  \

#define arm_access_memory_imm_pre_wb(adjust_dir_op, reverse_dir_op)           \
  arm_access_memory_imm_pre(adjust_dir_op, reverse_dir_op);                   \
  generate_store_reg(a0, rn)                                                  \

#define arm_access_memory_imm_post(adjust_dir_op, reverse_dir_op)             \
  generate_load_reg(a0, rn);                                                  \
  generate_##adjust_dir_op##_imm(a0, offset);                                 \
  generate_store_reg(a0, rn);                                                 \
  generate_##reverse_dir_op##_imm(a0, offset)                                 \


#define arm_data_trans_reg(adjust_op, adjust_dir_op, reverse_dir_op)          \
  arm_decode_data_trans_reg();                                                \
  generate_load_offset_sh();                                                  \
  arm_access_memory_reg_##adjust_op(adjust_dir_op, reverse_dir_op)            \

#define arm_data_trans_imm(adjust_op, adjust_dir_op, reverse_dir_op)          \
  arm_decode_data_trans_imm();                                                \
  arm_access_memory_imm_##adjust_op(adjust_dir_op, reverse_dir_op)            \

#define arm_data_trans_half_reg(adjust_op, adjust_dir_op, reverse_dir_op)     \
  arm_decode_half_trans_r();                                                  \
  generate_load_reg(a1, rm);                                                  \
  arm_access_memory_reg_##adjust_op(adjust_dir_op, reverse_dir_op)            \

#define arm_data_trans_half_imm(adjust_op, adjust_dir_op, reverse_dir_op)     \
  arm_decode_half_trans_of();                                                 \
  arm_access_memory_imm_##adjust_op(adjust_dir_op, reverse_dir_op)            \

#define arm_access_memory(access_type, direction, adjust_op, mem_type,        \
 offset_type)                                                                 \
{                                                                             \
  arm_data_trans_##offset_type(adjust_op,                                     \
   arm_access_memory_adjust_op_##direction,                                   \
   arm_access_memory_reverse_op_##direction);                                 \
                                                                              \
  arm_access_memory_##access_type(mem_type);                                  \
}                                                                             \

#define word_bit_count(word)                                                  \
  (bit_count[word >> 8] + bit_count[word & 0xFF])                             \


#define arm_block_memory_load()                                               \
  generate_load_pc(a1, pc);                                                   \
  generate_function_call(execute_load_u32);                                   \
  generate_store_reg(rv, i)                                                   \

#define arm_block_memory_store()                                              \
  generate_load_reg_pc(a1, i, 8);                                             \
  generate_function_call(execute_store_aligned_u32)                           \

#define arm_block_memory_final_load(writeback_type)                           \
  arm_block_memory_load()                                                     \

#define arm_block_memory_final_store(writeback_type)                          \
  generate_load_reg_pc(a1, i, 12);                                            \
  arm_block_memory_writeback_post_store(writeback_type);                      \
  generate_store_reg_i32(pc + 4, REG_PC);                                     \
  generate_function_call(execute_store_u32)                                   \

#define arm_block_memory_adjust_pc_store()                                    \

#define arm_block_memory_adjust_pc_load()                                     \
  if(reg_list & 0x8000)                                                       \
  {                                                                           \
    generate_indirect_branch_arm();                                           \
  }                                                                           \

#define arm_block_memory_offset_down_a()                                      \
  generate_add_imm(a0, -((word_bit_count(reg_list) * 4) - 4))                 \

#define arm_block_memory_offset_down_b()                                      \
  generate_add_imm(a0, -(word_bit_count(reg_list) * 4))                       \

#define arm_block_memory_offset_no()                                          \

#define arm_block_memory_offset_up()                                          \
  generate_add_imm(a0, 4)                                                     \

#define arm_block_memory_writeback_down()                                     \
  generate_load_reg(a2, rn)                                                   \
  generate_add_imm(a2, -(word_bit_count(reg_list) * 4));                      \
  generate_store_reg(a2, rn)                                                  \

#define arm_block_memory_writeback_up()                                       \
  generate_load_reg(a2, rn);                                                  \
  generate_add_imm(a2, (word_bit_count(reg_list) * 4));                       \
  generate_store_reg(a2, rn)                                                  \

#define arm_block_memory_writeback_no()

// Only emit writeback if the register is not in the list

#define arm_block_memory_writeback_pre_load(writeback_type)                   \
  if(!((reg_list >> rn) & 0x01))                                              \
  {                                                                           \
    arm_block_memory_writeback_##writeback_type();                            \
  }                                                                           \

#define arm_block_memory_writeback_pre_store(writeback_type)                  \

#define arm_block_memory_writeback_post_store(writeback_type)                 \
  arm_block_memory_writeback_##writeback_type()                               \

#define arm_block_memory(access_type, offset_type, writeback_type, s_bit)     \
{                                                                             \
  arm_decode_block_trans();                                                   \
  u32 offset = 0;                                                             \
  u32 i;                                                                      \
                                                                              \
  generate_load_reg(a0, rn);                                                  \
  arm_block_memory_offset_##offset_type();                                    \
  generate_and_imm(a0, ~0x03);                                                \
  generate_store_reg(a0, REG_SAVE3);                                          \
  arm_block_memory_writeback_pre_##access_type(writeback_type);               \
                                                                              \
  for(i = 0; i < 16; i++)                                                     \
  {                                                                           \
    if((reg_list >> i) & 0x01)                                                \
    {                                                                         \
      cycle_count++;                                                          \
      generate_load_reg(a0, REG_SAVE3);                                       \
      generate_add_imm(a0, offset)                                            \
      if(reg_list & ~((2 << i) - 1))                                          \
      {                                                                       \
        arm_block_memory_##access_type();                                     \
        offset += 4;                                                          \
      }                                                                       \
      else                                                                    \
      {                                                                       \
        arm_block_memory_final_##access_type(writeback_type);                 \
      }                                                                       \
    }                                                                         \
  }                                                                           \
                                                                              \
  arm_block_memory_adjust_pc_##access_type();                                 \
}                                                                             \

#define arm_swap(type)                                                        \
{                                                                             \
  arm_decode_swap();                                                          \
  cycle_count += 3;                                                           \
  generate_load_reg(a0, rn);                                                  \
  generate_load_pc(a1, pc);                                                   \
  generate_function_call(execute_load_##type);                                \
  generate_mov(a2, rv);                                                       \
  generate_load_reg(a0, rn);                                                  \
  generate_load_reg(a1, rm);                                                  \
  generate_store_reg(a2, rd);                                                 \
  generate_function_call(execute_store_##type);                               \
}                                                                             \

#define thumb_rn_op_reg(_rn)                                                  \
  generate_load_reg(a0, _rn)                                                  \

#define thumb_rn_op_imm(_imm)                                                 \
  generate_load_imm(a0, _imm)                                                 \

// Types: add_sub, add_sub_imm, alu_op, imm
// Affects N/Z/C/V flags

#define generate_store_reg_pc_thumb(ireg, rd)                                 \
  generate_store_reg(ireg, rd);                                               \
  if(rd == 15)                                                                \
  {                                                                           \
    generate_indirect_branch_cycle_update(thumb);                             \
  }                                                                           \


// Decode types: shift, alu_op
// Operation types: lsl, lsr, asr, ror
// Affects N/Z/C flags

#define thumb_lsl_imm_op()                                                    \
  if (imm) {                                                                  \
    generate_shift_left(a0, imm);                                             \
    generate_update_flag(c, REG_C_FLAG)                                       \
  } else {                                                                    \
    generate_or(a0, a0);                                                      \
  }                                                                           \
  update_logical_flags()                                                      \

#define thumb_lsr_imm_op()                                                    \
  if (imm) {                                                                  \
    generate_shift_right(a0, imm);                                            \
    generate_update_flag(c, REG_C_FLAG)                                       \
  } else {                                                                    \
    generate_shift_right(a0, 31);                                             \
    generate_update_flag(nz, REG_C_FLAG)                                      \
    generate_xor(a0, a0);                                                     \
  }                                                                           \
  update_logical_flags()                                                      \

#define thumb_asr_imm_op()                                                    \
  if (imm) {                                                                  \
    generate_shift_right_arithmetic(a0, imm);                                 \
    generate_update_flag(c, REG_C_FLAG)                                       \
  } else {                                                                    \
    generate_shift_right_arithmetic(a0, 31);                                  \
    generate_update_flag(s, REG_C_FLAG)                                       \
  }                                                                           \
  update_logical_flags()                                                      \


#define generate_shift_load_operands_reg()                                    \
  generate_load_reg(a0, rd);                                                  \
  generate_load_reg(a1, rs)                                                   \

#define generate_shift_load_operands_imm()                                    \
  generate_load_reg(a0, rs);                                                  \
  generate_load_imm(a1, imm)                                                  \

#define thumb_shift_operation_imm(op_type)                                    \
  thumb_##op_type##_imm_op()

#define thumb_shift_operation_reg(op_type)                                    \
  generate_##op_type##_flags_reg(a0);                                         \
  generate_or(a0, a0);                                                        \
  update_logical_flags()                                                      \

#define thumb_shift(decode_type, op_type, value_type)                         \
{                                                                             \
  thumb_decode_##decode_type();                                               \
  generate_shift_load_operands_##value_type();                                \
  thumb_shift_operation_##value_type(op_type);                                \
  generate_store_reg(rv, rd);                                                 \
}                                                                             \

// Operation types: imm, mem_reg, mem_imm

#define thumb_load_pc_pool_const(reg_rd, value)                               \
  generate_store_reg_i32(value, reg_rd)                                       \

#define thumb_access_memory_load(mem_type, reg_rd)                            \
  cycle_count += 2;                                                           \
  generate_load_pc(a1, pc);                                                   \
  generate_function_call(execute_load_##mem_type);                            \
  generate_store_reg(rv, reg_rd)                                              \

#define thumb_access_memory_store(mem_type, reg_rd)                           \
  cycle_count++;                                                              \
  generate_load_reg(a1, reg_rd);                                              \
  generate_store_reg_i32(pc + 2, REG_PC);                                     \
  generate_function_call(execute_store_##mem_type)                            \

#define thumb_access_memory_generate_address_pc_relative(offset, _rb, _ro)    \
  generate_load_pc(a0, (offset))                                              \

#define thumb_access_memory_generate_address_reg_imm_sp(offset, _rb, _ro)     \
  generate_load_reg(a0, _rb);                                                 \
  generate_add_imm(a0, (offset * 4))                                          \

#define thumb_access_memory_generate_address_reg_imm(offset, _rb, _ro)        \
  generate_load_reg(a0, _rb);                                                 \
  generate_add_imm(a0, (offset))                                              \

#define thumb_access_memory_generate_address_reg_reg(offset, _rb, _ro)        \
  generate_load_reg(a0, _rb);                                                 \
  generate_load_reg(a1, _ro);                                                 \
  generate_add(a0, a1)                                                        \

#define thumb_access_memory(access_type, op_type, _rd, _rb, _ro,              \
 address_type, offset, mem_type)                                              \
{                                                                             \
  thumb_decode_##op_type();                                                   \
  thumb_access_memory_generate_address_##address_type(offset, _rb, _ro);      \
  thumb_access_memory_##access_type(mem_type, _rd);                           \
}                                                                             \

#define thumb_block_address_preadjust_up()                                    \
  generate_add_imm(a0, (bit_count[reg_list] * 4))                             \

#define thumb_block_address_preadjust_down()                                  \
  generate_sub_imm(a0, (bit_count[reg_list] * 4))                             \

#define thumb_block_address_preadjust_push_lr()                               \
  generate_sub_imm(a0, ((bit_count[reg_list] + 1) * 4))                       \

#define thumb_block_address_preadjust_no()                                    \

#define thumb_block_address_postadjust_no(base_reg)                           \
  generate_store_reg(a0, base_reg)                                            \

#define thumb_block_address_postadjust_up(base_reg)                           \
  generate_add_imm(a0, (bit_count[reg_list] * 4));                            \
  generate_store_reg(a0, base_reg)                                            \

#define thumb_block_address_postadjust_down(base_reg)                         \
  generate_sub_imm(a0, (bit_count[reg_list] * 4));                            \
  generate_store_reg(a0, base_reg)                                            \

#define thumb_block_address_postadjust_pop_pc(base_reg)                       \
  generate_add_imm(a0, ((bit_count[reg_list] + 1) * 4));                      \
  generate_store_reg(a0, base_reg)                                            \

#define thumb_block_address_postadjust_push_lr(base_reg)                      \
  generate_store_reg(a0, base_reg)                                            \

#define thumb_block_memory_extra_no()                                         \

#define thumb_block_memory_extra_up()                                         \

#define thumb_block_memory_extra_down()                                       \

#define thumb_block_memory_extra_pop_pc()                                     \
  generate_load_reg(a0, REG_SAVE3);                                           \
  generate_add_imm(a0, (bit_count[reg_list] * 4));                            \
  generate_load_pc(a1, pc);                                                   \
  generate_function_call(execute_load_u32);                                   \
  generate_store_reg(rv, REG_PC);                                             \
  generate_indirect_branch_cycle_update(thumb)                                \

#define thumb_block_memory_extra_push_lr(base_reg)                            \
  generate_load_reg(a0, REG_SAVE3);                                           \
  generate_add_imm(a0, (bit_count[reg_list] * 4));                            \
  generate_load_reg(a1, REG_LR);                                              \
  generate_function_call(execute_store_aligned_u32)                           \

#define thumb_block_memory_load()                                             \
  generate_load_pc(a1, pc);                                                   \
  generate_function_call(execute_load_u32);                                   \
  generate_store_reg(rv, i)                                                   \

#define thumb_block_memory_store()                                            \
  generate_load_reg(a1, i);                                                   \
  generate_function_call(execute_store_aligned_u32)                           \

#define thumb_block_memory_final_load()                                       \
  thumb_block_memory_load()                                                   \

#define thumb_block_memory_final_store()                                      \
  generate_load_reg(a1, i);                                                   \
  generate_store_reg_i32(pc + 2, REG_PC);                                     \
  generate_function_call(execute_store_u32)                                   \

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

#define thumb_block_memory(access_type, pre_op, post_op, base_reg)            \
{                                                                             \
  thumb_decode_rlist();                                                       \
  u32 i;                                                                      \
  u32 offset = 0;                                                             \
                                                                              \
  generate_load_reg(a0, base_reg);                                            \
  generate_and_imm(a0, ~0x03);                                                \
  thumb_block_address_preadjust_##pre_op();                                   \
  generate_store_reg(a0, REG_SAVE3);                                          \
  thumb_block_address_postadjust_##post_op(base_reg);                         \
                                                                              \
  for(i = 0; i < 8; i++)                                                      \
  {                                                                           \
    if((reg_list >> i) & 0x01)                                                \
    {                                                                         \
      cycle_count++;                                                          \
      generate_load_reg(a0, REG_SAVE3);                                       \
      generate_add_imm(a0, offset)                                            \
      if(reg_list & ~((2 << i) - 1))                                          \
      {                                                                       \
        thumb_block_memory_##access_type();                                   \
        offset += 4;                                                          \
      }                                                                       \
      else                                                                    \
      {                                                                       \
        thumb_block_memory_final_##post_op(access_type);                      \
      }                                                                       \
    }                                                                         \
  }                                                                           \
                                                                              \
  thumb_block_memory_extra_##post_op();                                       \
}                                                                             \


#define thumb_conditional_branch(condition)                                   \
{                                                                             \
  generate_cycle_update();                                                    \
  generate_condition_##condition(a0);                                         \
  generate_branch_no_cycle_update(                                            \
   block_exits[block_exit_position].branch_source,                            \
   block_exits[block_exit_position].branch_target);                           \
  generate_branch_patch_conditional(backpatch_address, translation_ptr);      \
  block_exit_position++;                                                      \
}                                                                             \

// Execute functions

#define update_logical_flags()                                                \
  if (check_generate_z_flag) {                                                \
    generate_update_flag(z, REG_Z_FLAG)                                       \
  }                                                                           \
  if (check_generate_n_flag) {                                                \
    generate_update_flag(s, REG_N_FLAG)                                       \
  }                                                                           \

#define update_add_flags()                                                    \
  update_logical_flags()                                                      \
  if (check_generate_c_flag) {                                                \
    generate_update_flag(c, REG_C_FLAG)                                       \
  }                                                                           \
  if (check_generate_v_flag) {                                                \
    generate_update_flag(o, REG_V_FLAG)                                       \
  }                                                                           \

#define update_sub_flags()                                                    \
  update_logical_flags()                                                      \
  if (check_generate_c_flag) {                                                \
    generate_update_flag(nc, REG_C_FLAG)                                      \
  }                                                                           \
  if (check_generate_v_flag) {                                                \
    generate_update_flag(o, REG_V_FLAG)                                       \
  }                                                                           \

#define arm_data_proc_add(rd, storefnc)                                       \
  generate_add(a0, a1);                                                       \
  storefnc(a0, rd);

#define arm_data_proc_adds(rd, storefnc)                                      \
  generate_add(a0, a1);                                                       \
  update_add_flags();                                                         \
  storefnc(a0, rd);

// Argument ordering is inverted between arm and x86
#define arm_data_proc_sub(rd, storefnc)                                       \
  generate_sub(a1, a0);                                                       \
  storefnc(a1, rd);

#define arm_data_proc_rsb(rd, storefnc)                                       \
  generate_sub(a0, a1);                                                       \
  storefnc(a0, rd);

// Borrow flag in ARM is opposite to carry flag in x86
#define arm_data_proc_subs(rd, storefnc)                                      \
  generate_sub(a1, a0);                                                       \
  update_sub_flags();                                                         \
  storefnc(a1, rd);

#define arm_data_proc_rsbs(rd, storefnc)                                      \
  generate_sub(a0, a1);                                                       \
  update_sub_flags();                                                         \
  storefnc(a0, rd);

#define arm_data_proc_mul(rd, storefnc)                                       \
  generate_multiply(a1);                                                      \
  storefnc(a0, rd);

#define arm_data_proc_muls(rd, storefnc)                                      \
  generate_multiply(a1);                                                      \
  generate_and(a0, a0);                                                       \
  update_logical_flags();                                                     \
  storefnc(a0, rd);

#define load_c_flag(tmpreg)                                                   \
  /* Loads the flag to the right value by adding it to ~0 causing carry */    \
  generate_load_imm(tmpreg, 0xffffffff);                                      \
  generate_add_memreg(tmpreg, REG_C_FLAG);                                    \

#define load_inv_c_flag(tmpreg)                                               \
  /* Loads the inverse C flag (for subtraction, since ARM's inverted) */      \
  generate_load_reg(tmpreg, REG_C_FLAG);                                      \
  generate_sub_imm(tmpreg, 1);                                                \


static void function_cc execute_swi(u32 pc)
{
  // Open bus value after SWI
  reg[REG_BUS_VALUE] = 0xe3a02004;
  REG_MODE(MODE_SUPERVISOR)[6] = pc;
  REG_SPSR(MODE_SUPERVISOR) = reg[REG_CPSR];
  // Move to ARM mode, supervisor mode, disable IRQs
  reg[REG_CPSR] = (reg[REG_CPSR] & ~0x3F) | 0x13 | 0x80;
  set_cpu_mode(MODE_SUPERVISOR);
}

#define arm_conditional_block_header()                                        \
  generate_cycle_update();                                                    \
  generate_condition(a0);                                                     \

#define arm_b()                                                               \
  generate_branch()                                                           \

#define arm_bl()                                                              \
  generate_load_pc(a0, (pc + 4));                                             \
  generate_store_reg(a0, REG_LR);                                             \
  generate_branch()                                                           \

#define arm_bx()                                                              \
  arm_decode_branchx(opcode);                                                 \
  generate_load_reg(a0, rn);                                                  \
  generate_indirect_branch_dual();                                            \

#define arm_swi()                                                             \
  collapse_flags(a0, a1);                                                     \
  generate_load_pc(arg0, (pc + 4));                                           \
  generate_function_call(execute_swi);                                        \
  generate_branch()                                                           \

#define thumb_b()                                                             \
  generate_branch_cycle_update(                                               \
   block_exits[block_exit_position].branch_source,                            \
   block_exits[block_exit_position].branch_target);                           \
  block_exit_position++                                                       \

#define thumb_bl()                                                            \
  generate_load_pc(a0, ((pc + 2) | 0x01));                                    \
  generate_store_reg(a0, REG_LR);                                             \
  generate_branch_cycle_update(                                               \
   block_exits[block_exit_position].branch_source,                            \
   block_exits[block_exit_position].branch_target);                           \
  block_exit_position++                                                       \

#define thumb_blh()                                                           \
{                                                                             \
  thumb_decode_branch();                                                      \
  generate_load_pc(a0, ((pc + 2) | 0x01));                                    \
  generate_load_reg(a1, REG_LR);                                              \
  generate_store_reg(a0, REG_LR);                                             \
  generate_mov(a0, a1);                                                       \
  generate_add_imm(a0, (offset * 2));                                         \
  generate_indirect_branch_cycle_update(thumb);                               \
}                                                                             \

#define thumb_bx()                                                            \
{                                                                             \
  thumb_decode_hireg_op();                                                    \
  generate_load_reg_pc(a0, rs, 4);                                            \
  generate_indirect_branch_cycle_update(dual);                                \
}                                                                             \

#define thumb_process_cheats()                                                \
  generate_function_call(process_cheats);

#define arm_process_cheats()                                                  \
  generate_function_call(process_cheats);

#define thumb_swi()                                                           \
  collapse_flags(a0, a1);                                                     \
  generate_load_pc(arg0, (pc + 2));                                           \
  generate_function_call(execute_swi);                                        \
  generate_branch_cycle_update(                                               \
   block_exits[block_exit_position].branch_source,                            \
   block_exits[block_exit_position].branch_target);                           \
  block_exit_position++                                                       \


#define emit_load_reg_pc(ireg, regnum, pc_offset)                             \
  if(regnum == REG_PC) {                                                      \
    generate_load_pc(ireg, it.pc + pc_offset);                                \
  } else {                                                                    \
    generate_load_reg(ireg, regnum);                                          \
  }                                                                           \

/* Just loads the LSB byte of the desired register */
#define emit_load_reg_pc_lsb(ireg, regnum, pc_offset)                         \
  if(regnum == REG_PC) {                                                      \
    x86_emit_mov_reg_imm(ireg, 0xFF & (it.pc + (pc_offset)));                 \
  } else {                                                                    \
    x86_emit_mem_movzxb(ireg, reg_base, (regnum) * 4);                        \
  }                                                                           \


#define update_cv_add_flags()                                                 \
  if (it.gen_flag_c()) {                                                      \
    generate_update_flag(c, REG_C_FLAG);                                      \
  }                                                                           \
  if (it.gen_flag_v()) {                                                      \
    generate_update_flag(o, REG_V_FLAG)                                       \
  }                                                                           \

#define update_cv_sub_flags()                                                 \
  if (it.gen_flag_c()) {                                                      \
    generate_update_flag(nc, REG_C_FLAG);  /* CF is inverted in ARM/x86 */    \
  }                                                                           \
  if (it.gen_flag_v()) {                                                      \
    generate_update_flag(o, REG_V_FLAG)                                       \
  }                                                                           \

class CodeEmitter : public CodeEmitterBase {
public:
  CodeEmitter(u8 *emit_ptr, u8 *emit_end, u32 pc)
   : CodeEmitterBase(emit_ptr, emit_end) {}

  template <FlagOperation flgmode>
  inline void upd_nz_flags(const InstFlagInfo & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    if (flgmode == SetFlags) {
      if (it.gen_flag_z()) {
        generate_update_flag(z, REG_Z_FLAG);
      }
      if (it.gen_flag_n()) {
        generate_update_flag(s, REG_N_FLAG);
      }
    }
  }

  template <FlagOperation flgmode>
  inline void upd_nz_flags_imm(const ARMInst & it, u32 imm) {
    if (flgmode == SetFlags) {
      u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
      if (it.gen_flag_z()) {
        generate_store_reg_i32((imm ? 0 : 1), REG_Z_FLAG);
      }
      if (it.gen_flag_n()) {
        generate_store_reg_i32((imm >> 31), REG_N_FLAG);
      }
    }
  }

  template <FlagOperation flgmode>
  inline void upd_nzcv_add_flags(const InstFlagInfo & it) {
    upd_nz_flags<flgmode>(it);
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    if (flgmode == SetFlags) {
      if (it.gen_flag_c()) {
        generate_update_flag(c, REG_C_FLAG);
      }
      if (it.gen_flag_v()) {
        generate_update_flag(o, REG_V_FLAG);
      }
    }
  }

  template <FlagOperation flgmode>
  inline void upd_nzcv_sub_flags(const InstFlagInfo & it) {
    upd_nz_flags<flgmode>(it);
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    if (flgmode == SetFlags) {
      if (it.gen_flag_c()) {
        generate_update_flag(nc, REG_C_FLAG);
      }
      if (it.gen_flag_v()) {
        generate_update_flag(o, REG_V_FLAG);
      }
    }
  }

  // ======== Thumb instructions ====================================
  template <AluOperation aluop>
  inline void thumb_aluop2(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    generate_load_reg(a0, it.rd());    // Load operands
    generate_load_reg(a1, it.rs());

    switch (aluop) {
    case OpOrr:
      generate_or(a0, a1);
      break;
    case OpAnd:
      generate_and(a0, a1);
      break;
    case OpXor:
      generate_xor(a0, a1);
      break;
    case OpBic:
      generate_not(a1);
      generate_and(a0, a1);
      break;
    case OpMul:
      generate_multiply(a1);     // Multiplied by a0 (EAX) implicitely
      generate_and(a0, a0);      // Force flag generation (ZF/SF)
      break;
    case OpAdd:
      generate_add(a0, a1);
      update_cv_add_flags();
      break;
    case OpSub:
      generate_sub(a0, a1);
      update_cv_sub_flags();
      break;
    case OpAdc:
      load_c_flag(a2);         // Load C flag into CFLAGS
      generate_adc(a0, a1);
      update_cv_add_flags();
      break;
    case OpSbc:
      load_inv_c_flag(a2);         // Load !C flag into CFLAGS
      generate_sbb(a0, a1);
      update_cv_sub_flags();
      break;
    };

    upd_nz_flags<SetFlags>(it);
    generate_store_reg(a0, it.rd());
  }

  template <AluOperation aluop>
  inline void thumb_aluop1(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    generate_load_reg(a0, it.rs());   // Load operand

    switch (aluop) {
    case OpNeg:
      generate_xor(a1, a1);
      generate_sub(a1, a0);
      update_cv_sub_flags();
      generate_store_reg(a1, it.rd());
      break;
    case OpMvn:
      generate_xor_imm(a0, ~0U);
      generate_store_reg(a0, it.rd());
      break;
    };

    upd_nz_flags<SetFlags>(it);
  }

  template <AluOperation testop>
  inline void thumb_testop(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    generate_load_reg(a0, it.rd());    // Load operands
    generate_load_reg(a1, it.rs());

    switch (testop) {
    case OpTst:
      generate_and(a0, a1);
      upd_nz_flags<SetFlags>(it);
      break;
    case OpCmp:
      generate_sub(a0, a1);
      upd_nzcv_sub_flags<SetFlags>(it);
      break;
    case OpCmn:
      generate_add(a0, a1);
      upd_nzcv_add_flags<SetFlags>(it);
      break;
    };
  }

  template <AluOperation aluop>
  inline void thumb_aluimm2(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    switch (aluop) {
    case OpMov:
      generate_store_reg_i32(it.imm8(), it.rd8());
      generate_store_reg_i32((it.imm8() ? 0 : 1), REG_Z_FLAG);
      generate_store_reg_i32(0, REG_N_FLAG);
      break;
    case OpAdd:
      generate_load_reg(a0, it.rd8());
      x86_emit_add_reg_imm(reg_a0, it.imm8());
      upd_nzcv_add_flags<SetFlags>(it);
      generate_store_reg(a0, it.rd8());
      break;
    case OpSub:
      generate_load_reg(a0, it.rd8());
      x86_emit_sub_reg_imm(reg_a0, it.imm8());
      upd_nzcv_sub_flags<SetFlags>(it);
      generate_store_reg(a0, it.rd8());
      break;
    case OpCmp:
      generate_load_reg(a1, it.rd8());
      generate_load_imm(a0, it.imm8());
      generate_sub(a1, a0);
      upd_nzcv_sub_flags<SetFlags>(it);
      break;
    };
  }

  template <AluOperation aluop>
  inline void thumb_aluimm3(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    generate_load_reg(a0, it.rs());

    switch (aluop) {
    case OpAdd:
      x86_emit_add_reg_imm(reg_a0, it.imm3());
      upd_nzcv_add_flags<SetFlags>(it);
      break;
    case OpSub:
      x86_emit_sub_reg_imm(reg_a0, it.imm3());
      upd_nzcv_sub_flags<SetFlags>(it);
      break;
    };

    generate_store_reg(a0, it.rd());
  }

  template <AluOperation aluop>
  inline void thumb_aluop3(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    generate_load_reg(a0, it.rs());
    generate_load_reg(a1, it.rn());

    switch (aluop) {
    case OpAdd:
      generate_add(a0, a1);
      upd_nzcv_add_flags<SetFlags>(it);
      break;
    case OpSub:
      generate_sub(a0, a1);
      upd_nzcv_sub_flags<SetFlags>(it);
      break;
    };

    generate_store_reg(a0, it.rd());
  }

  template <AluOperation aluop>
  inline void thumb_aluhi(const ThumbInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    emit_load_reg_pc(a0, it.rs_hi(), 4);

    switch (aluop) {
    case OpAdd:
      emit_load_reg_pc(a1, it.rd_hi(), 4);
      generate_add(a0, a1);
      generate_store_reg_pc_thumb(a0, it.rd_hi());
      break;
    case OpCmp:
      emit_load_reg_pc(a1, it.rd_hi(), 4);
      generate_sub(a1, a0);
      upd_nzcv_sub_flags<SetFlags>(it);
      break;
    case OpMov:
      generate_store_reg_pc_thumb(a0, it.rd_hi());
      break;
    };
  }

  template <u32 ref_reg>
  inline void thumb_regoff(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    if (ref_reg == REG_PC) {
      generate_store_reg_i32((it.pc & ~2) + 4 + 4 * it.imm8(), it.rd8());
    } else {
      generate_load_reg(a0, ref_reg);
      generate_add_imm(a0, 4 * it.imm8());
      generate_store_reg(a0, it.rd8());
    }
  }

  inline void thumb_spadj(s8 offset) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    generate_load_reg(a0, REG_SP);
    generate_add_imm(a0, offset * 4);
    generate_store_reg(a0, REG_SP);
  }

  // ======== ARM instructions ======================================
  template <AluOperation aluop, FlagOperation flg>
  inline void arm_aluimm3(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    emit_load_reg_pc(a0, it.rn(), 8);

    // Immediate is a 8 bit rotated immediate
    u32 sa = it.rot4() * 2;
    u32 imm = rotr32(it.imm8(), sa);

    // Set/Clear carry flag if appropriate (rotation result)
    if (aluop == OpAnd || aluop == OpOrr || aluop == OpXor || aluop == OpBic) {
      if (flg == SetFlags && it.rot4() != 0 && it.gen_flag_c()) {
        generate_store_reg_i32((imm >> 31), REG_C_FLAG);
      }
    }

    switch (aluop) {
    case OpAnd:
      x86_emit_and_reg_imm(reg_a0, imm);
      upd_nz_flags<flg>(it);
      break;
    case OpOrr:
      x86_emit_or_reg_imm(reg_a0, imm);
      upd_nz_flags<flg>(it);
      break;
    case OpXor:
      x86_emit_xor_reg_imm(reg_a0, imm);
      upd_nz_flags<flg>(it);
      break;
    case OpBic:
      x86_emit_and_reg_imm(reg_a0, ~imm);
      upd_nz_flags<flg>(it);
      break;
    case OpAdd:
      x86_emit_add_reg_imm(reg_a0, imm);
      upd_nzcv_add_flags<flg>(it);
      break;
    case OpAdc:
      load_c_flag(a2);         // Load C flag into CFLAGS
      x86_emit_adc_reg_imm(reg_a0, imm);
      upd_nzcv_add_flags<flg>(it);
      break;
    case OpSub:
      x86_emit_sub_reg_imm(reg_a0, imm);
      upd_nzcv_sub_flags<flg>(it);
      break;
    case OpRsb:
      generate_load_imm(a1, imm);
      x86_emit_sub_reg_reg(reg_a1, reg_a0);
      upd_nzcv_sub_flags<flg>(it);
      break;
    case OpSbc:
      load_inv_c_flag(a2);     // Load C flag into CFLAGS
      x86_emit_sbb_reg_imm(reg_a0, imm);
      upd_nzcv_sub_flags<flg>(it);
      break;
    case OpRsc:
      load_inv_c_flag(a2);     // Load C flag into CFLAGS
      generate_load_imm(a1, imm);
      x86_emit_sbb_reg_reg(reg_a1, reg_a0);
      upd_nzcv_sub_flags<flg>(it);
      break;
    };

    const u8 condition = it.cond();        // TODO remove this
    if (flg == SetFlags) {
      if (aluop == OpRsb || aluop == OpRsc) {
        generate_store_reg_pc_flags(a1, it.rd());
      } else {
        generate_store_reg_pc_flags(a0, it.rd());
      }
    } else {
      if (aluop == OpRsb || aluop == OpRsc) {
        generate_store_reg_pc_no_flags(a1, it.rd());
      } else {
        generate_store_reg_pc_no_flags(a0, it.rd());
      }
    }
  }

  template <AluOperation aluop>
  inline void arm_aluimm2(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    emit_load_reg_pc(a0, it.rn(), 8);

    // Immediate is a 8 bit rotated immediate
    u32 sa = it.rot4() * 2;
    u32 imm = rotr32(it.imm8(), sa);

    // Set/Clear carry flag if appropriate (rotation result)
    if (it.rot4() != 0 && it.gen_flag_c()) {
      generate_store_reg_i32((imm >> 31), REG_C_FLAG);
    }

    switch (aluop) {
    case OpTst:
      x86_emit_and_reg_imm(reg_a0, imm);
      upd_nz_flags<SetFlags>(it);
      break;
    case OpTeq:
      x86_emit_xor_reg_imm(reg_a0, imm);
      upd_nz_flags<SetFlags>(it);
      break;
    case OpCmp:
      x86_emit_sub_reg_imm(reg_a0, imm);
      upd_nzcv_sub_flags<SetFlags>(it);
      break;
    case OpCmn:
      x86_emit_add_reg_imm(reg_a0, imm);
      upd_nzcv_add_flags<SetFlags>(it);
      break;
    };
  }

  template <AluOperation aluop, FlagOperation flg>
  inline void arm_aluimm1(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    // Immediate is a 8 bit rotated immediate
    u32 sa = it.rot4() * 2;
    u32 imm = rotr32(it.imm8(), sa);

    // Set/Clear carry flag if appropriate (rotation result)
    if (flg == SetFlags && it.rot4() != 0 && it.gen_flag_c()) {
      generate_store_reg_i32((imm >> 31), REG_C_FLAG);
    }

    if (aluop == OpMvn)
      imm = ~imm;

    generate_load_imm(a0, imm);
    upd_nz_flags_imm<flg>(it, imm);

    const u8 condition = it.cond();        // TODO remove this
    if (flg == SetFlags) {
      generate_store_reg_pc_flags(a0, it.rd());
    } else {
      generate_store_reg_pc_no_flags(a0, it.rd());
    }
  }

  // Calculates operand 2 when register is shifted/rotated by an immediate.
  template<FlagOperation flg>
  inline void emit_op2_shimm(const ARMInst &it) {
    u32 imm = it.op2sa();      // Shift amount [0..31]
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    // Uses X86 similarities to ARM to calculate the carry flag

    switch (it.op2smode()) {
    case 0:      /* LSL */
      emit_load_reg_pc(a0, it.rm(), 8);
      if (imm) {
        generate_shift_left(a0, imm);
        if (flg == SetFlags) {
          generate_update_flag(c, REG_C_FLAG);
        }
      }
      break;

    case 1:      /* LSR (0 means shift by 32) */
      if (imm) {
        emit_load_reg_pc(a0, it.rm(), 8);
        generate_shift_right(a0, imm);
        if (flg == SetFlags) {
          generate_update_flag(c, REG_C_FLAG);
        }
      } else {
        if (flg == SetFlags) {
          emit_load_reg_pc(a0, it.rm(), 8);
          generate_shift_right(a0, 31);
          generate_store_reg(a0, REG_C_FLAG);
        }
        generate_load_imm(a0, 0);
      }
      break;

    case 2:      /* ASR (0 is also shift by 32) */
      emit_load_reg_pc(a0, it.rm(), 8);
      if (imm) {
        generate_shift_right_arithmetic(a0, imm);
        if (flg == SetFlags) {
          generate_update_flag(c, REG_C_FLAG);
        }
      } else {
        // Shift by "32"
        generate_shift_right_arithmetic(a0, 31);
        if (flg == SetFlags) {
          generate_update_flag(nz, REG_C_FLAG);
        }
      }
      break;

    case 3:      /* ROR */
      emit_load_reg_pc(a0, it.rm(), 8);
      if (imm) {
        generate_rotate_right(a0, imm);
        if (flg == SetFlags) {
          generate_update_flag(c, REG_C_FLAG);
        }
      } else {   /* RRX{S} mode */
        generate_load_reg(a2, REG_C_FLAG);
        generate_shift_right(a0, 1);
        if (flg == SetFlags) {
          generate_update_flag(c, REG_C_FLAG);
        }
        generate_shift_left(a2, 31);
        generate_or(a0, a2);
      }
      break;
    };
  }

  // Calculates operand 2 when register is shifted/rotated by another register.
  template<FlagOperation flg>
  inline void emit_op2_shreg(const ARMInst &it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    emit_load_reg_pc(a0, it.rm(), 12);
    emit_load_reg_pc_lsb(reg_a2, it.rs(), 12);   // Loads the LSB byte only! Into ECX

    if (flg == SetFlags) {
      u8 *iszeroj, *jmpz32;
      x86_emit_jecxz_filler(iszeroj);    // Skip if shift amount is zero.
      switch (it.op2smode()) {
        case 0:     /* LSL */
          generate_sub_imm(a2, 1);
          generate_shift_left_var(a0);
          x86_emit_bittest(reg_a0, 31);
          generate_update_flag(c, REG_C_FLAG);
          generate_shift_left(a0, 1);
          generate_cmp_imm(a2, 32);
          x86_emit_j_filler(x86_condition_code_l, jmpz32);
            generate_load_imm(a0, 0);
            generate_store_reg_i32(0, REG_C_FLAG);
          generate_branch_patch_conditional(jmpz32, translation_ptr);
          break;
        case 1:     /* LSR */
          generate_sub_imm(a2, 1);
          generate_shift_right_var(a0);
          generate_test_imm(a0, 1);
          generate_update_flag(nz, REG_C_FLAG);
          generate_shift_right(a0, 1);
          generate_cmp_imm(a2, 32);
          x86_emit_j_filler(x86_condition_code_l, jmpz32);
            generate_load_imm(a0, 0);
            generate_store_reg_i32(0, REG_C_FLAG);
          generate_branch_patch_conditional(jmpz32, translation_ptr);
          break;
        case 2:     /* ASR */
          generate_shift_right_arithmetic_var(a0);
          generate_update_flag(c, REG_C_FLAG);
          generate_cmp_imm(a2, 32);
          x86_emit_j_filler(x86_condition_code_l, jmpz32);
          generate_shift_right_arithmetic(a0, 16);
          generate_shift_right_arithmetic(a0, 16);
          generate_update_flag(c, REG_C_FLAG);
          generate_branch_patch_conditional(jmpz32, translation_ptr);
          break;
        case 3:     /* ROR */
          generate_rotate_right_var(a0);
          x86_emit_bittest(reg_a0, 31);
          generate_update_flag(c, REG_C_FLAG);
          break;
      };
      generate_branch_patch_jecxz(iszeroj, translation_ptr);
    } else {
      switch (it.op2smode()) {
        case 0:     /* LSL */
          generate_xor(a1, a1);
          generate_shift_left_var(a0);
          generate_cmp_imm(a2, 32);
          x86_emit_cmov(nc, reg_a0, reg_a1);
          break;
        case 1:     /* LSR */
          generate_xor(a1, a1);
          generate_shift_right_var(a0);
          generate_cmp_imm(a2, 32);
          x86_emit_cmov(nc, reg_a0, reg_a1);
          break;
        case 2:     /* ASR */
          generate_cmp_imm(a2, 32);
          generate_load_imm(a1, 31);
          x86_emit_cmov(nc, reg_a2, reg_a1);
          generate_shift_right_arithmetic_var(a0);
          break;
        case 3:     /* ROR */
          generate_rotate_right_var(a0);
          break;
      };
    }
  }

  // Calculates the flex operand to a0, honoring flag (CF) generation
  template <FlagOperation flg>
  inline void emit_arm_aluop2(const ARMInst & it) {
    // Calculates the Op2 part and writes it to a0
    if (flg == SetFlags && it.gen_flag_c()) {
      if (it.op2imm())
        emit_op2_shimm<SetFlags>(it);
      else
        emit_op2_shreg<SetFlags>(it);
    } else {
      if (it.op2imm())
        emit_op2_shimm<NoFlags>(it);
      else
        emit_op2_shreg<NoFlags>(it);
    }
  }

  // 3 regs (with op2) instructions
  template <AluOperation aluop, FlagOperation flg>
  inline void arm_alureg3(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    // Generate op2 to a0, op1 to a1
    if (aluop == OpAdd || aluop == OpSub || aluop == OpRsb ||
        aluop == OpAdc || aluop == OpSbc || aluop == OpRsc)
      emit_arm_aluop2<NoFlags>(it);   // Do not generate C flag
    else
      emit_arm_aluop2<flg>(it);
    emit_load_reg_pc(a1, it.rn(), (it.op2imm() ? 8 : 12));

    switch (aluop) {
    case OpAnd:
       generate_and(a0, a1);
       upd_nz_flags<flg>(it);
       break;
    case OpOrr:
       generate_or(a0, a1);
       upd_nz_flags<flg>(it);
       break;
    case OpXor:
       generate_xor(a0, a1);
       upd_nz_flags<flg>(it);
       break;
    case OpBic:
       generate_not(a0);
       generate_and(a0, a1);
       upd_nz_flags<flg>(it);
       break;
    case OpAdd:
       generate_add(a0, a1);
       upd_nzcv_add_flags<flg>(it);
       break;
    case OpAdc:
       load_c_flag(a2);         // Load C flag into CFLAGS
       generate_adc(a0, a1);
       upd_nzcv_add_flags<flg>(it);
       break;
    case OpSub:
       generate_sub(a1, a0);
       upd_nzcv_sub_flags<flg>(it);
       break;
    case OpSbc:
       load_inv_c_flag(a2);     // Load C flag into CFLAGS
       generate_sbb(a1, a0);
       upd_nzcv_sub_flags<flg>(it);
       break;
    case OpRsb:
       generate_sub(a0, a1);
       upd_nzcv_sub_flags<flg>(it);
       break;
    case OpRsc:
       load_inv_c_flag(a2);     // Load C flag into CFLAGS
       generate_sbb(a0, a1);
       upd_nzcv_sub_flags<flg>(it);
       break;
    };

    const u8 condition = it.cond();        // TODO remove this
    if (flg == SetFlags) {
      if (aluop == OpSub || aluop == OpSbc) {
        generate_store_reg_pc_flags(a1, it.rd());
      } else {
        generate_store_reg_pc_flags(a0, it.rd());
      }
    } else {
      if (aluop == OpSub || aluop == OpSbc) {
        generate_store_reg_pc_no_flags(a1, it.rd());
      } else {
        generate_store_reg_pc_no_flags(a0, it.rd());
      }
    }
  }

  template <AluOperation aluop, FlagOperation flg>
  inline void arm_alureg1(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    emit_arm_aluop2<flg>(it);   // Generate op2 to a0
    switch (aluop) {
    case OpMvn:
       generate_xor_imm(a0, ~0U);  // Forces flag generation
       upd_nz_flags<flg>(it);
       break;
    case OpMov:
       if (flg == SetFlags) {
         generate_or(a0, a0);
         upd_nz_flags<SetFlags>(it);
       }
       break;
    };

    const u8 condition = it.cond();        // TODO remove this
    if (flg == SetFlags) {
      generate_store_reg_pc_flags(a0, it.rd());
    } else {
      generate_store_reg_pc_no_flags(a0, it.rd());
    }
  }

  // compare/test instructions
  template <AluOperation aluop, FlagOperation c_flag>
  inline void arm_alureg2(const ARMInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    emit_arm_aluop2<c_flag>(it);   // Generate op2 to a0 (with/without C flag)
    emit_load_reg_pc(a1, it.rn(), (it.op2imm() ? 8 : 12));

    switch (aluop) {
    case OpAnd:
       generate_and(a0, a1);
       upd_nz_flags<SetFlags>(it);
       break;
    case OpXor:
       generate_xor(a0, a1);
       upd_nz_flags<SetFlags>(it);
       break;
    case OpCmp:
       generate_sub(a1, a0);
       upd_nzcv_sub_flags<SetFlags>(it);
       break;
    case OpCmn:
       generate_add(a1, a0);
       upd_nzcv_add_flags<SetFlags>(it);
       break;
    };
  }
};


#define arm_hle_div(cpu_mode)                                                 \
{                                                                             \
  u8 *jmpinst;                                                                \
  generate_load_reg(a0, 0);                                                   \
  generate_load_reg(a2, 1);                                                   \
  generate_cmp_imm(a2, 0);                                                    \
  x86_emit_j_filler(x86_condition_code_z, jmpinst);                           \
  x86_emit_cdq();                                                             \
  x86_emit_idiv_eax_reg(reg_a2);                                              \
  generate_store_reg(a0, 0);                                                  \
  generate_store_reg(a1, 1);                                                  \
  generate_mov(a1, a0);                                                       \
  generate_shift_right_arithmetic(a1, 31);                                    \
  generate_xor(a0, a1);                                                       \
  generate_sub(a0, a1);                                                       \
  generate_store_reg(a0, 3);                                                  \
  generate_branch_patch_conditional(jmpinst, translation_ptr);                \
}

#define arm_hle_div_arm(cpu_mode)                                             \
{                                                                             \
  u8 *jmpinst;                                                                \
  generate_load_reg(a0, 1);                                                   \
  generate_load_reg(a2, 0);                                                   \
  generate_cmp_imm(a2, 0);                                                    \
  x86_emit_j_filler(x86_condition_code_z, jmpinst);                           \
  x86_emit_cdq();                                                             \
  x86_emit_idiv_eax_reg(reg_a2);                                              \
  generate_store_reg(a0, 0);                                                  \
  generate_store_reg(a1, 1);                                                  \
  generate_mov(a1, a0);                                                       \
  generate_shift_right_arithmetic(a1, 31);                                    \
  generate_xor(a0, a1);                                                       \
  generate_sub(a0, a1);                                                       \
  generate_store_reg(a0, 3);                                                  \
  generate_branch_patch_conditional(jmpinst, translation_ptr);                \
}

#define generate_translation_gate(type)                                       \
  generate_load_pc(a0, pc);                                                   \
  generate_indirect_branch_no_cycle_update(type)                              \

extern void* x86_table_data[9][16];
extern void* x86_table_info[9][16];

void init_emitter(bool must_swap) {
  memcpy(x86_table_info, x86_table_data, sizeof(x86_table_data));

  rom_cache_watermark = INITIAL_ROM_WATERMARK;
  init_bios_hooks();
}

u32 execute_arm_translate(u32 cycles) {
  return execute_arm_translate_internal(cycles, &reg[0]);
}

#endif
