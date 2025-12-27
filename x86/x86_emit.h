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

  u32 execute_read_cpsr();
  u32 execute_read_spsr();
  void execute_store_spsr(u32 new_spsr, u32 store_mask);
  void execute_store_cpsr(u32 new_cpsr, u32 store_mask);

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

#define generate_add_mem(imm, ireg_base, offset)                              \
  x86_emit_add_mem_imm(imm, reg_##ireg_base, (offset))                        \

#define generate_and(ireg_dest, ireg_src)                                     \
  x86_emit_and_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_add(ireg_dest, ireg_src)                                     \
  x86_emit_add_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_adc(ireg_dest, ireg_src)                                     \
  x86_emit_adc_reg_reg(reg_##ireg_dest, reg_##ireg_src)                       \

#define generate_add_memreg(ireg_dest, arm_reg_src)                           \
  x86_emit_add_reg_mem(reg_##ireg_dest, reg_base, arm_reg_src * 4)            \

#define generate_sub_memreg(ireg_dest, arm_reg_src)                           \
  x86_emit_sub_reg_mem(reg_##ireg_dest, reg_base, arm_reg_src * 4)            \

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


// Operation types: imm, mem_reg, mem_imm

#define thumb_load_pc_pool_const(reg_rd, value)                               \
  generate_store_reg_i32(value, reg_rd)                                       \


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

// Borrow flag in ARM is opposite to carry flag in x86

#define load_c_flag()                                                         \
  x86_emit_mem_bittest(0, reg_base, REG_C_FLAG * 4)                           \

#define load_inv_c_flag()                                                     \
  x86_emit_mem_bittest(0, reg_base, REG_C_FLAG * 4)                           \
  x86_emit_cmc()

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


/* Just loads the LSB byte of the desired register */
#define emit_load_reg_pc_lsb(ireg, regnum, pcvalue)                           \
  if(regnum == REG_PC) {                                                      \
    x86_emit_mov_reg_imm(ireg, 0xFF & (pcvalue));                             \
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

template <typename memtype> inline uintptr_t call_ldr_handler();
template <typename memtype> inline uintptr_t call_str_handler();

template <> inline uintptr_t call_ldr_handler<u32>() { return (uintptr_t)execute_load_u32; }
template <> inline uintptr_t call_ldr_handler<u16>() { return (uintptr_t)execute_load_u16; }
template <> inline uintptr_t call_ldr_handler<u8>()  { return (uintptr_t)execute_load_u8 ; }
template <> inline uintptr_t call_ldr_handler<s16>() { return (uintptr_t)execute_load_s16; }
template <> inline uintptr_t call_ldr_handler<s8>()  { return (uintptr_t)execute_load_s8 ; }

template <> inline uintptr_t call_str_handler<u32>() { return (uintptr_t)execute_store_u32; }
template <> inline uintptr_t call_str_handler<u16>() { return (uintptr_t)execute_store_u16; }
template <> inline uintptr_t call_str_handler<u8>()  { return (uintptr_t)execute_store_u8 ; }


class CodeEmitter : public CodeEmitterBase {
public:
  CodeEmitter(u8 *emit_ptr, u8 *emit_end, u32 pc)
   : CodeEmitterBase(emit_ptr, emit_end) {}

  template <FlagOperation flgmode>
  inline void upd_nz_flags(const BaseInst & it) {
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
  inline void upd_nzcv_add_flags(const BaseInst & it) {
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
  inline void upd_nzcv_sub_flags(const BaseInst & it) {
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

  inline void load_reg(u32 dreg, u32 regnum, u32 pc_value) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    if (regnum == REG_PC) {
      x86_emit_mov_reg_imm(dreg, pc_value);
    } else {
      x86_emit_mov_reg_mem(dreg, reg_base, regnum * 4);
    }
  }

  inline void store_reg(u32 dreg, u32 regnum) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    x86_emit_mov_mem_reg(dreg, reg_base, regnum * 4)
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
      x86_emit_add_reg_reg(reg_a0, reg_a1);
      update_cv_add_flags();
      break;
    case OpSub:
      x86_emit_sub_reg_reg(reg_a0, reg_a1);
      update_cv_sub_flags();
      break;
    case OpAdc:
      load_c_flag();         // Load C flag into CFLAGS
      generate_adc(a0, a1);
      update_cv_add_flags();
      break;
    case OpSbc:
      load_inv_c_flag();         // Load !C flag into CFLAGS
      generate_sbb(a0, a1);
      update_cv_sub_flags();
      break;
    };

    upd_nz_flags<SetFlags>(it);
    generate_store_reg(a0, it.rd());
  }

  template <OpType stype, ShiftType st>
  inline void thumb_shft(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    if (stype == OpImm) {
      if (it.gen_flag_c())
        emit_op2_shimm<SetFlags>(reg_a0, it.rs(), st, it.imm5(), 0);
      else
        emit_op2_shimm<NoFlags>(reg_a0, it.rs(), st, it.imm5(), 0);
    } else {
      if (it.gen_flag_c())
        emit_op2_shreg<SetFlags>(reg_a0, it.rd(), it.rs(), st, 0);
      else
        emit_op2_shreg<NoFlags>(reg_a0, it.rd(), it.rs(), st, 0);
    }

    store_reg(reg_a0, it.rd());

    if (it.gen_flag_z() || it.gen_flag_n()) {
      generate_or(a0, a0);
      if (it.gen_flag_z()) {
        generate_update_flag(z, REG_Z_FLAG);
      }
      if (it.gen_flag_n()) {
        generate_update_flag(s, REG_N_FLAG);
      }
    }
  }

  template <AluOperation aluop>
  inline void thumb_aluop1(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    generate_load_reg(a0, it.rs());   // Load operand

    switch (aluop) {
    case OpNeg:
      generate_xor(a1, a1);
      x86_emit_sub_reg_reg(reg_a1, reg_a0);
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
      x86_emit_sub_reg_reg(reg_a0, reg_a1);
      upd_nzcv_sub_flags<SetFlags>(it);
      break;
    case OpCmn:
      x86_emit_add_reg_reg(reg_a0, reg_a1);
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
      generate_add_mem(it.imm8(), base, it.rd8() * 4);
      upd_nzcv_add_flags<SetFlags>(it);
      break;
    case OpSub:
      generate_sub_mem(it.imm8(), base, it.rd8() * 4);
      upd_nzcv_sub_flags<SetFlags>(it);
      break;
    case OpCmp:
      generate_load_reg(a1, it.rd8());
      generate_load_imm(a0, it.imm8());
      x86_emit_sub_reg_reg(reg_a1, reg_a0);
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

    switch (aluop) {
    case OpAdd:
      generate_add_memreg(a0, it.rn());
      upd_nzcv_add_flags<SetFlags>(it);
      break;
    case OpSub:
      generate_sub_memreg(a0, it.rn());
      upd_nzcv_sub_flags<SetFlags>(it);
      break;
    };

    generate_store_reg(a0, it.rd());
  }

  template <AluOperation aluop>
  inline void thumb_aluhi(const ThumbInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    load_reg(reg_a0, it.rs_hi(), it.pc + 4);

    switch (aluop) {
    case OpAdd:
      load_reg(reg_a1, it.rd_hi(), it.pc + 4);
      x86_emit_add_reg_reg(reg_a0, reg_a1);
      generate_store_reg_pc_thumb(a0, it.rd_hi());
      break;
    case OpCmp:
      load_reg(reg_a1, it.rd_hi(), it.pc + 4);
      x86_emit_sub_reg_reg(reg_a1, reg_a0);
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
    generate_add_mem((offset * 4), base, REG_SP * 4);
  }

  // ======== Memory instructions ===================================
  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memaddr(const ThumbInst & it, u32 regn) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    // Generate the memory address to a0
    if (offt == OffPC) {
      // PC-relative offset. It is word aligned.
      generate_load_pc(a0, ((it.pc & (~3U)) + it.imm8() * 4 + 4));
    } else {
      generate_load_reg(a0, regn);
      if (offt == OffReg) {
        generate_add_memreg(a0, it.ro());
      } else if (offt == OffImm5) {
        generate_add_imm(a0, it.imm5() * sizeof(memtype));
      } else {
        generate_add_imm(a0, it.imm8() * sizeof(memtype));
      }
    }
  }

  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memld(const ThumbInst & it, u32 regd, u32 regn, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    cycle_count += 2;  // TODO: Use proper cycle accounting and honor WAITCNT
    // Generate the address
    thumb_memaddr<memtype, offt>(it, regn);
    // Generate call to handler, store the result in the rd() register
    generate_load_pc(a1, it.pc);
    generate_function_call(call_ldr_handler<memtype>());
    generate_store_reg(rv, regd);
  }

  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memst(const ThumbInst & it, u32 regd, u32 regn, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    cycle_count++;  // TODO: Use proper cycle accounting and honor WAITCNT
    // Generate the address
    thumb_memaddr<memtype, offt>(it, regn);
    // Load value and generate call to handler
    load_reg(reg_a1, regd, it.pc + 12);
    generate_store_reg_i32(it.pc + 2, REG_PC);
    generate_function_call(call_str_handler<memtype>());
  }

  template <ARMMemOffset offt, MemOffDir dir>
  inline void arm_memaddr(u32 faddr_reg, u32 baddr_reg, const ARMInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    // Load base register
    load_reg(baddr_reg, it.rn(), it.pc + 8);

    switch (offt) {
    case OffImm12:     // [rn +/- imm12]
      {
        const u32 off = (dir == OffPositive) ? it.off12() : -it.off12();
        x86_emit_lea_reg_mem(faddr_reg, baddr_reg, off);
      }
      break;
    case OffHImm8:     // [rn +/- imm8]
      {
        const u32 off = (dir == OffPositive) ? it.off8() : -it.off8();
        x86_emit_lea_reg_mem(faddr_reg, baddr_reg, off);
      }
      break;
    case OffHReg:      // [rn +/- rm]
      load_reg(faddr_reg, it.rm(), it.pc + 8);
      if (dir == OffNegative) {
        x86_emit_neg_reg(faddr_reg);
      }
      x86_emit_add_reg_reg(faddr_reg, baddr_reg);
      break;
    case OffOp2Reg:    // [rn +/- rm shift/rot amount]
      emit_op2_shimm<NoFlags>(faddr_reg, it.rm(), (ShiftType)it.op2smode(), it.op2sa(), it.pc + 8);
      if (dir == OffNegative) {
        x86_emit_neg_reg(faddr_reg);
      }
      x86_emit_add_reg_reg(faddr_reg, baddr_reg);
      break;
    };
  }

  template <typename memtype, ARMMemOffset offt, MemOffDir dir, MemIdxMode idxm>
  inline void arm_memst(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    cycle_count++;    // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the final address and base address, and write back if necessary
    if (idxm == MemIdxPostWB) {
      arm_memaddr<offt, dir>(reg_a1, reg_a0, it);  // Uses base_reg for the access
      generate_store_reg(a1, it.rn());
    }
    else {
      arm_memaddr<offt, dir>(reg_a0, reg_a1, it);  // Uses final addr for the access
      if (idxm == MemIdxPreWB) {
        generate_store_reg(a0, it.rn());
      }
    }

    // Generate call to handler, load the value to write to a1
    load_reg(reg_a1, it.rd(), it.pc + 12);
    generate_store_reg_i32(it.pc + 4, REG_PC);
    generate_function_call(call_str_handler<memtype>());
  }

  template <typename memtype, ARMMemOffset offt, MemOffDir dir, MemIdxMode idxm>
  inline void arm_memld(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u8 condition = it.cond();        // TODO remove this
    cycle_count += 2;    // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the final address and base address, and write back if necessary
    if (idxm == MemIdxPostWB) {
      arm_memaddr<offt, dir>(reg_a1, reg_a0, it);  // Uses base_reg for the access
      generate_store_reg(a1, it.rn());
    }
    else {
      arm_memaddr<offt, dir>(reg_a0, reg_a1, it);  // Uses final addr for the access
      if (idxm == MemIdxPreWB) {
        generate_store_reg(a0, it.rn());
      }
    }

    // Generate call to handler, load the value to write to a1
    generate_load_pc(a1, it.pc);
    generate_function_call(call_ldr_handler<memtype>());
    generate_store_reg_pc_no_flags(rv, it.rd());
  }

  template <typename memtype>
  inline void arm_swap(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    cycle_count += 3;   // TODO: Some more accurate accounting :)

    // rd = mem[rn], mem[rn] = rm (Note: all regs could be the same!)

    load_reg(reg_a0, it.rn(), it.pc + 8);
    generate_load_pc(a1, it.pc);
    generate_function_call(call_ldr_handler<memtype>());

    generate_mov(a2, rv);
    generate_load_reg(a0, it.rn());
    generate_load_reg(a1, it.rm());
    generate_store_reg(a2, it.rd());
    generate_store_reg_i32(it.pc + 4, REG_PC);
    generate_function_call(call_str_handler<memtype>());
  }

  template <CPUInstMode cpum, AccMode amode, AddrMode addrmode, bool writeback, bool sbit>
  inline void mem_multi(u32 pc, u32 condition, u32 basereg, u16 rlist, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 numops = bit_count[rlist >> 8] + bit_count[rlist & 0xFF];
    cycle_count += numops;    // TODO: Use proper cycle accounting.

    const u32 itsize = (cpum == ModeARM) ? 4 : 2;
    const s32 stpoff = (addrmode == AddrPreInc || addrmode == AddrPostInc) ? 4 : -4;
    const s32 endoff = stpoff * numops;
    const s32 inioff = (addrmode == AddrPreInc)  ? 4 :
                       (addrmode == AddrPostInc) ? 0 :
                       (addrmode == AddrPreDec)  ? endoff :
                                                   endoff + 4;

    generate_load_reg(a0, basereg);  // Load base reg and word-align it.
    generate_and_imm(a0, ~0x03);
    generate_store_reg(a0, REG_SAVE3);

    // If base is in the reglist and writeback is enabled, the value of the
    // written register depends on the write cycle (ARM7TDM manual 4.11.6).
    // If the register is the first, the written value is the original value,
    // otherwise the update base register is written. For LDM loaded data
    // takes always precendence.
    bool wrbck_base = (1 << basereg) & rlist;
    bool base_first = (((1 << basereg) - 1) & rlist) == 0;
    bool writeback_first = (amode == AccLoad) || !(wrbck_base && base_first);

    // This is the most common case by far.
    if (writeback && writeback_first) {
      generate_add_mem(endoff, base, basereg * 4);
    }

    u32 aoff = 0;
    for (u32 i = 0; i < 16; i++) {
      if (rlist & (1 << i)) {
        generate_load_reg(a0, REG_SAVE3);
        generate_add_imm(a0, (aoff + inioff));
        if (amode == AccLoad) {
          generate_load_pc(a1, pc);
          generate_function_call(execute_load_u32);
          generate_store_reg(rv, i);
        } else {
          load_reg(reg_a1, i, pc + 2*itsize);

          // Update the base register right after the first read if necessary
          if (writeback && !writeback_first) {
            generate_add_mem(endoff, base, basereg * 4);
            writeback_first = true;
          }

          if (rlist >> (i + 1)) {
            generate_function_call(execute_store_aligned_u32);
          } else {
            // Only the last store can produce side-effects
            // TODO: Evaluate if this is enough or we should improve it.
            generate_store_reg_i32(pc + itsize, REG_PC);
            generate_function_call(execute_store_u32);
          }
        }
        aoff += 4;
      }
    }

    // Load PC requires an indirect branch
    if (amode == AccLoad && (rlist & (1 << REG_PC))) {
      if (cpum == ModeARM) {
        generate_indirect_branch_arm();
      } else {
        generate_indirect_branch_cycle_update(thumb);
      }
    }
  }

  // ======== ARM instructions ======================================
  template <AluOperation aluop, FlagOperation flg>
  inline void arm_aluimm3(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    load_reg(reg_a0, it.rn(), it.pc + 8);

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
      load_c_flag();         // Load C flag into CFLAGS
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
      load_inv_c_flag();     // Load C flag into CFLAGS
      x86_emit_sbb_reg_imm(reg_a0, imm);
      upd_nzcv_sub_flags<flg>(it);
      break;
    case OpRsc:
      load_inv_c_flag();     // Load C flag into CFLAGS
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
    load_reg(reg_a0, it.rn(), it.pc + 8);

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
  // Uses no other registers beside `dreg`.
  // NOTE: dreg is a native reg, sreg an ARM reg
  template<FlagOperation c_flg>
  inline void emit_op2_shimm(u32 dreg, u32 sreg, ShiftType st, u32 sa, u32 pc) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    // Uses X86 similarities to ARM to calculate the carry flag

    switch (st) {
    case ShiftLSL:
      load_reg(dreg, sreg, pc);
      if (sa) {
        x86_emit_shl_reg_imm(dreg, sa);
        if (c_flg == SetFlags) {
          generate_update_flag(c, REG_C_FLAG);
        }
      }
      break;

    case ShiftLSR:
      if (sa) {
        load_reg(dreg, sreg, pc);
        x86_emit_shr_reg_imm(dreg, sa);
        if (c_flg == SetFlags) {
          generate_update_flag(c, REG_C_FLAG);
        }
      } else {
        if (c_flg == SetFlags) {
          load_reg(dreg, sreg, pc);
          x86_emit_shr_reg_imm(dreg, 31);
          generate_store_reg(a0, REG_C_FLAG);
        }
        x86_emit_mov_reg_imm(dreg, 0);
      }
      break;

    case ShiftASR:
      load_reg(dreg, sreg, pc);
      if (sa) {
        x86_emit_sar_reg_imm(dreg, sa);
        if (c_flg == SetFlags) {
          generate_update_flag(c, REG_C_FLAG);
        }
      } else {   // Shift by "32"
        x86_emit_sar_reg_imm(dreg, 31);
        if (c_flg == SetFlags) {
          generate_update_flag(nz, REG_C_FLAG);
        }
      }
      break;

    case ShiftROR:
      load_reg(dreg, sreg, pc);
      if (sa) {
        x86_emit_ror_reg_imm(dreg, sa);
        if (c_flg == SetFlags) {
          generate_update_flag(c, REG_C_FLAG);
        }
      } else {   /* RRX{S} mode */
        load_c_flag();
        x86_emit_rot_reg1(rcr, dreg);
        if (c_flg == SetFlags) {
          generate_update_flag(c, REG_C_FLAG);
        }
      }
      break;
    };
  }

  // Calculates operand 2 when register is shifted/rotated by another register.
  template<FlagOperation c_flg>
  inline void emit_op2_shreg(u32 dreg, u32 sreg, u32 areg, ShiftType st, u32 pc) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    load_reg(dreg, sreg, pc);
    emit_load_reg_pc_lsb(reg_a2, areg, pc);   // Loads the LSB byte only! Into ECX

    if (c_flg == SetFlags) {
      u8 *iszeroj, *jmpz32;
      x86_emit_jecxz_filler(iszeroj);    // Skip if shift amount is zero.
      switch (st) {
        case ShiftLSL:
          generate_sub_imm(a2, 1);
          x86_emit_shl_reg_reg(dreg);
          x86_emit_bittest(dreg, 31);
          generate_update_flag(c, REG_C_FLAG);
          x86_emit_shl_reg_imm(dreg, 1);
          generate_cmp_imm(a2, 32);
          x86_emit_j_filler(x86_condition_code_l, jmpz32);
            x86_emit_mov_reg_imm(dreg, 0);
            generate_store_reg_i32(0, REG_C_FLAG);
          generate_branch_patch_conditional(jmpz32, translation_ptr);
          break;
        case ShiftLSR:
          generate_sub_imm(a2, 1);
          x86_emit_shr_reg_reg(dreg);
          x86_emit_test_reg_imm(dreg, 0x1);
          generate_update_flag(nz, REG_C_FLAG);
          x86_emit_shr_reg_imm(dreg, 1);
          generate_cmp_imm(a2, 32);
          x86_emit_j_filler(x86_condition_code_l, jmpz32);
            x86_emit_mov_reg_imm(dreg, 0);
            generate_store_reg_i32(0, REG_C_FLAG);
          generate_branch_patch_conditional(jmpz32, translation_ptr);
          break;
        case ShiftASR:
          x86_emit_sar_reg_reg(dreg);
          generate_update_flag(c, REG_C_FLAG);
          generate_cmp_imm(a2, 32);
          x86_emit_j_filler(x86_condition_code_l, jmpz32);
          x86_emit_sar_reg_imm(dreg, 16);
          x86_emit_sar_reg_imm(dreg, 16);
          generate_update_flag(c, REG_C_FLAG);
          generate_branch_patch_conditional(jmpz32, translation_ptr);
          break;
        case ShiftROR:
          x86_emit_rot_reg_reg(ror, dreg);
          x86_emit_bittest(dreg, 31);
          generate_update_flag(c, REG_C_FLAG);
          break;
      };
      generate_branch_patch_jecxz(iszeroj, translation_ptr);
    } else {
      switch (st) {
        case ShiftLSL:
          generate_xor(a1, a1);
          x86_emit_shl_reg_reg(dreg);
          generate_cmp_imm(a2, 32);
          x86_emit_cmov(nc, dreg, reg_a1);
          break;
        case ShiftLSR:
          generate_xor(a1, a1);
          x86_emit_shr_reg_reg(dreg);
          generate_cmp_imm(a2, 32);
          x86_emit_cmov(nc, dreg, reg_a1);
          break;
        case ShiftASR:
          generate_cmp_imm(a2, 32);
          generate_load_imm(a1, 31);
          x86_emit_cmov(nc, reg_a2, reg_a1);
          x86_emit_sar_reg_reg(dreg);
          break;
        case ShiftROR:
          x86_emit_rot_reg_reg(ror, dreg);
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
        emit_op2_shimm<SetFlags>(reg_a0, it.rm(), (ShiftType)it.op2smode(), it.op2sa(), it.pc + 8);
      else
        emit_op2_shreg<SetFlags>(reg_a0, it.rm(), it.rs(), (ShiftType)it.op2smode(), it.pc + 12);
    } else {
      if (it.op2imm())
        emit_op2_shimm<NoFlags>(reg_a0, it.rm(), (ShiftType)it.op2smode(), it.op2sa(), it.pc + 8);
      else
        emit_op2_shreg<NoFlags>(reg_a0, it.rm(), it.rs(), (ShiftType)it.op2smode(), it.pc + 12);
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
    load_reg(reg_a1, it.rn(), it.pc + (it.op2imm() ? 8 : 12));

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
       x86_emit_add_reg_reg(reg_a0, reg_a1);
       upd_nzcv_add_flags<flg>(it);
       break;
    case OpAdc:
       load_c_flag();         // Load C flag into CFLAGS
       generate_adc(a0, a1);
       upd_nzcv_add_flags<flg>(it);
       break;
    case OpSub:
       x86_emit_sub_reg_reg(reg_a1, reg_a0);
       upd_nzcv_sub_flags<flg>(it);
       break;
    case OpSbc:
       load_inv_c_flag();     // Load C flag into CFLAGS
       generate_sbb(a1, a0);
       upd_nzcv_sub_flags<flg>(it);
       break;
    case OpRsb:
       x86_emit_sub_reg_reg(reg_a0, reg_a1);
       upd_nzcv_sub_flags<flg>(it);
       break;
    case OpRsc:
       load_inv_c_flag();     // Load C flag into CFLAGS
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
    load_reg(reg_a1, it.rn(), it.pc + (it.op2imm() ? 8 : 12));

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
       x86_emit_sub_reg_reg(reg_a1, reg_a0);
       upd_nzcv_sub_flags<SetFlags>(it);
       break;
    case OpCmn:
       x86_emit_add_reg_reg(reg_a1, reg_a0);
       upd_nzcv_add_flags<SetFlags>(it);
       break;
    };
  }

  // Performs 32 bit multiplications (rd and rn are swapped)
  template<FlagOperation flg, MulMode mm>
  inline void arm_mul32(const ARMInst &it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    load_reg(reg_a0, it.rm(), it.pc + 8);
    load_reg(reg_a1, it.rs(), it.pc + 8);
    generate_multiply(a1);

    if (mm == MulAdd) {
      load_reg(reg_a1, it.rd(), it.pc + 8);
      x86_emit_add_reg_reg(reg_a0, reg_a1);
    } else if (flg == SetFlags) {
      generate_and(a0, a0);
    }

    upd_nz_flags<flg>(it);
    generate_store_reg(a0, it.rn());
  }

  // Performs 64 bit multiplications
  template<FlagOperation flg, MulMode mm, bool signmul>
  inline void arm_mul64(const ARMInst &it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    load_reg(reg_a0, it.rm(), it.pc + 8);
    load_reg(reg_a1, it.rs(), it.pc + 8);

    if (signmul) {
      x86_emit_imul_eax_reg(reg_a1); // EAX * A1 -> EDX:EAX
    } else {
      x86_emit_mul_eax_reg(reg_a1);
    }

    if (mm == MulAdd) {
      generate_load_reg(a2, it.rdlo());
      generate_load_reg(t0, it.rdhi());
      x86_emit_add_reg_reg(reg_a0, reg_a2);
      generate_adc(a1, t0);
    }

    if (flg == SetFlags) {
      generate_mov(t0, a1);
      generate_and(t0, t0);
      generate_update_flag(s, REG_N_FLAG);
      generate_or(t0, a0);
      generate_update_flag(z, REG_Z_FLAG);
    }

    generate_store_reg(a0, it.rdlo());
    generate_store_reg(a1, it.rdhi());
  }

  // PSR register read
  template<PSReg reg>
  inline void arm_read_psr(const ARMInst &it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    if (reg == RegCPSR) {
      generate_function_call(execute_read_cpsr);
    } else {
      generate_function_call(execute_read_spsr);
    }

    generate_store_reg(rv, it.rd());
  }

  // PSR register write
  template<PSReg reg, OpType opt>
  inline void arm_write_psr(const ARMInst &it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    if (opt == OpReg) {
      generate_load_reg(a0, it.rm());
    } else {
      u32 imm = rotr32(it.imm8(), it.rot4() * 2);
      generate_load_imm(a0, imm);
    }

    if (reg == RegCPSR) {
      generate_load_imm(a1, cpsr_masks[it.field_fc()][0]);
      generate_load_imm(a2, cpsr_masks[it.field_fc()][1]);
      generate_store_reg_i32(it.pc, REG_PC);
      generate_function_call(execute_store_cpsr);
    } else {
      generate_load_imm(a1, spsr_masks[it.field_fc()]);
      generate_function_call(execute_store_spsr);
    }
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
  x86_emit_sub_reg_reg(reg_a0, reg_a1);                                       \
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
  x86_emit_sub_reg_reg(reg_a0, reg_a1);                                       \
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
