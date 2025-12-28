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
  u32 execute_spsr_restore_body(u32 address);

  void execute_aligned_store32(u32 addr, u32 data);
  u32 execute_aligned_load32(u32 addr);

  u32 execute_arm_translate_internal(u32 cycles, void *regptr);
}

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

#define generate_addsubi(dreg, sreg, imm)                                     \
{                                                                             \
  if ((s32)(imm) >= 0) {                                                      \
    aa64_emit_addi(dreg, sreg, (imm));                                        \
  } else {                                                                    \
    aa64_emit_subi(dreg, sreg, -(imm));                                       \
  }                                                                           \
}                                                                             \


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

#define generate_block_extra_vars()                                           \
  u32 stored_pc = pc;                                                         \

#define generate_block_extra_vars_arm()                                       \
  generate_block_extra_vars();                                                \


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


#define load_c_flag()                                                         \
  aa64_emit_movne(reg_temp, 0);                                               \
  aa64_emit_adds(reg_temp, reg_temp, reg_c_cache);                            \

#define thumb_load_pc_pool_const(rd, value)                                   \
  generate_load_imm(arm_to_a64_reg[rd], (value));                             \

#define check_store_reg_pc_thumb(_rd)                                         \
  if(_rd == REG_PC)                                                           \
  {                                                                           \
    generate_indirect_branch_cycle_update(thumb);                             \
  }                                                                           \


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
  u8 *update_trampoline;     // TODO: Unused, remove!

  static unsigned block_prologue_size() { return 0; }

  inline void emit_block_prologue() {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    generate_load_imm(reg_pc, this->block_pc);
  }

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
  inline void update_nz_flags(const BaseInst & it, u32 reg) {
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

  template <FlagOperation flgmode>
  inline void update_nzcv_arith_flags(const BaseInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    if (flgmode == SetFlags) {
      if (it.gen_flag_c()) {
        aa64_emit_cset(reg_c_cache, ccode_hs);
      }
      if (it.gen_flag_v()) {
        aa64_emit_cset(reg_v_cache, ccode_vs);
      }
      if (it.gen_flag_n()) {
        aa64_emit_cset(reg_n_cache, ccode_mi);
      }
      if (it.gen_flag_z()) {
        aa64_emit_cset(reg_z_cache, ccode_eq);
      }
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

    update_nzcv_arith_flags<SetFlags>(it);
  }

  template <AluOperation aluop>
  inline void thumb_aluop2(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rs = arm_to_a64_reg[it.rs()];
    u32 rd = arm_to_a64_reg[it.rd()];

    switch (aluop) {
    case OpOrr:
      aa64_emit_orr(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpAnd:
      aa64_emit_and(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpXor:
      aa64_emit_xor(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpBic:
      aa64_emit_bic(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpMul:
      aa64_emit_mul(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpAdd:
      aa64_emit_adds(rd, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpSub:
      aa64_emit_subs(rd, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpAdc:
      load_c_flag();
      aa64_emit_adcs(rd, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpSbc:
      load_c_flag();
      aa64_emit_sbcs(rd, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    };
  }

  template <OpType stype, ShiftType st>
  inline void thumb_shft(const ThumbInst & it) {
    u32 rd = arm_to_a64_reg[it.rd()];

    if (stype == OpImm) {
      if (it.gen_flag_c())
        emit_op2_shimm<SetFlags>(rd, it.rs(), st, it.imm5(), 0);
      else
        emit_op2_shimm<NoFlags>(rd, it.rs(), st, it.imm5(), 0);
    } else {
      if (it.gen_flag_c())
        emit_op2_shreg<SetFlags>(rd, it.rd(), it.rs(), st, 0);
      else
        emit_op2_shreg<NoFlags>(rd, it.rd(), it.rs(), st, 0);
    }

    update_nz_flags<SetFlags>(it, rd);
  }

  template <AluOperation aluop>
  inline void thumb_aluop1(const ThumbInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rs = arm_to_a64_reg[it.rs()];
    u32 rd = arm_to_a64_reg[it.rd()];

    switch (aluop) {
    case OpNeg:
      aa64_emit_subs(rd, reg_zero, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpMvn:
      aa64_emit_orn(rd, reg_zero, rs);
      update_nz_flags<SetFlags>(it, rd);
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
      update_nz_flags<SetFlags>(it, reg_temp);
      break;
    case OpCmp:
      aa64_emit_subs(reg_zero, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpCmn:
      aa64_emit_adds(reg_zero, rd, rs);
      update_nzcv_arith_flags<SetFlags>(it);
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
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpSub:
      aa64_emit_subis(rd, rd, it.imm8());
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpCmp:
      aa64_emit_subis(reg_temp, rd, it.imm8());
      update_nzcv_arith_flags<SetFlags>(it);
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

    update_nzcv_arith_flags<SetFlags>(it);
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
      update_nzcv_arith_flags<SetFlags>(it);
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

  inline void thumb_bx(u32 pc, u32 regn, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    force_load_reg(regn, reg_a0, pc + 4);
    generate_indirect_branch_cycle_update(dual);
  }

  inline bool thumb_emu_swi(u32 pc, u32 num, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    switch (num) {
    case 6:
    case 7:
      {
        u32 regA = (num == 6) ? reg_r0 : reg_r1;
        u32 regB = (num == 6) ? reg_r1 : reg_r0;

        aa64_emit_sdiv(reg_r3, regA, regB);
        aa64_emit_msub(reg_r1, regA, regB, reg_r3);
        aa64_emit_mov(reg_r0, reg_r3);
        aa64_emit_cmpi(reg_r3, 0);
        aa64_emit_csneg(reg_r3, reg_r3, reg_r3, ccode_ge);
      }
      cycle_count += 64;    // Big under-estimation here
      return true;
    default:
      return false;
    };
    return false;
  }

  inline u8* thumb_swi(u32 pc, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this
    u8 *brtgt = NULL;

    generate_load_pc(reg_a0, (pc + 2));
    generate_function_call(execute_swi);
    generate_branch_cycle_update(brtgt, 0x00000008);

    return brtgt;
  }

  inline u8* thumb_b(u32 pc, u32 target, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this
    u8 *brtgt = NULL;
    generate_branch_cycle_update(brtgt, target);
    return brtgt;
  }

  inline u8* thumb_bl(u32 pc, u32 target, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this
    u8 *brtgt = NULL;

    generate_load_pc(reg_r14, ((pc + 2) | 0x01));
    generate_branch_cycle_update(brtgt, target);
    return brtgt;
  }

  inline void thumb_blh(u32 pc, u32 offset, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this

    generate_alu_imm(addi, add, reg_a0, reg_r14, offset);
    generate_load_pc(reg_r14, ((pc + 2) | 0x01));
    generate_indirect_branch_cycle_update(thumb);
  }


  // ============= Memory functions =================
  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memaddr(const ThumbInst & it, u32 regn) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this

    // Generate the memory address to a0
    switch (offt) {
    case OffPC:
      // PC-relative offset. It is word aligned.
      generate_load_pc(reg_a0, ((it.pc & (~3U)) + it.imm8() * 4 + 4));
      break;

    // rb/ro/regn are never PC in thumb mode (this is handled by OffPC mode)
    case OffReg:
      aa64_emit_add(reg_a0, arm_to_a64_reg[regn], arm_to_a64_reg[it.ro()]);
      break;
    case OffImm5:
      aa64_emit_addi(reg_a0, arm_to_a64_reg[regn], it.imm5() * sizeof(memtype));
      break;
    case OffImm8:
      aa64_emit_addi(reg_a0, arm_to_a64_reg[regn], it.imm8() * sizeof(memtype));
      break;
    }
  }

  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memld(const ThumbInst & it, u32 regd, u32 regn, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this
    cycle_count += 2;  // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the address
    thumb_memaddr<memtype, offt>(it, regn);
    // Generate a call to the right memory section handler.
    generate_load_pc(reg_a1, it.pc);
    generate_function_call(call_ldr_handler<memtype>());
    generate_store_reg(reg_res, regd);
  }

  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memst(const ThumbInst & it, u32 regd, u32 regn, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this
    cycle_count++;  // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the address
    thumb_memaddr<memtype, offt>(it, regn);
    // Load value and generate call to handler
    generate_load_reg(reg_a1, regd);
    generate_load_pc(reg_a2, (it.pc + 2));
    generate_function_call(call_str_handler<memtype>());
  }

  template <ARMMemOffset offt, MemOffDir dir>
  inline void arm_memaddr(u32 oreg, const ARMInst & it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    // Load base register if needed
    u32 breg = load_alloc_reg(it.rn(), oreg, it.pc + 8);

    switch (offt) {
    case OffImm12:     // [rn +/- imm12]
      if (dir == OffPositive) {
        aa64_emit_addi(oreg, breg, it.off12());
      } else {
        aa64_emit_subi(oreg, breg, it.off12());
      }
      break;
    case OffHImm8:     // [rn +/- imm8]
      if (dir == OffPositive) {
        aa64_emit_addi(oreg, breg, it.off8());
      } else {
        aa64_emit_subi(oreg, breg, it.off8());
      }
      break;
    case OffHReg:      // [rn +/- rm]
      {
        u32 secreg = load_alloc_reg(it.rm(), reg_temp, it.pc + 8);
        if (dir == OffPositive) {
          aa64_emit_add(oreg, breg, secreg);
        } else {
          aa64_emit_sub(oreg, breg, secreg);
        }
      }
      break;
    case OffOp2Reg:    // [rn +/- rm shift/rot amount]
      emit_op2_shimm<NoFlags>(reg_a2, it.rm(), (ShiftType)it.op2smode(), it.op2sa(), it.pc + 8);
      if (dir == OffPositive) {
        aa64_emit_add(oreg, breg, reg_a2);
      } else {
        aa64_emit_sub(oreg, breg, reg_a2);
      }
      break;
    };
  }

  template <typename memtype, ARMMemOffset offt, MemOffDir dir, MemIdxMode idxm>
  inline void arm_memst(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this
    cycle_count++;    // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the final address and base address, and write back if necessary
    if (idxm == MemIdxPostWB) {
      // Load the base reg to a0
      force_load_reg(it.rn(), reg_a0, it.pc + 4);
      // Calculate the final value to the final reg.
      u32 wbreg = store_alloc_reg(it.rn(), reg_a2);
      arm_memaddr<offt, dir>(wbreg, it);
    }
    else {
      arm_memaddr<offt, dir>(reg_a0, it);  // Calculate final addr to a0
      if (idxm == MemIdxPreWB) {
        generate_store_reg(reg_a0, it.rn());
      }
    }

    // Generate call to handler, load the value to write to a1
    force_load_reg(it.rd(), reg_a1, it.pc + 12);
    generate_load_pc(reg_a2, (it.pc + 4));
    generate_function_call(call_str_handler<memtype>());
  }

  template <typename memtype, ARMMemOffset offt, MemOffDir dir, MemIdxMode idxm>
  inline void arm_memld(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this
    const u8 condition = it.cond();        // TODO remove this
    cycle_count += 2;    // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the final address and base address, and write back if necessary
    if (idxm == MemIdxPostWB) {
      // Load the base reg to a0
      force_load_reg(it.rn(), reg_a0, it.pc + 4);
      // Calculate the final value to the final reg.
      u32 wbreg = store_alloc_reg(it.rn(), reg_a2);
      arm_memaddr<offt, dir>(wbreg, it);
    }
    else {
      arm_memaddr<offt, dir>(reg_a0, it);  // Calculate final addr to a0
      if (idxm == MemIdxPreWB) {
        generate_store_reg(reg_a0, it.rn());
      }
    }

    // Generate call to handler, load the value to write to a1
    generate_load_pc(reg_a1, it.pc);
    generate_function_call(call_ldr_handler<memtype>());
    generate_store_reg(reg_res, it.rd());

    check_store_reg_pc_no_flags(it.rd());
  }

  template <typename memtype>
  inline void arm_swap(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this
    cycle_count += 3;   // TODO: Some more accurate accounting :)

    // rd = mem[rn], mem[rn] = rm (Note: all regs could be the same!)

    force_load_reg(it.rn(), reg_a0, it.pc + 4);
    generate_load_pc(reg_a1, it.pc);
    generate_function_call(call_ldr_handler<memtype>());

    aa64_emit_mov(reg_temp, reg_res);
    force_load_reg(it.rn(), reg_a0, it.pc + 4);
    force_load_reg(it.rm(), reg_a1, it.pc + 4);
    generate_store_reg(reg_temp, it.rd());
    generate_load_pc(reg_a2, (it.pc + 4));
    generate_function_call(call_str_handler<memtype>());
  }

  template <CPUInstMode cpum, AccMode amode, AddrMode addrmode, bool writeback, bool sbit>
  inline void mem_multi(u32 pc, u32 condition, u32 basereg, u16 rlist, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this

    const u32 numops = bit_count[rlist >> 8] + bit_count[rlist & 0xFF];
    cycle_count += numops;    // TODO: Use proper cycle accounting.

    const u32 itsize = (cpum == ModeARM) ? 4 : 2;
    const s32 stpoff = (addrmode == AddrPreInc || addrmode == AddrPostInc) ? 4 : -4;
    const s32 endoff = stpoff * numops;
    const s32 inioff = (addrmode == AddrPreInc)  ? 4 :
                       (addrmode == AddrPostInc) ? 0 :
                       (addrmode == AddrPreDec)  ? endoff :
                                                   endoff + 4;

    // Load base register, clearing the lowest 2 bits (align)
    u32 screg = load_alloc_reg(basereg, reg_save0, pc + 2*itsize);
    aa64_emit_andi(reg_save0, screg, 30, 29);  /* clear 2 LSB */

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
      generate_addsubi(arm_to_a64_reg[basereg], arm_to_a64_reg[basereg], endoff);
    }

    u32 aoff = 0;
    for (u32 i = 0; i < 16; i++) {
      if (rlist & (1 << i)) {
        generate_addsubi(reg_a0, reg_save0, (aoff + inioff));
        if (amode == AccLoad) {
          generate_function_call(execute_aligned_load32);
          generate_store_reg(reg_res, i);
        } else {
          force_load_reg(i, reg_a1, pc + 2*itsize);

          // Update the base register right after the first read if necessary
          if (writeback && !writeback_first) {
            generate_addsubi(arm_to_a64_reg[basereg], arm_to_a64_reg[basereg], endoff);
            writeback_first = true;
          }

          if (rlist >> (i + 1)) {
            generate_function_call(execute_aligned_store32);
          } else {
            // Only the last store can produce side-effects
            // TODO: Evaluate if this is enough or we should improve it.
            generate_load_pc(reg_a2, (pc + itsize));
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
        update_nzcv_arith_flags<SetFlags>(it);
      }
      break;
    case OpAdc:
      load_c_flag();
      generate_load_imm(reg_temp, imm);
      aa64_emit_adcs(rd, rn, reg_temp);
      update_nzcv_arith_flags<flg>(it);
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
        update_nzcv_arith_flags<SetFlags>(it);
      }
      break;
    case OpRsb:
      generate_load_imm(reg_temp, imm);
      aa64_emit_subs(rd, reg_temp, rn);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpSbc:
      load_c_flag();
      generate_load_imm(reg_temp, imm);
      aa64_emit_sbcs(rd, rn, reg_temp);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpRsc:
      load_c_flag();
      generate_load_imm(reg_temp, imm);
      aa64_emit_sbcs(rd, reg_temp, rn);
      update_nzcv_arith_flags<flg>(it);
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
      update_nzcv_arith_flags<SetFlags>(it);
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
      update_nzcv_arith_flags<SetFlags>(it);
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
  inline void emit_op2_shimm(u32 dreg, u32 sreg, ShiftType st, u32 sa, u32 pc) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    u32 rm;

    switch (st) {
    case ShiftLSL:
      rm = load_alloc_reg(sreg, dreg, pc);
      if (flg == SetFlags && sa) {
        aa64_emit_ubfx(reg_c_cache, rm, (32 - sa), 1);
      }
      aa64_emit_lsl(dreg, rm, sa);
      break;

    case ShiftLSR:      /* (sa 0 means shift by 32) */
      if (sa) {
        rm = load_alloc_reg(sreg, dreg, pc);
        if (flg == SetFlags) {
          aa64_emit_ubfx(reg_c_cache, rm, (sa - 1), 1);
        }
        aa64_emit_lsr(dreg, rm, sa);
      } else {
        if (flg == SetFlags) {
          rm = load_alloc_reg(sreg, dreg, pc);
          aa64_emit_lsr(reg_c_cache, rm, 31);
        }
        aa64_emit_movlo(dreg, 0);
      }
      break;

    case ShiftASR:      /* (sa 0 is also shift by 32) */
      rm = load_alloc_reg(sreg, dreg, pc);
      if (flg == SetFlags) {
        aa64_emit_ubfx(reg_c_cache, rm, ((sa ? sa : 32) - 1), 1);
      }
      aa64_emit_asr(dreg, rm, (sa ? sa : 31));
      break;

    case ShiftROR:
      rm = load_alloc_reg(sreg, reg_temp, pc);
      if (sa) {
        if (flg == SetFlags) {
          aa64_emit_ubfx(reg_c_cache, rm, (sa - 1), 1);
        }
        aa64_emit_ror(dreg, rm, sa);
      } else {
        // TODO this doesn't work when rm and dreg are the same register.
        aa64_emit_extr(dreg, reg_c_cache, rm, 1);
        if (flg == SetFlags) {
          aa64_emit_ubfx(reg_c_cache, rm, 0, 1);
        }
      }
      break;
    };
  }

  // Calculates operand 2 when register is shifted/rotated by another register.
  template<FlagOperation flg>
  inline void emit_op2_shreg(u32 dreg, u32 sreg, u32 areg, ShiftType st, u32 pc) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    load_alloc_reg_lsb(areg, reg_a1, pc);  // Loads the LSB byte only!

    if (flg == SetFlags) {
      force_load_reg(sreg, dreg, pc);    // Force load reg into dreg
      switch (st) {
        case 0:     /* LSL */
          aa64_emit_cbz(reg_a1, 8);           // Skip it all on shift = 0
          // This code works if shift <= 32.
          aa64_emit_subi(reg_temp, reg_a1, 1);
          aa64_emit_lslv(dreg, dreg, reg_temp);
          aa64_emit_lsr(reg_c_cache, dreg, 31);
          aa64_emit_cmpi(reg_a1, 33);
          aa64_emit_lsl(dreg, dreg, 1);
          // If shift > 32 we just clear both reg and C flag
          aa64_emit_csel(reg_c_cache, reg_zero, reg_c_cache, ccode_hs);
          aa64_emit_csel(dreg,        reg_zero, dreg,        ccode_hs);
          break;
        case 1:     /* LSR */
          aa64_emit_cbz(reg_a1, 8);           // Skip it all on shift = 0
          aa64_emit_subi(reg_temp, reg_a1, 1);
          aa64_emit_lsrv(dreg, dreg, reg_temp);
          aa64_emit_andi(reg_c_cache, dreg, 0, 0);  /* imm=1 */
          aa64_emit_cmpi(reg_a1, 33);
          aa64_emit_lsr(dreg, dreg, 1);
          // If shift > 32 we just clear both reg and C flag
          aa64_emit_csel(reg_c_cache, reg_zero, reg_c_cache, ccode_hs);
          aa64_emit_csel(dreg,        reg_zero, dreg,        ccode_hs);
          break;
        case 2:     /* ASR */
          aa64_emit_cbz(reg_a1, 8);           // Skip it all on shift = 0
          aa64_emit_movlo(reg_temp, 32);      // Cap amount to 32.
          aa64_emit_cmpi(reg_a1, 32);
          aa64_emit_csel(reg_a1, reg_a1, reg_temp, ccode_ls);
          aa64_emit_subi(reg_temp, reg_a1, 1);
          aa64_emit_asrv(dreg, dreg, reg_temp);
          aa64_emit_andi(reg_c_cache, dreg, 0, 0);  /* imm=1 */
          aa64_emit_asr(dreg, dreg, 1);
          break;
        case 3:     /* ROR */
          // ror/lsrv only use the 5 LSB in aarch64
          aa64_emit_rorv(dreg, dreg, reg_a1);
          aa64_emit_cbz(reg_a1, 2);
          aa64_emit_lsr(reg_c_cache, dreg, 31);
          break;
      };
    } else {
      u32 rm = load_alloc_reg(sreg, dreg, pc);
      switch (st) {
        case 0:     /* LSL */
          aa64_emit_cmpi(reg_a1, 32);
          aa64_emit_lslv(reg_temp, rm, reg_a1);
          aa64_emit_csel(dreg, reg_zero, reg_temp, ccode_hs);
          break;
        case 1:     /* LSR */
          aa64_emit_cmpi(reg_a1, 32);
          aa64_emit_lsrv(reg_temp, rm, reg_a1);
          aa64_emit_csel(dreg, reg_zero, reg_temp, ccode_hs);
          break;
        case 2:     /* ASR */
          aa64_emit_cmpi(reg_a1, 31);
          aa64_emit_asr(reg_temp, rm, 31);
          aa64_emit_asrv(dreg, rm, reg_a1);
          aa64_emit_csel(dreg, dreg, reg_temp, ccode_lo);
          break;
        case 3:     /* ROR */
          aa64_emit_rorv(dreg, rm, reg_a1);
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
        emit_op2_shimm<SetFlags>(reg_a0, it.rm(), (ShiftType)it.op2smode(), it.op2sa(), it.pc + 8);
      else
        emit_op2_shimm<NoFlags>(reg_a0, it.rm(), (ShiftType)it.op2smode(), it.op2sa(), it.pc + 8);
    } else {
      if (flg == SetFlags && it.gen_flag_c())
        emit_op2_shreg<SetFlags>(reg_a0, it.rm(), it.rs(), (ShiftType)it.op2smode(), it.pc + 12);
      else
        emit_op2_shreg<NoFlags>(reg_a0, it.rm(), it.rs(), (ShiftType)it.op2smode(), it.pc + 12);
    }
    return reg_a0;
  }

  // 3 regs (with op2) instructions
  template <AluOperation aluop, FlagOperation flg>
  inline void arm_alureg3(const ARMInst & it, u32 & cycle_count) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    // Generate op2 to a0, op1 to a1
    u32 regop2 = (aluop == OpAdd || aluop == OpSub || aluop == OpRsb ||
                  aluop == OpAdc || aluop == OpSbc || aluop == OpRsc) ?
                  emit_arm_aluop2<NoFlags>(it) :  // Do not generate C flag
                  emit_arm_aluop2<flg>(it);

    u32 rn = load_alloc_reg(it.rn(), reg_a1, it.pc + (it.op2imm() ? 8 : 12));
    u32 rd = store_alloc_reg(it.rd(), reg_a0);

    switch (aluop) {
    case OpAnd:
      aa64_emit_and(rd, rn, regop2);
      update_nz_flags<flg>(it, rd);
      break;
    case OpOrr:
      aa64_emit_orr(rd, rn, regop2);
      update_nz_flags<flg>(it, rd);
      break;
    case OpXor:
      aa64_emit_xor(rd, rn, regop2);
      update_nz_flags<flg>(it, rd);
      break;
    case OpBic:
      aa64_emit_bic(rd, rn, regop2);
      update_nz_flags<flg>(it, rd);
      break;
    case OpAdd:
      aa64_emit_adds(rd, rn, regop2);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpAdc:
      load_c_flag();
      aa64_emit_adcs(rd, rn, regop2);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpSub:
      aa64_emit_subs(rd, rn, regop2);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpSbc:
      load_c_flag();
      aa64_emit_sbcs(rd, rn, regop2);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpRsb:
      aa64_emit_subs(rd, regop2, rn);
      update_nzcv_arith_flags<flg>(it);
      break;
    case OpRsc:
      load_c_flag();
      aa64_emit_sbcs(rd, regop2, rn);
      update_nzcv_arith_flags<flg>(it);
      break;
    };

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
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    case OpCmn:
      aa64_emit_adds(reg_zero, rn, regop2);
      update_nzcv_arith_flags<SetFlags>(it);
      break;
    };
  }

  // Performs 32 bit multiplications (rd and rn are swapped)
  template<FlagOperation flg, MulMode mm>
  inline void arm_mul32(const ARMInst &it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    u32 rm = load_alloc_reg(it.rm(), reg_a0, it.pc + 8);
    u32 rs = load_alloc_reg(it.rs(), reg_a1, it.pc + 8);
    u32 rd = store_alloc_reg(it.rn(), reg_a2);

    if (mm == MulAdd) {
      u32 rn = load_alloc_reg(it.rd(), reg_temp, it.pc + 8);
      aa64_emit_madd(rd, rn, rm, rs);
    } else {
      aa64_emit_mul(rd, rm, rs);
    }

    update_nz_flags<flg>(it, rd);
    // Writing PC is not really defined.
  }

  // Performs 64 bit multiplications
  template<FlagOperation flg, MulMode mm, bool signmul>
  inline void arm_mul64(const ARMInst &it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this

    u32 rm = load_alloc_reg(it.rm(), reg_a0, it.pc + 8);
    u32 rs = load_alloc_reg(it.rs(), reg_a1, it.pc + 8);
    u32 rdlo = (mm == MulAdd) ? load_alloc_reg(it.rdlo(), reg_temp, it.pc + 8)
                              : store_alloc_reg(it.rdlo(), reg_temp);
    u32 rdhi = (mm == MulAdd) ? load_alloc_reg(it.rdhi(), reg_temp2, it.pc + 8)
                              : store_alloc_reg(it.rdhi(), reg_temp2);

    if (mm == MulAdd) {
      aa64_emit_merge_regs(reg_a2, rdhi, rdlo);
      if (signmul) {
        aa64_emit_smaddl(reg_a2, reg_a2, rm, rs);
      } else {
        aa64_emit_umaddl(reg_a2, reg_a2, rm, rs);
      }
    } else {
      if (signmul) {
        aa64_emit_smaddl(reg_a2, reg_zero, rm, rs);
      } else {
        aa64_emit_umaddl(reg_a2, reg_zero, rm, rs);
      }
    }

    aa64_emit_andi64(rdlo, reg_a2, 0, 31);
    aa64_emit_lsr64(rdhi, reg_a2, 32);

    if (flg == SetFlags) {
      aa64_emit_orr(reg_z_cache, rdlo, rdhi);
      aa64_emit_cmpi(reg_z_cache, 0);  // TODO: perform the check on 64 bits to save 1 inst.
      aa64_emit_cset(reg_z_cache, ccode_eq);
      aa64_emit_lsr(reg_n_cache, rdhi, 31);
    }
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

    generate_store_reg(reg_res, it.rd());
  }

  // PSR register write
  template<PSReg reg, OpType opt>
  inline void arm_write_psr(const ARMInst &it) {
    u8 * &translation_ptr = this->emit_ptr;   // TODO: Remove this
    const u32 stored_pc = this->block_pc;     // TODO: Remove this

    if (opt == OpReg) {
      generate_load_reg(reg_a0, it.rm());
    } else {
      u32 imm = rotr32(it.imm8(), it.rot4() * 2);
      generate_load_imm(reg_a0, imm);
    }

    if (reg == RegCPSR) {
      generate_load_pc(reg_a1, it.pc);
      generate_load_imm(reg_a2, cpsr_masks[it.field_fc()][0]);
      generate_load_imm(reg_temp, cpsr_masks[it.field_fc()][1]);
      generate_function_call(execute_store_cpsr);
    } else {
      generate_load_imm(reg_a1, spsr_masks[it.field_fc()]);
      generate_function_call(execute_store_spsr);
    }
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


