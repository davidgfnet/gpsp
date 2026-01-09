/* gameplaySP
 *
 * Copyright (C) 2006 Exophase <exophase@gmail.com>
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

#ifndef MIPS_EMIT_H
#define MIPS_EMIT_H

#include "mips/mips_codegen.h"

// Pointer table to stubs, indexed by type and region
extern u32 tmemld[11][16];
extern u32 tmemst[ 4][16];
extern u32 thnjal[15*16];

// Pointers to default handlers.
// Use IWRAM as default, assume aligned by default too
#define execute_load_u8   tmemld[0][3]
#define execute_load_s8   tmemld[1][3]
#define execute_load_u16  tmemld[2][3]
#define execute_load_s16  tmemld[4][3]
#define execute_load_u32  tmemld[6][3]
#define execute_aligned_load32 tmemld[10][3]
#define execute_store_u8  tmemst[0][3]
#define execute_store_u16 tmemst[1][3]
#define execute_store_u32 tmemst[2][3]
#define execute_aligned_store32 tmemst[3][3]

extern "C" {
  u32 mips_update_gba(u32 pc);

  // Although these are defined as a function, don't call them as
  // such (jump to it instead)
  void mips_indirect_branch_arm(u32 address);
  void mips_indirect_branch_thumb(u32 address);
  void mips_indirect_branch_dual(u32 address);

  u32 execute_read_cpsr();
  u32 execute_read_spsr();
  void execute_swi(u32 pc);
  void mips_cheat_hook(void);
  void smc_write();
  void write_io_epilogue();

  u32 execute_spsr_restore(u32 address);
  void execute_store_cpsr(u32 new_cpsr, u32 store_mask);
  void execute_store_spsr(u32 new_spsr, u32 store_mask);

  u32 execute_spsr_restore_body(u32 address);

  u32 execute_arm_translate_internal(u32 cycles, void *regptr);
}

#define reg_base    mips_reg_s0
#define reg_cycles  mips_reg_s1
#define reg_a0      mips_reg_a0
#define reg_a1      mips_reg_a1
#define reg_a2      mips_reg_a2
#define reg_rv      mips_reg_v0
#define reg_pc      mips_reg_s3
#define reg_temp    mips_reg_at
#define reg_zero    mips_reg_zero

#define reg_n_cache mips_reg_s4
#define reg_z_cache mips_reg_s5
#define reg_c_cache mips_reg_s6
#define reg_v_cache mips_reg_s7

#define reg_r0      mips_reg_v1
#define reg_r1      mips_reg_a3
#define reg_r2      mips_reg_t0
#define reg_r3      mips_reg_t1
#define reg_r4      mips_reg_t2
#define reg_r5      mips_reg_t3
#define reg_r6      mips_reg_t4
#define reg_r7      mips_reg_t5
#define reg_r8      mips_reg_t6
#define reg_r9      mips_reg_t7
#define reg_r10     mips_reg_s2
#define reg_r11     mips_reg_t8
#define reg_r12     mips_reg_t9
#define reg_r13     mips_reg_gp
#define reg_r14     mips_reg_fp

// Writing to r15 goes straight to a0, to be chained with other ops

const mips_regnum arm_to_mips_reg[] = {
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

// Palette conversion functions. a1 contains the palette value (16 LSB)
// Places the result in reg_temp, can use a0 as temporary register
#if defined(USE_XBGR1555_FORMAT)
  /* PS2's native format */
  #define palette_convert()                       \
    emit_andi(reg_temp, reg_a1, 0x7FFF);
#else
  /* 0BGR to RGB565 (clobbers a0) */
  #ifdef MIPS_HAS_R2_INSTS
    #define palette_convert()                       \
      emit_ext(reg_temp, reg_a1, 10, 5);       \
      emit_ins(reg_temp, reg_a1, 11, 5);       \
      emit_ext(reg_a0, reg_a1, 5, 5);          \
      emit_ins(reg_temp, reg_a0, 6, 5);
  #else
    #define palette_convert()                       \
      emit_srl(reg_a0, reg_a1, 10);            \
      emit_andi(reg_temp, reg_a0, 0x1F);       \
      emit_sll(reg_a0, reg_a1, 1);             \
      emit_andi(reg_a0, reg_a0, 0x7C0);        \
      emit_or(reg_temp, reg_temp, reg_a0);     \
      emit_andi(reg_a0, reg_a1, 0x1F);         \
      emit_sll(reg_a0, reg_a0, 11);            \
      emit_or(reg_temp, reg_temp, reg_a0);
  #endif
#endif


#define generate_load_reg(ireg, reg_index)                                    \
  emit_addu(ireg, arm_to_mips_reg[reg_index], reg_zero)                  \

#define generate_load_imm(ireg, imm)                                          \
  if(((s32)imm >= -32768) && ((s32)imm <= 32767)) {                           \
    emit_addiu(ireg, reg_zero, (u16)imm);                                     \
  } else if(((u32)imm >> 16) == 0x0000) {                                     \
    emit_ori(ireg, reg_zero, (u16)imm);                                       \
  } else {                                                                    \
    emit_lui(ireg, imm >> 16);                                                \
    if (((u32)(imm) & 0x0000FFFF)) {                                          \
      emit_ori(ireg, ireg, (imm) & 0xFFFF);                                   \
    }                                                                         \
  }                                                                           \

#define generate_store_reg(ireg, reg_index)                                   \
  emit_addu(arm_to_mips_reg[reg_index], ireg, reg_zero)                  \

#define generate_mov(ireg_dest, ireg_src)                                     \
  emit_addu(ireg_dest, ireg_src, reg_zero)                               \

#define generate_function_call(function_location)                             \
  emit_jal(mips_absolute_offset(function_location));                     \
  emit_nop()                                                             \

#define generate_raw_u32(value)                                               \
  *((u32 *)this->emit_ptr) = (value);                                         \
  this->emit_ptr += 4                                                         \

#define generate_function_call_swap_delay(function_location)                  \
{                                                                             \
  u32 delay_instruction = address32(this->emit_ptr, -4);                      \
  this->emit_ptr -= 4;                                                        \
  emit_jal(mips_absolute_offset(function_location));                     \
  address32(this->emit_ptr, 0) = delay_instruction;                           \
  this->emit_ptr += 4;                                                        \
}                                                                             \

#define generate_function_return_swap_delay()                                 \
{                                                                             \
  u32 delay_instruction = address32(this->emit_ptr, -4);                      \
  this->emit_ptr -= 4;                                                        \
  emit_jr(mips_reg_ra);                                                  \
  address32(this->emit_ptr, 0) = delay_instruction;                           \
  this->emit_ptr += 4;                                                        \
}                                                                             \

#define generate_swap_delay()                                                 \
{                                                                             \
  u32 delay_instruction = address32(this->emit_ptr, -8);                      \
  u32 branch_instruction = address32(this->emit_ptr, -4);                     \
  branch_instruction = (branch_instruction & 0xFFFF0000) |                    \
   (((branch_instruction & 0x0000FFFF) + 1) & 0x0000FFFF);                    \
  address32(this->emit_ptr, -8) = branch_instruction;                         \
  address32(this->emit_ptr, -4) = delay_instruction;                          \
}                                                                             \

#define generate_cycle_update()                                               \
  if(cycle_count != 0)                                                        \
  {                                                                           \
    emit_addiu(reg_cycles, reg_cycles, -cycle_count);                         \
    cycle_count = 0;                                                          \
  }                                                                           \

#define generate_cycle_update_force()                                         \
  emit_addiu(reg_cycles, reg_cycles, -cycle_count);                           \
  cycle_count = 0                                                             \

#define generate_branch_patch_conditional(dest, offset)                       \
  *((u16 *)(dest)) = mips_relative_offset(dest, offset)                       \

#define generate_branch_patch_unconditional(dest, offset)                     \
  *((u32 *)(dest)) = (mips_opcode_j << 26) |                                  \
   ((mips_absolute_offset(offset)) & 0x3FFFFFF)                               \

#define generate_branch_no_cycle_update(writeback_location, new_pc)           \
  if(pc == idle_loop_target_pc) {                                             \
    emit_load_pc(reg_a0, new_pc);                                         \
    emit_lui(reg_cycles, 0);                                                  \
    generate_function_call_swap_delay(mips_update_gba);                       \
    writeback_location = emit_j(0);                                           \
    emit_nop();                                                          \
  } else {                                                                     \
    emit_load_pc(reg_a0, new_pc);                                         \
    emit_bltzal(reg_cycles,                                              \
      mips_relative_offset(this->emit_ptr, update_trampoline));               \
    generate_swap_delay();                                                    \
    writeback_location = emit_j(0);                                   \
    emit_nop();                                                          \
  }                                                                           \

#define generate_branch_cycle_update(writeback_location, new_pc)              \
  generate_cycle_update();                                                    \
  generate_branch_no_cycle_update(writeback_location, new_pc)                 \

// a0 holds the destination

#define generate_indirect_branch_cycle_update(type)                           \
  emit_j(mips_absolute_offset(mips_indirect_branch_##type));             \
  generate_cycle_update_force()                                               \

#define generate_indirect_branch_no_cycle_update(type)                        \
  emit_j(mips_absolute_offset(mips_indirect_branch_##type));             \
  emit_nop()                                                             \


#define check_load_reg_pc(arm_reg, reg_index, pc_offset)                      \
  if(reg_index == REG_PC) {                                                   \
    reg_index = arm_reg;                                                      \
    emit_load_pc(arm_to_mips_reg[arm_reg], (pc + pc_offset));             \
  }                                                                           \

#define check_store_reg_pc_no_flags(reg_index)                                \
  if(reg_index == REG_PC) {                                                   \
    generate_indirect_branch_arm();                                           \
  }                                                                           \

#define check_store_reg_pc_flags(reg_index)                                   \
  if(reg_index == REG_PC) {                                                   \
    generate_function_call(execute_spsr_restore);                             \
    generate_indirect_branch_dual();                                          \
  }                                                                           \

#define generate_indirect_branch_arm() {                                      \
    if(condition == 0x0E) {                                                   \
      generate_indirect_branch_cycle_update(arm);                             \
    } else {                                                                  \
      generate_indirect_branch_no_cycle_update(arm);                          \
    }                                                                         \
  }                                                                           \

#define generate_indirect_branch_dual() {                                     \
    if(condition == 0x0E) {                                                   \
      generate_indirect_branch_cycle_update(dual);                            \
    } else {                                                                  \
      generate_indirect_branch_no_cycle_update(dual);                         \
    }                                                                         \
  }                                                                           \


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

#define thumb_load_pc_pool_const(rd, value)                                   \
  generate_load_imm(arm_to_mips_reg[rd], (value));                            \

#define check_store_reg_pc_thumb(_rd)                                         \
  if(_rd == REG_PC) {                                                         \
    generate_indirect_branch_cycle_update(thumb);                             \
  }                                                                           \

#define update_addi_flags(_rd, _rs, imm)                                      \
  if (it.gen_flag_v())                                                        \
    emit_nor(reg_v_cache, _rs, _rs);                                     \
  emit_addiu(_rd, _rs, imm);                                                  \
  if (it.gen_flag_c()) {                                                      \
    /* If result is smaller than imm, there was unsigned overflow! */         \
    emit_sltiu(reg_c_cache, _rd, imm);                                   \
  }                                                                           \
  update_nz_flags<SetFlags>(it, _rd);                                         \
  if (it.gen_flag_v()) {                                                      \
    emit_and(reg_v_cache, reg_v_cache, _rd);                             \
    emit_srl(reg_v_cache, reg_v_cache, 31);                              \
  }                                                                           \

// V_flag = SignRs & !SignRd = !(!SignRs | SignRd)
#define update_subi_flags(_rd, _rs, imm)                                      \
  if (it.gen_flag_c()) {                                                      \
    /* If rs is smaller than imm, will cause carry! (!borrow) */              \
    emit_sltiu(reg_c_cache, _rs, imm);                                   \
    emit_xori(reg_c_cache, reg_c_cache, 1);                              \
  }                                                                           \
  if (it.gen_flag_v())                                                        \
    emit_nor(reg_v_cache, _rs, _rs);                                     \
  emit_addiu(_rd, _rs, -imm);                                                 \
  update_nz_flags<SetFlags>(it, _rd);                                         \
  if (it.gen_flag_v()) {                                                      \
    emit_nor(reg_v_cache, reg_v_cache, _rd);                             \
    emit_srl(reg_v_cache, reg_v_cache, 31);                              \
  }

// Some macros to wrap device-specific instructions

/* MIPS32R2 and PSP support ins, ext, seb, rotr */
#ifdef MIPS_HAS_R2_INSTS
  // Inserts LSB bits into another register
  #define insert_bits(rdest, rsrc, rtemp, pos, size) \
    emit_ins(rdest, rsrc, pos, size);
  // Doubles a byte into a halfword
  #define double_byte(reg, rtmp) \
    emit_ins(reg, reg, 8, 8);
  // Clears numbits at LSB position (to align an address)
  #define emit_align_reg(reg, numbits) \
    emit_ins(reg, reg_zero, 0, numbits)
  // Extract a bitfield (pos, size) to a register
  #define extract_bits(rt, rs, pos, size) \
    emit_ext(rt, rs, pos, size)
  // Extends signed byte to u32
  #define extend_byte_signed(rd, rs) \
    emit_seb(rd, rs)
  // Rotates a word using a temp reg if necessary
  #define rotate_right(rdest, rsrc, rtemp, amount) \
    emit_rotr(rdest, rsrc, amount);
  // Same but variable amount rotation (register)
  #define rotate_right_var(rdest, rsrc, rtemp, ramount) \
    emit_rotrv(rdest, rsrc, ramount);
#else
  // Inserts LSB bits into another register
  // *assumes dest bits are cleared*!
  #define insert_bits(rdest, rsrc, rtemp, pos, size) \
    emit_sll(rtemp, rsrc, 32 - size);           \
    emit_srl(rtemp, rtemp, 32 - size - pos);    \
    emit_or(rdest, rdest, rtemp);
  // Doubles a byte into a halfword
  #define double_byte(reg, rtmp)    \
    emit_sll(rtmp, reg, 8);    \
    emit_andi(reg, reg, 0xff); \
    emit_or(reg, reg, rtmp);
  // Clears numbits at LSB position (to align an address)
  #define emit_align_reg(reg, numbits) \
    emit_srl(reg, reg, numbits); \
    emit_sll(reg, reg, numbits)
  // Extract a bitfield (pos, size) to a register
  // TODO: Optimize for the case bits are the MSB
  #define extract_bits(rt, rs, pos, size) \
    emit_sll(rt, rs, 32 - ((pos) + (size))); \
    emit_srl(rt, rt, 32 - (size))
  // Extends signed byte to u32
  #define extend_byte_signed(rd, rs) \
    emit_sll(rd, rs, 24); \
    emit_sra(rd, rd, 24)
  // Rotates a word (uses temp reg)
  #define rotate_right(rdest, rsrc, rtemp, amount) \
    emit_sll(rtemp, rsrc, 32 - (amount));     \
    emit_srl(rdest, rsrc, (amount));          \
    emit_or(rdest, rdest, rtemp)
  // Variable rotation using temp reg (dst != src)
  #define rotate_right_var(rdest, rsrc, rtemp, ramount) \
    emit_andi(rtemp, ramount, 0x1F);               \
    emit_srlv(rdest, rsrc, rtemp);                 \
    emit_subu(rtemp, reg_zero, rtemp);             \
    emit_addiu(rtemp, rtemp, 32);                       \
    emit_sllv(rtemp, rsrc, rtemp);                 \
    emit_or(rdest, rdest, rtemp)

#endif


// Register save layout as follows:
#define ReOff_RegPC    (REG_PC    * 4) // REG_PC
#define ReOff_CPSR     (REG_CPSR  * 4) // REG_CPSR
#define ReOff_SaveR1   (REG_SAVE  * 4) // 3 save scratch regs
#define ReOff_SaveR2   (REG_SAVE2 * 4)
#define ReOff_SaveR3   (REG_SAVE3 * 4)
#define ReOff_OamUpd   (OAM_UPDATED*4) // OAM_UPDATED
#define ReOff_GP_Save  (REG_SAVE5 * 4) // GP_SAVE

// Saves all regs to their right slot and loads gp
#define emit_save_regs(save_a2) {                                             \
  int i;                                                                      \
  for (i = 0; i < 15; i++)                                                    \
    emit_sw(arm_to_mips_reg[i], reg_base, 4 * i);                        \
  if (save_a2)                                                                \
    emit_sw(reg_a2, reg_base, ReOff_SaveR2);                             \
  /* Load the gp pointer, used by C code */                                   \
  emit_lw(mips_reg_gp, reg_base, ReOff_GP_Save);                         \
}

// Restores the registers from their slot
#define emit_restore_regs(restore_a2) {                                       \
  int i;                                                                      \
  if (restore_a2)                                                             \
    emit_lw(reg_a2, reg_base, ReOff_SaveR2);                             \
  for (i = 0; i < 15; i++)                                                    \
    emit_lw(arm_to_mips_reg[i], reg_base, 4 * i);                        \
}

// Emits a function call for a read or a write (for special stuff like flash)
#define emit_mem_call_ds(fnptr, mask)                                         \
  emit_sw(mips_reg_ra, reg_base, ReOff_SaveR1);                          \
  emit_save_regs(true);                                                       \
  genccall(fnptr);                                                            \
  emit_andi(reg_a0, reg_a0, (mask));                                     \
  emit_lw(mips_reg_ra, reg_base, ReOff_SaveR1);                          \
  emit_restore_regs(true);

#define emit_mem_call(fnptr, mask)      \
  emit_mem_call_ds(fnptr, mask)         \
  emit_jr(mips_reg_ra);            \
  emit_nop();

// This is a pointer table to the open load stubs, used by the BIOS (optimization)
u32* openld_core_ptrs[11];

const u8 ldopmap[6][2] = { {0, 1}, {1, 2}, {2, 4}, {4, 6}, {6, 10}, {10, 11} };
const u8 ldhldrtbl[11] = {0, 1, 2, 2, 3, 3, 4, 4, 4, 4, 5};
#define ld_phndlr_branch(memop) \
  (((u32*)&rom_translation_cache[ldhldrtbl[(memop)]*16*4]) - ((u32*)this->emit_ptr + 1))

#define st_phndlr_branch(memop) \
  (((u32*)&rom_translation_cache[((memop) + 6)*16*4]) - ((u32*)this->emit_ptr + 1))

#define branch_handlerid(phndlrid) \
  (((u32*)&rom_translation_cache[(phndlrid)*16*4]) - ((u32*)this->emit_ptr + 1))

#define branch_offset(ptr) \
  (((u32*)ptr) - ((u32*)this->emit_ptr + 1))


#ifdef PIC
  #define genccall(fn)                                         \
    emit_lui(mips_reg_t9, ((u32)fn) >> 16);               \
    emit_ori(mips_reg_t9, mips_reg_t9, ((u32)fn));        \
    emit_jalr(mips_reg_t9);
#else
  #define genccall(fn) emit_jal(((u32)fn) >> 2);
#endif

// Describes a "plain" memory are, that is, an area that is just accessed
// as normal memory (with some caveats tho).
typedef struct {
  unsigned region;      // Region ID (top 8 bits)
  unsigned memsize;     // 0 byte, 1 halfword, 2 word
  bool check_smc;       // Whether the memory can contain code
  bool bus16;           // Whether it can only be accessed at 16bit
  u32 baseptr;          // Memory base address.
  u32 baseoff;          // Offset from base_reg
} t_stub_meminfo;

typedef void (*sthldr_t)(
  unsigned memop_number, const t_stub_meminfo *meminfo,
  unsigned size, bool aligned);

typedef void (*ldhldr_t)(
  unsigned memop_number, const t_stub_meminfo *meminfo,
  bool signext, unsigned size,
  unsigned alignment, bool aligned, bool must_swap);

inline bool isimm16(u32 imm) {
  return (imm & 0xFFFF0000) == 0;
}

inline bool isimmhi16(u32 imm) {
  return (imm & 0x0000FFFF) == 0;
}

inline bool isimm16s(u32 imm) {
  s32 si = (s32)imm;
  return si >= -32768 && si  <= 32767;
}

#define SMC_WRITE_OFF    (10*16*4)   /* 10 handlers (16 insts) */
#define IOEPILOGUE_OFF   (SMC_WRITE_OFF + 4*2)   /* Trampolines are two insts */
#define EWRAM_SPM_OFF    (IOEPILOGUE_OFF + 4*2)

class CodeEmitter : public MIPSEmitter {
public:
  CodeEmitter(u8 *emit_ptr, u8 *emit_end, u32 pc)
   : MIPSEmitter(emit_ptr, emit_end), block_pc(pc) {}

  u32 block_pc;              // PC address for the block base
  u8 *update_trampoline;
  u8 *spaccess_trampoline;

  static unsigned block_prologue_size() { return 16; }  // 4 trampoline insts.

  inline void emit_block_prologue() {
    update_trampoline = this->emit_ptr;
    emit_j(mips_absolute_offset(mips_update_gba));
    emit_nop();
    spaccess_trampoline = this->emit_ptr;
    emit_j(mips_absolute_offset(&rom_translation_cache[EWRAM_SPM_OFF]));
    emit_nop();
    generate_load_imm(reg_pc, block_pc)
  }

  inline mips_regnum load_alloc_reg(u32 regn, mips_regnum tmp_reg, u32 pcvalue) {
    if (regn == REG_PC) {
      emit_load_pc(tmp_reg, pcvalue);
      return tmp_reg;
    }
    return arm_to_mips_reg[regn];
  }

  inline mips_regnum store_alloc_reg(u32 regn, mips_regnum tmp_reg) {
    if (regn == REG_PC)
      return tmp_reg;
    return arm_to_mips_reg[regn];
  }

  // Forces a register load!
  inline void force_load_reg(mips_regnum outreg, u32 regn, u32 pcvalue) {
    if (regn == REG_PC)
      emit_load_pc(outreg, pcvalue);
    else
      emit_addu(outreg, arm_to_mips_reg[regn], reg_zero);
  }

  // Aux functions used to emit certain common sequences
  inline void emit_load_imm_reg(mips_regnum regn, u32 imm) {
    if (isimm16(imm))
      emit_ori(regn, reg_zero, imm);    // Loads 0x0000XXXX
    else if (isimm16s(imm))
      emit_addiu(regn, reg_zero, imm);  // Loads 0xFFFF8000 ... 00007FFF
    else if (isimmhi16(imm))
      emit_lui(regn, imm >> 16);        // Loads 0xXXXX0000
    else {
      emit_lui(regn, imm >> 16);
      emit_ori(regn, regn, imm);
    }
  }

  inline void emit_load_pc(mips_regnum reg, u32 pc) {
    s32 pc_delta = pc - this->block_pc;
    if ((pc_delta >= -32768) && (pc_delta <= 32767))
      emit_addiu(reg, reg_pc, pc_delta);
    else
      emit_load_imm_reg(reg, pc);
  }

  template <FlagOperation flgmode>
  inline void update_nz_flags(const BaseInst & it, mips_regnum reg) {
    if (flgmode == SetFlags) {
      if (it.gen_flag_n())
        emit_srl(reg_n_cache, reg, 31);
      if (it.gen_flag_z())
        emit_sltiu(reg_z_cache, reg, 1);
    }
  }

  template <FlagOperation flg>
  inline void generate_sbc(const BaseInst & it, mips_regnum rd, mips_regnum rn, mips_regnum rm) {
    emit_xori(reg_temp, reg_c_cache, 1);     // Borrow flag is inverted
    if (flg == SetFlags) {
      if (it.gen_flag_c()) {
        emit_sltu(reg_c_cache, rm, rn);
        emit_sltu(reg_rv, rn, rm);
        emit_xori(reg_rv, reg_rv, 1);
        emit_movz(reg_c_cache, reg_rv, reg_temp);
      }
      if (it.gen_flag_v()) {
        emit_xor(reg_v_cache, rn, rm);
        emit_nor(reg_rv, rm, reg_zero);
      }
    }
    emit_subu(rd, rn, rm);
    emit_subu(rd, rd, reg_temp);
    if (flg == SetFlags && it.gen_flag_v()) {
      emit_xor(reg_rv, reg_rv, rd);
      emit_and(reg_v_cache, reg_v_cache, reg_rv);
      emit_srl(reg_v_cache, reg_v_cache, 31);
    }
    update_nz_flags<flg>(it, rd);
  }

  inline void generate_adcs(const BaseInst & it, mips_regnum rd, mips_regnum rn, mips_regnum rm) {
    if (it.gen_flag_v()) {
      emit_xor(reg_v_cache, rn, rm);
      emit_nor(reg_v_cache, reg_v_cache, reg_zero);
      emit_addu(reg_rv, rn, reg_zero);
    }
    emit_addu(reg_a2, rn, rm);
    if (it.gen_flag_c())
      emit_sltu(reg_temp, reg_a2, rm);
    emit_addu(rd, reg_a2, reg_c_cache);
    if (it.gen_flag_v()) {
      emit_xor(reg_rv, reg_rv, rd);
      emit_and(reg_v_cache, reg_rv, reg_v_cache);
      emit_srl(reg_v_cache, reg_v_cache, 31);
    }
    if (it.gen_flag_c()) {
      emit_sltu(reg_c_cache, rd, reg_c_cache);
      emit_or(reg_c_cache, reg_temp, reg_c_cache);
    }
    update_nz_flags<SetFlags>(it, rd);
  }

  inline void generate_adds(const BaseInst & it, mips_regnum rd, mips_regnum rn, mips_regnum rm) {
    if (it.gen_flag_c() | it.gen_flag_v())
      emit_addu(reg_c_cache, rn, reg_zero);
    if (it.gen_flag_v())
      emit_slt(reg_v_cache, rm, reg_zero);
    emit_addu(rd, rn, rm);
    if (it.gen_flag_v()) {
      emit_slt(reg_a0, rd, reg_c_cache);
      emit_xor(reg_v_cache, reg_v_cache, reg_a0);
    }
    if (it.gen_flag_c())
      emit_sltu(reg_c_cache, rd, reg_c_cache);
    update_nz_flags<SetFlags>(it, rd);
  }

  inline void generate_subs(const BaseInst & it, mips_regnum rd, mips_regnum rn, mips_regnum rm) {
    if (it.gen_flag_c()) {
      emit_sltu(reg_c_cache, rn, rm);
      emit_xori(reg_c_cache, reg_c_cache, 1);
    }
    if (it.gen_flag_v())
      emit_slt(reg_v_cache, rn, rm);
    emit_subu(rd, rn, rm);
    update_nz_flags<SetFlags>(it, rd);
    if (it.gen_flag_v()) {
      if (!it.gen_flag_n())
        emit_srl(reg_n_cache, rd, 31);
      emit_xor(reg_v_cache, reg_v_cache, reg_n_cache);
    }
  }

  inline void generate_negs(const BaseInst & it, mips_regnum rd, mips_regnum rs) {
    if (it.gen_flag_v())
      emit_slt(reg_v_cache, mips_reg_zero, rs);
    emit_subu(rd, mips_reg_zero, rs);
    if (it.gen_flag_z())
      emit_sltiu(reg_z_cache, rd, 1);
    if (it.gen_flag_n() | it.gen_flag_v())
      emit_srl(reg_n_cache, rd, 31);
    if (it.gen_flag_c())
      emit_sltiu(reg_c_cache, rd, 1);  // C is 1 only when rs (or rd) are zero.
    if (it.gen_flag_v()) {
      emit_srl(reg_n_cache, rd, 31);
      emit_xor(reg_v_cache, reg_v_cache, reg_n_cache);
    }
  }

  template <CPUInstMode cm>
  inline void generate_translation_gate(u32 pc) {
    emit_load_pc(reg_a0, pc);
    if (cm == ModeARM)
      emit_j(mips_absolute_offset(mips_indirect_branch_arm));
    else
      emit_j(mips_absolute_offset(mips_indirect_branch_thumb));
    emit_nop();
  }

  inline void emit_cycle_update(u32 & cycle_count) {
    generate_cycle_update();
  }

  template <CPUInstMode cm>
  inline void emit_cheat_hook() {
    generate_function_call(mips_cheat_hook);
  }

  inline void emit_load_const_pool(u32 regn, u32 value) {
    generate_load_imm(arm_to_mips_reg[regn], (value));
  }

  inline void arm_conditional_block_header(u32 condition, u32 & cycle_count, u8 * & backpatch_address) {
    // TODO: Fix cycle generation
    backpatch_address = emit_opp_condbranch((ARMCondCode)condition, cycle_count);  // TODO: use ARMCondCode as type natively
  }

  // Condition code generation
  inline u8 *emit_opp_condbranch(ARMCondCode ccode, u32 & cycle_count) {
    // TODO Take reg num as input.
    // TODO We emit cycle updating in the dedlay slot, not ideal (vs other archs)

    // We emit a branch that branches on the opposite condition.
    // Returns the patching address (so the branch offset can be filled)
    u8 *ret = NULL;

    switch (ccode) {
    case CondEQ:
      ret = emit_beq(reg_z_cache, reg_zero, 0);
      generate_cycle_update_force();
      break;
    case CondNE:
      ret = emit_bne(reg_z_cache, reg_zero, 0);
      generate_cycle_update_force();
      break;
    case CondCS:
      ret = emit_beq(reg_c_cache, reg_zero, 0);
      generate_cycle_update_force();
      break;
    case CondCC:
      ret = emit_bne(reg_c_cache, reg_zero, 0);
      generate_cycle_update_force();
      break;
    case CondMI:
      ret = emit_beq(reg_n_cache, reg_zero, 0);
      generate_cycle_update_force();
      break;
    case CondPL:
      ret = emit_bne(reg_n_cache, reg_zero, 0);
      generate_cycle_update_force();
      break;
    case CondVS:
      ret = emit_beq(reg_v_cache, reg_zero, 0);
      generate_cycle_update_force();
      break;
    case CondVC:
      ret = emit_bne(reg_v_cache, reg_zero, 0);
      generate_cycle_update_force();
      break;
    case CondHI:
      emit_xori(reg_temp, reg_c_cache, 1);
      emit_or(reg_temp, reg_temp, reg_z_cache);
      ret = emit_bne(reg_temp, reg_zero, 0);
      generate_cycle_update_force();
      break;
    case CondLS:
      emit_xori(reg_temp, reg_c_cache, 1);
      emit_or(reg_temp, reg_temp, reg_z_cache);
      ret = emit_beq(reg_temp, reg_zero, 0);
      generate_cycle_update_force();
      break;
    case CondGE:
      ret = emit_bne(reg_n_cache, reg_v_cache, 0);
      generate_cycle_update_force();
      break;
    case CondLT:
      ret = emit_beq(reg_n_cache, reg_v_cache, 0);
      generate_cycle_update_force();
      break;
    case CondGT:
      emit_xor(reg_temp, reg_n_cache, reg_v_cache);
      emit_or(reg_temp, reg_temp, reg_z_cache);
      ret = emit_bne(reg_temp, reg_zero, 0);
      generate_cycle_update_force();
      break;
    case CondLE:
      emit_xor(reg_temp, reg_n_cache, reg_v_cache);
      emit_or(reg_temp, reg_temp, reg_z_cache);
      ret = emit_beq(reg_temp, reg_zero, 0);
      generate_cycle_update_force();
      break;
    };

    return ret;
  }


  template <ARMOp aluop>
  inline void thumb_aluop3(const ThumbInst & it) {
    const mips_regnum rs = arm_to_mips_reg[it.rs()];
    const mips_regnum rn = arm_to_mips_reg[it.rn()];
    const mips_regnum rd = arm_to_mips_reg[it.rd()];

    switch (aluop) {
    case OpAdd:
      generate_adds(it, rd, rs, rn);
      break;
    case OpSub:
      generate_subs(it, rd, rs, rn);
      break;
    };
  }

  template <ARMOp aluop>
  inline void thumb_aluop2(const ThumbInst & it) {
    const mips_regnum rs = arm_to_mips_reg[it.rs()];
    const mips_regnum rd = arm_to_mips_reg[it.rd()];

    switch (aluop) {
    case OpOrr:
      emit_or(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpAnd:
      emit_and(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpXor:
      emit_xor(rd, rd, rs);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpBic:
      emit_nor(reg_temp, rs, reg_zero);
      emit_and(rd, rd, reg_temp);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpMul:
      emit_multu(rd, rs);
      emit_mflo(rd);
      update_nz_flags<SetFlags>(it, rd);
      break;
    case OpAdd:
      generate_adds(it, rd, rs, rd);
      break;
    case OpSub:
      generate_subs(it, rd, rs, rd);
      break;
    case OpAdc:
      generate_adcs(it, rd, rs, rd);
      break;
    case OpSbc:
      generate_sbc<SetFlags>(it, rd, rd, rs);
      break;
    };
  }

  template <OpType stype, ShiftType st>
  inline void thumb_shft(const ThumbInst & it) {
    const mips_regnum rd = arm_to_mips_reg[it.rd()];

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

  template <ARMOp aluop>
  inline void thumb_aluop1(const ThumbInst & it) {
    const mips_regnum rs = arm_to_mips_reg[it.rs()];
    const mips_regnum rd = arm_to_mips_reg[it.rd()];

    switch (aluop) {
    case OpNeg:
      generate_negs(it, rd, rs);
      break;
    case OpMvn:
      emit_nor(rd, rs, reg_zero);
      update_nz_flags<SetFlags>(it, rd);
      break;
    };
  }

  template <ARMOp testop>
  inline void thumb_testop(const ThumbInst & it) {
    const mips_regnum rs = arm_to_mips_reg[it.rs()];
    const mips_regnum rd = arm_to_mips_reg[it.rd()];

    switch (testop) {
    case OpTst:
      emit_and(reg_temp, rs, rd);
      update_nz_flags<SetFlags>(it, reg_temp);
      break;
    case OpCmp:
      generate_subs(it, reg_temp, rd, rs);
      break;
    case OpCmn:
      generate_adds(it, reg_temp, rs, rd);
      break;
    };
  }


  template <ARMOp aluop>
  inline void thumb_aluimm2(const ThumbInst & it) {
    const mips_regnum rd = arm_to_mips_reg[it.rd8()];

    switch (aluop) {
    case OpMov:
      emit_addiu(rd, reg_zero, it.imm8());
      emit_addiu(reg_n_cache, reg_zero, 0);
      emit_addiu(reg_z_cache, reg_zero, it.imm8() ? 0 : 1);
      break;
    case OpAdd:
      update_addi_flags(rd, rd, it.imm8());
      break;
    case OpSub:
      update_subi_flags(rd, rd, it.imm8());
      break;
    case OpCmp:
      update_subi_flags(reg_temp, rd, it.imm8());
      break;
    };
  }

  template <ARMOp aluop>
  inline void thumb_aluimm3(const ThumbInst & it) {
    const mips_regnum rs = arm_to_mips_reg[it.rs()];
    const mips_regnum rd = arm_to_mips_reg[it.rd()];

    switch (aluop) {
    case OpAdd:
      update_addi_flags(rd, rs, it.imm3());
      break;
    case OpSub:
      update_subi_flags(rd, rs, it.imm3());
      break;
    };
  }

  template <ARMOp aluop>
  inline void thumb_aluhi(const ThumbInst & it, u32 & cycle_count) {
    const mips_regnum rs = load_alloc_reg(it.rs_hi(), reg_a1, it.pc + 4);

    // TODO Improve and make PC writes clearer!
    if (aluop == OpAdd) {
      mips_regnum rd = load_alloc_reg(it.rd_hi(), reg_a0, it.pc + 4);
      emit_addu(rd, rd, rs);
      check_store_reg_pc_thumb(it.rd_hi());
    } else if (aluop == OpCmp) {
      mips_regnum rd = load_alloc_reg(it.rd_hi(), reg_a0, it.pc + 4);
      generate_subs(it, reg_temp, rd, rs);
    } else if (aluop == OpMov) {
      mips_regnum rd = store_alloc_reg(it.rd_hi(), reg_a0);
      emit_addu(rd, rs, reg_zero);
      check_store_reg_pc_thumb(it.rd_hi());
    }
  }

  template <u32 ref_reg>
  inline void thumb_regoff(const ThumbInst & it) {
    if (ref_reg == REG_PC)
      emit_load_pc(arm_to_mips_reg[it.rd8()], (it.pc & ~2) + 4 + 4 * it.imm8());
    else
      emit_addiu(arm_to_mips_reg[it.rd8()], arm_to_mips_reg[ref_reg], 4 * it.imm8());
  }

  inline void thumb_spadj(s8 offset) {
    emit_addiu(reg_r13, reg_r13, (offset * 4));
  }

  inline void thumb_bx(u32 pc, u32 regn, u32 & cycle_count) {
    force_load_reg(reg_a0, regn, pc + 4);
    generate_indirect_branch_cycle_update(dual);
  }

  inline void arm_bx(const ARMInst & it, u32 & cycle_count) {
    const u8 condition = it.cond();        // TODO remove this
    force_load_reg(reg_a0, it.rm(), it.pc + 8);
    generate_indirect_branch_dual();
  }

  inline bool thumb_emu_swi(u32 pc, u32 num, u32 & cycle_count) {
    switch (num) {
    case 6:
    case 7:
      {
        mips_regnum regA = (num == 6) ? reg_r0 : reg_r1;
        mips_regnum regB = (num == 6) ? reg_r1 : reg_r0;

        emit_div(regA, regB);
        emit_mflo(reg_r0);
        emit_mfhi(reg_r1);
        emit_sra(reg_a0, reg_r0, 31);
        emit_xor(reg_r3, reg_r0, reg_a0);
        emit_subu(reg_r3, reg_r3, reg_a0);
      }
      cycle_count += 64;    // Big under-estimation here
      return true;
    default:
      return false;
    };
    return false;
  }

  inline bool arm_emu_swi(u32 pc, u32 num, u32 & cycle_count) {
    return thumb_emu_swi(pc, num, cycle_count);
  }

  inline u8* thumb_swi(u32 pc, u32 & cycle_count) {
    u8 *brtgt = NULL;

    emit_load_pc(reg_a0, (pc + 2));
    generate_function_call_swap_delay(execute_swi);
    generate_branch_cycle_update(brtgt, 0x00000008);

    return brtgt;
  }

  inline u8* arm_swi(u32 pc, u32 & cycle_count) {
    u8 *brtgt = NULL;

    emit_load_pc(reg_a0, pc + 4);
    generate_function_call_swap_delay(execute_swi);
    generate_branch_cycle_update(brtgt, 0x00000008);

    return brtgt;
  }

  template <ARMCondCode ccode>
  inline u8* thumb_brcond(u32 pc, u32 target, u32 & cycle_count) {
    u8 *brtgt = NULL;

    u8 *ptch = emit_opp_condbranch(ccode, cycle_count);
    generate_branch_no_cycle_update(brtgt, target);
    generate_branch_patch_conditional(ptch, this->emit_ptr);
    return brtgt;
  }

  inline u8* thumb_b(u32 pc, u32 target, u32 & cycle_count) {
    u8 *brtgt = NULL;
    generate_branch_cycle_update(brtgt, target);
    return brtgt;
  }

  inline u8* arm_b(const ARMInst & it, u32 target, u32 & cycle_count) {
    const u32 pc = it.pc;  // TODO: Remove this
    u8 *brtgt = NULL;
    if (it.cond() == CondAL) {
      generate_branch_cycle_update(brtgt, target);
    } else {
      generate_branch_no_cycle_update(brtgt, target);
    }
    return brtgt;
  }

  inline u8* thumb_bl(u32 pc, u32 target, u32 & cycle_count) {
    u8 *brtgt = NULL;

    emit_load_pc(reg_r14, ((pc + 2) | 0x01));
    generate_branch_cycle_update(brtgt, target);
    return brtgt;
  }

  inline u8* arm_bl(const ARMInst & it, u32 target, u32 & cycle_count) {
    const u32 pc = it.pc;  // TODO: Remove this
    u8 *brtgt = NULL;
    emit_load_pc(reg_r14, ((pc + 4)));
    if (it.cond() == CondAL) {
      generate_branch_cycle_update(brtgt, target);
    } else {
      generate_branch_no_cycle_update(brtgt, target);
    }
    return brtgt;
  }

  inline void thumb_blh(u32 pc, u32 offset, u32 & cycle_count) {
    emit_addiu(reg_a0, reg_r14, offset);
    emit_load_pc(reg_r14, ((pc + 2) | 0x01));
    generate_indirect_branch_cycle_update(thumb);
  }

  // ============= Memory functions =================
  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memaddr(const ThumbInst & it, u32 regn) {
    // Generate the memory address to a0
    switch (offt) {
    case OffPC:
      // PC-relative offset. It is word aligned.
      emit_load_pc(reg_a0, ((it.pc & (~3U)) + it.imm8() * 4 + 4));
      break;

    // rb/ro/regn are never PC in thumb mode (this is handled by OffPC mode)
    case OffReg:
      emit_addu(reg_a0, arm_to_mips_reg[regn], arm_to_mips_reg[it.ro()]);
      break;
    case OffImm5:
      emit_addiu(reg_a0, arm_to_mips_reg[regn], it.imm5() * sizeof(memtype));
      break;
    case OffImm8:
      emit_addiu(reg_a0, arm_to_mips_reg[regn], it.imm8() * sizeof(memtype));
      break;
    }
  }

  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memld(const ThumbInst & it, u32 regd, u32 regn, u32 & cycle_count) {
    cycle_count += 2;  // TODO: Use proper cycle accounting and honor WAITCNT
    // Generate the address
    thumb_memaddr<memtype, offt>(it, regn);
    // Generate call to handler, store the result in the rd() register
    emit_load_pc(reg_a1, it.pc);
    generate_function_call_swap_delay(call_ldr_handler<memtype>());
    generate_store_reg(reg_rv, regd);
  }

  template <typename memtype, ThumbMemOffset offt>
  inline void thumb_memst(const ThumbInst & it, u32 regd, u32 regn, u32 & cycle_count) {
    cycle_count++;  // TODO: Use proper cycle accounting and honor WAITCNT
    // Generate the address
    thumb_memaddr<memtype, offt>(it, regn);
    // Load value and generate call to handler
    generate_load_reg(reg_a1, regd);
    emit_load_pc(reg_a2, (it.pc + 2));
    generate_function_call_swap_delay(call_str_handler<memtype>());
  }

  template <ARMMemOffset offt, MemOffDir dir>
  inline void arm_memaddr(mips_regnum oreg, const ARMInst & it) {
    // Load base register if needed
    mips_regnum breg = load_alloc_reg(it.rn(), oreg, it.pc + 8);

    switch (offt) {
    case OffImm12:     // [rn +/- imm12]
      if (dir == OffPositive)
        emit_addiu(oreg, breg, it.off12());
      else
        emit_addiu(oreg, breg, -it.off12());
      break;
    case OffHImm8:     // [rn +/- imm8]
      if (dir == OffPositive)
        emit_addiu(oreg, breg, it.off8());
      else
        emit_addiu(oreg, breg, -it.off8());
      break;
    case OffHReg:      // [rn +/- rm]
      {
        mips_regnum secreg = load_alloc_reg(it.rm(), reg_temp, it.pc + 8);
        if (dir == OffPositive)
          emit_addu(oreg, breg, secreg);
        else
          emit_subu(oreg, breg, secreg);
      }
      break;
    case OffOp2Reg:    // [rn +/- rm shift/rot amount]
      emit_op2_shimm<NoFlags>(reg_rv, it.rm(), (ShiftType)it.op2smode(), it.op2sa(), it.pc + 8);
      if (dir == OffPositive)
        emit_addu(oreg, breg, reg_rv);
      else
        emit_subu(oreg, breg, reg_rv);
      break;
    };
  }

  template <typename memtype, ARMMemOffset offt, MemOffDir dir, MemIdxMode idxm>
  inline void arm_memst(const ARMInst & it, u32 & cycle_count) {
    cycle_count++;    // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the final address and base address, and write back if necessary
    if (idxm == MemIdxPostWB) {
      // Load the base reg to a0
      force_load_reg(reg_a0, it.rn(), it.pc + 4);
      // Calculate the final value to the final reg.
      mips_regnum wbreg = store_alloc_reg(it.rn(), reg_a2);
      arm_memaddr<offt, dir>(wbreg, it);
    }
    else {
      arm_memaddr<offt, dir>(reg_a0, it);  // Calculate final addr to a0
      if (idxm == MemIdxPreWB) {
        generate_store_reg(reg_a0, it.rn());
      }
    }

    // Generate call to handler, load the value to write to a1
    force_load_reg(reg_a1, it.rd(), it.pc + 12);
    emit_load_pc(reg_a2, (it.pc + 4));
    generate_function_call_swap_delay(call_str_handler<memtype>());
  }

  template <typename memtype, ARMMemOffset offt, MemOffDir dir, MemIdxMode idxm>
  inline void arm_memld(const ARMInst & it, u32 & cycle_count) {
    const u8 condition = it.cond();        // TODO remove this
    cycle_count += 2;    // TODO: Use proper cycle accounting and honor WAITCNT

    // Generate the final address and base address, and write back if necessary
    if (idxm == MemIdxPostWB) {
      // Load the base reg to a0
      force_load_reg(reg_a0, it.rn(), it.pc + 4);
      // Calculate the final value to the final reg.
      mips_regnum wbreg = store_alloc_reg(it.rn(), reg_a2);
      arm_memaddr<offt, dir>(wbreg, it);
    }
    else {
      arm_memaddr<offt, dir>(reg_a0, it);  // Calculate final addr to a0
      if (idxm == MemIdxPreWB) {
        generate_store_reg(reg_a0, it.rn());
      }
    }

    // Generate call to handler, load the value to write to a1
    emit_load_pc(reg_a1, it.pc);
    generate_function_call_swap_delay(call_ldr_handler<memtype>());
    generate_store_reg(reg_rv, it.rd());

    check_store_reg_pc_no_flags(it.rd());
  }

  template <typename memtype>
  inline void arm_swap(const ARMInst & it, u32 & cycle_count) {
    cycle_count += 3;   // TODO: Some more accurate accounting :)

    // rd = mem[rn], mem[rn] = rm (Note: all regs could be the same!)

    force_load_reg(reg_a0, it.rn(), it.pc + 4);
    emit_load_pc(reg_a1, it.pc);
    generate_function_call_swap_delay(call_ldr_handler<memtype>());

    generate_mov(reg_temp, reg_rv);
    force_load_reg(reg_a0, it.rn(), it.pc + 4);
    force_load_reg(reg_a1, it.rm(), it.pc + 4);
    generate_store_reg(reg_temp, it.rd());
    emit_load_pc(reg_a2, (it.pc + 4));
    generate_function_call_swap_delay(call_str_handler<memtype>());
  }

  template <CPUInstMode cpum, AccMode amode, AddrMode addrmode, bool writeback, bool sbit>
  inline void mem_multi(u32 pc, u32 condition, u32 basereg, u16 rlist, u32 & cycle_count) {
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
    emit_addiu(reg_a2, arm_to_mips_reg[basereg], 0);     // TODO: Improve using one less move?
    emit_align_reg(reg_a2, 2);
    // TODO: Implement SP-relative accessing? TODO

    // If base is in the reglist and writeback is enabled, the value of the
    // written register depends on the write cycle (ARM7TDM manual 4.11.6).
    // If the register is the first, the written value is the original value,
    // otherwise the update base register is written. For LDM loaded data
    // takes always precendence.
    bool wrbck_base = (1 << basereg) & rlist;
    bool base_first = (((1 << basereg) - 1) & rlist) == 0;
    bool writeback_first = (amode == AccLoad) || !(wrbck_base && base_first);

    // This is the most common case by far.
    if (writeback && writeback_first)
      emit_addiu(arm_to_mips_reg[basereg], arm_to_mips_reg[basereg], endoff);

    u32 aoff = 0;
    for (u32 i = 0; i < 16; i++) {
      if (rlist & (1 << i)) {
        emit_addiu(reg_a0, reg_a2, (aoff + inioff));
        if (amode == AccLoad) {
          generate_function_call_swap_delay(execute_aligned_load32);
          generate_store_reg(reg_rv, i);
        } else {
          force_load_reg(reg_a1, i, pc + 2*itsize);

          // Update the base register right after the first read if necessary
          if (writeback && !writeback_first) {
            emit_addiu(arm_to_mips_reg[basereg], arm_to_mips_reg[basereg], endoff);
            writeback_first = true;
          }

          if (rlist >> (i + 1)) {
            generate_function_call_swap_delay(execute_aligned_store32);
          } else {
            // Only the last store can produce side-effects
            // TODO: Evaluate if this is enough or we should improve it.
            emit_load_pc(reg_a2, (pc + itsize));
            generate_function_call_swap_delay(execute_store_u32);
          }
        }
        aoff += 4;
      }
    }

    // Load PC requires an indirect branch
    if (amode == AccLoad && (rlist & (1 << REG_PC))) {
      // Move ret load value to arg0
      generate_mov(reg_a0, reg_rv);

      if (cpum == ModeARM) {
        generate_indirect_branch_arm();
      } else {
        generate_indirect_branch_cycle_update(thumb);
      }
    }
  }


  // ======== ARM instructions ======================================
  template <ARMOp aluop, FlagOperation flg>
  inline void arm_aluimm3(const ARMInst & it, u32 & cycle_count) {
    mips_regnum rn = load_alloc_reg(it.rn(), reg_a1, it.pc + 8);
    mips_regnum rd = store_alloc_reg(it.rd(), reg_a0);

    // Immediate is a 8 bit rotated immediate
    u32 sa = it.rot4() * 2;   // TODO remove this absurd scaling here
    u32 imm = rotr32(it.imm8(), sa);

    // Set/Clear carry flag if appropriate (rotation result)
    if (aluop == OpAnd || aluop == OpOrr || aluop == OpXor || aluop == OpBic) {
      if (flg == SetFlags && it.rot4() != 0 && it.gen_flag_c())
        emit_addiu(reg_c_cache, reg_zero, ((imm) >> 31));
    }

    // TODO: Implement add/sub with flags in a more efficient way
    // for small immediates.
    switch (aluop) {
    case OpBic:
      imm = ~imm;
      /* fallthrough */
    case OpAnd:
      if (isimm16(imm))
        emit_andi(rd, rn, imm);
      else {
        emit_load_imm_reg(reg_temp, imm);
        emit_and(rd, rn, reg_temp);
      }
      update_nz_flags<flg>(it, rd);
      break;
    case OpOrr:
      if (isimm16(imm))
        emit_ori(rd, rn, imm);
      else {
        emit_load_imm_reg(reg_temp, imm);
        emit_or(rd, rn, reg_temp);
      }
      update_nz_flags<flg>(it, rd);
      break;
    case OpXor:
      if (isimm16(imm))
        emit_xori(rd, rn, imm);
      else {
        emit_load_imm_reg(reg_temp, imm);
        emit_xor(rd, rn, reg_temp);
      }
      update_nz_flags<flg>(it, rd);
      break;
    case OpAdd:
      if (flg == NoFlags) {
        if (isimm16s(imm))
          emit_addiu(rd, rn, imm);
        else {
          emit_load_imm_reg(reg_temp, imm);
          emit_addu(rd, rn, reg_temp);
        }
      } else {
        emit_load_imm_reg(reg_temp, imm);
        generate_adds(it, rd, rn, reg_temp);
      }
      break;
    case OpAdc:
      if (flg == NoFlags) {
        if (isimm16s(imm)) {
          emit_addiu(rd, rn, imm);
          emit_addu(rd, rd, reg_c_cache);
        } else {
          emit_load_imm_reg(reg_temp, imm);
          emit_addu(rd, rn, reg_temp);
          emit_addu(rd, rd, reg_c_cache);
        }
      } else {
        emit_load_imm_reg(reg_temp, imm);
        generate_adcs(it, rd, rn, reg_temp);
      }
      break;
    case OpSub:
      if (flg == NoFlags) {
        if (isimm16s(-imm))
          emit_addiu(rd, rn, -imm);
        else {
          emit_load_imm_reg(reg_temp, imm);
          emit_subu(rd, rn, reg_temp);
        }
      } else {
        emit_load_imm_reg(reg_temp, imm);
        generate_subs(it, rd, rn, reg_temp);
      }
      break;
    case OpRsb:
      emit_load_imm_reg(reg_temp, imm);
      if (flg == NoFlags)
        emit_subu(rd, reg_temp, rn);
      else
        generate_subs(it, rd, reg_temp, rn);
      break;
    case OpSbc:
      emit_load_imm_reg(reg_a2, imm);
      generate_sbc<flg>(it, rd, rn, reg_a2);
      break;
    case OpRsc:
      emit_load_imm_reg(reg_a2, imm);
      generate_sbc<flg>(it, rd, reg_a2, rn);
      break;
    };

    const u8 condition = it.cond();        // TODO remove this
    if (flg == NoFlags) {
      check_store_reg_pc_no_flags(it.rd());
    } else {
      check_store_reg_pc_flags(it.rd());
    }
  }

  template <ARMOp aluop>
  inline void arm_aluimm2(const ARMInst & it, u32 & cycle_count) {
    mips_regnum rn = load_alloc_reg(it.rn(), reg_a1, it.pc + 8);

    // Immediate is a 8 bit rotated immediate
    const u32 sa = it.rot4() * 2;   // TODO remove this absurd scaling here
    const u32 imm = rotr32(it.imm8(), sa);

    // Set/Clear carry flag if appropriate (rotation result)
    if (it.rot4() != 0 && it.gen_flag_c())
      emit_addiu(reg_c_cache, reg_zero, ((imm) >> 31));

    switch (aluop) {
    case OpTst:
      if (isimm16(imm))
        emit_andi(reg_temp, rn, imm);
      else {
        emit_load_imm_reg(reg_temp, imm);
        emit_and(reg_temp, rn, reg_temp);
      }
      update_nz_flags<SetFlags>(it, reg_temp);
      break;
    case OpTeq:
      if (isimm16(imm))
        emit_xori(reg_temp, rn, imm);
      else {
        emit_load_imm_reg(reg_temp, imm);
        emit_xor(reg_temp, rn, reg_temp);
      }
      update_nz_flags<SetFlags>(it, reg_temp);
      break;
    case OpCmp:
      emit_load_imm_reg(reg_temp, imm);
      generate_subs(it, reg_temp, rn, reg_temp);
      break;
    case OpCmn:
      emit_load_imm_reg(reg_temp, imm);
      generate_adds(it, reg_temp, rn, reg_temp);
      break;
    };
  }

  template <ARMOp aluop, FlagOperation flg>
  inline void arm_aluimm1(const ARMInst & it, u32 & cycle_count) {
    mips_regnum rd = store_alloc_reg(it.rd(), reg_a0);

    // Immediate is a 8 bit rotated immediate
    const u32 sa = it.rot4() * 2;   // TODO remove this absurd scaling here
    const u32 imm = rotr32(it.imm8(), sa);
    const u32 movimm = (aluop == OpMvn) ? ~imm : imm;

    // Set/Clear carry flag if appropriate (rotation result)
    if (flg == SetFlags && it.rot4() != 0 && it.gen_flag_c())
      emit_addiu(reg_c_cache, reg_zero, ((imm) >> 31));

    emit_load_imm_reg(rd, movimm);
    update_nz_flags<flg>(it, rd);

    const u8 condition = it.cond();        // TODO remove this
    if (flg == NoFlags) {
      check_store_reg_pc_no_flags(it.rd());
    } else {
      check_store_reg_pc_flags(it.rd());
    }
  }


  // Calculates operand 2 when register is shifted/rotated by an immediate.
  template<FlagOperation flg>
  inline void emit_op2_shimm(mips_regnum dreg, u32 sreg, ShiftType st, u32 sa, u32 pc) {
    mips_regnum rm;

    switch (st) {
    case ShiftLSL:
      rm = load_alloc_reg(sreg, dreg, pc);
      if (flg == SetFlags && sa) {
        extract_bits(reg_c_cache, rm, (32 - sa), 1);
      }
      emit_sll(dreg, rm, sa);
      break;

    case ShiftLSR:      /* (sa 0 means shift by 32) */
      if (sa) {
        rm = load_alloc_reg(sreg, dreg, pc);
        if (flg == SetFlags) {
          extract_bits(reg_c_cache, rm, (sa - 1), 1);
        }
        emit_srl(dreg, rm, sa);
      } else {
        if (flg == SetFlags) {
          rm = load_alloc_reg(sreg, dreg, pc);
          emit_srl(reg_c_cache, rm, 31);
        }
        // TODO: Can we just return reg_zero and save an inst?
        emit_addu(dreg, reg_zero, reg_zero);
      }
      break;

    case ShiftASR:      /* (sa 0 is also shift by 32) */
      rm = load_alloc_reg(sreg, dreg, pc);
      if (flg == SetFlags) {
        extract_bits(reg_c_cache, rm, ((sa ? sa : 32) - 1), 1);
      }
      emit_sra(dreg, rm, (sa ? sa : 31));
      break;

    case ShiftROR:
      rm = load_alloc_reg(sreg, reg_a1, pc);
      if (sa) {
        rotate_right(dreg, rm, reg_temp, sa);
        if (flg == SetFlags)
          emit_srl(reg_c_cache, dreg, 31);  // CF is just the MSB bit
      } else {   /* RRX */
        emit_sll(reg_temp, reg_c_cache, 31);
        if (flg == SetFlags)
          emit_andi(reg_c_cache, rm, 1);
        emit_srl(dreg, rm, 1);
        emit_or(dreg, dreg, reg_temp);
      }
      break;
    };
  }

  // Calculates operand 2 when register is shifted/rotated by another register.
  template<FlagOperation flg>
  inline void emit_op2_shreg(mips_regnum dreg, u32 sreg, u32 areg, ShiftType st, u32 pc) {
    // Loads the LSB byte only!
    if (areg == REG_PC)
      emit_addiu(reg_a1, reg_zero, (pc & 0xFF));
    else
      emit_andi(reg_a1, arm_to_mips_reg[areg], 0xFF);

    if (flg == SetFlags) {
      switch (st) {
        case ShiftLSL:
          force_load_reg(dreg, sreg, pc);
          /* Skip it all on imm = 0 */
          emit_beq(reg_a1, reg_zero, 7);
          generate_swap_delay();
          emit_addiu(reg_temp, reg_a1, -1);
          emit_sllv(dreg, dreg, reg_temp);
          emit_srl(reg_c_cache, dreg, 31);
          emit_sltiu(reg_temp, reg_a1, 33);
          emit_sll(dreg, dreg, 1);
          /* Result and flag to be zero if shift is >32 */
          emit_movz(reg_c_cache, reg_zero, reg_temp);
          emit_movz(dreg, reg_zero, reg_temp);
          break;
        case ShiftLSR:
          force_load_reg(dreg, sreg, pc);
          emit_beq(reg_a1, reg_zero, 7);  // Skip it all on shift = 0
          generate_swap_delay();
          emit_addiu(reg_temp, reg_a1, -1);
          emit_srlv(dreg, dreg, reg_temp);
          emit_andi(reg_c_cache, dreg, 1);
          emit_sltiu(reg_temp, reg_a1, 33);
          emit_srl(dreg, dreg, 1);
          /* Result and flag to be zero if shift is >32 */
          emit_movz(reg_c_cache, reg_zero, reg_temp);
          emit_movz(dreg, reg_zero, reg_temp);
          break;
        case ShiftASR:
          force_load_reg(dreg, sreg, pc);
          emit_beq(reg_a1, reg_zero, 7);
          generate_swap_delay();
          emit_addiu(reg_temp, reg_zero, 32);
          emit_srl(reg_rv, reg_a1, 5);             // Check if shift >= 32
          emit_movn(reg_a1, reg_temp, reg_rv);     // Cap it at 32
          emit_addiu(reg_temp, reg_a1, -1);        // Shift in two steps
          emit_srav(dreg, dreg, reg_temp);
          emit_andi(reg_c_cache, dreg, 1);
          emit_sra(dreg, dreg, 1);
          break;
        case ShiftROR:
          {
            mips_regnum rm = load_alloc_reg(sreg, reg_a2, pc);
            rotate_right_var(dreg, rm, reg_temp, reg_a1);
            emit_srl(reg_temp, dreg, 31);  // CF is just the MSB bit
            emit_movn(reg_c_cache, reg_temp, reg_a1);
          }
          break;
      };
    } else {
      mips_regnum rm = load_alloc_reg(sreg, dreg, pc);
      switch (st) {
        case ShiftLSL:
          emit_sltiu(reg_temp, reg_a1, 32);
          emit_sllv(dreg, rm, reg_a1);
          emit_movz(dreg, reg_zero, reg_temp);
          break;
        case ShiftLSR:
          emit_sltiu(reg_temp, reg_a1, 32);
          emit_srlv(dreg, rm, reg_a1);
          emit_movz(dreg, reg_zero, reg_temp);
          break;
        case ShiftASR:
          emit_sltiu(reg_temp, reg_a1, 32);
          emit_bne(reg_temp, reg_zero, 2);
          emit_srav(dreg, rm, reg_a1);
          emit_sra(dreg, dreg, 31);
          break;
        case ShiftROR:
          // TODO: src and dst must be different!
          rotate_right_var(dreg, rm, reg_temp, reg_a1);
          break;
      };
    }
  }

  // Calculates the flex operand, honoring flag (CF) generation and returns the
  // native register where the value is placed (either reg_a0 or some ARM reg).
  template <FlagOperation flg>
  inline mips_regnum emit_arm_aluop2(const ARMInst & it) {
    // Calculates the Op2 part and writes it to a0
    if (it.op2imm()) {
      // Special case: LSL with imm = 0 means unmodified register (and Cflag).
      // Just return the register directly (or scratch to a0 for PC)
      // Saves one instruction (it is relatively common)
      if (it.op2sa() == 0 && it.op2smode() == ShiftLSL)
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
  template <ARMOp aluop, FlagOperation flg>
  inline void arm_alureg3(const ARMInst & it, u32 & cycle_count) {
    // Generate op2 to a0, op1 to a1
    mips_regnum regop2 = (aluop == OpAdd || aluop == OpSub || aluop == OpRsb ||
                          aluop == OpAdc || aluop == OpSbc || aluop == OpRsc) ?
                          emit_arm_aluop2<NoFlags>(it) :  // Do not generate C flag
                          emit_arm_aluop2<flg>(it);

    mips_regnum rn = load_alloc_reg(it.rn(), reg_a1, it.pc + (it.op2imm() ? 8 : 12));
    mips_regnum rd = store_alloc_reg(it.rd(), reg_a0);

    switch (aluop) {
    case OpAnd:
      emit_and(rd, rn, regop2);
      update_nz_flags<flg>(it, rd);
      break;
    case OpOrr:
      emit_or(rd, rn, regop2);
      update_nz_flags<flg>(it, rd);
      break;
    case OpXor:
      emit_xor(rd, rn, regop2);
      update_nz_flags<flg>(it, rd);
      break;
    case OpBic:
      emit_nor(reg_rv, regop2, reg_zero);
      emit_and(rd, rn, reg_rv);
      update_nz_flags<flg>(it, rd);
      break;

    case OpAdd:
      if (flg == NoFlags)
        emit_addu(rd, rn, regop2);
      else
        generate_adds(it, rd, rn, regop2);
      break;
    case OpAdc:
      if (flg == SetFlags)
        generate_adcs(it, rd, rn, regop2);
      else {
        emit_addu(reg_temp, regop2, reg_c_cache);
        emit_addu(rd, rn, reg_temp);
      }
      break;
    case OpSub:
      if (flg == NoFlags)
        emit_subu(rd, rn, regop2);
      else
        generate_subs(it, rd, rn, regop2);
      break;
    case OpSbc:
      generate_sbc<flg>(it, rd, rn, regop2);
      break;
    case OpRsb:
      if (flg == NoFlags)
        emit_subu(rd, regop2, rn);
      else
        generate_subs(it, rd, regop2, rn);
      break;
    case OpRsc:
      generate_sbc<flg>(it, rd, regop2, rn);
      break;
    };

    const u8 condition = it.cond();        // TODO remove this
    if (flg == NoFlags) {
      check_store_reg_pc_no_flags(it.rd());
    } else {
      check_store_reg_pc_flags(it.rd());
    }
  }


  template <ARMOp aluop, FlagOperation flg>
  inline void arm_alureg1(const ARMInst & it, u32 & cycle_count) {
    mips_regnum regop2 = emit_arm_aluop2<flg>(it);   // Generate op2 to a0
    mips_regnum rd = store_alloc_reg(it.rd(), reg_a0);

    switch (aluop) {
    case OpMvn:
      emit_nor(rd, reg_zero, regop2);
      break;
    case OpMov:
      generate_mov(rd, regop2);
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
  template <ARMOp aluop, FlagOperation c_flag>
  inline void arm_alureg2(const ARMInst & it) {
    mips_regnum regop2 = emit_arm_aluop2<c_flag>(it);   // Generate op2 to a0 (with/without C flag)
    mips_regnum rn = load_alloc_reg(it.rn(), reg_a1, it.pc + (it.op2imm() ? 8 : 12));

    switch (aluop) {
    case OpTst:
       emit_and(reg_temp, rn, regop2);
       update_nz_flags<SetFlags>(it, reg_temp);
       break;
    case OpTeq:
       emit_xor(reg_temp, rn, regop2);
       update_nz_flags<SetFlags>(it, reg_temp);
       break;
    case OpCmp:
      generate_subs(it, reg_temp, rn, regop2);
      break;
    case OpCmn:
      generate_adds(it, reg_temp, rn, regop2);
      break;
    };
  }

  // Performs 32 bit multiplications (rd and rn are swapped)
  template<FlagOperation flg, MulMode mm>
  inline void arm_mul32(const ARMInst &it) {
    mips_regnum rm = load_alloc_reg(it.rm(), reg_a0, it.pc + 8);
    mips_regnum rs = load_alloc_reg(it.rs(), reg_a1, it.pc + 8);
    mips_regnum rd = store_alloc_reg(it.rn(), reg_a2);

    emit_multu(rm, rs);

    if (mm == MulAdd) {
      mips_regnum rn = load_alloc_reg(it.rd(), reg_temp, it.pc + 8);
      emit_mflo(reg_rv);
      emit_addu(rd, reg_rv, rn);
    } else {
      emit_mflo(rd);
    }

    update_nz_flags<flg>(it, rd);
    // Writing PC is not really defined.
  }

  // Performs 64 bit multiplications
  template<FlagOperation flg, MulMode mm, bool signmul>
  inline void arm_mul64(const ARMInst &it) {
    mips_regnum rm = load_alloc_reg(it.rm(), reg_a0, it.pc + 8);
    mips_regnum rs = load_alloc_reg(it.rs(), reg_a1, it.pc + 8);
    mips_regnum rdlo = (mm == MulAdd) ? load_alloc_reg(it.rdlo(), reg_a2, it.pc + 8)
                                      : store_alloc_reg(it.rdlo(), reg_a2);
    mips_regnum rdhi = (mm == MulAdd) ? load_alloc_reg(it.rdhi(), reg_temp, it.pc + 8)
                                      : store_alloc_reg(it.rdhi(), reg_temp);

    if (mm == MulAdd) {
      emit_mtlo(rdlo);
      emit_mthi(rdhi);
      if (signmul)
        emit_madd(rm, rs);
      else
        emit_maddu(rm, rs);
    } else {
      if (signmul)
        emit_mult(rm, rs);
      else
        emit_multu(rm, rs);
    }

    emit_mflo(rdlo);
    emit_mfhi(rdhi);

    if (flg == SetFlags) {
      emit_sltiu(reg_z_cache, rdlo, 1);   // TODO use orr then stliu?
      emit_sltiu(reg_a0, rdhi, 1);
      emit_and(reg_z_cache, reg_z_cache, reg_a0);
      emit_srl(reg_n_cache, rdhi, 31);
    }
  }

  // PSR register read
  template<PSReg reg>
  inline void arm_read_psr(const ARMInst &it) {
    if (reg == RegCPSR) {
      generate_function_call(execute_read_cpsr);
    } else {
      generate_function_call(execute_read_spsr);
    }

    generate_store_reg(reg_rv, it.rd());
  }

  // PSR register write
  template<PSReg reg, OpType opt>
  inline void arm_write_psr(const ARMInst &it) {
    if (opt == OpReg) {
      generate_load_reg(reg_a0, it.rm());
    } else {
      u32 imm = rotr32(it.imm8(), it.rot4() * 2);
      generate_load_imm(reg_a0, imm);
    }

    if (reg == RegCPSR) {
      emit_load_pc(reg_a1, it.pc);
      generate_function_call_swap_delay(execute_store_cpsr);
      generate_raw_u32(cpsr_masks[it.field_fc()][0]);
      generate_raw_u32(cpsr_masks[it.field_fc()][1]);
    } else {
      generate_load_imm(reg_a1, spsr_masks[it.field_fc()]);
      generate_function_call_swap_delay(execute_store_spsr);
    }
  }

  template <CPUInstMode cm>
  inline void trace_instruction(u32 pc, u32 opcode) {
    #ifdef TRACE_INSTRUCTIONS
    emit_save_regs(false);
    generate_load_imm(reg_a0, pc);
    generate_load_imm(reg_a2, opcode);
    if (cm == ModeThumb) {
      genccall(&trace_instruction_hook_thumb);
    } else {
      genccall(&trace_instruction_hook_arm);
    }
    emit_nop();
    emit_restore_regs(false);
    #endif
  }


  // ---- Init stub / handler codegeneration -----

  void emit_mem_access_loadop(u32 base_addr, unsigned size, unsigned alignment, bool signext) {
    switch (size) {
    case 2:
      emit_lw(reg_rv, reg_rv, (base_addr & 0xffff));
      break;
    case 1:
      if (!signext)
        emit_lhu(reg_rv, reg_rv, (base_addr & 0xffff));
      else {
        if (alignment)    // Unaligned signed 16b load, is just a load byte (due to sign extension)
          emit_lb(reg_rv, reg_rv, ((base_addr | 1) & 0xffff));
        else
          emit_lh(reg_rv, reg_rv, (base_addr & 0xffff));
      }
      break;
    default:
      if (signext)
        emit_lb(reg_rv, reg_rv, (base_addr & 0xffff));
      else
        emit_lbu(reg_rv, reg_rv, (base_addr & 0xffff));
      break;
    };
  }

  // Generates the stub to access memory for a given region, access type,
  // size and misalignment.
  // Handles "special" cases like weirdly mapped memory
  void emit_pmemld_stub(
    unsigned memop_number, const t_stub_meminfo *meminfo,
    bool signext, unsigned size,
    unsigned alignment, bool aligned, bool must_swap)
  {
    unsigned region = meminfo->region;
    u32 base_addr = meminfo->baseptr;

    if (region >= 9 && region <= 11) {
      // Use the same handler for these regions (just replicas)
      tmemld[memop_number][region] = tmemld[memop_number][8];
      return;
    }

    // Clean up one or two bits (to align access). It might already be aligned!
    u32 memmask = (meminfo->memsize - 1);
    memmask = (memmask >> size) << size;    // Clear 1 or 2 (or none) bits

    // Add the stub to the table (add the JAL instruction encoded already)
    tmemld[memop_number][region] = (u32)emit_ptr;

    // Size: 0 (8 bits), 1 (16 bits), 2 (32 bits)
    // First check we are in the right memory region
    unsigned regionbits = 8;
    unsigned regioncheck = region;
    if (region == 8) {
      // This is an optimization for ROM regions
      // For region 8-11 we reuse the same code (and have a more generic check)
      // Region 12 is harder to cover without changing the check (shift + xor)
      regionbits = 6;
      regioncheck >>= 2;   // Ignore the two LSB, don't care
    }

    // Address checking: jumps to handler if bad region/alignment
    emit_srl(reg_temp, reg_a0, (32 - regionbits));
    if (!aligned && size != 0) {  // u8 or aligned u32 dont need to check alignment bits
      insert_bits(reg_temp, reg_a0, reg_rv, regionbits, size);  // Add 1 or 2 bits of alignment
    }
    if (regioncheck || alignment)   // If region and alignment are zero, can skip
      emit_xori(reg_temp, reg_temp, regioncheck | (alignment << regionbits));

    // The patcher to use depends on ld/st, access size, and sign extension
    // (so there's 10 of them). They live in the top stub addresses.
    emit_bne(reg_zero, reg_temp, ld_phndlr_branch(memop_number));

    // BIOS region requires extra checks for protected reads
    if (region == 0) {
      // BIOS is *not* mirrored, check that
      emit_srl(reg_rv, reg_a0, 14);
      emit_bne(reg_zero, reg_rv, branch_offset(openld_core_ptrs[memop_number]));

      // Check whether the read is allowed. Only within BIOS! (Ignore aligned, bad a1)
      if (!aligned) {
        emit_srl(reg_temp, reg_a1, 14);
        emit_bne(reg_zero, reg_temp, branch_offset(openld_core_ptrs[memop_number]));
      }
    }

    if (region >= 8 && region <= 12) {
      // ROM area: might need to load the ROM on-demand
      emit_srl(reg_rv, reg_a0, 15);  // 32KB page number
      emit_sll(reg_rv, reg_rv,  2);  // (word indexed)
      emit_addu(reg_rv, reg_rv, reg_base);    // base + offset
      emit_lw(reg_rv, reg_rv, 0x8000);        // base[offset-0x8000] is readmap ptr
      emit_andi(reg_temp, reg_a0, memmask);   // Get the lowest 15 bits [can go in delay slot]

      if (must_swap) {   // Do not emit if the ROM is fully loaded, save some cycles
        u8 * jmppatch = emit_bne(reg_rv, reg_zero, 0);  // if not null, can skip load page
        generate_swap_delay();

        // This code call the C routine to map the relevant ROM page
        emit_save_regs(aligned);
        emit_sw(mips_reg_ra, reg_base, ReOff_SaveR3);
        extract_bits(reg_a0, reg_a0, 15, 10);    // a0 = (addr >> 15) & 0x3ff
        genccall(&load_gamepak_page);            // Returns valid pointer in rv
        emit_sw(reg_temp, reg_base, ReOff_SaveR1);

        emit_lw(reg_temp, reg_base, ReOff_SaveR1);
        emit_restore_regs(aligned);
        emit_lw(mips_reg_ra, reg_base, ReOff_SaveR3);

        generate_branch_patch_conditional(jmppatch - 4, emit_ptr);
      }
      // Now we can proceed to load, place addr in the right register
      emit_addu(reg_rv, reg_rv, reg_temp);
    } else if (region == 14) {
      // Read from flash, is a bit special, fn call
      emit_mem_call_ds(&read_backup, 0xFFFF);
      if (!size && signext) {
        extend_byte_signed(reg_rv, reg_rv);
      } else if (size == 1 && alignment) {
        extend_byte_signed(reg_rv, reg_rv);
      } else if (size == 2) {
        rotate_right(reg_rv, reg_rv, reg_temp, 8 * alignment);
      }
      generate_function_return_swap_delay();
      return;
    } else {
      // Generate upper bits of the addr and do addr mirroring
      // (The address hi16 is rounded up since load uses signed offset)
      if (!meminfo->baseoff)
        emit_lui(reg_rv, ((base_addr + 0x8000) >> 16));
      else
        base_addr = meminfo->baseoff;

      if (region == 2) {
        // Can't do EWRAM with an `andi` instruction (18 bits mask)
        extract_bits(reg_a0, reg_a0, 0, 18);       // &= 0x3ffff
        if (!aligned && alignment != 0) {
          emit_align_reg(reg_a0, size);            // addr & ~1/2 (align to size)
        }
        // Need to insert a zero in the addr (due to how it's mapped)
        emit_addu(reg_rv, reg_rv, reg_a0);    // Adds to the base addr
      } else if (region == 6) {
        // VRAM is mirrored every 128KB but the last 32KB is mapped to the previous
        extract_bits(reg_temp, reg_a0, 15, 2);     // Extract bits 15 and 16
        emit_addiu(reg_temp, reg_temp, -3);   // Check for 3 (last block)
        if (!aligned && alignment != 0) {
          emit_align_reg(reg_a0, size);            // addr & ~1/2 (align to size)
        }
        extract_bits(reg_a0, reg_a0, 0, 17);       // addr & 0x1FFFF [delay]
        emit_bne(reg_zero, reg_temp, 1);   // Skip unless last block
        generate_swap_delay();
        emit_addiu(reg_a0, reg_a0, 0x8000);   // addr - 0x8000 (mirror last block)
        emit_addu(reg_rv, reg_rv, reg_a0);    // addr = base + adjusted offset
      } else {
        // Generate regular (<=32KB) mirroring
        mips_regnum breg = (meminfo->baseoff ? reg_base : reg_rv);
        emit_andi(reg_temp, reg_a0, memmask); // Clear upper bits (mirroring)
        emit_addu(reg_rv, breg, reg_temp);    // Adds to base addr
      }
    }

    // Emit load operation
    emit_mem_access_loadop(base_addr, size, alignment, signext);

    if (!(alignment == 0 || (size == 1 && signext))) {
      // Unaligned accesses require rotation, except for size=1 & signext
      rotate_right(reg_rv, reg_rv, reg_temp, alignment * 8);
    }

    generate_function_return_swap_delay();   // Return. Move prev inst to delay slot
  }

  // Generates the stub to store memory for a given region and size
  // Handles "special" cases like weirdly mapped memory
  void emit_pmemst_stub(
    unsigned memop_number, const t_stub_meminfo *meminfo,
    unsigned size, bool aligned) {
    unsigned region = meminfo->region;
    u32 base_addr = meminfo->baseptr;

    // Palette, VRAM and OAM cannot be really byte accessed (use a 16 bit store)
    bool doubleaccess = (size == 0 && meminfo->bus16);
    unsigned realsize = size;
    if (doubleaccess)
      realsize = 1;

    // Clean up one or two bits (to align access). It might already be aligned!
    u32 memmask = (meminfo->memsize - 1);
    memmask = (memmask >> realsize) << realsize;

    // Add the stub to the table (add the JAL instruction encoded already)
    tmemst[memop_number][region] = (u32)emit_ptr;

    // First check we are in the right memory region (same as loads)
    emit_srl(reg_temp, reg_a0, 24);
    emit_xori(reg_temp, reg_temp, region);
    emit_bne(reg_zero, reg_temp, st_phndlr_branch(memop_number));

    emit_lui(reg_rv, ((base_addr + 0x8000) >> 16));

    if (doubleaccess) {
      double_byte(reg_a1, reg_temp);        // value = value | (value << 8)
    }

    if (region == 2) {
      // Can't do EWRAM with an `andi` instruction (18 bits mask)
      extract_bits(reg_a0, reg_a0, 0, 18);       // &= 0x3ffff
      if (!aligned && realsize != 0) {
        emit_align_reg(reg_a0, size);            // addr & ~1/2 (align to size)
      }
      // Need to insert a zero in the addr (due to how it's mapped)
      emit_addu(reg_rv, reg_rv, reg_a0);    // Adds to the base addr
    } else if (region == 6) {
      // VRAM is mirrored every 128KB but the last 32KB is mapped to the previous
      extract_bits(reg_temp, reg_a0, 15, 2);     // Extract bits 15 and 16
      emit_addiu(reg_temp, reg_temp, -3);   // Check for 3 (last block)
      if (!aligned && realsize != 0) {
        emit_align_reg(reg_a0, realsize);        // addr & ~1/2 (align to size)
      }
      extract_bits(reg_a0, reg_a0, 0, 17);       // addr & 0x1FFFF [delay]
      emit_bne(reg_zero, reg_temp, 1);   // Skip next inst unless last block
      generate_swap_delay();
      emit_addiu(reg_a0, reg_a0, 0x8000);   // addr - 0x8000 (mirror last block)
      emit_addu(reg_rv, reg_rv, reg_a0);    // addr = base + adjusted offset
    } else {
      // Generate regular (<=32KB) mirroring
      emit_andi(reg_a0, reg_a0, memmask);   // Clear upper bits (mirroring)
      emit_addu(reg_rv, reg_rv, reg_a0);    // Adds to base addr
    }

    // Generate SMC write and tracking
    // TODO: Should we have SMC checks here also for aligned?
    if (meminfo->check_smc && !aligned) {
      if (region == 2) {
        emit_lui(reg_temp, 0x40000 >> 16);
        emit_addu(reg_temp, reg_rv, reg_temp); // SMC lives after the ewram
      } else {
        emit_addiu(reg_temp, reg_rv, 0x8000); // -32KB is the addr of the SMC buffer
      }
      if (realsize == 2)
        emit_lw(reg_temp, reg_temp, base_addr);
      else if (realsize == 1)
        emit_lh(reg_temp, reg_temp, base_addr);
      else
        emit_lb(reg_temp, reg_temp, base_addr);
      // If the data is non zero, we just wrote over code
      // Local-jump to the smc_write (which lives at offset:0)
      emit_bne(reg_zero, reg_temp, branch_offset(&rom_translation_cache[SMC_WRITE_OFF]));
    }

    // Store the data (delay slot from the SMC branch)
    if (realsize == 2)
      emit_sw(reg_a1, reg_rv, base_addr);
    else if (realsize == 1)
      emit_sh(reg_a1, reg_rv, base_addr);
    else
      emit_sb(reg_a1, reg_rv, base_addr);

    // Post processing store:
    // Signal that OAM was updated
    if (region == 7) {
      // Write any nonzero data
      emit_sw(reg_base, reg_base, ReOff_OamUpd);
      generate_function_return_swap_delay();
    }
    else {
      emit_jr(mips_reg_ra);
      emit_nop();
    }
  }

  // Palette is accessed differently and stored in a decoded manner
  void emit_palette_hdl(
    unsigned memop_number, const t_stub_meminfo *meminfo,
    unsigned size, bool aligned)
  {
    // Palette cannot be accessed at byte level
    unsigned realsize = size ? size : 1;
    u32 memmask = (meminfo->memsize - 1);
    memmask = (memmask >> realsize) << realsize;

    // Add the stub to the table (add the JAL instruction encoded already)
    tmemst[memop_number][5] = (u32)emit_ptr;

    // First check we are in the right memory region (same as loads)
    emit_srl(reg_temp, reg_a0, 24);
    emit_xori(reg_temp, reg_temp, 5);
    emit_bne(reg_zero, reg_temp, st_phndlr_branch(memop_number));
    emit_andi(reg_rv, reg_a0, memmask);   // Clear upper bits (mirroring)
    if (size == 0) {
      double_byte(reg_a1, reg_temp);    // value = value | (value << 8)
    }
    emit_addu(reg_rv, reg_rv, reg_base);

    // Store the data in real palette memory
    if (realsize == 2) {
      emit_sw(reg_a1, reg_rv, 0x100);
    } else if (realsize == 1) {
      emit_sh(reg_a1, reg_rv, 0x100);
    }

    // Convert and store in mirror memory
    palette_convert();
    emit_sh(reg_temp, reg_rv, 0x500);

    if (size == 2) {
      // Convert the second half-word also
      emit_srl(reg_a1, reg_a1, 16);
      palette_convert();
      emit_sh(reg_temp, reg_rv, 0x502);
    }
    generate_function_return_swap_delay();
  }

  // This emits stubs for regions where writes have no side-effects
  void emit_ignorestore_stub(unsigned size) {
    // Region 0-1 (BIOS and ignore)
    tmemst[size][0] = tmemst[size][1] = (u32)emit_ptr;
    emit_srl(reg_temp, reg_a0, 25);               // Check 7 MSB to be zero
    emit_bne(reg_temp, reg_zero, st_phndlr_branch(size));
    emit_nop();
    emit_jr(mips_reg_ra);
    emit_nop();

    // Region 9-C
    tmemst[size][ 9] = tmemst[size][10] =
    tmemst[size][11] = tmemst[size][12] = (u32)emit_ptr;

    emit_srl(reg_temp, reg_a0, 24);
    emit_addiu(reg_temp, reg_temp, -9);
    emit_srl(reg_temp, reg_temp, 2);
    emit_bne(reg_temp, reg_zero, st_phndlr_branch(size));
    emit_nop();
    emit_jr(mips_reg_ra);
    emit_nop();

    // Region F or higher
    tmemst[size][15] = (u32)emit_ptr;
    emit_srl(reg_temp, reg_a0, 24);
    emit_sltiu(reg_rv, reg_temp, 0x0F);  // Is < 15?
    emit_bne(reg_rv, reg_zero, st_phndlr_branch(size));
    emit_nop();
    emit_jr(mips_reg_ra);
    emit_nop();
  }

  // Stubs for regions with EEPROM or flash/SRAM (also RTC)
  void emit_saveaccess_stub() {
    unsigned opt, i, strop;

    // Writes to region 8 are directed to RTC (only 16 bit ones though)
    tmemld[1][8] = (u32)emit_ptr;
    emit_mem_call(&write_gpio, 0xFE);

    // These are for region 0xD where EEPROM is mapped. Addr is ignored
    // Value is limited to one bit (both reading and writing!)
    u32 *read_hndlr = (u32*)emit_ptr;
    emit_mem_call(&read_eeprom, 0x3FF);
    u32 *write_hndlr = (u32*)emit_ptr;
    emit_mem_call(&write_eeprom, 0x3FF);

    // Map loads to the read handler.
    for (opt = 0; opt < 6; opt++) {
      // Unalignment is not relevant here, so map them all to the same handler.
      for (i = ldopmap[opt][0]; i < ldopmap[opt][1]; i++)
        tmemld[i][13] = (u32)emit_ptr;
      // Emit just a check + patch jump
      emit_srl(reg_temp, reg_a0, 24);
      emit_xori(reg_rv, reg_temp, 0x0D);
      emit_bne(reg_rv, reg_zero, branch_handlerid(opt));
      emit_nop();
      emit_beq(reg_zero, reg_zero, branch_offset(read_hndlr));
    }
    // This is for stores
    for (strop = 0; strop <= 3; strop++) {
      tmemst[strop][13] = (u32)emit_ptr;
      emit_srl(reg_temp, reg_a0, 24);
      emit_xori(reg_rv, reg_temp, 0x0D);
      emit_bne(reg_rv, reg_zero, st_phndlr_branch(strop));
      emit_nop();
      emit_beq(reg_zero, reg_zero, branch_offset(write_hndlr));
    }

    // Flash/SRAM/Backup writes are only 8 byte supported
    for (strop = 0; strop <= 3; strop++) {
      tmemst[strop][14] = (u32)emit_ptr;
      emit_srl(reg_temp, reg_a0, 24);
      emit_xori(reg_rv, reg_temp, 0x0E);
      emit_bne(reg_rv, reg_zero, st_phndlr_branch(strop));
      if (strop == 0) {
        emit_mem_call(&write_backup, 0xFFFF);
      } else {
        emit_nop();
        emit_jr(mips_reg_ra);   // Does nothing in this case
        emit_nop();
      }
    }

    // RTC writes, only for 16 bit accesses
    for (strop = 0; strop <= 3; strop++) {
      tmemst[strop][8] = (u32)emit_ptr;
      emit_srl(reg_temp, reg_a0, 24);
      emit_xori(reg_rv, reg_temp, 0x08);
      emit_bne(reg_rv, reg_zero, st_phndlr_branch(strop));
      if (strop == 1) {
        emit_mem_call(&write_gpio, 0xFF);  // Addr
      } else {
        emit_nop();
        emit_jr(mips_reg_ra);   // Do nothing
        emit_nop();
      }
    }

    // Region 4 writes
    // I/O writes are also a bit special, they can trigger things like DMA, IRQs...
    // Also: aligned (strop==3) accesses do not trigger IRQs
    const u32 iowrtbl[] = {
      (u32)&write_io_register8, (u32)&write_io_register16,
      (u32)&write_io_register32, (u32)&write_io_register32 };
    const u32 amsk[] = {0x3FF, 0x3FE, 0x3FC, 0x3FC};
    for (strop = 0; strop <= 3; strop++) {
      tmemst[strop][4] = (u32)emit_ptr;
      emit_srl(reg_temp, reg_a0, 24);
      emit_xori(reg_temp, reg_temp, 0x04);
      emit_bne(reg_zero, reg_temp, st_phndlr_branch(strop));

      emit_sw(mips_reg_ra, reg_base, ReOff_SaveR3); // Store the return addr
      emit_save_regs(strop == 3);
      emit_andi(reg_a0, reg_a0, amsk[strop]);
      genccall(iowrtbl[strop]);

      if (strop < 3) {
        emit_sw(reg_a2, reg_base, ReOff_RegPC);   // Save PC (delay)
        // If I/O writes returns non-zero, means we need to process side-effects.
        emit_bne(reg_zero, reg_rv, branch_offset(&rom_translation_cache[IOEPILOGUE_OFF]));
        emit_lw(mips_reg_ra, reg_base, ReOff_SaveR3);   // (in delay slot but not used)
        emit_restore_regs(false);
      } else {
        emit_nop();
        emit_lw(mips_reg_ra, reg_base, ReOff_SaveR3);
        emit_restore_regs(true);
      }
      generate_function_return_swap_delay();
    }
  }

  // Emits openload stub
  // These are used for reading unmapped regions, we just make them go
  // through the slow handler since should rarely happen.
  void emit_openload_stub(unsigned opt, bool signext, unsigned size) {
    int i;
    const u32 hndreadtbl[] = {
      (u32)&read_memory8,  (u32)&read_memory16,  (u32)&read_memory32,
      (u32)&read_memory8s, (u32)&read_memory16s, (u32)&read_memory32 };

    // This affects regions 1 and 15
    for (i = ldopmap[opt][0]; i < ldopmap[opt][1]; i++)
      tmemld[i][ 1] = tmemld[i][15] = (u32)emit_ptr;

    // Alignment is ignored since the handlers do the magic for us
    // Only check region match: if we are accessing a non-ignore region
    emit_srl(reg_temp, reg_a0, 24);
    emit_sltiu(reg_rv, reg_temp, 0x0F);
    emit_addiu(reg_temp, reg_temp, -1);
    emit_sltu(reg_temp, reg_zero, reg_temp);
    emit_and(reg_temp, reg_temp, reg_rv);

    // Jump to patch handler
    emit_bne(reg_zero, reg_temp, branch_handlerid(opt));

    // BIOS can jump here to do open loads
    for (i = ldopmap[opt][0]; i < ldopmap[opt][1]; i++)
      openld_core_ptrs[i] = (u32*)emit_ptr;

    emit_save_regs(true);
    emit_sw(mips_reg_ra, reg_base, ReOff_SaveR1);   // Delay slot
    genccall(hndreadtbl[size + (signext ? 3 : 0)]);
    if (opt < 5)
      emit_sw(reg_a1, reg_base, ReOff_RegPC);       // Save current PC
    else
      emit_nop();   // Aligned loads do not hold PC in a1 (imprecision)

    emit_lw(mips_reg_ra, reg_base, ReOff_SaveR1);
    emit_restore_regs(true);
    generate_function_return_swap_delay();
  }

  // Generates a patch handler for a given access size
  // It will detect the access alignment and memory region and load
  // the corresponding handler from the table (at the right offset)
  // and patch the jal instruction from where it was called.
  void emit_phand(unsigned size, unsigned toff, bool check_alignment) {
    u8 *iptr = emit_ptr;

    emit_srl(reg_temp, reg_a0, 24);
    #ifdef PSP
      emit_addiu(reg_rv, reg_zero, 15*4);  // Table limit (max)
      emit_sll(reg_temp, reg_temp, 2);     // Table is word indexed
      mips_emit_min(reg_temp, reg_temp, reg_rv);// Do not overflow table
    #else
      emit_sltiu(reg_rv, reg_temp, 0x0F);  // Check for addr 0x1XXX.. 0xFXXX
      emit_sll(reg_temp, reg_temp, 2);     // Table is word indexed
      emit_bne(reg_zero, reg_rv, 1);    // Skip next inst if region is good
      generate_swap_delay();
      emit_addiu(reg_temp, reg_zero, 15*4);// Simulate ld/st to 0x0FXXX (open/ignore)
    #endif

    // Stores or byte-accesses do not care about alignment
    if (check_alignment) {
      // Move alignment bits for the table lookup (1 or 2, to bits 6 and 7)
      insert_bits(reg_temp, reg_a0, reg_rv, 6, size);
    }

    unsigned tbloff = 256 + 3*1024 + 220 + 4 * toff;  // Skip regs and RAMs
    unsigned tbloff2 = tbloff + 960;              // JAL opcode table
    emit_addu(reg_temp, reg_temp, reg_base); // Add to the base_reg the table offset
    emit_lw(reg_rv,   reg_temp, tbloff);     // Get func addr from 1st table
    emit_lw(reg_temp, reg_temp, tbloff2);    // Get opcode from 2nd table
    emit_sw(reg_temp, mips_reg_ra, -8);      // Patch instruction!

    #if defined(PSP)
      emit_cache(0x1A, mips_reg_ra, -8);
      emit_jr(reg_rv);                       // Jump directly to target for speed
      emit_cache(0x08, mips_reg_ra, -8);
    #else
      emit_jr(reg_rv);
      #ifdef MIPS_HAS_R2_INSTS
        emit_synci(mips_reg_ra, -8);
      #endif
    #endif

    // Round up handlers to 16 instructions for easy addressing
    // PSP/MIPS32r2 uses up to 12 insts
    while (emit_ptr - iptr < 64)
      emit_nop();
  }

  // This function emits the following stubs:
  // - smc_write: Jumps to C code to trigger a cache flush
  // - memop patcher: Patches a memop whenever it accesses the wrong mem region
  // - mem stubs: There's stubs for load & store, and every memory region
  //    and possible operand size and misaligment (+sign extensions)
  void emit_stubs(bool must_swap) {
    // Initialize memory to a debuggable state
    rom_cache_watermark = INITIAL_ROM_WATERMARK;

    // Generate first the patch handlers
    // We have 6+4 patchers, one per mem type (6 or 4)

    // Calculate the offset into tmemld[10][XX];
    emit_phand(0,  0 * 16, false);  // ld u8
    emit_phand(0,  1 * 16, false);  // ld s8
    emit_phand(1,  2 * 16, true);   // ld u16 + u16u1
    emit_phand(1,  4 * 16, true);   // ld s16 + s16u1
    emit_phand(2,  6 * 16, true);   // ld u32 (0/1/2/3u)
    emit_phand(2, 10 * 16, false);  // ld aligned 32
    // Store table is immediately after
    emit_phand(0, 11 * 16, false);  // st u8
    emit_phand(1, 12 * 16, false);  // st u16
    emit_phand(2, 13 * 16, false);  // st u32
    emit_phand(2, 14 * 16, false);  // st aligned 32

    // Trampoline area
    emit_j(((u32)&smc_write) >> 2);
    emit_nop();

    emit_j(((u32)&write_io_epilogue) >> 2);
    emit_nop();

    // Special trampoline for SP-relative ldm/stm (to EWRAM)
    generate_load_imm(reg_a1, 0x3FFFC);
    emit_and(reg_a1, reg_a1, reg_a2);
    emit_lui(reg_a0, ((u32)(ewram + 0x8000) >> 16));
    generate_function_return_swap_delay();

    // Generate the openload handlers (for accesses to unmapped mem)
    emit_openload_stub(0, false, 0);  // ld u8
    emit_openload_stub(1, true,  0);  // ld s8
    emit_openload_stub(2, false, 1);  // ld u16
    emit_openload_stub(3, true,  1);  // ld s16
    emit_openload_stub(4, false, 2);  // ld u32
    emit_openload_stub(5, false, 2);  // ld a32

    // Here we emit the ignore store area, just checks and does nothing
    for (int i = 0; i < 4; i++)
      emit_ignorestore_stub(i);

    // Here go the save game handlers
    emit_saveaccess_stub();

    // Generate memory handlers
    const t_stub_meminfo ldinfo [] = {
      {  0, 0x4000, false, false, (u32)bios_rom, 0},
      // 1 Open load / Ignore store
      {  2, 0x8000, true,  false, (u32)ewram, 0 },      // memsize wrong on purpose
      {  3, 0x8000, true,  false, (u32)&iwram[0x8000], 0 },
      {  4,  0x400, false, false, (u32)io_registers, 0 },
      {  5,  0x400, false, true,  (u32)palette_ram, 0x100 },
      {  6,    0x0, false, true,  (u32)vram, 0 },             // same, vram is a special case
      {  7,  0x400, false, true,  (u32)oam_ram, 0x900 },
      {  8, 0x8000, false, false,  0, 0 },
      {  9, 0x8000, false, false,  0, 0 },
      { 10, 0x8000, false, false,  0, 0 },
      { 11, 0x8000, false, false,  0, 0 },
      { 12, 0x8000, false, false,  0, 0 },
      // 13 is EEPROM mapped already (a bit special)
      { 14,      0, false, false,  0, 0 },                    // Mapped via function call
      // 15 Open load / Ignore store
    };

    for (int i = 0; i < sizeof(ldinfo)/sizeof(ldinfo[0]); i++) {
      /*          region  info      signext sz al  isaligned */
      emit_pmemld_stub(0, &ldinfo[i], false, 0, 0, false, must_swap);  // ld u8
      emit_pmemld_stub(1, &ldinfo[i], true,  0, 0, false, must_swap);  // ld s8

      emit_pmemld_stub(2, &ldinfo[i], false, 1, 0, false, must_swap);  // ld u16
      emit_pmemld_stub(3, &ldinfo[i], false, 1, 1, false, must_swap);  // ld u16u1
      emit_pmemld_stub(4, &ldinfo[i], true,  1, 0, false, must_swap);  // ld s16
      emit_pmemld_stub(5, &ldinfo[i], true,  1, 1, false, must_swap);  // ld s16u1

      emit_pmemld_stub(6, &ldinfo[i], false, 2, 0, false, must_swap);  // ld u32
      emit_pmemld_stub(7, &ldinfo[i], false, 2, 1, false, must_swap);  // ld u32u1
      emit_pmemld_stub(8, &ldinfo[i], false, 2, 2, false, must_swap);  // ld u32u2
      emit_pmemld_stub(9, &ldinfo[i], false, 2, 3, false, must_swap);  // ld u32u3

      emit_pmemld_stub(10,&ldinfo[i], false, 2, 0, true,  must_swap);  // aligned ld u32
    }

    const t_stub_meminfo stinfo [] = {
      { 2, 0x8000, true,  false, (u32)ewram, 0 },
      { 3, 0x8000, true,  false, (u32)&iwram[0x8000], 0 },
      // I/O is special and mapped with a function call
      { 5,  0x400, false, true,  (u32)palette_ram, 0x100 },
      { 6,    0x0, false, true,  (u32)vram, 0 },          // same, vram is a special case
      { 7,  0x400, false, true,  (u32)oam_ram, 0x900 },
    };

    // Store only for "regular"-ish mem regions
    //
    for (int i = 0; i < sizeof(stinfo)/sizeof(stinfo[0]); i++) {
      if (stinfo[i].region == 5) {
        emit_palette_hdl(0, &stinfo[i], 0, false);  // st u8
        emit_palette_hdl(1, &stinfo[i], 1, false);  // st u16
        emit_palette_hdl(2, &stinfo[i], 2, false);  // st u32
        emit_palette_hdl(3, &stinfo[i], 2, true );  // st aligned 32
      } else {
        emit_pmemst_stub(0, &stinfo[i], 0, false);  // st u8
        emit_pmemst_stub(1, &stinfo[i], 1, false);  // st u16
        emit_pmemst_stub(2, &stinfo[i], 2, false);  // st u32
        emit_pmemst_stub(3, &stinfo[i], 2, true );  // st aligned 32
      }
    }

    // Generate JAL tables
    u32 *tmemptr = &tmemld[0][0];
    for (int i = 0; i < 15*16; i++)
      thnjal[i] = ((tmemptr[i] >> 2) & 0x3FFFFFF) | (mips_opcode_jal << 26);
  }
};

void init_emitter(bool must_swap) {
  // Emit at the cache base
  CodeEmitter ce(rom_translation_cache, &rom_translation_cache[ROM_TRANSLATION_CACHE_SIZE], 0);
  ce.emit_stubs(must_swap);

  // Ensure rom flushes do not wipe this area
  rom_cache_watermark = (u32)(ce.emit_ptr - rom_translation_cache);

  init_bios_hooks();
}

u32 execute_arm_translate(u32 cycles) {
  return execute_arm_translate_internal(cycles, &reg[0]);
}

#endif


