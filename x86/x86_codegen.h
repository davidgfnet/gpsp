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

#ifndef X86_CODEGEN_H
#define X86_CODEGEN_H

typedef enum {
  x86_reg_eax = 0,
  x86_reg_ecx = 1,
  x86_reg_edx = 2,
  x86_reg_ebx = 3,
  x86_reg_esp = 4,
  x86_reg_ebp = 5,
  x86_reg_esi = 6,
  x86_reg_edi = 7
} x86_regnum;

typedef enum {
  x86_mod_mem        = 0,
  x86_mod_mem_disp8  = 1,
  x86_mod_mem_disp32 = 2,
  x86_mod_reg        = 3
} x86_mod;


typedef enum {
  x86_opcode_mov_rm_reg                 = 0x89,
  x86_opcode_mov_reg_rm                 = 0x8B,
  x86_opcode_mov_reg_imm                = 0xB8,
  x86_opcode_mov_rm_imm                 = 0x00C7,
  x86_opcode_ror_reg_imm                = 0x01C1,
  x86_opcode_shl_reg_imm                = 0x04C1,
  x86_opcode_shr_reg_imm                = 0x05C1,
  x86_opcode_sar_reg_imm                = 0x07C1,
  x86_opcode_ror_reg_rm                 = 0x01D3,
  x86_opcode_rcr_reg_rm                 = 0x03D3,
  x86_opcode_shl_reg_rm                 = 0x04D3,
  x86_opcode_shr_reg_rm                 = 0x05D3,
  x86_opcode_sar_reg_rm                 = 0x07D3,
  x86_opcode_rcr_reg1                   = 0x03D1,
  x86_opcode_call_offset                = 0xE8,
  x86_opcode_ret                        = 0xC3,
  x86_opcode_cmc                        = 0xF5,
  x86_opcode_test_reg_rm                = 0x85,
  x86_opcode_test_rm_imm                = 0x00F7,
  x86_opcode_not_rm                     = 0x02F7,
  x86_opcode_neg_rm                     = 0x03F7,
  x86_opcode_mul_eax_rm                 = 0x04F7,
  x86_opcode_imul_eax_rm                = 0x05F7,
  x86_opcode_idiv_eax_rm                = 0x07F7,
  x86_opcode_add_rm_imm                 = 0x0081,
  x86_opcode_or_rm_imm                  = 0x0181,
  x86_opcode_adc_rm_imm                 = 0x0281,
  x86_opcode_sbb_rm_imm                 = 0x0381,
  x86_opcode_and_rm_imm                 = 0x0481,
  x86_opcode_sub_rm_imm                 = 0x0581,
  x86_opcode_xor_rm_imm                 = 0x0681,
  x86_opcode_cmp_rm_imm                 = 0x0781,
  x86_opcode_add_reg_rm                 = 0x03,
  x86_opcode_adc_reg_rm                 = 0x13,
  x86_opcode_and_reg_rm                 = 0x23,
  x86_opcode_or_reg_rm                  = 0x0B,
  x86_opcode_sub_reg_rm                 = 0x2B,
  x86_opcode_sbb_reg_rm                 = 0x1B,
  x86_opcode_xor_reg_rm                 = 0x33,
  x86_opcode_cmp_reg_rm                 = 0x39,
  x86_opcode_lea_reg_rm                 = 0x8D,
  x86_opcode_j                          = 0x80,
  x86_opcode_cdq                        = 0x99,
  x86_opcode_jecxz                      = 0xE3,
  x86_opcode_jmp                        = 0xE9,
  x86_opcode_jmp_reg                    = 0x04FF,
  x86_opcode_ext                        = 0x0F
} x86_opcodes;

typedef enum
{
  x86_opcode_cmov_base                  = 0x40,
  x86_opcode_cmovc                      = 0x42,
  x86_opcode_cmovnc                     = 0x43,
  x86_opcode_cmovnl                     = 0x4D,
  x86_opcode_set_base                   = 0x90,
  x86_opcode_seto                       = 0x90,
  x86_opcode_setno                      = 0x91,
  x86_opcode_setc                       = 0x92,
  x86_opcode_setnc                      = 0x93,
  x86_opcode_setz                       = 0x94,
  x86_opcode_setnz                      = 0x95,
  x86_opcode_setna                      = 0x96,
  x86_opcode_seta                       = 0x97,
  x86_opcode_sets                       = 0x98,
  x86_opcode_setns                      = 0x99,
  x86_opcode_movzxb                     = 0xB6,
  x86_opcode_movzxw                     = 0xB7,
  x86_opcode_bt                         = 0xBA,
} x86_ext_opcodes;

typedef enum
{
  x86_condition_code_o                  = 0x00,
  x86_condition_code_no                 = 0x01,
  x86_condition_code_c                  = 0x02,
  x86_condition_code_nc                 = 0x03,
  x86_condition_code_z                  = 0x04,
  x86_condition_code_nz                 = 0x05,
  x86_condition_code_na                 = 0x06,
  x86_condition_code_a                  = 0x07,
  x86_condition_code_s                  = 0x08,
  x86_condition_code_ns                 = 0x09,
  x86_condition_code_p                  = 0x0A,
  x86_condition_code_np                 = 0x0B,
  x86_condition_code_l                  = 0x0C,
  x86_condition_code_nl                 = 0x0D,
  x86_condition_code_ng                 = 0x0E,
  x86_condition_code_g                  = 0x0F
} x86_condition_codes;

#define x86_mod_rm(mod, rm, spare)  (((mod) << 6) | ((spare) << 3) | (rm))

class X86Emitter : public CodeEmitterBase {
private:

  inline void x86_emit_dword(uint32_t value) {
    *this->emit_ptr++ = value >>  0;
    *this->emit_ptr++ = value >>  8;
    *this->emit_ptr++ = value >> 16;
    *this->emit_ptr++ = value >> 24;
  }

  inline void x86_emit_memop(x86_regnum dst, x86_regnum base, uint32_t offset) {
    if (!offset)
      *this->emit_ptr++ = x86_mod_rm(x86_mod_mem, base, dst);
    else if (((signed)offset < 127) && ((signed)offset > -128)) {
      *this->emit_ptr++ = x86_mod_rm(x86_mod_mem_disp8, base, dst);
      *this->emit_ptr++ = (char)offset;
    }
    else {
      *this->emit_ptr++ = x86_mod_rm(x86_mod_mem_disp32, base, dst);
      this->x86_emit_dword(offset);
    }
  }

  // Emits a 1 byte opcode instruction with two regs
  inline void emit_x86_1b_reg(x86_opcodes opcode, x86_regnum dst, x86_regnum src) {
    *this->emit_ptr++ = opcode;
    *this->emit_ptr++ = x86_mod_rm(x86_mod_reg, src, dst);
  }
  // Emits 2 byte opcode instruction (with just one reg)
  inline void emit_x86_2b_reg(x86_opcodes opcode, x86_regnum dst) {
    *this->emit_ptr++ = (opcode & 0xFF);
    *this->emit_ptr++ = x86_mod_rm(x86_mod_reg, dst, opcode >> 8);
  }
  // Emits 2 byte opcode instruction with reg and immediate (1 byte)
  inline void emit_x86_2b_reg_imm(x86_opcodes opcode, x86_regnum dst, uint8_t imm) {
    *this->emit_ptr++ = (opcode & 0xFF);
    *this->emit_ptr++ = x86_mod_rm(x86_mod_reg, dst, opcode >> 8);
    *this->emit_ptr++ = imm;
  }
  // Emits 2 byte opcode instruction with reg and immediate (32 bits)
  inline void emit_x86_2b_reg_imm32(x86_opcodes opcode, x86_regnum dst, uint32_t imm32) {
    *this->emit_ptr++ = (opcode & 0xFF);
    *this->emit_ptr++ = x86_mod_rm(x86_mod_reg, dst, opcode >> 8);
    this->x86_emit_dword(imm32);
  }

  // Emits a 1 byte opcode instruction with dest reg and source mem ref (base + offset)
  inline void emit_x86_1b_mem(x86_opcodes opcode, x86_regnum dst, x86_regnum base, uint32_t offset) {
    *this->emit_ptr++ = opcode;
    this->x86_emit_memop(dst, base, offset);
  }
  inline void emit_x86_2b_mem(x86_opcodes opcode, x86_regnum base, uint32_t offset) {
    *this->emit_ptr++ = opcode & 0xFF;
    this->x86_emit_memop((x86_regnum)(opcode >> 8), base, offset);
  }

public:

  X86Emitter(uint8_t *emit_ptr, uint8_t *emit_end)
   : CodeEmitterBase(emit_ptr, emit_end) {}

  // Move (load store, imm)
  inline void x86_emit_reg_mov(x86_regnum dst, x86_regnum src) {
    emit_x86_1b_reg(x86_opcode_mov_reg_rm, dst, src);
  }
  inline void x86_emit_reg_load(x86_regnum dst, x86_regnum base, uint32_t offset) {
    emit_x86_1b_mem(x86_opcode_mov_reg_rm, dst, base, offset);
  }
  inline void x86_emit_reg_store(x86_regnum src, x86_regnum base, uint32_t offset) {
    emit_x86_1b_mem(x86_opcode_mov_rm_reg, src, base, offset);
  }
  inline void x86_emit_reg_loadub(x86_regnum dst, x86_regnum base, uint32_t offset) {
    *this->emit_ptr++ = x86_opcode_ext;
    emit_x86_1b_mem((x86_opcodes)x86_opcode_movzxb, dst, base, offset);
  }
  inline void x86_emit_load_imm(x86_regnum dst, uint32_t value) {
    *this->emit_ptr++ = x86_opcode_mov_reg_imm | dst;
    this->x86_emit_dword(value);
  }
  inline void x86_emit_store_imm32(uint32_t imm32, x86_regnum base, uint32_t offset) {
    this->emit_x86_2b_mem(x86_opcode_mov_rm_imm, base, offset);
    this->x86_emit_dword(imm32);
  }

  // Logic instructions
  inline void x86_emit_reg_and(x86_regnum dst, x86_regnum src) {
    emit_x86_1b_reg(x86_opcode_and_reg_rm, dst, src);
  }
  inline void x86_emit_reg_xor(x86_regnum dst, x86_regnum src) {
    emit_x86_1b_reg(x86_opcode_xor_reg_rm, dst, src);
  }
  inline void x86_emit_reg_or(x86_regnum dst, x86_regnum src) {
    emit_x86_1b_reg(x86_opcode_or_reg_rm, dst, src);
  }
  inline void x86_emit_mem_and(x86_regnum dst, x86_regnum base, uint32_t offset) {
    emit_x86_1b_mem(x86_opcode_and_reg_rm, dst, base, offset);
  }
  inline void x86_emit_mem_xor(x86_regnum dst, x86_regnum base, uint32_t offset) {
    emit_x86_1b_mem(x86_opcode_xor_reg_rm, dst, base, offset);
  }
  inline void x86_emit_mem_or(x86_regnum dst, x86_regnum base, uint32_t offset) {
    emit_x86_1b_mem(x86_opcode_or_reg_rm, dst, base, offset);
  }
  inline void x86_emit_imm_and(x86_regnum dst, uint32_t imm32) {
    emit_x86_2b_reg_imm32(x86_opcode_and_rm_imm, dst, imm32);
  }
  inline void x86_emit_imm_xor(x86_regnum dst, uint32_t imm32) {
    emit_x86_2b_reg_imm32(x86_opcode_xor_rm_imm, dst, imm32);
  }
  inline void x86_emit_imm_or(x86_regnum dst, uint32_t imm32) {
    emit_x86_2b_reg_imm32(x86_opcode_or_rm_imm, dst, imm32);
  }
  inline void x86_emit_mem_imm_and(uint32_t imm32, x86_regnum base, uint32_t offset) {
    this->emit_x86_2b_mem(x86_opcode_and_rm_imm, base, offset);
    this->x86_emit_dword(imm32);
  }

  // Shift instructions
  inline void x86_emit_reg_shr(x86_regnum dst) {
    emit_x86_2b_reg(x86_opcode_shr_reg_rm, dst);
  }
  inline void x86_emit_reg_sar(x86_regnum dst) {
    emit_x86_2b_reg(x86_opcode_sar_reg_rm, dst);
  }
  inline void x86_emit_reg_shl(x86_regnum dst) {
    emit_x86_2b_reg(x86_opcode_shl_reg_rm, dst);
  }
  inline void x86_emit_reg_ror(x86_regnum dst) {
    emit_x86_2b_reg(x86_opcode_ror_reg_rm, dst);
  }
  inline void x86_emit_reg_rcr(x86_regnum dst) {
    emit_x86_2b_reg(x86_opcode_rcr_reg1, dst);
  }
  inline void x86_emit_reg_shr_imm(x86_regnum dst, uint8_t imm) {
    emit_x86_2b_reg_imm(x86_opcode_shr_reg_imm, dst, imm);
  }
  inline void x86_emit_reg_sar_imm(x86_regnum dst, uint8_t imm) {
    emit_x86_2b_reg_imm(x86_opcode_sar_reg_imm, dst, imm);
  }
  inline void x86_emit_reg_shl_imm(x86_regnum dst, uint8_t imm) {
    emit_x86_2b_reg_imm(x86_opcode_shl_reg_imm, dst, imm);
  }
  inline void x86_emit_reg_ror_imm(x86_regnum dst, uint8_t imm) {
    emit_x86_2b_reg_imm(x86_opcode_ror_reg_imm, dst, imm);
  }

  // Arithmetic instructions
  inline void x86_emit_reg_add(x86_regnum dst, x86_regnum src) {
    emit_x86_1b_reg(x86_opcode_add_reg_rm, dst, src);
  }
  inline void x86_emit_reg_sub(x86_regnum dst, x86_regnum src) {
    emit_x86_1b_reg(x86_opcode_sub_reg_rm, dst, src);
  }
  inline void x86_emit_reg_adc(x86_regnum dst, x86_regnum src) {
    emit_x86_1b_reg(x86_opcode_adc_reg_rm, dst, src);
  }
  inline void x86_emit_reg_sbb(x86_regnum dst, x86_regnum src) {
    emit_x86_1b_reg(x86_opcode_sbb_reg_rm, dst, src);
  }
  inline void x86_emit_reg_cmp(x86_regnum dst, x86_regnum src) {
    emit_x86_1b_reg(x86_opcode_cmp_reg_rm, dst, src);
  }
  inline void x86_emit_reg_test(x86_regnum dst, x86_regnum src) {
    emit_x86_1b_reg(x86_opcode_test_reg_rm, dst, src);
  }
  inline void x86_emit_mem_add(x86_regnum dst, x86_regnum base, uint32_t offset) {
    emit_x86_1b_mem(x86_opcode_add_reg_rm, dst, base, offset);
  }
  inline void x86_emit_mem_sub(x86_regnum dst, x86_regnum base, uint32_t offset) {
    emit_x86_1b_mem(x86_opcode_sub_reg_rm, dst, base, offset);
  }
  inline void x86_emit_mem_cmp(x86_regnum dst, x86_regnum base, uint32_t offset) {
    emit_x86_1b_mem(x86_opcode_cmp_reg_rm, dst, base, offset);
  }
  inline void x86_emit_imm_add(x86_regnum dst, uint32_t imm32) {
    emit_x86_2b_reg_imm32(x86_opcode_add_rm_imm, dst, imm32);
  }
  inline void x86_emit_imm_sub(x86_regnum dst, uint32_t imm32) {
    emit_x86_2b_reg_imm32(x86_opcode_sub_rm_imm, dst, imm32);
  }
  inline void x86_emit_imm_adc(x86_regnum dst, uint32_t imm32) {
    emit_x86_2b_reg_imm32(x86_opcode_adc_rm_imm, dst, imm32);
  }
  inline void x86_emit_imm_sbb(x86_regnum dst, uint32_t imm32) {
    emit_x86_2b_reg_imm32(x86_opcode_sbb_rm_imm, dst, imm32);
  }
  inline void x86_emit_imm_cmp(x86_regnum dst, uint32_t imm32) {
    emit_x86_2b_reg_imm32(x86_opcode_cmp_rm_imm, dst, imm32);
  }
  inline void x86_emit_imm_test(x86_regnum dst, uint32_t imm32) {
    emit_x86_2b_reg_imm32(x86_opcode_test_rm_imm, dst, imm32);
  }
  inline void x86_emit_reg_neg(x86_regnum dst) {
    emit_x86_2b_reg(x86_opcode_neg_rm, dst);
  }
  inline void x86_emit_reg_not(x86_regnum dst) {
    emit_x86_2b_reg(x86_opcode_not_rm, dst);
  }

  inline void x86_emit_mem_imm_add(uint32_t imm32, x86_regnum base, uint32_t offset) {
    this->emit_x86_2b_mem(x86_opcode_add_rm_imm, base, offset);
    this->x86_emit_dword(imm32);
  }
  inline void x86_emit_mem_imm_sub(uint32_t imm32, x86_regnum base, uint32_t offset) {
    this->emit_x86_2b_mem(x86_opcode_sub_rm_imm, base, offset);
    this->x86_emit_dword(imm32);
  }

  inline void x86_emit_mul_eax(x86_regnum src) {
    emit_x86_2b_reg(x86_opcode_mul_eax_rm, src);
  }
  inline void x86_emit_imul_eax(x86_regnum src) {
    emit_x86_2b_reg(x86_opcode_imul_eax_rm, src);
  }
  inline void x86_emit_idiv_eax(x86_regnum src) {
    emit_x86_2b_reg(x86_opcode_idiv_eax_rm, src);
  }

  // Misc stuff
  inline void x86_emit_setcc_mem(x86_condition_codes code, x86_regnum base, uint32_t offset) {
    x86_opcodes opc2 = (x86_opcodes)(x86_opcode_set_base + code);
    *this->emit_ptr++ = x86_opcode_ext;
    this->emit_x86_1b_mem(opc2, x86_reg_eax, base, offset);
  }
  inline void x86_emit_reg_cmov(x86_condition_codes code, x86_regnum dst, x86_regnum src) {
    x86_opcodes opc2 = (x86_opcodes)(x86_opcode_cmov_base + code);
    *this->emit_ptr++ = x86_opcode_ext;
    this->emit_x86_1b_reg(opc2, dst, src);
  }
  inline void x86_emit_reg_bittest(x86_regnum src, uint8_t bitnum) {
    *this->emit_ptr++ = x86_opcode_ext;
    this->emit_x86_1b_reg((x86_opcodes)x86_opcode_bt, (x86_regnum)0x04, src);
    *this->emit_ptr++ = bitnum;
  }
  inline void x86_emit_mem_bittest(x86_regnum base, uint32_t offset, uint8_t bitnum) {
    *this->emit_ptr++ = x86_opcode_ext;
    emit_x86_1b_mem((x86_opcodes)x86_opcode_bt, (x86_regnum)0x04, base, offset);
    *this->emit_ptr++ = bitnum;
  }
  inline void x86_emit_call(uint32_t offset) {
    *this->emit_ptr++ = x86_opcode_call_offset;
    this->x86_emit_dword(offset);
  }
  inline void x86_emit_lea(x86_regnum dst, x86_regnum base, uint32_t offset) {
    emit_x86_1b_mem(x86_opcode_lea_reg_rm, dst, base, offset);
  }

  // Misc single opcodes
  inline void x86_emit_cdq() { *this->emit_ptr++ = x86_opcode_cdq; }
  inline void x86_emit_cmc() { *this->emit_ptr++ = x86_opcode_cmc; }

};

#define x86_relative_offset(source, offset, next)                             \
  ((uint32_t)((uintptr_t)offset - ((uintptr_t)source + next)))

#define generate_branch_patch_jecxz(dest, offset)                             \
  *((uint8_t *)(dest)) = x86_relative_offset(dest, offset, 1)

#define generate_branch_patch_conditional(dest, offset)                       \
  *((uint32_t *)(dest)) = x86_relative_offset(dest, offset, 4)

#define generate_branch_patch_unconditional(dest, offset)                     \
  *((uint32_t *)(dest)) = x86_relative_offset(dest, offset, 4)


#define x86_emit_byte(value)                                                  \
  *this->emit_ptr++ = value;                                                  \

#define mx86_emit_dword(value)                                                \
  *((uint32_t *)this->emit_ptr) = value;                                      \
  this->emit_ptr += 4                                                         \

#define x86_emit_jecxz_filler(writeback_location)                             \
  x86_emit_byte(x86_opcode_jecxz);                                            \
  (writeback_location) = this->emit_ptr;                                      \
  this->emit_ptr++;                                                           \

#define x86_emit_j_filler(condition_code, writeback_location)                 \
  x86_emit_byte(x86_opcode_ext);                                              \
  x86_emit_byte(x86_opcode_j | condition_code);                               \
  (writeback_location) = this->emit_ptr;                                      \
  this->emit_ptr += 4                                                         \

#define x86_emit_j_offset(condition_code, offset)                             \
  x86_emit_byte(x86_opcode_ext);                                              \
  x86_emit_byte(x86_opcode_j | condition_code);                               \
  mx86_emit_dword(offset)                                                     \

#define x86_emit_jmp_filler(writeback_location)                               \
  x86_emit_byte(x86_opcode_jmp);                                              \
  (writeback_location) = this->emit_ptr;                                      \
  this->emit_ptr += 4                                                         \

#define x86_emit_jmp_offset(offset)                                           \
  x86_emit_byte(x86_opcode_jmp);                                              \
  mx86_emit_dword(offset)                                                     \

#define generate_function_call(faddr)                                         \
  x86_emit_call(x86_relative_offset(this->emit_ptr, faddr, 5));               \

#endif

