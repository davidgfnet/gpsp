/* gameplaySP
 *
 * Copyright (C) 2006 Exophase <exophase@gmail.com>
 * Copyright (C) 2023 David Guillen Fandos <david@davidgf.net>
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

#include "common.h"
#include "decoder.h"
#include "gba_memory_cpp.h"
#include "cpu_instrument.h"

// Flag management
enum FlagNum {
  FLAG_N = 31,
  FLAG_Z = 30,
  FLAG_C = 29,
  FLAG_V = 28,
};

// Returns a bit (0/1) with the value of the specified flag bit.
template<enum FlagNum flagn>
inline static u32 read_flag() {
  return ((reg[REG_CPSR] >> flagn) & 1);
}

// Returns a boolean indicating whether the flag is set.
template<enum FlagNum flagn>
inline static bool isset_flag() {
  return (reg[REG_CPSR] & (1 << flagn)) != 0;
}

// Sets the flag to 0 or 1.
template<enum FlagNum flagn>
inline static void set_flag(bool value) {
  if (value)
    reg[REG_CPSR] |=  (1 << flagn);
  else
    reg[REG_CPSR] &= ~(1 << flagn);
}

// Calculates zero and negative flags given a uint32 value.
inline static void set_NZ_flags(u32 value) {
  set_flag<FLAG_Z>(value == 0);
  set_flag<FLAG_N>(value & 0x80000000);
}

// Reads a register accounting for PC offset if necessary.
template <u32 pc_offset>
inline static u32 read_reg(u32 rn) {
  u32 value = reg[rn];
  return value + ((rn == REG_PC) ? pc_offset : 0);
}

// Mode changes (used when rd==REG_PC and using flag set mode)
// In non-user mode it restores to the previous mode

inline static cpu_alert_type process_spsr_restore() {
  if (reg[CPU_MODE] != MODE_USER && reg[CPU_MODE] != MODE_SYSTEM) {
    // Restore the CPSR from the SPSR buffer.
    reg[REG_CPSR] = REG_SPSR(reg[CPU_MODE]);
    // Restore the corresponding mode (and its registers)
    set_cpu_mode(cpu_modes[reg[REG_CPSR] & 0xF]);
    // Check if we have pending interrupts (since I bit might be different).
    return check_interrupt();
  }
  return CPU_ALERT_NONE;
}

// Calculate whether this instruction must be nullified (due to condition code)
inline static bool arm_null_inst(const ARMInst &inst) {
  switch (inst.cond()) {
    case 0x0:            /* EQ */
       return !isset_flag<FLAG_Z>();
    case 0x1:            /* NE */
       return isset_flag<FLAG_Z>();
    case 0x2:            /* CS */
       return !isset_flag<FLAG_C>();
    case 0x3:            /* CC */
       return isset_flag<FLAG_C>();
    case 0x4:            /* MI */
       return !isset_flag<FLAG_N>();
    case 0x5:            /* PL */
       return isset_flag<FLAG_N>();
    case 0x6:            /* VS */
       return !isset_flag<FLAG_V>();
    case 0x7:            /* VC */
       return isset_flag<FLAG_V>();
    case 0x8:            /* HI */
       return !isset_flag<FLAG_C>() || isset_flag<FLAG_Z>();
    case 0x9:            /* LS  */
       return isset_flag<FLAG_C>() && !isset_flag<FLAG_Z>();
    case 0xA:            /* GE  */
       return isset_flag<FLAG_N>() != isset_flag<FLAG_V>();
    case 0xB:            /* LT  */
       return isset_flag<FLAG_N>() == isset_flag<FLAG_V>();
    case 0xC:            /* GT */
       return isset_flag<FLAG_Z>() || (isset_flag<FLAG_N>() != isset_flag<FLAG_V>());
    case 0xD:            /* LE */
       return !isset_flag<FLAG_Z>() && (isset_flag<FLAG_N>() == isset_flag<FLAG_V>());
    case 0xE:            /* AL */
       return false;
    case 0xF:            /* Reserved - treat as "never" */
    default:
       return true;
  };
}

#define check_pc_region() {                                                   \
  u32 new_pc_region = (reg[REG_PC] >> 15);                                    \
  if(new_pc_region != pc_region)                                              \
  {                                                                           \
    pc_region = new_pc_region;                                                \
    pc_address_block = memory_map_read[new_pc_region];                        \
    touch_gamepak_page(pc_region);                                            \
                                                                              \
    if(!pc_address_block)                                                     \
      pc_address_block = load_gamepak_page(pc_region & 0x3FF);                \
  }                                                                           \
}

#define arm_pc_offset(val)                                                    \
  reg[REG_PC] += val                                                          \

#define thumb_pc_offset(val)                                                  \
  reg[REG_PC] += val                                                          \

typedef enum { MulReg, MulAdd } MulMode;
typedef enum { SiSigned, SiUnsigned } SignMode;
typedef enum { ShfLSL, ShfLSR, ShfASR, ShfROR } ShiftMode;
typedef enum { LgcAnd, LgcOrr, LgcXor, LgcBic, LgcMul, LgcNot, LgcMov } LogicMode;
typedef enum { FlagsSet, FlagsIgnore } FlagMode;
typedef enum { OpDirect, OpReverse } OperandMode;
typedef enum { Op2Reg, Op2Imm } ArmOp2;
typedef enum { Op2PlusReg, Op2MinusReg, Op2PlusImm, Op2MinusImm,
               HOp2PlusReg, HOp2MinusReg, HOp2PlusImm, HOp2MinusImm } MemOp2;
typedef enum { MemIdxPre, MemIdxPreWB, MemIdxPostWB } MemIdxMode;
typedef enum { AccLoad, AccStore } AccMode;
typedef enum { AddrPreInc, AddrPreDec, AddrPostInc, AddrPostDec } AddrMode;

// Calculates operand 2 when register is shifted/rotated by an immediate.
template<FlagMode fm>
inline static u32 calc_op2_shimm(const ARMInst &it) {
  u32 imm = it.op2sa();      // Shift amount [0..31]
  u32 rmval = reg[it.rm()];  // Register to shift/rotate.
  bool cflag = isset_flag<FLAG_C>();

  switch (it.op2smode()) {
  case 0:      /* LSL */
    if (imm)
      cflag = (rmval >> (32 - imm)) & 1;
    rmval <<= imm;
    break;
  case 1:      /* LSR (0 means shift by 32) */
    cflag = (rmval >> (imm - 1)) & 1;
    rmval = imm ? (rmval >> imm) : 0;
    break;
  case 2:      /* ASR (0 is also shift by 32) */
    if (imm) {
      cflag = (rmval >> (imm - 1)) & 1;
      rmval = (s32)rmval >> imm;
    } else {
      cflag = rmval >> 31;
      rmval = (s32)rmval >> 31;
    }
    break;
  case 3:      /* ROR */
    if (imm) {
      cflag = (rmval >> (imm - 1)) & 1;
      rmval = rotr32(rmval, imm);
    } else {   /* RRX special case, rotate through carry bit */
      u32 old_c_flag = cflag ? 1 : 0;
      cflag = rmval & 1;
      rmval = (rmval >> 1) | (old_c_flag << 31);
    }
    break;
  };

  // Update the flags if needed
  if (fm == FlagsSet)
    set_flag<FLAG_C>(cflag);

  return rmval;
}

// Calculates operand 2 when register is shifted/rotated by another register.
template<FlagMode fm>
inline static u32 calc_op2_shreg(const ARMInst &it) {
  u32 rmval = reg[it.rm()];  // Register to shift/rotate.

  u32 amount = reg[it.rs()]; // Register that contains the rotation amount
  if (it.rs() == REG_PC)     // Correct for PC value
    amount += 4;
  amount &= 0xff;            // Only the 8 LSB are meaningful for this operation

  if (amount) {
    bool cflag;

    switch (it.op2smode()) {
    case 0:      /* LSL */
      if (amount <= 31) {
        cflag = (rmval >> (32 - amount)) & 1;
        rmval <<= amount;
      } else {
        cflag = (amount == 32) ? (rmval & 1) : false;
        rmval = 0;
      }
      break;
    case 1:      /* LSR */
      if (amount <= 31) {
        cflag = (rmval >> (amount - 1)) & 1;
        rmval >>= amount;
      } else {
        cflag = (amount == 32) ? (rmval >> 31) : false;
        rmval = 0;
      }
      break;
    case 2:      /* ASR */
      if (amount <= 31) {
        cflag = (rmval >> (amount - 1)) & 1;
        rmval = (s32)rmval >> amount;
      } else {
        rmval = (s32)rmval >> 31;
        cflag = rmval;
      }
      break;
    case 3:      /* ROR */
      cflag = (rmval >> ((amount - 1) & 31)) & 1;
      rmval = rotr32(rmval, (amount & 31));
      break;
    };

    if (fm == FlagsSet)
      set_flag<FLAG_C>(cflag);
  }

  return rmval;
}

// Calculates the Operand2 value for the ARM instruction. Updates C flag
// accordingly.
template<FlagMode fm, ArmOp2 op2m>
inline static u32 calculate_op2(const ARMInst &it) {
  if (op2m == Op2Imm) {
    // Op2 is a 4+8 immediate (8 bit with 16 possible rotations).
    u32 sa = it.rot4() * 2;
    u32 res = rotr32(it.imm8(), sa);

    // Op2 sets the carry flag, out of the rotation operation.
    if (fm == FlagsSet && sa != 0)
      set_flag<FLAG_C>(res >> 31);
    return res;
  } else {
    // Op2 is a register with a rot/shift by another reg or immediate.
    return it.op2imm() ? calc_op2_shimm<fm>(it) : calc_op2_shreg<fm>(it);
  }
}

// Performs all arm logic operations (result + flags)
template<LogicMode mode, FlagMode fm, ArmOp2 op2m>
inline static cpu_alert_type arm_logic(const ARMInst &it) {
  arm_pc_offset(8);     // Reading the PC should read PC+8

  // Calculate the 2nd operand, according to mode.
  u32 op2v = calculate_op2<fm, op2m>(it);

  u32 res;
  switch (mode) {
  case LgcAnd: res = reg[it.rn()] & op2v; break;
  case LgcOrr: res = reg[it.rn()] | op2v; break;
  case LgcXor: res = reg[it.rn()] ^ op2v; break;
  case LgcBic: res = reg[it.rn()] & (~op2v); break;
  case LgcNot: res = ~op2v; break;
  case LgcMov: res =  op2v; break;
  };

  if (fm == FlagsSet)
    set_NZ_flags(res);

  arm_pc_offset(-4);
  reg[it.rd()] = res;

  if (fm == FlagsSet && it.rd() == REG_PC)
    return process_spsr_restore();

  return CPU_ALERT_NONE;
}

// Performs tst/teq operations (only updates flags)
template<LogicMode mode, ArmOp2 op2m>
inline static void arm_logic_test(const ARMInst &it) {
  arm_pc_offset(8);     // Reading the PC should read PC+8

  // Calculate the 2nd operand, according to mode.
  u32 op2v = calculate_op2<FlagsSet, op2m>(it);

  u32 res;
  switch (mode) {
  case LgcAnd: res = reg[it.rn()] & op2v; break;
  case LgcXor: res = reg[it.rn()] ^ op2v; break;
  };

  set_NZ_flags(res);
  arm_pc_offset(-4);
}

// Performs add/adc/cmn operations
template<FlagMode fm, ArmOp2 op2m, bool writeback>
inline static cpu_alert_type arm_add(const ARMInst &it, bool cin) {
  arm_pc_offset(8);     // Reading the PC should read PC+8

  // Calculate the 2nd operand, according to mode.
  u32 op1v = reg[it.rn()];
  u32 op2v = calculate_op2<fm, op2m>(it);

  // Calculate the result and its carry as well.
  u32 res = op1v + op2v;
  bool cout = res < op2v;
  if (cin) {
    res++;
    if (!res)
      cout = true;
  }

  arm_pc_offset(-4);
  if (writeback)
    reg[it.rd()] = res;

  if (fm == FlagsSet) {
    set_NZ_flags(res);
    set_flag<FLAG_C>(cout);
    set_flag<FLAG_V>((~((op1v) ^ (op2v)) & ((op1v) ^ (res))) & 0x80000000);

    if (it.rd() == REG_PC)
      return process_spsr_restore();
  }
  return CPU_ALERT_NONE;
}

// Performs sub/sbc/cmp operations
template<FlagMode fm, ArmOp2 op2m, OperandMode opm, bool writeback>
inline static cpu_alert_type arm_sub(const ARMInst &it, bool bin) {
  arm_pc_offset(8);     // Reading the PC should read PC+8

  // Calculate the 2nd operand, according to mode.
  u32 regv = reg[it.rn()];
  u32 op2v = calculate_op2<fm, op2m>(it);

  u32 opn1 = opm == OpDirect ? regv : op2v;
  u32 opn2 = opm == OpDirect ? op2v : regv;

  // Calculate the result and its carry as well.
  u32 res = opn1 + ~opn2 + (bin ? 1 : 0);

  arm_pc_offset(-4);
  if (writeback)
    reg[it.rd()] = res;

  if (fm == FlagsSet) {
    set_NZ_flags(res);
    set_flag<FLAG_C>((bin) ? (opn2 <= opn1) : (opn2 < opn1));
    set_flag<FLAG_V>(((opn1 ^ opn2) & (opn1 ^ res)) & 0x80000000);

    if (it.rd() == REG_PC)
      return process_spsr_restore();
  }
  return CPU_ALERT_NONE;
}

// Performs 32 bit multiplications (rd and rn are swapped)
template<FlagMode fm, MulMode mm>
inline static void arm_mul32(const ARMInst &it) {
  u32 res = reg[it.rm()] * reg[it.rs()];
  if (mm == MulAdd)
    res += reg[it.rd()];

  if (fm == FlagsSet)
    set_NZ_flags(res);
  reg[it.rn()] = res;
  arm_pc_offset(4);
}

// Performs 64 bit multiplications
template<FlagMode fm, MulMode mm, SignMode sm>
inline static void arm_mul64(const ARMInst &it) {
  u64 res = (sm == SiUnsigned) ? (u64)reg[it.rm()] * (u64)reg[it.rs()] :
                (s64)((s32)reg[it.rm()]) * (s64)((s32)reg[it.rs()]);

  if (mm == MulAdd)
    res += ((u64)reg[it.rdhi()] << 32) | reg[it.rdlo()];

  if (fm == FlagsSet) {
    set_flag<FLAG_Z>(res == 0);
    set_flag<FLAG_N>(res & 0x8000000000000000);
  }

  reg[it.rdhi()] = res >> 32;
  reg[it.rdlo()] = res & 0xFFFFFFFF;
  arm_pc_offset(4);
}

// Writes CPSR and SPSR registers
inline static cpu_alert_type cpsr_write(const ARMInst &it, u32 wval) {
  const u32 smask = cpsr_masks[it.psr_field()][PRIVMODE(reg[CPU_MODE])];
  reg[REG_CPSR] = (wval & smask) | (reg[REG_CPSR] & (~smask));

  arm_pc_offset(4);

  // Writing the CPU mode and/or Interrupt flags could mean a mode change or
  // an interrupt triggering.
  if (smask & 0xFF) {
    set_cpu_mode(cpu_modes[reg[REG_CPSR] & 0xF]);
    return check_interrupt();
  }
  return CPU_ALERT_NONE;
}

inline static void spsr_write(const ARMInst &it, u32 wval) {
  const u32 smask = spsr_masks[it.psr_field()];
  const u32 cur_spsr = REG_SPSR(reg[CPU_MODE]);
  REG_SPSR(reg[CPU_MODE]) = (wval & smask) | (cur_spsr & (~smask));
  arm_pc_offset(4);
}

template <typename memtype>
u32 perform_memload(u32 address) {
  u8 region = address >> 24;
  const u32 align_mask = sizeof(memtype) - 1;  // 0, 1, 3 for each type

  bool bad_bios = (region == 0) && (reg[REG_PC] >= 0x4000);
  bool unaligned = (address & align_mask) != 0;
  bool outofrange = (address & 0xF0000000) != 0;

  if (bad_bios || unaligned || outofrange)
    return read_memcb<memtype>(address);

  const u8 *map = memory_map_read[address >> 15];
  if (!map)
    return read_memcb<memtype>(address);

  return read_mem<memtype>(map, address & 0x7FFF);
}

template <typename memtype>
cpu_alert_type perform_memstore(u32 address, u32 data) {
  // Align address to data type
  address &= ~(sizeof(memtype)-1);
  // Clear out the 4 MSB as well since they can be safely ignored.
  // TODO Is this OK?
  // address &= ~0xF0000000;

  return write_memcb<memtype>(address, (memtype)data);
}

template<typename memmode>
inline static cpu_alert_type arm_swap(const ARMInst &it, s32 &cyccnt) {
  u32 tmp = perform_memload<memmode>(read_reg<8>(it.rn()));
  cpu_alert_type ret = perform_memstore<memmode>(read_reg<8>(it.rn()), read_reg<8>(it.rm()));
  reg[it.rd()] = tmp;

  arm_pc_offset(4);
  return ret;
}

template<AccMode mode, typename memmode>
inline static cpu_alert_type thumb_memop(u32 rd, u32 addr, s32 &cyccnt) {
  u8 region = addr >> 24;

  thumb_pc_offset(2);  // Advance PC

  // Account for access timing
  if (region < 16)
    cyccnt -= ws_cyc_nseq[region][sizeof(memmode) / 4];

  if (mode == AccStore)
    return perform_memstore<memmode>(addr, reg[rd]);

  reg[rd] = perform_memload<memmode>(addr);
  return CPU_ALERT_NONE;
}

template<AccMode mode, typename memmode, MemOp2 op2m, MemIdxMode midx>
inline static cpu_alert_type arm_memop(const ARMInst &it, s32 &cyccnt) {
  arm_pc_offset(8);  // Advance PC

  // Offset can be:
  // - 12 bit offset
  // - Regmode flexible operand (reg shifted/rotated by 5 bit immediate)
  // - 8 bit immediate (for "Additional Memory Instructions")
  // - A register (for "Additional Memory Instructions")
  u32 offval = (op2m == Op2PlusImm)   ?  it.off12() :
               (op2m == Op2MinusImm)  ? -it.off12() :
               (op2m == Op2PlusReg)   ?  calc_op2_shimm<FlagsIgnore>(it) :
               (op2m == Op2MinusReg)  ? -calc_op2_shimm<FlagsIgnore>(it) :
               (op2m == HOp2PlusImm)  ?  it.off8() :
               (op2m == HOp2MinusImm) ? -it.off8() :
               (op2m == HOp2PlusReg)  ?  reg[it.rm()] :
                                        -reg[it.rm()];

  // Calculate the address (might use offset depending on the mode)
  u32 address = reg[it.rn()];
  if (midx == MemIdxPre || midx == MemIdxPreWB)
    address += offval;

  // Write back the address whenever necessary
  if (midx == MemIdxPreWB)
    reg[it.rn()] = address;
  else if (midx == MemIdxPostWB)
    reg[it.rn()] = address + offval;

  // Account for access timing
  u8 region = address >> 24;
  if (region < 16)
    cyccnt -= ws_cyc_nseq[region][sizeof(memmode) / 4];

  arm_pc_offset(-4);
  // TODO: Offset is really 12, but we use 8, since we already incremented by 4
  if (mode == AccStore)
    return perform_memstore<memmode>(address, read_reg<8>(it.rd()));

  reg[it.rd()] = perform_memload<memmode>(address);
  return CPU_ALERT_NONE;
}

// Excutes an LDM/STM instruction

template<AccMode mode, bool writeback, bool sbit, AddrMode addr_mode>
inline static cpu_alert_type arm_block_mem(const ARMInst &it, s32 &cyccnt) {
  cpu_alert_type cpu_alert = CPU_ALERT_NONE;
  u32 rn = it.rn();
  u32 reglist = it.rlist();

  // Register register usage stats.
  using_register(arm, rn, memory_base);
  using_register_list(arm, reglist, 16);

  // Calcualte base address.
  u32 base = reg[rn];
  u32 numops = (bit_count[reglist >> 8] + bit_count[reglist & 0xFF]);
  s32 addr_off = (addr_mode == AddrPreInc || addr_mode == AddrPostInc) ? 4 : -4;  // Address incr/decr amount.
  u32 endaddr = base + addr_off * numops;

  u32 address = (addr_mode == AddrPreInc)  ? base + 4 :
                (addr_mode == AddrPostInc) ? base :
                (addr_mode == AddrPreDec)  ? endaddr : endaddr + 4;
  address &= ~3U;

  // If sbit is set, change to user mode and back, so to write the user regs.
  // However for LDM {PC} we restore CPSR from SPSR.
  // TODO: implement CPSR restore, only USER mode is now implemented.
  u32 old_cpsr = reg[REG_CPSR];
  if (sbit && (mode == AccStore || rn != REG_PC))
    set_cpu_mode(MODE_USER);

  // If base is in the reglist and writeback is enabled, the value of the
  // written register depends on the write cycle (ARM7TDM manual 4.11.6).
  // If the register is the first, the written value is the original value,
  // otherwise the update base register is written. For LDM loaded date
  // takes always precendence.
  bool wrbck_base = (1 << rn) & reglist;
  bool base_first = (((1 << rn) - 1) & reglist) == 0;
  bool writeback_first = (mode == AccLoad) || !(wrbck_base && base_first);

  if (writeback && writeback_first)
    reg[rn] = endaddr;

  // Inaccuracy: we take the first address for timing calculation and scale it.
  u8 region = address >> 24;
  if (region < 16)
    cyccnt -= ws_cyc_seq[region][1] * numops;

  arm_pc_offset(4);  // Advance PC

  for (u32 i = 0; i < 16; i++)  {
    if ((reglist >> i) & 0x01) {
      if (mode == AccLoad)
        reg[i] = perform_memload<u32>(address);
      else
        cpu_alert |= perform_memstore<u32>(address, read_reg<4>(i));
      address += 4;
    }
  }

  if (writeback && !writeback_first)
    reg[rn] = endaddr;

  if (sbit) {
    if (mode == AccStore || rn != REG_PC)
      set_cpu_mode(cpu_modes[old_cpsr & 0xF]);
    else
      return process_spsr_restore();
  }

  return cpu_alert;
}

template<AccMode mode, AddrMode addr_mode>
inline static cpu_alert_type thumb_block_mem(u32 rn, u32 reglist, s32 &cyccnt) {
  cpu_alert_type cpu_alert = CPU_ALERT_NONE;
  // Register register usage stats.
  using_register(arm, rn, memory_base);
  using_register_list(arm, reglist, 16);

  // Calcualte base address.
  u32 base = reg[rn];
  u32 numops = bit_count[reglist & 0xFF] + (bit_count[reglist >> 8] ? 1 : 0);
  s32 addr_off = (addr_mode == AddrPreInc || addr_mode == AddrPostInc) ? 4 : -4;  // Address incr/decr amount.
  u32 endaddr = base + addr_off * numops;

  u32 address = (addr_mode == AddrPreInc)  ? base + 4 :
                (addr_mode == AddrPostInc) ? base :
                (addr_mode == AddrPreDec)  ? endaddr : endaddr + 4;
  address &= ~3U;

  // Similar to the ARM version, just a bit simpler. See above.
  bool wrbck_base = (1 << rn) & reglist;
  bool base_first = (((1 << rn) - 1) & reglist) == 0;
  bool writeback_first = (mode == AccLoad) || !(wrbck_base && base_first);

  if (writeback_first)
    reg[rn] = endaddr;

  // Inaccuracy: we take the first address for timing calculation and scale it.
  u8 region = address >> 24;
  if (region < 16)
    cyccnt -= ws_cyc_seq[region][1] * numops;

  thumb_pc_offset(2);  // Advance PC

  if (mode == AccLoad) {
    for (u32 i = 0; i < 8; i++)  {
      if ((reglist >> i) & 0x01) {
        reg[i] = perform_memload<u32>(address);
        address += 4;
      }
    }
    if (reglist & (1 << REG_PC))
      reg[REG_PC] = perform_memload<u32>(address) & ~1U;
  } else {
    for (u32 i = 0; i < 8; i++)  {
      if ((reglist >> i) & 0x01) {
        cpu_alert |= perform_memstore<u32>(address, reg[i]);
        address += 4;
      }
    }
    if (reglist & (1 << REG_LR))
      cpu_alert |= perform_memstore<u32>(address, reg[REG_LR]);
  }

  if (!writeback_first)
    reg[rn] = endaddr;

  return cpu_alert;
}

inline static void thumb_add(u32 rd, u32 op1v, u32 op2v, bool carry) {
  u32 res = op1v + op2v;
  bool caout = res < op2v;
  if (carry) {
    res++;
    if (!res)
      caout = true;
  }
  reg[rd] = res;

  set_NZ_flags(res);
  set_flag<FLAG_V>((~((op1v) ^ (op2v)) & ((op1v) ^ (res))) & 0x80000000);
  set_flag<FLAG_C>(caout);
  thumb_pc_offset(2);
}

inline static void thumb_sub(u32 rd, u32 op1v, u32 op2v, bool nborrow) {
  u32 res = op1v + ~op2v + (nborrow ? 1 : 0);
  reg[rd] = res;

  set_NZ_flags(res);
  set_flag<FLAG_C>(nborrow ? (op2v <= op1v) : op2v < op1v);
  set_flag<FLAG_V>(((op1v ^ op2v) & (~op2v ^ res)) & 0x80000000);
  thumb_pc_offset(2);
}

inline static void thumb_cmp(u32 op1v, u32 op2v) {
  u32 res = op1v - op2v;
  set_NZ_flags(res);
  set_flag<FLAG_C>(op2v <= op1v);
  set_flag<FLAG_V>(((op1v ^ op2v) & (~op2v ^ res)) & 0x80000000);
  thumb_pc_offset(2);
}

inline static void thumb_cmn(u32 op1v, u32 op2v) {
  u32 res = op1v + op2v;
  set_NZ_flags(res);
  set_flag<FLAG_C>(res < op1v);
  set_flag<FLAG_V>((~((op1v) ^ (op2v)) & ((op1v) ^ (res))) & 0x80000000);
  thumb_pc_offset(2);
}


template<LogicMode mode>
inline static void thumb_logic_reg(const ThumbInst &it) {
  using_register(thumb, it.rd(), op_src_dest);
  using_register(thumb, it.rs(), op_src);

  switch (mode) {
  case LgcAnd: reg[it.rd()] = reg[it.rd()] & reg[it.rs()]; break;
  case LgcOrr: reg[it.rd()] = reg[it.rd()] | reg[it.rs()]; break;
  case LgcXor: reg[it.rd()] = reg[it.rd()] ^ reg[it.rs()]; break;
  case LgcMul: reg[it.rd()] = reg[it.rd()] * reg[it.rs()]; break;
  case LgcBic: reg[it.rd()] = reg[it.rd()] & (~reg[it.rs()]); break;
  case LgcNot: reg[it.rd()] = ~reg[it.rs()]; break;
  };

  set_NZ_flags(reg[it.rd()]);
  thumb_pc_offset(2);
}

template<ShiftMode mode>
inline static void thumb_shift_imm(const ThumbInst &it) {
  using_register(thumb, it.rd(), op_dest);
  using_register(thumb, it.rs(), op_shift);

  switch (mode) {
  case ShfLSL:
    if (it.imm5())
      set_flag<FLAG_C>((reg[it.rs()] >> (32 - it.imm5())) & 1);
    reg[it.rd()] = reg[it.rs()] << it.imm5();
    break;

  case ShfLSR:
    set_flag<FLAG_C>((reg[it.rs()] >> ((it.imm5() - 1) & 31)) & 1);
    reg[it.rd()] = it.imm5() ? reg[it.rs()] >> it.imm5() : 0;
    break;

  case ShfASR:
    set_flag<FLAG_C>((reg[it.rs()] >> ((it.imm5() - 1) & 31)) & 1);
    reg[it.rd()] = (s32)reg[it.rs()] >> (it.imm5() ? it.imm5() : 31);
    break;
  };

  set_NZ_flags(reg[it.rd()]);
  thumb_pc_offset(2);
}

template<ShiftMode mode>
inline static void thumb_shift_reg(const ThumbInst &it) {
  using_register(thumb, it.rd(), op_src_dest);
  using_register(thumb, it.rs(), op_src);

  u32 shift = reg[it.rs()] & 0xFF;   // Only the LSB byte

  if (shift) {
    switch (mode) {
    case ShfLSL:
      if (shift > 32)
        set_flag<FLAG_C>(false);
      else
        set_flag<FLAG_C>((reg[it.rd()] >> (32 - shift)) & 1);

      reg[it.rd()] = (shift < 32) ? reg[it.rd()] << shift : 0;
      break;

    case ShfLSR:
      if (shift <= 32)
        set_flag<FLAG_C>((reg[it.rd()] >> (shift - 1)) & 1);
      else
        set_flag<FLAG_C>(false);
      reg[it.rd()] = (shift < 32) ? reg[it.rd()] >> shift : 0;
      break;

    case ShfASR:
      if (shift <= 32)
        set_flag<FLAG_C>((reg[it.rd()] >> (shift - 1)) & 1);
      else
        set_flag<FLAG_C>(reg[it.rd()] >> 31);
      reg[it.rd()] = (s32)reg[it.rd()] >> ((shift < 32) ? shift : 31);
      break;

   case ShfROR:
      set_flag<FLAG_C>((reg[it.rd()] >> (shift - 1)) & 1);
      reg[it.rd()] = rotr32(reg[it.rd()], shift);
      break;
    };
  }

  set_NZ_flags(reg[it.rd()]);
  thumb_pc_offset(2);
}

inline static u32 thumb_hireg_read(u32 rs) {
  return reg[rs] + ((rs == REG_PC) ? 4 : 0);
}

inline static void thumb_hireg_write(u32 rd, u32 value) {
  if (rd == REG_PC) {
    reg[REG_PC] = value & (~1U);
  } else {
    reg[rd] = value;
    thumb_pc_offset(2);
  }
}

// Operation types: imm, mem_reg, mem_imm

#define thumb_cond_br(condition)                                              \
{                                                                             \
  if(condition)                                                               \
  {                                                                           \
    thumb_pc_offset(inst.cbr_offset() + 4);                                   \
  }                                                                           \
  else                                                                        \
  {                                                                           \
    thumb_pc_offset(2);                                                       \
  }                                                                           \
  cyccnt -= ws_cyc_nseq[reg[REG_PC] >> 24][0];                                \
}                                                                             \

u32 instruction_count = 0;


#ifndef HAVE_DYNAREC
u8 *memory_map_read [8 * 1024];
u16 oam_ram[512];
u16 palette_ram[512];
u16 palette_ram_converted[512];
u8 ewram[1024 * 256 * 2];
u8 iwram[1024 * 32 * 2];
u8 vram[1024 * 96];
u16 io_registers[512];
#endif

cpu_alert_type execute_thumb_instruction(u16 opcode16, s32 &cyccnt) {
   const ThumbInst inst(opcode16);
   switch ((inst.opcode >> 8) & 0xFF)
   {
      case 0x00 ... 0x07:          /* LSL rd, rs, offset */
         thumb_shift_imm<ShfLSL>(inst);
         break;
      case 0x08 ... 0x0F:          /* LSR rd, rs, offset */
         thumb_shift_imm<ShfLSR>(inst);
         break;
      case 0x10 ... 0x17:          /* ASR rd, rs, offset */
         thumb_shift_imm<ShfASR>(inst);
         break;

      case 0x18 ... 0x19:          /* ADD rd, rs, rn */
         thumb_add(inst.rd(), reg[inst.rs()], reg[inst.rn()], false);
         break;
      case 0x1A ... 0x1B:          /* SUB rd, rs, rn */
         thumb_sub(inst.rd(), reg[inst.rs()], reg[inst.rn()], true);
         break;
      case 0x1C ... 0x1D:          /* ADD rd, rs, imm */
         thumb_add(inst.rd(), reg[inst.rs()], inst.imm3(), false);
         break;
      case 0x1E ... 0x1F:          /* SUB rd, rs, imm */
         thumb_sub(inst.rd(), reg[inst.rs()], inst.imm3(), true);
         break;

      case 0x20 ... 0x27:
         /* MOV r0..7, imm */
         reg[inst.rd8()] = inst.imm8();
         set_NZ_flags(inst.imm8());
         thumb_pc_offset(2);
         break;

      case 0x28 ... 0x2F:
         /* CMP r0..7, imm */
         thumb_cmp(reg[inst.rd8()], inst.imm8());
         break;

      case 0x30 ... 0x37:
         /* ADD r0..7, imm */
         thumb_add(inst.rd8(), reg[inst.rd8()], inst.imm8(), false);
         break;

      case 0x38 ... 0x3F:
         /* SUB r0..7, imm */
         thumb_sub(inst.rd8(), reg[inst.rd8()], inst.imm8(), true);
         break;

      case 0x40 ... 0x43:
         /* Arith/Logic reg-reg instructions */
         switch((inst.opcode >> 6) & 0xF) {
            case 0x00:             /* AND rd, rs */
               thumb_logic_reg<LgcAnd>(inst);
               break;
            case 0x01:             /* EOR rd, rs */
               thumb_logic_reg<LgcXor>(inst);
               break;
            case 0x02:             /* LSL rd, rs */
               thumb_shift_reg<ShfLSL>(inst);
               break;
            case 0x03:             /* LSR rd, rs */
               thumb_shift_reg<ShfLSR>(inst);
               break;
            case 0x04:             /* ASR rd, rs */
               thumb_shift_reg<ShfASR>(inst);
               break;
            case 0x05:             /* ADC rd, rs */
               thumb_add(inst.rd(), reg[inst.rd()], reg[inst.rs()], isset_flag<FLAG_C>());
               break;
            case 0x06:             /* SBC rd, rs */
               thumb_sub(inst.rd(), reg[inst.rd()], reg[inst.rs()], isset_flag<FLAG_C>());
               break;
            case 0x07:             /* ROR rd, rs */
               thumb_shift_reg<ShfROR>(inst);
               break;
            case 0x08:             /* TST rd, rs */
               set_NZ_flags(reg[inst.rd()] & reg[inst.rs()]); thumb_pc_offset(2);
               break;
            case 0x09:             /* NEG rd, rs */
               thumb_sub(inst.rd(), 0, reg[inst.rs()], true);
               break;
            case 0x0A:             /* CMP rd, rs */
               thumb_cmp(reg[inst.rd()], reg[inst.rs()]);
               break;
            case 0x0B:             /* CMN rd, rs */
               thumb_cmn(reg[inst.rd()], reg[inst.rs()]);
               break;
            case 0x0C:             /* ORR rd, rs */
               thumb_logic_reg<LgcOrr>(inst);
               break;
            case 0x0D:             /* MUL rd, rs */
               thumb_logic_reg<LgcMul>(inst);
               break;
            case 0x0E:             /* BIC rd, rs */
               thumb_logic_reg<LgcBic>(inst);
               break;
            case 0x0F:             /* MVN rd, rs */
               thumb_logic_reg<LgcNot>(inst);
               break;
         }
         break;

      case 0x44:         /* ADD rd, rs */
         thumb_hireg_write(inst.rd_hi(), thumb_hireg_read(inst.rd_hi()) + thumb_hireg_read(inst.rs_hi()));
         break;
      case 0x45:         /* CMP rd, rs */
         thumb_cmp(reg[inst.rd_hi()], thumb_hireg_read(inst.rs_hi()));
         break;
      case 0x46:         /* MOV rd, rs */
         thumb_hireg_write(inst.rd_hi(), thumb_hireg_read(inst.rs_hi()));
         break;

      case 0x47:         /* BX rs */
         {
            u32 newpc = thumb_hireg_read(inst.rs_hi());
            if (newpc & 0x01)
               reg[REG_PC] = newpc - 1;
            else {
               /* Switch to ARM mode */
               reg[REG_PC] = newpc;
               reg[REG_CPSR] &= ~0x20;
            }
         }
         break;

      case 0x48 ... 0x4F:          /* LDR r0..7, [pc + imm] */
         return thumb_memop<AccLoad, u32>(inst.rd8(), (reg[REG_PC] & ~3) + inst.imm8() * 4 + 4, cyccnt);
      case 0x50 ... 0x51:          /* STR rd, [rb + ro] */
         return thumb_memop<AccStore, u32>(inst.rd(), reg[inst.rb()] + reg[inst.ro()], cyccnt);
      case 0x52 ... 0x53:          /* STRH rd, [rb + ro] */
         return thumb_memop<AccStore, u16>(inst.rd(), reg[inst.rb()] + reg[inst.ro()], cyccnt);
      case 0x54 ... 0x55:          /* STRB rd, [rb + ro] */
         return thumb_memop<AccStore, u8>(inst.rd(), reg[inst.rb()] + reg[inst.ro()], cyccnt);
      case 0x56 ... 0x57:          /* LDSB rd, [rb + ro] */
         return thumb_memop<AccLoad, s8>(inst.rd(), reg[inst.rb()] + reg[inst.ro()], cyccnt);
      case 0x58 ... 0x59:          /* LDR rd, [rb + ro] */
         return thumb_memop<AccLoad, u32>(inst.rd(), reg[inst.rb()] + reg[inst.ro()], cyccnt);
      case 0x5A ... 0x5B:          /* LDRH rd, [rb + ro] */
         return thumb_memop<AccLoad, u16>(inst.rd(), reg[inst.rb()] + reg[inst.ro()], cyccnt);
      case 0x5C ... 0x5D:          /* LDRB rd, [rb + ro] */
         return thumb_memop<AccLoad, u8>(inst.rd(), reg[inst.rb()] + reg[inst.ro()], cyccnt);
      case 0x5E ... 0x5F:          /* LDSH rd, [rb + ro] */
         return thumb_memop<AccLoad, s16>(inst.rd(), reg[inst.rb()] + reg[inst.ro()], cyccnt);
      case 0x60 ... 0x67:          /* STR rd, [rb + imm] */
         return thumb_memop<AccStore, u32>(inst.rd(), reg[inst.rb()] + inst.imm5() * 4, cyccnt);
      case 0x68 ... 0x6F:          /* LDR rd, [rb + imm] */
         return thumb_memop<AccLoad, u32>(inst.rd(), reg[inst.rb()] + inst.imm5() * 4, cyccnt);
      case 0x70 ... 0x77:          /* STRB rd, [rb + imm] */
         return thumb_memop<AccStore, u8>(inst.rd(), reg[inst.rb()] + inst.imm5(), cyccnt);
      case 0x78 ... 0x7F:          /* LDRB rd, [rb + imm] */
         return thumb_memop<AccLoad, u8>(inst.rd(), reg[inst.rb()] + inst.imm5(), cyccnt);
      case 0x80 ... 0x87:          /* STRH rd, [rb + imm] */
         return thumb_memop<AccStore, u16>(inst.rd(), reg[inst.rb()] + inst.imm5() * 2, cyccnt);
      case 0x88 ... 0x8F:          /* LDRH rd, [rb + imm] */
         return thumb_memop<AccLoad, u16>(inst.rd(), reg[inst.rb()] + inst.imm5() * 2, cyccnt);
      case 0x90 ... 0x97:          /* STR r0..7, [sp + imm] */
         return thumb_memop<AccStore, u32>(inst.rd8(), reg[REG_SP] + inst.imm8() * 4, cyccnt);
      case 0x98 ... 0x9F:          /* LDR r0..7, [sp + imm] */
         return thumb_memop<AccLoad, u32>(inst.rd8(), reg[REG_SP] + inst.imm8() * 4, cyccnt);

      case 0xA0 ... 0xA7:
         /* ADD r0..7, pc, +imm */
         reg[inst.rd8()] = (reg[REG_PC] & ~2) + 4 + inst.imm8() * 4;
         thumb_pc_offset(2);
         break;
      case 0xA8 ... 0xAF:
         /* ADD r0..7, sp, +imm */
         reg[inst.rd8()] = reg[REG_SP] + inst.imm8() * 4;
         thumb_pc_offset(2);
         break;
      case 0xB0 ... 0xB3:          /* ADD sp, -/+imm */
         reg[REG_SP] += inst.imm71() * 4;
         thumb_pc_offset(2);
         break;

      case 0xB4:  /* PUSH rlist */
         return thumb_block_mem<AccStore, AddrPreDec>(REG_SP, inst.rlist(), cyccnt);
      case 0xB5:  /* PUSH rlist, lr */
         return thumb_block_mem<AccStore, AddrPreDec>(REG_SP, inst.rlist() | (1 << REG_LR), cyccnt);
      case 0xBC:  /* POP rlist */
         return thumb_block_mem<AccLoad, AddrPostInc>(REG_SP, inst.rlist(), cyccnt);
      case 0xBD:  /* POP rlist, pc */
         return thumb_block_mem<AccLoad, AddrPostInc>(REG_SP, inst.rlist() | (1 << REG_PC), cyccnt);
      case 0xC0 ... 0xC7:    /* STMIA r0..7!, rlist */
         return thumb_block_mem<AccStore, AddrPostInc>(inst.rptr(), inst.rlist(), cyccnt);
      case 0xC8 ... 0xCF:    /* LDMIA r0..7!, rlist */
         return thumb_block_mem<AccLoad, AddrPostInc>(inst.rptr(), inst.rlist(), cyccnt);

      case 0xD0:   /* BEQ label */
         thumb_cond_br(isset_flag<FLAG_Z>());
         break;
      case 0xD1:   /* BNE label */
         thumb_cond_br(!isset_flag<FLAG_Z>());
         break;
      case 0xD2:   /* BCS label */
         thumb_cond_br(isset_flag<FLAG_C>());
         break;
      case 0xD3:   /* BCC label */
         thumb_cond_br(!isset_flag<FLAG_C>());
         break;
      case 0xD4:   /* BMI label */
         thumb_cond_br(isset_flag<FLAG_N>());
         break;
      case 0xD5:   /* BPL label */
         thumb_cond_br(!isset_flag<FLAG_N>());
         break;
      case 0xD6:   /* BVS label */
         thumb_cond_br(isset_flag<FLAG_V>());
         break;
      case 0xD7:   /* BVC label */
         thumb_cond_br(!isset_flag<FLAG_V>());
         break;
      case 0xD8:   /* BHI label */
         thumb_cond_br(isset_flag<FLAG_C>() && !isset_flag<FLAG_Z>());
         break;
      case 0xD9:   /* BLS label */
         thumb_cond_br(!isset_flag<FLAG_C>() || isset_flag<FLAG_Z>());
         break;
      case 0xDA:   /* BGE label */
         thumb_cond_br(isset_flag<FLAG_N>() == isset_flag<FLAG_V>());
         break;
      case 0xDB:   /* BLT label */
         thumb_cond_br(isset_flag<FLAG_N>() != isset_flag<FLAG_V>());
         break;
      case 0xDC:   /* BGT label */
         thumb_cond_br(!isset_flag<FLAG_Z>() && (isset_flag<FLAG_N>() == isset_flag<FLAG_V>()));
         break;
      case 0xDD:   /* BLE label */
         thumb_cond_br(isset_flag<FLAG_Z>() || (isset_flag<FLAG_N>() != isset_flag<FLAG_V>()));
         break;

      case 0xDF:   /* SWI */
         REG_MODE(MODE_SUPERVISOR)[6] = reg[REG_PC] + 2;
         REG_SPSR(MODE_SUPERVISOR) = reg[REG_CPSR];
         reg[REG_PC] = 0x00000008;
         // Move to ARM mode, Supervisor mode and disable IRQs
         reg[REG_CPSR] = (reg[REG_CPSR] & ~0x3F) | 0x13 | 0x80;
         set_cpu_mode(MODE_SUPERVISOR);
         reg[REG_BUS_VALUE] = 0xe3a02004;  // After SWI, we read bios[0xE4]
         break;

      case 0xE0 ... 0xE7:          /* B label */
         reg[REG_PC] += inst.abr_offset() + 4;
         cyccnt -= ws_cyc_nseq[reg[REG_PC] >> 24][0];
         break;

      case 0xF0 ... 0xF7:          /* (low word) BL label */
         reg[REG_LR] = reg[REG_PC] + 4 + inst.abr_offset_hi();
         thumb_pc_offset(2);
         break;

      case 0xF8 ... 0xFF:          /* (high word) BL label */
         {
            u32 newlr = (reg[REG_PC] + 2) | 0x01;
            reg[REG_PC] = reg[REG_LR] + inst.abr_offset_lo();
            reg[REG_LR] = newlr;
            cyccnt -= ws_cyc_nseq[reg[REG_PC] >> 24][0];
            break;
         }
   }
   return CPU_ALERT_NONE;
}


cpu_alert_type execute_arm_instruction(u32 opcode, s32 &cyccnt) {
   const ARMInst inst(opcode);
   switch (inst.op8()) {
      case 0x00:
         if((opcode & 0x90) == 0x90) {
            if(opcode & 0x20) /* STRH rd, [rn], -rm */
               return arm_memop<AccStore, u16, HOp2MinusReg, MemIdxPostWB>(inst, cyccnt);
            else    /* MUL rd, rm, rs */
               arm_mul32<FlagsIgnore, MulReg>(inst);
         }
         else  /* AND rd, rn, reg_op */
            return arm_logic<LgcAnd, FlagsIgnore, Op2Reg>(inst);
         break;

      case 0x01:
         if((opcode & 0x90) == 0x90)
            switch((opcode >> 5) & 0x03) {
               case 0:
                  arm_mul32<FlagsSet, MulReg>(inst);
                  break;
               case 1:   /* LDRH rd, [rn], -rm */
                  return arm_memop<AccLoad, u16, HOp2MinusReg, MemIdxPostWB>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn], -rm */
                  return arm_memop<AccLoad, s8, HOp2MinusReg, MemIdxPostWB>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn], -rm */
                  return arm_memop<AccLoad, s16, HOp2MinusReg, MemIdxPostWB>(inst, cyccnt);
            }
         else  /* ANDS rd, rn, reg_op */
            return arm_logic<LgcAnd, FlagsSet, Op2Reg>(inst);
         break;

      case 0x02:
         if((opcode & 0x90) == 0x90) {
            if(opcode & 0x20) /* STRH rd, [rn], -rm */
               return arm_memop<AccStore, u16, HOp2MinusReg, MemIdxPostWB>(inst, cyccnt);
            else              /* MLA rd, rm, rs, rn */
               arm_mul32<FlagsIgnore, MulAdd>(inst);
         }
         else  /* EOR rd, rn, reg_op */
            return arm_logic<LgcXor, FlagsIgnore, Op2Reg>(inst);
         break;

      case 0x03:
         if((opcode & 0x90) == 0x90)
            switch((opcode >> 5) & 0x03) {
               case 0:   /* MLAS rd, rm, rs, rn */
                  arm_mul32<FlagsSet, MulAdd>(inst);
                  break;
               case 1:   /* LDRH rd, [rn], -rm */
                  return arm_memop<AccLoad, u16, HOp2MinusReg, MemIdxPostWB>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn], -rm */
                  return arm_memop<AccLoad, s8, HOp2MinusReg, MemIdxPostWB>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn], -rm */
                  return arm_memop<AccLoad, s16, HOp2MinusReg, MemIdxPostWB>(inst, cyccnt);
            }
         else  /* EORS rd, rn, reg_op */
            return arm_logic<LgcXor, FlagsSet, Op2Reg>(inst);
         break;

      case 0x04:
         if((opcode & 0x90) == 0x90)    /* STRH rd, [rn], -imm */
            return arm_memop<AccStore, u16, HOp2MinusImm, MemIdxPostWB>(inst, cyccnt);
         else                           /* SUB rd, rn, reg_op */
            return arm_sub<FlagsIgnore, Op2Reg, OpDirect, true>(inst, true);

      case 0x05:
         if((opcode & 0x90) == 0x90)
            switch((opcode >> 5) & 0x03) {
               case 1:   /* LDRH rd, [rn], -imm */
                  return arm_memop<AccLoad, u16, HOp2MinusImm, MemIdxPostWB>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn], -imm */
                  return arm_memop<AccLoad, s8, HOp2MinusImm, MemIdxPostWB>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn], -imm */
                  return arm_memop<AccLoad, s16, HOp2MinusImm, MemIdxPostWB>(inst, cyccnt);
            }
         else  /* SUBS rd, rn, reg_op */
            return arm_sub<FlagsSet, Op2Reg, OpDirect, true>(inst, true);
         break;

      case 0x06:
         if((opcode & 0x90) == 0x90)    /* STRH rd, [rn], -imm */
            return arm_memop<AccStore, u16, HOp2MinusImm, MemIdxPostWB>(inst, cyccnt);
         else                           /* RSB rd, rn, reg_op */
            return arm_sub<FlagsIgnore, Op2Reg, OpReverse, true>(inst, true);

      case 0x07:
         if((opcode & 0x90) == 0x90)
            switch((opcode >> 5) & 0x03) {
               case 1:   /* LDRH rd, [rn], -imm */
                  return arm_memop<AccLoad, u16, HOp2MinusImm, MemIdxPostWB>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn], -imm */
                  return arm_memop<AccLoad, s8, HOp2MinusImm, MemIdxPostWB>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn], -imm */
                  return arm_memop<AccLoad, s16, HOp2MinusImm, MemIdxPostWB>(inst, cyccnt);
            }
         else  /* RSBS rd, rn, reg_op */
            return arm_sub<FlagsSet, Op2Reg, OpReverse, true>(inst, true);
         break;

      case 0x08:
         if((opcode & 0x90) == 0x90) {
            if(opcode & 0x20)      /* STRH rd, [rn], +rm */
               return arm_memop<AccStore, u16, HOp2PlusReg, MemIdxPostWB>(inst, cyccnt);
            else                   /* UMULL rd, rm, rs */
               arm_mul64<FlagsIgnore, MulReg, SiUnsigned>(inst);
         }
         else  /* ADD rd, rn, reg_op */
            return arm_add<FlagsIgnore, Op2Reg, true>(inst, false);
         break;

      case 0x09:
         if((opcode & 0x90) == 0x90) {
            switch((opcode >> 5) & 0x03) {
               case 0:   /* UMULLS rdlo, rdhi, rm, rs */
                  arm_mul64<FlagsSet, MulReg, SiUnsigned>(inst);
                  break;
               case 1:   /* LDRH rd, [rn], +rm */
                  return arm_memop<AccLoad, u16, HOp2PlusReg, MemIdxPostWB>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn], +rm */
                  return arm_memop<AccLoad, s8, HOp2PlusReg, MemIdxPostWB>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn], +rm */
                  return arm_memop<AccLoad, s16, HOp2PlusReg, MemIdxPostWB>(inst, cyccnt);
            }
         }
         else  /* ADDS rd, rn, reg_op */
            return arm_add<FlagsSet, Op2Reg, true>(inst, false);
         break;

      case 0x0A:
         if((opcode & 0x90) == 0x90) {
            if(opcode & 0x20)      /* STRH rd, [rn], +rm */
               return arm_memop<AccStore, u16, HOp2PlusReg, MemIdxPostWB>(inst, cyccnt);
            else    /* UMLAL rd, rm, rs */
               arm_mul64<FlagsIgnore, MulAdd, SiUnsigned>(inst);
         }
         else  /* ADC rd, rn, reg_op */
            return arm_add<FlagsIgnore, Op2Reg, true>(inst, isset_flag<FLAG_C>());
         break;

      case 0x0B:
         if((opcode & 0x90) == 0x90) {
            switch((opcode >> 5) & 0x03) {
               case 0:   /* UMLALS rdlo, rdhi, rm, rs */
                  arm_mul64<FlagsSet, MulAdd, SiUnsigned>(inst);
                  break;
               case 1:   /* LDRH rd, [rn], +rm */
                  return arm_memop<AccLoad, u16, HOp2PlusReg, MemIdxPostWB>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn], +rm */
                  return arm_memop<AccLoad, s8, HOp2PlusReg, MemIdxPostWB>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn], +rm */
                  return arm_memop<AccLoad, s16, HOp2PlusReg, MemIdxPostWB>(inst, cyccnt);
            }
         }
         else  /* ADCS rd, rn, reg_op */
            return arm_add<FlagsSet, Op2Reg, true>(inst, isset_flag<FLAG_C>());
         break;

      case 0x0C:
         if((opcode & 0x90) == 0x90) {
            if(opcode & 0x20)      /* STRH rd, [rn], +imm */
               return arm_memop<AccStore, u16, HOp2PlusImm, MemIdxPostWB>(inst, cyccnt);
            else                   /* SMULL rd, rm, rs */
               arm_mul64<FlagsIgnore, MulReg, SiSigned>(inst);
         }
         else  /* SBC rd, rn, reg_op */
            return arm_sub<FlagsIgnore, Op2Reg, OpDirect, true>(inst, isset_flag<FLAG_C>());
         break;

      case 0x0D:
         if((opcode & 0x90) == 0x90) {
            switch((opcode >> 5) & 0x03) {
               case 0:   /* SMULLS rdlo, rdhi, rm, rs */
                  arm_mul64<FlagsSet, MulReg, SiSigned>(inst);
                  break;
               case 1:   /* LDRH rd, [rn], +imm */
                  return arm_memop<AccLoad, u16, HOp2PlusImm, MemIdxPostWB>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn], +imm */
                  return arm_memop<AccLoad, s8, HOp2PlusImm, MemIdxPostWB>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn], +imm */
                  return arm_memop<AccLoad, s16, HOp2PlusImm, MemIdxPostWB>(inst, cyccnt);
            }
         }
         else  /* SBCS rd, rn, reg_op */
            return arm_sub<FlagsSet, Op2Reg, OpDirect, true>(inst, isset_flag<FLAG_C>());
         break;

      case 0x0E:
         if((opcode & 0x90) == 0x90)
         {
            if(opcode & 0x20)      /* STRH rd, [rn], +imm */
               return arm_memop<AccStore, u16, HOp2PlusImm, MemIdxPostWB>(inst, cyccnt);
            else                   /* SMLAL rd, rm, rs */
               arm_mul64<FlagsIgnore, MulAdd, SiSigned>(inst);
         }
         else  /* RSC rd, rn, reg_op */
            return arm_sub<FlagsIgnore, Op2Reg, OpReverse, true>(inst, isset_flag<FLAG_C>());
         break;

      case 0x0F:
         if((opcode & 0x90) == 0x90) {
            switch((opcode >> 5) & 0x03) {
               case 0:   /* SMLALS rdlo, rdhi, rm, rs */
                  arm_mul64<FlagsSet, MulAdd, SiSigned>(inst);
                  break;
               case 1:   /* LDRH rd, [rn], +imm */
                  return arm_memop<AccLoad, u16, HOp2PlusImm, MemIdxPostWB>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn], +imm */
                  return arm_memop<AccLoad, s8, HOp2PlusImm, MemIdxPostWB>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn], +imm */
                  return arm_memop<AccLoad, s16, HOp2PlusImm, MemIdxPostWB>(inst, cyccnt);
            }
         }
         else  /* RSCS rd, rn, reg_op */
            return arm_sub<FlagsSet, Op2Reg, OpReverse, true>(inst, isset_flag<FLAG_C>());
         break;

      case 0x10:
         if((opcode & 0x90) == 0x90) {
            if(opcode & 0x20)      /* STRH rd, [rn - rm] */
               return arm_memop<AccStore, u16, HOp2MinusReg, MemIdxPre>(inst, cyccnt);
            else                   /* SWP rd, rm, [rn] */
               return arm_swap<u32>(inst, cyccnt);
         }
         else {/* MRS rd, cpsr */
            reg[inst.rd()] = reg[REG_CPSR];
            arm_pc_offset(4);
         }
         break;

      case 0x11:
         if((opcode & 0x90) == 0x90) {
            switch((opcode >> 5) & 0x03) {
               case 1:   /* LDRH rd, [rn - rm] */
                  return arm_memop<AccLoad, u16, HOp2MinusReg, MemIdxPre>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn - rm] */
                  return arm_memop<AccLoad, s8, HOp2MinusReg, MemIdxPre>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn - rm] */
                  return arm_memop<AccLoad, s16, HOp2MinusReg, MemIdxPre>(inst, cyccnt);
            }
         }
         else  /* TST rd, rn, reg_op */
            arm_logic_test<LgcAnd, Op2Reg>(inst);
         break;

      case 0x12:
         if((opcode & 0x90) == 0x90)    /* STRH rd, [rn - rm]! */
            return arm_memop<AccStore, u16, HOp2MinusReg, MemIdxPreWB>(inst, cyccnt);
         else {
            if(opcode & 0x10) {
               /* BX rn */
               u32 newpc = reg[inst.rm()];
               if (newpc & 0x01) {
                  reg[REG_PC] = newpc - 1;
                  reg[REG_CPSR] |= 0x20;
               }
               else {
                  reg[REG_PC] = newpc;
               }
               cyccnt -= ws_cyc_nseq[reg[REG_PC] >> 24][1];
            }
            else  /* MSR cpsr, rm */
               return cpsr_write(inst, reg[inst.rm()]);
         }
         break;

      case 0x13:
         if((opcode & 0x90) == 0x90)
            switch((opcode >> 5) & 0x03) {
               case 1:   /* LDRH rd, [rn - rm]! */
                  return arm_memop<AccLoad, u16, HOp2MinusReg, MemIdxPreWB>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn - rm]! */
                  return arm_memop<AccLoad, s8, HOp2MinusReg, MemIdxPreWB>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn - rm]! */
                  return arm_memop<AccLoad, s16, HOp2MinusReg, MemIdxPreWB>(inst, cyccnt);
            }
         else  /* TEQ rd, rn, reg_op */
            arm_logic_test<LgcXor, Op2Reg>(inst);
         break;

      case 0x14:
         if((opcode & 0x90) == 0x90) {
            if(opcode & 0x20)      /* STRH rd, [rn - imm] */
               return arm_memop<AccStore, u16, HOp2MinusImm, MemIdxPre>(inst, cyccnt);
            else                   /* SWPB rd, rm, [rn] */
               return arm_swap<u8>(inst, cyccnt);
         }
         else {/* MRS rd, spsr */
            reg[inst.rd()] = REG_SPSR(reg[CPU_MODE]);
            arm_pc_offset(4);
         }
         break;

      case 0x15:
         if((opcode & 0x90) == 0x90)
            switch((opcode >> 5) & 0x03) {
               case 1:   /* LDRH rd, [rn - imm] */
                  return arm_memop<AccLoad, u16, HOp2MinusImm, MemIdxPre>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn - imm] */
                  return arm_memop<AccLoad, s8, HOp2MinusImm, MemIdxPre>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn - imm] */
                  return arm_memop<AccLoad, s16, HOp2MinusImm, MemIdxPre>(inst, cyccnt);
            }
         else  /* CMP rn, reg_op */
            arm_sub<FlagsSet, Op2Reg, OpDirect, false>(inst, true);
         break;

      case 0x16:
         if((opcode & 0x90) == 0x90)    /* STRH rd, [rn - imm]! */
            return arm_memop<AccStore, u16, HOp2MinusImm, MemIdxPreWB>(inst, cyccnt);
         else                           /* MSR spsr, rm */
            spsr_write(inst, reg[inst.rm()]);
         break;

      case 0x17:
         if((opcode & 0x90) == 0x90)
            switch((opcode >> 5) & 0x03) {
               case 1:   /* LDRH rd, [rn - imm]! */
                  return arm_memop<AccLoad, u16, HOp2MinusImm, MemIdxPreWB>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn - imm]! */
                  return arm_memop<AccLoad, s8, HOp2MinusImm, MemIdxPreWB>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn - imm]! */
                  return arm_memop<AccLoad, s16, HOp2MinusImm, MemIdxPreWB>(inst, cyccnt);
            }
         else  /* CMN rd, rn, reg_op */
            arm_add<FlagsSet, Op2Reg, false>(inst, false);
         break;

      case 0x18:
         if((opcode & 0x90) == 0x90)    /* STRH rd, [rn + rm] */
            return arm_memop<AccStore, u16, HOp2PlusReg, MemIdxPre>(inst, cyccnt);
         else                           /* ORR rd, rn, reg_op */
            return arm_logic<LgcOrr, FlagsIgnore, Op2Reg>(inst);

      case 0x19:
         if((opcode & 0x90) == 0x90)
            switch((opcode >> 5) & 0x03) {
               case 1:   /* LDRH rd, [rn + rm] */
                  return arm_memop<AccLoad, u16, HOp2PlusReg, MemIdxPre>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn + rm] */
                  return arm_memop<AccLoad, s8, HOp2PlusReg, MemIdxPre>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn + rm] */
                  return arm_memop<AccLoad, s16, HOp2PlusReg, MemIdxPre>(inst, cyccnt);
            }
         else  /* ORRS rd, rn, reg_op */
            return arm_logic<LgcOrr, FlagsSet, Op2Reg>(inst);
         break;

      case 0x1A:
         if((opcode & 0x90) == 0x90)    /* STRH rd, [rn + rm]! */
            return arm_memop<AccStore, u16, HOp2PlusReg, MemIdxPreWB>(inst, cyccnt);
         else                           /* MOV rd, reg_op */
            return arm_logic<LgcMov, FlagsIgnore, Op2Reg>(inst);

      case 0x1B:
         if((opcode & 0x90) == 0x90)
            switch((opcode >> 5) & 0x03) {
               case 1:   /* LDRH rd, [rn + rm]! */
                  return arm_memop<AccLoad, u16, HOp2PlusReg, MemIdxPreWB>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn + rm]! */
                  return arm_memop<AccLoad, s8, HOp2PlusReg, MemIdxPreWB>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn + rm]! */
                  return arm_memop<AccLoad, s16, HOp2PlusReg, MemIdxPreWB>(inst, cyccnt);
            }
         else  /* MOVS rd, reg_op */
            return arm_logic<LgcMov, FlagsSet, Op2Reg>(inst);
         break;

      case 0x1C:
         if((opcode & 0x90) == 0x90)    /* STRH rd, [rn + imm] */
            return arm_memop<AccStore, u16, HOp2PlusImm, MemIdxPre>(inst, cyccnt);
         else  /* BIC rd, rn, reg_op */
            return arm_logic<LgcBic, FlagsIgnore, Op2Reg>(inst);

      case 0x1D:
         if((opcode & 0x90) == 0x90)
            switch((opcode >> 5) & 0x03) {
               case 1:   /* LDRH rd, [rn + imm] */
                  return arm_memop<AccLoad, u16, HOp2PlusImm, MemIdxPre>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn + imm] */
                  return arm_memop<AccLoad, s8, HOp2PlusImm, MemIdxPre>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn + imm] */
                  return arm_memop<AccLoad, s16, HOp2PlusImm, MemIdxPre>(inst, cyccnt);
            }
         else  /* BICS rd, rn, reg_op */
            return arm_logic<LgcBic, FlagsSet, Op2Reg>(inst);
         break;

      case 0x1E:
         if((opcode & 0x90) == 0x90)    /* STRH rd, [rn + imm]! */
            return arm_memop<AccStore, u16, HOp2PlusImm, MemIdxPreWB>(inst, cyccnt);
         else  /* MVN rd, reg_op */
            return arm_logic<LgcNot, FlagsIgnore, Op2Reg>(inst);

      case 0x1F:
         if((opcode & 0x90) == 0x90)
            switch((opcode >> 5) & 0x03) {
               case 1:   /* LDRH rd, [rn + imm]! */
                  return arm_memop<AccLoad, u16, HOp2PlusImm, MemIdxPreWB>(inst, cyccnt);
               case 2:   /* LDRSB rd, [rn + imm]! */
                  return arm_memop<AccLoad, s8, HOp2PlusImm, MemIdxPreWB>(inst, cyccnt);
               case 3:   /* LDRSH rd, [rn + imm]! */
                  return arm_memop<AccLoad, s16, HOp2PlusImm, MemIdxPreWB>(inst, cyccnt);
            }
         else  /* MVNS rd, rn, reg_op */
            return arm_logic<LgcNot, FlagsSet, Op2Reg>(inst);
         break;

      case 0x20:         /* AND rd, rn, imm */
         return arm_logic<LgcAnd, FlagsIgnore, Op2Imm>(inst);
      case 0x21:         /* ANDS rd, rn, imm */
         return arm_logic<LgcAnd, FlagsSet, Op2Imm>(inst);
      case 0x22:         /* EOR rd, rn, imm */
         return arm_logic<LgcXor, FlagsIgnore, Op2Imm>(inst);
      case 0x23:         /* EORS rd, rn, imm */
         return arm_logic<LgcXor, FlagsSet, Op2Imm>(inst);
      case 0x24:         /* SUB rd, rn, imm */
         return arm_sub<FlagsIgnore, Op2Imm, OpDirect, true>(inst, true);
      case 0x25:         /* SUBS rd, rn, imm */
         return arm_sub<FlagsSet, Op2Imm, OpDirect, true>(inst, true);
      case 0x26:         /* RSB rd, rn, imm */
         return arm_sub<FlagsIgnore, Op2Imm, OpReverse, true>(inst, true);
      case 0x27:         /* RSBS rd, rn, imm */
         return arm_sub<FlagsSet, Op2Imm, OpReverse, true>(inst, true);
      case 0x28:         /* ADD rd, rn, imm */
         return arm_add<FlagsIgnore, Op2Imm, true>(inst, false);
      case 0x29:         /* ADDS rd, rn, imm */
         return arm_add<FlagsSet, Op2Imm, true>(inst, false);
      case 0x2A:         /* ADC rd, rn, imm */
         return arm_add<FlagsIgnore, Op2Imm, true>(inst, isset_flag<FLAG_C>());
      case 0x2B:         /* ADCS rd, rn, imm */
         return arm_add<FlagsSet, Op2Imm, true>(inst, isset_flag<FLAG_C>());
      case 0x2C:         /* SBC rd, rn, imm */
         return arm_sub<FlagsIgnore, Op2Imm, OpDirect, true>(inst, isset_flag<FLAG_C>());
      case 0x2D:         /* SBCS rd, rn, imm */
         return arm_sub<FlagsSet, Op2Imm, OpDirect, true>(inst, isset_flag<FLAG_C>());
      case 0x2E:         /* RSC rd, rn, imm */
         return arm_sub<FlagsIgnore, Op2Imm, OpReverse, true>(inst, isset_flag<FLAG_C>());
      case 0x2F:         /* RSCS rd, rn, imm */
         return arm_sub<FlagsSet, Op2Imm, OpReverse, true>(inst, isset_flag<FLAG_C>());
      case 0x30 ... 0x31:  /* TST rn, imm */
         arm_logic_test<LgcAnd, Op2Imm>(inst);
         break;
      case 0x32:         /* MSR cpsr, imm */
         return cpsr_write(inst, inst.rot_imm8());
      case 0x33:         /* TEQ rn, imm */
         arm_logic_test<LgcXor, Op2Imm>(inst);
         break;
      case 0x34 ... 0x35:    /* CMP rn, imm */
         arm_sub<FlagsSet, Op2Imm, OpDirect, false>(inst, true);
         break;
      case 0x36:         /* MSR spsr, imm */
         spsr_write(inst, inst.rot_imm8());
         break;
      case 0x37:         /* CMN rn, imm */
         return arm_add<FlagsSet, Op2Imm, false>(inst, false);
      case 0x38:         /* ORR rd, rn, imm */
         return arm_logic<LgcOrr, FlagsIgnore, Op2Imm>(inst);
      case 0x39:         /* ORRS rd, rn, imm */
         return arm_logic<LgcOrr, FlagsSet, Op2Imm>(inst);
      case 0x3A:         /* MOV rd, imm */
         return arm_logic<LgcMov, FlagsIgnore, Op2Imm>(inst);
      case 0x3B:         /* MOVS rd, imm */
         return arm_logic<LgcMov, FlagsSet, Op2Imm>(inst);
      case 0x3C:         /* BIC rd, rn, imm */
         return arm_logic<LgcBic, FlagsIgnore, Op2Imm>(inst);
      case 0x3D:         /* BICS rd, rn, imm */
         return arm_logic<LgcBic, FlagsSet, Op2Imm>(inst);
      case 0x3E:         /* MVN rd, imm */
         return arm_logic<LgcNot, FlagsIgnore, Op2Imm>(inst);
      case 0x3F:         /* MVNS rd, imm */
         return arm_logic<LgcNot, FlagsSet, Op2Imm>(inst);

      /* Load/Store with immediate post increment/decrement (byte and word) */
      case 0x40: case 0x42:   /* STR/STRT rd, [rn], -imm */
         return arm_memop<AccStore, u32, Op2MinusImm, MemIdxPostWB>(inst, cyccnt);
      case 0x41: case 0x43:   /* LDR/LDRT rd, [rn], -imm */
         return arm_memop<AccLoad, u32, Op2MinusImm, MemIdxPostWB>(inst, cyccnt);
      case 0x44: case 0x46:   /* STRB/STRBT rd, [rn], -imm */
         return arm_memop<AccStore, u8, Op2MinusImm, MemIdxPostWB>(inst, cyccnt);
      case 0x45: case 0x47:   /* LDRB/LDRBT rd, [rn], -imm */
         return arm_memop<AccLoad, u8, Op2MinusImm, MemIdxPostWB>(inst, cyccnt);
      case 0x48: case 0x4A:   /* STR/STRT rd, [rn], +imm */
         return arm_memop<AccStore, u32, Op2PlusImm, MemIdxPostWB>(inst, cyccnt);
      case 0x49: case 0x4B:   /* LDR/LDRT rd, [rn], +imm */
         return arm_memop<AccLoad, u32, Op2PlusImm, MemIdxPostWB>(inst, cyccnt);
      case 0x4C: case 0x4E:   /* STRB/STRBT rd, [rn], +imm */
         return arm_memop<AccStore, u8, Op2PlusImm, MemIdxPostWB>(inst, cyccnt);
      case 0x4D: case 0x4F:   /* LDRB/LDRBT rd, [rn], +imm */
         return arm_memop<AccLoad, u8, Op2PlusImm, MemIdxPostWB>(inst, cyccnt);

      /* Load/Store with optional immediate pre increment/decrement (byte and word) */
      case 0x50:              /* STR rd, [rn - imm] */
         return arm_memop<AccStore, u32, Op2MinusImm, MemIdxPre>(inst, cyccnt);
      case 0x51:              /* LDR rd, [rn - imm] */
         return arm_memop<AccLoad, u32, Op2MinusImm, MemIdxPre>(inst, cyccnt);
      case 0x52:              /* STR rd, [rn - imm]! */
         return arm_memop<AccStore, u32, Op2MinusImm, MemIdxPreWB>(inst, cyccnt);
      case 0x53:              /* LDR rd, [rn - imm]! */
         return arm_memop<AccLoad, u32, Op2MinusImm, MemIdxPreWB>(inst, cyccnt);
      case 0x54:              /* STRB rd, [rn - imm] */
         return arm_memop<AccStore, u8, Op2MinusImm, MemIdxPre>(inst, cyccnt);
      case 0x55:              /* LDRB rd, [rn - imm] */
         return arm_memop<AccLoad, u8, Op2MinusImm, MemIdxPre>(inst, cyccnt);
      case 0x56:              /* STRB rd, [rn - imm]! */
         return arm_memop<AccStore, u8, Op2MinusImm, MemIdxPreWB>(inst, cyccnt);
      case 0x57:              /* LDRB rd, [rn - imm]! */
         return arm_memop<AccLoad, u8, Op2MinusImm, MemIdxPreWB>(inst, cyccnt);

      case 0x58:              /* STR rd, [rn + imm] */
         return arm_memop<AccStore, u32, Op2PlusImm, MemIdxPre>(inst, cyccnt);
      case 0x59:              /* LDR rd, [rn + imm] */
         return arm_memop<AccLoad, u32, Op2PlusImm, MemIdxPre>(inst, cyccnt);
      case 0x5A:              /* STR rd, [rn + imm]! */
         return arm_memop<AccStore, u32, Op2PlusImm, MemIdxPreWB>(inst, cyccnt);
      case 0x5B:              /* LDR rd, [rn + imm]! */
         return arm_memop<AccLoad, u32, Op2PlusImm, MemIdxPreWB>(inst, cyccnt);
      case 0x5C:              /* STRB rd, [rn + imm] */
         return arm_memop<AccStore, u8, Op2PlusImm, MemIdxPre>(inst, cyccnt);
      case 0x5D:              /* LDRB rd, [rn + imm] */
         return arm_memop<AccLoad, u8, Op2PlusImm, MemIdxPre>(inst, cyccnt);
      case 0x5E:              /* STRB rd, [rn + imm]! */
         return arm_memop<AccStore, u8, Op2PlusImm, MemIdxPreWB>(inst, cyccnt);
      case 0x5F:              /* LDRB rd, [rn + imm]! */
         return arm_memop<AccLoad, u8, Op2PlusImm, MemIdxPreWB>(inst, cyccnt);

      /* Load/Store with shifted-reg post increment/decrement (byte and word) */
      case 0x60: case 0x62:  /* STR/STRT rd, [rn], -reg_op */
         return arm_memop<AccStore, u32, Op2MinusReg, MemIdxPostWB>(inst, cyccnt);
      case 0x61: case 0x63:   /* LDR rd, [rn], -reg_op */
         return arm_memop<AccLoad, u32, Op2MinusReg, MemIdxPostWB>(inst, cyccnt);
      case 0x64: case 0x66:   /* STRB/STRBT rd, [rn], -reg_op */
         return arm_memop<AccStore, u8, Op2MinusReg, MemIdxPostWB>(inst, cyccnt);
      case 0x65: case 0x67:   /* LDRB/LDRBT rd, [rn], -reg_op */
         return arm_memop<AccLoad, u8, Op2MinusReg, MemIdxPostWB>(inst, cyccnt);

      case 0x68: case 0x6A:   /* STR/STRT rd, [rn], +reg_op */
         return arm_memop<AccStore, u32, Op2PlusReg, MemIdxPostWB>(inst, cyccnt);
      case 0x69: case 0x6B:   /* LDR/LDRT rd, [rn], +reg_op */
         return arm_memop<AccLoad, u32, Op2PlusReg, MemIdxPostWB>(inst, cyccnt);
      case 0x6C: case 0x6E:   /* STRB/STRBT rd, [rn], +reg_op */
         return arm_memop<AccStore, u8, Op2PlusReg, MemIdxPostWB>(inst, cyccnt);
      case 0x6D: case 0x6F:   /* LDRB/LDRBT rd, [rn], +reg_op */
         return arm_memop<AccLoad, u8, Op2PlusReg, MemIdxPostWB>(inst, cyccnt);

      /* Load/Store with optional shifted-reg pre increment/decrement (byte and word) */
      case 0x70:              /* STR rd, [rn - reg_op] */
         return arm_memop<AccStore, u32, Op2MinusReg, MemIdxPre>(inst, cyccnt);
      case 0x71:              /* LDR rd, [rn - reg_op] */
         return arm_memop<AccLoad, u32, Op2MinusReg, MemIdxPre>(inst, cyccnt);
      case 0x72:              /* STR rd, [rn - reg_op]! */
         return arm_memop<AccStore, u32, Op2MinusReg, MemIdxPreWB>(inst, cyccnt);
      case 0x73:              /* LDR rd, [rn - reg_op]! */
         return arm_memop<AccLoad, u32, Op2MinusReg, MemIdxPreWB>(inst, cyccnt);
      case 0x74:              /* STRB rd, [rn - reg_op] */
         return arm_memop<AccStore, u8, Op2MinusReg, MemIdxPre>(inst, cyccnt);
      case 0x75:              /* LDRB rd, [rn - reg_op] */
         return arm_memop<AccLoad, u8, Op2MinusReg, MemIdxPre>(inst, cyccnt);
      case 0x76:              /* STRB rd, [rn - reg_op]! */
         return arm_memop<AccStore, u8, Op2MinusReg, MemIdxPreWB>(inst, cyccnt);
      case 0x77:              /* LDRB rd, [rn - reg_op]! */
         return arm_memop<AccLoad, u8, Op2MinusReg, MemIdxPreWB>(inst, cyccnt);

      case 0x78:              /* STR rd, [rn + reg_op] */
         return arm_memop<AccStore, u32, Op2PlusReg, MemIdxPre>(inst, cyccnt);
      case 0x79:              /* LDR rd, [rn + reg_op] */
         return arm_memop<AccLoad, u32, Op2PlusReg, MemIdxPre>(inst, cyccnt);
      case 0x7A:              /* STR rd, [rn + reg_op]! */
         return arm_memop<AccStore, u32, Op2PlusReg, MemIdxPreWB>(inst, cyccnt);
      case 0x7B:              /* LDR rd, [rn + reg_op]! */
         return arm_memop<AccLoad, u32, Op2PlusReg, MemIdxPreWB>(inst, cyccnt);
      case 0x7C:              /* STRB rd, [rn + reg_op] */
         return arm_memop<AccStore, u8, Op2PlusReg, MemIdxPre>(inst, cyccnt);
      case 0x7D:              /* LDRB rd, [rn + reg_op] */
         return arm_memop<AccLoad, u8, Op2PlusReg, MemIdxPre>(inst, cyccnt);
      case 0x7E:              /* STRB rd, [rn + reg_op]! */
         return arm_memop<AccStore, u8, Op2PlusReg, MemIdxPreWB>(inst, cyccnt);
      case 0x7F:              /* LDRB rd, [rn + reg_op]! */
         return arm_memop<AccLoad, u8, Op2PlusReg, MemIdxPreWB>(inst, cyccnt);

      /* STM instructions: STMDA, STMIA, STMDB, STMIB */

      case 0x80:   /* STMDA rn, rlist */
        return arm_block_mem<AccStore, false, false, AddrPostDec>(inst, cyccnt);
      case 0x88:   /* STMIA rn, rlist */
        return arm_block_mem<AccStore, false, false, AddrPostInc>(inst, cyccnt);
      case 0x90:   /* STMDB rn, rlist */
        return arm_block_mem<AccStore, false, false, AddrPreDec>(inst, cyccnt);
      case 0x98:   /* STMIB rn, rlist */
        return arm_block_mem<AccStore, false, false, AddrPreInc>(inst, cyccnt);

      case 0x82:   /* STMDA rn!, rlist */
        return arm_block_mem<AccStore, true, false, AddrPostDec>(inst, cyccnt);
      case 0x8A:   /* STMIA rn!, rlist */
        return arm_block_mem<AccStore, true, false, AddrPostInc>(inst, cyccnt);
      case 0x92:   /* STMDB rn!, rlist */
        return arm_block_mem<AccStore, true, false, AddrPreDec>(inst, cyccnt);
      case 0x9A:   /* STMIB rn!, rlist */
        return arm_block_mem<AccStore, true, false, AddrPreInc>(inst, cyccnt);

      case 0x84:   /* STMDA rn, rlist^ */
        return arm_block_mem<AccStore, false, true, AddrPostDec>(inst, cyccnt);
      case 0x8C:   /* STMIA rn, rlist^ */
        return arm_block_mem<AccStore, false, true, AddrPostInc>(inst, cyccnt);
      case 0x94:   /* STMDB rn, rlist^ */
        return arm_block_mem<AccStore, false, true, AddrPreDec>(inst, cyccnt);
      case 0x9C:   /* STMIB rn, rlist^ */
        return arm_block_mem<AccStore, false, true, AddrPreInc>(inst, cyccnt);

      case 0x86:   /* STMDA rn!, rlist^ */
        return arm_block_mem<AccStore, true, true, AddrPostDec>(inst, cyccnt);
      case 0x8E:   /* STMIA rn!, rlist^ */
        return arm_block_mem<AccStore, true, true, AddrPostInc>(inst, cyccnt);
      case 0x96:   /* STMDB rn!, rlist^ */
        return arm_block_mem<AccStore, true, true, AddrPreDec>(inst, cyccnt);
      case 0x9E:   /* STMIB rn!, rlist^ */
        return arm_block_mem<AccStore, true, true, AddrPreInc>(inst, cyccnt);

      /* LDM instructions: LDMDA, LDMIA, LDMDB, LDMIB */

      case 0x81:   /* LDMDA rn, rlist */
        return arm_block_mem<AccLoad, false, false, AddrPostDec>(inst, cyccnt);
      case 0x89:   /* LDMIA rn, rlist */
        return arm_block_mem<AccLoad, false, false, AddrPostInc>(inst, cyccnt);
      case 0x91:   /* LDMDB rn, rlist */
        return arm_block_mem<AccLoad, false, false, AddrPreDec>(inst, cyccnt);
      case 0x99:   /* LDMIB rn, rlist */
        return arm_block_mem<AccLoad, false, false, AddrPreInc>(inst, cyccnt);

      case 0x83:   /* LDMDA rn!, rlist */
        return arm_block_mem<AccLoad, true, false, AddrPostDec>(inst, cyccnt);
      case 0x8B:   /* LDMIA rn!, rlist */
        return arm_block_mem<AccLoad, true, false, AddrPostInc>(inst, cyccnt);
      case 0x93:   /* LDMDB rn!, rlist */
        return arm_block_mem<AccLoad, true, false, AddrPreDec>(inst, cyccnt);
      case 0x9B:   /* LDMIB rn!, rlist */
        return arm_block_mem<AccLoad, true, false, AddrPreInc>(inst, cyccnt);

      case 0x85:   /* LDMDA rn, rlist^ */
        return arm_block_mem<AccLoad, false, true, AddrPostDec>(inst, cyccnt);
      case 0x8D:   /* LDMIA rn, rlist^ */
        return arm_block_mem<AccLoad, false, true, AddrPostInc>(inst, cyccnt);
      case 0x95:   /* LDMDB rn, rlist^ */
        return arm_block_mem<AccLoad, false, true, AddrPreDec>(inst, cyccnt);
      case 0x9D:   /* LDMIB rn, rlist^ */
        return arm_block_mem<AccLoad, false, true, AddrPreInc>(inst, cyccnt);

      case 0x87:   /* LDMDA rn!, rlist^ */
        return arm_block_mem<AccLoad, true, true, AddrPostDec>(inst, cyccnt);
      case 0x8F:   /* LDMIA rn!, rlist^ */
        return arm_block_mem<AccLoad, true, true, AddrPostInc>(inst, cyccnt);
      case 0x97:   /* LDMDB rn!, rlist^ */
        return arm_block_mem<AccLoad, true, true, AddrPreDec>(inst, cyccnt);
      case 0x9F:   /* LDMIB rn!, rlist^ */
        return arm_block_mem<AccLoad, true, true, AddrPreInc>(inst, cyccnt);


      case 0xA0 ... 0xAF:          /* B offset */
         reg[REG_PC] += inst.br_offset() + 8;
         cyccnt -= ws_cyc_nseq[reg[REG_PC] >> 24][1];
         break;
      case 0xB0 ... 0xBF:          /* BL offset */
         reg[REG_LR] = reg[REG_PC] + 4;
         reg[REG_PC] += inst.br_offset() + 8;
         cyccnt -= ws_cyc_nseq[reg[REG_PC] >> 24][1];
         break;

#ifdef HAVE_UNUSED
      case 0xC0 ... 0xEF:
         /* coprocessor instructions, reserved on GBA */
         break;
#endif

      case 0xF0 ... 0xFF:
        reg[REG_BUS_VALUE] = 0xe3a02004;  // After SWI, we read bios[0xE4]
        REG_MODE(MODE_SUPERVISOR)[6] = reg[REG_PC] + 4;
        REG_SPSR(MODE_SUPERVISOR) = reg[REG_CPSR];
        reg[REG_PC] = 0x00000008;
        // Move to ARM mode, Supervisor mode and disable IRQs
        reg[REG_CPSR] = (reg[REG_CPSR] & ~0x3F) | 0x13 | 0x80;
        set_cpu_mode(MODE_SUPERVISOR);
        break;
   }
   return CPU_ALERT_NONE;
}

void execute_arm(u32 cycles)
{
  u32 pc_region = ~0U;
  u8 *pc_address_block = NULL;
  s32 cyccnt;

  // Reload cycle counter
  cyccnt = cycles;

  while(1) {
    /* Do not execute until CPU is active */
    if (reg[CPU_HALT_STATE] != CPU_ACTIVE) {
       u32 ret = update_gba(cyccnt);
       if (completed_frame(ret))
          return;

       cyccnt = cycles_to_run(ret);
    }

    u32 cpu_alert = CPU_ALERT_NONE;

    while(cyccnt > 0) {
       /* Process cheats if we are about to execute the cheat hook */
       if (reg[REG_PC] == cheat_master_hook)
          process_cheats();

       /* Ensure we load/map instruction memory */
       check_pc_region();

       bool is_thumb = reg[REG_CPSR] & 0x20;

       // Account for instruction base execution time
       cyccnt -= ws_cyc_seq[(reg[REG_PC] >> 24) & 0xF][is_thumb ? 0 : 1];

       if (is_thumb) {
         // Thumb mode instruction
         using_instruction(thumb);
         reg[REG_PC] &= ~0x01;

         u16 opcode16 = read_mem<u16>(pc_address_block, (reg[REG_PC] & 0x7FFF));

         #ifdef TRACE_INSTRUCTIONS
         interp_trace_instruction(reg[REG_PC], 0);
         #endif

         cpu_alert = execute_thumb_instruction(opcode16, cyccnt);
       } else {
         // ARM mode
         using_instruction(arm);
         reg[REG_PC] &= ~0x03;

         u32 opcode32 = read_mem<u32>(pc_address_block, (reg[REG_PC] & 0x7FFF));

         if (arm_null_inst(opcode32))   // Check for instruction condition
           arm_pc_offset(4);
         else {
           #ifdef TRACE_INSTRUCTIONS
             interp_trace_instruction(reg[REG_PC], 1);
           #endif

           cpu_alert = execute_arm_instruction(opcode32, cyccnt);
         }
       }

       // Check for IRQ, raise (will change PC and CPU mode)
       if (cpu_alert & CPU_ALERT_IRQ)
         check_and_raise_interrupts();

       // Stop executing any further instruction.
       if (cpu_alert & CPU_ALERT_HALT)
         break;

       // On idle target consume all cycles immediately
       if (reg[REG_PC] == idle_loop_target_pc)
         cyccnt = 0;
    }

    // Process next event after consuming all cycles
    u32 update_ret = update_gba(cyccnt);
    if (completed_frame(update_ret))
       return;
    cyccnt = cycles_to_run(update_ret);
  }
}


