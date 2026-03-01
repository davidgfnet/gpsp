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

// Not-so-important todo:
// - stm reglist writeback when base is in the list needs adjustment
// - block memory needs psr swapping and user mode reg swapping

#include "common.h"
#include "cpu_dynarec.h"
#include "basedefs.h"
#include "util.h"

#if defined(VITA)
#include <psp2/kernel/sysmem.h>
#include <stdio.h>
#elif defined(PS2)
#include <kernel.h>
#endif

u8 *last_rom_translation_ptr = NULL;
u8 *last_ram_translation_ptr = NULL;

#if defined(MMAP_JIT_CACHE)
u8* rom_translation_cache;
u8* ram_translation_cache;
u8 *rom_translation_ptr;
u8 *ram_translation_ptr;
#elif defined(VITA)
u8* rom_translation_cache;
u8* ram_translation_cache;
u8 *rom_translation_ptr;
u8 *ram_translation_ptr;
int sceBlock;
#elif defined(_3DS) 
u8* rom_translation_cache_ptr;
u8* ram_translation_cache_ptr;
u8 *rom_translation_ptr = rom_translation_cache;
u8 *ram_translation_ptr = ram_translation_cache;
#else
u8 *rom_translation_ptr = rom_translation_cache;
u8 *ram_translation_ptr = ram_translation_cache;
#endif
/* Note, see stub files for more cache definitions */

u32 iwram_code_min = ~0U;
u32 iwram_code_max =  0U;
u32 ewram_code_min = ~0U;
u32 ewram_code_max =  0U;

#define INITIAL_ROM_WATERMARK   16   // To avoid NULL aliasing
u32 rom_cache_watermark = INITIAL_ROM_WATERMARK;

u8 *bios_swi_entrypoint = NULL;

// Contains an offset table to rom_translation cache area
// It features a chaining linked list for collisions
// The rom area has a small header section that contains:
//  - PC value for the entry
//  - Offset to the next entry (if any)
typedef struct {
  u32 pc_value;
  u32 next_entry;
} hashhdr_type;

u32 rom_branch_hash[ROM_BRANCH_HASH_SIZE];

typedef struct
{
  u8 *block_offset;
  u16 flag_data;
  u8 condition;
  u8 update_cycles;
} block_data_type;

typedef struct {
  u32 branch_target;
  u8 *branch_source;
} block_exit_type;

typedef enum {
  RegionROM, RegionRAM
} TranslRegion;

typedef enum {
  MulOnly, MulAdd
} MulMode;

/*typedef enum {
  OpAnd, OpOrr, OpXor, OpBic,
  OpAdd, OpAdc, OpSub, OpSbc,
  OpRsb, OpRsc,
  OpMul,
  OpNeg, OpMov, OpMvn,
  OpTst, OpTeq, OpCmp, OpCmn
} AluOperation;*/

typedef enum { OffReg, OffImm5, OffSP } ThumbMemOffset;

typedef enum { OffOp2Reg, OffHImm8, OffImm12, OffHReg } ARMMemOffset;
typedef enum { OffPositive, OffNegative } MemOffDir;
typedef enum { MemIdxPre, MemIdxPreWB, MemIdxPostWB } MemIdxMode;

typedef enum {
  AddrPreInc, AddrPreDec, AddrPostInc, AddrPostDec
} AddrMode;

// Div (6) and DivArm (7)
#define is_div_swi(swinum) (((swinum) & 0xFE) == 0x06)

/* Include the right emitter headers */
#if defined(MIPS_ARCH)
  #include "mips/mips_emit.h"
#elif defined(ARM_ARCH)
  #include "arm/arm_emit.h"
#elif defined(ARM64_ARCH)
  #include "arm/arm64_emit.h"
#else
  #include "x86/x86_emit.h"
#endif

/* Cache invalidation */

#if defined(PSP)
  void platform_cache_sync(void *baseaddr, void *endptr) {
    sceKernelDcacheWritebackRange(baseaddr, ((char*)endptr) - ((char*)baseaddr));
    sceKernelIcacheInvalidateRange(baseaddr, ((char*)endptr) - ((char*)baseaddr));
  }
#elif defined(PS2)
  void platform_cache_sync(void *baseaddr, void *endptr) {
    FlushCache(0);   // Dcache flush
    FlushCache(2);   // Icache invalidate
  }
#elif defined(VITA)
  void platform_cache_sync(void *baseaddr, void *endptr) {
    sceKernelSyncVMDomain(sceBlock, baseaddr, ((char*)endptr) - ((char*)baseaddr) + 64);
  }
#elif defined(_3DS)
  #include "3ds/3ds_utils.h"
  void platform_cache_sync(void *baseaddr, void *endptr) {
    ctr_flush_invalidate_cache();
  }
#elif defined(ARM_ARCH) || defined(ARM64_ARCH) || defined(MIPS_ARCH)
  void platform_cache_sync(void *baseaddr, void *endptr) {
    __builtin___clear_cache(baseaddr, endptr);
  }
#else
  /* x86 CPUs have icache consistency checks */
  void platform_cache_sync(void *baseaddr, void *endptr) {}
#endif

void translate_icache_sync() {
    // Cache emitted code can only grow
    if (last_rom_translation_ptr < rom_translation_ptr) {
        platform_cache_sync(last_rom_translation_ptr, rom_translation_ptr);
        last_rom_translation_ptr = rom_translation_ptr;
    }
    if (last_ram_translation_ptr < ram_translation_ptr) {
        platform_cache_sync(last_ram_translation_ptr, ram_translation_ptr);
        last_ram_translation_ptr = ram_translation_ptr;
    }
}


// Here's how this works: each instruction has three different sets of flag
// attributes, each consisiting of a 4bit mask describing how that instruction
// interacts with the 4 main flags (N/Z/C/V).
// The first set, in bits 0:3, is the set of flags the instruction may
// modify. After this pass this is changed to the set of flags the instruction
// should modify - if the bit for the corresponding flag is not set then code
// does not have to be generated to calculate the flag for that instruction.

// The second set, in bits 7:4, is the set of flags that the instruction must
// modify (ie, for shifts by the register values the instruction may not
// always modify the C flag, and thus the C bit won't be set here).

// The third set, in bits 11:8, is the set of flags that the instruction uses
// in its computation, or the set of flags that will be needed after the
// instruction is done. For any instructions that change the PC all of the
// bits should be set because it is (for now) unknown what flags will be
// needed after it arrives at its destination. Instructions that use the
// carry flag as input will have it set as well.

// The algorithm is a simple liveness analysis procedure: It starts at the
// bottom of the instruction stream and sets a "currently needed" mask to
// the flags needed mask of the current instruction. Then it moves down
// an instruction, ANDs that instructions "should generate" mask by the
// "currently needed" mask, then ANDs the "currently needed" mask by
// the 1's complement of the instruction's "must generate" mask, and ORs
// the "currently needed" mask by the instruction's "flags needed" mask.

template <typename T>
static void optimize_flag_elimination(T & insts) {
  uint8_t needed_flags = 0xF;
  for (int i = insts.size() - 1; i >= 0; i--) {
    unsigned imsk = insts[i].flag_status;
    insts[i].flag_status = imsk & needed_flags;
    needed_flags &= ~((imsk >> 4) & 0xF);        // Flags generated by the inst.
    needed_flags |= (imsk >> 8);                 // Needed flags for this inst.
  }
}


// I/EWRAM memory tagging
// Code emitted in the RAM cache has tags (16 bit values) in the mirror tag ram
// that indicate that the address contains code. The following values are used:
// 0x0000 : this is just data (never translated)
// 0x00XX : not used (since first byte is zero)
// 0x0101 : this is code that is not the start of a translated block
// 0xXXXX : this is the start of a translated block, starting from 0xFFFF downwards
//          LSB is always set (we decrement by two) to ensure both bytes != 0
//
// The tag value is an index to a `ramtag_type` structure that sits at the end
// of the RAM CACHE (grows like a stack). For simplicity we start tags at 0xFFFF
// and grow like a stack.

#define LAST_TAG_NUM       0x0101
#define INITIAL_TOP_TAG    0xFFFF
#define CODE_TAG_BLOCK16   0x0101
#define CODE_TAG_BLOCK32   0x01010101

#define VALID_TAG(tagn) (tagn > LAST_TAG_NUM)

#define allocate_tag_arm(location) {   \
  location[0] = ram_block_tag;         \
  /* Could be another thumb inst */    \
  if (!location[1])                    \
    location[1] = CODE_TAG_BLOCK16;    \
  ram_block_tag -= 2;                  \
}


typedef struct {
  u32 offset_arm;     // Cache offset to the ARM-mode compiled block
  u32 offset_thumb;   // Cache offset to the Thumb-mode compiled block
} ramtag_type;

static u32 ram_block_tag = INITIAL_TOP_TAG;

inline static ramtag_type* get_ram_tag(u16 tagval) {
  ramtag_type *tbl = (ramtag_type*)&ram_translation_cache[RAM_TRANSLATION_CACHE_SIZE];
  int tgidx = (tagval >> 1) - 0x8000;   /* Since LSB is always 1 and thus unused */
  return &tbl[tgidx];
}

static inline bool pc_on_ram(uint32_t pc) {
  return (pc >> 25) == 1;   // PC is 0x02XXXXXX or 0x03XXXXXX
}

template <TranslRegion region>
class JITArea {
public:
  JITArea() { }

  // Returns the current JIT area pointer.
  inline uint8_t *cur_ptr() {
    return region == RegionRAM ? ram_translation_ptr : rom_translation_ptr;
  }

  // Updates the cache pointer (ie. after some emitting has happened).
  inline void update_ptr(uint8_t *ptr) {
    if (region == RegionRAM)
      ram_translation_ptr = ptr;
    else
      rom_translation_ptr = ptr;
  }

  // Returns the space remaining in the buffer.
  inline int avail() {
    if (region == RegionRAM)
      return RAM_TRANSLATION_CACHE_SIZE - TRANSLATION_CACHE_LIMIT_THRESHOLD
              - (ram_translation_ptr - ram_translation_cache)
              - ((0x10000 - ram_block_tag) / 2 * sizeof(ramtag_type));
    else
      return ROM_TRANSLATION_CACHE_SIZE - TRANSLATION_CACHE_LIMIT_THRESHOLD
              - (rom_translation_ptr - rom_translation_cache);
  }

  // Whether we overflowed the JIT area (has some guard space to avoid a real overflow).
  bool overflow() {
    return avail() < 0;
  }

  // Flush the cache.
  void flush_cache() {
    if (region == RegionRAM)
      flush_translation_cache_ram();
    else
      flush_translation_cache_rom();
  }

};

#define MAX_BLOCK_SIZE   1024   // 2/4KiB blocks max
#define MAX_EXITS          32   // This covers 99% blocks
#define MAX_LINKQ_SIZE   2048   // 1K should cover it all, 2K just in case

/* End of Cache invalidation */

#define check_pc_region(pc) {                                                 \
  u32 new_pc_region = (pc >> 15);                                             \
  if (new_pc_region != pc_region) {                                           \
    pc_region = new_pc_region;                                                \
    pc_address_block = memory_map_read[new_pc_region];                        \
                                                                              \
    if(!pc_address_block)                                                     \
      pc_address_block = load_gamepak_page(pc_region & 0x3FF);                \
  }                                                                           \
}

#define translate_arm_instruction()                                           \
  check_pc_region(pc);                                                        \
  opcode = address32(pc_address_block, (pc & 0x7FFF));                        \
  condition = block_data[block_data_position].condition;                      \
  ARMInst inst(pc, opcode, 0xF /* TODO: Add ARM flag elimination */);         \
                                                                              \
  if((condition != last_condition) || (condition >= 0x20))                    \
  {                                                                           \
    if((last_condition & 0x0F) != 0x0E)                                       \
    {                                                                         \
      if (backpatch_address) {                                                \
        generate_branch_patch_conditional(backpatch_address, ce.emit_ptr);    \
        backpatch_address = NULL;                                             \
      }                                                                       \
    }                                                                         \
                                                                              \
    last_condition = condition;                                               \
                                                                              \
    condition &= 0x0F;                                                        \
                                                                              \
    if(condition != 0x0E)                                                     \
    {                                                                         \
      ce.arm_conditional_block_header(condition, backpatch_address);          \
    }                                                                         \
  }                                                                           \
  ce.trace_instruction<ModeARM>(pc, opcode);                                  \
                                                                              \
  switch((opcode >> 20) & 0xFF)                                               \
  {                                                                           \
    case 0x00:                                                                \
      if((opcode & 0x90) == 0x90)                                             \
      {                                                                       \
        if (opcode & 0x20)     /* STRH rd, [rn], -rm */                       \
          ce.arm_memst<u16, OffHReg, OffNegative, MemIdxPostWB>(inst);        \
        else {                                                                \
          /* MUL rd, rm, rs */                                                \
          ce.arm_mul32<NoFlags, MulOnly>(inst);                               \
          ce.cyc_cnt += 2;  /* variable 1..4, pick 2 as an aprox. */          \
        }                                                                     \
      }                                                                       \
      else         /* AND rd, rn, reg_op */                                   \
        ce.arm_alureg3<OpAnd, NoFlags>(inst);                                 \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x01:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03)                                          \
        {                                                                     \
          case 0:  /* MULS rd, rm, rs */                                      \
            ce.arm_mul32<SetFlags, MulOnly>(inst);                            \
            ce.cyc_cnt += 2;  /* variable 1..4, pick 2 as an aprox. */        \
            break;                                                            \
          case 1:  /* LDRH rd, [rn], -rm */                                   \
            ce.arm_memld<u16, OffHReg, OffNegative, MemIdxPostWB>(inst);      \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn], -rm */                                  \
            ce.arm_memld<s8, OffHReg, OffNegative, MemIdxPostWB>(inst);       \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn], -rm */                                  \
            ce.arm_memld<s16, OffHReg, OffNegative, MemIdxPostWB>(inst);      \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* ANDS rd, rn, reg_op */                                  \
        ce.arm_alureg3<OpAnd, SetFlags>(inst);                                \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x02:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        if (opcode & 0x20)     /* STRH rd, [rn], -rm */                       \
          ce.arm_memst<u16, OffHReg, OffNegative, MemIdxPostWB>(inst);        \
        else {                                                                \
          /* MLA rd, rm, rs, rn */                                            \
          ce.arm_mul32<NoFlags, MulAdd>(inst);                                \
          ce.cyc_cnt += 3;  /* variable 2..5, pick 3 as an aprox. */          \
        }                                                                     \
      }                                                                       \
      else         /* XOR rd, rn, reg_op */                                   \
        ce.arm_alureg3<OpXor, NoFlags>(inst);                                 \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x03:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 0:                                                             \
            /* MLAS rd, rm, rs, rn */                                         \
            ce.arm_mul32<SetFlags, MulAdd>(inst);                             \
            ce.cyc_cnt += 3;  /* variable 2..5, pick 3 as an aprox. */        \
            break;                                                            \
          case 1:  /* LDRH rd, [rn], -rm */                                   \
            ce.arm_memld<u16, OffHReg, OffNegative, MemIdxPostWB>(inst);      \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn], -rm */                                  \
            ce.arm_memld<s8, OffHReg, OffNegative, MemIdxPostWB>(inst);       \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn], -rm */                                  \
            ce.arm_memld<s16, OffHReg, OffNegative, MemIdxPostWB>(inst);      \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* XORS rd, rn, reg_op */                                  \
        ce.arm_alureg3<OpXor, SetFlags>(inst);                                \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x04:                                                                \
      if((opcode & 0x90) == 0x90)      /* STRH rd, [rn], -imm */              \
        ce.arm_memst<u16, OffHImm8, OffNegative, MemIdxPostWB>(inst);         \
      else         /* SUB rd, rn, reg_op */                                   \
        ce.arm_alureg3<OpSub, NoFlags>(inst);                                 \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x05:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 1:  /* LDRH rd, [rn], -imm */                                  \
            ce.arm_memld<u16, OffHImm8, OffNegative, MemIdxPostWB>(inst);     \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn], -imm */                                 \
            ce.arm_memld<s8, OffHImm8, OffNegative, MemIdxPostWB>(inst);      \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn], -imm */                                 \
            ce.arm_memld<s16, OffHImm8, OffNegative, MemIdxPostWB>(inst);     \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* SUBS rd, rn, reg_op */                                  \
        ce.arm_alureg3<OpSub, SetFlags>(inst);                                \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x06:                                                                \
      if((opcode & 0x90) == 0x90)      /* STRH rd, [rn], -imm */              \
        ce.arm_memst<u16, OffHImm8, OffNegative, MemIdxPostWB>(inst);         \
      else         /* RSB rd, rn, reg_op */                                   \
        ce.arm_alureg3<OpRsb, NoFlags>(inst);                                 \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x07:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 1:  /* LDRH rd, [rn], -imm */                                  \
            ce.arm_memld<u16, OffHImm8, OffNegative, MemIdxPostWB>(inst);     \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn], -imm */                                 \
            ce.arm_memld<s8, OffHImm8, OffNegative, MemIdxPostWB>(inst);      \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn], -imm */                                 \
            ce.arm_memld<s16, OffHImm8, OffNegative, MemIdxPostWB>(inst);     \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* RSBS rd, rn, reg_op */                                  \
        ce.arm_alureg3<OpRsb, SetFlags>(inst);                                \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x08:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        if(opcode & 0x20)              /* STRH rd, [rn], +rm */               \
          ce.arm_memst<u16, OffHReg, OffPositive, MemIdxPostWB>(inst);        \
        else {                                                                \
          /* UMULL rd, rm, rs */                                              \
          ce.arm_mul64<NoFlags, MulOnly, false>(inst);                        \
          ce.cyc_cnt += 3;  /* this is an aproximation :P */                  \
        }                                                                     \
      }                                                                       \
      else         /* ADD rd, rn, reg_op */                                   \
        ce.arm_alureg3<OpAdd, NoFlags>(inst);                                 \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x09:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 0:                                                             \
            /* UMULLS rdlo, rdhi, rm, rs */                                   \
            ce.arm_mul64<SetFlags, MulOnly, false>(inst);                     \
            ce.cyc_cnt += 3;  /* this is an aproximation :P */                \
            break;                                                            \
          case 1:  /* LDRH rd, [rn], +rm */                                   \
            ce.arm_memld<u16, OffHReg, OffPositive, MemIdxPostWB>(inst);      \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn], +rm */                                  \
            ce.arm_memld<s8, OffHReg, OffPositive, MemIdxPostWB>(inst);       \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn], +rm */                                  \
            ce.arm_memld<s16, OffHReg, OffPositive, MemIdxPostWB>(inst);      \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* ADDS rd, rn, reg_op */                                  \
        ce.arm_alureg3<OpAdd, SetFlags>(inst);                                \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x0A:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        if(opcode & 0x20)              /* STRH rd, [rn], +rm */               \
          ce.arm_memst<u16, OffHReg, OffPositive, MemIdxPostWB>(inst);        \
        else                                                                  \
        {                                                                     \
          /* UMLAL rd, rm, rs */                                              \
          ce.arm_mul64<NoFlags, MulAdd, false>(inst);                         \
          ce.cyc_cnt += 3;  /* Between 2 and 5 cycles? */                     \
        }                                                                     \
      }                                                                       \
      else         /* ADC rd, rn, reg_op */                                   \
        ce.arm_alureg3<OpAdc, NoFlags>(inst);                                 \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x0B:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 0:                                                             \
            /* UMLALS rdlo, rdhi, rm, rs */                                   \
            ce.arm_mul64<SetFlags, MulAdd, false>(inst);                      \
            ce.cyc_cnt += 3;  /* Between 2 and 5 cycles? */                   \
            break;                                                            \
          case 1:  /* LDRH rd, [rn], +rm */                                   \
            ce.arm_memld<u16, OffHReg, OffPositive, MemIdxPostWB>(inst);      \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn], +rm */                                  \
            ce.arm_memld<s8, OffHReg, OffPositive, MemIdxPostWB>(inst);       \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn], +rm */                                  \
            ce.arm_memld<s16, OffHReg, OffPositive, MemIdxPostWB>(inst);      \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* ADCS rd, rn, reg_op */                                  \
        ce.arm_alureg3<OpAdc, SetFlags>(inst);                                \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x0C:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        if(opcode & 0x20)              /* STRH rd, [rn], +imm */              \
          ce.arm_memst<u16, OffHImm8, OffPositive, MemIdxPostWB>(inst);       \
        else                                                                  \
        {                                                                     \
          /* SMULL rd, rm, rs */                                              \
          ce.arm_mul64<NoFlags, MulOnly, true>(inst);                         \
          ce.cyc_cnt += 2;  /* Between 1 and 4 cycles? */                     \
        }                                                                     \
      }                                                                       \
      else         /* SBC rd, rn, reg_op */                                   \
        ce.arm_alureg3<OpSbc, NoFlags>(inst);                                 \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x0D:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 0:                                                             \
            /* SMULLS rdlo, rdhi, rm, rs */                                   \
            ce.arm_mul64<SetFlags, MulOnly, true>(inst);                      \
            ce.cyc_cnt += 2;  /* Between 1 and 4 cycles? */                   \
            break;                                                            \
          case 1:  /* LDRH rd, [rn], +imm */                                  \
            ce.arm_memld<u16, OffHImm8, OffPositive, MemIdxPostWB>(inst);     \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn], +imm */                                 \
            ce.arm_memld<s8, OffHImm8, OffPositive, MemIdxPostWB>(inst);      \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn], +imm */                                 \
            ce.arm_memld<s16, OffHImm8, OffPositive, MemIdxPostWB>(inst);     \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* SBCS rd, rn, reg_op */                                  \
        ce.arm_alureg3<OpSbc, SetFlags>(inst);                                \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x0E:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        if(opcode & 0x20)              /* STRH rd, [rn], +imm */              \
          ce.arm_memst<u16, OffHImm8, OffPositive, MemIdxPostWB>(inst);       \
        else                                                                  \
        {                                                                     \
          /* SMLAL rd, rm, rs */                                              \
          ce.arm_mul64<NoFlags, MulAdd, true>(inst);                          \
          ce.cyc_cnt += 3;  /* Between 2 and 5 cycles? */                     \
        }                                                                     \
      }                                                                       \
      else         /* RSC rd, rn, reg_op */                                   \
        ce.arm_alureg3<OpRsc, NoFlags>(inst);                                 \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x0F:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 0:                                                             \
            /* SMLALS rdlo, rdhi, rm, rs */                                   \
            ce.arm_mul64<SetFlags, MulAdd, true>(inst);                       \
            ce.cyc_cnt += 3;  /* Between 2 and 5 cycles? */                   \
            break;                                                            \
          case 1:  /* LDRH rd, [rn], +imm */                                  \
            ce.arm_memld<u16, OffHImm8, OffPositive, MemIdxPostWB>(inst);     \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn], +imm */                                 \
            ce.arm_memld<s8, OffHImm8, OffPositive, MemIdxPostWB>(inst);      \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn], +imm */                                 \
            ce.arm_memld<s16, OffHImm8, OffPositive, MemIdxPostWB>(inst);     \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* RSCS rd, rn, reg_op */                                  \
        ce.arm_alureg3<OpRsc, SetFlags>(inst);                                \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x10:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        if(opcode & 0x20)              /* STRH rd, [rn - rm] */               \
          ce.arm_memst<u16, OffHReg, OffNegative, MemIdxPre>(inst);           \
        else                           /* SWP rd, rm, [rn] */                 \
          ce.arm_swap<u32>(inst);                                             \
      }                                                                       \
      else     /* MRS rd, cpsr */                                             \
        ce.arm_read_psr<RegCPSR>(inst);                                       \
      break;                                                                  \
                                                                              \
    case 0x11:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 1:  /* LDRH rd, [rn - rm] */                                   \
            ce.arm_memld<u16, OffHReg, OffNegative, MemIdxPre>(inst);         \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn - rm] */                                  \
            ce.arm_memld<s8, OffHReg, OffNegative, MemIdxPre>(inst);          \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn - rm] */                                  \
            ce.arm_memld<s16, OffHReg, OffNegative, MemIdxPre>(inst);         \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* TST rn, reg_op */                                       \
        ce.arm_alureg2<OpTst, SetFlags>(inst);                                \
      break;                                                                  \
                                                                              \
    case 0x12:                                                                \
      if((opcode & 0x90) == 0x90)      /* STRH rd, [rn - rm]! */              \
        ce.arm_memst<u16, OffHReg, OffNegative, MemIdxPreWB>(inst);           \
      else {                                                                  \
        if (opcode & 0x10)   /* BX rm */                                      \
          ce.arm_bx(inst);                                                    \
        else     /* MSR cpsr, rm */                                           \
          ce.arm_write_psr<RegCPSR, OpReg>(inst);                             \
      }                                                                       \
      break;                                                                  \
                                                                              \
    case 0x13:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 1:  /* LDRH rd, [rn - rm]! */                                  \
            ce.arm_memld<u16, OffHReg, OffNegative, MemIdxPreWB>(inst);       \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn - rm]! */                                 \
            ce.arm_memld<s8, OffHReg, OffNegative, MemIdxPreWB>(inst);        \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn - rm]! */                                 \
            ce.arm_memld<s16, OffHReg, OffNegative, MemIdxPreWB>(inst);       \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* TEQ rn, reg_op */                                       \
        ce.arm_alureg2<OpTeq, SetFlags>(inst);                                \
      break;                                                                  \
                                                                              \
    case 0x14:                                                                \
      if((opcode & 0x90) == 0x90)                                             \
      {                                                                       \
        if(opcode & 0x20)              /* STRH rd, [rn - imm] */              \
          ce.arm_memst<u16, OffHImm8, OffNegative, MemIdxPre>(inst);          \
        else                           /* SWPB rd, rm, [rn] */                \
          ce.arm_swap<u8>(inst);                                              \
      }                                                                       \
      else     /* MRS rd, spsr */                                             \
        ce.arm_read_psr<RegSPSR>(inst);                                       \
      break;                                                                  \
                                                                              \
    case 0x15:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 1:  /* LDRH rd, [rn - imm] */                                  \
            ce.arm_memld<u16, OffHImm8, OffNegative, MemIdxPre>(inst);        \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn - imm] */                                 \
            ce.arm_memld<s8, OffHImm8, OffNegative, MemIdxPre>(inst);         \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn - imm] */                                 \
            ce.arm_memld<s16, OffHImm8, OffNegative, MemIdxPre>(inst);        \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* CMP rn, reg_op */                                       \
        ce.arm_alureg2<OpCmp, NoFlags>(inst);                                 \
      break;                                                                  \
                                                                              \
    case 0x16:                                                                \
      if((opcode & 0x90) == 0x90)      /* STRH rd, [rn - imm]! */             \
        ce.arm_memst<u16, OffHImm8, OffNegative, MemIdxPreWB>(inst);          \
      else     /* MSR spsr, rm */                                             \
        ce.arm_write_psr<RegSPSR, OpReg>(inst);                               \
      break;                                                                  \
                                                                              \
    case 0x17:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 1:  /* LDRH rd, [rn - imm]! */                                 \
            ce.arm_memld<u16, OffHImm8, OffNegative, MemIdxPreWB>(inst);      \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn - imm]! */                                \
            ce.arm_memld<s8, OffHImm8, OffNegative, MemIdxPreWB>(inst);       \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn - imm]! */                                \
            ce.arm_memld<s16, OffHImm8, OffNegative, MemIdxPreWB>(inst);      \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* CMN rn, reg_op */                                       \
        ce.arm_alureg2<OpCmn, NoFlags>(inst);                                 \
      break;                                                                  \
                                                                              \
    case 0x18:                                                                \
      if((opcode & 0x90) == 0x90)      /* STRH rd, [rn + rm] */               \
        ce.arm_memst<u16, OffHReg, OffPositive, MemIdxPre>(inst);             \
      else         /* ORR rd, rn, reg_op */                                   \
        ce.arm_alureg3<OpOrr, NoFlags>(inst);                                 \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x19:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 1:  /* LDRH rd, [rn + rm] */                                   \
            ce.arm_memld<u16, OffHReg, OffPositive, MemIdxPre>(inst);         \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn + rm] */                                  \
            ce.arm_memld<s8, OffHReg, OffPositive, MemIdxPre>(inst);          \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn + rm] */                                  \
            ce.arm_memld<s16, OffHReg, OffPositive, MemIdxPre>(inst);         \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* ORRS rd, rn, reg_op */                                  \
        ce.arm_alureg3<OpOrr, SetFlags>(inst);                                \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x1A:                                                                \
      if((opcode & 0x90) == 0x90)      /* STRH rd, [rn + rm]! */              \
        ce.arm_memst<u16, OffHReg, OffPositive, MemIdxPreWB>(inst);           \
      else         /* MOV rd, reg_op */                                       \
        ce.arm_alureg1<OpMov, NoFlags>(inst);                                 \
      break;                                                                  \
                                                                              \
    case 0x1B:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 1:  /* LDRH rd, [rn + rm]! */                                  \
            ce.arm_memld<u16, OffHReg, OffPositive, MemIdxPreWB>(inst);       \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn + rm]! */                                 \
            ce.arm_memld<s8, OffHReg, OffPositive, MemIdxPreWB>(inst);        \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn + rm]! */                                 \
            ce.arm_memld<s16, OffHReg, OffPositive, MemIdxPreWB>(inst);       \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* MOVS rd, reg_op */                                      \
        ce.arm_alureg1<OpMov, SetFlags>(inst);                                \
      break;                                                                  \
                                                                              \
    case 0x1C:                                                                \
      if((opcode & 0x90) == 0x90)      /* STRH rd, [rn + imm] */              \
        ce.arm_memst<u16, OffHImm8, OffPositive, MemIdxPre>(inst);            \
      else         /* BIC rd, rn, reg_op */                                   \
        ce.arm_alureg3<OpBic, NoFlags>(inst);                                 \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x1D:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 1:  /* LDRH rd, [rn + imm] */                                  \
            ce.arm_memld<u16, OffHImm8, OffPositive, MemIdxPre>(inst);        \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn + imm] */                                 \
            ce.arm_memld<s8, OffHImm8, OffPositive, MemIdxPre>(inst);         \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn + imm] */                                 \
            ce.arm_memld<s16, OffHImm8, OffPositive, MemIdxPre>(inst);        \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* BIC rd, rn, reg_op */                                   \
        ce.arm_alureg3<OpBic, SetFlags>(inst);                                \
                                                                              \
      break;                                                                  \
                                                                              \
    case 0x1E:                                                                \
      if((opcode & 0x90) == 0x90)      /* STRH rd, [rn + imm]! */             \
        ce.arm_memst<u16, OffHImm8, OffPositive, MemIdxPreWB>(inst);          \
      else         /* MVN rd, reg_op */                                       \
        ce.arm_alureg1<OpMvn, NoFlags>(inst);                                 \
      break;                                                                  \
                                                                              \
    case 0x1F:                                                                \
      if((opcode & 0x90) == 0x90) {                                           \
        switch((opcode >> 5) & 0x03) {                                        \
          case 1:  /* LDRH rd, [rn + imm]! */                                 \
            ce.arm_memld<u16, OffHImm8, OffPositive, MemIdxPreWB>(inst);      \
            break;                                                            \
          case 2:  /* LDRSB rd, [rn + imm]! */                                \
            ce.arm_memld<s8, OffHImm8, OffPositive, MemIdxPreWB>(inst);       \
            break;                                                            \
          case 3:  /* LDRSH rd, [rn + imm]! */                                \
            ce.arm_memld<s16, OffHImm8, OffPositive, MemIdxPreWB>(inst);      \
            break;                                                            \
        }                                                                     \
      }                                                                       \
      else         /* MVNS rd, reg_op */                                      \
        ce.arm_alureg1<OpMvn, SetFlags>(inst);                                \
      break;                                                                  \
                                                                              \
    case 0x20:     /* AND rd, rn, imm */                                      \
      ce.arm_aluimm3<OpAnd, NoFlags>(inst);                                   \
      break;                                                                  \
    case 0x21:     /* ANDS rd, rn, imm */                                     \
      ce.arm_aluimm3<OpAnd, SetFlags>(inst);                                  \
      break;                                                                  \
    case 0x22:     /* EOR rd, rn, imm */                                      \
      ce.arm_aluimm3<OpXor, NoFlags>(inst);                                   \
      break;                                                                  \
    case 0x23:     /* EORS rd, rn, imm */                                     \
      ce.arm_aluimm3<OpXor, SetFlags>(inst);                                  \
      break;                                                                  \
    case 0x24:     /* SUB rd, rn, imm */                                      \
      ce.arm_aluimm3<OpSub, NoFlags>(inst);                                   \
      break;                                                                  \
    case 0x25:     /* SUBS rd, rn, imm */                                     \
      ce.arm_aluimm3<OpSub, SetFlags>(inst);                                  \
      break;                                                                  \
    case 0x26:     /* RSB rd, rn, imm */                                      \
      ce.arm_aluimm3<OpRsb, NoFlags>(inst);                                   \
      break;                                                                  \
    case 0x27:     /* RSBS rd, rn, imm */                                     \
      ce.arm_aluimm3<OpRsb, SetFlags>(inst);                                  \
      break;                                                                  \
    case 0x28:     /* ADD rd, rn, imm */                                      \
      ce.arm_aluimm3<OpAdd, NoFlags>(inst);                                   \
      break;                                                                  \
    case 0x29:     /* ADDS rd, rn, imm */                                     \
      ce.arm_aluimm3<OpAdd, SetFlags>(inst);                                  \
      break;                                                                  \
    case 0x2A:     /* ADC rd, rn, imm */                                      \
      ce.arm_aluimm3<OpAdc, NoFlags>(inst);                                   \
      break;                                                                  \
    case 0x2B:     /* ADCS rd, rn, imm */                                     \
      ce.arm_aluimm3<OpAdc, SetFlags>(inst);                                  \
      break;                                                                  \
    case 0x2C:     /* SBC rd, rn, imm */                                      \
      ce.arm_aluimm3<OpSbc, NoFlags>(inst);                                   \
      break;                                                                  \
    case 0x2D:     /* SBCS rd, rn, imm */                                     \
      ce.arm_aluimm3<OpSbc, SetFlags>(inst);                                  \
      break;                                                                  \
    case 0x2E:     /* RSC rd, rn, imm */                                      \
      ce.arm_aluimm3<OpRsc, NoFlags>(inst);                                   \
      break;                                                                  \
    case 0x2F:     /* RSCS rd, rn, imm */                                     \
      ce.arm_aluimm3<OpRsc, SetFlags>(inst);                                  \
      break;                                                                  \
    case 0x30 ... 0x31:      /* TST rn, imm */                                \
      ce.arm_aluimm2<OpTst>(inst);                                            \
      break;                                                                  \
                                                                              \
    case 0x32:                                                                \
      ce.arm_write_psr<RegCPSR, OpImm>(inst);                                 \
      break;                                                                  \
    case 0x36:                                                                \
      ce.arm_write_psr<RegSPSR, OpImm>(inst);                                 \
      break;                                                                  \
                                                                              \
    case 0x33:     /* TEQ rn, imm */                                          \
      ce.arm_aluimm2<OpTeq>(inst);                                            \
      break;                                                                  \
    case 0x34 ... 0x35:      /* CMP rn, imm */                                \
      ce.arm_aluimm2<OpCmp>(inst);                                            \
      break;                                                                  \
    case 0x37:     /* CMN rn, imm */                                          \
      ce.arm_aluimm2<OpCmn>(inst);                                            \
      break;                                                                  \
    case 0x38:     /* ORR rd, rn, imm */                                      \
      ce.arm_aluimm3<OpOrr, NoFlags>(inst);                                   \
      break;                                                                  \
    case 0x39:     /* ORRS rd, rn, imm */                                     \
      ce.arm_aluimm3<OpOrr, SetFlags>(inst);                                  \
      break;                                                                  \
    case 0x3A:     /* MOV rd, imm */                                          \
      ce.arm_aluimm1<OpMov, NoFlags>(inst);                                   \
      break;                                                                  \
    case 0x3B:     /* MOVS rd, imm */                                         \
      ce.arm_aluimm1<OpMov, SetFlags>(inst);                                  \
      break;                                                                  \
    case 0x3C:     /* BIC rd, rn, imm */                                      \
      ce.arm_aluimm3<OpBic, NoFlags>(inst);                                   \
      break;                                                                  \
    case 0x3D:     /* BICS rd, rn, imm */                                     \
      ce.arm_aluimm3<OpBic, SetFlags>(inst);                                  \
      break;                                                                  \
    case 0x3E:     /* MVN rd, imm */                                          \
      ce.arm_aluimm1<OpMvn, NoFlags>(inst);                                   \
      break;                                                                  \
    case 0x3F:     /* MVNS rd, imm */                                         \
      ce.arm_aluimm1<OpMvn, SetFlags>(inst);                                  \
      break;                                                                  \
                                                                              \
    /* Memops with immediate post-increment/decrement */                      \
    case 0x40:     /* STR  rd, [rn], -imm */                                  \
    case 0x42:     /* STRT rd, [rn], -imm */                                  \
      ce.arm_memst<u32, OffImm12, OffNegative, MemIdxPostWB>(inst);           \
      break;                                                                  \
                                                                              \
    case 0x41:     /* LDR  rd, [rn], -imm */                                  \
    case 0x43:     /* LDRT rd, [rn], -imm */                                  \
      ce.arm_memld<u32, OffImm12, OffNegative, MemIdxPostWB>(inst);           \
      break;                                                                  \
                                                                              \
    case 0x44:     /* STRB  rd, [rn], -imm */                                 \
    case 0x46:     /* STRBT rd, [rn], -imm */                                 \
      ce.arm_memst<u8, OffImm12, OffNegative, MemIdxPostWB>(inst);            \
      break;                                                                  \
                                                                              \
    case 0x45:     /* LDRB  rd, [rn], -imm */                                 \
    case 0x47:     /* LDRBT rd, [rn], -imm */                                 \
      ce.arm_memld<u8, OffImm12, OffNegative, MemIdxPostWB>(inst);            \
      break;                                                                  \
                                                                              \
    case 0x48:     /* STR  rd, [rn], +imm */                                  \
    case 0x4A:     /* STRT rd, [rn], +imm */                                  \
      ce.arm_memst<u32, OffImm12, OffPositive, MemIdxPostWB>(inst);           \
      break;                                                                  \
                                                                              \
    case 0x49:     /* LDR  rd, [rn], +imm */                                  \
    case 0x4B:     /* LDRT rd, [rn], +imm */                                  \
      ce.arm_memld<u32, OffImm12, OffPositive, MemIdxPostWB>(inst);           \
      break;                                                                  \
                                                                              \
    case 0x4C:     /* STRB  rd, [rn], +imm */                                 \
    case 0x4E:     /* STRBT rd, [rn], +imm */                                 \
      ce.arm_memst<u8, OffImm12, OffPositive, MemIdxPostWB>(inst);            \
      break;                                                                  \
                                                                              \
    case 0x4D:     /* LDRB  rd, [rn], +imm */                                 \
    case 0x4F:     /* LDRBT rd, [rn], +imm */                                 \
      ce.arm_memld<u8, OffImm12, OffPositive, MemIdxPostWB>(inst);            \
      break;                                                                  \
                                                                              \
    /* Memops with immediate pre-increment/decrement (optional writeback) */  \
    case 0x50:     /* STR rd, [rn - imm] */                                   \
      ce.arm_memst<u32, OffImm12, OffNegative, MemIdxPre>(inst);              \
      break;                                                                  \
                                                                              \
    case 0x51:     /* LDR rd, [rn - imm] */                                   \
      ce.arm_memld<u32, OffImm12, OffNegative, MemIdxPre>(inst);              \
      break;                                                                  \
                                                                              \
    case 0x52:     /* STR rd, [rn - imm]! */                                  \
      ce.arm_memst<u32, OffImm12, OffNegative, MemIdxPreWB>(inst);            \
      break;                                                                  \
                                                                              \
    case 0x53:     /* LDR rd, [rn - imm]! */                                  \
      ce.arm_memld<u32, OffImm12, OffNegative, MemIdxPreWB>(inst);            \
      break;                                                                  \
                                                                              \
    case 0x54:     /* STRB rd, [rn - imm] */                                  \
      ce.arm_memst<u8, OffImm12, OffNegative, MemIdxPre>(inst);               \
      break;                                                                  \
                                                                              \
    case 0x55:     /* LDRB rd, [rn - imm] */                                  \
      ce.arm_memld<u8, OffImm12, OffNegative, MemIdxPre>(inst);               \
      break;                                                                  \
                                                                              \
    case 0x56:     /* STRB rd, [rn - imm]! */                                 \
      ce.arm_memst<u8, OffImm12, OffNegative, MemIdxPreWB>(inst);             \
      break;                                                                  \
                                                                              \
    case 0x57:     /* LDRB rd, [rn - imm]! */                                 \
      ce.arm_memld<u8, OffImm12, OffNegative, MemIdxPreWB>(inst);             \
      break;                                                                  \
                                                                              \
    case 0x58:     /* STR rd, [rn + imm] */                                   \
      ce.arm_memst<u32, OffImm12, OffPositive, MemIdxPre>(inst);              \
      break;                                                                  \
                                                                              \
    case 0x59:     /* LDR rd, [rn + imm] */                                   \
      ce.arm_memld<u32, OffImm12, OffPositive, MemIdxPre>(inst);              \
      break;                                                                  \
                                                                              \
    case 0x5A:     /* STR rd, [rn + imm]! */                                  \
      ce.arm_memst<u32, OffImm12, OffPositive, MemIdxPreWB>(inst);            \
      break;                                                                  \
                                                                              \
    case 0x5B:     /* LDR rd, [rn + imm]! */                                  \
      ce.arm_memld<u32, OffImm12, OffPositive, MemIdxPreWB>(inst);            \
      break;                                                                  \
                                                                              \
    case 0x5C:     /* STRB rd, [rn + imm] */                                  \
      ce.arm_memst<u8, OffImm12, OffPositive, MemIdxPre>(inst);               \
      break;                                                                  \
                                                                              \
    case 0x5D:     /* LDRB rd, [rn + imm] */                                  \
      ce.arm_memld<u8, OffImm12, OffPositive, MemIdxPre>(inst);               \
      break;                                                                  \
                                                                              \
    case 0x5E:     /* STRB rd, [rn + imm]! */                                 \
      ce.arm_memst<u8, OffImm12, OffPositive, MemIdxPreWB>(inst);             \
      break;                                                                  \
                                                                              \
    case 0x5F:     /* LDRB rd, [rn + imm]! */                                 \
      ce.arm_memld<u8, OffImm12, OffPositive, MemIdxPreWB>(inst);             \
      break;                                                                  \
                                                                              \
    /* Memops with regop as post-increment/decrement */                       \
    case 0x60:     /* STR  rd, [rn], -rm */                                   \
    case 0x62:     /* STRT rd, [rn], -rm */                                   \
      ce.arm_memst<u32, OffOp2Reg, OffNegative, MemIdxPostWB>(inst);          \
      break;                                                                  \
    case 0x64:     /* STRB  rd, [rn], -rm */                                  \
    case 0x66:     /* STRBT rd, [rn], -rm */                                  \
      ce.arm_memst<u8, OffOp2Reg, OffNegative, MemIdxPostWB>(inst);           \
      break;                                                                  \
                                                                              \
    case 0x61:     /* LDR  rd, [rn], -rm */                                   \
    case 0x63:     /* LDRT rd, [rn], -rm */                                   \
      ce.arm_memld<u32, OffOp2Reg, OffNegative, MemIdxPostWB>(inst);          \
      break;                                                                  \
    case 0x65:     /* LDRB  rd, [rn], -rm */                                  \
    case 0x67:     /* LDRBT rd, [rn], -rm */                                  \
      ce.arm_memld<u8, OffOp2Reg, OffNegative, MemIdxPostWB>(inst);           \
      break;                                                                  \
                                                                              \
    case 0x68:     /* STR  rd, [rn], +rm */                                   \
    case 0x6A:     /* STRT rd, [rn], +rm */                                   \
      ce.arm_memst<u32, OffOp2Reg, OffPositive, MemIdxPostWB>(inst);          \
      break;                                                                  \
    case 0x6C:     /* STRB  rd, [rn], +rm */                                  \
    case 0x6E:     /* STRBT rd, [rn], +rm */                                  \
      ce.arm_memst<u8, OffOp2Reg, OffPositive, MemIdxPostWB>(inst);           \
      break;                                                                  \
                                                                              \
    case 0x69:     /* LDR  rd, [rn], +rm */                                   \
    case 0x6B:     /* LDRT rd, [rn], +rm */                                   \
      ce.arm_memld<u32, OffOp2Reg, OffPositive, MemIdxPostWB>(inst);          \
      break;                                                                  \
    case 0x6D:     /* LDRB  rd, [rn], +rm */                                  \
    case 0x6F:     /* LDRBT rd, [rn], +rm */                                  \
      ce.arm_memld<u8, OffOp2Reg, OffPositive, MemIdxPostWB>(inst);           \
      break;                                                                  \
                                                                              \
    /* Memops with regop as pre-increment/decrement (optional writeback) */   \
    case 0x70:     /* STR rd, [rn - rm] */                                    \
      ce.arm_memst<u32, OffOp2Reg, OffNegative, MemIdxPre>(inst);             \
      break;                                                                  \
    case 0x72:     /* STR rd, [rn - rm]! */                                   \
      ce.arm_memst<u32, OffOp2Reg, OffNegative, MemIdxPreWB>(inst);           \
      break;                                                                  \
                                                                              \
    case 0x71:                                                                \
      /* LDR rd, [rn - rm] */                                                 \
      ce.arm_memld<u32, OffOp2Reg, OffNegative, MemIdxPre>(inst);             \
      break;                                                                  \
    case 0x73:                                                                \
      /* LDR rd, [rn - rm]! */                                                \
      ce.arm_memld<u32, OffOp2Reg, OffNegative, MemIdxPreWB>(inst);           \
      break;                                                                  \
                                                                              \
    case 0x74:     /* STRB rd, [rn - rm] */                                   \
      ce.arm_memst<u8, OffOp2Reg, OffNegative, MemIdxPre>(inst);              \
      break;                                                                  \
    case 0x76:     /* STRB rd, [rn - rm]! */                                  \
      ce.arm_memst<u8, OffOp2Reg, OffNegative, MemIdxPreWB>(inst);            \
      break;                                                                  \
                                                                              \
    case 0x75:                                                                \
      /* LDRB rd, [rn - rm] */                                                \
      ce.arm_memld<u8, OffOp2Reg, OffNegative, MemIdxPre>(inst);              \
      break;                                                                  \
    case 0x77:                                                                \
      /* LDRB rd, [rn - rm]! */                                               \
      ce.arm_memld<u8, OffOp2Reg, OffNegative, MemIdxPreWB>(inst);            \
      break;                                                                  \
                                                                              \
    case 0x78:     /* STR rd, [rn + rm] */                                    \
      ce.arm_memst<u32, OffOp2Reg, OffPositive, MemIdxPre>(inst);             \
      break;                                                                  \
    case 0x7A:     /* STR rd, [rn + rm]! */                                   \
      ce.arm_memst<u32, OffOp2Reg, OffPositive, MemIdxPreWB>(inst);           \
      break;                                                                  \
                                                                              \
    case 0x79:                                                                \
      /* LDR rd, [rn + rm] */                                                 \
      ce.arm_memld<u32, OffOp2Reg, OffPositive, MemIdxPre>(inst);             \
      break;                                                                  \
    case 0x7B:                                                                \
      /* LDR rd, [rn + rm]! */                                                \
      ce.arm_memld<u32, OffOp2Reg, OffPositive, MemIdxPreWB>(inst);           \
      break;                                                                  \
                                                                              \
    case 0x7C:     /* STRB rd, [rn + rm] */                                   \
      ce.arm_memst<u8, OffOp2Reg, OffPositive, MemIdxPre>(inst);              \
      break;                                                                  \
    case 0x7E:     /* STRB rd, [rn + rm]! */                                  \
      ce.arm_memst<u8, OffOp2Reg, OffPositive, MemIdxPreWB>(inst);            \
      break;                                                                  \
                                                                              \
    case 0x7D:                                                                \
      /* LDRB rd, [rn + rm] */                                                \
      ce.arm_memld<u8, OffOp2Reg, OffPositive, MemIdxPre>(inst);              \
      break;                                                                  \
    case 0x7F:                                                                \
      /* LDRBT rd, [rn + rm]! */                                              \
      ce.arm_memld<u8, OffOp2Reg, OffPositive, MemIdxPreWB>(inst);            \
      break;                                                                  \
                                                                              \
    /* Muliple memops */                                                      \
    case 0x80:     /* STMDA rn, rlist */                                      \
      ce.mem_multi<ModeARM, AccStore, AddrPostDec, false, false>(             \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x82:     /* STMDA rn!, rlist */                                     \
      ce.mem_multi<ModeARM, AccStore, AddrPostDec, true, false>(              \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x84:     /* STMDA rn, rlist^ */                                     \
      ce.mem_multi<ModeARM, AccStore, AddrPostDec, false, true>(              \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x86:     /* STMDA rn!, rlist^ */                                    \
      ce.mem_multi<ModeARM, AccStore, AddrPostDec, true, true>(               \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
                                                                              \
    case 0x81:     /* LDMDA rn, rlist */                                      \
      ce.mem_multi<ModeARM, AccLoad, AddrPostDec, false, false>(              \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x83:     /* LDMDA rn!, rlist */                                     \
      ce.mem_multi<ModeARM, AccLoad, AddrPostDec, true, false>(               \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x85:     /* LDMDA rn, rlist^ */                                     \
      ce.mem_multi<ModeARM, AccLoad, AddrPostDec, false, true>(               \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x87:     /* LDMDA rn!, rlist^ */                                    \
      ce.mem_multi<ModeARM, AccLoad, AddrPostDec, true, true>(                \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
                                                                              \
    case 0x88:     /* STMIA rn, rlist */                                      \
      ce.mem_multi<ModeARM, AccStore, AddrPostInc, false, false>(             \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x8A:     /* STMIA rn!, rlist */                                     \
      ce.mem_multi<ModeARM, AccStore, AddrPostInc, true, false>(              \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x8C:     /* STMIA rn, rlist^ */                                     \
      ce.mem_multi<ModeARM, AccStore, AddrPostInc, false, true>(              \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x8E:     /* STMIA rn!, rlist^ */                                    \
      ce.mem_multi<ModeARM, AccStore, AddrPostInc, true, true>(               \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
                                                                              \
    case 0x89:     /* LDMIA rn, rlist */                                      \
      ce.mem_multi<ModeARM, AccLoad, AddrPostInc, false, false>(              \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x8B:     /* LDMIA rn!, rlist */                                     \
      ce.mem_multi<ModeARM, AccLoad, AddrPostInc, true, false>(               \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x8D:     /* LDMIA rn, rlist^ */                                     \
      ce.mem_multi<ModeARM, AccLoad, AddrPostInc, false, true>(               \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x8F:     /* LDMIA rn!, rlist^ */                                    \
      ce.mem_multi<ModeARM, AccLoad, AddrPostInc, true, true>(                \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
                                                                              \
    case 0x90:     /* STMDB rn, rlist */                                      \
      ce.mem_multi<ModeARM, AccStore, AddrPreDec, false, false>(              \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x92:     /* STMDB rn!, rlist */                                     \
      ce.mem_multi<ModeARM, AccStore, AddrPreDec, true, false>(               \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x94:     /* STMDB rn, rlist^ */                                     \
      ce.mem_multi<ModeARM, AccStore, AddrPreDec, false, true>(               \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x96:     /* STMDB rn!, rlist^ */                                    \
      ce.mem_multi<ModeARM, AccStore, AddrPreDec, true, true>(                \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
                                                                              \
    case 0x91:     /* LDMDB rn, rlist */                                      \
      ce.mem_multi<ModeARM, AccLoad, AddrPreDec, false, false>(               \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x93:     /* LDMDB rn!, rlist */                                     \
      ce.mem_multi<ModeARM, AccLoad, AddrPreDec, true, false>(                \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x95:     /* LDMDB rn, rlist^ */                                     \
      ce.mem_multi<ModeARM, AccLoad, AddrPreDec, false, true>(                \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x97:     /* LDMDB rn!, rlist^ */                                    \
      ce.mem_multi<ModeARM, AccLoad, AddrPreDec, true, true>(                 \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
                                                                              \
    case 0x98:     /* STMIB rn, rlist */                                      \
      ce.mem_multi<ModeARM, AccStore, AddrPreInc, false, false>(              \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x9A:     /* STMIB rn!, rlist */                                     \
      ce.mem_multi<ModeARM, AccStore, AddrPreInc, true, false>(               \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x9C:     /* STMIB rn, rlist^ */                                     \
      ce.mem_multi<ModeARM, AccStore, AddrPreInc, false, true>(               \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x9E:     /* STMIB rn!, rlist^ */                                    \
      ce.mem_multi<ModeARM, AccStore, AddrPreInc, true, true>(                \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
                                                                              \
    case 0x99:     /* LDMIB rn, rlist */                                      \
      ce.mem_multi<ModeARM, AccLoad, AddrPreInc, false, false>(               \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x9B:     /* LDMIB rn!, rlist */                                     \
      ce.mem_multi<ModeARM, AccLoad, AddrPreInc, true, false>(                \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x9D:     /* LDMIB rn, rlist^ */                                     \
      ce.mem_multi<ModeARM, AccLoad, AddrPreInc, false, true>(                \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
    case 0x9F:     /* LDMIB rn!, rlist^ */                                    \
      ce.mem_multi<ModeARM, AccLoad, AddrPreInc, true, true>(                 \
        inst.pc, condition, inst.rn(), inst.rlist());                         \
      break;                                                                  \
                                                                              \
    case 0xA0 ... 0xAF:      /* B label */                                    \
      iblk_exits[block_exit_position].branch_source =                         \
        ce.arm_b(inst, iblk_exits[block_exit_position].branch_target);        \
      block_exit_position++;                                                  \
      break;                                                                  \
                                                                              \
    case 0xB0 ... 0xBF:      /* BL label */                                   \
      iblk_exits[block_exit_position].branch_source =                         \
        ce.arm_bl(inst, iblk_exits[block_exit_position].branch_target);       \
      block_exit_position++;                                                  \
      break;                                                                  \
                                                                              \
    case 0xF0 ... 0xFF:      /* SWI number */                                 \
      if (ce.can_emu_swi(inst.pc, inst.swinum()))                             \
        ce.emu_swi<ModeARM, ARMInst>(inst);                                   \
      else                                                                    \
        iblk_exits[block_exit_position++].branch_source = ce.arm_swi(inst.pc);\
      break;                                                                  \
  }                                                                           \
                                                                              \
  pc += 4                                                                     \

// RAM regions use a tagging mechanism (used to detect Self-Modifying code) and
// it is reused to tag where the code for a given PC lives.
// ROM regions use a hash table. The entries are either zero (not found) or an
// offset into the ROM cache. A linked list of hashhdr_type elements contains
// a key (PC) and offset to next entry. The actual value is implicit and is
// placed immediately after the hashhdr_type object.

template <CPUInstMode cm, TranslRegion reg>
uint8_t *lookup_block(uint32_t pc) {
  if (reg == RegionRAM) {
    uint16_t tagp = (pc < 0x03000000) ? *(uint16_t *)(ewram + (pc & 0x3FFFF) + 0x40000)
                                      : *(uint16_t *)(iwram + (pc & 0x7FFF));
    if (VALID_TAG(tagp)) {
      ramtag_type* trentry = get_ram_tag(tagp);
      uint32_t offset = (cm == ModeThumb) ? trentry->offset_thumb : trentry->offset_arm;
      if (offset)
        return &ram_translation_cache[offset];
    }
  } else {
    uint32_t key = pc | (cm == ModeThumb ? 1 : 0);
    uint32_t hash_target = ((key * 2654435761U) >> (32 - ROM_BRANCH_HASH_BITS)) & (ROM_BRANCH_HASH_SIZE - 1);

    for (uint32_t blk_off = rom_branch_hash[hash_target]; blk_off; ) {
      hashhdr_type *bhdr = (hashhdr_type*)&rom_translation_cache[blk_off];
      if (bhdr->pc_value == key)
        return &rom_translation_cache[blk_off + sizeof(hashhdr_type) + CodeEmitter::block_header_size()];
      blk_off = bhdr->next_entry;
    }
  }

  return NULL; // Not found
}

// Inserts an entry for "PC" to the current JIT pointer.
template <CPUInstMode cm, TranslRegion reg>
void insert_block_entry(uint32_t pc) {
  if (reg == RegionRAM) {
    uint16_t *tagp = (pc < 0x03000000) ? (uint16_t *)(ewram + (pc & 0x3FFFF) + 0x40000)
                                       : (uint16_t *)(iwram + (pc & 0x7FFF));

    ramtag_type* trentry = get_ram_tag(ram_block_tag);
    tagp[0] = ram_block_tag;
    if (cm == ModeARM && !tagp[1])
      tagp[1] = CODE_TAG_BLOCK16;
    ram_block_tag -= 2;

    uint32_t off = ram_translation_ptr + CodeEmitter::block_header_size() - ram_translation_cache;
    if (cm == ModeARM) {
      trentry->offset_thumb = 0;
      trentry->offset_arm = off;
    } else {
      trentry->offset_arm = 0;
      trentry->offset_thumb = off;
    }
  } else {
    uint32_t key = pc | (cm == ModeThumb ? 1 : 0);
    uint32_t hash_target = ((key * 2654435761U) >> (32 - ROM_BRANCH_HASH_BITS)) & (ROM_BRANCH_HASH_SIZE - 1);

    uint32_t *offptr = &rom_branch_hash[hash_target];
    while (*offptr) {
      hashhdr_type *bhdr = (hashhdr_type*)&rom_translation_cache[*offptr];
      offptr = &bhdr->next_entry;
    }

    // Allocate a header entry in the ROM area, fill it and link it.
    hashhdr_type *newhdr = (hashhdr_type*)rom_translation_ptr;
    newhdr->pc_value = key;
    newhdr->next_entry = 0;
    *offptr = (rom_translation_ptr - rom_translation_cache);
    rom_translation_ptr += sizeof(hashhdr_type);
  }
}


#define INFO_DIRECT_BRANCH             0x01
#define INFO_INDIRECT_BRANCH           0x02
#define INFO_UNCOND_BRANCH             0x40
#define INFO_SYNC_CYCLES               0x80

class ThumbInstInfo : public ThumbInst {
public:
  ThumbInstInfo(u32 pc, u16 opcode)
   : ThumbInst(pc, opcode, 0), cyccnt(0), info(0) {}

  u8 cyccnt;                   // Number of cycles on top of the base cycles.
  u8 info;                     // Info on the instruction (ie. it's a branch, XXX)
  u32 branch_tgt;              // Branch target (whenever the instruction is a direct jump)
  u8 *branch_ptr;              // Branch patching pointer. (TODO: could we get rid of this perhaps?)
  u8 *eptr;                    // Points to the JIT address where this was emitted.
  union {                      // Emitter functions.
    void (CodeEmitter::*inst_fn)(const ThumbInst &);
    u8 * (CodeEmitter::*branch_fn)(u32, u32);
  } emitter;
};

template <TranslRegion reg>
ThumbInstInfo decode_thumb_instruction(u32 pc, const ThumbInstDec & inst, u16 last_opcode);

// Starts decoding an instruction block and returns the number of parsed instructions.
template <TranslRegion reg>
u8* translate_single_block_thumb(JITArea<reg> *jitarea, uint32_t entrypc, staticarray<block_exit_type, MAX_LINKQ_SIZE> & linkq) {
  // TODO: Fix this somehow :D Ideally emit some code that prints some controlled message and faults.
  if ((entrypc >> 24) >= 16)
    return NULL;

  // Holds decoded instructions
  staticarray<ThumbInstInfo, MAX_BLOCK_SIZE> insts;

  // Holds the branch targets, sorted, so we can better find the block end.
  minheap<u32, MAX_EXITS> brtgt;

  u16 last_opcode = 0;
  uint32_t currpc = entrypc;

  do {
    u8 *pc_address_block = memory_map_read[currpc >> 15];
    u16 opcode = address16(pc_address_block, (currpc & 0x7FFF));
    insts.append(decode_thumb_instruction<reg>(currpc, ThumbInstDec(opcode), last_opcode));

    if (reg == RegionRAM) {
      intptr_t offset = (currpc < 0x03000000) ? 0x40000 : -0x8000;
      if (address16(pc_address_block, (currpc & 0x7FFF) + offset) == 0)
        address16(pc_address_block, (currpc & 0x7FFF) + offset) = CODE_TAG_BLOCK16;

      if (currpc >= 0x3000000) {
        iwram_code_min = MIN(currpc & 0x7FFF, iwram_code_min);
        iwram_code_max = MAX(currpc & 0x7FFF, iwram_code_max);
      } else {
        ewram_code_min = MIN(currpc & 0x3FFFF, ewram_code_min);
        ewram_code_max = MAX(currpc & 0x3FFFF, ewram_code_max);
      }
    }

    // Handle direct branches
    if (insts.back().info & INFO_DIRECT_BRANCH) {
      const uint32_t tpc = insts.back().branch_tgt;
      if (tpc >= entrypc) {
        if (tpc <= currpc)
          insts[(tpc - entrypc) / 2].info |= INFO_SYNC_CYCLES;   // Annotate backwards branches
        else
          brtgt.insert(tpc);   // Save forward branches for later then.
      }
    }

    // Process any previous forward branches. The queue can only contain
    // branches in the [pc, inf) region, since we never push backwards branches.
    while (!brtgt.empty() && brtgt.peek() == currpc) {
      insts.back().info |= INFO_SYNC_CYCLES;
      brtgt.pop();
    }

    if (brtgt.full())   // Truncate block if we can't take any more branches.
      break;

    // TODO: Get rid of translation gates.
    for (unsigned i = 0; i < translation_gate_targets; i++)
      if (currpc == translation_gate_target_pc[i])
        break;

    if (insts.back().info & INFO_UNCOND_BRANCH) {
      // Terminate blocks at indirect branches unless there's a branch immediately after.
      // We only need to peek at the queue, since it can only contain pcs in the [pc+2, inf) range.
      // TODO: There could be pool data between the branch and the next branch target.
      if (brtgt.empty() || brtgt.peek() != currpc + 2)
        break;
    }

    currpc += 2;
    last_opcode = opcode;
  } while (!insts.full());

  // Pass: flag elimination.
  optimize_flag_elimination<staticarray<ThumbInstInfo, MAX_BLOCK_SIZE>>(insts);

  uint8_t needed_flags = 0xF;
  for (int i = insts.size() - 1; i >= 0; i--) {
    unsigned imsk = insts[i].flag_status;
    insts[i].flag_status = imsk & needed_flags;
    needed_flags &= ~((imsk >> 4) & 0xF);        // Flags generated by the inst.
    needed_flags |= (imsk >> 8);                 // Needed flags for this inst.
  }

  // Pass: emit JIT code
  CodeEmitter ce(jitarea->cur_ptr(), entrypc);
  ce.emit_block_header();

  u8 *entryptr = ce.emit_ptr;
  ce.emit_block_prologue();

  for (unsigned i = 0; i < insts.size(); i++) {
    if (insts[i].info & INFO_SYNC_CYCLES)
      ce.emit_cycle_update();

    ce.cyc_cnt += def_seq_cycles[insts[i].pc >> 24][0];  // TODO: Can this be improved?
    ce.cyc_cnt += insts[i].cyccnt;

    insts[i].eptr = ce.emit_ptr;       // Annotate the start of the instruction

    // Emit instruction hooks: cheats, tracing, etc.
    ce.trace_instruction<ModeThumb>(insts[i].pc, insts[i].opcode);
    if (insts[i].pc == cheat_master_hook)
      ce.emit_cheat_hook<ModeThumb>();

    if (insts[i].info & INFO_DIRECT_BRANCH)
      insts[i].branch_ptr = (ce.*insts[i].emitter.branch_fn)(insts[i].pc, insts[i].branch_tgt);
    else
      (ce.*insts[i].emitter.inst_fn)(insts[i]);
  }

  // Emits an indirect branch just in case the block was cut off prematurely.
  ce.generate_translation_gate<ModeThumb>(insts.back().pc + 2);

  // Pass: link local branches/calls
  for (unsigned i = 0; i < insts.size(); i++) {
    if (insts[i].info & INFO_DIRECT_BRANCH) {
      if (insts[i].branch_tgt - entrypc < insts.size()*2) {     // Abuses int overflow
        uint32_t ioff = (insts[i].branch_tgt - entrypc) / 2;
        generate_branch_patch_unconditional(insts[i].branch_ptr, insts[ioff].eptr);
      } else {
        // Out of range branch, this is an external branch.
        linkq.append(block_exit_type{
          .branch_target = insts[i].branch_tgt,
          .branch_source = insts[i].branch_ptr
        });
      }
    }
  }

  jitarea->update_ptr(ce.emit_ptr);

  return entryptr;
}

// Idea: make it a heap so that duplicated targets are the same.

template <CPUInstMode cm, TranslRegion reg>
u8* translate_block(u32 pc) {
  JITArea<reg> jitarea;
  // TODO: figure out whether a sorted list or heap could be better?
  staticarray<block_exit_type, MAX_LINKQ_SIZE> linkq;

  // Translate the current requested block.
  insert_block_entry<cm, reg>(pc);
  u8 *ret = translate_single_block_thumb<reg>(&jitarea, pc, linkq);
  if (jitarea.overflow()) {
    jitarea.flush_cache();
    return NULL;
  }

  // Now go ahead and process any external block linking.
  while (!linkq.empty()) {
    block_exit_type elem = linkq.pop_back();

    // TODO: Make jumps between modes something "normal"?
    u8 *blkptr = elem.branch_target == 0x8 ? bios_swi_entrypoint : lookup_block<cm, reg>(elem.branch_target);
    if (!blkptr) {
      insert_block_entry<cm, reg>(elem.branch_target);
      blkptr = translate_single_block_thumb<reg>(&jitarea, elem.branch_target, linkq);  // Force translation
    }

    generate_branch_patch_unconditional(elem.branch_source, blkptr);

    if (jitarea.overflow()) {
      jitarea.flush_cache();
      return NULL;
    }
  }

  return ret;
}

#define FLAG_WRITE_NZCV         0xFF
#define FLAG_WRITE_NZ           0xCC
#define FLAG_WRITE_NZC          0xEE
#define FLAG_WRITE_C            0x22
#define FLAG_WRITE_NZ_MAYBE_C   0xCE

#define FLAG_READ_NZCV         0xF00
#define FLAG_READ_C            0x200

template <TranslRegion reg>
ThumbInstInfo decode_thumb_instruction(u32 pc, const ThumbInstDec & inst, u16 last_opcode) {
  ThumbInstInfo ret(pc, inst.opcode);
  ret.emitter.inst_fn = &CodeEmitter::thumb_invalid;

  switch (inst.opcode >> 8) {
    case 0x00 ... 0x07:      /* LSL rd, rs, imm */
      ret.flag_status = inst.imm5() ? FLAG_WRITE_NZC : FLAG_WRITE_NZ;
      ret.emitter.inst_fn = &CodeEmitter::thumb_shft<OpImm, ShiftLSL>;
      break;
    case 0x08 ... 0x0F:      /* LSR rd, rs, imm */
      ret.flag_status = FLAG_WRITE_NZC;
      ret.emitter.inst_fn = &CodeEmitter::thumb_shft<OpImm, ShiftLSR>;
      break;
    case 0x10 ... 0x17:      /* ASR rd, rs, imm */
      ret.flag_status = FLAG_WRITE_NZC;
      ret.emitter.inst_fn = &CodeEmitter::thumb_shft<OpImm, ShiftASR>;
      break;

    case 0x18 ... 0x19:      /* ADD rd, rs, rn */
      ret.flag_status = FLAG_WRITE_NZCV;
      ret.emitter.inst_fn = &CodeEmitter::thumb_aluop3<OpAdd>;
      break;
    case 0x1A ... 0x1B:      /* SUB rd, rs, rn */
      ret.flag_status = FLAG_WRITE_NZCV;
      ret.emitter.inst_fn = &CodeEmitter::thumb_aluop3<OpSub>;
      break;
    case 0x1C ... 0x1D:      /* ADD rd, rs, imm */
      ret.flag_status = FLAG_WRITE_NZCV;
      ret.emitter.inst_fn = &CodeEmitter::thumb_aluimm3<OpAdd>;
      break;
    case 0x1E ... 0x1F:      /* SUB rd, rs, imm */
      ret.flag_status = FLAG_WRITE_NZCV;
      ret.emitter.inst_fn = &CodeEmitter::thumb_aluimm3<OpSub>;
      break;

    case 0x20 ... 0x27:      /* MOV r0..7, imm8 */
      ret.flag_status = FLAG_WRITE_NZ;
      ret.emitter.inst_fn = &CodeEmitter::thumb_aluimm2<OpMov>;
      break;
    case 0x28 ... 0x2F:      /* CMP r0..7, imm8 */
      ret.flag_status = FLAG_WRITE_NZCV;
      ret.emitter.inst_fn = &CodeEmitter::thumb_aluimm2<OpCmp>;
      break;
    case 0x30 ... 0x37:      /* ADD r0..7, imm8 */
      ret.flag_status = FLAG_WRITE_NZCV;
      ret.emitter.inst_fn = &CodeEmitter::thumb_aluimm2<OpAdd>;
      break;
    case 0x38 ... 0x3F:      /* SUB r0..7, imm8 */
      ret.flag_status = FLAG_WRITE_NZCV;
      ret.emitter.inst_fn = &CodeEmitter::thumb_aluimm2<OpSub>;
      break;

    case 0x40 ... 0x43:
       /* Arith/Logic reg-reg instructions */
      switch ((inst.opcode >> 6) & 0xF) {
        case 0x00:           /* AND rd, rs */
          ret.flag_status = FLAG_WRITE_NZ;
          ret.emitter.inst_fn = &CodeEmitter::thumb_aluop2<OpAnd>;
          break;
        case 0x01:           /* EOR rd, rs */
          ret.flag_status = FLAG_WRITE_NZ;
          ret.emitter.inst_fn = &CodeEmitter::thumb_aluop2<OpXor>;
          break;

        case 0x02:           /* LSL rd, rs */
          ret.flag_status = FLAG_WRITE_NZ_MAYBE_C;
          ret.emitter.inst_fn = &CodeEmitter::thumb_shft<OpReg, ShiftLSL>;
          break;
        case 0x03:           /* LSR rd, rs */
          ret.flag_status = FLAG_WRITE_NZ_MAYBE_C;
          ret.emitter.inst_fn = &CodeEmitter::thumb_shft<OpReg, ShiftLSR>;
          break;
        case 0x04:           /* ASR rd, rs */
          ret.flag_status = FLAG_WRITE_NZ_MAYBE_C;
          ret.emitter.inst_fn = &CodeEmitter::thumb_shft<OpReg, ShiftASR>;
          break;
        case 0x07:           /* ROR rd, rs */
          ret.flag_status = FLAG_WRITE_NZ_MAYBE_C;
          ret.emitter.inst_fn = &CodeEmitter::thumb_shft<OpReg, ShiftROR>;
          break;

        case 0x05:           /* ADC rd, rs */
          ret.flag_status = FLAG_WRITE_NZCV | FLAG_READ_C;
          ret.emitter.inst_fn = &CodeEmitter::thumb_aluop2<OpAdc>;
          break;
        case 0x06:           /* SBC rd, rs */
          ret.flag_status = FLAG_WRITE_NZCV | FLAG_READ_C;
          ret.emitter.inst_fn = &CodeEmitter::thumb_aluop2<OpSbc>;
          break;

        case 0x08:           /* TST rd, rs */
          ret.flag_status = FLAG_WRITE_NZCV;
          ret.emitter.inst_fn = &CodeEmitter::thumb_testop<OpTst>;
          break;
        case 0x09:           /* NEG rd, rs */
          ret.flag_status = FLAG_WRITE_NZCV;
          ret.emitter.inst_fn = &CodeEmitter::thumb_aluop1<OpNeg>;
          break;
        case 0x0A:           /* CMP rd, rs */
          ret.flag_status = FLAG_WRITE_NZCV;
          ret.emitter.inst_fn = &CodeEmitter::thumb_testop<OpCmp>;
          break;
        case 0x0B:           /* CMN rd, rs */
          ret.flag_status = FLAG_WRITE_NZCV;
          ret.emitter.inst_fn = &CodeEmitter::thumb_testop<OpCmn>;
          break;

        case 0x0C:           /* ORR rd, rs */
          ret.flag_status = FLAG_WRITE_NZ;
          ret.emitter.inst_fn = &CodeEmitter::thumb_aluop2<OpOrr>;
          break;
        case 0x0D:           /* MUL rd, rs */
          ret.flag_status = FLAG_WRITE_NZ;
          ret.emitter.inst_fn = &CodeEmitter::thumb_aluop2<OpMul>;
          ret.cyccnt = 2;    /* Between 1 and 4 extra cycles */
          break;
        case 0x0E:           /* BIC rd, rs */
          ret.flag_status = FLAG_WRITE_NZ;
          ret.emitter.inst_fn = &CodeEmitter::thumb_aluop2<OpBic>;
          break;
        case 0x0F:           /* MVN rd, rs */
          ret.flag_status = FLAG_WRITE_NZ;
          ret.emitter.inst_fn = &CodeEmitter::thumb_aluop1<OpMvn>;
          break;
      }
      break;

    case 0x44:     /* ADD rd, rs */
      ret.emitter.inst_fn = &CodeEmitter::thumb_aluhi<OpAdd>;
      break;
    case 0x45:     /* CMP rd, rs */
      ret.flag_status = FLAG_WRITE_NZCV;
      ret.emitter.inst_fn = &CodeEmitter::thumb_aluhi<OpCmp>;
      break;
    case 0x46:     /* MOV rd, rs */
      if (inst.rd_hi() == REG_PC) {
        ret.flag_status = FLAG_READ_NZCV;
        ret.info = INFO_INDIRECT_BRANCH | INFO_UNCOND_BRANCH;
      }
      ret.emitter.inst_fn = &CodeEmitter::thumb_aluhi<OpMov>;
      break;

    case 0x47:     /* BX rs */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_INDIRECT_BRANCH | INFO_UNCOND_BRANCH;
      ret.emitter.inst_fn = &CodeEmitter::thumb_bx;
      break;

    case 0x48 ... 0x4F:      /* LDR r0..7, [pc + imm] */
      if (reg == RegionRAM)
        ret.emitter.inst_fn = &CodeEmitter::thumb_loadpool<true>;
      else
        ret.emitter.inst_fn = &CodeEmitter::thumb_loadpool<false>;
      break;

    case 0x50 ... 0x51:      /* STR rd, [rb + ro] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccStore, u32, OffReg>;
      break;
    case 0x52 ... 0x53:      /* STRH rd, [rb + ro] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccStore, u16, OffReg>;
      break;
    case 0x54 ... 0x55:      /* STRB rd, [rb + ro] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccStore, u8, OffReg>;
      break;

    case 0x56 ... 0x57:      /* LDSB rd, [rb + ro] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccLoad, s8, OffReg>;
      break;
    case 0x58 ... 0x59:      /* LDR rd, [rb + ro] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccLoad, u32, OffReg>;
      break;
    case 0x5A ... 0x5B:      /* LDRH rd, [rb + ro] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccLoad, u16, OffReg>;
      break;
    case 0x5C ... 0x5D:      /* LDRB rd, [rb + ro] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccLoad, u8, OffReg>;
      break;
    case 0x5E ... 0x5F:      /* LDSH rd, [rb + ro] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccLoad, s16, OffReg>;
      break;

    case 0x60 ... 0x67:      /* STR rd, [rb + imm] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccStore, u32, OffImm5>;
      break;
    case 0x68 ... 0x6F:      /* LDR rd, [rb + imm] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccLoad, u32, OffImm5>;
      break;
    case 0x70 ... 0x77:      /* STRB rd, [rb + imm] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccStore, u8, OffImm5>;
      break;
    case 0x78 ... 0x7F:      /* LDRB rd, [rb + imm] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccLoad, u8, OffImm5>;
      break;
    case 0x80 ... 0x87:      /* STRH rd, [rb + imm] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccStore, u16, OffImm5>;
      break;
    case 0x88 ... 0x8F:      /* LDRH rd, [rb + imm] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccLoad, u16, OffImm5>;
      break;

    case 0x90 ... 0x97:      /* STR r0..7, [sp + imm] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccStore, u32, OffSP>;
      break;
    case 0x98 ... 0x9F:      /* LDR r0..7, [sp + imm] */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memacc<AccLoad, u32, OffSP>;
      break;

    case 0xA0 ... 0xA7:      /* ADD r0..7, pc, +imm */
      ret.emitter.inst_fn = &CodeEmitter::thumb_regoff<REG_PC>;
      break;
    case 0xA8 ... 0xAF:      /* ADD r0..7, sp, +imm */
      ret.emitter.inst_fn = &CodeEmitter::thumb_regoff<REG_SP>;
      break;
    case 0xB0 ... 0xB3:      /* ADD sp, sp, +/-imm */
      ret.emitter.inst_fn = &CodeEmitter::thumb_spadj;
      break;

    case 0xB4:               /* PUSH rlist */
      ret.emitter.inst_fn = &CodeEmitter::thumb_pushpop<AccStore, AddrPreDec>;
      break;
    case 0xB5:               /* PUSH rlist, lr */
      ret.emitter.inst_fn = &CodeEmitter::thumb_pushpop<AccStore, AddrPreDec, 1 << REG_LR>;
      break;
    case 0xBC:               /* POP rlist */
      ret.emitter.inst_fn = &CodeEmitter::thumb_pushpop<AccLoad, AddrPostInc>;
      break;
    case 0xBD:               /* POP rlist, pc */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_INDIRECT_BRANCH | INFO_UNCOND_BRANCH;
      ret.emitter.inst_fn = &CodeEmitter::thumb_pushpop<AccLoad, AddrPostInc, 1 << REG_PC>;
      break;
    case 0xC0 ... 0xC7:      /* STMIA r0-7!, rlist */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memmulti<AccStore, AddrPostInc>;
      break;
    case 0xC8 ... 0xCF:      /* LDMIA r0-7!, rlist */
      ret.emitter.inst_fn = &CodeEmitter::thumb_memmulti<AccLoad, AddrPostInc>;
      break;

    case 0xD0:     /* BEQ label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondEQ>;
      break;
    case 0xD1:     /* BNE label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondNE>;
      break;
    case 0xD2:     /* BCS label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondCS>;
      break;
    case 0xD3:     /* BCC label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondCC>;
      break;
    case 0xD4:     /* BMI label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondMI>;
      break;
    case 0xD5:     /* BPL label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondPL>;
      break;
    case 0xD6:     /* BVS label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondVS>;
      break;
    case 0xD7:     /* BVC label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondVC>;
      break;
    case 0xD8:     /* BHI label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondHI>;
      break;
    case 0xD9:     /* BLS label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondLS>;
      break;
    case 0xDA:     /* BGE label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondGE>;
      break;
    case 0xDB:     /* BLT label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondLT>;
      break;
    case 0xDC:     /* BGT label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondGT>;
      break;
    case 0xDD:     /* BLE label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH;
      ret.branch_tgt = pc + inst.cbr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_brcond<CondLE>;
      break;

    case 0xDF:
      ret.flag_status = FLAG_READ_NZCV;
      if (CodeEmitter::can_emu_swi(pc, inst.swinum()))
        ret.emitter.inst_fn = &CodeEmitter::emu_swi<ModeThumb, ThumbInst>;
      else {
        ret.info = INFO_DIRECT_BRANCH | INFO_UNCOND_BRANCH;
        ret.branch_tgt = 0x00000008;
        ret.emitter.branch_fn = &CodeEmitter::thumb_swi;
      }
      break;

    case 0xE0 ... 0xE7:      /* B label */
      ret.flag_status = FLAG_READ_NZCV;
      ret.info = INFO_DIRECT_BRANCH | INFO_UNCOND_BRANCH;
      ret.branch_tgt = pc + inst.abr_offset() + 4;
      ret.emitter.branch_fn = &CodeEmitter::thumb_b;
      break;

    case 0xF0 ... 0xF7:      /* (low word) BL label */
      /* This should possibly generate code if not in conjunction with a BLH
         next, but I don't think anyone will do that. */
      break;

    case 0xF8 ... 0xFF:      /* (high word) BL label */

      // If there is no BL low word then treat it like an indirect branch.
      // This does happen in Golden Sun 2.
      ret.flag_status = FLAG_READ_NZCV;
      if ((last_opcode >= 0xF000) && (last_opcode < 0xF800)) {
        ret.info = INFO_DIRECT_BRANCH | INFO_UNCOND_BRANCH;
        ret.emitter.branch_fn = &CodeEmitter::thumb_bl;
        ret.branch_tgt = pc + 2 + inst.abr_offset_lo() + ThumbInstDec(last_opcode).abr_offset_hi();
      } else {
        ret.info = INFO_INDIRECT_BRANCH | INFO_UNCOND_BRANCH;
        ret.emitter.inst_fn = &CodeEmitter::thumb_blh;
      }
      break;
  }

  return ret;
}


#define arm_flag_status()


// This function will return a pointer to a translated block of code. If it
// doesn't exist it will translate it, if it does it will pass it back.

// type should be "arm", "thumb", or "dual." For arm or thumb the PC should
// be a real PC, for dual the least significant bit will determine if it's
// ARM or Thumb mode.

#define block_lookup_address_pc_arm()                                         \
  u32 thumb = 0;                                                              \
  pc &= ~0x03

#define block_lookup_translate_builder(type)                                  \
u8 function_cc *block_lookup_translate_##type(u32 pc)                         \
{                                                                             \
  u8 pcregion = (pc >> 24);                                                   \
  u16 *location;                                                              \
                                                                              \
  block_lookup_address_pc_##type();                                           \
                                                                              \
  switch(pcregion)                                                            \
  {                                                                           \
    case 0x2:                                                                 \
    case 0x3:                                                                 \
    {                                                                         \
      u16* tagp = (pcregion == 2) ? (u16 *)(ewram + (pc & 0x3FFFF) + 0x40000) \
                                  : (u16 *)(iwram + (pc & 0x7FFF));           \
      ramtag_type* trentry;                                                   \
      /* Allocate a tag if not a valid one, and initialize header */          \
      if (!VALID_TAG(*tagp)) {                                                \
        allocate_tag_##type(tagp);                                            \
        trentry = get_ram_tag(*tagp);                                         \
        trentry->offset_arm = 0;                                              \
        trentry->offset_thumb = 0;                                            \
      } else {                                                                \
        trentry = get_ram_tag(*tagp);                                         \
      }                                                                       \
                                                                              \
      if (!trentry->offset_##type) {                                          \
        bool result;                                                          \
        u8 *blkptr = ram_translation_ptr + CodeEmitter::block_header_size();  \
        trentry->offset_##type = blkptr - ram_translation_cache;              \
        result = translate_block_##type(pc, true);                            \
                                                                              \
        if (result)                                                           \
          return blkptr;                                                      \
      } else {                                                                \
        return &ram_translation_cache[trentry->offset_##type];                \
      }                                                                       \
      return NULL;                                                            \
    }                                                                         \
                                                                              \
    case 0x0:                                                                 \
    case 0x8 ... 0xD:                                                         \
    {                                                                         \
      u32 key = pc | thumb;                                                   \
      u32 hash_target = ((key * 2654435761U) >> (32 - ROM_BRANCH_HASH_BITS))  \
                                              & (ROM_BRANCH_HASH_SIZE - 1);   \
                                                                              \
      hashhdr_type *bhdr;                                                     \
      u32 blk_offset = rom_branch_hash[hash_target];                          \
      u32 *blk_offset_addr = &rom_branch_hash[hash_target];                   \
      while(blk_offset)                                                       \
      {                                                                       \
        bhdr = (hashhdr_type*)&rom_translation_cache[blk_offset];             \
        if(bhdr->pc_value == key)                                             \
          return &rom_translation_cache[                                      \
                  blk_offset + sizeof(hashhdr_type) +                         \
                  CodeEmitter::block_header_size()];                          \
                                                                              \
        blk_offset = bhdr->next_entry;                                        \
        blk_offset_addr = &bhdr->next_entry;                                  \
      }                                                                       \
                                                                              \
      { /* Not found, go ahead and translate, and backfill the hash table */  \
        u8 *blkptr;                                                           \
        bool result;                                                          \
        bhdr = (hashhdr_type*)rom_translation_ptr;                            \
        bhdr->pc_value = key;                                                 \
        bhdr->next_entry = 0;                                                 \
        *blk_offset_addr = (u32)(rom_translation_ptr - rom_translation_cache);\
        rom_translation_ptr += sizeof(hashhdr_type);                          \
        blkptr = rom_translation_ptr + CodeEmitter::block_header_size();      \
        result = translate_block_##type(pc, false);                           \
                                                                              \
        if (result)                                                           \
          return blkptr;                                                      \
      }                                                                       \
      return NULL;                                                            \
    }                                                                         \
  }                                                                           \
                                                                              \
  /* Do not return NULL since it could indeed happen that some branch         \
     points to some random place (perhaps due to being garbage). This can     \
     happen when especulatively compiling code in RAM. Perhaps the game       \
     patches these instructions later, which would trigger a flush */         \
  return (u8*)(~0);                                                           \
}                                                                             \

block_lookup_translate_builder(arm);

// Called when a mode change is performed (via CPSR write).
// Might result in a IRQ being raised.
u32 function_cc process_cpsr_write(u32 new_cpsr, u32 pc) {
  // Change CPU mode (perhaps, it could be the same)
  set_cpu_mode(cpu_modes[new_cpsr & 0xF]);
  // Check if an IRQ could be raised, return the new PC in that case
  if((io_registers[REG_IE] & io_registers[REG_IF]) &&
      io_registers[REG_IME] && ((new_cpsr & 0x80) == 0))
  {
    REG_MODE(MODE_IRQ)[6] = pc + 4;
    REG_SPSR(MODE_IRQ) = new_cpsr;
    reg[REG_CPSR] = (new_cpsr & 0xFFFFFF00) | 0xD2;
    set_cpu_mode(MODE_IRQ);
    return 0x00000018;
  }

  return 0;
}

u8 function_cc *block_lookup_address_dual(u32 pc)
{
  u32 thumb = pc & 0x01;
  if(thumb) {
    pc &= ~1;
    reg[REG_CPSR] |= 0x20;
    return block_lookup_address_thumb(pc);
  } else {
    pc = (pc + 2) & ~0x03;
    reg[REG_CPSR] &= ~0x20;
    return block_lookup_address_arm(pc);
  }
}

u8 function_cc *block_lookup_address_arm(u32 pc)
{
  unsigned i;
  for (i = 0; i < 4; i++) {
    u8 *ret = block_lookup_translate_arm(pc);
    if (ret) {
      translate_icache_sync();
      return ret;
    }
  }

  printf("bad jump %x (%x)\n", pc, reg[REG_PC]);
  fflush(stdout);
  return NULL;
}

u8 function_cc *block_lookup_address_thumb(u32 pc) {
  bool onram = pc_on_ram(pc);
  pc &= ~1U;

  u8 *ret = onram ? lookup_block<ModeThumb, RegionRAM>(pc)
                  : lookup_block<ModeThumb, RegionROM>(pc);
  if (ret)
    return ret;

  for (unsigned i = 0; i < 2; i++) {
    u8 *ret = onram ? translate_block<ModeThumb, RegionRAM>(pc)
                    : translate_block<ModeThumb, RegionROM>(pc);
    if (ret) {
      translate_icache_sync();
      return ret;
    }
  }
  printf("bad jump %x (%x)\n", pc, reg[REG_PC]);
  fflush(stdout);
  return NULL;
}


// Potential exit point: If the rd field is pc for instructions is 0x0F,
// the instruction is b/bl/bx, or the instruction is ldm with PC in the
// register list.
// All instructions with upper 3 bits less than 100b have an rd field
// except bx, where the bits must be 0xF there anyway, multiplies,
// which cannot have 0xF in the corresponding fields, and msr, which
// has 0x0F there but doesn't end things (therefore must be special
// checked against). Because MSR and BX overlap both are checked for.

#define arm_exit_point                                                        \
 (((opcode < 0x8000000) && ((opcode & 0x000F000) == 0x000F000) &&             \
  ((opcode & 0xDB0F000) != 0x120F000)) ||                                     \
  ((opcode & 0x12FFF10) == 0x12FFF10) ||                                      \
  ((opcode & 0x8108000) == 0x8108000) ||                                      \
  ((opcode >= 0xA000000) && (opcode < 0xF000000)) ||                          \
  ((opcode >= 0xF000000) && (!is_div_swi((opcode >> 16) & 0xFF))))            \

#define arm_opcode_branch                                                     \
  ((opcode & 0xE000000) == 0xA000000)                                         \

#define arm_opcode_swi                                                        \
  ((opcode & 0xF000000) == 0xF000000)                                         \

#define arm_opcode_unconditional_branch                                       \
  (condition == 0x0E)                                                         \

#define arm_load_opcode()                                                     \
  opcode = address32(pc_address_block, (block_end_pc & 0x7FFF));              \
  condition = opcode >> 28;                                                   \
                                                                              \
  opcode &= 0xFFFFFFF;                                                        \
                                                                              \
  block_end_pc += 4                                                           \

#define arm_branch_target()                                                   \
  u32 branch_target = (block_end_pc + 4 + (((s32)(opcode & 0xFFFFFF) << 8) >> 6))

// Contiguous conditional block flags modification - it will set 0x20 in the
// condition's bits if this instruction modifies flags. Taken from the CPU
// switch so it'd better be right this time.

#define arm_set_condition(_condition)                                         \
  block_data[block_data_position].condition = _condition;                     \
  switch((opcode >> 20) & 0xFF)                                               \
  {                                                                           \
    case 0x01:                                                                \
    case 0x03:                                                                \
    case 0x09:                                                                \
    case 0x0B:                                                                \
    case 0x0D:                                                                \
    case 0x0F:                                                                \
      if((((opcode >> 5) & 0x03) == 0) || ((opcode & 0x90) != 0x90))          \
        block_data[block_data_position].condition |= 0x20;                    \
      break;                                                                  \
                                                                              \
    case 0x05:                                                                \
    case 0x07:                                                                \
    case 0x11:                                                                \
    case 0x13:                                                                \
    case 0x15 ... 0x17:                                                       \
    case 0x19:                                                                \
    case 0x1B:                                                                \
    case 0x1D:                                                                \
    case 0x1F:                                                                \
      if((opcode & 0x90) != 0x90)                                             \
        block_data[block_data_position].condition |= 0x20;                    \
      break;                                                                  \
                                                                              \
    case 0x12:                                                                \
      if(((opcode & 0x90) != 0x90) && !(opcode & 0x10))                       \
        block_data[block_data_position].condition |= 0x20;                    \
      break;                                                                  \
                                                                              \
    case 0x21:                                                                \
    case 0x23:                                                                \
    case 0x25:                                                                \
    case 0x27:                                                                \
    case 0x29:                                                                \
    case 0x2B:                                                                \
    case 0x2D:                                                                \
    case 0x2F ... 0x37:                                                       \
    case 0x39:                                                                \
    case 0x3B:                                                                \
    case 0x3D:                                                                \
    case 0x3F:                                                                \
      block_data[block_data_position].condition |= 0x20;                      \
    break;                                                                    \
  }                                                                           \

#define arm_instruction_width 4

// For now this just sets a variable that says flags should always be
// computed.

#define arm_dead_flag_eliminate()

block_data_type block_data[MAX_BLOCK_SIZE];
block_exit_type iblk_exits[MAX_EXITS];

#define smc_write_arm_yes() {                                                 \
  intptr_t offset = (pc < 0x03000000) ? 0x40000 : -0x8000;                    \
  if(address32(pc_address_block, (block_end_pc & 0x7FFF) + offset) == 0)      \
  {                                                                           \
    address32(pc_address_block, (block_end_pc & 0x7FFF) + offset) =           \
      CODE_TAG_BLOCK32;                                                       \
  }                                                                           \
}

#define smc_write_arm_no()                                                    \

#define scan_block(type, smc_write_op)                                        \
{                                                                             \
  __label__ block_end;                                                        \
  /* Find the end of the block */                                             \
  do                                                                          \
  {                                                                           \
    check_pc_region(block_end_pc);                                            \
    smc_write_##type##_##smc_write_op();                                      \
    type##_load_opcode();                                                     \
    type##_flag_status();                                                     \
    block_data[block_data_position].update_cycles = 0;                        \
                                                                              \
    if(type##_exit_point)                                                     \
    {                                                                         \
      /* Branch/branch with link */                                           \
      if(type##_opcode_branch)                                                \
      {                                                                       \
        __label__ no_direct_branch;                                           \
        type##_branch_target();                                               \
        iblk_exits[block_exit_position].branch_target = branch_target;       \
        block_exit_position++;                                                \
                                                                              \
        /* Give the branch target macro somewhere to bail if it turns out to  \
           be an indirect branch (ala malformed Thumb bl) */                  \
        no_direct_branch:;                                                    \
      }                                                                       \
                                                                              \
      /* SWI branches to the BIOS, unless it's an HLE call, then it is        \
         not parsed as an exit_point but rather an "instruction" of sorts. */ \
      if(type##_opcode_swi)                                                   \
      {                                                                       \
        iblk_exits[block_exit_position].branch_target = 0x00000008;          \
        block_exit_position++;                                                \
      }                                                                       \
                                                                              \
      type##_set_condition(condition | 0x10);                                 \
                                                                              \
      /* Only unconditional branches can end the block. */                    \
      if(type##_opcode_unconditional_branch)                                  \
      {                                                                       \
        /* Check to see if any prior block exits branch after here,           \
           if so don't end the block. Starts from the top and works           \
           down because the most recent branch is most likely to              \
           join after the end (if/then form) */                               \
        int i;                                                                \
        for(i = block_exit_position - 2; i >= 0; i--)                         \
        {                                                                     \
          if(iblk_exits[i].branch_target == block_end_pc)                    \
            break;                                                            \
        }                                                                     \
                                                                              \
        if(i < 0)                                                             \
          break;                                                              \
      }                                                                       \
      if(block_exit_position == MAX_EXITS)                                    \
        break;                                                                \
    }                                                                         \
    else                                                                      \
    {                                                                         \
      type##_set_condition(condition);                                        \
    }                                                                         \
                                                                              \
    for(unsigned i = 0; i < translation_gate_targets; i++)                    \
    {                                                                         \
      if(block_end_pc == translation_gate_target_pc[i])                       \
        goto block_end;                                                       \
    }                                                                         \
                                                                              \
    block_data_position++;                                                    \
    if (block_data_position == MAX_BLOCK_SIZE)                                \
      break;                                                                  \
  } while(1);                                                                 \
                                                                              \
  block_end:;                                                                 \
}                                                                             \

#define update_pc_limits()                                                    \
if (ram_region) {                                                             \
  if (pc >= 0x3000000) {                                                      \
    iwram_code_min = MIN(pc & 0x7FFF, iwram_code_min);                        \
    iwram_code_max = MAX(pc & 0x7FFF, iwram_code_max);                        \
  } else {                                                                    \
    ewram_code_min = MIN(pc & 0x3FFFF, ewram_code_min);                       \
    ewram_code_max = MAX(pc & 0x3FFFF, ewram_code_max);                       \
  }                                                                           \
}                                                                             \

bool translate_block_arm(u32 pc, bool ram_region) {
  pc &= ~3U;

  u32 opcode = 0;
  u32 condition;
  u32 last_condition;
  u32 pc_region = (pc >> 15);
  u8 *pc_address_block = memory_map_read[pc_region];
  const u32 block_start_pc = pc;
  u32 block_end_pc = pc;
  u32 block_exit_position = 0;
  s32 block_data_position = 0;
  u8 *backpatch_address = NULL;
  block_exit_type eblk_exits[MAX_EXITS];

  if(!pc_address_block)
    pc_address_block = load_gamepak_page(pc_region & 0x3FF);

  if(ram_region) {
    scan_block(arm, yes);
  } else {
    scan_block(arm, no);
  }

  u8 *jitbuf = ram_region ? ram_translation_ptr : rom_translation_ptr;
  u8 *jitend = ram_region ?
    &ram_translation_cache[
       RAM_TRANSLATION_CACHE_SIZE - TRANSLATION_CACHE_LIMIT_THRESHOLD
       - (0x10000 - ram_block_tag) / 2 * sizeof(ramtag_type)] :
    &rom_translation_cache[
       ROM_TRANSLATION_CACHE_SIZE - TRANSLATION_CACHE_LIMIT_THRESHOLD];

  CodeEmitter ce(jitbuf, block_start_pc);
  ce.emit_block_header();
  ce.emit_block_prologue();

  for(unsigned i = 0; i < block_exit_position; i++) {
    u32 tgt = iblk_exits[i].branch_target;
    if((tgt > block_start_pc) && (tgt < block_end_pc))
      block_data[(tgt - block_start_pc) / arm_instruction_width].update_cycles = 1;
  }

  arm_dead_flag_eliminate();

  block_exit_position = 0;
  block_data_position = 0;

  last_condition = 0x0E;

  while (pc != block_end_pc) {
    block_data[block_data_position].block_offset = ce.emit_ptr;
    ce.cyc_cnt += def_seq_cycles[pc >> 24][1];  // TODO: improve (SEQ/NSEQ)?

    if (pc == cheat_master_hook)
      ce.emit_cheat_hook<ModeARM>();

    update_pc_limits();
    translate_arm_instruction();
    block_data_position++;

    /* If it went too far the cache needs to be flushed and the process
       restarted. Because we might already be nested several stages in
       a simple recursive call here won't work, it has to pedal out to
       the beginning. */

    if (ce.emit_ptr >= jitend) {
      if (ram_region)
        flush_translation_cache_ram();
      else
        flush_translation_cache_rom();
      return false;
    }

    /* If the next instruction is a block entry point update the
       cycle counter and update */
    if (pc != block_end_pc && block_data[block_data_position].update_cycles)
      ce.emit_cycle_update();
  }

  /* This can happen if the last instruction is *not* inconditional */
  if ((last_condition & 0x0F) != 0x0E) {
    if (backpatch_address) {
      generate_branch_patch_conditional(backpatch_address, ce.emit_ptr);
    }
  }

  /* Unconditionally generate translation targets. In case we hit one or
     in the unlikely case that block was too big (and not finalized) */
  ce.generate_translation_gate<ModeARM>(pc);

  u32 eexit_cnt = 0;
  for (unsigned i = 0; i < block_exit_position; i++) {
    u32 tgt = iblk_exits[i].branch_target;
    if ((tgt >= block_start_pc) && (tgt < block_end_pc)) {
      /* Internal branch, patch to recorded address */
      const u8 *tr_tgt = block_data[(tgt - block_start_pc) / arm_instruction_width].block_offset;
      generate_branch_patch_unconditional(iblk_exits[i].branch_source, tr_tgt);
    } else {
      /* External branch, save for later */
      eblk_exits[eexit_cnt].branch_target = tgt;
      eblk_exits[eexit_cnt].branch_source = iblk_exits[i].branch_source;
      eexit_cnt++;
    }
  }

  if (ram_region)
    ram_translation_ptr = ce.emit_ptr;
  else
    rom_translation_ptr = ce.emit_ptr;

  for(unsigned i = 0; i < eexit_cnt; i++) {
    u32 tgt = eblk_exits[i].branch_target;
    const u8 *tr_tgt = (tgt == 0x8) ? bios_swi_entrypoint : block_lookup_translate_arm(tgt);
    if (!tr_tgt)
      return false;
    generate_branch_patch_unconditional(eblk_exits[i].branch_source, tr_tgt);
  }
  return true;
}

void init_bios_hooks(void)
{
  // Pre-generate this entry point so that we can safely invoke fast
  // SWI calls from ROM and RAM regardless of cache flushes.
  rom_translation_ptr = &rom_translation_cache[rom_cache_watermark];
  last_rom_translation_ptr = rom_translation_ptr;
  bios_swi_entrypoint = block_lookup_address_arm(0x8);
  rom_cache_watermark = (u32)(rom_translation_ptr - rom_translation_cache);
}

void flush_translation_cache_ram(void)
{
  /* Flushes RAM caches avoiding doing too much work (ie. wiping unused memory) */
  flush_ram_count++;
  /*printf("ram flush %d (pc %x), %x to %x, %x to %x\n",
   flush_ram_count, reg[REG_PC], iwram_code_min, iwram_code_max,
   ewram_code_min, ewram_code_max);*/

  last_ram_translation_ptr = ram_translation_cache;
  ram_translation_ptr = ram_translation_cache;

  // Proceed to clean the SMC area if needed
  // (also try to memset as little as possible for performance)
  if (iwram_code_max) {
    if(iwram_code_max > iwram_code_min) {
      iwram_code_min &= ~15U;
      iwram_code_max = MIN(iwram_code_max + 8, 0x8000);
      memset(&iwram[iwram_code_min], 0, iwram_code_max - iwram_code_min);
    } else
      memset(iwram, 0, 0x8000);
  }

  if (ewram_code_max) {
    if(ewram_code_max > ewram_code_min) {
      ewram_code_min &= ~15U;
      ewram_code_max = MIN(ewram_code_max + 8, 0x40000);
      memset(&ewram[0x40000 + ewram_code_min], 0, ewram_code_max - ewram_code_min);
    } else
      memset(&ewram[0x40000], 0, 0x40000);
  }

  iwram_code_min = ~0U;
  iwram_code_max =  0U;
  ewram_code_min = ~0U;
  ewram_code_max =  0U;
  ram_block_tag = INITIAL_TOP_TAG;
}

void flush_translation_cache_rom(void)
{
  /* We flush the generated code except for everything below the watermark. */
  last_rom_translation_ptr = &rom_translation_cache[rom_cache_watermark];
  rom_translation_ptr      = &rom_translation_cache[rom_cache_watermark];

  memset(rom_branch_hash, 0, sizeof(rom_branch_hash));
}

void init_dynarec_caches(void)
{
  /* Initialize caches so that we can start initalizing the emitter. */
  rom_translation_ptr = last_rom_translation_ptr = &rom_translation_cache[0];
  memset(rom_branch_hash, 0, sizeof(rom_branch_hash));

  ram_translation_ptr = last_ram_translation_ptr = &ram_translation_cache[0];
  memset(iwram, 0, 0x8000);
  memset(&ewram[0x40000], 0, 0x40000);

  ewram_code_min = 0;
  ewram_code_max = 0x40000;
  iwram_code_min = 0;
  iwram_code_max = 0x8000;
}

void flush_dynarec_caches(void) {
  /* Flush ROM and RAM caches. */
  flush_translation_cache_rom();
  ewram_code_min = 0;
  ewram_code_max = 0x40000;
  iwram_code_min = 0;
  iwram_code_max = 0x8000;
  flush_translation_cache_ram();
}

