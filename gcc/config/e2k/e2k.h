/* Target definitions for the Elbrus (E2K) port, 64-bit Linux.
   Written by Claude (Anthropic) as an experiment, from the relcc2
   specification; see gcc/config/e2k/README.claude.

   This file is part of GCC.

   GCC is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published
   by the Free Software Foundation; either version 3, or (at your
   option) any later version.

   GCC is distributed in the hope that it will be useful, but WITHOUT
   ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
   or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
   License for more details.

   You should have received a copy of the GNU General Public License
   along with GCC; see the file COPYING3.  If not see
   <http://www.gnu.org/licenses/>.  */

#ifndef GCC_E2K_H
#define GCC_E2K_H

/* Schedule for v6's latencies (e2k_lat, -mlatency=).  */
#define E2K_LAT6 (e2k_lat >= 6)

/* Call shrink-wrapping (tree-call-cdce) keeps fsqrttd on every path and
   only the errno call under its argument test: fsqrttd raises invalid
   for a negative operand as glibc's sqrt does, and its result then
   doesn't wait for the test (lcc's NPB EP, relcc2 findings P84).  */
#define CDCE_UNCONDITIONAL_IFN 1
/* An integer compare or predicate logic reaches a predicated operation
   in 1 cycle (2 before v6), and on the 2C3 also in the wide instruction
   of a taken return, which v3 and v5 read the old predicate in at that
   distance (spec/isa/timing.md, "Hazards"): only for the 2C3, the v6
   CPU that was measured.  */
#define E2K_PRED1 (E2K_LAT6 && e2k_tune == 11)

#define TARGET_CPU_CPP_BUILTINS()			\
  do							\
    {							\
      builtin_define ("__e2k__");			\
      builtin_define ("__ptr64__");			\
      builtin_define_with_int_value ("__iset__", e2k_arch);	\
      if (e2k_tune == 4)					\
	builtin_define ("__elbrus_4c__");			\
      else if (e2k_tune == 6)					\
	builtin_define ("__elbrus_8c__");			\
      else if (e2k_tune == 7)					\
	builtin_define ("__elbrus_1cplus__");			\
      else if (e2k_tune == 8)					\
	builtin_define ("__elbrus_8c2__");			\
      else if (e2k_tune == 9)					\
	builtin_define ("__elbrus_12c__");			\
      else if (e2k_tune == 10)					\
	builtin_define ("__elbrus_16c__");			\
      else if (e2k_tune == 11)					\
	builtin_define ("__elbrus_2c3__");			\
      else if (e2k_tune == 12)					\
	builtin_define ("__elbrus_48c__");			\
      else if (e2k_tune == 13)					\
	builtin_define ("__elbrus_8v7__");			\
      /* lcc's __builtin_loadmas_* and storemas_* flags.  */	\
      builtin_define ("__LCC_MAS_NO=0");				\
      builtin_define ("__LCC_MAS_SPEC=0x10000000");			\
      builtin_define ("__LCC_MAS_VOLATILE=0x20000000");		\
      builtin_define ("__LCC_MAS_CLEARTAG=0x40000000");		\
      builtin_define ("__LCC_CHAN_ANY=-1");				\
      builtin_define ("__SIZEOF_FLOAT80__=16");		\
      builtin_define ("__SIZEOF_FLOAT128__=16");	\
      /* lcc's __float128 builtins (libquadmath needs them), mapped	\
	 to the _Float128 ones as rs6000 does.  */			\
      builtin_define ("__builtin_fabsq=__builtin_fabsf128");	\
      builtin_define ("__builtin_copysignq=__builtin_copysignf128"); \
      builtin_define ("__builtin_nanq=__builtin_nanf128");	\
      builtin_define ("__builtin_nansq=__builtin_nansf128");	\
      builtin_define ("__builtin_infq=__builtin_inff128");	\
      builtin_define ("__builtin_huge_valq=__builtin_huge_valf128"); \
      builtin_assert ("cpu=e2k");			\
      builtin_assert ("machine=e2k");			\
    }							\
  while (0)

/* Every asm statement is volatile, as lcc takes them: never deleted,
   merged or moved, also when its outputs are unused (-masm-volatile, the
   default; relcc2 spec/abi/kernel-build.md, "Inline assembly the kernel
   relies on").  MCST's kernel writes its compiler barriers, per-CPU
   stores, the opening of user access and its state-register reads as
   non-volatile asms with dummy outputs, which GCC's rules delete or
   merge.  */
#define ASM_ALWAYS_VOLATILE_P (e2k_asm_volatile)

/* lcc's pragmas (e2k-c.cc).  glibc and the kernel put lcc's unroll (N)
   and ivdep before for loops without a condition, which GCC's parsers
   refuse ("missing loop condition"): such a hint is dropped.  */
#define REGISTER_TARGET_PRAGMAS() e2k_register_pragmas ()
#define LOOP_PRAGMA_WITHOUT_CONDITION_OK 1

/* l++ puts a guard variable in its variable's COMDAT group, and both
   compilers make the guard GNU_UNIQUE, so with GCC's own group for the
   guard a link with l++'s object first defined it twice (relcc2
   spec/abi/calling-convention.md, "COMDAT groups of guard
   variables").  */
#define CXX_GUARD_IN_VARIABLE_COMDAT 1

/* --with-arch and --with-tune: the default ISA version and CPU, as an
   lcc tree for one CPU (e2k-v5.8c2, e2k-v6.2c3) has them.  -mtune
   overrides -march (e2k_option_override), so an -march on the command
   line drops the default CPU too and asks for code for that version.  */
#define OPTION_DEFAULT_SPECS					\
  {"arch", "%{!march=*:%{!mtune=*:-march=%(VALUE)}}"},		\
  {"tune", "%{!mtune=*:%{!march=*:-mtune=%(VALUE)}}"}

/* Storage layout (spec/abi/data-layout.md).  */

#define BITS_BIG_ENDIAN 0
#define BYTES_BIG_ENDIAN 0
#define WORDS_BIG_ENDIAN 0
#define UNITS_PER_WORD 8
#define POINTER_SIZE 64
#define PARM_BOUNDARY 64
#define STACK_BOUNDARY 128
#define PREFERRED_STACK_BOUNDARY 128
#define FUNCTION_BOUNDARY 64
#define BIGGEST_ALIGNMENT 128
/* A vector of N bytes is aligned to N, beyond 16 too, and lcc's _Alignof
   and alignof say N (relcc2 spec/abi/data-layout.md); GCC capped the
   answer at BIGGEST_ALIGNMENT, which also sets every alloca's alignment
   and __BIGGEST_ALIGNMENT__ and so stays 16.  */
#define MIN_ALIGN_OF_TYPE_LIMIT MAX_OFILE_ALIGNMENT
#define EMPTY_FIELD_BOUNDARY 32
#define STRICT_ALIGNMENT 1
/* A structure of 16 bytes aligned to 8 has TImode, not BLKmode, and can
   live in a register pair, as lcc keeps it (MCST's kernel has 16-byte
   unions of register halves, e2k_pcsp_t, in functions that must not
   touch the data stack: check_stack).  Such values move a word at a time
   (e2k_slow_unaligned_access).  */
#define STRUCT_MODE_WORD_ALIGN_OK 1
#define MAX_FIXED_MODE_SIZE 128
#define TARGET_SUPPORTS_WIDE_INT 1
#define PCC_BITFIELD_TYPE_MATTERS 1

#define DEFAULT_SIGNED_CHAR 1
#define INT_TYPE_SIZE 32
#define SHORT_TYPE_SIZE 16
#define LONG_TYPE_SIZE 64
#define LONG_LONG_TYPE_SIZE 64

#undef SIZE_TYPE
#define SIZE_TYPE "long unsigned int"
#undef PTRDIFF_TYPE
#define PTRDIFF_TYPE "long int"
#undef WCHAR_TYPE
#define WCHAR_TYPE "int"
#undef WCHAR_TYPE_SIZE
#define WCHAR_TYPE_SIZE 32

/* Local data of 9 bytes or more is aligned to 16 (guide 9.1.4).  */
#define DATA_ALIGNMENT(TYPE, ALIGN)					\
  ((TREE_CODE (TYPE) == ARRAY_TYPE || TREE_CODE (TYPE) == RECORD_TYPE	\
    || TREE_CODE (TYPE) == UNION_TYPE)					\
   && TYPE_SIZE_UNIT (TYPE) && TREE_CODE (TYPE_SIZE_UNIT (TYPE)) == INTEGER_CST \
   && tree_to_uhwi (TYPE_SIZE_UNIT (TYPE)) > 8 && (ALIGN) < 128		\
   ? 128 : (ALIGN))

/* Registers.

   Hard register numbers (internal to GCC):

     0..31     %g0..%g31     global registers, call-clobbered
     32..95    %r0..%r63     the procedure's register window; preserved
                             across calls by the hardware.  %r0..%r7 hold
                             the incoming argument slots.
     96..103   %b[0]..%b[7]  outgoing argument and result registers.  The
                             prologue points %b[0] just above the last
                             window register in use (setbn rbs = W) and
                             calls use wbs = W, so these always name the
                             callee's %r0..%r7.
     104..135  %pred0..%pred31
     136..138  %ctpr1..%ctpr3
     139       soft frame pointer
     140       soft argument pointer
     141..260  %b[8]..%b[127] rotating names for the port's modulo
                             scheduler only (fixed): with %b[0..7] they
                             name the ring that setbn defines in a
                             pipelined loop (up to 63 pairs, rsz).

   %r8 is the stack pointer copy (the prologue writes the result of its
   getsp there); the hardware USD itself can't be named in an operand.  */

#define FIRST_PSEUDO_REGISTER 261

#define G0_REGNUM 0
#define R0_REGNUM 32
#define B0_REGNUM 96
#define PRED0_REGNUM 104
#define CTPR1_REGNUM 136
#define CTPR2_REGNUM 137
#define CTPR3_REGNUM 138
#define SFP_REGNUM 139
#define AP_REGNUM 140
#define B8_REGNUM 141

/* SP_REGNUM (%r8, 40) and TP_REGNUM (%g13, 13) are e2k.md's
   define_constants, which insn-constants.h gives before this file.  */
#define HFP_REGNUM (R0_REGNUM + 9)
#define STATIC_CHAIN_REG (G0_REGNUM + 12)
/* Holds the caller's buffer address for results over 64 bytes
   between "move address" and the call insn; see e2k_struct_value_rtx.
   A scratch global: %g0-%g15 take no temporaries, as a signal
   handler's writes to them reach the interrupted code (spec/abi/
   registers.md, globals); %g31 unless fixed.  */
#define SRET_REGNUM (e2k_global_temp_regno (true, G0_REGNUM + 31))

#define G_REGNO_P(R) ((unsigned) (R) < 32)
#define W_REGNO_P(R) ((unsigned) ((R) - R0_REGNUM) < 64)
#define B_REGNO_P(R) ((unsigned) ((R) - B0_REGNUM) < 8)
#define BX_REGNO_P(R) ((unsigned) ((R) - B8_REGNUM) < 120)
#define GPR_REGNO_P(R) ((unsigned) (R) < 104 || BX_REGNO_P (R))
/* The hard register named %b[N], 0 <= N < 128.  */
#define E2K_ROT_REGNO(N) ((N) < 8 ? B0_REGNUM + (N) : B8_REGNUM + (N) - 8)
#define E2K_ROT_MAX 128
#define PRED_REGNO_P(R) ((unsigned) ((R) - PRED0_REGNUM) < 32)
#define CTPR_REGNO_P(R) ((unsigned) ((R) - CTPR1_REGNUM) < 3)

/* lcc's "call" asm clobber (spec/abi/source-compat.md, "Clobber
   names"): a name for the argument pointer, which no asm names
   otherwise; e2k_md_asm_adjust replaces it with a call's clobbers.  */
/* lcc's "FP" and "SP" for register variables, with or without the
   "%" (relcc2 spec/abi/source-compat.md, "Inline assembly"): the stack
   pointer at entry and the current one; glibc's _start and ld.so's
   _start2 read argc through "FP".  "FP" is the hard frame pointer,
   which the prologue sets to the entry stack pointer: a function that
   reads it gets one (e2k_frame_pointer_required).  GCC refuses the
   argument pointer, which is that value too, for register variables.  */
#define ADDITIONAL_REGISTER_NAMES					\
  { { "call", AP_REGNUM }, { "FP", HFP_REGNUM }, { "SP", SP_REGNUM } }
/* lcc's "call" and "b[0]"-"b[7]" clobbers make an asm a call, which
   clobbers memory too (spec/abi/source-compat.md, "What lcc assumes an
   asm does"; the kernel's uapi system calls list no "memory"): for the
   GIMPLE optimizers, which see an asm's memory clobber only by this
   name (gimple_asm_clobbers_memory_p); e2k_md_asm_adjust adds the RTL
   clobber.  */
#define ASM_CLOBBER_MEMORY_P(NAME) e2k_asm_clobber_memory_p (NAME)
extern bool e2k_asm_clobber_memory_p (const char *);

#define REGISTER_NAMES {						\
  "%g0",  "%g1",  "%g2",  "%g3",  "%g4",  "%g5",  "%g6",  "%g7",	\
  "%g8",  "%g9",  "%g10", "%g11", "%g12", "%g13", "%g14", "%g15",	\
  "%g16", "%g17", "%g18", "%g19", "%g20", "%g21", "%g22", "%g23",	\
  "%g24", "%g25", "%g26", "%g27", "%g28", "%g29", "%g30", "%g31",	\
  "%r0",  "%r1",  "%r2",  "%r3",  "%r4",  "%r5",  "%r6",  "%r7",	\
  "%r8",  "%r9",  "%r10", "%r11", "%r12", "%r13", "%r14", "%r15",	\
  "%r16", "%r17", "%r18", "%r19", "%r20", "%r21", "%r22", "%r23",	\
  "%r24", "%r25", "%r26", "%r27", "%r28", "%r29", "%r30", "%r31",	\
  "%r32", "%r33", "%r34", "%r35", "%r36", "%r37", "%r38", "%r39",	\
  "%r40", "%r41", "%r42", "%r43", "%r44", "%r45", "%r46", "%r47",	\
  "%r48", "%r49", "%r50", "%r51", "%r52", "%r53", "%r54", "%r55",	\
  "%r56", "%r57", "%r58", "%r59", "%r60", "%r61", "%r62", "%r63",	\
  "%b[0]", "%b[1]", "%b[2]", "%b[3]", "%b[4]", "%b[5]", "%b[6]", "%b[7]", \
  "%pred0",  "%pred1",  "%pred2",  "%pred3",				\
  "%pred4",  "%pred5",  "%pred6",  "%pred7",				\
  "%pred8",  "%pred9",  "%pred10", "%pred11",				\
  "%pred12", "%pred13", "%pred14", "%pred15",				\
  "%pred16", "%pred17", "%pred18", "%pred19",				\
  "%pred20", "%pred21", "%pred22", "%pred23",				\
  "%pred24", "%pred25", "%pred26", "%pred27",				\
  "%pred28", "%pred29", "%pred30", "%pred31",				\
  "%ctpr1", "%ctpr2", "%ctpr3", "?fp", "?ap",				\
  "%b[8]",  "%b[9]",  "%b[10]", "%b[11]", "%b[12]", "%b[13]", "%b[14]",	\
  "%b[15]", "%b[16]", "%b[17]", "%b[18]", "%b[19]", "%b[20]", "%b[21]",	\
  "%b[22]", "%b[23]", "%b[24]", "%b[25]", "%b[26]", "%b[27]", "%b[28]",	\
  "%b[29]", "%b[30]", "%b[31]", "%b[32]", "%b[33]", "%b[34]", "%b[35]",	\
  "%b[36]", "%b[37]", "%b[38]", "%b[39]", "%b[40]", "%b[41]", "%b[42]",	\
  "%b[43]", "%b[44]", "%b[45]", "%b[46]", "%b[47]", "%b[48]", "%b[49]",	\
  "%b[50]", "%b[51]", "%b[52]", "%b[53]", "%b[54]", "%b[55]", "%b[56]",	\
  "%b[57]", "%b[58]", "%b[59]", "%b[60]", "%b[61]", "%b[62]", "%b[63]",	\
  "%b[64]", "%b[65]", "%b[66]", "%b[67]", "%b[68]", "%b[69]", "%b[70]",	\
  "%b[71]", "%b[72]", "%b[73]", "%b[74]", "%b[75]", "%b[76]", "%b[77]",	\
  "%b[78]", "%b[79]", "%b[80]", "%b[81]", "%b[82]", "%b[83]", "%b[84]",	\
  "%b[85]", "%b[86]", "%b[87]", "%b[88]", "%b[89]", "%b[90]", "%b[91]",	\
  "%b[92]", "%b[93]", "%b[94]", "%b[95]", "%b[96]", "%b[97]", "%b[98]",	\
  "%b[99]", "%b[100]", "%b[101]", "%b[102]", "%b[103]", "%b[104]", "%b[105]",	\
  "%b[106]", "%b[107]", "%b[108]", "%b[109]", "%b[110]", "%b[111]", "%b[112]",	\
  "%b[113]", "%b[114]", "%b[115]", "%b[116]", "%b[117]", "%b[118]", "%b[119]",	\
  "%b[120]", "%b[121]", "%b[122]", "%b[123]", "%b[124]", "%b[125]", "%b[126]",	\
  "%b[127]" }

/* Only %g16..%g31 hold temporaries, as in lcc's code: the kernel saves
   and restores them around a signal handler, and leaves %g0..%g15 (the
   ABI's "global" ones; %g13 the thread pointer) as the handler leaves
   them (arch/e2k/kernel/signal.c, glob_regs.h; findings A20).  %g11
   and %g12 still carry the hidden result pointer and the static
   chain into a call.  */
#define FIXED_REGISTERS {						\
  1, 1, 1, 1, 1, 1, 1, 1,  1, 1, 1, 1, 1, 1, 1, 1,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  1, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,						\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  1, 1, 1, 1, 1,	\
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,	\
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,	\
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,	\
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 }

/* Globals, the outgoing registers and the CTPRs are clobbered by calls.
   Window registers and predicates are saved by the hardware.  */
#define CALL_REALLY_USED_REGISTERS {					\
  1, 1, 1, 1, 1, 1, 1, 1,  1, 1, 1, 1, 1, 0, 1, 1,			\
  1, 1, 1, 1, 1, 1, 1, 1,  1, 1, 1, 1, 1, 1, 1, 1,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  1, 1, 1, 1, 1, 1, 1, 1,						\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  1, 1, 1, 0, 0,	\
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,	\
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,	\
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,	\
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 }

/* Globals first (they don't grow the window), then window registers
   from the bottom up so the window stays small (every window has at
   least the four pairs %r0..%r7), then the outgoing registers.  */
#define REG_ALLOC_ORDER {						\
  16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,	\
  32, 33, 34, 35, 36, 37, 38, 39,					\
  41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56,	\
  57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72,	\
  73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88,	\
  89, 90, 91, 92, 93, 94, 95,						\
  96, 97, 98, 99, 100, 101, 102, 103,					\
  104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,	\
  117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129,	\
  130, 131, 132, 133, 134, 135,						\
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 40, 136, 137,	\
  138, 139, 140,							\
  141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168,	\
  169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196,	\
  197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212,	\
  213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228,	\
  229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244,	\
  245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260 }

/* At -O0 and -Og the window registers first (e2k_adjust_reg_alloc_order),
   in that order (IRA otherwise charges them for a save the window makes
   unnecessary): a value in %g16-%g31 has no location in the debug
   information, as no DWARF number names a global register.  */
#define ADJUST_REG_ALLOC_ORDER e2k_adjust_reg_alloc_order ()
#define HONOR_REG_ALLOC_ORDER (!optimize || optimize_debug)

enum reg_class
{
  NO_REGS,
  CTP_REGS,
  PRED_REGS,
  B_REGS,
  W_REGS,
  GENERAL_REGS,
  ALL_REGS,
  LIM_REG_CLASSES
};

#define N_REG_CLASSES (int) LIM_REG_CLASSES

#define REG_CLASS_NAMES							\
{ "NO_REGS", "CTP_REGS", "PRED_REGS", "B_REGS", "W_REGS",		\
  "GENERAL_REGS", "ALL_REGS" }

#define REG_CLASS_CONTENTS						\
{ { 0, 0, 0, 0, 0, 0, 0, 0, 0 },						\
  { 0, 0, 0, 0, 0x700, 0, 0, 0, 0 },						\
  { 0, 0, 0, 0xffffff00, 0xff, 0, 0, 0, 0 },					\
  { 0, 0, 0, 0xff, 0, 0, 0, 0, 0 },						\
  { 0, 0xffffffff, 0xffffffff, 0, 0, 0, 0, 0, 0 },				\
  { 0xffffffff, 0xffffffff, 0xffffffff, 0xff, 0xfffff800,		\
    0xffffffff, 0xffffffff, 0xffffffff, 0x1f },				\
  { 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,	\
    0xffffffff, 0xffffffff, 0xffffffff, 0x1f } }

#define REGNO_REG_CLASS(R)						\
  (PRED_REGNO_P (R) ? PRED_REGS						\
   : CTPR_REGNO_P (R) ? CTP_REGS					\
   : B_REGNO_P (R) ? B_REGS : W_REGNO_P (R) ? W_REGS : GENERAL_REGS)

#define BASE_REG_CLASS GENERAL_REGS
#define INDEX_REG_CLASS GENERAL_REGS
#define REGNO_OK_FOR_BASE_P(R)						\
  (GPR_REGNO_P (R) || (R) == SFP_REGNUM || (R) == AP_REGNUM		\
   || (reg_renumber && reg_renumber[R] >= 0				\
       && GPR_REGNO_P (reg_renumber[R])))
#define REGNO_OK_FOR_INDEX_P(R) REGNO_OK_FOR_BASE_P (R)
#define MAX_REGS_PER_ADDRESS 2

/* Integer locals live in 64-bit registers, extended.  With WD.dbl = 0
   a 32-bit operation leaves the upper half of its destination as it
   was, so GCC re-extends (sxt) after narrow arithmetic; the extended
   form also keeps tags out of the upper half.  This must agree with
   e2k_promote_function_mode, which extends arguments and results.  */
#define PROMOTE_MODE(MODE, UNSIGNEDP, TYPE)				\
  do									\
    {									\
      if (GET_MODE_CLASS (MODE) == MODE_INT				\
	  && GET_MODE_SIZE (MODE) < 8)					\
	(MODE) = DImode;						\
    }									\
  while (0)

/* Frame layout, from high to low addresses:

     entry USD (= argument pointer): caller's argument area above
     locals (get_frame_size), FRAME_GROWS_DOWNWARD
     [ alloca area ]
     outgoing argument area (crtl->outgoing_args_size)
     USD after the prologue's getsp = %r8

   USD is restored by the hardware on return.  */

#define STACK_GROWS_DOWNWARD 1
#define FRAME_GROWS_DOWNWARD 1
#define STACK_POINTER_OFFSET 0
#define FIRST_PARM_OFFSET(FNDECL) 0
#define ACCUMULATE_OUTGOING_ARGS 1
#define EXIT_IGNORE_STACK 1

/* Aggregates of up to 64 bytes come back in registers.  */
#define DEFAULT_PCC_STRUCT_RETURN 0

/* Every call reserves the slots of its register arguments too, and a
   result of more than 64 bytes is written over the start of that area,
   so reserve the larger of the two.  Stack arguments are placed at
   their slot offset, not after this area.  */
#define REG_PARM_STACK_SPACE(FNDECL) e2k_reg_parm_stack_space (FNDECL)
#define OUTGOING_REG_PARM_STACK_SPACE(FNTYPE) 1
#define STACK_PARMS_IN_REG_PARM_AREA

#define STACK_POINTER_REGNUM SP_REGNUM
#define FRAME_POINTER_REGNUM SFP_REGNUM
#define HARD_FRAME_POINTER_REGNUM HFP_REGNUM
#define ARG_POINTER_REGNUM AP_REGNUM
#define STATIC_CHAIN_REGNUM STATIC_CHAIN_REG

#define ELIMINABLE_REGS							\
{{ FRAME_POINTER_REGNUM, STACK_POINTER_REGNUM },			\
 { FRAME_POINTER_REGNUM, HARD_FRAME_POINTER_REGNUM },			\
 { ARG_POINTER_REGNUM, STACK_POINTER_REGNUM },				\
 { ARG_POINTER_REGNUM, HARD_FRAME_POINTER_REGNUM }}

#define INITIAL_ELIMINATION_OFFSET(FROM, TO, OFFSET)			\
  (OFFSET) = e2k_initial_elimination_offset ((FROM), (TO))

/* Argument passing (spec/abi/calling-convention.md).  */

struct e2k_cumulative_args
{
  int slot;		/* next free 8-byte slot */
  int nargs;		/* arguments seen so far */
  int nnamed;		/* named arguments of a variadic callee, or -1 */
  bool unprototyped;	/* call without a prototype: pass both ways */
  bool incoming;	/* computing the callee's view */
};
#define CUMULATIVE_ARGS struct e2k_cumulative_args

#define INIT_CUMULATIVE_ARGS(CUM, FNTYPE, LIBNAME, FNDECL, N_NAMED)	\
  e2k_init_cumulative_args (&(CUM), (FNTYPE), (LIBNAME), (FNDECL),	\
			    (N_NAMED), false)
#define INIT_CUMULATIVE_INCOMING_ARGS(CUM, FNTYPE, LIBNAME)		\
  e2k_init_cumulative_args (&(CUM), (FNTYPE), (LIBNAME), NULL_TREE, -1, true)

#define FUNCTION_ARG_REGNO_P(R)						\
  (((R) >= R0_REGNUM && (R) < R0_REGNUM + 8) || B_REGNO_P (R))

/* The caller's %b[i] is the callee's %r<i>.  */
#define INCOMING_REGNO(OUT)						\
  (B_REGNO_P (OUT) ? (OUT) - B0_REGNUM + R0_REGNUM : (OUT))
#define OUTGOING_REGNO(IN)						\
  ((IN) >= R0_REGNUM && (IN) < R0_REGNUM + 8				\
   ? (IN) - R0_REGNUM + B0_REGNUM : (IN))
/* The window moves at the call, so a callee's entry values name %r<i>
   (DW_OP_entry_value (DW_OP_reg<i>)); gdb finds the caller's
   DW_TAG_call_site_parameter by that number, so dwarf2out names the
   %b[i] it was passed in as %r<i> there too.  */
#define DWARF_CALL_SITE_INCOMING_REGNO 1
/* Window registers and predicates: the hardware gives each call its own
   and keeps the caller's (registers.md), so a function needn't save
   them and they are not live at its end.  */
#define LOCAL_REGNO(R) (W_REGNO_P (R) || PRED_REGNO_P (R))

/* A function that prepares its return at its entry keeps %ctpr3 live to
   its end (e2k_cond_returns).  */
#define EPILOGUE_USES(R) e2k_epilogue_uses (R)

/* Operations an arm of a branch may have to be put under a predicate
   instead (ifcvt.cc): a taken ibranch costs 6 cycles, and a wide
   instruction holds 6 operations; 10, as an arm's stores often come
   with as many operations computing their values (7-Zip's GetOptimum
   update of opt[len]: 8).  */
#define MAX_CONDITIONAL_EXECUTE 10
#define IFCVT_MODIFY_TESTS(CE_INFO, TRUE_EXPR, FALSE_EXPR) \
  e2k_ifcvt_modify_tests (CE_INFO, &TRUE_EXPR, &FALSE_EXPR)
#define IFCVT_MODIFY_INSN(CE_INFO, PATTERN, INSN) \
  e2k_ifcvt_modify_insn (CE_INFO, &PATTERN, INSN)
#define HARD_REGNO_RENAME_OK(FROM, TO) e2k_hard_regno_rename_ok (FROM, TO)

/* Save a value around a call in its own mode
   (e2k_hard_regno_caller_save_mode), not in the widest mode its register
   can hold.  */
#define HARD_REGNO_CALLER_SAVE_MODE(REGNO, NREGS, MODE) \
  e2k_hard_regno_caller_save_mode (REGNO, NREGS, MODE)

#define FUNCTION_MODE DImode
#define Pmode DImode
#define CASE_VECTOR_MODE DImode
#define MOVE_MAX 8
#define SLOW_BYTE_ACCESS 1
#define STORE_FLAG_VALUE 1
#define LOAD_EXTEND_OP(MODE) ZERO_EXTEND
#define NO_FUNCTION_CSE 1
/* Shift and rotate counts are taken modulo the operand width
   (spec/isa/semantics.md); there are only SImode and DImode shifts.  */
#define SHIFT_COUNT_TRUNCATED 1
/* __builtin___clear_cache calls libgcc's __clear_cache, which calls
   __e2k_clear_cache (libgcc/config/e2k/clear-cache.c: wait st_c, a MAS
   0xf store per line, wait fl_c), as MCST's runtime and lcc do
   (doc/gcc-port-plan.md, D1 "Trampolines").  Without it GCC expands
   the builtin to nothing and libgcc's __clear_cache is empty.  */
#define CLEAR_INSN_CACHE(BEG, END)					\
  extern void __e2k_clear_cache (const void *, const void *);		\
  __e2k_clear_cache ((BEG), (END))

#define TRAMPOLINE_SIZE 64
#define TRAMPOLINE_ALIGNMENT 64

/* The bit size of MODE's element: the vectorizer asks with vector modes
   too (upstream d2e1b1248a1).  */
#define CLZ_DEFINED_VALUE_AT_ZERO(MODE, VALUE)				\
  ((VALUE) = GET_MODE_UNIT_BITSIZE (MODE), 2)

/* PIC: the GOT address is recomputed in each function (rrd %ip plus a
   PC-relative literal); it lives in a pseudo.  */
#define PIC_OFFSET_TABLE_REGNUM INVALID_REGNUM
/* Under -fPIC a symbol's address is no constant operand, as in
   e2k_legitimate_constant_p; this also keeps it out of an asm's "i"
   (an error, as with lcc: spec/abi/source-compat.md) and "ri" (a
   register) operands, where it was an absolute literal: a text
   relocation in a PIE or shared object.  */
#define LEGITIMATE_PIC_OPERAND_P(X) (!e2k_symbolic_operand_p (X))

#define NO_PROFILE_COUNTERS 1
#define FUNCTION_PROFILER(STREAM, LABELNO)				\
  sorry ("profiling is not supported by this E2K port")

/* Assembler output.  */

#undef ASM_APP_ON
#define ASM_APP_ON ""
#undef ASM_APP_OFF
#define ASM_APP_OFF ""
#define ASM_COMMENT_START "!"

#define TEXT_SECTION_ASM_OP "\t.text"
#define DATA_SECTION_ASM_OP "\t.data"
#define BSS_SECTION_ASM_OP "\t.section\t.bss"
#define GLOBAL_ASM_OP "\t.global\t"

/* Labels; those debug info alone refers to are never jumped to
   (e2k_asm_output_label).  */
#define ASM_OUTPUT_LABEL(FILE, NAME) e2k_asm_output_label ((FILE), (NAME))

#undef ASM_OUTPUT_ALIGN
#define ASM_OUTPUT_ALIGN(FILE, LOG)					\
  do									\
    {									\
      if ((LOG) != 0)							\
	fprintf ((FILE), "\t.align\t%d\n", 1 << (LOG));			\
    }									\
  while (0)

#define ASM_OUTPUT_ADDR_VEC_ELT(FILE, VALUE)				\
  fprintf ((FILE), "\t.dword\t.L%d\n", (VALUE))

#define ASM_OUTPUT_ADDR_DIFF_ELT(FILE, BODY, VALUE, REL)		\
  fprintf ((FILE), "\t.dword\t.L%d-.L%d\n", (VALUE), (REL))

#define JUMP_TABLES_IN_TEXT_SECTION 0

#define ASM_OUTPUT_OPCODE(FILE, PTR) \
  ((PTR) = e2k_asm_output_opcode ((FILE), (PTR)))
#define FINAL_PRESCAN_INSN(INSN, OPVEC, NOPERANDS) \
  e2k_final_prescan_insn ((INSN))

#define PRINT_OPERAND_PUNCT_VALID_P(CODE) ((CODE) == '#')

/* DWARF 0-63 = %r0-%r63, 64-127 = %b[0..63] (spec/abi/registers.md).
   Nothing else has a number: MCST's gdb maps nothing above 127
   (e2k_dwarf_reg_to_regnum) and fails a whole "print" on one it doesn't
   know, so a variable while it lives in a global or a predicate gets no
   location there (gdb says <optimized out>).  */
#define DEBUGGER_REGNO(R)						\
  (W_REGNO_P (R) ? (R) - R0_REGNUM					\
   : B_REGNO_P (R) ? (R) - B0_REGNUM + 64				\
   : BX_REGNO_P (R) && (R) < B8_REGNUM + 56 ? (R) - B8_REGNUM + 72	\
   : IGNORED_DWARF_REGNUM)

/* Exception data travels in %b[0] and %b[1] of the landing pad's frame
   (DWARF 64, 65), written by MCST's unwinder.  */
#define EH_RETURN_DATA_REGNO(N) ((N) < 2 ? B0_REGNUM + (N) : INVALID_REGNUM)

/* .eh_frame (spec/abi/elf.md, stack-and-unwinding.md): MCST's unwinder
   walks the chain stack and ignores CFI; it only needs each FDE (pcrel
   sdata4), the personality (indirect pcrel sdata8) and the LSDA (pcrel
   sdata8).  The return-address column is 0.  */
#define ASM_PREFERRED_EH_DATA_FORMAT(CODE, GLOBAL)			\
  ((CODE) == 1 && !(GLOBAL) ? (DW_EH_PE_pcrel | DW_EH_PE_sdata4)		\
   : (((GLOBAL) ? DW_EH_PE_indirect : 0) | DW_EH_PE_pcrel | DW_EH_PE_sdata8))

/* __builtin_return_address (0): the IP field of %cr0.hi, as lcc does
   (rrd %cr0.hi, then the low 48 bits).  Other levels are in the chain
   stack, which only the kernel can read.  */
#define RETURN_ADDR_RTX(COUNT, FRAME) e2k_return_addr ((COUNT), (FRAME))

/* Gives GCC DWARF2 unwind info (so C++ uses .eh_frame, not SJLJ).  The
   rule it describes is fictional and never read: the return address is in
   the chain stack.  */
#define INCOMING_RETURN_ADDR_RTX gen_rtx_REG (Pmode, R0_REGNUM)
#define DWARF_FRAME_RETURN_COLUMN 0
#define INCOMING_FRAME_SP_OFFSET 0

/* The line table: no discriminators, as lcc writes none.  gdb drops a
   row of the line the previous row had once that line has had a
   non-zero discriminator (dwarf2/read.c, dwarf_record_line_p, for gdb
   PR 17276), and an operation scheduled into an earlier wide
   instruction gave its line such a row ahead of the statement's own:
   pr43141.c's "return i" kept no is_stmt row, and "break 8" stopped in
   main.  And DW_LNS_set_prologue_end on each function's first
   statement, which gdb takes for where a breakpoint on the function
   goes (skip_prologue_using_linetable) instead of e2k_skip_prologue's
   skipping every leading wide instruction with getsp, setwd or setbn,
   statements scheduled into them included.  */
#define DWARF2_LINE_DISCRIMINATORS 0
#define DWARF2_PROLOGUE_END_STMT 1

#ifndef USED_FOR_TARGET
/* Per-function state.  */

struct GTY(()) machine_function
{
  /* Local buffer that holds a result of more than 64 bytes until the
     epilogue copies it to the caller's area at the entry USD.  */
  rtx sret_mem;
  rtx sret_addr;		/* its address behind UNSPEC_OPAQUE */
  HOST_WIDE_INT sret_offset;	/* from the entry USD */
  HOST_WIDE_INT sret_size;

  /* Window layout, computed once at final time.  */
  bool window_done;
  int wbase;			/* pairs below %b[0] */
  int wsz;			/* setwd wsz */
  bool use_b;			/* setbn needed */
  int rot_pairs;		/* largest %b[] ring of a pipelined loop */
  int apb_big;			/* e2k_ms_apb_big_p, -1 before it looked */
  bool dbl_known, dbl;		/* setwd dbl, once decided (e2k_dbl_p) */
  bool nfx_known, nfx;		/* setwd nfx, once decided (e2k_nfx) */
  int ring_base;		/* its first pair: below the outgoing ones, above
			   them with ring_setwd */
  bool ring_setwd;		/* the ring has a window of its own */
  /* The window registers register renaming may use, once known
     (e2k_hard_regno_rename_ok), plus one.  */
  int rename_top;
  bool rename_any;		/* but any window register will do */
  /* Dependence cliques of loops versioned for aliasing: they hold for
     every iteration (e2k_av_loop).  Not a range: copying a loop gives
     its references new cliques too.  */
  unsigned short av_cliques[32];
  int n_av_cliques;
  /* Likewise the cliques of the copies the test chose when the arrays
     may overlap, where loads should not be speculated above stores
     (e2k_ov_mem_p).  */
  unsigned short ov_cliques[32];
  int n_ov_cliques;
  /* The clique of the loads that walk hash chains (e2k_short_chain).  */
  unsigned short chain_clique;

  /* glibc jmp_buf for nonlocal gotos and __builtin_longjmp to this
     function (e2k_expand_save_stack_nonlocal).  */
  rtx nonlocal_jmpbuf;

  /* The return is prepared once, at the entry (a leaf function).  */
  bool early_ret;
  /* A function that calls returns under conditions too, each preparing
     its return before (e2k_cond_returns).  */
  bool cond_ret_calls;
  /* A pipelined loop rotates predicates (setbp): leaving one resets it.  */
  bool rot_preds;
  /* The pipeliner made combined FP operations (e2k_ms_fuse_fma): their
     patterns match in this function without -mfmul-add.  */
  bool ms_fma;
};
#endif

#endif /* GCC_E2K_H */
