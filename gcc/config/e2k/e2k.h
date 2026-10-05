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

#define TARGET_CPU_CPP_BUILTINS()			\
  do							\
    {							\
      builtin_define ("__e2k__");			\
      builtin_define ("__ptr64__");			\
      builtin_define_with_int_value ("__iset__", e2k_arch);	\
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
#define EMPTY_FIELD_BOUNDARY 32
#define STRICT_ALIGNMENT 1
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
     141..196  %b[8]..%b[63] rotating names for the port's modulo scheduler
                             only (fixed): with %b[0..7] they name the
                             ring that setbn defines in a pipelined loop.

   %r8 is the stack pointer copy (the prologue writes the result of its
   getsp there); the hardware USD itself can't be named in an operand.  */

#define FIRST_PSEUDO_REGISTER 197

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

#define SP_REGNUM (R0_REGNUM + 8)
#define HFP_REGNUM (R0_REGNUM + 9)
#define TP_REGNUM (G0_REGNUM + 13)
#define STATIC_CHAIN_REG (G0_REGNUM + 12)
/* Holds the caller's buffer address for results over 64 bytes
   between "move address" and the call insn; see e2k_struct_value_rtx.  */
#define SRET_REGNUM (G0_REGNUM + 11)

#define G_REGNO_P(R) ((unsigned) (R) < 32)
#define W_REGNO_P(R) ((unsigned) ((R) - R0_REGNUM) < 64)
#define B_REGNO_P(R) ((unsigned) ((R) - B0_REGNUM) < 8)
#define BX_REGNO_P(R) ((unsigned) ((R) - B8_REGNUM) < 56)
#define GPR_REGNO_P(R) ((unsigned) (R) < 104 || BX_REGNO_P (R))
/* The hard register named %b[N], 0 <= N < 64.  */
#define E2K_ROT_REGNO(N) ((N) < 8 ? B0_REGNUM + (N) : B8_REGNUM + (N) - 8)
#define E2K_ROT_MAX 64
#define PRED_REGNO_P(R) ((unsigned) ((R) - PRED0_REGNUM) < 32)
#define CTPR_REGNO_P(R) ((unsigned) ((R) - CTPR1_REGNUM) < 3)

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
  "%b[57]", "%b[58]", "%b[59]", "%b[60]", "%b[61]", "%b[62]", "%b[63]" }

/* %g13 is the thread pointer.  %g24..%g31 can rotate (abg), and lcc
   assumes their base may change, so they are left alone.  */
#define FIXED_REGISTERS {						\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 1, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  1, 1, 1, 1, 1, 1, 1, 1,			\
  0, 0, 0, 0, 0, 0, 0, 0,  1, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,						\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  1, 1, 1, 1, 1,	\
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,	\
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 }

/* Globals, the outgoing registers and the CTPRs are clobbered by calls.
   Window registers and predicates are saved by the hardware.  */
#define CALL_REALLY_USED_REGISTERS {					\
  1, 1, 1, 1, 1, 1, 1, 1,  1, 1, 1, 1, 1, 0, 1, 1,			\
  1, 1, 1, 1, 1, 1, 1, 1,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  1, 1, 1, 1, 1, 1, 1, 1,						\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,			\
  1, 1, 1, 0, 0,	\
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,	\
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 }

/* Globals first (they don't grow the window), then window registers
   from the bottom up so the window stays small (every window has at
   least the four pairs %r0..%r7), then the outgoing registers.  */
#define REG_ALLOC_ORDER {						\
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 14, 15, 16, 17, 18, 19, 20, 21,	\
  22, 23, 11, 12,							\
  32, 33, 34, 35, 36, 37, 38, 39,					\
  41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56,	\
  57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72,	\
  73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88,	\
  89, 90, 91, 92, 93, 94, 95,						\
  96, 97, 98, 99, 100, 101, 102, 103,					\
  104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,	\
  117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129,	\
  130, 131, 132, 133, 134, 135,						\
  13, 24, 25, 26, 27, 28, 29, 30, 31, 40, 136, 137, 138, 139, 140,	\
  141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168,	\
  169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196 }

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
{ { 0, 0, 0, 0, 0, 0, 0 },						\
  { 0, 0, 0, 0, 0x700, 0, 0 },						\
  { 0, 0, 0, 0xffffff00, 0xff, 0, 0 },					\
  { 0, 0, 0, 0xff, 0, 0, 0 },						\
  { 0, 0xffffffff, 0xffffffff, 0, 0, 0, 0 },				\
  { 0xffffffff, 0xffffffff, 0xffffffff, 0xff, 0xfffff800,		\
    0xffffffff, 0x1f },							\
  { 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,	\
    0xffffffff, 0x1f } }

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
  e2k_init_cumulative_args (&(CUM), (FNTYPE), (LIBNAME), (FNDECL), false)
#define INIT_CUMULATIVE_INCOMING_ARGS(CUM, FNTYPE, LIBNAME)		\
  e2k_init_cumulative_args (&(CUM), (FNTYPE), (LIBNAME), NULL_TREE, true)

#define FUNCTION_ARG_REGNO_P(R)						\
  (((R) >= R0_REGNUM && (R) < R0_REGNUM + 8) || B_REGNO_P (R))

/* The caller's %b[i] is the callee's %r<i>.  */
#define INCOMING_REGNO(OUT)						\
  (B_REGNO_P (OUT) ? (OUT) - B0_REGNUM + R0_REGNUM : (OUT))
#define OUTGOING_REGNO(IN)						\
  ((IN) >= R0_REGNUM && (IN) < R0_REGNUM + 8				\
   ? (IN) - R0_REGNUM + B0_REGNUM : (IN))
/* Window registers and predicates: the hardware gives each call its own
   and keeps the caller's (registers.md), so a function needn't save
   them and they are not live at its end.  */
#define LOCAL_REGNO(R) (W_REGNO_P (R) || PRED_REGNO_P (R))
/* Keep register renaming out of the outgoing registers: values there
   block software pipelining (setbn renames them), and the window has
   room.  */
#define HARD_REGNO_RENAME_OK(FROM, TO) (!B_REGNO_P (TO))

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
#define TRAMPOLINE_SIZE 64
#define TRAMPOLINE_ALIGNMENT 64

#define CLZ_DEFINED_VALUE_AT_ZERO(MODE, VALUE)				\
  ((VALUE) = GET_MODE_BITSIZE (MODE), 2)

/* PIC: the GOT address is recomputed in each function (rrd %ip plus a
   PC-relative literal); it lives in a pseudo.  */
#define PIC_OFFSET_TABLE_REGNUM INVALID_REGNUM

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
   The spec gives globals no number, but GCC needs one for every
   register that can hold a variable; 128-159 is this port's guess
   (MCST's gdb maps nothing above 127).  */
#define DEBUGGER_REGNO(R)						\
  (W_REGNO_P (R) ? (R) - R0_REGNUM					\
   : B_REGNO_P (R) ? (R) - B0_REGNUM + 64				\
   : BX_REGNO_P (R) ? (R) - B8_REGNUM + 72				\
   : G_REGNO_P (R) ? (R) + 128 : INVALID_REGNUM)

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

#endif /* GCC_E2K_H */
