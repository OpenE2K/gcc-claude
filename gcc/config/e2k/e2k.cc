/* Subroutines for the Elbrus (E2K) port, 64-bit Linux: the target
   hooks, and what belongs to no other file (options, register modes,
   addresses and constants, costs, operand printing, types).  The other
   files are listed in STATUS.claude.md, "Source files".
   Written by Claude (Anthropic) as an experiment, from the relcc2
   specification (spec/isa, spec/abi); see README.claude.  This code
   is not intended for contribution to GCC.

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

#define IN_TARGET_CODE 1

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "target.h"
#include "rtl.h"
#include "tree.h"
#include "stringpool.h"
#include "attribs.h"
#include "df.h"
#include "regs.h"
#include "memmodel.h"
#include "emit-rtl.h"
#include "diagnostic-core.h"
#include "output.h"
#include "stor-layout.h"
#include "varasm.h"
#include "calls.h"
#include "expr.h"
#include "builtins.h"
#include "optabs.h"
#include "explow.h"
#include "cfgrtl.h"
#include "cfghooks.h"
#include "cfganal.h"
#include "cfgbuild.h"
#include "ifcvt.h"
#include "alias.h"
#include "targhooks.h"
#include "langhooks.h"
#include "insn-config.h"
#include "insn-attr.h"
#include "recog.h"
#include "tm_p.h"
#include "tm-constrs.h"
#include "sched-int.h"
#include "rtl-iter.h"
#include "tree-pass.h"
#include "function-abi.h"
#include "print-tree.h"
#include "fold-const.h"
#include "gimple-expr.h"
#include "cfgloop.h"
#include "hw-doloop.h"
#include "opts.h"
#include "context.h"
#include "predict.h"
#include "gimple.h"
#include "ssa.h"
#include "gimple-iterator.h"
#include "gimplify-me.h"
#include "tree-data-ref.h"
#include "tree-scalar-evolution.h"
#include "tree-ssa-loop-manip.h"
#include "tree-ssa-loop-ivopts.h"
#include "tree-ssa-loop.h"
#include "tree-ssa-loop-niter.h"
#include "gimple-fold.h"
#include "tree-affine.h"
#include "tree-into-ssa.h"
#include "cfgloopmanip.h"
#include "tree-pretty-print.h"
#include "tree-cfg.h"
#include "tree-cfgcleanup.h"
#include "tree-dfa.h"
#include "tree-eh.h"

/* This file should be included last.  */
#include "e2k-internal.h"
#include "target-def.h"

static struct machine_function *
e2k_init_machine_status (void)
{
  machine_function *m = ggc_cleared_alloc<machine_function> ();
  m->apb_big = -1;
  return m;
}

/* ADJUST_REG_ALLOC_ORDER: at -O0 and -Og, the window registers and the
   outgoing ones before the globals %g16-%g31, which no DWARF number
   names (MCST's gdb maps only %r0-%r63 and %b[0]-%b[63]), so a variable
   kept in one has no location: a pr36728.c local aligned beyond the
   stack, reached through a pointer in %g16, had none even at -O0.  The
   window grows instead.  Otherwise REG_ALLOC_ORDER as it is.  */
void
e2k_adjust_reg_alloc_order (void)
{
  static const int order[] = REG_ALLOC_ORDER;
  const unsigned n = ARRAY_SIZE (order);
  unsigned k = 0;
  if (optimize && !optimize_debug)
    memcpy (reg_alloc_order, order, sizeof order);
  else
    {
      for (unsigned i = 0; i < n; i++)
	if (!IN_RANGE (order[i], 16, 31))
	  reg_alloc_order[k++] = order[i];
      for (unsigned i = 0; i < n; i++)
	if (IN_RANGE (order[i], 16, 31))
	  reg_alloc_order[k++] = order[i];
    }
  /* init_reg_sets_1 inverted the order before this.  */
  for (k = 0; k < n; k++)
    inv_reg_alloc_order[reg_alloc_order[k]] = k;
}

static void
e2k_option_override (void)
{
  init_machine_status = e2k_init_machine_status;

  static bool passes_done;
  if (!passes_done)
    {
      passes_done = true;
      struct register_pass_info info
	= { make_pass_e2k_alias_version (g, false), "vect", 1,
	    PASS_POS_INSERT_AFTER };
      register_pass (&info);
      struct register_pass_info vlinfo
	= { make_pass_e2k_vect_mark (g, false), "vect", 1,
	    PASS_POS_INSERT_BEFORE };
      register_pass (&vlinfo);
      struct register_pass_info vhinfo
	= { make_pass_e2k_vect_mark (g, true), "vect", 1,
	    PASS_POS_INSERT_AFTER };
      register_pass (&vhinfo);
      struct register_pass_info vinfo
	= { make_pass_e2k_alias_version (g, true), "slp", 1,
	    PASS_POS_INSERT_AFTER };
      register_pass (&vinfo);
      struct register_pass_info binfo
	= { make_pass_e2k_block_version (g), "store-merging", 1,
	    PASS_POS_INSERT_AFTER };
      register_pass (&binfo);
      struct register_pass_info zinfo
	= { make_pass_e2k_dbl_zext (g), "ree", 1, PASS_POS_INSERT_AFTER };
      register_pass (&zinfo);
      struct register_pass_info winfo
	= { make_pass_e2k_dbl_widen (g), "combine", 1,
	    PASS_POS_INSERT_AFTER };
      register_pass (&winfo);
      struct register_pass_info hinfo
	= { make_pass_e2k_addr_height (g), "combine", 1,
	    PASS_POS_INSERT_AFTER };
      register_pass (&hinfo);
      struct register_pass_info linfo
	= { make_pass_e2k_latch_copies (g), "loop2_invariant", 1,
	    PASS_POS_INSERT_AFTER };
      register_pass (&linfo);
      struct register_pass_info ninfo
	= { make_pass_e2k_narrow_ext (g), "ree", 1, PASS_POS_INSERT_AFTER };
      register_pass (&ninfo);
    }

  /* A select of two loads stays two loads (run speculatively, then
     merged: e2k_unpredicate_loads), not one load from a selected address
     waiting for the condition (7-Zip's and xz's binary-tree match
     finders: the next node's load waited for a compare that waited for
     a cache miss).  */
  SET_OPTION_IF_UNSET (&global_options, &global_options_set,
		       param_phiopt_factor_loads, 0);

  if (e2k_ptr32)
    error ("%<-mptr32%> (32-bit mode) is not supported: this compiler "
	   "generates 64-bit code only");
  if (e2k_ptr128)
    error ("%<-mptr128%> (protected mode) is not supported: this compiler "
	   "generates 64-bit code only");

  /* -mtune names a CPU and with it the ISA version, over -march (lcc,
     spec/abi/source-compat.md); gas gets -mcpu=<cpu> (linux.h).  */
  if (e2k_tune == 4)
    e2k_arch = 3;
  else if (e2k_tune == 6 || e2k_tune == 7)
    e2k_arch = 4;
  else if (e2k_tune == 8)
    e2k_arch = 5;
  else if (e2k_tune >= 9 && e2k_tune <= 11)
    e2k_arch = 6;
  else if (e2k_tune == 12 || e2k_tune == 13)
    e2k_arch = 7;
  /* With 16-byte vectors (v5 and later, -mvect128 by default) the
     vectorizer's costs are the pipeliner's II (e2k_vector_costs): GCC's
     very cheap model at -O2, which takes no loop that needs a runtime
     check, peeling or an epilogue, would vectorize next to nothing
     (PolyBench on the 8C2: gemm 1.59 times as fast, jacobi-1d 1.65,
     with the dynamic one).  */
  if (e2k_vect128 && e2k_arch >= 5)
    SET_OPTION_IF_UNSET (&global_options, &global_options_set,
			 flag_vect_cost_model, VECT_COST_MODEL_DYNAMIC);
  /* The latencies are v3's up to v5 and changed on v6 (spec/isa/timing.md,
     "Elbrus-2C3 (v6)"); v7 has none measured and takes v6's.  The ISA
     version stays what decides encodings, channels and the APB and loop
     rules, which every CPU that runs the code must obey.  */
  if (e2k_lat == 0)
    e2k_lat = e2k_arch >= 6 ? 6 : 3;
  /* A gather read as far as an L2 hit, plus the slack an L1 load has:
     L2 takes 11 cycles up to v5, 13 on v6 (NPB CG.W: 12 best on the
     8C2, 16 on the 2C3).  */
  if (!OPTION_SET_P (e2k_ms_gather_far))
    e2k_ms_gather_far = e2k_lat == 6 ? 16 : 12;

  /* v6 fuses a * b + c, rounded once.  lcc does that only under
     -ffp-contract=fast or -ffast-math (relcc2 findings P40), not by
     GCC's default for GNU C, and never in a reduction, where the add
     (4 cycles) is the recurrence and an fma (5) would lengthen it.  */
  if (e2k_arch >= 6)
    {
      if (!OPTION_SET_P (flag_fp_contract_mode)
	  && !flag_unsafe_math_optimizations)
	flag_fp_contract_mode = FP_CONTRACT_OFF;
      SET_OPTION_IF_UNSET (&global_options, &global_options_set,
			   param_avoid_fma_max_bits, 64);
    }

  /* 64-bit DWARF, lcc's default (lcc 1.28's changelog, -gdwarf64;
     spec/abi/stack-and-unwinding.md, "Debug information"): with 32-bit
     offsets the .debug_info, .debug_str, .debug_line and other sections
     of one program can't pass 4 GiB, and ld stops with relocations
     truncated to fit.  */
  if (!OPTION_SET_P (dwarf_offset_size))
    dwarf_offset_size = 8;

  /* -Og: no modulo scheduling.  Its kernel runs several iterations at
     once, so a loop's variables have no one value in it.  */
  if (optimize_debug && !OPTION_SET_P (e2k_pipeline))
    e2k_pipeline = 0;
  /* Nor renaming for speculation: at -Og a line's operations stay after
     the line before, so the renamed values (in free registers, often
     %g16-%g31, which no DWARF number names) mostly bought copies back
     (sets 1-3: 258,291 wide instructions with it, 253,626 without).  */
  if (optimize_debug && !OPTION_SET_P (e2k_spec_rename_p))
    e2k_spec_rename_p = 0;

  /* With -g but no unwind tables, GCC has gas build a .debug_frame from
     the .cfi directives.  MCST's gdb reads no CFI (e2k_debug_unwind_info)
     and lcc writes none; our CFI's return column is fictional.  GCC's
     own CFI, which gives DW_AT_frame_base, needs no directives.  */
  if (!OPTION_SET_P (flag_dwarf2_cfi_asm)
      && !flag_exceptions && !flag_unwind_tables
      && !flag_asynchronous_unwind_tables && !flag_non_call_exceptions)
    flag_dwarf2_cfi_asm = 0;

  /* -funroll-loops is on at -O2 (e2k-common.cc); factors 2, 4 and 8 gave
     the same CoreMark and Linpack speed on the 4C, so keep the code
     smaller.  */
  SET_OPTION_IF_UNSET (&global_options, &global_options_set,
		       param_max_unroll_times, 4);

  /* Inline more than GCC's -O2 default (15): a call costs a window
     switch and prepared transfers, and larger functions give the
     scheduler more to pack.  CoreMark on the 8C2: 3,012 -> 3,310 it/s
     at 100 (CoreMark's state machine is inlined, as lcc does); 200 or
     more, or a larger inline-unit-growth, gained nothing more.  */
  if (optimize >= 2 && !optimize_size)
    SET_OPTION_IF_UNSET (&global_options, &global_options_set,
			 param_max_inline_insns_auto, 100);

  /* sched-ebb extends a superblock only through a fall-through at least
     this likely (GCC's 50 without a profile): loads and ALU operations
     move above a branch at no cost here (",sm", e2k_spec_kind), so let
     them move above unlikely ones too.  GCC guesses "if (a != b)
     return" taken, which ended an EBB at every step of bzip2's mainGtU.
     8C2: zlib -9 2.24 -> 2.17 s, bzip2 -9 2.50 -> 2.35 s.  */
  SET_OPTION_IF_UNSET (&global_options, &global_options_set,
		       param_tracer_min_branch_probability, 10);
}

/* ------------------------------------------------------------------ */
/* Registers                                                           */
/* ------------------------------------------------------------------ */

/* Two consecutive GCC register numbers name adjacent hardware registers
   only inside one of the three files.  */
static bool
e2k_same_file_p (unsigned a, unsigned b)
{
  return (G_REGNO_P (a) && G_REGNO_P (b))
	 || (W_REGNO_P (a) && W_REGNO_P (b))
	 || (B_REGNO_P (a) && B_REGNO_P (b));
}

static bool
e2k_hard_regno_mode_ok (unsigned int regno, machine_mode mode)
{
  if (PRED_REGNO_P (regno))
    return mode == BImode;
  if (CTPR_REGNO_P (regno))
    return mode == DImode;
  if (regno == SFP_REGNUM || regno == AP_REGNUM)
    return mode == Pmode;
  if (mode == BImode)
    return false;
  if (COMPLEX_MODE_P (mode))
    return false;
  /* 64-bit vectors (e2k-vect.md) in any register, as DImode; 16-byte
     ones on v5+ in one register of the general ones (its extended part
     holds the high half).  */
  if (VECTOR_MODE_P (mode))
    return (GET_MODE_SIZE (mode) == 8
	    || (e2k_v16_mode_p (mode) && GPR_REGNO_P (regno)));

  unsigned size = GET_MODE_SIZE (mode);
  if (size <= 8)
    return true;
  /* 16-byte values take an even-aligned pair, as inline asm "r" operands
     do in lcc (spec/abi/source-compat.md) and as argument slots are.  */
  if (size == 16)
    return e2k_same_file_p (regno, regno + 1)
	   && (G_REGNO_P (regno) ? regno % 2 == 0
	       : W_REGNO_P (regno) ? (regno - R0_REGNUM) % 2 == 0
	       : (regno - B0_REGNUM) % 2 == 0);
  return false;
}

static unsigned int
e2k_hard_regno_nregs (unsigned int regno, machine_mode mode)
{
  if (PRED_REGNO_P (regno) || CTPR_REGNO_P (regno) || e2k_v16_mode_p (mode))
    return 1;
  return CEIL (GET_MODE_SIZE (mode), UNITS_PER_WORD);
}

/* HARD_REGNO_CALLER_SAVE_MODE: save a value that lives across a call
   (LRA's split around the call) in its own mode, as LoongArch and SPARC
   do.  The default, choose_hard_reg_mode, picks the widest mode the
   register holds, a 16-byte vector mode on v5+, so every value was saved
   with stqp and restored with ldqp.  The stqp also stores the register's
   high half, which a 64-bit or narrower value leaves undefined: a call's
   window may bring it back with another frame's bits and tags (an
   nfx = 1 frame spilled and refilled at a context switch or a signal
   handler loses its high halves, spec/abi/registers.md, "nfx"), and when
   they are diagnostic (tag 1, bit 30) the stqp, which is not speculative,
   is SIGILL ILL_ILLOPN (spec/isa/speculation.md, "Diagnostic values":
   store data).  pcre2test's process_data, saving a pointer in %b[5]
   around the malloc of the DFA workspace, died so on the 8C2 at
   "stqp,5 %dr8, 0xe0, %qpb[5]" with the high half 0x4afafafa4afafaf8,
   tags 1/1: in 3 full test-suite runs of 200 next to a GCC bootstrap, and
   in 140 test-14 runs of 2,000 under a 50 us timer signal.  The value's
   own mode reads only its bits: an SImode value saved as DImode under
   dbl = 0 would store an upper half that may be diagnostic too
   (spec/abi/registers.md, "dbl").  An ldd from L1 is also faster than an
   ldqp, which the 8C2 serves from L2.  VOIDmode is caller-save.cc's table
   for reload, which LRA doesn't use; it keeps the default.  */
machine_mode
e2k_hard_regno_caller_save_mode (unsigned int regno, unsigned int nregs,
				 machine_mode mode)
{
  if (mode == VOIDmode)
    return choose_hard_reg_mode (regno, nregs, NULL);
  return mode;
}

static bool
e2k_modes_tieable_p (machine_mode m1, machine_mode m2)
{
  if (m1 == m2)
    return true;
  if (m1 == BImode || m2 == BImode)
    return false;
  if (e2k_v16_mode_p (m1) || e2k_v16_mode_p (m2))
    return e2k_v16_mode_p (m1) && e2k_v16_mode_p (m2);
  return (GET_MODE_SIZE (m1) <= 8
	  && GET_MODE_SIZE (m2) <= 8);
}

/* A 16-byte vector in one register (v5+) and a value in a pair or a
   narrower one lay out their bits differently: no subregs between
   them.  */
static bool
e2k_can_change_mode_class (machine_mode from, machine_mode to, reg_class_t)
{
  if (e2k_v16_mode_p (from) || e2k_v16_mode_p (to))
    return e2k_v16_mode_p (from) && e2k_v16_mode_p (to);
  return true;
}

/* A 16-byte vector is one register's worth (v5+).  */
static poly_uint64
e2k_regmode_natural_size (machine_mode mode)
{
  return e2k_v16_mode_p (mode) ? 16 : UNITS_PER_WORD;
}

/* ------------------------------------------------------------------ */
/* Addresses and constants                                             */
/* ------------------------------------------------------------------ */

bool
e2k_tls_symbol_p (rtx x)
{
  return GET_CODE (x) == SYMBOL_REF && SYMBOL_REF_TLS_MODEL (x) != 0;
}

bool
e2k_tls_referenced_p (rtx x)
{
  if (!targetm.have_tls)
    return false;
  subrtx_var_iterator::array_type array;
  FOR_EACH_SUBRTX_VAR (iter, array, x, ALL)
    if (e2k_tls_symbol_p (*iter))
      return true;
  return false;
}

bool
e2k_symbolic_operand_p (rtx x)
{
  switch (GET_CODE (x))
    {
    case SYMBOL_REF:
    case LABEL_REF:
      return true;
    case CONST:
      x = XEXP (x, 0);
      return (GET_CODE (x) == PLUS
	      && (GET_CODE (XEXP (x, 0)) == SYMBOL_REF
		  || GET_CODE (XEXP (x, 0)) == LABEL_REF)
	      && CONST_INT_P (XEXP (x, 1)));
    default:
      return false;
    }
}

bool
e2k_legitimate_constant_p (machine_mode, rtx x)
{
  switch (GET_CODE (x))
    {
    case CONST_INT:
    case CONST_DOUBLE:
    case CONST_WIDE_INT:
      return true;
    case CONST_VECTOR:
      return GET_MODE_SIZE (GET_MODE (x)) == 8;
    case SYMBOL_REF:
    case LABEL_REF:
    case CONST:
      if (e2k_tls_referenced_p (x))
	return false;
      if (flag_pic)
	return false;
      return e2k_symbolic_operand_p (x);
    case HIGH:
    default:
      return false;
    }
}

static bool
e2k_legitimate_constant_hook (machine_mode mode, rtx x)
{
  return e2k_legitimate_constant_p (mode, x);
}

static bool
e2k_cannot_force_const_mem (machine_mode, rtx x)
{
  return e2k_tls_referenced_p (x) || flag_pic;
}

static bool
e2k_base_reg_p (rtx x, bool strict)
{
  if (!REG_P (x))
    return false;
  unsigned regno = REGNO (x);
  if (strict)
    return REGNO_OK_FOR_BASE_P (regno);
  return regno >= FIRST_PSEUDO_REGISTER || GPR_REGNO_P (regno)
	 || regno == SFP_REGNUM || regno == AP_REGNUM;
}

bool
e2k_reloc_unspec_p (rtx x)
{
  return (GET_CODE (x) == UNSPEC
	  && (XINT (x, 1) == UNSPEC_GOT || XINT (x, 1) == UNSPEC_TLS_IE
	      || XINT (x, 1) == UNSPEC_TLS_GDMOD
	      || XINT (x, 1) == UNSPEC_TLS_GDREL
	      || XINT (x, 1) == UNSPEC_TLS_LE
	      || XINT (x, 1) == UNSPEC_GOTOFF));
}

/* Addresses are SRC1 + SRC2: a register plus a register or a literal
   of up to 64 bits, or a literal alone (spec/isa/bundle.md; loads take
   ALOPF1 operands).  */
bool
e2k_legitimate_address_p (machine_mode mode, rtx x, bool strict)
{
  /* 16-byte values are split into two accesses at +0 and +8.  */
  bool pair = GET_MODE_SIZE (mode) > 8;

  if (e2k_base_reg_p (x, strict))
    return true;
  if (GET_CODE (x) == PLUS)
    {
      rtx a = XEXP (x, 0), b = XEXP (x, 1);
      if (!e2k_base_reg_p (a, strict))
	return false;
      if (CONST_INT_P (b))
	return true;
      if (pair)
	return false;
      if (e2k_base_reg_p (b, strict))
	return true;
      if (e2k_reloc_unspec_p (b))
	return true;
      if (!flag_pic && e2k_symbolic_operand_p (b) && !e2k_tls_referenced_p (b))
	return true;
      return false;
    }
  if (!flag_pic && e2k_symbolic_operand_p (x) && !e2k_tls_referenced_p (x))
    return true;
  return false;
}

static bool
e2k_legitimate_address_hook (machine_mode mode, rtx x, bool strict,
			     code_helper = ERROR_MARK)
{
  return e2k_legitimate_address_p (mode, x, strict);
}

/* ------------------------------------------------------------------ */
/* Costs                                                               */
/* ------------------------------------------------------------------ */

static bool e2k_symbolic_address_p (rtx);

static bool
e2k_rtx_costs (rtx x, machine_mode mode, int outer, int, int *total, bool)
{
  int code = GET_CODE (x);
  switch (code)
    {
    case CONST_INT:
      *total = (INTVAL (x) >= 0 && INTVAL (x) < 16) ? 0 : 1;
      return true;
    case CONST:
    case SYMBOL_REF:
    case LABEL_REF:
      *total = flag_pic ? COSTS_N_INSNS (2) : 1;
      return true;
    case CONST_DOUBLE:
    case CONST_VECTOR:
      *total = 1;
      return true;
    case MEM:
      *total = COSTS_N_INSNS (3);
      /* A symbol in the address is a 64-bit literal, half a wide
	 instruction's literal syllables: dearer than a register holding
	 it.  */
      if (e2k_symbolic_address_p (XEXP (x, 0)))
	*total += COSTS_N_INSNS (1);
      return outer != SET;
    case MULT:
      *total = COSTS_N_INSNS (FLOAT_MODE_P (mode) ? 4 : 4);
      return false;
    case TRUNCATE:
      /* The high half of a product (expmed's division by a constant):
	 smulhd/umulhd, or smulx/umulx and a shift, 4 cycles; costed by
	 parts, its double-width shift and extensions looked as dear as
	 a division.  */
      if (GET_CODE (XEXP (x, 0)) == LSHIFTRT
	  && GET_CODE (XEXP (XEXP (x, 0), 0)) == MULT)
	{
	  *total = COSTS_N_INSNS (4);
	  return true;
	}
      return false;
    case DIV:
    case UDIV:
    case MOD:
    case UMOD:
      if (!FLOAT_MODE_P (mode) && CONST_INT_P (XEXP (x, 1))
	  && INTVAL (XEXP (x, 1)) != 0)
	{
	  /* By a constant, what expand_divmod emits: shifts for a power of
	     two, else a high-part multiply and shifts, and for a remainder
	     a multiply and a subtract more.  Loop trip counts such as
	     (len - 3) / 3 + 1 (zlib's inflate_fast copy) stay cheap enough
	     for a hardware loop (doloop's 10 instructions).  */
	  bool rem = GET_CODE (x) == MOD || GET_CODE (x) == UMOD;
	  bool uns = GET_CODE (x) == UDIV || GET_CODE (x) == UMOD;
	  if (pow2p_hwi (absu_hwi (INTVAL (XEXP (x, 1)))))
	    *total = COSTS_N_INSNS (uns ? 1 : rem ? 4 : 3);
	  else
	    *total = COSTS_N_INSNS (rem ? 11 : 6);
	  return false;
	}
      if (GET_CODE (x) == MOD || GET_CODE (x) == UMOD)
	{
	  /* No remainder operation (smodx/umodx divide 64 bits by 32 into
	     32): a divide, a multiply and a subtract.  */
	  *total = COSTS_N_INSNS (21);
	  return false;
	}
      /* An integer divide takes 13-19 cycles by the quotient's size, in
	 the one divider ALC5's divides share (spec/isa/timing.md,
	 "Divider"; findings I24).  16, so that expand_divmod divides by
	 constants with a high-part multiply, which it allows a remainder
	 only the divide's cost less a multiply and an add.  */
      *total = COSTS_N_INSNS (FLOAT_MODE_P (mode) ? 14 : 16);
      return false;
    case PLUS:
    case MINUS:
      *total = COSTS_N_INSNS (FLOAT_MODE_P (mode) ? 4 : 1);
      return false;
    case AND:
      /* v5's getfz: a scaled field in one operation (*getfz<mode>_lshr),
	 not a shift and an AND.  */
      if ((GET_CODE (XEXP (x, 0)) == LSHIFTRT
	   || GET_CODE (XEXP (x, 0)) == ASHIFT)
	  && REG_P (XEXP (XEXP (x, 0), 0))
	  && e2k_getfz_desc (mode, GET_CODE (XEXP (x, 0)) == LSHIFTRT,
			     XEXP (XEXP (x, 0), 1), XEXP (x, 1)) >= 0)
	{
	  *total = COSTS_N_INSNS (1);
	  return true;
	}
      return false;
    default:
      return false;
    }
}

/* Whether address X has a symbolic constant: a 64-bit literal, two of
   the four literal syllables of a wide instruction.  */
static bool
e2k_symbolic_address_p (rtx x)
{
  auto sym = [] (rtx y)
    {
      return (GET_CODE (y) == SYMBOL_REF || GET_CODE (y) == LABEL_REF
	      || GET_CODE (y) == CONST);
    };
  return (sym (x)
	  || (GET_CODE (x) == PLUS && (sym (XEXP (x, 0)) || sym (XEXP (x, 1)))));
}

static int
e2k_address_cost (rtx x, machine_mode, addr_space_t, bool)
{
  return e2k_symbolic_address_p (x) ? 2 : 0;
}

static int
e2k_memory_move_cost (machine_mode, reg_class_t, bool)
{
  return 6;
}

static int
e2k_register_move_cost (machine_mode, reg_class_t from, reg_class_t to)
{
  if (from == PRED_REGS || to == PRED_REGS)
    return 20;
  return 2;
}

/* ------------------------------------------------------------------ */
/* Assembler output                                                    */
/* ------------------------------------------------------------------ */

bool e2k_bundling;	/* bundle marks are valid for this function */
bool e2k_in_bundle;

static void
e2k_print_reg (FILE *f, int regno)
{
  fputs (reg_names[regno], f);
}

static const char *
e2k_cmp_suffix (rtx op)
{
  machine_mode mode = GET_MODE (XEXP (op, 0));
  bool fp = FLOAT_MODE_P (mode);
  switch (GET_CODE (op))
    {
    case EQ: return fp ? "eq" : "e";
    case NE: return "neq";
    case LT: return fp ? "lt" : "l";
    case LE: return "le";
    case LTU: return "b";
    case LEU: return "be";
    case UNORDERED: return "uod";
    case ORDERED: return "od";
    default: gcc_unreachable ();
    }
}

static void
e2k_print_const (FILE *f, rtx x)
{
  /* A vector constant is its 64-bit image.  */
  if (GET_CODE (x) == CONST_VECTOR)
    x = simplify_subreg (DImode, x, GET_MODE (x), 0);
  if (CONST_INT_P (x))
    fprintf (f, HOST_WIDE_INT_PRINT_DEC, INTVAL (x));
  else if (CONST_DOUBLE_P (x) && GET_MODE (x) == SFmode)
    {
      long l;
      REAL_VALUE_TO_TARGET_SINGLE (*CONST_DOUBLE_REAL_VALUE (x), l);
      fprintf (f, "0x%08lx", l & 0xffffffffUL);
    }
  else if (CONST_DOUBLE_P (x) && GET_MODE (x) == DFmode)
    {
      long l[2];
      REAL_VALUE_TO_TARGET_DOUBLE (*CONST_DOUBLE_REAL_VALUE (x), l);
      fprintf (f, "0x%08lx%08lx", l[1] & 0xffffffffUL, l[0] & 0xffffffffUL);
    }
  else
    output_addr_const (f, x);
}

static void
e2k_print_reloc (FILE *f, rtx x)
{
  output_addr_const (f, XVECEXP (x, 0, 0));
  switch (XINT (x, 1))
    {
    case UNSPEC_GOT: fputs ("@GOT", f); break;
    case UNSPEC_GOTOFF: fputs ("@GOTOFF", f); break;
    case UNSPEC_TLS_IE: fputs ("@TLS_IE", f); break;
    case UNSPEC_TLS_LE: fputs ("@TLS_LE", f); break;
    case UNSPEC_TLS_GDMOD: fputs ("@TLS_GDMOD", f); break;
    case UNSPEC_TLS_GDREL: fputs ("@TLS_GDREL", f); break;
    default: gcc_unreachable ();
    }
}

/* Addresses print as "src1, src2".  */
static void
e2k_print_operand_address (FILE *f, machine_mode, rtx x)
{
  if (REG_P (x))
    {
      e2k_print_reg (f, REGNO (x));
      fputs (", 0x0", f);
      return;
    }
  if (GET_CODE (x) == PLUS)
    {
      rtx a = XEXP (x, 0), b = XEXP (x, 1);
      e2k_print_reg (f, REGNO (a));
      fputs (", ", f);
      if (REG_P (b))
	e2k_print_reg (f, REGNO (b));
      else if (GET_CODE (b) == UNSPEC)
	e2k_print_reloc (f, b);
      else
	e2k_print_const (f, b);
      return;
    }
  fputs ("0x0, ", f);
  output_addr_const (f, x);
}
/* Whether the insn being printed takes ",sm" (a pipelined loop's, or one
   moved above a branch).  */
bool e2k_cur_sm;

static void
e2k_print_operand (FILE *f, rtx x, int code)
{
  switch (code)
    {
    case ',':
      {
	/* After a mnemonic e2k_asm_output_opcode can't see whole.  */
	int chan = e2k_cur_chan ();
	if (chan >= 0)
	  fprintf (f, ",%d", chan);
	if (e2k_cur_sm)
	  fputs (",sm", f);
	return;
      }
    case '?':
      /* The condition of a predicated operation (define_cond_exec), at
	 the end of its line.  */
      if (current_output_insn && INSN_P (current_output_insn)
	  && GET_CODE (PATTERN (current_output_insn)) == COND_EXEC)
	{
	  rtx cond = COND_EXEC_TEST (PATTERN (current_output_insn));
	  fprintf (f, " ? %s%s", GET_CODE (cond) == EQ ? "~" : "",
		   reg_names[REGNO (XEXP (cond, 0))]);
	}
      return;
    case '#':
      /* In an asm, lcc's %#: the window base for a call the asm makes
	 ("call %%ctpr1, wbs = %#"; spec/abi/source-compat.md), whose
	 outgoing pairs e2k_compute_window then provides.  In the
	 port's templates a break between wide instructions.  */
      if (this_is_asm_operands)
	{
	  fprintf (f, "0x%x", e2k_window_base ());
	  return;
	}
      if (e2k_bundling)
	fputs ("\n\t}\n\t{\n\t", f);
      else
	fputs ("\n\t", f);
      return;
    case '<':
      if (!e2k_bundling)
	fputs ("{\n\t", f);
      return;
    case '>':
      if (!e2k_bundling)
	fputs ("\n\t}", f);
      return;
    case 'H':
      gcc_assert (REG_P (x));
      e2k_print_reg (f, REGNO (x) + 1);
      return;
    case 'K':
      fputs (e2k_cmp_suffix (x), f);
      return;
    case 'C':
      if (GET_CODE (x) == EQ)
	fputc ('~', f);
      return;
    case 'R':
      {
	static const char *const fp_state[] = { "pfpfr", "fpcr", "fpsr" };
	gcc_assert (CONST_INT_P (x) && IN_RANGE (INTVAL (x), 0, 2));
	fputs (fp_state[INTVAL (x)], f);
	return;
      }
    case 0:
      break;
    default:
      output_operand_lossage ("invalid operand code '%c'", code);
      return;
    }

  switch (GET_CODE (x))
    {
    case REG:
      e2k_print_reg (f, REGNO (x));
      break;
    case MEM:
      e2k_print_operand_address (f, GET_MODE (x), XEXP (x, 0));
      break;
    case UNSPEC:
      e2k_print_reloc (f, x);
      break;
    default:
      e2k_print_const (f, x);
      break;
    }
}

static bool
e2k_print_operand_punct_valid_p (unsigned char code)
{
  return (code == '#' || code == '<' || code == '>' || code == ','
	  || code == '?');
}

/* va_list is a plain pointer to the next argument slot (spec/abi/
   calling-convention.md), and a char * as in lcc: C++ names mangle it
   "Pc" there (Unipro's clang "Pv"), so "void f (va_list)" links with
   lcc's code only so.  GCC's generic va_start and va_arg handle it.  */
static tree
e2k_build_builtin_va_list (void)
{
  return build_pointer_type (char_type_node);
}

/* No decl for the stack protector's guard: stack_protect_set and
   stack_protect_test read glibc's at TP - 8 (e2k_ssp_guard).  */
static tree
e2k_stack_protect_guard (void)
{
  return NULL_TREE;
}

static void
e2k_asm_file_start (void)
{
  default_file_start ();
  fputs ("\t.ignore\tld_st_style\n\t.ignore\tstrict_delay\n", asm_out_file);
}

/* gas moves every label in code that could be a jump target out of
   offsets 0x1c0-0x1ff of each 1 KiB block with empty wide instructions,
   and raises the section's alignment to 1 KiB (MCSTBug #140436,
   spec/isa/hwbugs.md).  Before v7 the internal labels only debug or
   unwind information refers to are marked as never jumped to, so -g
   changes neither the code nor its sections: those of lines, blocks,
   inline entries and variable locations, a function's begin, end and
   second section and its frame changes (which code without unwind
   tables has only with -g) and the text sections' ends and first
   labels.  */
static const char *const e2k_debug_only_labels[] = {
  "LBB", "LBE", "LBI", "LVL", "LDL", "LM", "LFB", "LFE", "LFSB", "LCFI",
  "Ltext", "Ltext_cold", "Letext", "Letext_cold"
};

static bool
e2k_debug_only_label_p (const char *prefix, size_t len)
{
  if (e2k_arch >= 7)
    return false;
  for (const char *p : e2k_debug_only_labels)
    if (strlen (p) == len && strncmp (prefix, p, len) == 0)
      return true;
  return false;
}

/* NAME is an internal label's whole name.  */
static void
e2k_output_non_target_label (FILE *file, const char *name)
{
  fputs ("\t.non_target_label\t", file);
  assemble_name_raw (file, name);
  fputc ('\n', file);
}

/* An internal label: one only debug information refers to as above.  */
static void
e2k_asm_internal_label (FILE *file, const char *prefix,
			unsigned long labelno)
{
  if (e2k_debug_only_label_p (prefix, strlen (prefix)))
    {
      char *buf = (char *) alloca (40 + strlen (prefix));
      ASM_GENERATE_INTERNAL_LABEL (buf, prefix, labelno);
      e2k_output_non_target_label (file, buf);
      return;
    }
  default_internal_label (file, prefix, labelno);
}

/* ASM_OUTPUT_LABEL: the internal labels dwarf2out prints with it (a
   function's end and second section, the text sections' first labels)
   as above.  */
void
e2k_asm_output_label (FILE *file, const char *name)
{
  /* ASM_GENERATE_INTERNAL_LABEL's "*.<prefix><number>".  */
  char probe[8];
  ASM_GENERATE_INTERNAL_LABEL (probe, "", 0);
  size_t lead = strlen (probe) - 1;
  if (strncmp (name, probe, lead) == 0)
    {
      const char *prefix = name + lead;
      size_t len = strlen (prefix);
      while (len > 0 && ISDIGIT (prefix[len - 1]))
	len--;
      if (len < strlen (prefix) && e2k_debug_only_label_p (prefix, len))
	{
	  e2k_output_non_target_label (file, name);
	  return;
	}
    }
  assemble_name (file, name);
  fputs (":\n", file);
}

/* ------------------------------------------------------------------ */
/* Types                                                               */
/* ------------------------------------------------------------------ */

static machine_mode
e2k_c_mode_for_floating_type (enum tree_index ti)
{
  if (ti == TI_LONG_DOUBLE_TYPE)
    return XFmode;
  return default_mode_for_floating_type (ti);
}

static bool
e2k_scalar_mode_supported_p (scalar_mode mode)
{
  if (mode == XFmode || mode == TFmode)
    return true;
  return default_scalar_mode_supported_p (mode);
}

static bool
e2k_libgcc_floating_mode_supported_p (scalar_float_mode mode)
{
  return mode == SFmode || mode == DFmode || mode == XFmode
	 || mode == TFmode;
}

/* Whether INSN divides 64-bit integers (sdivd, udivd).  */
bool
e2k_div64_p (rtx_insn *insn)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
    if ((GET_CODE (*iter) == DIV || GET_CODE (*iter) == UDIV)
	&& GET_MODE (*iter) == DImode)
      return true;
  return false;
}

/* Bypass guard: predicate logic reaches a predicated operation in 1
   cycle (E2K_PRED1).  */
bool
e2k_pred1_p (rtx_insn *, rtx_insn *)
{
  return E2K_PRED1;
}

/* Bypass guard: whether OUT's result is only the addend of IN, a
   combined FP operation (a fmul_add, fmul_sub or fmul_rsub).  */
bool
e2k_fma_addend_p (rtx_insn *out, rtx_insn *in)
{
  rtx os = single_set (out), is = single_set (in);
  if (!os || !is || !REG_P (SET_DEST (os)))
    return false;
  rtx src = SET_SRC (is);
  if (GET_CODE (src) != PLUS && GET_CODE (src) != MINUS)
    return false;
  int m = GET_CODE (XEXP (src, 0)) == MULT ? 0 : 1;
  if (GET_CODE (XEXP (src, m)) != MULT)
    return false;
  return (reg_overlap_mentioned_p (SET_DEST (os), XEXP (src, 1 - m))
	  && !reg_overlap_mentioned_p (SET_DEST (os), XEXP (src, m)));
}

/* DEST (SFmode or DFmode) = unsigned DImode X: the signed conversion
   when the top bit is clear, else that of (x >> 1 | x & 1) doubled,
   which rounds alike (and is exact, setting no flag, whenever the
   direct conversion is).  */
void
e2k_expand_floatunsdi (rtx dest, rtx x)
{
  machine_mode fm = GET_MODE (dest);
  x = force_reg (DImode, x);
  rtx d1 = gen_reg_rtx (fm), d2 = gen_reg_rtx (fm);
  emit_insn (gen_rtx_SET (d1, gen_rtx_FLOAT (fm, x)));
  rtx h = expand_simple_binop (DImode, LSHIFTRT, x, const1_rtx, NULL_RTX, 1,
			       OPTAB_DIRECT);
  rtx b = expand_simple_binop (DImode, AND, x, const1_rtx, NULL_RTX, 1,
			       OPTAB_DIRECT);
  rtx t = expand_simple_binop (DImode, IOR, h, b, NULL_RTX, 1, OPTAB_DIRECT);
  emit_insn (gen_rtx_SET (d2, gen_rtx_FLOAT (fm, force_reg (DImode, t))));
  rtx d3 = expand_simple_binop (fm, PLUS, d2, d2, NULL_RTX, 0, OPTAB_DIRECT);
  emit_move_insn (dest, d1);
  rtx_code_label *done = gen_label_rtx ();
  emit_cmp_and_jump_insns (x, const0_rtx, GE, NULL_RTX, DImode, 0, done);
  emit_move_insn (dest, d3);
  emit_label (done);
}

/* Reassociation (tree-ssa-reassoc) builds trees this wide: six integer
   channels at 1 cycle, four FP ones at 4 (spec/isa/timing.md); lcc's
   sums are trees too.  */
static int
e2k_reassociation_width (tree_code, machine_mode mode)
{
  if (INTEGRAL_MODE_P (mode) || FLOAT_MODE_P (mode))
    return 4;
  return 1;
}

/* 1.0q is a __float128 constant, 1.0w a __float80 one, as on x86.  */
static machine_mode
e2k_c_mode_for_suffix (char suffix)
{
  if (suffix == 'q')
    return TFmode;
  if (suffix == 'w')
    return XFmode;
  return VOIDmode;
}

static const char *
e2k_mangle_type (const_tree type)
{
  if (TYPE_MAIN_VARIANT (type) == float128t_type_node)
    return "g";
  /* long double and __float80, the same type, are "e"; _Float64x, also
     XFmode, keeps the generic DF64x, as on x86 (lcc has no _FloatNx).  */
  if (TYPE_MAIN_VARIANT (type) == long_double_type_node)
    return "e";
  return NULL;
}

static void
e2k_trampoline_init (rtx, tree, rtx)
{
  sorry ("nested function trampolines are not supported by this E2K port");
}

/* ------------------------------------------------------------------ */
/* Target hooks                                                        */
/* ------------------------------------------------------------------ */

#undef TARGET_OPTION_OVERRIDE
#define TARGET_OPTION_OVERRIDE e2k_option_override

#undef TARGET_HARD_REGNO_MODE_OK
#define TARGET_HARD_REGNO_MODE_OK e2k_hard_regno_mode_ok
#undef TARGET_CAN_CHANGE_MODE_CLASS
#define TARGET_CAN_CHANGE_MODE_CLASS e2k_can_change_mode_class
#undef TARGET_REGMODE_NATURAL_SIZE
#define TARGET_REGMODE_NATURAL_SIZE e2k_regmode_natural_size
#undef TARGET_HARD_REGNO_NREGS
#define TARGET_HARD_REGNO_NREGS e2k_hard_regno_nregs
#undef TARGET_MODES_TIEABLE_P
#define TARGET_MODES_TIEABLE_P e2k_modes_tieable_p

#undef TARGET_SCHED_REASSOCIATION_WIDTH
#define TARGET_SCHED_REASSOCIATION_WIDTH e2k_reassociation_width
#undef TARGET_VECTOR_MODE_SUPPORTED_P
#define TARGET_VECTOR_MODE_SUPPORTED_P e2k_vector_mode_supported_p
#undef TARGET_VECTORIZE_PREFERRED_SIMD_MODE
#define TARGET_VECTORIZE_PREFERRED_SIMD_MODE e2k_preferred_simd_mode
#undef TARGET_VECTORIZE_VEC_PERM_CONST
#define TARGET_VECTORIZE_VEC_PERM_CONST e2k_vectorize_vec_perm_const
#undef TARGET_VECTORIZE_CREATE_COSTS
#define TARGET_VECTORIZE_CREATE_COSTS e2k_vectorize_create_costs
#undef TARGET_VECTORIZE_BUILTIN_VECTORIZATION_COST
#define TARGET_VECTORIZE_BUILTIN_VECTORIZATION_COST \
  e2k_builtin_vectorization_cost

#undef TARGET_LEGITIMATE_ADDRESS_P
#define TARGET_LEGITIMATE_ADDRESS_P e2k_legitimate_address_hook
#undef TARGET_LEGITIMATE_CONSTANT_P
#define TARGET_LEGITIMATE_CONSTANT_P e2k_legitimate_constant_hook
#undef TARGET_CANNOT_FORCE_CONST_MEM
#define TARGET_CANNOT_FORCE_CONST_MEM e2k_cannot_force_const_mem
#undef TARGET_LEGITIMIZE_ADDRESS
#define TARGET_LEGITIMIZE_ADDRESS e2k_legitimize_address
#undef TARGET_DELEGITIMIZE_ADDRESS
#define TARGET_DELEGITIMIZE_ADDRESS e2k_delegitimize_address

#undef TARGET_HAVE_TLS
#define TARGET_HAVE_TLS true
#undef TARGET_INIT_PIC_REG
#define TARGET_INIT_PIC_REG e2k_init_pic_reg
#undef TARGET_USE_PSEUDO_PIC_REG
#define TARGET_USE_PSEUDO_PIC_REG hook_bool_void_true

#undef TARGET_FUNCTION_ARG
#define TARGET_FUNCTION_ARG e2k_function_arg
#undef TARGET_FUNCTION_INCOMING_ARG
#define TARGET_FUNCTION_INCOMING_ARG e2k_function_incoming_arg
#undef TARGET_FUNCTION_ARG_ADVANCE
#define TARGET_FUNCTION_ARG_ADVANCE e2k_function_arg_advance
#undef TARGET_FUNCTION_ARG_BOUNDARY
#define TARGET_FUNCTION_ARG_BOUNDARY e2k_function_arg_boundary
#undef TARGET_STRICT_ARGUMENT_NAMING
#define TARGET_STRICT_ARGUMENT_NAMING e2k_strict_argument_naming
#undef TARGET_BUILD_BUILTIN_VA_LIST
#define TARGET_BUILD_BUILTIN_VA_LIST e2k_build_builtin_va_list
#undef TARGET_PROMOTE_FUNCTION_MODE
#define TARGET_PROMOTE_FUNCTION_MODE e2k_promote_function_mode
#undef TARGET_RETURN_IN_MEMORY
#define TARGET_RETURN_IN_MEMORY e2k_return_in_memory
#undef TARGET_FUNCTION_VALUE
#define TARGET_FUNCTION_VALUE e2k_function_value
#undef TARGET_LIBCALL_VALUE
#define TARGET_LIBCALL_VALUE e2k_libcall_value
#undef TARGET_FUNCTION_VALUE_REGNO_P
#define TARGET_FUNCTION_VALUE_REGNO_P e2k_function_value_regno_p
#undef TARGET_STRUCT_VALUE_RTX
#define TARGET_STRUCT_VALUE_RTX e2k_struct_value_rtx
#undef TARGET_FUNCTION_OK_FOR_SIBCALL
#define TARGET_FUNCTION_OK_FOR_SIBCALL e2k_function_ok_for_sibcall

#undef TARGET_STACK_PROTECT_GUARD
#define TARGET_STACK_PROTECT_GUARD e2k_stack_protect_guard
#undef TARGET_FRAME_POINTER_REQUIRED
#define TARGET_FRAME_POINTER_REQUIRED e2k_frame_pointer_required
#undef TARGET_CAN_ELIMINATE
#define TARGET_CAN_ELIMINATE e2k_can_eliminate

#undef TARGET_RTX_COSTS
#define TARGET_RTX_COSTS e2k_rtx_costs
#undef TARGET_ADDRESS_COST
#define TARGET_ADDRESS_COST e2k_address_cost
#undef TARGET_MEMORY_MOVE_COST
#define TARGET_MEMORY_MOVE_COST e2k_memory_move_cost
#undef TARGET_REGISTER_MOVE_COST
#define TARGET_REGISTER_MOVE_COST e2k_register_move_cost

#undef TARGET_PRINT_OPERAND
#define TARGET_PRINT_OPERAND e2k_print_operand
#undef TARGET_PRINT_OPERAND_ADDRESS
#define TARGET_PRINT_OPERAND_ADDRESS e2k_print_operand_address
#undef TARGET_PRINT_OPERAND_PUNCT_VALID_P
#define TARGET_PRINT_OPERAND_PUNCT_VALID_P e2k_print_operand_punct_valid_p
#undef TARGET_DEBUG_UNWIND_INFO
#define TARGET_DEBUG_UNWIND_INFO e2k_debug_unwind_info

#undef TARGET_MD_ASM_ADJUST
#define TARGET_MD_ASM_ADJUST e2k_md_asm_adjust

#undef TARGET_ASM_FILE_START
#define TARGET_ASM_FILE_START e2k_asm_file_start
#undef TARGET_ASM_INTERNAL_LABEL
#define TARGET_ASM_INTERNAL_LABEL e2k_asm_internal_label
#undef TARGET_SCHED_DEPENDENCIES_EVALUATION_HOOK
#define TARGET_SCHED_DEPENDENCIES_EVALUATION_HOOK e2k_spec_pin
#undef TARGET_SCHED_SET_SCHED_FLAGS
#define TARGET_SCHED_SET_SCHED_FLAGS e2k_set_sched_flags
#undef TARGET_SCHED_SPECULATE_INSN
#define TARGET_SCHED_SPECULATE_INSN e2k_speculate_insn
#undef TARGET_SCHED_NEEDS_BLOCK_P
#define TARGET_SCHED_NEEDS_BLOCK_P e2k_needs_block_p
#undef TARGET_SCHED_GEN_SPEC_CHECK
#define TARGET_SCHED_GEN_SPEC_CHECK e2k_gen_spec_check
#undef TARGET_SCHED_GET_INSN_SPEC_DS
#define TARGET_SCHED_GET_INSN_SPEC_DS e2k_get_insn_spec_ds
#undef TARGET_SCHED_GET_INSN_CHECKED_DS
#define TARGET_SCHED_GET_INSN_CHECKED_DS e2k_get_insn_spec_ds
#undef TARGET_CAN_USE_DOLOOP_P
#define TARGET_CAN_USE_DOLOOP_P e2k_can_use_doloop_p
#undef TARGET_LOOP_UNROLL_ADJUST
#define TARGET_LOOP_UNROLL_ADJUST e2k_loop_unroll_adjust
#undef TARGET_INVALID_WITHIN_DOLOOP
#define TARGET_INVALID_WITHIN_DOLOOP e2k_invalid_within_doloop
#undef TARGET_ASM_OUTPUT_MI_THUNK
#define TARGET_ASM_OUTPUT_MI_THUNK e2k_output_mi_thunk
#undef TARGET_ASM_CAN_OUTPUT_MI_THUNK
#define TARGET_ASM_CAN_OUTPUT_MI_THUNK hook_bool_const_tree_hwi_hwi_const_tree_true
#undef TARGET_ASM_FUNCTION_PROLOGUE
#define TARGET_ASM_FUNCTION_PROLOGUE e2k_asm_function_prologue
#undef TARGET_ASM_FUNCTION_EPILOGUE
#define TARGET_ASM_FUNCTION_EPILOGUE e2k_asm_function_epilogue
#undef TARGET_ASM_FINAL_POSTSCAN_INSN
#define TARGET_ASM_FINAL_POSTSCAN_INSN e2k_final_postscan_insn
#undef TARGET_ASM_ALIGNED_DI_OP
#define TARGET_ASM_ALIGNED_DI_OP "\t.dword\t"
#undef TARGET_ASM_UNALIGNED_DI_OP
#define TARGET_ASM_UNALIGNED_DI_OP "\t.dword\t"

/* Also makes the scheduler apply address replacements (moving a memory
   access across an increment of its base) only from the next cycle.  */
#undef TARGET_SCHED_EXPOSED_PIPELINE
#define TARGET_SCHED_EXPOSED_PIPELINE true
#undef TARGET_SCHED_ADJUST_COST
#define TARGET_SCHED_ADJUST_COST e2k_adjust_cost
#undef TARGET_SCHED_ISSUE_RATE
#define TARGET_SCHED_ISSUE_RATE e2k_issue_rate
#undef TARGET_SCHED_FIRST_CYCLE_MULTIPASS_DFA_LOOKAHEAD_GUARD
#define TARGET_SCHED_FIRST_CYCLE_MULTIPASS_DFA_LOOKAHEAD_GUARD e2k_lookahead_guard
#undef TARGET_SCHED_FIRST_CYCLE_MULTIPASS_DFA_LOOKAHEAD
#define TARGET_SCHED_FIRST_CYCLE_MULTIPASS_DFA_LOOKAHEAD e2k_multipass_lookahead
#undef TARGET_SCHED_REORDER
#define TARGET_SCHED_REORDER e2k_sched_reorder
#undef TARGET_SCHED_REORDER2
#define TARGET_SCHED_REORDER2 e2k_sched_reorder2
#undef TARGET_SCHED_INIT
#define TARGET_SCHED_INIT e2k_sched_init
#undef TARGET_SCHED_VARIABLE_ISSUE
#define TARGET_SCHED_VARIABLE_ISSUE e2k_variable_issue
#undef TARGET_DELAY_SCHED2
#define TARGET_DELAY_SCHED2 true
#undef TARGET_DELAY_VARTRACK
#define TARGET_DELAY_VARTRACK true
#undef TARGET_MACHINE_DEPENDENT_REORG
#define TARGET_MACHINE_DEPENDENT_REORG e2k_reorg

#undef TARGET_C_MODE_FOR_FLOATING_TYPE
#define TARGET_C_MODE_FOR_FLOATING_TYPE e2k_c_mode_for_floating_type
#undef TARGET_SCALAR_MODE_SUPPORTED_P
#define TARGET_SCALAR_MODE_SUPPORTED_P e2k_scalar_mode_supported_p
#undef TARGET_LIBGCC_FLOATING_MODE_SUPPORTED_P
#define TARGET_LIBGCC_FLOATING_MODE_SUPPORTED_P \
  e2k_libgcc_floating_mode_supported_p
#undef TARGET_INIT_BUILTINS
#define TARGET_INIT_BUILTINS e2k_init_builtins
#undef TARGET_BUILTIN_DECL
#define TARGET_BUILTIN_DECL e2k_builtin_decl
#undef TARGET_EXPAND_BUILTIN
#define TARGET_EXPAND_BUILTIN e2k_expand_builtin
#undef TARGET_ATOMIC_ASSIGN_EXPAND_FENV
#define TARGET_ATOMIC_ASSIGN_EXPAND_FENV e2k_atomic_assign_expand_fenv
#undef TARGET_C_MODE_FOR_SUFFIX
#define TARGET_C_MODE_FOR_SUFFIX e2k_c_mode_for_suffix
#undef TARGET_MANGLE_TYPE
#define TARGET_MANGLE_TYPE e2k_mangle_type

#undef TARGET_TRAMPOLINE_INIT
#define TARGET_TRAMPOLINE_INIT e2k_trampoline_init

struct gcc_target targetm = TARGET_INITIALIZER;
