/* Subroutines for the Elbrus (E2K) port, 64-bit Linux.
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
#include "tree-affine.h"
#include "tree-into-ssa.h"
#include "cfgloopmanip.h"
#include "tree-pretty-print.h"
#include "tree-cfg.h"
#include "tree-cfgcleanup.h"
#include "tree-dfa.h"
#include "tree-eh.h"

/* This file should be included last.  */
#include "target-def.h"

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
  int ring_base;		/* its first pair: below the outgoing ones, above
			   them with ring_setwd */
  bool ring_setwd;		/* the ring has a window of its own */
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

  /* glibc jmp_buf for nonlocal gotos and __builtin_longjmp to this
     function (e2k_expand_save_stack_nonlocal).  */
  rtx nonlocal_jmpbuf;

  /* The return is prepared once, at the entry (a leaf function).  */
  bool early_ret;
  /* A pipelined loop rotates predicates (setbp): leaving one resets it.  */
  bool rot_preds;
};

static struct machine_function *
e2k_init_machine_status (void)
{
  machine_function *m = ggc_cleared_alloc<machine_function> ();
  m->apb_big = -1;
  return m;
}

static gimple_opt_pass *make_pass_e2k_alias_version (gcc::context *, bool);
static gimple_opt_pass *make_pass_e2k_block_version (gcc::context *);
static rtl_opt_pass *make_pass_e2k_dbl_zext (gcc::context *);
static rtl_opt_pass *make_pass_e2k_dbl_widen (gcc::context *);
static rtl_opt_pass *make_pass_e2k_addr_height (gcc::context *);
static rtl_opt_pass *make_pass_e2k_latch_copies (gcc::context *);
static rtl_opt_pass *make_pass_e2k_narrow_ext (gcc::context *);

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

  /* -mtune names a CPU and with it the ISA version, over -march (lcc,
     spec/abi/source-compat.md); gas gets -mcpu=<cpu> (linux.h).  */
  if (e2k_tune == 4)
    e2k_arch = 3;
  else if (e2k_tune == 8)
    e2k_arch = 5;
  else if (e2k_tune >= 9 && e2k_tune <= 11)
    e2k_arch = 6;
  /* The latencies are v3's up to v5 and changed on v6 (spec/isa/timing.md,
     "Elbrus-2C3 (v6)"); v7 has none measured and takes v6's.  The ISA
     version stays what decides encodings, channels and the APB and loop
     rules, which every CPU that runs the code must obey.  */
  if (e2k_lat == 0)
    e2k_lat = e2k_arch >= 6 ? 6 : 3;

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

  /* We schedule and bundle in machine reorg ourselves.  */
  if (flag_var_tracking)
    flag_var_tracking_assignments = 0;

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
  /* 64-bit vectors (e2k-vect.md) in any register, as DImode.  */
  if (VECTOR_MODE_P (mode))
    return GET_MODE_SIZE (mode) == 8;

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
  if (PRED_REGNO_P (regno) || CTPR_REGNO_P (regno))
    return 1;
  return CEIL (GET_MODE_SIZE (mode), UNITS_PER_WORD);
}

static bool
e2k_modes_tieable_p (machine_mode m1, machine_mode m2)
{
  if (m1 == m2)
    return true;
  if (m1 == BImode || m2 == BImode)
    return false;
  return (GET_MODE_SIZE (m1) <= 8
	  && GET_MODE_SIZE (m2) <= 8);
}

/* ------------------------------------------------------------------ */
/* Addresses and constants                                             */
/* ------------------------------------------------------------------ */

bool
e2k_tls_symbol_p (rtx x)
{
  return GET_CODE (x) == SYMBOL_REF && SYMBOL_REF_TLS_MODEL (x) != 0;
}

static bool
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

static bool
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
/* PIC and TLS (spec/abi/elf.md)                                       */
/* ------------------------------------------------------------------ */

static rtx
e2k_got_reg (void)
{
  if (pic_offset_table_rtx)
    {
      crtl->uses_pic_offset_table = 1;
      return pic_offset_table_rtx;
    }
  /* Cost estimates run before the pseudo exists.  */
  return gen_reg_rtx (Pmode);
}

static void
e2k_init_pic_reg (void)
{
  start_sequence ();
  emit_insn (gen_e2k_gotbase (pic_offset_table_rtx));
  rtx_insn *seq = end_sequence ();
  edge entry_edge = single_succ_edge (ENTRY_BLOCK_PTR_FOR_FN (cfun));
  insert_insn_on_edge (seq, entry_edge);
  commit_one_edge_insertion (entry_edge);
}

/* Split a symbolic constant into symbol and offset.  */
static rtx
e2k_split_symbolic (rtx x, HOST_WIDE_INT *off)
{
  *off = 0;
  if (GET_CODE (x) == CONST)
    {
      x = XEXP (x, 0);
      gcc_assert (GET_CODE (x) == PLUS && CONST_INT_P (XEXP (x, 1)));
      *off = INTVAL (XEXP (x, 1));
      x = XEXP (x, 0);
    }
  return x;
}

static rtx
e2k_got_load (rtx sym, int kind, rtx dst)
{
  rtx got = e2k_got_reg ();
  rtx addr = gen_rtx_PLUS (Pmode, got,
			   gen_rtx_UNSPEC (Pmode, gen_rtvec (1, sym), kind));
  rtx mem = gen_const_mem (Pmode, addr);
  if (!dst)
    dst = gen_reg_rtx (Pmode);
  emit_move_insn (dst, mem);
  return dst;
}

/* Address of SYM in PIC code: local symbols relative to the GOT
   (@GOTOFF, a 64-bit literal), others through their GOT entry (@GOT).  */
static rtx
e2k_legitimize_pic (rtx x)
{
  HOST_WIDE_INT off;
  rtx sym = e2k_split_symbolic (x, &off);
  rtx reg = gen_reg_rtx (Pmode);

  bool local = (GET_CODE (sym) == LABEL_REF
		|| (SYMBOL_REF_LOCAL_P (sym)
		    && !(SYMBOL_REF_DECL (sym)
			 && lookup_attribute ("ifunc",
					      DECL_ATTRIBUTES (SYMBOL_REF_DECL (sym))))));
  if (local)
    {
      rtx got = e2k_got_reg ();
      emit_insn (gen_rtx_SET (reg,
			      gen_rtx_PLUS (Pmode, got,
					    gen_rtx_UNSPEC (Pmode,
							    gen_rtvec (1, sym),
							    UNSPEC_GOTOFF))));
    }
  else
    e2k_got_load (sym, UNSPEC_GOT, reg);

  if (off)
    {
      rtx t = gen_reg_rtx (Pmode);
      emit_insn (gen_adddi3 (t, reg, GEN_INT (off)));
      reg = t;
    }
  return reg;
}

static GTY(()) rtx e2k_tls_get_addr_sym;

static rtx
e2k_tls_get_addr (void)
{
  if (!e2k_tls_get_addr_sym)
    e2k_tls_get_addr_sym = init_one_libfunc ("__tls_get_addr");
  return e2k_tls_get_addr_sym;
}

/* GD: __tls_get_addr (module, offset) with both from the GOT;
   IE: TP offset from the GOT; LE: a 64-bit literal from %g13.  There is
   no local-dynamic model.  */
static rtx
e2k_legitimize_tls (rtx x)
{
  HOST_WIDE_INT off;
  rtx sym = e2k_split_symbolic (x, &off);
  enum tls_model model = SYMBOL_REF_TLS_MODEL (sym);
  rtx tp = gen_rtx_REG (Pmode, TP_REGNUM);
  rtx reg = gen_reg_rtx (Pmode);

  if (model == TLS_MODEL_LOCAL_DYNAMIC)
    model = TLS_MODEL_GLOBAL_DYNAMIC;
  if (!flag_pic && model == TLS_MODEL_GLOBAL_DYNAMIC)
    model = TLS_MODEL_INITIAL_EXEC;

  switch (model)
    {
    case TLS_MODEL_GLOBAL_DYNAMIC:
      {
	rtx mod = e2k_got_load (sym, UNSPEC_TLS_GDMOD, NULL_RTX);
	rtx dtp = e2k_got_load (sym, UNSPEC_TLS_GDREL, NULL_RTX);
	rtx r = emit_library_call_value (e2k_tls_get_addr (), NULL_RTX,
					 LCT_CONST, Pmode, mod, Pmode,
					 dtp, Pmode);
	emit_move_insn (reg, r);
	break;
      }
    case TLS_MODEL_INITIAL_EXEC:
      {
	rtx t;
	if (flag_pic)
	  t = e2k_got_load (sym, UNSPEC_TLS_IE, NULL_RTX);
	else
	  {
	    /* Non-PIC code still needs the GOT base for the IE entry.  */
	    t = e2k_got_load (sym, UNSPEC_TLS_IE, NULL_RTX);
	  }
	emit_insn (gen_adddi3 (reg, tp, t));
	break;
      }
    case TLS_MODEL_LOCAL_EXEC:
      emit_insn (gen_rtx_SET (reg,
			      gen_rtx_PLUS (Pmode, tp,
					    gen_rtx_UNSPEC (Pmode,
							    gen_rtvec (1, sym),
							    UNSPEC_TLS_LE))));
      break;
    default:
      gcc_unreachable ();
    }

  if (off)
    {
      rtx t = gen_reg_rtx (Pmode);
      emit_insn (gen_adddi3 (t, reg, GEN_INT (off)));
      reg = t;
    }
  return reg;
}

static rtx
e2k_legitimize_address (rtx x, rtx, machine_mode)
{
  if (e2k_tls_referenced_p (x) && can_create_pseudo_p ())
    {
      if (GET_CODE (x) == PLUS && !e2k_tls_referenced_p (XEXP (x, 1)))
	return gen_rtx_PLUS (Pmode,
			     force_reg (Pmode, e2k_legitimize_tls (XEXP (x, 0))),
			     XEXP (x, 1));
      if (e2k_symbolic_operand_p (x))
	return e2k_legitimize_tls (x);
    }
  if (flag_pic && e2k_symbolic_operand_p (x) && can_create_pseudo_p ())
    return e2k_legitimize_pic (x);
  return x;
}

/* Expand a move; return true if done.  */
/* A 64-bit view of a value of at most 4 bytes.  Under dbl = 0 a 32-bit
   operation leaves the upper half of its register as it was, tag
   included, and a 64-bit read of a diagnostic upper half traps
   (spec/abi/calling-convention.md, "Unused parts of a slot"): a dead
   speculative load leaves one behind.  So no 64-bit operation may read
   such a value; combine would otherwise make (ashift:DI (subreg:DI
   (reg:SI))) wherever it masks off the upper bits later.  */
bool
e2k_partial_subreg_p (const_rtx op)
{
  return (SUBREG_P (op)
	  && paradoxical_subreg_p (op)
	  && GET_MODE_SIZE (GET_MODE (op)) > 4
	  && GET_MODE_SIZE (GET_MODE (SUBREG_REG (op))) <= 4);
}

bool
e2k_expand_move (machine_mode mode, rtx *operands)
{
  rtx dst = operands[0], src = operands[1];

  /* Zero-extend instead (e2k_partial_subreg_p).  */
  if (e2k_partial_subreg_p (src) && GET_MODE_SIZE (mode) == 8
      && can_create_pseudo_p ())
    {
      rtx inner = SUBREG_REG (src);
      machine_mode imode = GET_MODE (inner);
      scalar_int_mode iimode = int_mode_for_mode (imode).require ();
      inner = gen_lowpart (iimode, force_reg (imode, inner));
      rtx t = gen_reg_rtx (DImode);
      emit_insn (gen_rtx_SET (t, gen_rtx_ZERO_EXTEND (DImode, inner)));
      emit_move_insn (dst, gen_lowpart (mode, t));
      return true;
    }

  if (GET_CODE (src) == UNSPEC && XINT (src, 1) == UNSPEC_OPAQUE)
    {
      rtx t = force_reg (Pmode, XVECEXP (src, 0, 0));
      emit_insn (gen_e2k_opaque_copy (force_reg (Pmode, dst), t));
      return true;
    }

  if (MEM_P (dst) && !register_operand (src, mode) && can_create_pseudo_p ())
    {
      src = force_reg (mode, src);
      operands[1] = src;
    }

  if (can_create_pseudo_p () && e2k_symbolic_operand_p (src))
    {
      if (e2k_tls_referenced_p (src))
	{
	  emit_move_insn (dst, e2k_legitimize_tls (src));
	  return true;
	}
      if (flag_pic)
	{
	  emit_move_insn (dst, e2k_legitimize_pic (src));
	  return true;
	}
    }
  return false;
}

/* Split a 16-byte move into two 64-bit ones after reload.  long double
   keeps only the 16-bit sign and exponent in its second register and in
   bytes 8-9 of memory.  */
void
e2k_split_double_move (rtx dst, rtx src)
{
  machine_mode mode = GET_MODE (dst);
  bool xf = mode == XFmode;
  rtx dlo, dhi, slo, shi;

  if (REG_P (dst))
    {
      dlo = gen_rtx_REG (DImode, REGNO (dst));
      dhi = gen_rtx_REG (xf && MEM_P (src) ? HImode : DImode, REGNO (dst) + 1);
    }
  else
    {
      dlo = adjust_address (dst, DImode, 0);
      dhi = adjust_address (dst, xf ? HImode : DImode, 8);
    }

  if (REG_P (src))
    {
      slo = gen_rtx_REG (DImode, REGNO (src));
      shi = gen_rtx_REG (xf && MEM_P (dst) ? HImode : DImode, REGNO (src) + 1);
    }
  else if (MEM_P (src))
    {
      slo = adjust_address (src, DImode, 0);
      shi = adjust_address (src, xf ? HImode : DImode, 8);
    }
  else if (CONST_DOUBLE_P (src) && SCALAR_FLOAT_MODE_P (mode))
    {
      long l[4];
      if (xf)
	real_to_target (l, CONST_DOUBLE_REAL_VALUE (src), XFmode);
      else
	real_to_target (l, CONST_DOUBLE_REAL_VALUE (src), TFmode);
      HOST_WIDE_INT lo = ((unsigned HOST_WIDE_INT) (unsigned long) l[1] << 32)
			 | (unsigned long) l[0];
      HOST_WIDE_INT hi = ((unsigned HOST_WIDE_INT) (unsigned long) l[3] << 32)
			 | (unsigned long) l[2];
      if (xf)
	hi &= 0xffff;
      slo = GEN_INT (lo);
      shi = GEN_INT (hi);
    }
  else
    {
      slo = simplify_gen_subreg (DImode, src, mode, 0);
      shi = simplify_gen_subreg (DImode, src, mode, 8);
    }

  /* Order the halves so that a register isn't overwritten before it is
     read (overlapping pairs, or a load whose address uses DLO).  */
  bool hi_first = false;
  if (REG_P (dst) && REG_P (src) && REGNO (dst) == REGNO (src) + 1)
    hi_first = true;
  if (REG_P (dst) && MEM_P (src)
      && reg_overlap_mentioned_p (dlo, XEXP (src, 0)))
    hi_first = true;

  if (hi_first)
    {
      emit_move_insn (dhi, shi);
      emit_move_insn (dlo, slo);
    }
  else
    {
      emit_move_insn (dlo, slo);
      emit_move_insn (dhi, shi);
    }
}

/* ------------------------------------------------------------------ */
/* Argument passing (spec/abi/calling-convention.md)                   */
/* ------------------------------------------------------------------ */

/* True while the parameters of the current function are being laid out.
   GCC asks promote_function_mode the same question for the caller and
   the callee, but the ABI wants different answers: callers extend
   narrow integer arguments to 64 bits, and callees extend them again
   rather than trust the caller (spec/abi/calling-convention.md,
   "Integer promotion").  So the callee sees narrow arguments in their
   own mode, and GCC re-extends them into the promoted pseudo.  */
static bool e2k_laying_out_parms;

void
e2k_init_cumulative_args (CUMULATIVE_ARGS *cum, tree fntype, rtx, tree,
			  bool incoming)
{
  e2k_laying_out_parms = incoming;
  cum->slot = 0;
  cum->nargs = 0;
  cum->nnamed = -1;
  cum->unprototyped = false;
  cum->incoming = incoming;
  if (fntype && !incoming)
    {
      if (stdarg_p (fntype))
	cum->nnamed = list_length (TYPE_ARG_TYPES (fntype));
      else if (!prototype_p (fntype))
	cum->unprototyped = true;
    }
}

static HOST_WIDE_INT
e2k_arg_size (const function_arg_info &arg)
{
  if (arg.type)
    return int_size_in_bytes (arg.type);
  return GET_MODE_SIZE (arg.mode);
}

/* First slot of an argument of SIZE bytes: 9 bytes or more start at an
   even slot, by size and not by alignment.  */
static int
e2k_arg_slot (int slot, HOST_WIDE_INT size)
{
  if (size > 8)
    slot = (slot + 1) & ~1;
  return slot;
}

/* Registers for a value of MODE/TYPE (SIZE bytes) occupying slots from
   SLOT, numbered from BASE (R0 for the callee's view, B0 for the
   caller's).  Scalars are one register (or an adjacent pair for 16-byte
   modes); aggregates and complex values are a PARALLEL of 64-bit
   pieces, packed as in memory.  A last piece holding 1-4 bytes is
   32-bit, so that the callee reads it at the width of its data (lcc
   writes such a slot with a 32-bit operation; see "Unused parts of a
   slot").  */
static rtx
e2k_slot_rtx (machine_mode mode, const_tree type, int slot, int base,
	      HOST_WIDE_INT size)
{
  bool aggregate = (type && (AGGREGATE_TYPE_P (type)
			     || TREE_CODE (type) == COMPLEX_TYPE))
		   || mode == BLKmode || COMPLEX_MODE_P (mode);

  if (!aggregate)
    return gen_rtx_REG (mode, base + slot);

  if (COMPLEX_MODE_P (mode))
    {
      machine_mode cm = GET_MODE_INNER (mode);
      HOST_WIDE_INT csize = GET_MODE_SIZE (cm);
      if (csize >= 8)
	{
	  rtx p0 = gen_rtx_EXPR_LIST (VOIDmode,
				      gen_rtx_REG (cm, base + slot),
				      const0_rtx);
	  rtx p1 = gen_rtx_EXPR_LIST (VOIDmode,
				      gen_rtx_REG (cm, base + slot + csize / 8),
				      GEN_INT (csize));
	  return gen_rtx_PARALLEL (mode, gen_rtvec (2, p0, p1));
	}
    }

  int n = (size + 7) / 8;
  if (n == 0)
    return NULL_RTX;
  rtvec v = rtvec_alloc (n);
  for (int i = 0; i < n; i++)
    {
      HOST_WIDE_INT rem = size - 8 * i;
      machine_mode pm = rem <= 4 ? SImode : DImode;
      RTVEC_ELT (v, i) = gen_rtx_EXPR_LIST (VOIDmode,
					    gen_rtx_REG (pm, base + slot + i),
					    GEN_INT (8 * i));
    }
  return gen_rtx_PARALLEL (mode, v);
}

static rtx
e2k_function_arg_1 (cumulative_args_t cum_v, const function_arg_info &arg,
		    bool incoming)
{
  CUMULATIVE_ARGS *cum = get_cumulative_args (cum_v);

  if (arg.end_marker_p ())
    return NULL_RTX;

  HOST_WIDE_INT size = e2k_arg_size (arg);
  if (size < 0)
    return NULL_RTX;
  int nslots = (size + 7) / 8;
  int slot = e2k_arg_slot (cum->slot, size);
  if (nslots == 0 || slot + nslots > 8)
    return NULL_RTX;

  rtx reg = e2k_slot_rtx (arg.mode, arg.type, slot,
			  incoming ? R0_REGNUM : B0_REGNUM, size);
  if (!reg || incoming)
    return reg;

  /* Variadic and unprototyped calls also store the argument in its
     slot in memory: the last named argument and every unnamed one, or
     everything for an unprototyped call.  A PARALLEL whose first
     element has no register means "also on the stack".  */
  bool both = (cum->unprototyped || !arg.named
	       || (cum->nnamed > 0 && cum->nargs == cum->nnamed - 1));
  if (!both)
    return reg;

  int n = GET_CODE (reg) == PARALLEL ? XVECLEN (reg, 0) : 1;
  rtvec v = rtvec_alloc (n + 1);
  RTVEC_ELT (v, 0) = gen_rtx_EXPR_LIST (VOIDmode, NULL_RTX, const0_rtx);
  if (GET_CODE (reg) == PARALLEL)
    for (int i = 0; i < n; i++)
      RTVEC_ELT (v, i + 1) = XVECEXP (reg, 0, i);
  else
    RTVEC_ELT (v, 1) = gen_rtx_EXPR_LIST (VOIDmode, reg, const0_rtx);
  return gen_rtx_PARALLEL (arg.mode, v);
}

static rtx
e2k_function_arg (cumulative_args_t cum, const function_arg_info &arg)
{
  return e2k_function_arg_1 (cum, arg, false);
}

static rtx
e2k_function_incoming_arg (cumulative_args_t cum,
			   const function_arg_info &arg)
{
  return e2k_function_arg_1 (cum, arg, true);
}

static void
e2k_function_arg_advance (cumulative_args_t cum_v,
			  const function_arg_info &arg)
{
  CUMULATIVE_ARGS *cum = get_cumulative_args (cum_v);
  HOST_WIDE_INT size = e2k_arg_size (arg);
  e2k_laying_out_parms = cum->incoming;
  if (size < 0)
    size = 8;
  cum->slot = e2k_arg_slot (cum->slot, size) + (size + 7) / 8;
  cum->nargs++;
}

static unsigned int
e2k_function_arg_boundary (machine_mode mode, const_tree type)
{
  HOST_WIDE_INT size = type ? int_size_in_bytes (type)
			    : GET_MODE_SIZE (mode);
  return size > 8 ? 128 : PARM_BOUNDARY;
}

static bool
e2k_strict_argument_naming (cumulative_args_t)
{
  return true;
}

/* Callers extend narrow integer arguments and results to 64 bits.  */
static machine_mode
e2k_promote_function_mode (const_tree type, machine_mode mode,
			   int *punsignedp, const_tree, int for_return)
{
  if (for_return == 0 && e2k_laying_out_parms)
    return mode;
  if (GET_MODE_CLASS (mode) == MODE_INT
      && GET_MODE_SIZE (mode) < 8
      && (!type || INTEGRAL_TYPE_P (type) || POINTER_TYPE_P (type)))
    {
      if (type)
	*punsignedp = TYPE_UNSIGNED (type);
      return DImode;
    }
  return mode;
}

static bool
e2k_return_in_memory (const_tree type, const_tree)
{
  HOST_WIDE_INT size = int_size_in_bytes (type);
  return size < 0 || size > 64;
}

static rtx
e2k_function_value (const_tree type, const_tree fn, bool outgoing)
{
  int unsignedp = TYPE_UNSIGNED (type);
  machine_mode mode = promote_function_mode (type, TYPE_MODE (type),
					     &unsignedp, fn, 1);
  HOST_WIDE_INT size = int_size_in_bytes (type);
  if (mode != TYPE_MODE (type))
    size = 8;
  rtx r = e2k_slot_rtx (mode, type, 0, outgoing ? R0_REGNUM : B0_REGNUM,
			size);
  if (!r)
    r = gen_rtx_REG (DImode, outgoing ? R0_REGNUM : B0_REGNUM);
  return r;
}

static rtx
e2k_libcall_value (machine_mode mode, const_rtx)
{
  return gen_rtx_REG (mode, B0_REGNUM);
}

static bool
e2k_function_value_regno_p (const unsigned int regno)
{
  return B_REGNO_P (regno);
}

/* C++ types that are not trivially copyable (TREE_ADDRESSABLE) must be
   built in place, so lcc returns them through a hidden pointer passed as
   argument 0, whatever their size (the arguments move up one slot); the
   callee doesn't return the address.  Returning NULL from
   struct_value_rtx gives GCC's hidden first argument.  FN is a decl or a
   function type.  */
static bool
e2k_hidden_sret_p (const_tree fn)
{
  const_tree fntype = TREE_CODE (fn) == FUNCTION_DECL ? TREE_TYPE (fn) : fn;
  if (!FUNC_OR_METHOD_TYPE_P (fntype))
    return false;
  tree rettype = TREE_TYPE (fntype);
  return rettype && TREE_ADDRESSABLE (rettype);
}

/* C++ thunks, as lcc writes them: no window of their own (no setwd);
   adjust `this' in its argument register, then transfer with ct, not
   call, so the target runs in the caller's call and returns straight
   to it, with every argument (variadic ones too, which GCC's generic
   thunks can't forward) where the caller put it.  %g0 is free here:
   callers don't expect globals below %g16 to survive a call.  The
   insns go through final, which gives the thunk its line info.  */
static void
e2k_output_mi_thunk (FILE *f, tree thunk, HOST_WIDE_INT delta,
		     HOST_WIDE_INT vcall_offset, tree function)
{
  const char *fnname = IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (thunk));
  /* A hidden result pointer takes slot 0 and moves `this' to slot 1.  */
  rtx this_rtx = gen_rtx_REG (Pmode, R0_REGNUM
				     + (e2k_hidden_sret_p (function) ? 1 : 0));
  rtx tmp = gen_rtx_REG (Pmode, G0_REGNUM);

  reload_completed = 1;
  emit_note (NOTE_INSN_PROLOGUE_END);

  if (delta)
    {
      rtx d = GEN_INT (delta);
      if (!e2k_src2_operand (d, Pmode))
	{
	  emit_move_insn (tmp, d);
	  d = tmp;
	}
      emit_insn (gen_adddi3 (this_rtx, this_rtx, d));
    }
  if (vcall_offset)
    {
      emit_move_insn (tmp, gen_rtx_MEM (Pmode, this_rtx));
      emit_move_insn (tmp, gen_rtx_MEM (Pmode, plus_constant (Pmode, tmp,
							     vcall_offset)));
      emit_insn (gen_adddi3 (this_rtx, this_rtx, tmp));
    }
  emit_insn (gen_e2k_thunk_jump (XEXP (DECL_RTL (function), 0)));

  rtx_insn *insn = get_insns ();
  shorten_branches (insn);
  assemble_start_function (thunk, fnname);
  final_start_function (insn, f, 1);
  final (insn, f, 1);
  final_end_function ();
  assemble_end_function (thunk, fnname);
  reload_completed = 0;
}

/* A result of more than 64 bytes is written by the callee at its entry
   USD, over the caller's argument area; there is no hidden pointer.
   The caller passes the address of its own buffer in SRET_REGNUM to its
   call expander, which copies the result there after the call.  The
   callee builds the result in a local buffer and copies it to the
   entry USD in the epilogue, after it has finished reading arguments
   that the result overlaps.  */
static rtx
e2k_struct_value_rtx (tree fn, int incoming)
{
  if (fn && e2k_hidden_sret_p (fn))
    return NULL_RTX;
  if (!incoming)
    return gen_rtx_REG (Pmode, SRET_REGNUM);

  if (!cfun || !cfun->machine)
    return NULL_RTX;
  machine_function *m = cfun->machine;
  if (m->sret_mem)
    return m->sret_addr;
  if (!currently_expanding_to_rtl || !fn)
    return NULL_RTX;

  tree fntype = TREE_CODE (fn) == FUNCTION_DECL ? TREE_TYPE (fn) : fn;
  tree rettype = TREE_TYPE (fntype);
  if (!rettype || !aggregate_value_p (rettype, fntype))
    return NULL_RTX;

  HOST_WIDE_INT size = int_size_in_bytes (rettype);
  if (size < 0)
    {
      sorry ("returning a variable-sized value");
      size = 8;
    }
  size = ROUND_UP (size, 8);
  m->sret_mem = assign_stack_local (BLKmode, size, 128);
  rtx addr = XEXP (m->sret_mem, 0);
  gcc_assert (GET_CODE (addr) == PLUS
	      && XEXP (addr, 0) == virtual_stack_vars_rtx);
  m->sret_offset = INTVAL (XEXP (addr, 1));
  m->sret_size = size;
  m->sret_addr = gen_rtx_UNSPEC (Pmode, gen_rtvec (1, addr), UNSPEC_OPAQUE);
  return m->sret_addr;
}

int
e2k_reg_parm_stack_space (const_tree fn)
{
  int space = 64;
  if (fn)
    {
      const_tree fntype = TREE_CODE (fn) == FUNCTION_DECL ? TREE_TYPE (fn)
							  : fn;
      if (FUNC_OR_METHOD_TYPE_P (fntype))
	{
	  tree rettype = TREE_TYPE (fntype);
	  if (rettype && TREE_CODE (rettype) != VOID_TYPE
	      && COMPLETE_TYPE_P (rettype) && !TREE_ADDRESSABLE (rettype))
	    {
	      HOST_WIDE_INT size = int_size_in_bytes (rettype);
	      if (size > 64)
		space = MAX (space, (int) ROUND_UP (size, 16));
	    }
	}
    }
  return space;
}

/* ------------------------------------------------------------------ */
/* Frame layout, prologue, epilogue                                    */
/* ------------------------------------------------------------------ */

static HOST_WIDE_INT
e2k_frame_size (void)
{
  return ROUND_UP (get_frame_size (), 16)
	 + ROUND_UP (crtl->outgoing_args_size, 16);
}

HOST_WIDE_INT
e2k_initial_elimination_offset (int from, int to)
{
  gcc_assert (from == FRAME_POINTER_REGNUM || from == ARG_POINTER_REGNUM);
  if (to == HARD_FRAME_POINTER_REGNUM)
    return 0;
  gcc_assert (to == STACK_POINTER_REGNUM);
  return e2k_frame_size ();
}

static bool
e2k_sp_mentioned_p (void)
{
  /* The prologue is built in a nested sequence.  */
  for (rtx_insn *insn = get_topmost_sequence ()->first; insn;
       insn = NEXT_INSN (insn))
    if (INSN_P (insn)
	&& reg_mentioned_p (stack_pointer_rtx, PATTERN (insn)))
      return true;
  return false;
}

void
e2k_expand_prologue (void)
{
  HOST_WIDE_INT total = e2k_frame_size ();

  /* -fstack-usage reports the data stack (USD) only; the window and the
     return address live in the procedure and chain stacks.  */
  if (flag_stack_usage_info)
    current_function_static_stack_size = total;

  emit_insn (gen_e2k_setwd ());

  /* return -> ct costs 6 cycles (spec/isa/control-transfer.md): in a
     function without calls, which would empty %ctpr3, prepare it once
     here, as lcc does; the epilogues are then the ct alone, and nothing
     else takes %ctpr3, live everywhere (e2k_prepare_branches takes only
     a CTPR dead at its branch).  */
  machine_function *m = cfun->machine;
  m->early_ret = (crtl->is_leaf && !cfun->calls_setjmp
		  && !crtl->calls_eh_return && !cfun->has_nonlocal_label);

  if (total > 0 || frame_pointer_needed || e2k_sp_mentioned_p ())
    {
      if (total > 0x7fffffff)
	sorry ("stack frame of more than 2 GiB");
      rtx_insn *insn
	= emit_insn (gen_e2k_getsp (stack_pointer_rtx, GEN_INT (-total)));
      /* The CFA is the entry USD.  getsp is an unspec, so describe it.  */
      RTX_FRAME_RELATED_P (insn) = 1;
      add_reg_note (insn, REG_CFA_DEF_CFA,
		    plus_constant (Pmode, stack_pointer_rtx, total));
    }
  if (frame_pointer_needed)
    {
      rtx_insn *insn
	= emit_insn (gen_adddi3 (hard_frame_pointer_rtx, stack_pointer_rtx,
				 GEN_INT (total)));
      RTX_FRAME_RELATED_P (insn) = 1;
      add_reg_note (insn, REG_CFA_DEF_CFA, hard_frame_pointer_rtx);
    }
  emit_insn (gen_blockage ());
  /* After the blockage, which would wait for its 6 cycles.  */
  if (m->early_ret)
    emit_insn (gen_e2k_return_prep ());
}

void
e2k_expand_epilogue (void)
{
  machine_function *m = cfun->machine;

  if (m->sret_mem)
    {
      /* Copy the result to the entry USD.  Globals are free here.  */
      rtx base;
      HOST_WIDE_INT bias;
      if (frame_pointer_needed)
	base = hard_frame_pointer_rtx, bias = 0;
      else
	base = stack_pointer_rtx, bias = e2k_frame_size ();
      for (HOST_WIDE_INT i = 0; i < m->sret_size; i += 8)
	{
	  rtx t = gen_rtx_REG (DImode, 16 + (i / 8) % 4);
	  emit_move_insn (t, gen_rtx_MEM (DImode,
					  plus_constant (Pmode, base,
							 bias + m->sret_offset
							 + i)));
	  emit_move_insn (gen_rtx_MEM (DImode,
				       plus_constant (Pmode, base, bias + i)),
			  t);
	}
    }

  if (!m->early_ret)
    emit_insn (gen_e2k_return_prep ());
  emit_jump_insn (gen_e2k_return ());
}

/* Window layout: W pairs hold the window registers the function uses;
   the outgoing registers %b[0..7] are the four pairs after them.  */
static void
e2k_compute_window (void)
{
  machine_function *m = cfun->machine;
  if (m->window_done)
    return;

  int maxr = -1;
  bool use_b = false, calls = false;
  for (rtx_insn *insn = get_insns (); insn; insn = NEXT_INSN (insn))
    {
      if (!INSN_P (insn))
	continue;
      if (CALL_P (insn))
	use_b = calls = true;
      auto note_reg = [&] (rtx r)
	{
	  if (!REG_P (r) || REGNO (r) >= FIRST_PSEUDO_REGISTER)
	    return;
	  for (unsigned i = REGNO (r); i < END_REGNO (r); i++)
	    {
	      if (W_REGNO_P (i))
		maxr = MAX (maxr, (int) (i - R0_REGNUM));
	      else if (B_REGNO_P (i))
		use_b = true;
	    }
	};
      subrtx_var_iterator::array_type array;
      FOR_EACH_SUBRTX_VAR (iter, array, PATTERN (insn), NONCONST)
	note_reg (*iter);
      if (CALL_P (insn))
	for (rtx link = CALL_INSN_FUNCTION_USAGE (insn); link;
	     link = XEXP (link, 1))
	  {
	    rtx u = XEXP (link, 0);
	    if (GET_CODE (u) == USE || GET_CODE (u) == CLOBBER)
	      {
		rtx r = XEXP (u, 0);
		if (GET_CODE (r) == PARALLEL)
		  {
		    for (int k = 0; k < XVECLEN (r, 0); k++)
		      if (XEXP (XVECEXP (r, 0, k), 0))
			note_reg (XEXP (XVECEXP (r, 0, k), 0));
		  }
		else
		  note_reg (r);
	      }
	  }
    }

  /* A pipelined loop's ring of %b[] lies between the window registers
     and the outgoing ones (e2k_output_setbn): a callee's setwd must
     cover all of the caller's window above wbs (spec/abi/registers.md),
     so calls keep handing over just the 4 outgoing pairs.  In a function
     that calls, the window grows for the ring only while the loop runs,
     as lcc does (e2k_output_setbn): otherwise every call leaves the ring
     below the callee, and a chain of such windows overflows the register
     file (xz's encoder calling its match finder: a spill and fill each
     time, 0.5% of xz -6 in BUB_B_RF_SPILLFILL).  Not in a leaf, which
     would pay for the setwds (about 3 cycles a loop, relcc2 findings
     I31) for nothing.  The ring then goes above the outgoing pairs,
     which can hold a value across the loop (%b[0..7] are allocatable;
     zlib's inflate kept one there).  */
  int top = (maxr + 2) / 2;
  /* Also where the outgoing pairs would follow too big a ring: gas
     takes rbs <= 63 (6 bits).  The window then takes at most 36 + 63
     pairs of the 112 the register file has.  */
  m->ring_setwd = (m->rot_pairs > 0
		   && ((calls && e2k_ring_setwd) || top + m->rot_pairs > 63));
  m->ring_base = m->ring_setwd ? top + 4 : top;
  m->wbase = m->ring_setwd ? top : top + m->rot_pairs;
  m->use_b = use_b;
  m->wsz = use_b ? m->wbase + 4 : MAX (m->wbase, 4);
  m->window_done = true;
}

int
e2k_window_base (void)
{
  e2k_compute_window ();
  return cfun->machine->wbase;
}

/* Whether this function runs with setwd dbl = 1, so that 32-bit
   operations zero-extend their results.  As lcc: at -O2 and above, in a
   function that zero-extends 32-bit values to 64 bits (spec/abi/
   registers.md).  Decided once, after expansion, from the insns.  */
bool
e2k_dbl_p (void)
{
  if (e2k_dbl)
    return true;
  if (!cfun || !cfun->machine || optimize < 2 || currently_expanding_to_rtl)
    return false;
  machine_function *m = cfun->machine;
  if (m->dbl_known)
    return m->dbl;
  m->dbl_known = true;
  m->dbl = false;
  for (rtx_insn *insn = get_insns (); insn && !m->dbl;
       insn = NEXT_INSN (insn))
    if (NONDEBUG_INSN_P (insn))
      {
	subrtx_iterator::array_type array;
	FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
	  if (GET_CODE (*iter) == ZERO_EXTEND && GET_MODE (*iter) == DImode
	      && GET_MODE (XEXP (*iter, 0)) == SImode
	      && !MEM_P (XEXP (*iter, 0)))
	    {
	      m->dbl = true;
	      break;
	    }
      }
  return m->dbl;
}

const char *
e2k_output_setwd (void)
{
  static char buf[160];
  machine_function *m = cfun->machine;
  e2k_compute_window ();
  if (m->use_b)
    snprintf (buf, sizeof buf,
	      "setwd\twsz = %d, nfx = 1, dbl = %d\n\t"
	      "setbn\trsz = 3, rbs = %d, rcur = 0",
	      m->wsz, e2k_dbl_p () ? 1 : 0, m->wbase);
  else
    snprintf (buf, sizeof buf, "setwd\twsz = %d, nfx = 1, dbl = %d",
	      m->wsz, e2k_dbl_p () ? 1 : 0);
  return buf;
}

const char *
e2k_output_call (void)
{
  static char buf[64];
  snprintf (buf, sizeof buf, "call\t%%%%ctpr1, wbs = %d", e2k_window_base ());
  return buf;
}

static bool
e2k_frame_pointer_required (void)
{
  return cfun->calls_alloca || cfun->has_nonlocal_label;
}

static bool
e2k_can_eliminate (const int, const int to)
{
  return to == HARD_FRAME_POINTER_REGNUM || !frame_pointer_needed;
}

/* ------------------------------------------------------------------ */
/* Calls                                                               */
/* ------------------------------------------------------------------ */

/* Whether expand_call loaded SRET_REGNUM for the call being emitted: it
   does so shortly before the call, only when struct_value_rtx returned
   it (not for the hidden-pointer returns of e2k_hidden_sret_p).  The
   call expander runs in a sequence of its own, so look through the
   enclosing ones too.  */
static bool
e2k_sret_reg_set_p (void)
{
  for (sequence_stack *seq = get_current_sequence (); seq; seq = seq->next)
    for (rtx_insn *insn = seq->last; insn; insn = PREV_INSN (insn))
      {
	if (CALL_P (insn) || LABEL_P (insn) || JUMP_P (insn))
	  return false;
	if (!INSN_P (insn))
	  continue;
	rtx set = single_set (insn);
	if (set && REG_P (SET_DEST (set))
	    && REGNO (SET_DEST (set)) == SRET_REGNUM)
	  return true;
      }
  return false;
}

void
e2k_expand_call (rtx retval, rtx mem, rtx argsize, rtx struct_size)
{
  rtx addr = XEXP (mem, 0);

  if (GET_CODE (addr) == SYMBOL_REF && !e2k_tls_symbol_p (addr))
    emit_insn (gen_e2k_disp (addr));
  else
    {
      if (flag_pic && e2k_symbolic_operand_p (addr))
	addr = e2k_legitimize_pic (addr);
      emit_insn (gen_e2k_movtd_ctpr1 (force_reg (Pmode, addr)));
    }

  rtx sret_addr = NULL_RTX;
  HOST_WIDE_INT ssize = (struct_size && CONST_INT_P (struct_size))
			? INTVAL (struct_size) : 0;
  if (ssize > 64 && e2k_sret_reg_set_p ())
    {
      sret_addr = gen_reg_rtx (Pmode);
      emit_move_insn (sret_addr, gen_rtx_REG (Pmode, SRET_REGNUM));
    }

  rtx target = gen_rtx_MEM (DImode, gen_rtx_REG (DImode, CTPR1_REGNUM));
  rtx call = gen_rtx_CALL (VOIDmode, target, argsize);
  if (retval)
    call = gen_rtx_SET (retval, call);
  emit_call_insn (call);

  if (sret_addr)
    {
      /* The callee wrote the result at our USD; nothing else may use the
	 argument area before it is copied out.  */
      rtx src = gen_rtx_MEM (BLKmode, stack_pointer_rtx);
      rtx dst = gen_rtx_MEM (BLKmode, sret_addr);
      set_mem_align (src, 128);
      set_mem_align (dst, 64);
      emit_block_move (dst, src, GEN_INT (ssize), BLOCK_OP_NO_LIBCALL);
    }
}

static bool
e2k_function_ok_for_sibcall (tree, tree)
{
  return false;
}

/* ------------------------------------------------------------------ */
/* Compares                                                            */
/* ------------------------------------------------------------------ */

/* Rewrite CODE (A, B) as a comparison the hardware has, possibly with
   swapped operands, and report whether the predicate must be inverted.
   Integer: e, l, le, b, be (guide 10.3.4); the others invert.  FP: eq,
   lt, le, uod, neq, od (guide 10.4); greater-than swaps.  The quiet
   unordered codes are handled by e2k_emit_cmp.  */
rtx
e2k_cmp_op (enum rtx_code code, machine_mode mode, rtx a, rtx b,
	    bool *invert)
{
  *invert = false;
  if (GET_MODE_CLASS (mode) == MODE_INT)
    {
      switch (code)
	{
	case EQ: case LT: case LE: case LTU: case LEU:
	  break;
	case NE: code = EQ; *invert = true; break;
	case GT: code = LE; *invert = true; break;
	case GE: code = LT; *invert = true; break;
	case GTU: code = LEU; *invert = true; break;
	case GEU: code = LTU; *invert = true; break;
	default: gcc_unreachable ();
	}
    }
  else
    {
      switch (code)
	{
	case EQ: case NE: case LT: case LE: case UNORDERED: case ORDERED:
	  break;
	case GT: code = LT; std::swap (a, b); break;
	case GE: code = LE; std::swap (a, b); break;
	default: gcc_unreachable ();
	}
    }
  return gen_rtx_fmt_ee (code, BImode, a, b);
}

/* Set PRED so that CODE (A, B) holds when PRED is true, or, if *INVERT
   is set on return, when it is false.  S1 and S2 are DImode scratch
   registers: both for XFmode, S1 for the quiet SF/DF codes.

   fcmplt/le (and nlt/nle) signal on quiet NaNs, so UNLT, UNLE, UNGT,
   UNGE and UNEQ use the quiet fcmpud*f, LTGT the signaling fcmpod*f;
   both write x86-style flags (less 0x1, equal 0x40, greater 0,
   unordered 0x45; checked on the 4C), tested with an integer compare.  */
static void
e2k_emit_cmp (enum rtx_code code, machine_mode mode, rtx a, rtx b,
	      rtx pred, rtx s1, rtx s2, bool *invert)
{
  if (code == UNLT || code == UNLE || code == UNGT || code == UNGE
      || code == UNEQ || code == LTGT)
    {
      if (code == UNGT || code == UNGE)
	{
	  code = code == UNGT ? UNLT : UNLE;
	  std::swap (a, b);
	}
      rtx r = gen_rtx_REG (SImode, REGNO (s1));
      /* LTGT signals on quiet NaNs (a < b || a > b folds to it);
	 islessgreater arrives as UNEQ, inverted.  */
      if (code == LTGT)
	{
	  if (mode == XFmode)
	    emit_insn (gen_e2k_fcmpoxf (r, a, b, s2));
	  else if (mode == DFmode)
	    emit_insn (gen_e2k_fcmpodf (r, a, b));
	  else
	    emit_insn (gen_e2k_fcmposf (r, a, b));
	}
      else if (mode == XFmode)
	emit_insn (gen_e2k_fcmpuxf (r, a, b, s2));
      else if (mode == DFmode)
	emit_insn (gen_e2k_fcmpudf (r, a, b));
      else
	emit_insn (gen_e2k_fcmpusf (r, a, b));
      rtx t;
      switch (code)
	{
	case UNLT:
	  t = gen_rtx_AND (SImode, r, const1_rtx);
	  *invert = true;
	  break;
	case UNLE:
	  t = r;
	  *invert = true;
	  break;
	case UNEQ:
	case LTGT:
	  t = gen_rtx_AND (SImode, r, GEN_INT (0x40));
	  *invert = code == UNEQ;
	  break;
	default:
	  gcc_unreachable ();
	}
      emit_insn (gen_rtx_SET (pred, gen_rtx_EQ (BImode, t, const0_rtx)));
      return;
    }

  rtx set = gen_rtx_SET (pred, e2k_cmp_op (code, mode, a, b, invert));
  if (mode == XFmode)
    emit_insn (gen_rtx_PARALLEL (VOIDmode,
				 gen_rtvec (3, set,
					    gen_rtx_CLOBBER (VOIDmode, s1),
					    gen_rtx_CLOBBER (VOIDmode, s2))));
  else
    emit_insn (set);
}

/* At expand time, replace a comparison *CMP of *A and *B (MODE) that
   needs fcmpu/fcmpo by an integer test of the flags those write, and
   return true; return false for the others.  The FP codes must not stay
   in the RTL: GCC reverses UNEQ (islessgreater's quiet compare,
   inverted) to LTGT, which must signal, and vice versa.  */
bool
e2k_lower_quiet_fp_cmp (rtx *cmp, rtx *a, rtx *b, machine_mode mode)
{
  enum rtx_code code = GET_CODE (*cmp);
  rtx x = force_reg (mode, *a), y = force_reg (mode, *b);
  switch (code)
    {
    case UNGT:
    case UNGE:
      code = code == UNGT ? UNLT : UNLE;
      std::swap (x, y);
      break;
    case UNLT:
    case UNLE:
    case UNEQ:
    case LTGT:
      break;
    default:
      return false;
    }

  rtx r = gen_reg_rtx (SImode);
  if (code == LTGT)
    {
      if (mode == XFmode)
	emit_insn (gen_e2k_fcmpoxf (r, x, y, gen_reg_rtx (DImode)));
      else if (mode == DFmode)
	emit_insn (gen_e2k_fcmpodf (r, x, y));
      else
	emit_insn (gen_e2k_fcmposf (r, x, y));
    }
  else if (mode == XFmode)
    emit_insn (gen_e2k_fcmpuxf (r, x, y, gen_reg_rtx (DImode)));
  else if (mode == DFmode)
    emit_insn (gen_e2k_fcmpudf (r, x, y));
  else
    emit_insn (gen_e2k_fcmpusf (r, x, y));

  /* less 0x1, equal 0x40, greater 0, unordered 0x45.  */
  rtx t = r;
  if (code != UNLE)
    {
      t = gen_reg_rtx (SImode);
      emit_insn (gen_andsi3 (t, r, GEN_INT (code == UNLT ? 1 : 0x40)));
    }
  *cmp = gen_rtx_fmt_ee (code == LTGT ? EQ : NE, VOIDmode, t, const0_rtx);
  *a = t;
  *b = const0_rtx;
  return true;
}

/* The value a bit test compares with zero: X & M, or with POS given,
   the field of M bits at POS, as X & its mask (cmpande, *cmpand_pred).  */
rtx
e2k_bit_test (machine_mode mode, rtx x, rtx m, rtx pos)
{
  if (pos)
    m = gen_int_mode (((HOST_WIDE_INT_1U << INTVAL (m)) - 1) << INTVAL (pos),
		      mode);
  return gen_rtx_AND (mode, x, m);
}

/* Operands: 0 comparison, 1 and 2 its operands, 3 label, 4 BI scratch,
   5 and 6 DI scratches (FP only; 6 for XFmode only).  */
void
e2k_split_compare_branch (rtx *operands, machine_mode mode)
{
  bool invert;
  rtx pred = operands[4];
  e2k_emit_cmp (GET_CODE (operands[0]), mode, operands[1], operands[2],
		pred, FLOAT_MODE_P (mode) ? operands[5] : NULL_RTX,
		mode == XFmode ? operands[6] : NULL_RTX, &invert);
  rtx test = gen_rtx_fmt_ee (invert ? EQ : NE, VOIDmode, pred, const0_rtx);
  emit_jump_insn (gen_rtx_SET (pc_rtx,
			       gen_rtx_IF_THEN_ELSE (VOIDmode, test,
						     gen_rtx_LABEL_REF (VOIDmode,
									operands[3]),
						     pc_rtx)));
}

/* Operands: 0 destination, 1 comparison, 2 and 3 its operands, 4 BI
   scratch, 5 DI scratch (FP only).  */
void
e2k_split_cstore (rtx *operands, machine_mode mode)
{
  bool invert;
  rtx pred = operands[4];
  e2k_emit_cmp (GET_CODE (operands[1]), mode, operands[2], operands[3],
		pred, FLOAT_MODE_P (mode) ? operands[5] : NULL_RTX, NULL_RTX,
		&invert);
  rtx test = gen_rtx_fmt_ee (invert ? EQ : NE, VOIDmode, pred, const0_rtx);
  rtx dst = operands[0];
  emit_insn (gen_rtx_SET (dst, gen_rtx_IF_THEN_ELSE (GET_MODE (dst), test,
						     const1_rtx, const0_rtx)));
}

/* Operands: 0 destination, 1 comparison, 2 and 3 its operands, 4 and 5
   the values, 6 BI scratch, 7 DI scratch (FP only).  */
void
e2k_split_movcc (rtx *operands, machine_mode mode)
{
  bool invert;
  rtx pred = operands[6];
  e2k_emit_cmp (GET_CODE (operands[1]), mode, operands[2], operands[3],
		pred, FLOAT_MODE_P (mode) ? operands[7] : NULL_RTX, NULL_RTX,
		&invert);
  rtx test = gen_rtx_fmt_ee (invert ? EQ : NE, VOIDmode, pred, const0_rtx);
  rtx dst = operands[0];
  emit_insn (gen_rtx_SET (dst, gen_rtx_IF_THEN_ELSE (GET_MODE (dst), test,
						     operands[4],
						     operands[5])));
}

/* movMODEcc: dst = cmp ? op2 : op3.  */
bool
e2k_expand_movcc (rtx *operands)
{
  rtx cmp = operands[1];
  rtx a = XEXP (cmp, 0), b = XEXP (cmp, 1);
  machine_mode cmode = GET_MODE (a);
  if (cmode == VOIDmode)
    cmode = GET_MODE (b);
  machine_mode mode = GET_MODE (operands[0]);
  enum rtx_code code = GET_CODE (cmp);

  if (cmode == SImode || cmode == DImode)
    {
      if (!e2k_int_cmp_operator (cmp, VOIDmode))
	return false;
      a = force_reg (cmode, a);
      if (!e2k_src2_operand (b, cmode))
	b = force_reg (cmode, b);
    }
  else if (cmode == SFmode || cmode == DFmode)
    {
      if (!e2k_any_fp_cmp_operator (cmp, VOIDmode))
	return false;
      /* x > y ? x : y is fmax (x, y), x < y ? x : y fmin (x, y); with
	 the arms the other way round, x > y ? y : x is fmin (y, x) and
	 x < y ? y : x fmax (y, x) (e2k_fmaxdf).  NPB EP's
	 "max (fabs (t3), fabs (t4))": a compare and a merge, 5 cycles,
	 in 2.  */
      rtx t = operands[2], f = operands[3];
      if ((code == GT || code == LT) && mode == cmode
	  && ((rtx_equal_p (t, a) && rtx_equal_p (f, b))
	      || (rtx_equal_p (t, b) && rtx_equal_p (f, a))))
	{
	  bool same = rtx_equal_p (t, a);
	  bool max = (code == GT) == same;
	  rtx x = force_reg (mode, same ? a : b);
	  rtx y = force_reg (mode, same ? b : a);
	  emit_insn (gen_rtx_SET (operands[0],
				  gen_rtx_UNSPEC (mode, gen_rtvec (2, x, y),
						  max ? UNSPEC_FMAX
						  : UNSPEC_FMIN)));
	  return true;
	}
      if (e2k_lower_quiet_fp_cmp (&cmp, &a, &b, cmode))
	{
	  cmode = SImode;
	  code = GET_CODE (cmp);
	}
      else
	{
	  a = force_reg (cmode, a);
	  b = force_reg (cmode, b);
	}
    }
  else
    return false;

  rtx t = operands[2], f = operands[3];
  if (!e2k_src2_operand (t, mode))
    t = force_reg (mode, t);
  if (!e2k_src1_operand (f, mode))
    f = force_reg (mode, f);

  rtx newcmp = gen_rtx_fmt_ee (code, VOIDmode, a, b);
  rtx set = gen_rtx_SET (operands[0],
			 gen_rtx_IF_THEN_ELSE (mode, newcmp, t, f));
  rtx bi = gen_rtx_CLOBBER (VOIDmode, gen_rtx_SCRATCH (BImode));
  if (FLOAT_MODE_P (cmode))
    emit_insn (gen_rtx_PARALLEL (VOIDmode,
				 gen_rtvec (3, set, bi,
					    gen_rtx_CLOBBER (VOIDmode,
							     gen_rtx_SCRATCH (DImode)))));
  else
    emit_insn (gen_rtx_PARALLEL (VOIDmode, gen_rtvec (2, set, bi)));
  return true;
}

/* MCST's gdb has no DWARF CFI unwinder: it walks the chain stack, and
   its "frame base" for DW_OP_call_frame_cfa is an offset in the
   procedure stack, not a data address.  So no .debug_frame, and
   DW_AT_frame_base becomes a register expression built from our CFI
   (%r8 + size after getsp, %r9 with a frame pointer), as lcc's is.  */
static enum unwind_info_type
e2k_debug_unwind_info (void)
{
  return UI_NONE;
}

/* ------------------------------------------------------------------ */
/* Inline assembly                                                     */
/* ------------------------------------------------------------------ */

/* Return CON with every 'x' replaced by 'r'.  */
static const char *
e2k_x_to_r (const char *con)
{
  char *s = XALLOCAVEC (char, strlen (con) + 1);
  strcpy (s, con);
  for (char *p = s; *p; p++)
    if (*p == 'x')
      *p = 'r';
  return ggc_strdup (s);
}

/* lcc's "x" constraint (spec/abi/source-compat.md): one extended
   register, which on v1-v4 holds a whole long double.  Our long double
   is a register pair, so an "x" operand becomes "r" on a DImode
   register: inputs (and inputs tied to "x" outputs) are packed with
   movif before the asm, outputs unpacked with movfi after it.  */
static rtx_insn *
e2k_md_asm_adjust (vec<rtx> &outputs, vec<rtx> &inputs,
		   vec<machine_mode> &input_modes,
		   vec<const char *> &constraints, vec<rtx> &, vec<rtx> &,
		   HARD_REG_SET &, location_t loc)
{
  unsigned nout = outputs.length ();
  auto_vec<bool, 16> xout;
  xout.safe_grow_cleared (nout);

  start_sequence ();
  for (unsigned i = 0; i < nout; i++)
    {
      if (!strchr (constraints[i], 'x'))
	continue;
      rtx dest = outputs[i];
      if (GET_MODE (dest) != XFmode)
	{
	  error_at (loc, "%<x%> %<asm%> operands must be %<long double%> "
		    "on this ISA");
	  continue;
	}
      rtx t = gen_reg_rtx (DImode);
      outputs[i] = t;
      constraints[i] = e2k_x_to_r (constraints[i]);
      xout[i] = true;
      if (REG_P (dest))
	emit_insn (gen_e2k_xf_unpack (dest, t));
      else
	{
	  rtx tmp = gen_reg_rtx (XFmode);
	  emit_insn (gen_e2k_xf_unpack (tmp, t));
	  emit_move_insn (dest, tmp);
	}
    }
  rtx_insn *after = get_insns ();
  end_sequence ();

  /* Insns emitted here go before the asm.  */
  for (unsigned k = 0; k < inputs.length (); k++)
    {
      const char *con = constraints[nout + k];
      bool tied = ISDIGIT (con[0]) && (unsigned) atoi (con) < nout
		  && xout[atoi (con)];
      if (!tied && !strchr (con, 'x'))
	continue;
      if (input_modes[k] != XFmode)
	{
	  error_at (loc, "%<x%> %<asm%> operands must be %<long double%> "
		    "on this ISA");
	  continue;
	}
      rtx t = gen_reg_rtx (DImode);
      emit_insn (gen_e2k_xf_pack (t, force_reg (XFmode, inputs[k])));
      inputs[k] = t;
      input_modes[k] = DImode;
      if (!tied)
	constraints[nout + k] = e2k_x_to_r (con);
    }
  return after;
}

/* ------------------------------------------------------------------ */
/* Atomics                                                             */
/* ------------------------------------------------------------------ */

rtx
e2k_return_addr (int count, rtx)
{
  if (count != 0)
    return NULL_RTX;
  rtx r = gen_reg_rtx (DImode);
  emit_insn (gen_e2k_rrd_cr0hi (r));
  return expand_simple_binop (DImode, AND, r,
			      gen_int_mode (HOST_WIDE_INT_C (0xffffffffffff),
					    DImode),
			      NULL_RTX, 1, OPTAB_DIRECT);
}

/* A BLKmode memory reference that orders all memory accesses.  */
rtx
e2k_barrier_mem (void)
{
  rtx mem = gen_rtx_MEM (BLKmode, gen_rtx_SCRATCH (Pmode));
  MEM_VOLATILE_P (mem) = 1;
  return mem;
}

/* The atomic sequences address memory as base register + 0.  */
rtx
e2k_atomic_mem (rtx mem)
{
  rtx addr = XEXP (mem, 0);
  if (!REG_P (addr))
    mem = replace_equiv_address (mem, force_reg (Pmode, addr));
  return mem;
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

static bool e2k_bundling;	/* bundle marks are valid for this function */
static bool e2k_in_bundle;

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

static int e2k_cur_chan (void);
/* Whether the insn being printed takes ",sm" (a pipelined loop's, or one
   moved above a branch).  */
static bool e2k_cur_sm;

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

static void
e2k_asm_file_start (void)
{
  default_file_start ();
  fputs ("\t.ignore\tld_st_style\n\t.ignore\tstrict_delay\n", asm_out_file);
}

/* ------------------------------------------------------------------ */
/* Scheduling and bundling                                             */
/* ------------------------------------------------------------------ */

/* Packed integer operations (e2k-vect.md).  */
static bool
e2k_packed_type_p (enum attr_type t)
{
  return t == TYPE_PINT || t == TYPE_PINT14 || t == TYPE_PMUL
	 || t == TYPE_PANY;
}

/* Literal syllables an insn needs (approximate: gas packs 16-bit
   literals two to a syllable).  */
static bool e2k_field_insn_p (rtx);

int
e2k_insn_lits (rtx_insn *insn)
{
  if (!INSN_P (insn) || JUMP_P (insn) || CALL_P (insn))
    return 0;
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) == USE || GET_CODE (pat) == CLOBBER
      || GET_CODE (pat) == ASM_INPUT || asm_noperands (pat) >= 0)
    return 0;
  if (recog_memoized (insn) < 0)
    return 0;
  if (INSN_CODE (insn) == CODE_FOR_e2k_disp
      || INSN_CODE (insn) == CODE_FOR_e2k_disp_label
      || INSN_CODE (insn) == CODE_FOR_e2k_ldisp_apb)
    return 0;
  {
    enum attr_type t = get_attr_type (insn);
    if (t == TYPE_MOVA || t == TYPE_AAU || t == TYPE_BAP)
      return 0;
  }
  if (e2k_field_insn_p (pat))
    return 1;
  /* An AAU store's literal is its byte offset, if any.  */
  if (e2k_staa_p (pat))
    return XVECEXP (XEXP (SET_DEST (pat), 0), 0, 2) != const0_rtx;

  int n = 0;
  subrtx_var_iterator::array_type array;
  FOR_EACH_SUBRTX_VAR (iter, array, pat, ALL)
    {
      rtx x = *iter;
      switch (GET_CODE (x))
	{
	case CONST_INT:
	  {
	    HOST_WIDE_INT v = INTVAL (x);
	    if (v >= 0 && v < 16)
	      ;
	    else if (v == (int32_t) v)
	      n += 1;
	    else
	      n += 2;
	    break;
	  }
	case CONST_DOUBLE:
	  n += GET_MODE_SIZE (GET_MODE (x)) > 4 ? 2 : 1;
	  break;
	case CONST_VECTOR:
	  {
	    rtx d = simplify_subreg (DImode, x, GET_MODE (x), 0);
	    HOST_WIDE_INT v = d ? INTVAL (d) : -1;
	    n += v >= 0 && v < 16 ? 0 : v == (int32_t) v ? 1 : 2;
	    iter.skip_subrtxes ();
	    break;
	  }
	case UNSPEC:
	  if (e2k_reloc_unspec_p (x))
	    {
	      n += (XINT (x, 1) == UNSPEC_GOTOFF
		    || XINT (x, 1) == UNSPEC_TLS_LE) ? 2 : 1;
	      iter.skip_subrtxes ();
	    }
	  break;
	case NEG:
	case ABS:
	  /* negsf2/absdf2 etc. print the sign mask as a literal.  */
	  if (GET_MODE (x) == SFmode)
	    n += 1;
	  else if (GET_MODE (x) == DFmode)
	    n += 2;
	  break;
	case SYMBOL_REF:
	case LABEL_REF:
	  n += 2;
	  break;
	case CONST:
	  n += 2;
	  iter.skip_subrtxes ();
	  break;
	default:
	  break;
	}
    }
  return MIN (n, 2);
}

static void
e2k_note_mem_store (rtx x, const_rtx, void *data)
{
  if (MEM_P (x))
    *(bool *) data = true;
}

static bool
e2k_mem_access_p (rtx_insn *insn)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
    if (MEM_P (*iter))
      return true;
  return false;
}

/* Every operation in a wide instruction reads the registers as they were
   before it, and two operations can't write one register in the same
   wide instruction.  Memory is not as simple (4C, findings I9, I12): a
   load in the wide instruction of a store to its address reads the old
   value, except that a load in ALC5 sees a store in ALC2.  gas chooses
   the channels, so a load and a store that may touch the same memory
   never share a wide instruction, in either order.  GCC's scheduler
   assumes sequential order inside a cycle unless told otherwise, so
   output dependences and any dependence between a store and another
   memory access cost a cycle.  The dependence need not be a true one:
   once a block has many memory accesses, sched-deps flushes its lists
   and later loads get only an anti dependence on the flushing store.  */
/* The memory reference of a load or store, or NULL.  */
static rtx
e2k_insn_mem (rtx_insn *insn)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
    if (MEM_P (*iter))
      return const_cast<rtx> (*iter);
  return NULL_RTX;
}

/* Whether store PRO and load CON may touch one doubleword: the same
   address apart from a constant less than 8 bytes.  On v6 only a load
   of bytes the store wrote pays (spec/isa/timing.md, "Elbrus-2C3"), so
   there their bytes must overlap.  */
static bool
e2k_same_dword_p (rtx_insn *pro, rtx_insn *con)
{
  rtx a = e2k_insn_mem (pro), b = e2k_insn_mem (con);
  if (!a || !b)
    return false;
  poly_int64 pa, pb;
  HOST_WIDE_INT oa, ob;
  rtx ba = strip_offset (XEXP (a, 0), &pa);
  rtx bb = strip_offset (XEXP (b, 0), &pb);
  if (!pa.is_constant (&oa) || !pb.is_constant (&ob))
    return true;
  if (!rtx_equal_p (ba, bb))
    return false;
  HOST_WIDE_INT sa = GET_MODE_SIZE (GET_MODE (a));
  HOST_WIDE_INT sb = GET_MODE_SIZE (GET_MODE (b));
  if (E2K_LAT6 && sa > 0 && sb > 0)
    return oa < ob + sb && ob < oa + sa;
  return oa - ob < 8 && ob - oa < 8;
}

static int e2k_spec_kind (rtx_insn *);
static bool e2k_spec_sets_live_p (rtx_insn *, rtx_insn *);

static bool e2k_ov_insn_p (rtx_insn *);

/* Per-insn flags of e2k_modsched and e2k_unpredicate_loads (e2k_ms_flag),
   for final: print ",sm", print abn, abp.  */
enum { E2K_MS_SM = 1, E2K_MS_ABN = 2, E2K_MS_ABP = 4 };

/* The condition a load had before e2k_unpredicate_loads ran it without
   one, by insn UID: the DAM may still move it above stores, with its
   check under the condition (a check under a false predicate does
   nothing, so its address need not be valid there; relcc2 findings
   I29).  */
static vec<rtx> e2k_unpred_cond;

static rtx
e2k_unpred_cond_of (const rtx_insn *insn)
{
  /* Only in machine reorg, which fills it and empties it at its end:
     sched1 of the next function reuses the UIDs.  */
  if (!reload_completed)
    return NULL_RTX;
  unsigned uid = INSN_UID (insn);
  return uid < e2k_unpred_cond.length () ? e2k_unpred_cond[uid] : NULL_RTX;
}

static void
e2k_set_unpred_cond (rtx_insn *insn, rtx cond)
{
  unsigned uid = INSN_UID (insn);
  if (uid >= e2k_unpred_cond.length ())
    e2k_unpred_cond.safe_grow_cleared (uid + 64);
  e2k_unpred_cond[uid] = copy_rtx (cond);
}

/* Whether INSN reads or writes a CTPR.  */
static bool
e2k_mentions_ctpr_p (rtx_insn *insn)
{
  for (unsigned r = CTPR1_REGNUM; r <= CTPR3_REGNUM; r++)
    if (reg_mentioned_p (gen_rtx_REG (DImode, r), PATTERN (insn)))
      return true;
  return false;
}

static int
e2k_adjust_cost (rtx_insn *con, int dep_type, rtx_insn *pro, int cost,
		 unsigned int)
{
  /* A taken transfer's whole wide instruction runs, and a call's too
     before the callee does.  So what depends on a call, and what depends
     on a jump because it has no speculative form or sets a register live
     where the jump goes, can't share their instruction.  Rewriting what
     the jump only reads (its predicate) can: the jump reads the old
     value.  e2k_spec_mark makes what does share it speculative, and
     only with control speculation (-mcontrol-spec): without it nothing
     shares (SQLite's createCollation, -mno-control-spec: a load of
     pColl->xCmp in the instruction of the jump that skips it when pColl
     is null, unmarked).  */
  if ((JUMP_P (pro) || CALL_P (pro)) && INSN_P (con) && cost < 1
      && (CALL_P (pro) || !e2k_control_spec || e2k_spec_kind (con) == 0
	  || e2k_spec_sets_live_p (con, pro)))
    return 1;
  /* Operations in the wide instruction with setwd already use the new
     window (spec/abi/registers.md), as lcc's prologues do; %b[] in the
     one with setbn still uses the old rotating base.  setwd is volatile,
     so everything after it depends on it, and on the prologue's
     blockage after it, which only keeps the body below the frame's
     setup (registers carry the rest).  */
  if (INSN_P (pro) && (recog_memoized (pro) == CODE_FOR_e2k_setwd
			|| recog_memoized (pro) == CODE_FOR_blockage
			|| recog_memoized (pro) == CODE_FOR_e2k_setbn_enter
			|| recog_memoized (pro) == CODE_FOR_e2k_setbn_leave)
      && INSN_P (con) && !CALL_P (con) && !JUMP_P (con)
      && !e2k_mentions_ctpr_p (con))
    {
      bool b = false;
      subrtx_iterator::array_type array;
      FOR_EACH_SUBRTX (iter, array, PATTERN (con), NONCONST)
	if (REG_P (*iter) && (B_REGNO_P (REGNO (*iter))
			      || BX_REGNO_P (REGNO (*iter))))
	  b = true;
      return b ? MAX (cost, 1) : 0;
    }
  /* rwd %lsr: only the loop's end reads %lsr, 4 cycles later
     (e2k_output_lsr_wait); what follows it may share its wide
     instruction, as lcc's AAU setup does.  But it is a barrier, which
     carries the dependences of what comes after it on what came before
     (sched-deps): a transfer, or a read of a CTPR, may depend on a
     prepare before it, and must not share that prepare's instruction.  */
  if (dep_type == REG_DEP_TRUE && INSN_P (pro)
      && recog_memoized (pro) == CODE_FOR_e2k_rwd_lsr)
    {
      bool ctpr = JUMP_P (con) || CALL_P (con) || e2k_mentions_ctpr_p (con);
      return ctpr ? MAX (MIN (cost, 2), 1) : 0;
    }
  if (INSN_P (pro) && INSN_P (con)
      && recog_memoized (pro) >= 0 && recog_memoized (con) >= 0)
    {
      enum attr_type pt = get_attr_type (pro), ct = get_attr_type (con);
      /* AAU writes are barriers to each other only to keep their order;
	 two fit a wide instruction (ALC2 and ALC5).  */
      if (pt == TYPE_AAU && ct == TYPE_AAU)
	return 0;
      /* fmax and fmin: 2 cycles, 2 more to an integer operation
	 (spec/isa/timing.md).  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_FCVT)
	if (rtx ps = single_set (pro))
	  if (GET_CODE (SET_SRC (ps)) == UNSPEC
	      && (XINT (SET_SRC (ps), 1) == UNSPEC_FMAX
		  || XINT (SET_SRC (ps), 1) == UNSPEC_FMIN))
	    return cost == 4 ? 2 : cost - 2;
      /* A conversion's result read in another format than the one it
	 produces arrives later: a double or 64-bit integer read as a
	 single 5, a 64-bit integer as a double 5, a single as a double 6
	 (spec/isa/timing.md, "Formats").  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_FCVT && cost == 4)
	if (rtx ps = single_set (pro))
	  if (REG_P (SET_DEST (ps)))
	    {
	      machine_mode pm = GET_MODE (SET_DEST (ps));
	      rtx pd = SET_DEST (ps);
	      rtx cs = single_set (con);
	      int lat = cost;
	      subrtx_iterator::array_type array;
	      if (cs)
		FOR_EACH_SUBRTX (iter, array, SET_SRC (cs), NONCONST)
		  if (REG_P (*iter) && REGNO (*iter) == REGNO (pd))
		    {
		      machine_mode cm = GET_MODE (*iter);
		      if (cm == pm || GET_MODE_SIZE (cm) > 8)
			continue;
		      lat = MAX (lat, (cm == DFmode && GET_MODE_SIZE (pm) == 4)
				      ? 6 : 5);
		    }
	      return lat;
	    }
      /* A conditional ct waits for its disp only 2 cycles when not
	 taken; taken, 5 minus the distance, still less than an ibranch
	 (spec/isa/control-transfer.md, "Costs").  Don't stretch the
	 fall-through path for it (e2k_prepare_branches).  An
	 unconditional one is always taken: it waits the whole 5.  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_DISP && ct == TYPE_CT
	  && (!e2k_uncond_ct_cost || !JUMP_P (con) || any_condjump_p (con)))
	return MIN (cost, 2);
      /* A barrier after a disp (sched-deps makes it depend on every set
	 before it) that doesn't read its CTPR needn't wait for the
	 prepare: setbn_leave on a pipelined loop's way out, which
	 e2k_lift_prepares puts disps above, the AAU setup of a loop.  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_DISP
	  && volatile_insn_p (PATTERN (con)))
	if (rtx s = single_set (pro))
	  if (!reg_overlap_mentioned_p (SET_DEST (s), PATTERN (con)))
	    return 0;
      /* Nor anything after a disp that is a barrier itself (the end of
	 array prefetch, e2k_apb_stop) and reads no CTPR: the barrier
	 carries the dependences on prepares before it.  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_DISP
	  && volatile_insn_p (PATTERN (pro))
	  && !JUMP_P (con) && !CALL_P (con) && !e2k_mentions_ctpr_p (con))
	return 0;
      /* A check after a jump (e2k_unpred_cond_deps): not in its wide
	 instruction, which runs also when it is taken.  */
      if (JUMP_P (pro) && ct == TYPE_LDCHK)
	return MAX (cost, 1);
      /* The same dependences of the load itself are for its check; the
	 lock load drops them, but only when it issues, and resolving one
	 earlier must not hold it back.  */
      if (dep_type == REG_DEP_TRUE && (ct == TYPE_LOAD || ct == TYPE_LDLOCK))
	if (rtx cond = e2k_unpred_cond_of (con))
	  if (JUMP_P (pro) ? !e2k_spec_sets_live_p (con, pro)
	      : reg_set_p (XEXP (cond, 0), pro))
	    return 0;
      /* A check waits for nothing of its lock load (relcc2 findings
	 I30), and its users wait 1 cycle for it: 2 cycles after the
	 lock, they get the lock's value in time.  */
      if (pt == TYPE_LDLOCK && ct == TYPE_LDCHK && dep_type == REG_DEP_TRUE)
	{
	  rtx pd = SET_DEST (XVECEXP (PATTERN (pro), 0, 0));
	  rtx cs = PATTERN (con);
	  if (GET_CODE (cs) == COND_EXEC)
	    cs = COND_EXEC_CODE (cs);
	  if (REG_P (pd) && GET_CODE (cs) == SET && REG_P (SET_DEST (cs))
	      && REGNO (SET_DEST (cs)) == REGNO (pd)
	      && !reg_overlap_mentioned_p (pd, XEXP (SET_SRC (cs), 1)))
	    return MIN (cost, 2);
	}
      /* No version can prepare and transfer through one CTPR in one wide
	 instruction: v1-v5 transfer to the old target, v6 falls through
	 (spec/isa/timing.md, "Elbrus-2C3 (v6)").  */
      if (dep_type == REG_DEP_ANTI
	  && (ct == TYPE_DISP || ct == TYPE_MOVCTP || ct == TYPE_RET)
	  && cost < 1
	  && (pt == TYPE_CT || pt == TYPE_CALL || pt == TYPE_BRANCH))
	return 1;
      /* A load of a doubleword stored in the wide instruction just before
	 gets its value about 8 cycles late; one cycle between them is
	 enough (spec/isa/timing.md, "Store to load").  Only for the same
	 doubleword, or in a loop copy for overlapping arrays, where they
	 mostly are (zlib's copies of distance 1: 40 cycles for 3 bytes);
	 a store and a load that merely may alias keep 1.  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_STORE
	  && (ct == TYPE_LOAD || ct == TYPE_LDLOCK || ct == TYPE_LDCHK)
	  && (e2k_same_dword_p (pro, con) || e2k_ov_insn_p (con)))
	return MAX (cost, 2);
    }
  if (cost >= 1)
    return cost;
  if (dep_type == REG_DEP_OUTPUT)
    return 1;
  if (!INSN_P (pro) || !INSN_P (con))
    return cost;
  bool pro_stores = false, con_stores = false;
  note_stores (pro, e2k_note_mem_store, &pro_stores);
  note_stores (con, e2k_note_mem_store, &con_stores);
  if ((pro_stores && e2k_mem_access_p (con))
      || (con_stores && e2k_mem_access_p (pro)))
    return 1;
  return cost;
}

static int
e2k_issue_rate (void)
{
  return 8;
}

static int
e2k_multipass_lookahead (void)
{
  return 4;
}

/* Cycle of each scheduled insn, for nop padding.  */
static int e2k_sched_clock;
static vec<int> e2k_insn_clock;
/* The extended block each insn was scheduled in (from 1; 0: not by
   sched-ebb), so that bundling knows whose clocks compare.  */
static vec<int> e2k_insn_ebb;
static int e2k_ebb_id;

static void
e2k_sched_init_global (FILE *, int, int)
{
  e2k_insn_clock.truncate (0);
  e2k_insn_clock.safe_grow_cleared (get_max_uid () + 1);
  e2k_insn_ebb.truncate (0);
}

static int
e2k_sched_reorder (FILE *, int, rtx_insn **, int *, int clock)
{
  e2k_sched_clock = clock;
  return e2k_issue_rate ();
}

static int
e2k_sched_reorder2 (FILE *, int, rtx_insn **, int *n_readyp, int clock)
{
  e2k_sched_clock = clock;
  return *n_readyp;
}

static void
e2k_sched_init (FILE *, int, int)
{
  e2k_ebb_id++;
}

static int
e2k_variable_issue (FILE *, int, rtx_insn *insn, int more)
{
  unsigned uid = INSN_UID (insn);
  /* Also the checks of lock loads, which the scheduler makes as it goes
     (without a clock the bundler counted their cycle as a nop).  */
  if (uid >= e2k_insn_clock.length ())
    e2k_insn_clock.safe_grow_cleared (uid + 64);
  e2k_insn_clock[uid] = e2k_sched_clock + 1;
  if (uid >= e2k_insn_ebb.length ())
    e2k_insn_ebb.safe_grow_cleared (uid + 64);
  e2k_insn_ebb[uid] = e2k_ebb_id;
  if (GET_CODE (PATTERN (insn)) == USE || GET_CODE (PATTERN (insn)) == CLOBBER)
    return more;
  return more - 1;
}

/* Bundle marks: for each insn UID, whether it opens a wide instruction,
   closes one, and how many empty cycles follow it.  */
struct e2k_mark
{
  bool open;
  bool close;
  int nops;
  /* After a conditional jump: empty cycles for the fall-through path
     only, as a wide instruction of its own before the next block.  */
  int post_nops;
  /* An empty wide instruction before this one (e2k_gen_bundles).  */
  bool lead_nop;
  /* The ALU channel chosen for the insn plus one (e2k_assign_channels),
     or 0 to let gas choose.  */
  unsigned char chan1;
};
static vec<e2k_mark> e2k_marks;

static bool
e2k_prints_p (rtx_insn *insn)
{
  if (!NONDEBUG_INSN_P (insn))
    return false;
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) == USE || GET_CODE (pat) == CLOBBER)
    return false;
  if (recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_GHOST)
    return false;
  return true;
}

static bool
e2k_asm_insn_p (rtx_insn *insn)
{
  rtx pat = PATTERN (insn);
  return GET_CODE (pat) == ASM_INPUT || asm_noperands (pat) >= 0;
}

/* Insns that print their own wide instructions and braces.  */
static bool
e2k_raw_insn_p (rtx_insn *insn)
{
  return (recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_RAW);
}

static void e2k_assign_channels (void);

/* Whether INSN takes a wide instruction of its own: a multi-insn
   sequence.  */
static bool
e2k_alone_p (rtx_insn *insn)
{
  return recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_MULTI;
}

/* Whether INSN prints a setwd, setbn or setbp: gas takes one of each per
   wide instruction, and code the scheduler didn't clock, such as one
   pipelined loop's way out followed by the next one's way in, puts two
   side by side (7-Zip's 7zUpdate.cpp).  */
static bool
e2k_setwd_type_p (rtx_insn *insn)
{
  return recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_SETWD;
}

/* Whether INSN sets a CTPR that JUMP reads.  */
static bool
e2k_writes_jump_reg_p (rtx_insn *insn, rtx_insn *jump)
{
  for (unsigned r = CTPR1_REGNUM; r <= CTPR3_REGNUM; r++)
    {
      rtx reg = gen_rtx_REG (DImode, r);
      if (reg_set_p (reg, insn)
	  && (reg_mentioned_p (reg, PATTERN (jump))
	      || (JUMP_LABEL (jump) && ANY_RETURN_P (JUMP_LABEL (jump))
		  && r == CTPR3_REGNUM)))
	return true;
    }
  return false;
}

static void
e2k_gen_bundles (void)
{
  e2k_marks.truncate (0);
  e2k_marks.safe_grow_cleared (get_max_uid () + 1);

  basic_block bb;
  /* The last insn of the block before, its instruction still open.  */
  rtx_insn *last = NULL;
  int last_clock = -1;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *end = NEXT_INSN (BB_END (bb));
      rtx_insn *prev = NULL;
      int prev_clock = -1;
      /* What the scheduler put in a conditional jump's cycle from the
	 block it falls through to, in its extended block, shares the
	 jump's wide instruction: it runs when the jump is taken too,
	 which e2k_adjust_cost allows and e2k_spec_mark makes
	 speculative.  Otherwise each such cycle cost one more.  */
      bool carry = false;
      if (last && JUMP_P (last) && !CALL_P (last) && last_clock > 0
	  && recog_memoized (last) >= 0
	  && (get_attr_type (last) == TYPE_CT
	      || get_attr_type (last) == TYPE_BRANCH)
	  && recog_memoized (last) != CODE_FOR_e2k_hwloop_end
	  && recog_memoized (last) != CODE_FOR_e2k_hwloop_end_wide
	  && !(bb->flags & BB_DISABLE_SCHEDULE)
	  && !(BLOCK_FOR_INSN (last)->flags & BB_DISABLE_SCHEDULE)
	  && !LABEL_P (BB_HEAD (bb)) && bb->prev_bb == BLOCK_FOR_INSN (last)
	  && single_pred_p (bb)
	  && (single_pred_edge (bb)->flags & EDGE_FALLTHRU)
	  && !e2k_raw_insn_p (last) && !e2k_asm_insn_p (last)
	  && !e2k_alone_p (last))
	for (rtx_insn *insn = BB_HEAD (bb); insn != end;
	     insn = NEXT_INSN (insn))
	  if (e2k_prints_p (insn))
	    {
	      unsigned u = INSN_UID (insn), lu = INSN_UID (last);
	      carry = (u < e2k_insn_clock.length ()
		       && u < e2k_insn_ebb.length ()
		       && lu < e2k_insn_ebb.length ()
		       && e2k_insn_clock[u] == last_clock
		       && e2k_insn_ebb[u] != 0
		       && e2k_insn_ebb[u] == e2k_insn_ebb[lu]
		       && GET_MODE (insn) != TImode);
	      break;
	    }
      /* The open instruction has a transfer already: one at most; and a
	 setwd, setbn or setbp.  */
      bool xfer = false, setwd = false;
      rtx_insn *carry_jump = carry ? last : NULL;
      if (carry)
	{
	  prev = last;
	  prev_clock = last_clock;
	  xfer = true;
	}
      else if (last)
	e2k_marks[INSN_UID (last)].close = true;
      last = NULL;
      /* A new cycle may start at an insn that prints nothing (a
	 blockage); carry it to the next one that prints.  */
      bool new_cycle = false;
      for (rtx_insn *insn = BB_HEAD (bb); insn != end; insn = NEXT_INSN (insn))
	{
	  if (INSN_P (insn) && GET_MODE (insn) == TImode)
	    new_cycle = true;
	  if (!e2k_prints_p (insn))
	    continue;
	  unsigned uid = INSN_UID (insn);
	  int clock = uid < e2k_insn_clock.length () ? e2k_insn_clock[uid] : 0;
	  bool open = (prev == NULL
		       || new_cycle
		       || e2k_raw_insn_p (insn) || e2k_raw_insn_p (prev)
		       || (clock > 0 && prev_clock > 0 && clock != prev_clock)
		       || e2k_asm_insn_p (insn)
		       || e2k_asm_insn_p (prev)
		       || CALL_P (prev)
		       || (JUMP_P (prev) && !(carry && clock == prev_clock))
		       /* A prepare of the CTPR the jump reads: never in one
			  instruction (v1-v5 transfer to the old target, v6
			  falls through; gas refuses it only up to v5).  */
		       || (carry && clock == last_clock
			   && carry_jump && e2k_writes_jump_reg_p (insn, carry_jump))
		       || ((JUMP_P (insn) || CALL_P (insn)) && xfer)
		       || (e2k_setwd_type_p (insn)
			   && (setwd || (carry && clock == last_clock)))
		       || e2k_alone_p (insn) || e2k_alone_p (prev));
	  if (open)
	    {
	      if (prev)
		{
		  e2k_marks[INSN_UID (prev)].close = true;
		  if (e2k_nops && clock > 0 && prev_clock > 0
		      && clock > prev_clock + 1 && !JUMP_P (prev)
		      && !CALL_P (prev))
		    e2k_marks[INSN_UID (prev)].nops = clock - prev_clock - 1;
		}
	      e2k_marks[uid].open = true;
	      xfer = false;
	      setwd = false;
	      carry_jump = NULL;
	    }
	  xfer |= JUMP_P (insn) || CALL_P (insn);
	  setwd |= e2k_setwd_type_p (insn);
	  new_cycle = false;
	  prev = insn;
	  if (clock > 0)
	    prev_clock = clock;
	}
      last = prev;
      last_clock = prev_clock;
    }
  if (last)
    e2k_marks[INSN_UID (last)].close = true;
  /* Within an extended block the scheduler's clocks go on past each
     jump: keep the cycles it left between a block and the block it falls
     through to.  Interlocks would cover most, not all: an operation in a
     wide instruction with a ct reads a predicate written one cycle before
     as it was (spec/isa/timing.md).  */
  if (e2k_nops)
    FOR_EACH_BB_FN (bb, cfun)
      {
	basic_block b = bb->next_bb;
	edge e = find_fallthru_edge (bb->succs);
	if (!e || e->dest != b)
	  continue;
	rtx_insn *last = NULL, *first = NULL, *insn;
	FOR_BB_INSNS (bb, insn)
	  if (e2k_prints_p (insn))
	    last = insn;
	FOR_BB_INSNS (b, insn)
	  if (e2k_prints_p (insn))
	    {
	      first = insn;
	      break;
	    }
	if (!last || !first || CALL_P (last))
	  continue;
	unsigned lu = INSN_UID (last), fu = INSN_UID (first);
	if (lu >= e2k_insn_clock.length () || fu >= e2k_insn_clock.length ()
	    || lu >= e2k_insn_ebb.length () || fu >= e2k_insn_ebb.length ()
	    || e2k_insn_ebb[lu] == 0 || e2k_insn_ebb[lu] != e2k_insn_ebb[fu]
	    || e2k_insn_clock[lu] == 0 || e2k_insn_clock[fu] == 0)
	  continue;
	int gap = e2k_insn_clock[fu] - e2k_insn_clock[lu] - 1;
	if (gap <= 0)
	  continue;
	if (JUMP_P (last))
	  e2k_marks[lu].post_nops = gap;
	else
	  e2k_marks[lu].nops = MAX (e2k_marks[lu].nops, gap);
      }

  /* The jumps into a block are not scheduled with it: if its first wide
     instruction transfers control and also reads a predicate in another
     operation (a merge, a predicated operation), that read doesn't wait
     for a compare in the jump's wide instruction (spec/isa/timing.md).
     Put an empty one before it.  The 2C3 reads the new value
     (E2K_PRED1).  */
  FOR_EACH_BB_FN (bb, cfun)
    {
      edge e;
      edge_iterator ei;
      bool jumped = false;
      FOR_EACH_EDGE (e, ei, bb->preds)
	jumped |= !(e->flags & EDGE_FALLTHRU);
      /* Not in a pipelined loop's kernel: its compensation code jumps
	 back into it from far away.  */
      if (!jumped || (bb->flags & BB_DISABLE_SCHEDULE) || E2K_PRED1)
	continue;
      rtx_insn *first = NULL, *insn;
      bool ct = false, pred_read = false;
      for (insn = BB_HEAD (bb); insn != NEXT_INSN (BB_END (bb));
	   insn = NEXT_INSN (insn))
	{
	  if (!e2k_prints_p (insn))
	    continue;
	  if (!first)
	    first = insn;
	  if (JUMP_P (insn))
	    ct = true;
	  else
	    {
	      subrtx_iterator::array_type array;
	      FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
		if (REG_P (*iter) && PRED_REGNO_P (REGNO (*iter))
		    && !reg_set_p (*iter, insn))
		  pred_read = true;
	    }
	  if (e2k_marks[INSN_UID (insn)].close)
	    break;
	}
      if (first && ct && pred_read)
	e2k_marks[INSN_UID (first)].lead_nop = true;
    }

  /* Check the rule above over every wide instruction: gas no longer
     does for v6.  */
  if (flag_checking)
    {
      HARD_REG_SET sets, reads;
      CLEAR_HARD_REG_SET (sets);
      CLEAR_HARD_REG_SET (reads);
      for (rtx_insn *insn = get_insns (); insn; insn = NEXT_INSN (insn))
	{
	  unsigned uid = INSN_UID (insn);
	  if (!e2k_prints_p (insn) || uid >= e2k_marks.length ()
	      || e2k_raw_insn_p (insn))
	    continue;
	  if (e2k_marks[uid].open)
	    {
	      CLEAR_HARD_REG_SET (sets);
	      CLEAR_HARD_REG_SET (reads);
	    }
	  bool xfer = JUMP_P (insn) || CALL_P (insn);
	  for (unsigned r = CTPR1_REGNUM; r <= CTPR3_REGNUM; r++)
	    {
	      rtx reg = gen_rtx_REG (DImode, r);
	      if (!xfer && reg_set_p (reg, insn))
		SET_HARD_REG_BIT (sets, r);
	      if (xfer
		  && (reg_mentioned_p (reg, PATTERN (insn))
		      || (JUMP_P (insn) && JUMP_LABEL (insn)
			  && ANY_RETURN_P (JUMP_LABEL (insn))
			  && r == CTPR3_REGNUM)))
		SET_HARD_REG_BIT (reads, r);
	    }
	  gcc_assert (!hard_reg_set_intersect_p (sets, reads));
	}
    }

  if (e2k_channels)
    e2k_assign_channels ();
}

/* Channels.  The six ALU channels form two clusters, ALC0-2 and ALC3-5,
   and a result reaches the other cluster later: integer results and
   loads one cycle, FP-class results two, which an integer consumer pays
   anyway (spec/isa/timing.md, "Clusters").  gas gives each operation the
   first free channel it allows, so a consumer the scheduler placed right
   after its producer often lands in the other cluster and stalls a whole
   4-cycle step.  Choose the channels here instead, per wide instruction,
   keeping consumers in their producers' clusters where the channel sets
   allow.  */

/* What a result is: packed results reach integer operations, and
   anything in the other cluster, at 4 (spec/isa/timing.md).  */
enum e2k_rkind { E2K_RK_NONE, E2K_RK_INT, E2K_RK_LOAD, E2K_RK_FP,
		 E2K_RK_PACKED };

/* The channels INSN may take (spec/isa/binutils-ops.yaml for v3, as in
   e2k-sched.md), 0 if it takes none, -1 if they are not known here.  A
   lock or check load prints its own channel: *FIXED is it and *BUSY the
   channels it keeps free of others.  */
static int
e2k_chan_set (rtx_insn *insn, int *fixed, int *busy, enum e2k_rkind *kind)
{
  *fixed = -1;
  *busy = 0;
  *kind = E2K_RK_INT;
  if (e2k_asm_insn_p (insn) || recog_memoized (insn) < 0)
    return -1;
  switch (get_attr_type (insn))
    {
    case TYPE_ALU:
      return 0x3f;
    case TYPE_ALU14:
      return 0x12;
    case TYPE_ALU0134:
      return 0x1b;
    case TYPE_CMP:
      return 0x1b;
    case TYPE_FP:
    case TYPE_FMA:
    case TYPE_FFMA:
      /* v4 added ALC2 and ALC5 for FP add, subtract, multiply and the
	 combined operations (e2k-sched.md, "e2k_fp6").  */
      *kind = E2K_RK_FP;
      return e2k_arch >= 4 ? 0x3f : 0x1b;
    case TYPE_MUL:
    case TYPE_FCVT:
    case TYPE_FCMP:
      *kind = E2K_RK_FP;
      return 0x1b;
    case TYPE_FDIV:
      *kind = E2K_RK_FP;
      return 0x20;
    case TYPE_DIV:
      return 0x20;
    case TYPE_PINT:
      *kind = E2K_RK_PACKED;
      return 0x09;
    case TYPE_PINT14:
    case TYPE_PMUL:
      *kind = E2K_RK_PACKED;
      return 0x12;
    case TYPE_PANY:
      *kind = E2K_RK_PACKED;
      return 0x1b;
    /* Array prefetch: movas in the AAS channels, at 5 cycles to any
       consumer; AAU register writes in ALC2/5.  */
    case TYPE_MOVA:
    case TYPE_BAP:
      *kind = E2K_RK_NONE;
      return 0;
    case TYPE_AAU:
      *kind = E2K_RK_NONE;
      return 0x24;
    case TYPE_LOAD:
      *kind = E2K_RK_LOAD;
      return 0x2d;
    case TYPE_STORE:
      *kind = E2K_RK_NONE;
      return 0x24;
    case TYPE_GETSP:
    case TYPE_MOVCTP:
      return 0x01;
    case TYPE_LDLOCK:
      *kind = E2K_RK_LOAD;
      *fixed = 0;
      *busy = 0x25;
      return 0;
    case TYPE_LDCHK:
      *kind = E2K_RK_LOAD;
      *fixed = 5;
      *busy = 0x24;
      return 0;
    case TYPE_DISP:
    case TYPE_RET:
    case TYPE_BRANCH:
    case TYPE_CT:
    case TYPE_CALL:
    case TYPE_WAIT:
    case TYPE_GHOST:
    case TYPE_PLOG:
    case TYPE_SETWD:
      *kind = E2K_RK_NONE;
      return 0;
    default:
      return -1;
    }
}

/* The last write of each register: its wide instruction, latency,
   cluster (-1 if not known) and kind.  */
struct e2k_chan_prod
{
  int pos;
  int lat;
  int cl;
  enum e2k_rkind kind;
  /* A predicated producer's predicate (else -1), and whether it runs
     when the predicate is false.  */
  int pred;
  bool inv;
  /* An FP-side result a write-back conflict delays by a cycle.  */
  bool late;
};

struct e2k_chan_use_data
{
  int regs[16];
  /* A store's data: it reads an FP-side result as an FP operation does,
     2 cycles later only from the other cluster (relcc2 findings I44).  */
  bool fp[16];
  int n;
};

static void
e2k_chan_note_use (rtx *loc, void *data)
{
  e2k_chan_use_data *d = (e2k_chan_use_data *) data;
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, *loc, NONCONST)
    if (REG_P (*iter) && GPR_REGNO_P (REGNO (*iter)) && d->n < 16)
      d->regs[d->n++] = REGNO (*iter);
}

/* Whether INSN is a check load: it waits for nothing of its lock load,
   and a use of its register in the next instruction issues as if it
   were not there (tools/isa-probes on the 4C and 8C2, relcc2 findings
   I30): for the channels and stalls its register keeps the lock load's
   value.  */
static bool
e2k_chan_check_p (rtx_insn *insn)
{
  return recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_LDCHK;
}

/* The registers INSN reads, for e2k_chan_early.  */
static void
e2k_chan_uses (rtx_insn *insn, e2k_chan_use_data *d)
{
  d->n = 0;
  note_uses (&PATTERN (insn), e2k_chan_note_use, d);
  for (int j = 0; j < d->n; j++)
    d->fp[j] = false;
  if (recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_STORE)
    {
      rtx set = PATTERN (insn);
      if (GET_CODE (set) == COND_EXEC)
	set = COND_EXEC_CODE (set);
      if (GET_CODE (set) == PARALLEL)
	set = XVECEXP (set, 0, 0);
      rtx src = GET_CODE (set) == SET ? SET_SRC (set) : NULL_RTX;
      if (src && SUBREG_P (src))
	src = SUBREG_REG (src);
      if (src && REG_P (src))
	for (int j = 0; j < d->n; j++)
	  d->fp[j] = IN_RANGE (d->regs[j], (int) REGNO (src),
			       (int) END_REGNO (src) - 1);
    }
  if (!e2k_chan_check_p (insn))
    return;
  rtx set = PATTERN (insn);
  if (GET_CODE (set) == COND_EXEC)
    set = COND_EXEC_CODE (set);
  /* A pipelined loop's check and its jump (e2k_ldchk_jump).  */
  if (GET_CODE (set) == PARALLEL)
    set = XVECEXP (set, 0, 0);
  int k = 0;
  for (int j = 0; j < d->n; j++)
    if (d->regs[j] != (int) REGNO (SET_DEST (set)))
      d->regs[k++] = d->regs[j];
  d->n = k;
}

/* The table of e2k_assign_channels, and each register's producer before
   the last one: a consumer under the predicate opposite to the last
   one's reads that one's value (the two arms of an if-converted if-else
   that share a register).  */
static e2k_chan_prod e2k_chan_tab[FIRST_PSEUDO_REGISTER];
static e2k_chan_prod e2k_chan_prev[FIRST_PSEUDO_REGISTER];

/* Write-back conflicts (spec/isa/timing.md): an FP-side result (FP
   operation, integer multiply) bound for an integer operation, or for an
   FP one in the other cluster, comes a cycle late when an ALU operation
   or a load issues in its channel 2 cycles after it.  The last FP-side
   operation of each channel: its position and its result.  */
#define E2K_WB_DISTANCE 2
static int e2k_chan_fp_pos[6];
static int e2k_chan_fp_reg[6];

/* The predicate INSN runs under in *PRED (-1: none) and *INV.  */
static void
e2k_chan_pred (rtx_insn *insn, int *pred, bool *inv)
{
  *pred = -1;
  *inv = false;
  if (GET_CODE (PATTERN (insn)) == COND_EXEC)
    {
      rtx c = COND_EXEC_TEST (PATTERN (insn));
      if (REG_P (XEXP (c, 0)))
	{
	  *pred = REGNO (XEXP (c, 0));
	  *inv = GET_CODE (c) == EQ;
	}
    }
}

/* Forget every register's producers.  */
static void
e2k_chan_clear (e2k_chan_prod *tab)
{
  for (int r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    {
      tab[r].kind = E2K_RK_NONE;
      e2k_chan_prev[r].kind = E2K_RK_NONE;
    }
  for (int c = 0; c < 6; c++)
    e2k_chan_fp_pos[c] = INT_MIN / 2;
}

/* Pipelined loops (e2k_modsched): for each prologue insn's UID, its
   node's insn in the kernel (whose channel it takes, so that a value
   an operation passes to its own next instance doesn't cross between
   the clusters on the way into the kernel); and the kernels' blocks
   (the second -1, or the block after a check that splits it).  */
static vec<int> e2k_ms_twin;
static vec<std::pair<int, int> > e2k_ms_kernels;
/* The number of rotating registers of each kernel's ring.  */
static vec<int> e2k_ms_kernel_rings;

static void
e2k_chan_note_def (rtx x, const_rtx, void *data)
{
  if (SUBREG_P (x))
    x = SUBREG_REG (x);
  if (!REG_P (x) || !HARD_REGISTER_P (x))
    return;
  for (unsigned r = REGNO (x); r < END_REGNO (x); r++)
    {
      e2k_chan_prev[r] = e2k_chan_tab[r];
      e2k_chan_tab[r] = *(e2k_chan_prod *) data;
    }
}

/* Cycles a consumer in channel C at position POS waits for the value of
   producer P, rounded up to the 4-cycle stall steps (spec/isa/timing.md).  */
static int
e2k_chan_stall_1 (const e2k_chan_prod &p, int c, int pos, bool fp)
{
  if (p.kind == E2K_RK_NONE || p.cl < 0)
    return 0;
  bool other = c / 3 != p.cl;
  int lat = p.lat;
  if (p.kind == E2K_RK_FP)
    lat += (other || !fp) ? 2 + p.late : 0;
  else if (p.kind == E2K_RK_PACKED)
    lat = (other || !fp) ? MAX (lat, 4) : lat;
  /* A v6 load costs its 5 cycles in either cluster.  */
  else if (!(p.kind == E2K_RK_LOAD && E2K_LAT6))
    lat += other;
  int e = lat - (pos - p.pos);
  return e > 0 ? 4 * ((e + 3) / 4) : 0;
}

/* The same for register R, from TAB, for a consumer under predicate PRED
   (INV as e2k_chan_pred).  */
static int
e2k_chan_stall (const e2k_chan_prod *tab, int r, int c, int pos, bool fp,
		int pred, bool inv)
{
  const e2k_chan_prod &p = tab[r];
  if (p.pred < 0 || p.kind == E2K_RK_NONE)
    return e2k_chan_stall_1 (p, c, pos, fp);
  if (p.pred == pred && p.inv != inv)
    return e2k_chan_stall_1 (e2k_chan_prev[r], c, pos, fp);
  if (p.pred == pred)
    return e2k_chan_stall_1 (p, c, pos, fp);
  return MAX (e2k_chan_stall_1 (p, c, pos, fp),
	      e2k_chan_stall_1 (e2k_chan_prev[r], c, pos, fp));
}

/* How many cycles early register R, from TAB, is for channel C at POS
   (e2k_chan_stall's E).  */
static int
e2k_chan_early (const e2k_chan_prod *tab, int r, int c, int pos, bool fp,
		int pred, bool inv)
{
  int s = e2k_chan_stall (tab, r, c, pos, fp, pred, inv);
  if (!s)
    return 0;
  for (int e = 1; e <= s; e++)
    if (e2k_chan_stall (tab, r, c, pos + e, fp, pred, inv) == 0)
      return e;
  return s;
}

/* Give the operations of a wide instruction at POS their channels, the
   ones whose operands come soonest (TAB: what each register's producer
   was).  With PAD, returns how many empty cycles to put before it, the
   most an operand is still early by up to 3: an early operand stalls 4
   cycles (spec/isa/timing.md), the empty cycles cost what they are
   (a load result or a value crossing the clusters one cycle late: crc32's
   braid, 6 stalls in 46 cycles).  */
static int
e2k_chan_bundle (rtx_insn **ops, int n, int pos, e2k_chan_prod *tab,
		 bool pad)
{
  int set[8], fixed[8], cost[8][6], chan[8], pred[8];
  bool load[8], store[8], fpo[8], inv[8];
  int busy = 0;
  bool ok = n <= 8;
  for (int i = 0; ok && i < n; i++)
    {
      int b;
      enum e2k_rkind kind;
      set[i] = e2k_chan_set (ops[i], &fixed[i], &b, &kind);
      if (set[i] < 0)
	{
	  ok = false;
	  break;
	}
      busy |= b;
      chan[i] = fixed[i];
      /* A channel chosen before stays: a kernel's (e2k_assign_channels
	 does those first), or its node's in the kernel for a prologue
	 instance.  */
      unsigned uid = INSN_UID (ops[i]);
      int pin = e2k_marks[uid].chan1 - 1;
      if (pin < 0 && uid < e2k_ms_twin.length () && e2k_ms_twin[uid])
	pin = e2k_marks[e2k_ms_twin[uid]].chan1 - 1;
      if (pin >= 0 && set[i] > 0 && (set[i] & (1 << pin)))
	set[i] = 1 << pin;
      enum attr_type t = get_attr_type (ops[i]);
      load[i] = t == TYPE_LOAD;
      store[i] = t == TYPE_STORE;
      bool fp = (t == TYPE_FP || t == TYPE_FMA || t == TYPE_FFMA
		 || t == TYPE_FCVT
		 || t == TYPE_MUL || t == TYPE_FCMP || t == TYPE_FDIV
		 || e2k_packed_type_p (t));
      fpo[i] = fp;
      e2k_chan_pred (ops[i], &pred[i], &inv[i]);
      e2k_chan_use_data d;
      e2k_chan_uses (ops[i], &d);
      for (int c = 0; c < 6; c++)
	{
	  cost[i][c] = 0;
	  if (set[i] & (1 << c))
	    for (int k = 0; k < d.n; k++)
	      cost[i][c] += e2k_chan_stall (tab, d.regs[k], c, pos,
					    fp || d.fp[k], pred[i], inv[i]);
	  /* Half a stall step for delaying an FP-side result (its consumer
	     may have slack).  */
	  if ((set[i] & (1 << c)) && !fp && !store[i]
	      && e2k_chan_fp_pos[c] == pos - E2K_WB_DISTANCE)
	    cost[i][c] += 2;
	}
    }

  if (ok)
    {
      /* Search every assignment; the first best one (the lowest channels
	 in order, as gas picks) wins ties.  */
      int best = INT_MAX, cur[8], bestc[8];
      int i = 0, used = busy;
      for (int k = 0; k < n; k++)
	cur[k] = -1;
      auto search = [&] (auto &&self, int i, int used, int sum) -> void
	{
	  if (sum >= best)
	    return;
	  if (i == n)
	    {
	      /* gas: no store in ALC2 with a load in ALC3, nor in ALC5
		 with a load in ALC0 (spec/isa/bundle.md).  */
	      bool st2 = false, st5 = false, ld0 = false, ld3 = false;
	      for (int k = 0; k < n; k++)
		{
		  st2 |= store[k] && cur[k] == 2;
		  st5 |= store[k] && cur[k] == 5;
		  ld0 |= load[k] && cur[k] == 0;
		  ld3 |= load[k] && cur[k] == 3;
		}
	      if ((st2 && ld3) || (st5 && ld0))
		return;
	      best = sum;
	      memcpy (bestc, cur, sizeof cur);
	      return;
	    }
	  if (set[i] == 0)
	    {
	      self (self, i + 1, used, sum);
	      return;
	    }
	  for (int c = 0; c < 6; c++)
	    if ((set[i] & (1 << c)) && !(used & (1 << c)))
	      {
		cur[i] = c;
		self (self, i + 1, used | (1 << c), sum + cost[i][c]);
	      }
	  cur[i] = -1;
	};
      search (search, i, used, 0);
      if (best == INT_MAX)
	ok = false;
      else
	for (int k = 0; k < n; k++)
	  if (set[k] > 0)
	    {
	      chan[k] = bestc[k];
	      e2k_marks[INSN_UID (ops[k])].chan1 = bestc[k] + 1;
	    }
    }

  int delay = 0;
  if (ok && pad)
    for (int i = 0; i < n; i++)
      if (chan[i] >= 0 && chan[i] < 6)
	{
	  e2k_chan_use_data d;
	  e2k_chan_uses (ops[i], &d);
	  for (int k = 0; k < d.n; k++)
	    delay = MAX (delay, e2k_chan_early (tab, d.regs[k], chan[i], pos,
						 fpo[i] || d.fp[k], pred[i],
						 inv[i]));
	}
  if (delay > 3)
    delay = 0;
  pos += delay;

  /* Record the results.  */
  for (int i = 0; i < n; i++)
    {
      rtx_insn *insn = ops[i];
      if (CALL_P (insn))
	{
	  e2k_chan_clear (tab);
	  continue;
	}
      int f, b;
      enum e2k_rkind kind;
      if (e2k_chan_set (insn, &f, &b, &kind) < 0)
	kind = E2K_RK_NONE;
      int cl = ok && chan[i] >= 0 ? chan[i] / 3 : -1;
      int lat = recog_memoized (insn) >= 0 ? insn_default_latency (insn) : 1;
      e2k_chan_prod p = { pos, lat, cl, kind, -1, false, false };
      e2k_chan_pred (insn, &p.pred, &p.inv);
      if (!e2k_chan_check_p (insn))
	note_stores (insn, e2k_chan_note_def, &p);
    }
  /* Write-back conflicts this instruction makes, then its FP-side
     results.  */
  for (int i = 0; ok && i < n; i++)
    if (chan[i] >= 0 && chan[i] < 6 && !fpo[i] && !store[i]
	&& !CALL_P (ops[i]) && e2k_chan_fp_pos[chan[i]] == pos - E2K_WB_DISTANCE)
      {
	int r = e2k_chan_fp_reg[chan[i]];
	if (r >= 0 && tab[r].kind == E2K_RK_FP
	    && tab[r].pos == pos - E2K_WB_DISTANCE && tab[r].cl == chan[i] / 3)
	  tab[r].late = true;
      }
  for (int i = 0; ok && i < n; i++)
    if (chan[i] >= 0 && chan[i] < 6 && fpo[i] && !CALL_P (ops[i]))
      {
	rtx set = single_set (ops[i]);
	rtx d = set ? SET_DEST (set) : NULL_RTX;
	if (d && SUBREG_P (d))
	  d = SUBREG_REG (d);
	e2k_chan_fp_pos[chan[i]] = pos;
	e2k_chan_fp_reg[chan[i]] = d && REG_P (d) && GPR_REGNO_P (REGNO (d))
				   ? (int) REGNO (d) : -1;
      }
  return delay;
}

/* Assign the channels of the wide instructions from FROM to before TO,
   the first at position *POS; with PAD, put empty cycles where they save
   a stall (e2k_chan_bundle) after a wide instruction that only falls
   through to the next.  */
static void
e2k_chan_range (rtx_insn *from, rtx_insn *to, int *pos, e2k_chan_prod *tab,
		bool pad)
{
  rtx_insn *ops[8];
  int n = 0;
  bool over = false;
  rtx_insn *prev = NULL;
  for (rtx_insn *insn = from; insn != to; insn = NEXT_INSN (insn))
    {
      if (LABEL_P (insn))
	prev = NULL;
      if (!e2k_prints_p (insn))
	continue;
      e2k_mark &m = e2k_marks[INSN_UID (insn)];
      if (m.open)
	{
	  n = 0;
	  over = false;
	}
      if (n < 8)
	ops[n++] = insn;
      else
	over = true;
      if (m.close)
	{
	  bool can = (pad && prev && !JUMP_P (prev) && !CALL_P (prev)
		      && !e2k_marks[INSN_UID (prev)].post_nops
		      && !e2k_marks[INSN_UID (ops[0])].lead_nop);
	  int delay = over ? 0 : e2k_chan_bundle (ops, n, *pos, tab, can);
	  if (delay)
	    {
	      e2k_marks[INSN_UID (prev)].nops += delay;
	      *pos += delay;
	    }
	  *pos += 1 + m.nops;
	  n = 0;
	  prev = insn;
	}
    }
}

/* abn: what an iteration writes as %b[N] the next one reads as %b[N + 2],
   in a ring of RING registers (spec/isa/loops.md): move the producers of
   the table accordingly.  */
static void
e2k_chan_rotate (int ring)
{
  if (ring <= 0 || ring > E2K_ROT_MAX)
    return;
  e2k_chan_prod t[E2K_ROT_MAX], p[E2K_ROT_MAX];
  for (int n = 0; n < ring; n++)
    {
      t[(n + 2) % ring] = e2k_chan_tab[E2K_ROT_REGNO (n)];
      p[(n + 2) % ring] = e2k_chan_prev[E2K_ROT_REGNO (n)];
    }
  for (int n = 0; n < ring; n++)
    {
      e2k_chan_tab[E2K_ROT_REGNO (n)] = t[n];
      e2k_chan_prev[E2K_ROT_REGNO (n)] = p[n];
    }
}

/* Assign the channels of FROM .. TO, a loop body, in its steady state:
   twice round, the second time with what the first left in the table
   (rotated by abn's step for a kernel's ring of RING registers).  */
static void
e2k_chan_loop (rtx_insn *from, rtx_insn *to, int ring)
{
  e2k_chan_prod *tab = e2k_chan_tab;
  e2k_chan_clear (tab);
  int pos = 0;
  for (int round = 0; round < 2; round++)
    {
      if (round)
	{
	  e2k_chan_rotate (ring);
	  for (rtx_insn *insn = from; insn != to; insn = NEXT_INSN (insn))
	    e2k_marks[INSN_UID (insn)].chan1 = 0;
	}
      e2k_chan_range (from, to, &pos, tab, false);
    }
}

static void
e2k_assign_channels (void)
{
  e2k_chan_prod *tab = e2k_chan_tab;
  /* Kernels first, in their steady state.  */
  auto_bitmap kernel_bbs;
  for (unsigned i = 0; i < e2k_ms_kernels.length (); i++)
    {
      std::pair<int, int> &k = e2k_ms_kernels[i];
      basic_block b1 = BASIC_BLOCK_FOR_FN (cfun, k.first);
      basic_block b2 = k.second >= 0 ? BASIC_BLOCK_FOR_FN (cfun, k.second) : b1;
      if (!b1 || !b2)
	continue;
      bitmap_set_bit (kernel_bbs, b1->index);
      bitmap_set_bit (kernel_bbs, b2->index);
      e2k_chan_loop (BB_HEAD (b1), NEXT_INSN (BB_END (b2)),
		     i < e2k_ms_kernel_rings.length ()
		     ? e2k_ms_kernel_rings[i] : 0);
    }
  /* So are the other loops of one block: their first instruction reads
     what their last one wrote (xz's crc64 loop stalled 4 cycles an
     iteration on a value crossing the clusters back to the top).  */
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    if (!bitmap_bit_p (kernel_bbs, bb->index)
	&& find_edge (bb, bb) && !(bb->flags & BB_DISABLE_SCHEDULE))
      e2k_chan_loop (BB_HEAD (bb), NEXT_INSN (BB_END (bb)), 0);
  e2k_chan_clear (tab);
  int pos = 0;
  e2k_chan_range (get_insns (), NULL, &pos, tab, e2k_nops);
}

static unsigned e2k_ms_flag (const rtx_insn *);

/* The channel chosen for the insn being printed, or -1.  */
static int
e2k_cur_chan (void)
{
  if (!e2k_bundling || !current_output_insn)
    return -1;
  unsigned uid = INSN_UID (current_output_insn);
  return uid < e2k_marks.length () ? e2k_marks[uid].chan1 - 1 : -1;
}

/* Data speculation labels (see e2k_output_spec_load).  */
static int e2k_dam_labelno;
static vec<int> e2k_dam_pending;	/* labels to print after the bundle */
static vec<int> e2k_dam_stubs;		/* stubs to print at the end */
/* Array prefetch programs (e2k_ms_apb_assign), printed after the
   function as lcc places them; loops that the profile or their count
   says run fewer than E2K_APB_MIN_TRIP times use it only when it
   shortens the kernel (e2k_ms_pipeline).  */
#define E2K_APB_MIN_TRIP 256
static int e2k_apb_labelno;
static vec<char *> e2k_apb_progs;

/* vlc: the count is valid (spec/isa/loops.md, %lsr bit 37).  */
#define E2K_LSR_VLC (HOST_WIDE_INT_1 << 37)
static bool e2k_fold_vlc (basic_block, rtx);

/* Strip-mined loops run chunks of this many iterations (a power of two
   below lcc's 0x3ffffe0), the first one shorter.  */
#define E2K_LSR_CHUNK (HOST_WIDE_INT_1 << 25)

/* Strip-mined loop ends (see e2k_output_hwloop_end_wide): the test for
   another chunk to print after the bundle, and the stubs.  */
struct e2k_hw_stub { int n; rtx ops[3]; };
static int e2k_hw_labelno;
static vec<e2k_hw_stub> e2k_hw_pending;
static vec<e2k_hw_stub> e2k_hw_stubs;

static void
e2k_dam_print_pending (FILE *f)
{
  for (int n : e2k_dam_pending)
    fprintf (f, ".LDAMB%d:\n", n);
  e2k_dam_pending.truncate (0);
  for (e2k_hw_stub &h : e2k_hw_pending)
    {
      output_asm_insn ("{\n\tcmpedb\t%1, 0, %2\n\t}", h.ops);
      fprintf (f, "\t{\n\tibranch\t.LHW%d ? ~", h.n);
      output_operand (h.ops[2], 0);
      fputs ("\n\t}\n", f);
    }
  e2k_hw_pending.truncate (0);
}

/* The wait before a hardware loop (e2k_lsr_wait, INSN): the loop may
   start 4 cycles after rwd %lsr (spec/isa/loops.md; v3-v5 run one
   iteration too many when it starts sooner, v6 only one).  Count the
   cycles of the wide instructions since rwd, printed before INSN, and
   wait out the rest.  Anything not counted exactly (a label, which
   another way in may reach, a multi-insn or raw sequence, asm) counts
   as no cycles, so the wait is never short.  */
const char *
e2k_output_lsr_wait (rtx_insn *insn)
{
  int cycles = 0;
  bool found = false;
  if (e2k_bundling)
    for (rtx_insn *x = PREV_INSN (insn); x; x = PREV_INSN (x))
      {
	if (LABEL_P (x) || BARRIER_P (x))
	  break;
	if (!NONDEBUG_INSN_P (x) || !e2k_prints_p (x))
	  continue;
	unsigned uid = INSN_UID (x);
	if (e2k_asm_insn_p (x) || e2k_raw_insn_p (x)
	    || uid >= e2k_marks.length ())
	  continue;
	if (recog_memoized (x) >= 0 && get_attr_type (x) == TYPE_MULTI)
	  continue;
	if (e2k_marks[uid].close)
	  cycles += 1 + e2k_marks[uid].nops + e2k_marks[uid].post_nops;
	if (recog_memoized (x) == CODE_FOR_e2k_rwd_lsr)
	  {
	    found = true;
	    break;
	  }
	if (e2k_marks[uid].lead_nop)
	  cycles += 1;
      }
  int wait = found ? 4 - cycles : 4;
  if (wait <= 0)
    return "";
  static char buf[32];
  snprintf (buf, sizeof buf, "{\n\tnop\t%d\n\t}", wait - 1);
  return buf;
}

/* N empty cycles as wide instructions of their own, each one cycle and
   up to 7 nops (the HS field).  Cutting a longer wait short makes the
   consumer issue early, and an interlock stall costs about a whole
   latency more (spec/isa/timing.md): a divide's 11 cycles became 21.  */
static void
e2k_print_empty (FILE *f, int n)
{
  while (n > 0)
    {
      int k = MIN (n - 1, 7);
      fprintf (f, "\t{\n\tnop\t%d\n\t}\n", k);
      n -= k + 1;
    }
}

void
e2k_final_prescan_insn (rtx_insn *insn)
{
  if (!INSN_P (insn))
    return;
  /* gas pads user asm as lcc does (.accept strict_delay around it).  */
  if (e2k_asm_insn_p (insn))
    {
      fputs ("\t.accept\tstrict_delay\n", asm_out_file);
      return;
    }
  e2k_cur_sm = (e2k_ms_flag (insn) & 1) != 0;
  if (!e2k_bundling)
    return;
  unsigned uid = INSN_UID (insn);
  if (uid < e2k_marks.length () && e2k_marks[uid].open && !e2k_in_bundle
      && e2k_prints_p (insn) && !e2k_raw_insn_p (insn))
    {
      if (e2k_marks[uid].lead_nop)
	fputs ("\t{\n\tnop\t0\n\t}\n", asm_out_file);
      fputs ("\t{\n", asm_out_file);
      e2k_in_bundle = true;
    }
}

static void
e2k_final_postscan_insn (FILE *f, rtx_insn *insn, rtx *, int)
{
  e2k_cur_sm = false;
  if (e2k_asm_insn_p (insn))
    {
      fputs ("\t.ignore\tstrict_delay\n", f);
      return;
    }
  if (!e2k_bundling)
    {
      e2k_dam_print_pending (f);
      return;
    }
  unsigned uid = INSN_UID (insn);
  if (e2k_in_bundle && uid < e2k_marks.length () && e2k_marks[uid].close)
    {
      int nops = e2k_marks[uid].nops;
      if (nops)
	fprintf (f, "\tnop\t%d\n", MIN (nops, 7));
      fputs ("\t}\n", f);
      e2k_in_bundle = false;
      e2k_dam_print_pending (f);
      e2k_print_empty (f, nops - MIN (nops, 7));
      e2k_print_empty (f, e2k_marks[uid].post_nops);
    }
}

const char *
e2k_asm_output_opcode (FILE *f, const char *code)
{
  /* "addd,3" (e2k_assign_channels), "addd,sm" (a pipelined loop's
     operation), "addd,3,sm".  A mnemonic with an operand in it prints
     its channel with "%,".  */
  int chan = e2k_cur_chan ();
  if (!e2k_cur_sm && chan < 0)
    return code;
  const char *p = code;
  while (*p && *p != '\t' && *p != ' ' && *p != '\n' && *p != ','
	 && *p != '%')
    p++;
  if (*p == '%')
    return code;
  fwrite (code, 1, p - code, f);
  if (chan >= 0)
    fprintf (f, ",%d", chan);
  if (e2k_cur_sm)
    fputs (",sm", f);
  return p;
}

static void
e2k_asm_function_prologue (FILE *)
{
  e2k_in_bundle = false;
}

static void
e2k_asm_function_epilogue (FILE *f)
{
  if (e2k_in_bundle)
    fputs ("\t}\n", f);
  e2k_in_bundle = false;
  e2k_bundling = false;
  e2k_dam_print_pending (f);
  for (int n : e2k_dam_stubs)
    fprintf (f, ".LDAM%d:\n\t{\n\tibranch\t.LDAMB%d\n\t}\n", n, n);
  e2k_dam_stubs.truncate (0);
  for (char *p : e2k_apb_progs)
    {
      fputs (p, f);
      free (p);
    }
  e2k_apb_progs.truncate (0);
  for (e2k_hw_stub &h : e2k_hw_stubs)
    {
      char buf[128];
      snprintf (buf, sizeof buf,
		"{\n\tsubd\t%%1, %#" PRIx64 ", %%1\n\trwd\t%#" PRIx64
		", %%%%lsr\n\tnop\t3\n\t}\n\t{\n\tct\t%%0\n\t}",
		(uint64_t) E2K_LSR_CHUNK,
		(uint64_t) (E2K_LSR_CHUNK | E2K_LSR_VLC));
      fprintf (f, ".LHW%d:\n", h.n);
      output_asm_insn (buf, h.ops);
    }
  e2k_hw_stubs.truncate (0);
}

/* The end of a strip-mined loop (e2k_hwloop_end_wide; OPERANDS: CTPR,
   label, iterations left, predicate).  When the chunk is done and
   iterations are left, the stub takes the next chunk: %lsr = CHUNK |
   vlc, at least 4 cycles before the CTPR's transfer back to the loop.
   Strip-mined loops are rare enough that the test after the loop
   needn't share wide instructions with the code that follows.  */
const char *
e2k_output_hwloop_end_wide (rtx_insn *insn, rtx *operands)
{
  e2k_hw_stub h;
  h.n = ++e2k_hw_labelno;
  h.ops[0] = operands[0];
  h.ops[1] = operands[2];
  h.ops[2] = operands[3];
  e2k_hw_pending.safe_push (h);
  e2k_hw_stubs.safe_push (h);
  return e2k_output_hwloop_end (insn);
}

/* Close innermost loops with a prepared transfer: "disp %ctprN, header"
   on the preheader edge and "ct %ctprN ? pred" in place of the latch's
   ibranch.  A taken ibranch costs 6 cycles on the 4C; a ct whose CTPR
   was prepared at least 5 cycles before costs nothing, and the CTPR keeps
   its target across iterations.  Calls clobber every CTPR, so loops with
   calls keep their ibranch.  */
static bool
e2k_jump_to_label_p (rtx_insn *jump, rtx label)
{
  if (!JUMP_P (jump) || JUMP_LABEL (jump) != label)
    return false;
  rtx pat = PATTERN (jump);
  if (GET_CODE (pat) != SET || SET_DEST (pat) != pc_rtx)
    return false;
  if (simplejump_p (jump))
    return true;
  rtx src = SET_SRC (pat);
  return (any_condjump_p (jump) && GET_CODE (src) == IF_THEN_ELSE
	  && GET_CODE (XEXP (src, 1)) == LABEL_REF
	  && XEXP (src, 2) == pc_rtx);
}

static void
e2k_prepare_loop_branches (void)
{
  loop_optimizer_init (AVOID_CFG_MODIFICATIONS);
  bool changed = false;

  for (auto loop : loops_list (cfun, LI_ONLY_INNERMOST))
    {
      basic_block header = loop->header;
      rtx label = block_label (header);

      /* Pick a CTPR nothing in the loop touches; calls clobber them all.  */
      bool has_call = false, uses[3] = { false, false, false };
      basic_block *body = get_loop_body (loop);
      for (unsigned i = 0; i < loop->num_nodes; i++)
	{
	  rtx_insn *insn;
	  FOR_BB_INSNS (body[i], insn)
	    {
	      if (!INSN_P (insn))
		continue;
	      if (CALL_P (insn))
		has_call = true;
	      for (int k = 0; k < 3; k++)
		if (reg_mentioned_p (gen_rtx_REG (DImode, CTPR1_REGNUM + k),
				     PATTERN (insn)))
		  uses[k] = true;
	    }
	}
      free (body);
      int k = !uses[1] ? 1 : !uses[0] ? 0 : -1;
      if (has_call || k < 0)
	continue;
      rtx ctpr = gen_rtx_REG (DImode, CTPR1_REGNUM + k);

      /* Edges entering the loop each get a disp; jumps along back edges
	 become ct.  */
      auto_vec<edge> entries;
      auto_vec<rtx_insn *> latches;
      edge e;
      edge_iterator ei;
      bool bad = false;
      FOR_EACH_EDGE (e, ei, header->preds)
	{
	  if (e->flags & EDGE_ABNORMAL)
	    bad = true;
	  else if (!flow_bb_inside_loop_p (loop, e->src))
	    entries.safe_push (e);
	  else if (e2k_jump_to_label_p (BB_END (e->src), label))
	    latches.safe_push (BB_END (e->src));
	}
      if (bad || entries.is_empty () || latches.is_empty ())
	continue;

      for (rtx_insn *jump : latches)
	{
	  rtx newpat
	    = gen_rtx_PARALLEL (VOIDmode,
				gen_rtvec (2, copy_rtx (PATTERN (jump)),
					   gen_rtx_USE (VOIDmode, ctpr)));
	  validate_change (jump, &PATTERN (jump), newpat, 1);
	}
      if (!apply_change_group ())
	continue;

      for (edge en : entries)
	{
	  start_sequence ();
	  rtx_insn *disp = emit_insn (gen_e2k_disp_label (ctpr, label));
	  add_reg_note (disp, REG_LABEL_OPERAND, label);
	  LABEL_NUSES (label)++;
	  rtx_insn *seq = end_sequence ();
	  insert_insn_on_edge (seq, en);
	}
      changed = true;
    }

  if (changed)
    commit_edge_insertions ();
  loop_optimizer_finalize ();
}

/* Prepare the other branches too: a taken ibranch costs 6 cycles, a ct
   whose disp is D cycles before it max (0, 5 - D) taken and nothing not
   taken once D >= 2 (spec/isa/control-transfer.md, "Costs").  A branch
   gets "disp %ctprK, target" right before it if some CTPR is dead after
   it, and becomes "ct %ctprK"; the scheduler then moves the disp up, the
   CTPRs taken in turn so that it can pass the transfers before.  Run
   again after e2k_modsched (AFTER_MS) for the branches it makes on the
   ways out of the loops it pipelines, leaving its own clocked blocks.  */
static void
e2k_prepare_branches (bool after_ms)
{
  df_analyze ();
  basic_block bb;
  int next = 0;
  bool changed = false;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *jump = BB_END (bb);
      if (!JUMP_P (jump) || recog_memoized (jump) < 0
	  || get_attr_type (jump) != TYPE_BRANCH
	  || (after_ms && (bb->flags & BB_DISABLE_SCHEDULE)))
	continue;
      rtx pat = PATTERN (jump);
      if (GET_CODE (pat) != SET || SET_DEST (pat) != pc_rtx)
	continue;
      rtx src = SET_SRC (pat), ref;
      if (GET_CODE (src) == LABEL_REF)
	ref = src;
      else if (GET_CODE (src) == IF_THEN_ELSE
	       && GET_CODE (XEXP (src, 1)) == LABEL_REF
	       && XEXP (src, 2) == pc_rtx)
	ref = XEXP (src, 1);
      else
	continue;
      rtx label = label_ref_label (ref);
      bitmap live = df_get_live_out (bb);
      int k = -1;
      for (int t = 0; t < 3 && k < 0; t++)
	{
	  int c = (next + t) % 3;
	  if (!bitmap_bit_p (live, CTPR1_REGNUM + c))
	    k = c;
	}
      if (k < 0)
	continue;
      rtx ctpr = gen_rtx_REG (DImode, CTPR1_REGNUM + k);
      rtx newpat
	= gen_rtx_PARALLEL (VOIDmode,
			    gen_rtvec (2, copy_rtx (pat),
				       gen_rtx_USE (VOIDmode, ctpr)));
      if (!validate_change (jump, &PATTERN (jump), newpat, 0))
	continue;
      rtx_insn *disp = emit_insn_before (gen_e2k_disp_label (ctpr, label),
					 jump);
      add_reg_note (disp, REG_LABEL_OPERAND, label);
      LABEL_NUSES (label)++;
      df_insn_rescan (jump);
      next = k + 1;
      changed = true;
    }
  if (changed)
    df_analyze ();
}

/* A ct leaves its CTPR as it was (only calls and returns empty them,
   spec/isa/control-transfer.md), so a branch to the target of one before
   it in a chain of fall-throughs can take that one's CTPR and drop its
   own disp: a run of early exits to one place (bzip2's mainGtU) then
   waits for no disp, where with one each only two could be prepared
   ahead.  After e2k_modsched, which rewrites the loops it pipelines and
   their disps.  */
static void
e2k_share_ctprs (void)
{
  basic_block bb, prev = NULL;
  /* The label each CTPR holds along the current chain, or NULL.  */
  rtx held[3] = { NULL_RTX, NULL_RTX, NULL_RTX };
  FOR_EACH_BB_FN (bb, cfun)
    {
      /* Entered other than by falling through from PREV: start over.  */
      if (!prev || !single_pred_p (bb) || single_pred (bb) != prev
	  || !(single_pred_edge (bb)->flags & EDGE_FALLTHRU)
	  || (bb->flags & BB_DISABLE_SCHEDULE))
	held[0] = held[1] = held[2] = NULL_RTX;
      prev = bb;
      rtx_insn *insn, *next;
      FOR_BB_INSNS_SAFE (bb, insn, next)
	{
	  if (!INSN_P (insn))
	    continue;
	  if (CALL_P (insn))
	    {
	      held[0] = held[1] = held[2] = NULL_RTX;
	      continue;
	    }
	  /* A branch "disp %ctprK, L; ct %ctprK" (e2k_prepare_branches).  */
	  rtx pat = PATTERN (insn);
	  rtx_insn *jump = next_nonnote_nondebug_insn (insn);
	  if (recog_memoized (insn) == CODE_FOR_e2k_disp_label
	      && jump && JUMP_P (jump) && jump == BB_END (bb)
	      && GET_CODE (PATTERN (jump)) == PARALLEL
	      && XVECLEN (PATTERN (jump), 0) == 2
	      && GET_CODE (XVECEXP (PATTERN (jump), 0, 1)) == USE
	      && rtx_equal_p (XEXP (XVECEXP (PATTERN (jump), 0, 1), 0),
			      SET_DEST (pat))
	      && JUMP_LABEL (jump)
	      && label_ref_label (XVECEXP (SET_SRC (pat), 0, 0))
		 == JUMP_LABEL (jump))
	    {
	      rtx label = JUMP_LABEL (jump);
	      int k = REGNO (SET_DEST (pat)) - CTPR1_REGNUM;
	      int c;
	      for (c = 0; c < 3; c++)
		if (held[c] == label)
		  break;
	      if (c < 3)
		{
		  rtx *use = &XEXP (XVECEXP (PATTERN (jump), 0, 1), 0);
		  if (validate_change (jump, use,
				       gen_rtx_REG (DImode, CTPR1_REGNUM + c),
				       0))
		    {
		      if (dump_file)
			fprintf (dump_file, ";; e2k_share_ctprs: jump %d takes "
				 "%%ctpr%d\n", INSN_UID (jump), c + 1);
		      LABEL_NUSES (label)--;
		      delete_insn (insn);
		      continue;
		    }
		}
	      held[k] = label;
	      continue;
	    }
	  for (int c = 0; c < 3; c++)
	    if (reg_set_p (gen_rtx_REG (DImode, CTPR1_REGNUM + c), insn))
	      held[c] = NULL_RTX;
	}
    }
}

/* The disp of a branch "disp %ctprK, L; ct %ctprK" that ends BB, or NULL.
   Not a loop-mode back edge (e2k_hwloop_end has the same shape).  */
static rtx_insn *
e2k_prep_pair (basic_block bb, rtx *ctpr)
{
  rtx_insn *jump = BB_END (bb);
  if (!JUMP_P (jump) || recog_memoized (jump) < 0
      || get_attr_type (jump) != TYPE_CT)
    return NULL;
  rtx pat = PATTERN (jump);
  if (GET_CODE (pat) != PARALLEL || XVECLEN (pat, 0) != 2
      || GET_CODE (XVECEXP (pat, 0, 0)) != SET
      || GET_CODE (XVECEXP (pat, 0, 1)) != USE)
    return NULL;
  rtx src = SET_SRC (XVECEXP (pat, 0, 0));
  if (GET_CODE (src) == IF_THEN_ELSE)
    {
      rtx cond = XEXP (src, 0);
      if (!COMPARISON_P (cond) || !REG_P (XEXP (cond, 0))
	  || !PRED_REGNO_P (REGNO (XEXP (cond, 0))))
	return NULL;
    }
  else if (GET_CODE (src) != LABEL_REF)
    return NULL;
  rtx_insn *d = prev_nonnote_nondebug_insn_bb (jump);
  if (!d || recog_memoized (d) != CODE_FOR_e2k_disp_label)
    return NULL;
  *ctpr = XEXP (XVECEXP (pat, 0, 1), 0);
  if (!rtx_equal_p (SET_DEST (PATTERN (d)), *ctpr))
    return NULL;
  return d;
}

/* A branch's disp comes right before its ct (e2k_prepare_branches), and
   on a pipelined loop's way out that is after the copies out of the ring
   and setbn_leave (e2k_ms_emit), a barrier the scheduler can't move it
   above: the ct waited for it (LZMA's match finder, Bt4 GetMatches'
   exit).  Put the disp above what precedes it in its block, when that
   holds such a barrier and nothing of it touches the CTPR.  */
static void
e2k_lift_prepares (void)
{
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx ctpr;
      rtx_insn *disp;
      if ((bb->flags & BB_DISABLE_SCHEDULE) || !(disp = e2k_prep_pair (bb, &ctpr)))
	continue;
      rtx_insn *top = NULL;
      bool barrier = false;
      for (rtx_insn *i = PREV_INSN (disp); i != PREV_INSN (BB_HEAD (bb));
	   i = PREV_INSN (i))
	if (NONDEBUG_INSN_P (i))
	  {
	    int code = recog_memoized (i);
	    if (CALL_P (i) || JUMP_P (i) || e2k_asm_insn_p (i)
		|| e2k_raw_insn_p (i) || code == CODE_FOR_blockage
		|| code == CODE_FOR_e2k_setwd || code == CODE_FOR_e2k_return_prep
		|| reg_mentioned_p (ctpr, PATTERN (i)) || reg_set_p (ctpr, i))
	      break;
	    barrier |= volatile_insn_p (PATTERN (i));
	    top = i;
	  }
      if (barrier)
	{
	  reorder_insns (disp, disp, PREV_INSN (top));
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_lift_prepares: disp %d above insn %d "
		     "in bb %d\n", INSN_UID (disp), INSN_UID (top), bb->index);
	}
    }
}

/* A branch at the end of a short extended block H whose disp can only
   go to H's top waits for it when taken: a ct issues 5 cycles after its
   disp at the earliest, and sched-ebb can't take the disp above a label
   (GetMatchesSpec1's tree walk, xz's bt4_skip: `{disp %ctpr1, .L; ldb;
   ldb; nop 1}{ct %ctpr1}`).  Prepare it instead in each predecessor of
   H, after the predecessor's last use of the CTPR, when that CTPR (or
   another free one) holds nothing else from there to the branch.  */

static basic_block e2k_chain_next (basic_block);

/* The first block of BB's extended block (schedule_ebbs' rule).  */
static basic_block
e2k_ebb_head (basic_block bb)
{
  while (!(bb->flags & BB_DISABLE_SCHEDULE)
	 && bb->prev_bb != ENTRY_BLOCK_PTR_FOR_FN (cfun)
	 && !(bb->prev_bb->flags & BB_DISABLE_SCHEDULE)
	 && e2k_chain_next (bb->prev_bb) == bb)
    bb = bb->prev_bb;
  return bb;
}

/* Whether INSN may read or write CTPR R: a call or a return empties
   them all, a conditional return reads %ctpr3 without saying so.  */
static bool
e2k_touches_ctpr_p (rtx_insn *insn, rtx r)
{
  return (CALL_P (insn) || e2k_asm_insn_p (insn) || e2k_raw_insn_p (insn)
	  || reg_mentioned_p (r, PATTERN (insn)) || reg_set_p (r, insn)
	  || (REGNO (r) == CTPR3_REGNUM
	      && (recog_memoized (insn) == CODE_FOR_e2k_cond_return
		  || (JUMP_P (insn) && JUMP_LABEL (insn)
		      && ANY_RETURN_P (JUMP_LABEL (insn))))));
}

/* Whether R set at the top of H holds until JUMP: dead into H, touched
   by nothing on the way but SKIP, dead where the side exits go.  */
static bool
e2k_ctpr_clear_p (basic_block h, rtx_insn *jump, rtx_insn *skip, rtx r)
{
  if (bitmap_bit_p (df_get_live_in (h), REGNO (r)))
    return false;
  for (rtx_insn *i = BB_HEAD (h); i != jump; i = NEXT_INSN (i))
    {
      if (!NONDEBUG_INSN_P (i) || i == skip)
	continue;
      if (e2k_touches_ctpr_p (i, r))
	return false;
      if (JUMP_P (i))
	{
	  edge e;
	  edge_iterator ei;
	  FOR_EACH_EDGE (e, ei, BLOCK_FOR_INSN (i)->succs)
	    if (!(e->flags & EDGE_FALLTHRU)
		&& bitmap_bit_p (df_get_live_in (e->dest), REGNO (r)))
	      return false;
	}
    }
  return true;
}

/* Where in P a prepare of R can go: before the first insn of P's tail
   that leaves R alone (above P's jump), not above the prologue.  */
static rtx_insn *
e2k_ctpr_quiet_from (basic_block p, rtx r)
{
  rtx_insn *end = BB_END (p), *at = NULL;
  if (JUMP_P (end))
    {
      at = end;
      end = PREV_INSN (end);
    }
  for (rtx_insn *i = end; i != PREV_INSN (BB_HEAD (p)); i = PREV_INSN (i))
    {
      if (NOTE_P (i) && NOTE_KIND (i) == NOTE_INSN_PROLOGUE_END)
	break;
      if (!NONDEBUG_INSN_P (i))
	continue;
      int code = recog_memoized (i);
      if (e2k_touches_ctpr_p (i, r) || code == CODE_FOR_e2k_setwd
	  || code == CODE_FOR_blockage || code == CODE_FOR_e2k_return_prep
	  || volatile_insn_p (PATTERN (i)))
	break;
      at = i;
    }
  return at;
}

/* About the cycle JUMP issues at counting from H's top: the longest
   chain of true register dependences, or six operations a cycle.  */
static int
e2k_jump_cycle (basic_block h, rtx_insn *jump, rtx_insn *skip)
{
  int ready[FIRST_PSEUDO_REGISTER];
  rtx_insn *def[FIRST_PSEUDO_REGISTER];
  memset (def, 0, sizeof def);
  int n = 0, t = 0;
  for (rtx_insn *i = BB_HEAD (h); ; i = NEXT_INSN (i))
    {
      if (NONDEBUG_INSN_P (i) && i != skip && recog_memoized (i) >= 0)
	{
	  t = 0;
	  df_ref ref;
	  FOR_EACH_INSN_USE (ref, i)
	    {
	      unsigned r = DF_REF_REGNO (ref);
	      if (r < FIRST_PSEUDO_REGISTER && def[r])
		t = MAX (t, ready[r] + insn_latency (def[r], i));
	    }
	  if (i == jump)
	    return MAX (t, n / 6);
	  n++;
	  FOR_EACH_INSN_DEF (ref, i)
	    {
	      unsigned r = DF_REF_REGNO (ref);
	      if (r < FIRST_PSEUDO_REGISTER)
		{
		  def[r] = i;
		  ready[r] = t;
		}
	    }
	}
      if (i == jump)
	return MAX (t, n / 6);
    }
}

static void
e2k_hoist_prepares (void)
{
  df_analyze ();
  dfa_start ();
  int n = 0;
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx k;
      rtx_insn *d;
      if ((bb->flags & BB_DISABLE_SCHEDULE) || !(d = e2k_prep_pair (bb, &k)))
	continue;
      rtx_insn *jump = BB_END (bb);
      /* Only a branch that is taken often: otherwise the disp costs at
	 most a cycle where it is.  */
      if (any_condjump_p (jump))
	{
	  edge be = BRANCH_EDGE (bb);
	  if (!be->probability.initialized_p ()
	      || be->probability.to_reg_br_prob_base () < REG_BR_PROB_BASE / 4)
	    continue;
	}
      basic_block h = e2k_ebb_head (bb);
      if ((h->flags & BB_DISABLE_SCHEDULE) || !LABEL_P (BB_HEAD (h))
	  || e2k_jump_cycle (h, jump, d) >= 5)
	continue;
      rtx label = XVECEXP (SET_SRC (PATTERN (d)), 0, 0);
      unsigned kn = REGNO (k) - CTPR1_REGNUM;
      for (unsigned t = 0; t < 3; t++)
	{
	  unsigned c = (kn + t) % 3;
	  rtx cr = gen_rtx_REG (DImode, CTPR1_REGNUM + c);
	  if (c == 2 && cfun->machine->early_ret)
	    continue;
	  /* Another CTPR: dead after the jump, and the prepare not shared
	     with a jump below (e2k_share_ctprs).  */
	  if (c != kn)
	    {
	      bool live = false;
	      edge e;
	      edge_iterator ei;
	      FOR_EACH_EDGE (e, ei, bb->succs)
		live |= (bitmap_bit_p (df_get_live_in (e->dest), REGNO (cr))
			 || bitmap_bit_p (df_get_live_in (e->dest), REGNO (k)));
	      if (live)
		continue;
	    }
	  if (!e2k_ctpr_clear_p (h, jump, d, cr))
	    continue;
	  auto_vec<basic_block, 4> ps;
	  bool ok = true;
	  edge e;
	  edge_iterator ei;
	  FOR_EACH_EDGE (e, ei, h->preds)
	    {
	      basic_block p = e->src;
	      if (p == ENTRY_BLOCK_PTR_FOR_FN (cfun)
		  || (e->flags & EDGE_COMPLEX)
		  || (p->flags & BB_DISABLE_SCHEDULE)
		  || e2k_ebb_head (p) == h
		  || (p->count.initialized_p () && h->count.initialized_p ()
		      && p->count > h->count.apply_scale (2, 1))
		  || ps.length () == 4)
		{
		  ok = false;
		  break;
		}
	      rtx_insn *pj = BB_END (p);
	      /* Nothing goes after a call that ends its block (one that
		 may throw), and a jump that may use the CTPR keeps it.  */
	      if ((JUMP_P (pj) && e2k_touches_ctpr_p (pj, cr))
		  || (!JUMP_P (pj) && control_flow_insn_p (pj)))
		{
		  ok = false;
		  break;
		}
	      edge o;
	      edge_iterator oi;
	      FOR_EACH_EDGE (o, oi, p->succs)
		if (o->dest != h
		    && (o->dest == EXIT_BLOCK_PTR_FOR_FN (cfun)
			|| bitmap_bit_p (df_get_live_in (o->dest),
					 REGNO (cr))))
		  ok = false;
	      ps.safe_push (p);
	    }
	  if (!ok || ps.is_empty ())
	    continue;
	  for (basic_block p : ps)
	    {
	      rtx_insn *at = e2k_ctpr_quiet_from (p, cr);
	      rtx pat = gen_e2k_disp_label (cr, label_ref_label (label));
	      rtx_insn *x = (at ? emit_insn_before (pat, at)
			     : emit_insn_after (pat, BB_END (p)));
	      add_reg_note (x, REG_LABEL_OPERAND, label_ref_label (label));
	      LABEL_NUSES (label_ref_label (label))++;
	      INSN_LOCATION (x) = INSN_LOCATION (d);
	    }
	  if (c != kn)
	    {
	      rtx *use = &XEXP (XVECEXP (PATTERN (jump), 0, 1), 0);
	      if (!validate_change (jump, use, cr, 0))
		gcc_unreachable ();
	    }
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_hoist_prepares: disp %d of bb %d into "
		     "%d predecessor(s) of bb %d, %%ctpr%u\n", INSN_UID (d),
		     bb->index, ps.length (), h->index, c + 1);
	  delete_insn (d);
	  df_analyze ();
	  n++;
	  break;
	}
    }
  dfa_finish ();
  if (n)
    df_analyze ();
}

/* Control speculation can't move a computation above a branch when its
   register still matters on the branch's other path, or to the branch
   itself, and sched2 doesn't rename: the load of list->next in
   "while (list && list->x != k) list = list->next" writes the register
   that the loop returns.  So in a block Y entered only by falling
   through from a conditional jump in X, give such a value a free
   register of its own (copied back after it if Y's successors still
   need it), and its uses in Y the new register.  Only values sched-ebb
   could then move: loads (as ld,sm), compares, and other ALU operations
   whose operands are available at the jump or renamed already.  */

static unsigned e2k_ms_flag (const rtx_insn *);
static void e2k_ms_set_flag (rtx_insn *, unsigned);

/* WTOP: the window registers below it (from %r0, as e2k_compute_window
   counts them, by pairs) cost the function nothing.  */
static bool
e2k_rename_free_p (unsigned r, machine_mode mode, bitmap live,
		   const HARD_REG_SET &busy, unsigned wtop = 0)
{
  if (fixed_regs[r] || TEST_HARD_REG_BIT (busy, r)
      || bitmap_bit_p (live, r) || !targetm.hard_regno_mode_ok (r, mode))
    return false;
  if (PRED_REGNO_P (r))
    return true;
  /* A global, or a window register the window has anyway.  */
  return (G_REGNO_P (r)
	  || (W_REGNO_P (r)
	      && (df_regs_ever_live_p (r) || r - R0_REGNUM < wtop)));
}

/* The first window register above every one the insns use, rounded up
   to its pair (e2k_compute_window's measure, now).  */
static unsigned
e2k_window_top (void)
{
  int maxr = -1;
  for (rtx_insn *insn = get_insns (); insn; insn = NEXT_INSN (insn))
    if (NONDEBUG_INSN_P (insn))
      {
	subrtx_iterator::array_type array;
	FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
	  if (REG_P (*iter) && HARD_REGISTER_P (*iter))
	    for (unsigned r = REGNO (*iter); r < END_REGNO (*iter); r++)
	      if (W_REGNO_P (r))
		maxr = MAX (maxr, (int) (r - R0_REGNUM));
      }
  return maxr < 0 ? 0 : (maxr | 1) + 1;
}

static void
e2k_note_regs (rtx x, HARD_REG_SET *set)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, x, NONCONST)
    if (REG_P (*iter) && HARD_REGISTER_P (*iter))
      add_to_hard_reg_set (set, GET_MODE (*iter), REGNO (*iter));
}

/* The block after BB in its extended block as schedule_ebbs makes them
   (sched-ebb.cc): entered only by falling through from BB, no label, a
   fall-through not below the tracer's probability cutoff.  */
static basic_block
e2k_chain_next (basic_block bb)
{
  basic_block n = bb->next_bb;
  if (n == EXIT_BLOCK_PTR_FOR_FN (cfun) || !single_pred_p (n)
      || single_pred (n) != bb
      || !(single_pred_edge (n)->flags & EDGE_FALLTHRU)
      || LABEL_P (BB_HEAD (n)))
    return NULL;
  edge e = single_pred_edge (n);
  int cutoff = (REG_BR_PROB_BASE / 100
		* (profile_status_for_fn (cfun) == PROFILE_READ
		   ? param_tracer_min_branch_probability_feedback
		   : param_tracer_min_branch_probability));
  if (e->probability.initialized_p ()
      && e->probability.to_reg_br_prob_base () <= cutoff)
    return NULL;
  return n;
}

/* Note in STAMP that BB, block POS of a chain, is in the way of each
   register it mentions, a call in it clobbers, or one of its jumps needs
   on the other path: a value of a block below written into such a
   register can't move above BB.  */
static void
e2k_chain_stamp (basic_block bb, int pos, int *stamp)
{
  rtx_insn *insn;
  FOR_BB_INSNS (bb, insn)
    if (NONDEBUG_INSN_P (insn))
      {
	subrtx_iterator::array_type array;
	FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
	  if (REG_P (*iter) && HARD_REGISTER_P (*iter))
	    for (unsigned r = REGNO (*iter); r < END_REGNO (*iter); r++)
	      stamp[r] = pos;
	if (CALL_P (insn))
	  {
	    HARD_REG_SET clob
	      = insn_callee_abi (insn).full_and_partial_reg_clobbers ();
	    for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
	      if (TEST_HARD_REG_BIT (clob, r))
		stamp[r] = pos;
	    for (rtx link = CALL_INSN_FUNCTION_USAGE (insn); link;
		 link = XEXP (link, 1))
	      FOR_EACH_SUBRTX (iter, array, XEXP (link, 0), NONCONST)
		if (REG_P (*iter) && HARD_REGISTER_P (*iter))
		  for (unsigned r = REGNO (*iter); r < END_REGNO (*iter); r++)
		    stamp[r] = pos;
	  }
      }
  edge e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, bb->succs)
    if (!(e->flags & EDGE_FALLTHRU))
      {
	unsigned r;
	bitmap_iterator bi;
	EXECUTE_IF_SET_IN_BITMAP (df_get_live_in (e->dest), 0, r, bi)
	  if (r < FIRST_PSEUDO_REGISTER)
	    stamp[r] = pos;
      }
}

static void
e2k_note_use_regs (rtx *loc, void *data)
{
  e2k_note_regs (*loc, (HARD_REG_SET *) data);
}

static void
e2k_spec_rename (void)
{
  df_analyze ();
  basic_block x;
  bool changed = false;
  unsigned wtop = e2k_window_top ();
  /* Along a chain of blocks falling through into each other (an extended
     block), the last block that is in the way of each register
     (e2k_chain_stamp), from 1, and the last block it is live out of.  */
  int stamp[FIRST_PSEUDO_REGISTER], live_to[FIRST_PSEUDO_REGISTER];
  int pos = 0;
  basic_block prev = NULL;
  FOR_EACH_BB_FN (x, cfun)
    {
      if (!prev || e2k_chain_next (prev) != x)
	{
	  memset (stamp, 0, sizeof stamp);
	  memset (live_to, 0, sizeof live_to);
	  pos = 0;
	  int p = 0;
	  for (basic_block b = x; b; b = e2k_chain_next (b))
	    {
	      unsigned r;
	      bitmap_iterator bi;
	      p++;
	      EXECUTE_IF_SET_IN_BITMAP (df_get_live_out (b), 0, r, bi)
		if (r < FIRST_PSEUDO_REGISTER)
		  live_to[r] = p;
	    }
	}
      prev = x;
      e2k_chain_stamp (x, ++pos, stamp);
      rtx_insn *jump = BB_END (x);
      if (!JUMP_P (jump) || !any_condjump_p (jump))
	continue;
      edge fall = FALLTHRU_EDGE (x);
      if (!fall || !(fall->flags & EDGE_FALLTHRU)
	  || fall->dest == EXIT_BLOCK_PTR_FOR_FN (cfun)
	  || !single_pred_p (fall->dest))
	continue;
      basic_block y = fall->dest;
      bitmap xlive = df_get_live_out (x), ylive = df_get_live_out (y);
      /* What Y mentions, and what its values are renamed into; what X
	 reads (predicated copies and store addresses too): only a value
	 X reads or needs after it is worth a copy back.  */
      HARD_REG_SET busy, xreads;
      CLEAR_HARD_REG_SET (busy);
      CLEAR_HARD_REG_SET (xreads);
      rtx_insn *insn;
      FOR_BB_INSNS (x, insn)
	if (NONDEBUG_INSN_P (insn))
	  note_uses (&PATTERN (insn), e2k_note_use_regs, &xreads);
      FOR_BB_INSNS (y, insn)
	if (NONDEBUG_INSN_P (insn))
	  e2k_note_regs (PATTERN (insn), &busy);
      /* Registers Y defines before the current insn (not available at
	 X's jump), and those renamed.  */
      HARD_REG_SET ydefs, renamed;
      CLEAR_HARD_REG_SET (ydefs);
      CLEAR_HARD_REG_SET (renamed);
      for (insn = BB_HEAD (y); insn && insn != NEXT_INSN (BB_END (y));
	   insn = NEXT_INSN (insn))
	{
	  if (!NONDEBUG_INSN_P (insn))
	    continue;
	  if (CALL_P (insn) || JUMP_P (insn) || e2k_asm_insn_p (insn)
	      || volatile_insn_p (PATTERN (insn)))
	    break;
	  rtx pat = PATTERN (insn);
	  rtx dest = GET_CODE (pat) == SET ? SET_DEST (pat) : NULL_RTX;
	  if (!dest || !REG_P (dest) || REG_NREGS (dest) != 1
	      || recog_memoized (insn) < 0)
	    {
	      note_stores (insn, [] (rtx d, const_rtx, void *data)
			   {
			     if (REG_P (d))
			       add_to_hard_reg_set ((HARD_REG_SET *) data,
						    GET_MODE (d), REGNO (d));
			   }, &ydefs);
	      continue;
	    }
	  unsigned dr = REGNO (dest);
	  machine_mode mode = GET_MODE (dest);
	  enum attr_type t = get_attr_type (insn);
	  /* Movable above the jump: the operands available there.  */
	  HARD_REG_SET srcs;
	  CLEAR_HARD_REG_SET (srcs);
	  e2k_note_regs (SET_SRC (pat), &srcs);
	  HARD_REG_SET late = srcs & ydefs & ~renamed;
	  bool movable = (hard_reg_set_empty_p (late)
			  && (t == TYPE_LOAD || t == TYPE_CMP || t == TYPE_ALU)
			  && !side_effects_p (SET_SRC (pat))
			  && (GPR_REGNO_P (dr) || PRED_REGNO_P (dr))
			  && !fixed_regs[dr]);
	  /* Where the register is in the way: X (its jump, its other path,
	     any insn of it), else the last block above that is; 0 for
	     nowhere.  */
	  bool near = bitmap_bit_p (xlive, dr) || stamp[dr] == pos;
	  int lim = near ? pos : stamp[dr];
	  /* Where this value is overwritten in Y, if it is, or a call that
	     may read it (its function usage) ends what can be renamed.  */
	  rtx_insn *redef = NULL, *stop = NULL, *u;
	  for (u = NEXT_INSN (insn); u && u != NEXT_INSN (BB_END (y));
	       u = NEXT_INSN (u))
	    {
	      if (!INSN_P (u))
		continue;
	      if (CALL_P (u))
		{
		  stop = u;
		  break;
		}
	      if (reg_set_p (dest, u))
		{
		  /* Only a whole new value ends it; a partial one reads it.  */
		  rtx up = PATTERN (u);
		  if (GET_CODE (up) == SET && REG_P (SET_DEST (up))
		      && REGNO (SET_DEST (up)) == dr)
		    redef = u;
		  else
		    stop = u;
		  break;
		}
	    }
	  bool copy = !redef && (stop || bitmap_bit_p (ylive, dr));
	  unsigned r = INVALID_REGNUM;
	  /* Above the blocks before X only without a copy back, and with one
	     only for a value X reads or needs after it (a register X only
	     writes is no reason for an extra copy).  */
	  if (movable && lim
	      && (copy ? (bitmap_bit_p (xlive, dr)
			  || TEST_HARD_REG_BIT (xreads, dr))
		       && !PRED_REGNO_P (dr)
		  : true))
	    {
	      /* The register least recently used along the chain, so that
		 the value moves farthest up (bzip2's mainGtU: each step's
		 bytes went to the registers of the step two up and waited
		 for its compare); not one a block further down keeps
		 across its end; globals first.  */
	      unsigned best = UINT_MAX;
	      for (unsigned c = 0; c < FIRST_PSEUDO_REGISTER; c++)
		if (PRED_REGNO_P (c) == PRED_REGNO_P (dr)
		    && stamp[c] < lim
		    && e2k_rename_free_p (c, mode, xlive, busy, wtop))
		  {
		    unsigned key
		      = (((unsigned) (live_to[c] > pos + 1) << 24)
			 | ((unsigned) stamp[c] << 2)
			 | (G_REGNO_P (c) || PRED_REGNO_P (c) ? 0
			    : df_regs_ever_live_p (c) ? 1 : 2));
		    if (key < best)
		      best = key, r = c;
		  }
	    }
	  if (r == INVALID_REGNUM)
	    {
	      add_to_hard_reg_set (&ydefs, mode, dr);
	      /* A value that moves up as it is (an address computed for a
		 load) is available at the jump too.  */
	      if (movable && !near)
		add_to_hard_reg_set (&renamed, mode, dr);
	      else
		remove_from_hard_reg_set (&renamed, mode, dr);
	      continue;
	    }
	  /* Rename the definition and the uses up to the next one (that
	     one's own uses of the old value included).  */
	  rtx nreg = gen_rtx_REG (mode, r);
	  validate_change (insn, &SET_DEST (pat), nreg, 1);
	  rtx_insn *end = (redef ? NEXT_INSN (redef)
			   : stop ? stop : NEXT_INSN (BB_END (y)));
	  bool overlap = false;
	  for (u = NEXT_INSN (insn); u != end; u = NEXT_INSN (u))
	    if (NONDEBUG_INSN_P (u))
	      {
		rtx *loc = &PATTERN (u);
		subrtx_ptr_iterator::array_type array;
		FOR_EACH_SUBRTX_PTR (iter, array, loc, NONCONST)
		  {
		    rtx *l = *iter;
		    /* A value of several registers that includes this one
		       (long double in a pair) can't follow it.  */
		    if (REG_P (*l) && HARD_REGISTER_P (*l)
			&& (REGNO (*l) == dr ? REG_NREGS (*l) != 1
			    : IN_RANGE (dr, REGNO (*l), END_REGNO (*l) - 1)))
		      overlap = true;
		    if (REG_P (*l) && REGNO (*l) == dr)
		      {
			/* Not the redefinition itself.  */
			if (u == redef && reg_set_p (*l, u)
			    && GET_CODE (PATTERN (u)) == SET
			    && l == &SET_DEST (PATTERN (u)))
			  continue;
			validate_change (u, l, gen_rtx_REG (GET_MODE (*l), r),
					 1);
		      }
		  }
	      }
	  if (overlap)
	    cancel_changes (0);
	  if (overlap || !apply_change_group ())
	    {
	      add_to_hard_reg_set (&ydefs, mode, dr);
	      continue;
	    }
	  for (u = insn; u != end; u = NEXT_INSN (u))
	    if (INSN_P (u))
	      {
		remove_note (u, find_reg_note (u, REG_EQUAL, NULL_RTX));
		remove_note (u, find_reg_note (u, REG_EQUIV, NULL_RTX));
		df_insn_rescan (u);
	      }
	  /* Debug binds of the new register in Y, or of the old one where
	     it was renamed, would show the wrong value.  */
	  {
	    bool in = false;
	    FOR_BB_INSNS (y, u)
	      {
		if (u == insn)
		  in = true;
		if (u == end)
		  in = false;
		if (DEBUG_BIND_INSN_P (u)
		    && (reg_mentioned_p (nreg, PATTERN (u))
			|| (in && reg_mentioned_p (dest, PATTERN (u)))))
		  {
		    INSN_VAR_LOCATION_LOC (u) = gen_rtx_UNKNOWN_VAR_LOC ();
		    df_insn_rescan_debug_internal (u);
		  }
	      }
	  }
	  if (!df_regs_ever_live_p (r))
	    df_set_regs_ever_live (r, true);
	  SET_HARD_REG_BIT (busy, r);
	  SET_HARD_REG_BIT (renamed, r);
	  add_to_hard_reg_set (&ydefs, mode, dr);
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_spec_rename: insn %d in bb %d: %s -> "
		     "%s, %d up%s\n", INSN_UID (insn), y->index, reg_names[dr],
		     reg_names[r], pos + 1 - lim, copy ? ", copied back" : "");
	  changed = true;
	  if (copy)
	    {
	      rtx_insn *c = emit_insn_after (gen_rtx_SET (gen_rtx_REG (mode, dr),
							  nreg), insn);
	      if (recog_memoized (c) < 0)
		gcc_unreachable ();
	      df_insn_rescan (c);
	      /* A copy of a value a merged chain computes speculatively
		 (e2k_merge_chains) is speculative too.  */
	      e2k_ms_set_flag (c, e2k_ms_flag (insn));
	      /* The copy stays.  */
	      insn = c;
	    }
	}
    }
  if (changed)
    df_analyze ();
}

/* Data speculation (see "Data speculation" in e2k.md).  */

/* Check loads print "rbranch .LDAMn" in their wide instruction; ".LDAMBn"
   follows the instruction (e2k_final_postscan_insn) and the stub
   ".LDAMn: ibranch .LDAMBn" goes at the end of the function
   (e2k_asm_function_epilogue).  When the check reloaded, the rbranch
   leaves the wide instruction after it unexecuted until the reload has
   landed: a consumer in the next instruction read the early value once
   on the 4C (first call of a function, a struct field just spilled).
   lcc pairs every check with an rbranch too.  */

/* An array prefetch read (e2k_mova<mode>): OPERANDS[1] the area (its
   program instruction), [2] the channel, [3] the element size, [4] the
   byte offset in the step, [5] whether it advances the area.  */
const char *
e2k_output_mova (rtx *operands)
{
  static char buf[80];
  int size = INTVAL (operands[3]);
  snprintf (buf, sizeof buf, "mova%c,%d\tarea=%d, ind=%d, am=%d, be=0, %%0",
	    size == 1 ? 'b' : size == 2 ? 'h' : size == 4 ? 'w' : 'd',
	    (int) INTVAL (operands[2]), (int) INTVAL (operands[1]),
	    (int) INTVAL (operands[4]), (int) INTVAL (operands[5]));
  return buf;
}

/* An AAU store (OPERANDS as e2k_staa<mode> has them) of SIZE bytes,
   with its incr.  */
const char *
e2k_output_staa (rtx *operands, int size)
{
  static char buf[96];
  HOST_WIDE_INT lit = INTVAL (operands[3]);
  char off[32] = "";
  if (lit)
    snprintf (off, sizeof off, " + %#" PRIx64, (uint64_t) (uint32_t) lit);
  snprintf (buf, sizeof buf, "staa%c\t%%0, %%%%aad%d[ %%%%aasti%d%s ]\n"
	    "\tincr\t%%%%aaincr%d",
	    size == 1 ? 'b' : size == 2 ? 'h' : size == 4 ? 'w' : 'd',
	    (int) INTVAL (operands[1]), (int) INTVAL (operands[2]), off,
	    (int) INTVAL (operands[4]));
  return buf;
}

/* Whether PAT is an AAU store's (e2k_staa<mode>).  */
bool
e2k_staa_p (rtx pat)
{
  if (GET_CODE (pat) != SET || !MEM_P (SET_DEST (pat)))
    return false;
  rtx a = XEXP (SET_DEST (pat), 0);
  return GET_CODE (a) == UNSPEC && XINT (a, 1) == UNSPEC_STAA;
}

/* A prefetch: speculative, unless the insn prints ",sm" already
   (e2k_asm_output_opcode), as the scheduler marks what it moves.  */
const char *
e2k_output_prefetch (void)
{
  return (e2k_cur_sm ? "ldb\t%a0, %%empty, mas=0x20"
	  : "ldb,sm\t%a0, %%empty, mas=0x20");
}

/* Print a lock load (LOCK) or a check load.  */
const char *
e2k_output_spec_load (rtx *operands, bool lock)
{
  static char buf[64];
  rtx mem = operands[1];
  if (GET_CODE (mem) == ZERO_EXTEND)
    mem = XEXP (mem, 0);
  operands[2] = mem;
  char sz;
  switch (GET_MODE_SIZE (GET_MODE (mem)))
    {
    case 1: sz = 'b'; break;
    case 2: sz = 'h'; break;
    case 4: sz = 'w'; break;
    case 8: sz = 'd'; break;
    default: gcc_unreachable ();
    }
  /* Its ",sm" is in the template, also for a load e2k_unpredicate_loads
     marked.  */
  e2k_cur_sm = false;
  if (lock)
    snprintf (buf, sizeof buf, "ld%c,0,sm\t%%2, %%0, mas=0x4", sz);
  else
    {
      int n = ++e2k_dam_labelno;
      e2k_dam_pending.safe_push (n);
      e2k_dam_stubs.safe_push (n);
      snprintf (buf, sizeof buf,
		"ld%c,5\t%%2, %%0, mas=0x3%%?\n\trbranch\t.LDAM%d", sz, n);
    }
  return buf;
}

/* IFCVT_MODIFY_TESTS: no operations under the predicate of an FP
   compare, which reaches them 4 cycles after it (spec/isa/timing.md):
   in a loop keeping a maximum (Linpack's idamax) the branch around the
   update costs nothing, while the predicated update makes the next
   iteration's compare wait for it.  */
void
e2k_ifcvt_modify_tests (struct ce_if_block *ce_info, rtx *true_expr,
			rtx *false_expr)
{
  rtx t = *true_expr;
  if (!t || !REG_P (XEXP (t, 0)))
    return;
  /* Loads and stores under a predicate only in integer code: in an FP
     loop they made the kernel stall (relcc2 findings I19; Linpack 7%
     slower), in integer code they turn branchy loops with stores in
     both arms into straight code (xz's binary tree walk).  */
  bool mem = false, fp = false;
  for (basic_block arm : { ce_info->then_bb, ce_info->else_bb })
    if (arm)
      {
	rtx_insn *insn;
	FOR_BB_INSNS (arm, insn)
	  if (NONDEBUG_INSN_P (insn) && recog_memoized (insn) >= 0)
	    {
	      enum attr_type ty = get_attr_type (insn);
	      rtx set = single_set (insn);
	      mem |= ty == TYPE_LOAD || ty == TYPE_STORE;
	      fp |= (ty == TYPE_FP || ty == TYPE_FMA || ty == TYPE_FFMA
		     || ty == TYPE_FCVT
		     || ty == TYPE_FDIV || ty == TYPE_FCMP
		     || (set && FLOAT_MODE_P (GET_MODE (SET_DEST (set)))));
	    }
      }
  if (mem && fp)
    {
      *true_expr = *false_expr = NULL_RTX;
      return;
    }
  basic_block bb = ce_info->test_bb;
  for (rtx_insn *insn = BB_END (bb); insn != PREV_INSN (BB_HEAD (bb));
       insn = PREV_INSN (insn))
    if (INSN_P (insn) && reg_set_p (XEXP (t, 0), insn))
      {
	if (recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_FCMP)
	  *true_expr = *false_expr = NULL_RTX;
	return;
      }
}

/* A pipelined loop's check load (e2k_ldchk_jump): its rbranch goes to
   the loop's compensation code.  */
const char *
e2k_output_ldchk_jump (rtx *operands)
{
  static char buf[64];
  rtx mem = operands[1];
  if (GET_CODE (mem) == ZERO_EXTEND)
    mem = XEXP (mem, 0);
  operands[3] = mem;
  const char *sz = "bhwd";
  int k = exact_log2 (GET_MODE_SIZE (GET_MODE (mem)));
  gcc_assert (k >= 0 && k <= 3);
  snprintf (buf, sizeof buf, "ld%c,5\t%%3, %%0, mas=0x3\n\trbranch\t%%l2",
	    sz[k]);
  return buf;
}

static bool
e2k_ldlock_p (const_rtx pat)
{
  return (GET_CODE (pat) == PARALLEL && XVECLEN (pat, 0) == 2
	  && GET_CODE (XVECEXP (pat, 0, 1)) == UNSPEC
	  && XINT (XVECEXP (pat, 0, 1), 1) == UNSPEC_LDLOCK);
}

/* Only after reload, in the EBB scheduler of machine reorg, and only
   data speculation: a semi-speculative load needs no check at all, and
   control speculation is a separate step.  */
static void
e2k_set_sched_flags (spec_info_t spec_info)
{
  unsigned int *flags = &current_sched_info->flags;
  if (e2k_dam && optimize > 0 && reload_completed
      && (*flags & SCHED_EBB))
    {
      /* Control speculation is done without checks (e2k_spec_prepare).  */
      spec_info->mask = e2k_dam ? BEGIN_DATA : 0;
      *flags |= USE_DEPS_LIST | DO_SPECULATION;
      spec_info->flags = 0;
      spec_info->dump = sched_verbose >= 1 ? sched_dump : 0;
    }
  else
    spec_info->mask = 0;
}

/* The pieces of a load the DAM can speculate: (set (reg) SRC) with SRC
   a memory reference or a zero-extended one, or a lock load of one.  */
static bool
e2k_spec_load_parts (rtx_insn *insn, rtx *dest, rtx *src)
{
  rtx pat = PATTERN (insn);
  if (e2k_ldlock_p (pat))
    pat = XVECEXP (pat, 0, 0);
  if (GET_CODE (pat) != SET)
    return false;
  *dest = SET_DEST (pat);
  *src = SET_SRC (pat);
  return (REG_P (*dest) && GPR_REGNO_P (REGNO (*dest))
	  && GET_MODE (*dest) == GET_MODE (*src)
	  && e2k_spec_load_operand (*src, GET_MODE (*src)));
}

/* Whether MEM is in a loop copy that runs when its arrays may overlap
   (e2k_av_loop): its loads mostly read what its stores just wrote, and a
   failed check costs its compensation code every time (zlib's
   inflate_fast, 46 cycles an iteration of 3 bytes instead of 10).  */
static bool
e2k_ov_mem_p (rtx mem)
{
  if (GET_CODE (mem) == ZERO_EXTEND || GET_CODE (mem) == SIGN_EXTEND)
    mem = XEXP (mem, 0);
  if (!MEM_P (mem) || !MEM_EXPR (mem))
    return false;
  tree base = get_base_address (MEM_EXPR (mem));
  if (!base
      || (TREE_CODE (base) != MEM_REF && TREE_CODE (base) != TARGET_MEM_REF))
    return false;
  unsigned short c = MR_DEPENDENCE_CLIQUE (base);
  machine_function *m = cfun->machine;
  for (int k = 0; c && k < m->n_ov_cliques; k++)
    if (c == m->ov_cliques[k])
      return true;
  return false;
}

/* Whether INSN accesses memory in such a copy.  */
static bool
e2k_ov_insn_p (rtx_insn *insn)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
    if (MEM_P (*iter) && e2k_ov_mem_p (const_cast<rtx> (*iter)))
      return true;
  return false;
}

static int
e2k_speculate_insn (rtx_insn *insn, ds_t ts, rtx *new_pat)
{
  rtx dest, src;
  if ((ts & ~BEGIN_DATA) != 0 || !e2k_spec_load_parts (insn, &dest, &src))
    return -1;
  if (e2k_ov_mem_p (src))
    return -1;
  if (e2k_ldlock_p (PATTERN (insn)))
    return 0;
  /* A pipelined loop's prologue is speculative already; a load
     e2k_unpredicate_loads ran without its condition is not.  */
  if (e2k_ms_flag (insn)
      && (e2k_ms_flag (insn) != E2K_MS_SM || !e2k_unpred_cond_of (insn)))
    return -1;
  /* Its check, a plain load, takes the load's dependences, and loads
     have none on branches (e2k_spec_prepare): not before every branch
     the load followed is scheduled, or the check could rise above one
     and fault on an address valid only past it.  */
  for (rtx_insn *p = PREV_INSN (insn);
       p && p != current_sched_info->prev_head && !e2k_unpred_cond_of (insn);
       p = PREV_INSN (p))
    if (JUMP_P (p)
	&& (INSN_UID (p) >= (int) e2k_insn_clock.length ()
	    || e2k_insn_clock[INSN_UID (p)] == 0))
      return -1;
  /* A failed check reloads from the address; it must still be there.  */
  if (reg_overlap_mentioned_p (dest, src))
    return -1;
  /* The lock load shares the SET with the original pattern: an address
     replacement (DEP_REPLACE, moving the load past an increment of its
     base) points into that SET and must change the lock load too.  The
     check copies the address current when it is made.  */
  *new_pat = gen_rtx_PARALLEL (VOIDmode,
			       gen_rtvec (2, PATTERN (insn),
					  gen_rtx_UNSPEC (VOIDmode,
							  gen_rtvec (1, const0_rtx),
							  UNSPEC_LDLOCK)));
  return 1;
}

/* Hold back a load about to be issued as a lock load while an increment
   of its base that may still be moved above it, by rewriting its
   address, is ready: issuing the load makes the check, which inherits
   the load's dependence on the increment as a hard one, and the
   increment was already in the ready list (an assertion in
   schedule_insn, gcc.c-torture/execute/920302-1.c).  Once the
   increment is issued, the rewritten address reaches the lock load
   (which shares the load's SET) and the check copies it.  */
static int
e2k_lookahead_guard (rtx_insn *insn, int)
{
  if (!(TODO_SPEC (insn) & BEGIN_DATA))
    return 0;
  sd_iterator_def sd_it;
  dep_t dep;
  FOR_EACH_DEP (insn, SD_LIST_FORW, sd_it, dep)
    {
      /* haifa-sched.cc's QUEUE_INDEX: -1 ready, >= 0 queued.  */
      int q = HID (DEP_CON (dep))->queue_index;
      if (DEP_REPLACE (dep) != NULL && (q == -1 || q >= 0))
	return -1;
    }
  return 0;
}

static bool
e2k_needs_block_p (ds_t)
{
  return false;
}

static rtx
e2k_gen_spec_check (rtx_insn *insn, rtx_insn *label, ds_t)
{
  rtx dest, src;
  gcc_assert (label == NULL);
  bool ok = e2k_spec_load_parts (insn, &dest, &src);
  gcc_assert (ok);
  machine_mode mode = GET_MODE (dest);
  rtx test = gen_rtx_NE (VOIDmode,
			 gen_rtx_UNSPEC (VOIDmode,
					 gen_rtvec (1, copy_rtx (dest)),
					 UNSPEC_LDCHK),
			 const0_rtx);
  rtx set = gen_rtx_SET (copy_rtx (dest),
			 gen_rtx_IF_THEN_ELSE (mode, test, copy_rtx (src),
					       copy_rtx (dest)));
  if (rtx cond = e2k_unpred_cond_of (insn))
    return gen_rtx_COND_EXEC (VOIDmode, copy_rtx (cond), set);
  return set;
}

static ds_t
e2k_get_insn_spec_ds (rtx_insn *insn)
{
  return e2k_ldlock_p (PATTERN (insn)) ? BEGIN_DATA : 0;
}

/* Counted loops on %lsr (see the "Counted loops" section of e2k.md).  */

/* Whether the loop the doloop pass is converting may run more than
   2^32 - 1 times (set by e2k_can_use_doloop_p for the doloop_end
   expander that follows).  */
bool e2k_doloop_wide;

/* The iterations the doloop pass knows that loop to run: its count if
   constant, else -2 - its bound, or -1: operand 4 of the doloop_end
   patterns, which e2k_hwloop_opt records for each hardware
   loop, by the UID of its loop end, for the modulo scheduler (array
   prefetch leaves loops known to be short alone).  RTL loops don't keep
   their bounds past the loop passes, nor loops their start labels.  */
HOST_WIDE_INT e2k_doloop_iters = -1;
static hash_map<int_hash<int, 0, -1>, HOST_WIDE_INT> *e2k_loop_iters;

/* Only innermost loops: %lsr is one register.  Its counter has 32 bits
   (v3); a loop whose count may not fit (iterations_max 0: unknown) is
   strip-mined (e2k_doloop_end_wide).  */
static bool
e2k_can_use_doloop_p (const widest_int &iterations,
		      const widest_int &iterations_max,
		      unsigned int loop_depth, bool entered_at_top)
{
  e2k_doloop_wide = (wi::eq_p (iterations_max, 0)
		     || !wi::leu_p (iterations_max, 0xffffffffU));
  e2k_doloop_iters = -1;
  if (wi::ne_p (iterations, 0) && wi::fits_shwi_p (iterations))
    e2k_doloop_iters = iterations.to_shwi ();
  else if (wi::ne_p (iterations_max, 0)
	   && wi::les_p (iterations_max, HOST_WIDE_INT_MAX / 2))
    e2k_doloop_iters = -2 - iterations_max.to_shwi ();
  return loop_depth == 1 && entered_at_top;
}

/* The most iterations of the hardware loop that JUMP ends, or -1.  */
static HOST_WIDE_INT
e2k_loop_max_iters (rtx_insn *jump)
{
  HOST_WIDE_INT *p = e2k_loop_iters ? e2k_loop_iters->get (INSN_UID (jump))
		     : NULL;
  return !p ? -1 : *p >= 0 ? *p : -2 - *p;
}

/* Its iterations if constant, or -1.  */
static HOST_WIDE_INT
e2k_loop_exact_iters (rtx_insn *jump)
{
  HOST_WIDE_INT *p = e2k_loop_iters ? e2k_loop_iters->get (INSN_UID (jump))
		     : NULL;
  return p && *p >= 0 ? *p : -1;
}

/* Whether the doloop pass should leave the loop starting at LABEL
   alone: one of two blocks whose first block leaves early (xz's
   lzma_memcmplen, "while (len < limit && a[len] == b[len]) len++"),
   which e2k_hwloop_opt doesn't put on %lsr.  Its counter would be split
   back into a decrement and a compare with zero next to the loop's own
   variable, still needed after the loop: an operation more per
   iteration than the compare it replaces (II 2 instead of 1 there).  */
bool
e2k_doloop_declined_p (rtx label)
{
  if (!e2k_pipeline || !e2k_pipeline_while || !current_loops
      || !LABEL_P (label) || !BLOCK_FOR_INSN (label))
    return false;
  class loop *loop = BLOCK_FOR_INSN (label)->loop_father;
  if (!loop || loop == current_loops->tree_root)
    return false;
  /* Two blocks once the empty latch the loop passes keep is gone, and
     two ways out.  */
  basic_block *bbs = get_loop_body (loop);
  unsigned full = 0, exits = 0;
  for (unsigned i = 0; i < loop->num_nodes; i++)
    {
      rtx_insn *insn;
      bool any = false;
      FOR_BB_INSNS (bbs[i], insn)
	if (NONDEBUG_INSN_P (insn))
	  any = true;
      full += any;
      edge e;
      edge_iterator ei;
      FOR_EACH_EDGE (e, ei, bbs[i]->succs)
	if (!flow_bb_inside_loop_p (loop, e->dest))
	  exits++;
    }
  free (bbs);
  return full == 2 && exits >= 2;
}

/* Whether BB, in LOOP, is an arm that if-conversion after reload will
   put under a predicate (a block of a few integer operations between a
   conditional branch and the join, both in the loop), so that it, and
   the join with it, become part of the branch's block.  */
static bool
e2k_ifcvt_arm_p (basic_block bb, class loop *loop)
{
  if (!single_pred_p (bb) || !single_succ_p (bb) || bb == loop->header)
    return false;
  basic_block p = single_pred (bb), j = single_succ (bb);
  if (!flow_bb_inside_loop_p (loop, p) || !flow_bb_inside_loop_p (loop, j)
      || EDGE_COUNT (p->succs) != 2 || j == loop->header)
    return false;
  int n = 0;
  rtx_insn *insn;
  FOR_BB_INSNS (bb, insn)
    if (NONDEBUG_INSN_P (insn))
      {
	rtx set = single_set (insn);
	if (!NONJUMP_INSN_P (insn) || !set || ++n > MAX_CONDITIONAL_EXECUTE
	    || FLOAT_MODE_P (GET_MODE (SET_DEST (set)))
	    || side_effects_p (PATTERN (insn)))
	  return false;
      }
  return n > 0;
}

/* Don't unroll what e2k_modsched will pipeline well (an innermost loop
   of one block without calls, whose addresses its dependence test
   understands: registers that the loop steps by a constant or doesn't
   change, plus a constant): its kernel overlaps iterations anyway, and
   an unrolled body needs a longer kernel and more rotating registers
   for the same speed or worse.  lcc doesn't unroll those either.  A
   branch around a few integer operations counts as one block: if-
   conversion puts them under a predicate (stores too), and the
   pipeliner takes those.  Other loops keep their unrolling for the
   scheduler.  */
/* Iterations from which a loop is worth pipelining for any gain over
   one iteration's length (e2k_ms_long_p, e2k_loop_rec_bound_p).  */
#define E2K_MS_LONG 64

/* Whether BB, the body of a loop, chains its iterations through a
   register too long for e2k_modsched to pipeline it: a kernel that
   isn't clearly shorter than one iteration (an II of the recurrence's
   length, at least, with II + 2 <= the iteration's length and 4 II <= 3
   times that, e2k_ms_pipeline).  PolyBench's seidel-2d, whose elements
   each wait for the last (six adds and a divide of 38 cycles in 49).
   Such a loop is better unrolled, for the scheduler to overlap what the
   iterations don't chain.  LONGRUN: the loop runs E2K_MS_LONG times or
   more, and any II shorter than an iteration pays (seidel-2d once its
   rows were told apart, II 38 as lcc's).  */
static bool
e2k_loop_rec_bound_p (basic_block bb, bool longrun)
{
  unsigned nr = max_reg_num ();
  auto_vec<int> arrive (nr), from (nr);
  arrive.safe_grow_cleared (nr);
  from.safe_grow (nr);
  auto_bitmap set, carried;
  rtx_insn *insn;
  /* The registers read before they are set: carried.  */
  FOR_BB_INSNS (bb, insn)
    if (NONDEBUG_INSN_P (insn) && !JUMP_P (insn))
      {
	rtx pat = single_set (insn);
	if (!pat)
	  return false;
	subrtx_iterator::array_type array;
	FOR_EACH_SUBRTX (iter, array, SET_SRC (pat), NONCONST)
	  if (REG_P (*iter) && !bitmap_bit_p (set, REGNO (*iter)))
	    bitmap_set_bit (carried, REGNO (*iter));
	if (REG_P (SET_DEST (pat)))
	  bitmap_set_bit (set, REGNO (SET_DEST (pat)));
      }
  bitmap_and_into (carried, set);
  /* One iteration's length, everything there at its start; and from
     each carried register's value at the start, when its next value is
     set.  */
  auto walk = [&] (vec<int> &t, bool all)
    {
      int len = 0;
      FOR_BB_INSNS (bb, insn)
	if (NONDEBUG_INSN_P (insn) && !JUMP_P (insn))
	  {
	    rtx pat = single_set (insn);
	    int a = all ? 0 : -1;
	    auto use = [&] (rtx x)
	      {
		subrtx_iterator::array_type array;
		FOR_EACH_SUBRTX (iter, array, x, NONCONST)
		  if (REG_P (*iter) && REGNO (*iter) < nr)
		    a = MAX (a, t[REGNO (*iter)]);
	      };
	    use (SET_SRC (pat));
	    if (MEM_P (SET_DEST (pat)))
	      use (XEXP (SET_DEST (pat), 0));
	    /* A copy costs nothing: e2k_ms_fold_copies folds it.  A
	       conditional move is a compare and a merge once split (its
	       "multi" latency is the DFA's guess for anything): 1 + 1, or
	       4 + 1 when the compare is an FP one (floyd-warshall's min).  */
	    rtx src = SET_SRC (pat);
	    int lat;
	    if (REG_P (src))
	      lat = 0;
	    else if (GET_CODE (src) == IF_THEN_ELSE)
	      lat = (FLOAT_MODE_P (GET_MODE (XEXP (XEXP (src, 0), 0))) ? 5 : 2);
	    else
	      lat = MAX (insn_default_latency (insn), 1);
	    int done = a < 0 ? -1 : a + lat;
	    len = MAX (len, done);
	    if (REG_P (SET_DEST (pat)) && REGNO (SET_DEST (pat)) < nr)
	      t[REGNO (SET_DEST (pat))] = done;
	  }
      return len;
    };
  int len = walk (arrive, true), rec = 0;
  bitmap_iterator bi;
  unsigned c;
  EXECUTE_IF_SET_IN_BITMAP (carried, 0, c, bi)
    {
      for (unsigned r = 0; r < nr; r++)
	from[r] = -1;
      from[c] = 0;
      walk (from, false);
      rec = MAX (rec, from[c]);
    }
  if (dump_file)
    fprintf (dump_file, ";; e2k: bb %d: recurrence %d of %d cycles\n",
	     bb->index, rec, len);
  return rec > 0 && (rec + 2 > len || (!longrun && 4 * rec > 3 * len));
}

static unsigned
e2k_loop_unroll_adjust (unsigned nunroll, class loop *loop)
{
  if (!e2k_pipeline || loop->inner)
    return nunroll;
  basic_block *bbs = get_loop_body (loop);
  int full = 0;
  bool ok = true, nocall = true;
  auto_bitmap set, stepped, multi, derived;
  for (unsigned i = 0; i < loop->num_nodes; i++)
    {
      rtx_insn *insn;
      bool any = false;
      FOR_BB_INSNS (bbs[i], insn)
	if (NONDEBUG_INSN_P (insn))
	  {
	    any = true;
	    if (CALL_P (insn))
	      ok = nocall = false;
	    rtx pat = single_set (insn);
	    if (pat && REG_P (SET_DEST (pat)))
	      {
		unsigned r = REGNO (SET_DEST (pat));
		rtx src = SET_SRC (pat);
		if (bitmap_bit_p (set, r))
		  bitmap_set_bit (multi, r);
		if (!bitmap_bit_p (set, r) && GET_CODE (src) == PLUS
		    && rtx_equal_p (XEXP (src, 0), SET_DEST (pat))
		    && CONST_INT_P (XEXP (src, 1)))
		  bitmap_set_bit (stepped, r);
		else
		  bitmap_clear_bit (stepped, r);
		bitmap_set_bit (set, r);
	      }
	  }
      full += any;
    }
  /* A register set once to a stepped one plus an invariant steps too
     (PolyBench's adi reads a column, u[j][i - 1] ... u[j][i + 1], through
     ivtmp + the column's offset): the pipeliner takes such addresses.  */
  for (unsigned i = 0; i < loop->num_nodes; i++)
    {
      rtx_insn *insn;
      FOR_BB_INSNS (bbs[i], insn)
	{
	  rtx pat = NONDEBUG_INSN_P (insn) ? single_set (insn) : NULL_RTX;
	  if (!pat || !REG_P (SET_DEST (pat)) || GET_CODE (SET_SRC (pat)) != PLUS
	      || bitmap_bit_p (multi, REGNO (SET_DEST (pat)))
	      || bitmap_bit_p (stepped, REGNO (SET_DEST (pat))))
	    continue;
	  rtx a = XEXP (SET_SRC (pat), 0), b = XEXP (SET_SRC (pat), 1);
	  auto st = [&] (rtx x)
	    {
	      return REG_P (x) && bitmap_bit_p (stepped, REGNO (x));
	    };
	  auto inv = [&] (rtx x)
	    {
	      return CONST_INT_P (x) || (REG_P (x) && !bitmap_bit_p (set, REGNO (x)));
	    };
	  if ((st (a) && inv (b)) || (st (b) && inv (a)))
	    bitmap_set_bit (derived, REGNO (SET_DEST (pat)));
	}
    }
  /* An arm if-conversion will predicate, and its join, join the block
     of its branch.  */
  int merged = 0;
  for (unsigned i = 0; i < loop->num_nodes; i++)
    if (e2k_ifcvt_arm_p (bbs[i], loop))
      {
	basic_block j = single_succ (bbs[i]);
	merged++;
	if (EDGE_COUNT (j->preds) == 2
	    && find_edge (single_pred (bbs[i]), j))
	  merged++;
      }
  /* Without stores there are no memory dependences to understand.  A
     while loop of a few blocks (xz's lzma_memcmplen, "while (len <
     limit && a[len] == b[len]) len++", two exits) is a while loop to
     e2k_modsched; unrolled, it is a chain of exits to different places
     that nothing pipelines.  One exit and a branch inside (CoreMark's
     crcu8) stays unrolled, for the scheduler.  */
  bool store = false;
  for (unsigned i = 0; i < loop->num_nodes; i++)
    {
      rtx_insn *insn;
      FOR_BB_INSNS (bbs[i], insn)
	if (NONJUMP_INSN_P (insn))
	  {
	    subrtx_iterator::array_type array;
	    FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
	      if (GET_CODE (*iter) == SET && MEM_P (SET_DEST (*iter)))
		store = true;
	  }
    }
  /* The one block with something in it.  */
  basic_block body = NULL;
  for (unsigned i = 0; i < loop->num_nodes; i++)
    {
      rtx_insn *insn;
      FOR_BB_INSNS (bbs[i], insn)
	if (NONDEBUG_INSN_P (insn) && !JUMP_P (insn))
	  body = bbs[i];
    }
  /* A loop known to run long is worth pipelining for any gain
     (e2k_ms_long_p).  */
  class niter_desc *desc = get_simple_loop_desc (loop);
  bool longrun = (e2k_ms_long && desc->simple_p && desc->const_iter
		  && desc->niter >= E2K_MS_LONG);
  bool rec = (full == 1 && ok && body
	      && e2k_loop_rec_bound_p (body, longrun));
  if (!store && ok && !rec && (full <= 1 || (full <= 3 && !single_exit (loop))))
    {
      free (bbs);
      return 1;
    }
  /* The one address the pipeliner can't follow, if there is just one,
     and the loads and stores through it.  A single load there, with
     stores to the same address (a histogram: NPB IS's
     "prv_buff1[key_buff2[i]]++"), is one lock load for e2k_modsched,
     which takes one; unrolled, it would be four.  */
  rtx other = NULL_RTX;
  bool others = false;
  int other_loads = 0, other_stores = 0;
  for (unsigned i = 0; nocall && i < loop->num_nodes; i++)
    {
      rtx_insn *insn;
      FOR_BB_INSNS (bbs[i], insn)
	if (NONDEBUG_INSN_P (insn))
	  {
	    rtx sset = single_set (insn);
	    subrtx_iterator::array_type array;
	    FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
	      if (MEM_P (*iter))
		{
		  rtx a = XEXP (*iter, 0);
		  rtx t[2] = { a, NULL_RTX };
		  if (GET_CODE (a) == PLUS)
		    {
		      t[0] = XEXP (a, 0);
		      t[1] = XEXP (a, 1);
		    }
		  for (int k = 0; k < 2; k++)
		    if (t[k] && !CONST_INT_P (t[k])
			&& !(REG_P (t[k])
			     && (!bitmap_bit_p (set, REGNO (t[k]))
				 || bitmap_bit_p (stepped, REGNO (t[k]))
				 || bitmap_bit_p (derived, REGNO (t[k])))))
		      {
			ok = false;
			if (!other)
			  other = a;
			else if (!rtx_equal_p (other, a))
			  others = true;
			if (!sset || SET_DEST (sset) != *iter)
			  other_loads++;
			else
			  other_stores++;
			break;
		      }
		}
	  }
    }
  free (bbs);
  /* Only with a store there too: a load alone that the pipeliner can't
     place stays unrolled for the scheduler (NPB FT's evolve,
     "ex[t * indexmap[k][j][i]]": 7% slower not unrolled).  */
  bool one_load = (nocall && !ok && other && !others && other_loads == 1
		   && other_stores > 0);
  if (dump_file)
    fprintf (dump_file, ";; e2k: loop %d: %d blocks (%d merged), %s\n",
	     loop->num, full, merged,
	     ok ? "simple addresses" : one_load ? "one other load" : "other");
  return full - merged <= 1 && (ok || one_load) && !rec ? 1 : nunroll;
}

/* A callee may run a loop of its own, which leaves %lsr finished.  */
static const char *
e2k_invalid_within_doloop (const rtx_insn *insn)
{
  if (CALL_P (insn))
    return "call in the loop";
  if (JUMP_P (insn) && computed_jump_p (insn))
    return "computed jump in the loop";
  return NULL;
}

static rtx
e2k_hwloop_pattern_reg (rtx_insn *insn)
{
  if (!JUMP_P (insn)
      || (recog_memoized (insn) != CODE_FOR_e2k_doloop_end
	  && recog_memoized (insn) != CODE_FOR_e2k_doloop_end_wide))
    return NULL_RTX;
  rtx reg = SET_DEST (XVECEXP (PATTERN (insn), 0, 1));
  return REG_P (reg) ? reg : NULL_RTX;
}

static bool
e2k_hwloop_opt (hwloop_info loop)
{
  if (loop->depth > 1 || loop->has_call || loop->has_asm
      || loop->iter_reg_used || loop->iter_reg_used_outside
      || loop->incoming == NULL || loop->start_label == NULL)
    return false;
  if (!GPR_REGNO_P (REGNO (loop->iter_reg)))
    return false;

  /* A loop of two blocks whose first one leaves early (xz's
     lzma_memcmplen, "while (len < limit && a[len] == b[len]) len++",
     counted by GCC) is a while loop to e2k_modsched; counted on %lsr it
     would end in "ct ? ~p && %NOT_LOOP_END", which it doesn't do yet.  */
  if (e2k_pipeline && e2k_pipeline_while && loop->blocks.length () == 2)
    {
      basic_block lb = BLOCK_FOR_INSN (loop->loop_end), bb;
      unsigned i;
      FOR_EACH_VEC_ELT (loop->blocks, i, bb)
	if (bb != lb)
	  {
	    edge e;
	    edge_iterator ei;
	    FOR_EACH_EDGE (e, ei, bb->succs)
	      if (!loop->blocks.contains (e->dest))
		return false;
	  }
    }

  /* A CTPR nothing in the loop touches.  */
  int k;
  for (k = 0; k < 2; k++)
    {
      rtx ctpr = gen_rtx_REG (DImode, CTPR1_REGNUM + k);
      bool used = false;
      basic_block bb;
      unsigned i;
      FOR_EACH_VEC_ELT (loop->blocks, i, bb)
	{
	  rtx_insn *insn;
	  FOR_BB_INSNS (bb, insn)
	    if (NONDEBUG_INSN_P (insn) && insn != loop->loop_end
		&& reg_mentioned_p (ctpr, PATTERN (insn)))
	      used = true;
	}
      if (!used)
	break;
    }
  if (k == 2)
    return false;
  rtx ctpr = gen_rtx_REG (DImode, CTPR1_REGNUM + k);

  /* A strip-mined loop computes its first chunk in the DImode scratch
     of the loop end; the predicate scratch tests for more chunks after
     the loop.  RA kept both out of the registers live into the loop.  */
  rtx pat = PATTERN (loop->loop_end);
  bool wide = recog_memoized (loop->loop_end) == CODE_FOR_e2k_doloop_end_wide;
  rtx pred = NULL_RTX, tmp = NULL_RTX;
  if (wide)
    {
      pred = XEXP (XVECEXP (pat, 0, 3), 0);
      tmp = XEXP (XVECEXP (pat, 0, 4), 0);
      if (!REG_P (pred) || !REG_P (tmp)
	  || REGNO_REG_SET_P (df_get_live_in (loop->head), REGNO (tmp))
	  || REGNO_REG_SET_P (df_get_live_in (loop->head), REGNO (pred)))
	return false;
    }

  /* Many ways in (a vectorized loop after its peeled, fully unrolled
     alignment prologue has eight) share one block, so that the setup
     below and a pipelined loop's prologue (e2k_modsched copies it onto
     each way in) are emitted once.  */
  edge e;
  edge_iterator ei;
  if (loop->incoming->length () > 2)
    {
      edge fall = NULL;
      FOR_EACH_EDGE (e, ei, loop->incoming)
	if (e->flags & (EDGE_COMPLEX | EDGE_EH))
	  return false;
	else if (e->flags & EDGE_FALLTHRU)
	  fall = e;
      if (!fall)
	fall = (*loop->incoming)[0];
      auto_vec<edge> others;
      FOR_EACH_EDGE (e, ei, loop->incoming)
	if (e != fall)
	  others.safe_push (e);
      basic_block fwd = split_edge (fall);
      for (edge o : others)
	if (!redirect_edge_and_branch (o, fwd))
	  redirect_edge_and_branch_force (o, fwd);
      vec_free (loop->incoming);
      vec_safe_push (loop->incoming, single_succ_edge (fwd));
    }

  /* Before the loop: %lsr = count | vlc, at least 4 cycles ahead, and
     the CTPR.  The iteration register is dead once the loop doesn't
     count it down, or holds the iterations after the first chunk:
     ((count - 1) & -CHUNK).  The first chunk is ((count - 1) &
     (CHUNK - 1)) + 1.  */
  FOR_EACH_EDGE (e, ei, loop->incoming)
    {
      start_sequence ();
      /* The CTPR first: it reads nothing, and the count's chain is
	 serial.  */
      rtx_insn *disp = emit_insn (gen_e2k_disp_label (ctpr,
						      loop->start_label));
      add_reg_note (disp, REG_LABEL_OPERAND, loop->start_label);
      LABEL_NUSES (loop->start_label)++;
      rtx lsr = loop->iter_reg;
      if (wide)
	{
	  rtx r = loop->iter_reg;
	  emit_insn (gen_adddi3 (r, r, constm1_rtx));
	  emit_insn (gen_anddi3 (tmp, r,
				 gen_int_mode (E2K_LSR_CHUNK - 1, DImode)));
	  emit_insn (gen_anddi3 (r, r, gen_int_mode (-E2K_LSR_CHUNK, DImode)));
	  emit_insn (gen_adddi3 (tmp, tmp,
				 gen_int_mode (E2K_LSR_VLC + 1, DImode)));
	  lsr = tmp;
	}
      else if (!e2k_fold_vlc (e->src, lsr))
	emit_insn (gen_iordi3 (lsr, lsr, gen_int_mode (E2K_LSR_VLC, DImode)));
      emit_insn (gen_e2k_rwd_lsr (lsr));
      emit_insn (gen_e2k_lsr_wait ());
      rtx_insn *seq = end_sequence ();
      insert_insn_on_edge (seq, e);
    }

  rtx_insn *jump
    = emit_jump_insn_before (wide
			     ? gen_e2k_hwloop_end_wide (ctpr, loop->start_label,
							loop->iter_reg, pred)
			     : gen_e2k_hwloop_end (ctpr, loop->start_label),
			     loop->loop_end);
  JUMP_LABEL (jump) = loop->start_label;
  LABEL_NUSES (loop->start_label)++;
  HOST_WIDE_INT iters = INTVAL (XVECEXP (XVECEXP (pat, 0, 2), 0, 1));
  if (iters != -1)
    {
      if (!e2k_loop_iters)
	e2k_loop_iters = new hash_map<int_hash<int, 0, -1>, HOST_WIDE_INT>;
      e2k_loop_iters->put (INSN_UID (jump), iters);
    }
  delete_insn (loop->loop_end);
  return true;
}

/* When the count COUNT that block BB hands its hardware loop is computed
   last in BB as X + C and nothing after reads it on another way, compute
   X + (C | vlc) there instead (the count is below 2^32, so adding the
   bit is ORing it): one operation less on the way in.  */
static bool
e2k_fold_vlc (basic_block bb, rtx count)
{
  if (!single_succ_p (bb))
    return false;
  for (rtx_insn *insn = BB_END (bb); insn != PREV_INSN (BB_HEAD (bb));
       insn = PREV_INSN (insn))
    {
      if (!NONDEBUG_INSN_P (insn))
	continue;
      if (!reg_set_p (count, insn))
	{
	  if (reg_mentioned_p (count, PATTERN (insn)))
	    return false;
	  continue;
	}
      rtx set = single_set (insn);
      if (!set || !REG_P (SET_DEST (set))
	  || REGNO (SET_DEST (set)) != REGNO (count)
	  || GET_CODE (SET_SRC (set)) != PLUS
	  || !CONST_INT_P (XEXP (SET_SRC (set), 1))
	  || INTVAL (XEXP (SET_SRC (set), 1)) < 0
	  || INTVAL (XEXP (SET_SRC (set), 1)) >= E2K_LSR_VLC
	  || reg_overlap_mentioned_p (count, XEXP (SET_SRC (set), 0)))
	return false;
      rtx c = gen_int_mode (INTVAL (XEXP (SET_SRC (set), 1)) | E2K_LSR_VLC,
			    GET_MODE (count));
      return validate_change (insn, &XEXP (SET_SRC (set), 1), c, false);
    }
  return false;
}

/* e2k_doloop_end stays and decrements, compares and branches itself.  */
/* A loop left to e2k_doloop_end: split it into the decrement, the
   compare and the branch, so that the scheduler and the while-loop
   pipeliner see ordinary operations.  */
static void
e2k_hwloop_fail (hwloop_info loop)
{
  rtx_insn *end = loop->loop_end;
  if (!end || (recog_memoized (end) != CODE_FOR_e2k_doloop_end
	       && recog_memoized (end) != CODE_FOR_e2k_doloop_end_wide))
    return;
  rtx pat = PATTERN (end);
  rtx reg = SET_DEST (XVECEXP (pat, 0, 1));
  rtx pred = XEXP (XVECEXP (pat, 0, 3), 0);
  if (!REG_P (reg) || !REG_P (pred) || !GPR_REGNO_P (REGNO (reg))
      || !PRED_REGNO_P (REGNO (pred)))
    {
      if (dump_file)
	fprintf (dump_file, ";; e2k_hwloop_fail: insn %d not split\n",
		 INSN_UID (end));
      return;
    }
  rtx label = JUMP_LABEL (end);
  rtx_insn *a = emit_insn_before (gen_adddi3 (reg, reg, constm1_rtx), end);
  /* Compares compute eq, lt, le, ltu, leu: back while not equal.  */
  rtx_insn *c = emit_insn_before (gen_rtx_SET (pred,
					       gen_rtx_EQ (BImode, reg,
							   const0_rtx)), end);
  rtx_insn *j = emit_jump_insn_before
    (gen_rtx_SET (pc_rtx,
		  gen_rtx_IF_THEN_ELSE (VOIDmode,
					gen_rtx_EQ (VOIDmode, pred, const0_rtx),
					gen_rtx_LABEL_REF (Pmode, label),
					pc_rtx)), end);
  if (recog_memoized (a) < 0 || recog_memoized (c) < 0
      || recog_memoized (j) < 0)
    {
      if (dump_file)
	fprintf (dump_file, ";; e2k_hwloop_fail: can't split insn %d "
		 "(%d %d %d)\n", INSN_UID (end), recog_memoized (a),
		 recog_memoized (c), recog_memoized (j));
      delete_insn (a);
      delete_insn (c);
      delete_insn (j);
      return;
    }
  JUMP_LABEL (j) = label;
  LABEL_NUSES (label)++;
  if (rtx note = find_reg_note (end, REG_BR_PROB, NULL_RTX))
    add_int_reg_note (j, REG_BR_PROB, XINT (note, 0));
  delete_insn (end);
}

static struct hw_doloop_hooks e2k_doloop_hooks =
{
  e2k_hwloop_pattern_reg,
  e2k_hwloop_opt,
  e2k_hwloop_fail
};

/* ------------------------------------------------------------------ */
/* Software pipelining (modulo scheduling)                             */
/* ------------------------------------------------------------------ */

/* After hw-doloop has made an innermost loop count on %lsr, a loop that
   is one basic block is modulo scheduled here, after register
   allocation, the way lcc builds its counted loops (spec/isa/loops.md,
   "How lcc builds loops"):

   - Every register the body defines is renamed into the rotating
     registers %b[]: the loop end gets "abn abnf=1, abnt=1", after which
     the old %b[N] is the new %b[N+2], so each iteration's values get
     fresh names and only true dependences constrain the schedule.  A
     value defined in stage D and read in stage U of an iteration D + K
     iterations later is %b[X + 2 (U - D + K)] there.
   - The kernel (II cycles, S stages) runs exactly n times, n the trip
     count already in %lsr.  The first S - 1 stages of iterations
     0 .. S - 2 are peeled before the loop (the prologue), with the
     names they would have after the rotations they skip.  There is no
     epilogue: the last n kernel iterations run the early stages of
     iterations past the end, so those stages must have no effect.
     Stores therefore all go in the last stage, and every other
     operation is speculative (",sm"): a load past the end of an array
     gives a diagnostic value instead of a fault, and so does an
     operation on one, which nothing then stores.
   - The ring lies between the window registers and the outgoing
     registers %b[0..7] of calls, so the diagnostic values that the
     last iterations leave behind never reach a callee's argument
     slots, which a variadic callee stores (a tag trap), and calls still
     hand over only those 4 pairs (a callee's setwd must cover what it
     inherits).
   - Values live into the loop are copied into the ring in the
     prologue, values live after it copied out on the exit edge, and
     setbn gives the outgoing registers back.

   Dependences between memory accesses are exact when both address the
   same array through one induction register (base + step per
   iteration); otherwise may_alias_p, which ignores offsets, decides
   whether they may conflict in any iteration.  */

/* Per-insn flags for final: print ",sm", print abn.  */
static vec<unsigned char> e2k_ms_flags;

/* Registers read after the loop by copies still waiting on the exit
   edge (e2k_ms_move_b), which dataflow doesn't see yet.  */
static HARD_REG_SET e2k_ms_live_out_extra;

/* Clocks of the kernel instructions, applied after schedule_ebbs.  */
struct e2k_ms_clock { rtx_insn *insn; int clock; };
static vec<e2k_ms_clock> e2k_ms_clocks;

static unsigned
e2k_ms_flag (const rtx_insn *insn)
{
  unsigned uid = INSN_UID (insn);
  return uid < e2k_ms_flags.length () ? e2k_ms_flags[uid] : 0;
}

static void
e2k_ms_set_flag (rtx_insn *insn, unsigned f)
{
  unsigned uid = INSN_UID (insn);
  if (uid >= e2k_ms_flags.length ())
    e2k_ms_flags.safe_grow_cleared (uid + 64);
  e2k_ms_flags[uid] |= f;
}

#define E2K_MS_MAX_NODES 256
#define E2K_MS_MAX_USES 4
#define E2K_MS_MAX_II 48

struct e2k_ms_use
{
  unsigned regno;
  int value;			/* a predicate's: its defining node */
  int dist;			/* 0: this iteration's value; 1: the last */
  bool pred;
};

struct e2k_ms_node
{
  rtx_insn *insn;
  int value;			/* value defined, or -1 */
  int nuses;
  e2k_ms_use uses[E2K_MS_MAX_USES];
  rtx mem;			/* memory reference, if any */
  bool store;
  bool pred;			/* sets a predicate (a while loop's exit test) */
  bool dpred;			/* sets a predicate merges or stores read */
  bool dead;			/* a copy folded into its source */
  bool lock;			/* a lock load (DAM) */
  int chk;			/* a check load: its lock load's node, else -1 */
  /* A load read through array prefetch (e2k_ms_mark_apb): INSN is its
     mova, ORIG the load, which the prologue keeps.  It reads an
     APB_SIZE-byte element at APB_IV + APB_INV + APB_OFF in iteration 0
     (APB_INV INVALID_REGNUM if none), APB_STEP bytes further each
     iteration, through descriptor APB_D (APB_IV + APB_INV on the way
     in); channel, area, offset in the area's step and whether it
     advances the area once scheduled (e2k_ms_apb_assign).  */
  bool apb;
  rtx_insn *orig;
  int apb_size, apb_d, apb_chan, apb_area, apb_ind, apb_am;
  unsigned apb_iv, apb_inv;
  HOST_WIDE_INT apb_off, apb_step;
  /* An AAU store (e2k_ms_mark_staa): INSN is its staa, ORIG the store.
     Iteration 0 writes APB_IV + APB_INV + APB_OFF, APB_STEP bytes further
     each iteration, through descriptor APB_D, whose base adds
     L->apb_adj[APB_D], and store index STAA_STI (0 on the way in), which
     %aaincr STAA_INCR steps (e2k_ms_staa_assign).  */
  bool staa;
  int staa_sti, staa_incr;
  /* What the kernel doesn't run: a node whose result only the movas'
     loads in the prologue and the AAU stores' addresses read
     (e2k_ms_mark_kdead).  The prologue runs it.  */
  bool kdead;
  int time;
  int pname;			/* a predicate's ring name in its iteration */
  /* A store that reads its address register from a later iteration,
     with REBASE_OFF taken off its offset (e2k_ms_rebase_stores): its
     use REBASE_USE, whose distance was REBASE_DIST0.  */
  int rebase_use, rebase_dist0;
  HOST_WIDE_INT rebase_off;
};

struct e2k_ms_value
{
  int node;			/* defining node */
  unsigned regno;
  /* The registers holding the instances of the iterations before the
     loop, -1 and -2 (INVALID_REGNUM if not known).  */
  unsigned init[2];
  machine_mode mode;
  bool carried;			/* read by the next iteration */
  bool carried2;		/* read two iterations later */
  int out_dist;			/* the instance of the iteration this many
				   before the last is read after the loop;
				   -1 if none is */
  int span;			/* rotations from the def to the last use */
  int name;			/* %b[] name in the defining iteration */
};

/* A register live after the loop, copied from VALUE's instance of the
   iteration DIST before the last.  HEND: a two-block while loop's value
   at the end of its first block, copied over the other under the first
   block's exit condition.  */
struct e2k_ms_out
{
  unsigned regno;
  machine_mode mode;
  int value;
  int dist;
  bool hend;
};

struct e2k_ms_dep
{
  int from, to, lat, dist;
  /* The part of LAT for a result crossing clusters, dropped in
     recurrences (e2k_ms_pipeline).  */
  int cross;
};

struct e2k_ms_loop
{
  basic_block bb;
  rtx_insn *jump;
  /* A one-block while loop's disp of its loop end's CTPR, in the loop
     (the loop end prepared like any branch): it goes to the start of
     each prologue, as a second block's does (e2k_ms_wl).  */
  rtx_insn *edisp;
  auto_vec<rtx_insn *> insns;	/* the body in order, without the jump */
  int n;
  e2k_ms_node nodes[E2K_MS_MAX_NODES];
  auto_vec<e2k_ms_value> values;
  auto_vec<e2k_ms_dep> deps;
  auto_vec<e2k_ms_out> outs;
  int ii, stages, pairs;
  /* The predicate ring (setbp psz = NPRED - 1), or 0: predicates keep
     their registers.  EXIT is where the loop ends.  */
  int npred;
  basic_block exit;
  /* While loops: STAY is the node setting the predicate the loop end
     tests.  Of two blocks, the first block's insns are the first NH,
     and C1 is the node setting P1, its exit taken when (E1 P1 0): a
     compare, or a landp of compares (a chain of branches merged,
     e2k_merge_chains).  C1S are the nodes computing P1 in order, which
     run again after the loop to tell the exits apart.  */
  bool wl;
  int stay, nh, c1;
  int nh0;			/* the first block's insns in INSNS */
  auto_vec<int> c1s;
  rtx p1, pstay;
  enum rtx_code e1;
  /* Where the first block's exit goes, if not where the loop ends.  */
  basic_block x1;
  /* Data speculation (spec/isa/speculation.md, DAM): with WANT_DAM a
     load that may read what a store of the loop wrote moves above it as
     a lock load, node DAM, checked by node KCHK in the last stage.
     DAM_DEPS are the store -> load dependences left out for it; MAY_DAM
     says there were some to leave out.  REC lists the instances (node,
     iterations after the checked one) that ran with the early value
     before the check, which a failed check redoes, and EXT the
     lifetimes that redoing extends (value, cycle).  */
  bool want_dam, may_dam;
  int dam, kchk;
  auto_vec<e2k_ms_dep> dam_deps;
  auto_vec<std::pair<int, int> > rec, ext;
  /* Array prefetch (spec/isa/apb.md): APB_OK when this loop may use it,
     NAPB loads that do through NAPB_D descriptors, APB_TMP a register
     free on the ways in; %aaincr1 .. APB_NINCR hold APB_INCR[1 ..]
     (e2k_ms_apb_assign).  */
  bool apb_ok = false;
  int napb = 0, napb_d = 0, apb_nincr = 0;
  /* AAU stores (e2k_ms_mark_staa): STAA_OK when this loop may use them,
     NSTAA stores through descriptors NAPB_D .. NAPB_D + NSTAA_D - 1.  */
  bool staa_ok = false;
  int nstaa = 0, nstaa_d = 0;
  /* The AAU stores don't lower the bound on II (e2k_ms_pipeline): try
     again without them, keeping array prefetch.  */
  bool staa_unwanted = false;
  HOST_WIDE_INT apb_incr[8];
  /* What descriptor D's base adds to its induction variable (and
     invariant): 0 or less, so that no area's disp is negative
     (e2k_ms_apb_assign); an AAU store's offset (e2k_ms_staa_assign).  */
  HOST_WIDE_INT apb_adj[32];
  unsigned apb_tmp = INVALID_REGNUM;
  /* Window registers and %g16-%g31 (the kernel restores those after a
     signal handler, spec/abi/registers.md) that no value of the loop
     needs around it nor reads as an invariant, for values outside the
     ring (e2k_ms_assign_names).  */
  HARD_REG_SET fix_free;
  /* Invariants in %b[K] with no register free for them (e2k_ms_move_b):
     bit K of BINV; the loop reads BMAP[K] instead, copied in on each way
     in before setbn renames %b[].  */
  unsigned binv = 0;
  unsigned bmap[8];
};

/* setbn_enter for L: it uses the %b[0..7] live after the loop, whose
   values pass through it, and nothing for the others, which would
   otherwise look live before every pipelined loop and so live out of an
   earlier one (NPB SP's zeta-direction fluxes, refused for a %b[1] only
   the next pipelined loop's setbn read).  */
static rtx
e2k_ms_gen_setbn_enter (e2k_ms_loop *l)
{
  rtx u[8];
  bitmap a = df_get_live_in (l->exit);
  bitmap b = l->x1 ? df_get_live_in (l->x1) : a;
  for (int k = 0; k < 8; k++)
    u[k] = (bitmap_bit_p (a, B0_REGNUM + k) || bitmap_bit_p (b, B0_REGNUM + k)
	    ? gen_rtx_REG (DImode, B0_REGNUM + k) : const0_rtx);
  return gen_e2k_setbn_enter (GEN_INT (l->pairs), GEN_INT (l->npred), u[0],
			      u[1], u[2], u[3], u[4], u[5], u[6], u[7]);
}

/* Whether a loop body insn can be pipelined: one SET of a register or
   memory, of a kind that has a speculative form, or a store under a
   predicate (if-conversion's); compares into predicates that merges and
   such stores read, and in a while loop (WL) also the compares and
   landp of its exit test, which only read registers and each other.  */
static bool
e2k_ms_insn_ok (rtx_insn *insn, bool wl)
{
  if (!NONJUMP_INSN_P (insn) || recog_memoized (insn) < 0)
    return false;
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) == COND_EXEC)
    {
      rtx test = COND_EXEC_TEST (pat);
      if ((GET_CODE (test) != NE && GET_CODE (test) != EQ)
	  || !REG_P (XEXP (test, 0)) || !PRED_REGNO_P (REGNO (XEXP (test, 0)))
	  || XEXP (test, 1) != const0_rtx)
	return false;
      pat = COND_EXEC_CODE (pat);
      if (GET_CODE (pat) != SET || !MEM_P (SET_DEST (pat)))
	return false;
    }
  if (GET_CODE (pat) != SET || volatile_refs_p (pat)
      || side_effects_p (SET_SRC (pat)))
    return false;
  enum attr_type t = get_attr_type (insn);
  if (REG_P (SET_DEST (pat)) && PRED_REGNO_P (REGNO (SET_DEST (pat))))
    {
      /* FP compares too (LAME's quantize_lines_xrpow_01, "ix[0] =
	 (compareval0 > xr[0]) ? 0 : 1"): speculated as the loop's other
	 FP operations, so not under -mno-spec-fp (e2k_ms_analyze).  */
      if (t != TYPE_CMP && t != TYPE_FCMP && (t != TYPE_PLOG || !wl))
	return false;
      subrtx_iterator::array_type array;
      FOR_EACH_SUBRTX (iter, array, SET_SRC (pat), NONCONST)
	{
	  const_rtx x = *iter;
	  if (MEM_P (x))
	    return false;
	  if (REG_P (x)
	      && (REG_NREGS (x) != 1 || BX_REGNO_P (REGNO (x))
		  || (t == TYPE_PLOG
		      ? !PRED_REGNO_P (REGNO (x)) : !GPR_REGNO_P (REGNO (x)))))
	    return false;
	}
      return true;
    }
  switch (t)
    {
    case TYPE_ALU: case TYPE_ALU14: case TYPE_ALU0134: case TYPE_MUL:
    case TYPE_FP:
    case TYPE_FMA: case TYPE_FFMA: case TYPE_FCVT: case TYPE_LOAD:
    case TYPE_STORE:
    case TYPE_PINT: case TYPE_PINT14: case TYPE_PMUL: case TYPE_PANY:
      break;
    /* FP divides (PolyBench's seidel-2d): the divider in ALC5 takes one
       every 2 cycles (e2k_ms_place); lcc speculates them in its
       pipelined loops too (spec/isa/speculation.md).  Not the square
       roots: fsqrts conflicts 5 cycles apart, fsqrttd reads two.  */
    case TYPE_FDIV:
      if (GET_CODE (SET_SRC (pat)) != DIV)
	return false;
      break;
    default:
      return false;
    }
  rtx dest = SET_DEST (pat);
  if (REG_P (dest))
    {
      unsigned r = REGNO (dest);
      if (REG_NREGS (dest) != 1 || !GPR_REGNO_P (r)
	  || BX_REGNO_P (r) || fixed_regs[r])
	return false;
    }
  else if (!MEM_P (dest))
    return false;
  int nmem = 0;
  /* A merge reads the predicate of its condition.  */
  rtx mcond = (GET_CODE (SET_SRC (pat)) == IF_THEN_ELSE
	       ? XEXP (XEXP (SET_SRC (pat), 0), 0) : NULL_RTX);
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, pat, NONCONST)
    {
      const_rtx x = *iter;
      if (MEM_P (x))
	{
	  nmem++;
	  if (MEM_VOLATILE_P (x) || GET_MODE (x) == BLKmode)
	    return false;
	}
      else if (REG_P (x) && x == mcond && PRED_REGNO_P (REGNO (x)))
	continue;
      else if (REG_P (x)
	       && (REG_NREGS (x) != 1
		   || BX_REGNO_P (REGNO (x)) || !GPR_REGNO_P (REGNO (x))))
	return false;
    }
  return nmem <= 1;
}

/* The registers X reads.  */
static bool
e2k_ms_note_uses (e2k_ms_node *node, rtx x)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, x, NONCONST)
    if (REG_P (*iter))
      {
	unsigned r = REGNO (*iter);
	int k;
	for (k = 0; k < node->nuses; k++)
	  if (node->uses[k].regno == r)
	    break;
	if (k < node->nuses)
	  continue;
	if (node->nuses == E2K_MS_MAX_USES)
	  return false;
	node->uses[node->nuses].regno = r;
	node->uses[node->nuses].value = -1;
	node->uses[node->nuses].dist = 0;
	node->nuses++;
      }
  return true;
}

/* An address as INV + IV + OFFSET: INV a loop-invariant register (or
   none), IV a register the loop steps by a constant (or none).  */
struct e2k_ms_addr
{
  unsigned inv, iv;		/* INVALID_REGNUM if absent */
  HOST_WIDE_INT offset;
  bool ok;
};

static void
e2k_ms_add_term (e2k_ms_addr *a, rtx x, const HOST_WIDE_INT *step)
{
  if (CONST_INT_P (x))
    a->offset += INTVAL (x);
  else if (REG_P (x) && step[REGNO (x)] != 0)
    {
      if (a->iv != INVALID_REGNUM)
	a->ok = false;
      a->iv = REGNO (x);
    }
  else if (REG_P (x) && step[REGNO (x)] == 0)
    {
      if (a->inv != INVALID_REGNUM)
	a->ok = false;
      a->inv = REGNO (x);
    }
  else
    a->ok = false;
}

/* Decompose MEM's address; STEP[r] is the per-iteration step of
   induction register r (0: invariant, HOST_WIDE_INT_MIN: varies).  */
static e2k_ms_addr
e2k_ms_decompose (rtx mem, const HOST_WIDE_INT *step)
{
  e2k_ms_addr a = { INVALID_REGNUM, INVALID_REGNUM, 0, true };
  rtx x = XEXP (mem, 0);
  if (GET_CODE (x) == PLUS)
    {
      e2k_ms_add_term (&a, XEXP (x, 0), step);
      e2k_ms_add_term (&a, XEXP (x, 1), step);
    }
  else
    e2k_ms_add_term (&a, x, step);
  if (a.inv != INVALID_REGNUM && step[a.inv] == HOST_WIDE_INT_MIN)
    a.ok = false;
  if (a.iv != INVALID_REGNUM && step[a.iv] == HOST_WIDE_INT_MIN)
    a.ok = false;
  return a;
}

static bool e2k_ms_inv_delta (unsigned, unsigned, basic_block,
			      HOST_WIDE_INT *, int = 0);

/* What INSN's SET_SRC, a register or a register plus a constant, is
   in terms of a register at the start of INSN's block: *C plus the
   register returned (through the block's own copies and constant adds
   before INSN: a latch that steps a pointer through a temporary,
   "t = r + 16000; ...; r = t"), or NULL.  */
static rtx
e2k_ms_block_start_value (rtx_insn *insn, HOST_WIDE_INT *c)
{
  basic_block bb = BLOCK_FOR_INSN (insn);
  *c = 0;
  for (int k = 0; k < 4; k++)
    {
      rtx set = PATTERN (insn);
      if (GET_CODE (set) != SET || !REG_P (SET_DEST (set))
	  || GET_MODE (SET_DEST (set)) != DImode)
	return NULL_RTX;
      rtx x = SET_SRC (set);
      if (GET_CODE (x) == PLUS && CONST_INT_P (XEXP (x, 1)))
	{
	  *c += INTVAL (XEXP (x, 1));
	  x = XEXP (x, 0);
	}
      if (!REG_P (x) || GET_MODE (x) != DImode)
	return NULL_RTX;
      rtx_insn *def = NULL;
      for (rtx_insn *i = PREV_INSN (insn);
	   i && i != PREV_INSN (BB_HEAD (bb)); i = PREV_INSN (i))
	if (INSN_P (i) && reg_set_p (x, i))
	  {
	    def = i;
	    break;
	  }
      if (!def)
	return x;
      insn = def;
    }
  return NULL_RTX;
}

/* For e2k_ms_inv_delta: what the pair of IA (setting RA) and IB
   (setting RB), the only insns of their block that set them, does to
   RA - RB: 1, it becomes *D; 2, it stays (both stepped by one
   constant); 0, anything else.  DEPTH: e2k_ms_inv_delta's.  */
static int
e2k_ms_pair_delta (rtx_insn *ia, rtx_insn *ib, unsigned ra, unsigned rb,
		   HOST_WIDE_INT *d, int depth)
{
  HOST_WIDE_INT ca, cb;
  rtx xa = e2k_ms_block_start_value (ia, &ca);
  rtx xb = e2k_ms_block_start_value (ib, &cb);
  if (!xa || !xb)
    return 0;
  if (REGNO (xa) == ra && REGNO (xb) == rb)
    return ca == cb ? 2 : 0;
  /* From one register: its value at the block's start.  */
  if (REGNO (xa) == REGNO (xb))
    {
      *d = ca - cb;
      return 1;
    }
  /* From two registers apart by a constant themselves at the block's
     start (seidel-2d's rows start as copies of their first values, set
     before the time loop).  */
  HOST_WIDE_INT dx;
  if (depth < 3
      && e2k_ms_inv_delta (REGNO (xa), REGNO (xb), BLOCK_FOR_INSN (ia), &dx,
			   depth + 1))
    {
      *d = dx + ca - cb;
      return 1;
    }
  return 0;
}

/* The one insn of BB that sets register R, or NULL; *N: how many do
   (a call that clobbers it counts).  */
static rtx_insn *
e2k_ms_block_def (basic_block bb, rtx r, int *n)
{
  rtx_insn *d = NULL, *insn;
  *n = 0;
  FOR_BB_INSNS (bb, insn)
    if (INSN_P (insn) && reg_set_p (r, insn))
      {
	d = insn;
	++*n;
      }
  return d;
}

/* Whether the registers RA and RB, which block AT doesn't set, differ
   by a constant at its start, *DELTA = RA - RB: on the way back from AT
   to where they were last set, every block that sets either sets both,
   once each, and either sets them from one register plus constants (or
   one from the other, or from two registers that differ by a constant
   there, to DEPTH 3), the same difference each time, or steps both by
   one constant and is itself reached that way.  The registers are hard
   ones, which other code of the function may use for other values: only
   the definitions that reach AT matter.  PolyBench's seidel-2d updates
   its array in place through rows i - 1, i and i + 1, pointers its outer
   loop steps by a row each: the store to row i and the load of the next
   element of row i are then a known distance apart, and the loads of
   the other rows (which the alias oracle has apart) can go through
   array prefetch.  */
static bool
e2k_ms_inv_delta (unsigned ra, unsigned rb, basic_block at,
		  HOST_WIDE_INT *delta, int depth)
{
  if (ra == rb)
    {
      *delta = 0;
      return true;
    }
  if (ra == INVALID_REGNUM || rb == INVALID_REGNUM
      || !GPR_REGNO_P (ra) || !GPR_REGNO_P (rb)
      || fixed_regs[ra] || fixed_regs[rb])
    return false;
  rtx xa = gen_rtx_REG (DImode, ra), xb = gen_rtx_REG (DImode, rb);
  bool ok = true, set = false;
  HOST_WIDE_INT d = 0;
  auto_bitmap seen;
  auto_vec<basic_block> work;
  work.safe_push (at);
  while (ok && !work.is_empty ())
    {
      basic_block b = work.pop ();
      edge e;
      edge_iterator ei;
      FOR_EACH_EDGE (e, ei, b->preds)
	{
	  basic_block p = e->src;
	  if (p == ENTRY_BLOCK_PTR_FOR_FN (cfun))
	    {
	      ok = false;
	      break;
	    }
	  if (!bitmap_set_bit (seen, p->index))
	    continue;
	  int na, nb;
	  rtx_insn *ia = e2k_ms_block_def (p, xa, &na);
	  rtx_insn *ib = e2k_ms_block_def (p, xb, &nb);
	  if (na == 0 && nb == 0)
	    {
	      work.safe_push (p);
	      continue;
	    }
	  HOST_WIDE_INT pd;
	  int kind = (na != 1 || nb != 1 || p == at ? 0
		      : e2k_ms_pair_delta (ia, ib, ra, rb, &pd, depth));
	  if (kind == 1 && (!set || pd == d))
	    {
	      set = true;
	      d = pd;
	    }
	  else if (kind == 2)
	    work.safe_push (p);
	  else
	    {
	      ok = false;
	      break;
	    }
	}
    }
  ok &= set;
  if (dump_file)
    fprintf (dump_file, ";; e2k_modsched: r%u - r%u at bb %d: %s "
	     HOST_WIDE_INT_PRINT_DEC "\n", ra, rb, at->index,
	     ok ? "apart by" : "unknown", ok ? d : (HOST_WIDE_INT) 0);
  if (ok)
    *delta = d;
  return ok;
}

static void
e2k_ms_add_dep (e2k_ms_loop *l, int from, int to, int lat, int dist,
		int cross = 0)
{
  for (e2k_ms_dep &d : l->deps)
    if (d.from == from && d.to == to && d.dist == dist)
      {
	int base = MAX (d.lat - d.cross, lat - cross);
	d.lat = MAX (d.lat, lat);
	d.cross = d.lat - base;
	return;
      }
  e2k_ms_dep d = { from, to, lat, dist, cross };
  l->deps.safe_push (d);
}

/* Whether A and B, through the same pointer, a parameter (one value in
   every iteration), are at byte ranges that don't overlap: the tree
   oracle does this only while the function is in SSA form (xz's price
   table and its trailing opts array, both in *coder).  */
static bool
e2k_ms_disjoint_p (rtx a, rtx b)
{
  tree ea = MEM_EXPR (a), eb = MEM_EXPR (b);
  if (!ea || !eb)
    return false;
  ao_ref ra, rb;
  ao_ref_init (&ra, ea);
  ao_ref_init (&rb, eb);
  tree ba = ao_ref_base (&ra), bb = ao_ref_base (&rb);
  if (!ba || !bb || TREE_CODE (ba) != MEM_REF || TREE_CODE (bb) != MEM_REF
      || TREE_CODE (TREE_OPERAND (ba, 0)) != SSA_NAME
      || TREE_OPERAND (ba, 0) != TREE_OPERAND (bb, 0)
      || !SSA_NAME_IS_DEFAULT_DEF (TREE_OPERAND (ba, 0)))
    return false;
  /* The access within what its expression may touch.  */
  for (rtx m : { a, b })
    {
      ao_ref &r = m == a ? ra : rb;
      if (!MEM_OFFSET_KNOWN_P (m) || !MEM_SIZE_KNOWN_P (m)
	  || maybe_lt (MEM_OFFSET (m), 0)
	  || (r.max_size_known_p ()
	      && maybe_gt ((MEM_OFFSET (m) + MEM_SIZE (m)) * BITS_PER_UNIT,
			   r.max_size)))
	return false;
    }
  poly_offset_int oa = ra.offset, ob = rb.offset;
  oa += mem_ref_offset (ba) << LOG2_BITS_PER_UNIT;
  ob += mem_ref_offset (bb) << LOG2_BITS_PER_UNIT;
  return !ranges_maybe_overlap_p (oa, ra.max_size, ob, rb.max_size);
}

/* Whether memory references A and B may conflict in any two iterations.
   may_alias_p ignores offsets, but believes dependence cliques, and
   those of an inlined function's restrict pointers only hold within one
   call (one iteration; gcc.dg/torture/pr90328.c): trust only clique 1
   (the function's own restrict pointers) and those of loops versioned
   for aliasing, and else ask again without the trees.  */
static bool
e2k_ms_may_alias (rtx a, rtx b)
{
  if (e2k_ms_disjoint_p (a, b))
    return false;
  if (may_alias_p (a, b))
    return true;
  tree ea = MEM_EXPR (a), eb = MEM_EXPR (b);
  if (!ea || !eb)
    return false;
  tree ba = get_base_address (ea), bb = get_base_address (eb);
  if (!ba || !bb
      || (TREE_CODE (ba) != MEM_REF && TREE_CODE (ba) != TARGET_MEM_REF)
      || (TREE_CODE (bb) != MEM_REF && TREE_CODE (bb) != TARGET_MEM_REF))
    return false;
  unsigned short c = MR_DEPENDENCE_CLIQUE (ba);
  machine_function *m = cfun->machine;
  if (c == 0 || c == 1 || c != MR_DEPENDENCE_CLIQUE (bb))
    return false;
  for (int k = 0; k < m->n_av_cliques; k++)
    if (c == m->av_cliques[k])
      return false;
  rtx a2 = copy_rtx (a), b2 = copy_rtx (b);
  set_mem_expr (a2, NULL_TREE);
  set_mem_expr (b2, NULL_TREE);
  return may_alias_p (a2, b2);
}

/* Whether a store to ST can't reach a later load from LD by the types
   they access (strict aliasing): a load may not read memory last stored
   through an incompatible type, while a later store may give it a new
   one, so only such true dependences may be left out, as GCC's
   true_dependence does (may_alias_p uses no types at all).  LAME's
   count_bits: int stores into ix against float loads of xr.  */
static bool
e2k_ms_tbaa_raw_p (rtx st, rtx ld)
{
  return (e2k_ms_tbaa && flag_strict_aliasing && MEM_ALIAS_SET (st)
	  && MEM_ALIAS_SET (ld)
	  && !alias_sets_conflict_p (MEM_ALIAS_SET (st), MEM_ALIAS_SET (ld)));
}

/* Memory dependences.  POS[i] is node i's place in the body; IVDEF[r]
   the node that steps induction register r.  */
static void
e2k_ms_mem_deps (e2k_ms_loop *l, const HOST_WIDE_INT *step,
		 const int *ivdef)
{
  for (int a = 0; a < l->n; a++)
    for (int b = a + 1; b < l->n; b++)
      {
	e2k_ms_node *na = &l->nodes[a], *nb = &l->nodes[b];
	if (!na->mem || !nb->mem || (!na->store && !nb->store))
	  continue;
	/* A mova reads what the unit fetched ahead; e2k_ms_mark_apb made
	   sure no store of the loop writes that.  */
	if (na->apb || nb->apb)
	  continue;
	bool alias = e2k_ms_may_alias (na->mem, nb->mem);
	/* A store's data reaches a load in the next wide instruction late
	   (spec/isa/timing.md, "Store to load").  */
	int lab = na->store && !nb->store ? 2 : 1;
	int lba = nb->store && !na->store ? 2 : 1;
	e2k_ms_addr aa = e2k_ms_decompose (na->mem, step);
	e2k_ms_addr ab = e2k_ms_decompose (nb->mem, step);
	if (dump_file)
	  fprintf (dump_file, ";; e2k_modsched: mem %d %d: %s, inv %d/%d "
		   "iv %d/%d ok %d/%d\n", INSN_UID (na->insn),
		   INSN_UID (nb->insn), alias ? "may alias" : "independent",
		   (int) aa.inv, (int) ab.inv, (int) aa.iv, (int) ab.iv,
		   aa.ok, ab.ok);
	if (!alias)
	  continue;
	/* A's invariant part from B's (e2k_ms_inv_delta).  */
	HOST_WIDE_INT dinv = 0;
	if (aa.ok && ab.ok && aa.iv == ab.iv && aa.iv != INVALID_REGNUM
	    && aa.inv != ab.inv
	    && e2k_ms_inv_delta (aa.inv, ab.inv, l->bb, &dinv))
	  aa.inv = ab.inv;
	if (aa.ok && ab.ok && aa.inv == ab.inv && aa.iv == ab.iv
	    && aa.iv != INVALID_REGNUM)
	  {
	    /* Both step through one array: the access of B in iteration
	       I + D starts at (ob - oa) + D * C bytes from A's in I.  */
	    HOST_WIDE_INT c = step[aa.iv];
	    HOST_WIDE_INT oa = (aa.offset + dinv
				+ (ivdef[aa.iv] < a ? c : 0));
	    HOST_WIDE_INT ob = ab.offset + (ivdef[ab.iv] < b ? c : 0);
	    HOST_WIDE_INT sa = GET_MODE_SIZE (GET_MODE (na->mem));
	    HOST_WIDE_INT sb = GET_MODE_SIZE (GET_MODE (nb->mem));
	    for (int d = 0; d <= E2K_MS_MAX_II; d++)
	      {
		HOST_WIDE_INT diff = ob - oa + d * c;	/* B(I+D) - A(I) */
		if (diff > -sb && diff < sa)
		  e2k_ms_add_dep (l, a, b, lab, d);
		diff = oa - ob + d * c;			/* A(I+D) - B(I) */
		if (d > 0 && diff > -sa && diff < sb)
		  e2k_ms_add_dep (l, b, a, lba, d);
	      }
	  }
	else if (aa.ok && ab.ok && aa.inv == ab.inv && aa.iv == ab.iv)
	  {
	    /* The same invariant address every iteration.  */
	    e2k_ms_add_dep (l, a, b, lab, 0);
	    e2k_ms_add_dep (l, b, a, lba, 1);
	  }
	else if (na->store != nb->store
		 && e2k_ms_tbaa_raw_p (na->store ? na->mem : nb->mem,
				       na->store ? nb->mem : na->mem))
	  {
	    /* Only the load before a store after it.  */
	    int st = na->store ? a : b, ld = na->store ? b : a;
	    e2k_ms_add_dep (l, ld, st, 1, na->store ? 1 : 0);
	  }
	else if (na->store != nb->store && l->want_dam)
	  {
	    /* Left out for a lock load and its check (e2k_ms_add_dam);
	       the load stays before a store after it.  */
	    int st = na->store ? a : b, ld = na->store ? b : a;
	    e2k_ms_dep d = { st, ld, 2, na->store ? 0 : 1, 0 };
	    l->dam_deps.safe_push (d);
	    e2k_ms_add_dep (l, ld, st, 1, na->store ? 1 : 0);
	  }
	else
	  {
	    /* Only may alias: not likely the same doubleword.  */
	    e2k_ms_add_dep (l, a, b, 1, 0);
	    e2k_ms_add_dep (l, b, a, 1, 1);
	    l->may_dam |= na->store != nb->store;
	  }
      }
}

/* Whether MEM is aligned to BYTES by what its object or the computation
   of its address shows.  Not MEM_ALIGN, which takes a pointer's target
   type at its word: a cast such as *(uint32_t *) (buf + 1), common in
   decoders, belies it.  */
static bool
e2k_known_aligned_p (rtx mem, unsigned bytes)
{
  if (!MEM_EXPR (mem) || !MEM_OFFSET_KNOWN_P (mem))
    return false;
  HOST_WIDE_INT off;
  if (!MEM_OFFSET (mem).is_constant (&off))
    return false;
  unsigned int align, bits = bytes * BITS_PER_UNIT;
  unsigned HOST_WIDE_INT bitpos;
  get_object_alignment_2 (MEM_EXPR (mem), &align, &bitpos, true);
  return (align >= bits
	  && (bitpos + (unsigned HOST_WIDE_INT) off * BITS_PER_UNIT) % bits == 0);
}

/* Array prefetch (spec/isa/apb.md) for the loads of L, a loop counted
   by %lsr: those that read aligned elements through an address the
   loop steps forward by a whole number of them (an increment
   register), and whose elements no store of the loop writes before
   they are read (the buffer doesn't see stores): a store may write the
   element the load read in the same iteration, after it, or behind
   it.  Each becomes a mova (latency 5, an AAS channel, no ALU channel)
   in the kernel; the prologue keeps the load.  Loads through one
   address share a descriptor; e2k_ms_apb_assign gives them areas.  At
   most 16 (4 AAS channels a cycle) through 8 descriptors with 7
   increments.  STEP and IVDEF as for e2k_ms_mem_deps; DERIVED the
   stepped registers the loop computes from another.  */
static void
e2k_ms_mark_apb (e2k_ms_loop *l, const HOST_WIDE_INT *step,
		 const int *ivdef, const bool *derived)
{
  l->napb = 0;
  l->napb_d = 0;
  if (!l->apb_ok || l->want_dam)
    return;
  HOST_WIDE_INT incrs[8];
  int nincr = 0;
  for (int i = 0; i < l->n && l->napb < 32; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      if (!node->mem || node->store || node->value < 0 || node->lock
	  || node->chk >= 0 || MEM_VOLATILE_P (node->mem))
	continue;
      rtx pat = PATTERN (node->insn);
      if (GET_CODE (pat) != SET || !REG_P (SET_DEST (pat)))
	continue;
      rtx src = SET_SRC (pat);
      if (GET_CODE (src) == ZERO_EXTEND)
	src = XEXP (src, 0);
      machine_mode dm = GET_MODE (SET_DEST (pat));
      HOST_WIDE_INT size = GET_MODE_SIZE (GET_MODE (src));
      if (!MEM_P (src) || (size != 1 && size != 2 && size != 4 && size != 8)
	  || MEM_ALIGN (src) < size * BITS_PER_UNIT
	  || (dm != QImode && dm != HImode && dm != SImode && dm != DImode
	      && dm != SFmode && dm != DFmode && GET_MODE_SIZE (dm) != 8)
	  || (GET_CODE (SET_SRC (pat)) == ZERO_EXTEND && dm != DImode))
	continue;
      e2k_ms_addr a = e2k_ms_decompose (src, step);
      /* The setup reads the stepped register before the loop: one the
	 loop computes from another has no value there.  */
      if (!a.ok || a.iv == INVALID_REGNUM || derived[a.iv])
	continue;
      /* Backwards too (negative increments work, spec/isa/apb.md; lcc
	 reads PolyBench's durbin "r[k-i-1]" so), from v5 on: before, an
	 area's offset from its base is 32 bits, zero-extended, so it may
	 not go below the base, which lcc puts at the last element read
	 (its start in %aaind), and the PoC at the first (gcc.dg/vect's
	 vect-15-big-array, SIGILL on the 4C).  */
      HOST_WIDE_INT stp = step[a.iv];
      if (stp == 0 || stp % size != 0 || stp / size > 0x7fffffff
	  || stp / size < -0x7fffffff || (stp < 0 && e2k_arch < 5))
	continue;
      /* v3 and v4 give diagnostic values from an area not aligned to its
	 elements; v5 reads 2, 4 and 8 bytes anywhere (spec/isa/apb.md).  */
      if (size > 1 && e2k_arch < 5 && !e2k_known_aligned_p (src, size))
	continue;
      /* Steps other than one element take an increment register.  */
      int ki = 0;
      if (stp != size)
	{
	  while (ki < nincr && incrs[ki] != stp / size)
	    ki++;
	  if (ki == 7)
	    continue;
	}
      HOST_WIDE_INT oa = a.offset + (ivdef[a.iv] < i ? stp : 0);
      bool ok = true;
      for (int k = 0; k < l->n && ok; k++)
	{
	  e2k_ms_node *st = &l->nodes[k];
	  if (!st->store || !e2k_ms_may_alias (st->mem, src))
	    continue;
	  e2k_ms_addr b = e2k_ms_decompose (st->mem, step);
	  HOST_WIDE_INT sb = GET_MODE_SIZE (GET_MODE (st->mem));
	  /* The store's invariant part from the load's.  */
	  HOST_WIDE_INT dinv = 0;
	  if (b.ok && b.iv == a.iv && b.inv != a.inv
	      && e2k_ms_inv_delta (b.inv, a.inv, l->bb, &dinv))
	    b.inv = a.inv;
	  HOST_WIDE_INT ob = b.offset + dinv + (b.iv != INVALID_REGNUM
						&& ivdef[b.iv] < k ? stp : 0);
	  /* (Backwards, none may write the array.)  */
	  ok = b.ok && b.inv == a.inv && b.iv == a.iv && stp > 0;
	  /* The store of an iteration against the movas D iterations on:
	     none may read what it wrote, nor in its own iteration once it
	     comes first (an unrolled body's store at dy+16 and load at
	     dy+8 are fine).  */
	  for (HOST_WIDE_INT d = k < i ? 0 : 1; ok && oa + stp * d < ob + sb;
	       d++)
	    ok = d < 64 && oa + stp * d + size <= ob;
	}
      if (!ok)
	continue;
      int d = -1;
      for (int k = 0; k < i && d < 0; k++)
	if (l->nodes[k].apb && l->nodes[k].apb_iv == a.iv
	    && l->nodes[k].apb_inv == a.inv)
	  d = l->nodes[k].apb_d;
      if (d < 0 && l->napb_d == 32)
	continue;
      rtx mova = gen_e2k_mova (dm, SET_DEST (pat), const0_rtx, const0_rtx,
			       GEN_INT (size), const0_rtx, const1_rtx);
      rtx_insn *mi = make_insn_raw (mova);
      INSN_LOCATION (mi) = INSN_LOCATION (node->insn);
      if (recog_memoized (mi) < 0)
	continue;
      if (d < 0)
	d = l->napb_d++;
      if (stp != size && ki == nincr)
	incrs[nincr++] = stp / size;
      l->napb++;
      node->apb = true;
      node->orig = node->insn;
      node->insn = mi;
      node->apb_size = size;
      node->apb_d = d;
      node->apb_iv = a.iv;
      node->apb_inv = a.inv;
      node->apb_off = oa;
      node->apb_step = stp;
      /* Its value reaches any consumer 5 cycles on, in any cluster.  */
      for (e2k_ms_dep &d : l->deps)
	if (d.from == i)
	  {
	    d.lat = 5;
	    d.cross = 0;
	  }
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: insn %d through array "
		 "prefetch\n", INSN_UID (node->orig));
    }
}

/* AAU stores (spec/isa/apb.md, "AAU stores") for the stores of L, a
   loop counted by %lsr, as lcc's kernels store: through a descriptor
   whose base is where the store writes in iteration 0, and a store
   index of its own, 0 on the way in, that its incr steps.  No literal
   offsets, which lcc uses: gas can't place two AAU stores' literals in
   one wide instruction by itself ("literals cannot be packed"), only
   when written with their LTS (relcc2 findings I42).  The kernel runs the last stage of each iteration once
   and the stores are there, so the index needs no correction for the
   prologue.  The store then reads no address in the kernel, and what
   only computed the addresses of movas and such stores leaves it
   (e2k_ms_mark_kdead): PolyBench's jacobi-2d, five FP operations and a
   store, on v5 at II 1 as lcc's instead of 2.  A register's elements
   of their type's alignment, stepped forward by a whole number of them
   (unlike array prefetch, a misaligned AAU store just stores, also on
   the 4C: relcc2 findings I43, as lcc's v3 code assumes); at most 16
   (%aasti0-15), with the increment registers array prefetch leaves.  STEP, IVDEF and DERIVED
   as for e2k_ms_mark_apb.  */
static void
e2k_ms_mark_staa (e2k_ms_loop *l, const HOST_WIDE_INT *step,
		  const int *ivdef, const bool *derived)
{
  l->nstaa = 0;
  l->nstaa_d = 0;
  if (!l->staa_ok || l->want_dam)
    return;
  HOST_WIDE_INT incrs[7];
  int nincr = 0;
  /* Whether a step of E elements has an increment register, ADD it.  */
  auto incr_ok = [&] (HOST_WIDE_INT e, bool add)
    {
      if (e == 1)
	return true;
      for (int k = 0; k < nincr; k++)
	if (incrs[k] == e)
	  return true;
      if (nincr == 7)
	return false;
      if (add)
	incrs[nincr++] = e;
      return true;
    };
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].apb)
      incr_ok (l->nodes[i].apb_step / l->nodes[i].apb_size, true);
  for (int i = 0; i < l->n && l->nstaa < 16; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      if (!node->store || MEM_VOLATILE_P (node->mem))
	continue;
      rtx pat = PATTERN (node->insn);
      if (GET_CODE (pat) != SET || !REG_P (SET_SRC (pat)))
	continue;
      rtx mem = SET_DEST (pat), src = SET_SRC (pat);
      machine_mode m = GET_MODE (mem);
      HOST_WIDE_INT size = GET_MODE_SIZE (m);
      if ((size != 1 && size != 2 && size != 4 && size != 8)
	  || GET_MODE (src) != m || REG_NREGS (src) != 1
	  || MEM_ALIGN (mem) < size * BITS_PER_UNIT)
	continue;
      e2k_ms_addr a = e2k_ms_decompose (mem, step);
      if (!a.ok || a.iv == INVALID_REGNUM || derived[a.iv])
	continue;
      HOST_WIDE_INT stp = step[a.iv];
      if (stp <= 0 || stp % size != 0 || stp / size > 0x7fffffff
	  || !incr_ok (stp / size, false))
	continue;
      HOST_WIDE_INT oa = a.offset + (ivdef[a.iv] < i ? stp : 0);
      if (l->napb_d + l->nstaa_d == 32)
	continue;
      rtx_insn *si = make_insn_raw (gen_e2k_staa (m, src, const0_rtx,
						  const0_rtx, const0_rtx,
						  const0_rtx));
      INSN_LOCATION (si) = INSN_LOCATION (node->insn);
      if (recog_memoized (si) < 0)
	continue;
      incr_ok (stp / size, true);
      int d = l->napb_d + l->nstaa_d++;
      node->staa = true;
      node->orig = node->insn;
      node->insn = si;
      node->apb_size = size;
      node->apb_d = d;
      node->apb_iv = a.iv;
      node->apb_inv = a.inv;
      node->apb_off = oa;
      node->apb_step = stp;
      node->staa_sti = l->nstaa++;
      /* It reads its data only: the address's registers and their
	 dependences go.  */
      int nu = 0;
      for (int k = 0; k < node->nuses; k++)
	if (node->uses[k].pred
	    || refers_to_regno_p (node->uses[k].regno, PATTERN (si)))
	  node->uses[nu++] = node->uses[k];
      node->nuses = nu;
      unsigned w = 0;
      for (unsigned k = 0; k < l->deps.length (); k++)
	{
	  e2k_ms_dep dp = l->deps[k];
	  int v = l->nodes[dp.from].value;
	  if (dp.to != i || v < 0
	      || refers_to_regno_p (l->values[v].regno, PATTERN (si)))
	    l->deps[w++] = dp;
	}
      l->deps.truncate (w);
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: insn %d through the AAU\n",
		 INSN_UID (node->orig));
    }
}

/* What the kernel doesn't need to run (e2k_ms_node::kdead): nodes whose
   results only movas (for their loads in the prologue), AAU stores' addresses
   (read by no node: e2k_ms_mark_staa) and other such nodes read, and
   nothing after the loop.  An induction step that only addressed
   arrays: an ALU channel each cycle of an II 1 kernel.  */
static void
e2k_ms_mark_kdead (e2k_ms_loop *l)
{
  if (!l->napb && !l->nstaa)
    return;
  for (bool more = true; more; )
    {
      more = false;
      for (int i = 0; i < l->n; i++)
	{
	  e2k_ms_node *nd = &l->nodes[i];
	  if (nd->kdead || nd->value < 0 || nd->store || nd->pred || nd->dpred
	      || nd->apb || nd->lock || nd->chk >= 0
	      || l->values[nd->value].out_dist >= 0)
	    continue;
	  bool used = false;
	  for (int j = 0; j < l->n && !used; j++)
	    if (j != i && !l->nodes[j].kdead && !l->nodes[j].apb)
	      for (int k = 0; k < l->nodes[j].nuses; k++)
		if (!l->nodes[j].uses[k].pred
		    && l->nodes[j].uses[k].value == nd->value)
		  used = true;
	  if (used)
	    continue;
	  nd->kdead = true;
	  more = true;
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: insn %d only in the "
		     "prologue\n", INSN_UID (nd->insn));
	}
    }
}

static bool
e2k_ms_why (const char *why)
{
  if (dump_file)
    fprintf (dump_file, ";; e2k_modsched: %s\n", why);
  return false;
}

/* A copy between registers costs nothing in the ring, where its value
   would only get another name: fold each copy into its source, of this
   iteration or the last (DS 0 or 1): what read the copy D iterations
   later reads the source D + DS iterations later (at most 2).  The
   instances from before the loop that reads then reach move too: the
   copy's instance -K is the source's -(K + DS), held by the register
   the copy's was in; not if the source's is another one.  Then drop the
   copies from L's nodes, and mark the registers they set in FOLDED.  */
static void
e2k_ms_fold_copies (e2k_ms_loop *l, bool *folded)
{
  bool any = false;
  for (int i = 0; i < l->n; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      rtx pat = PATTERN (node->insn);
      int vc = node->value;
      if (vc < 0 || node->nuses != 1 || !REG_P (SET_SRC (pat))
	  || GET_MODE (SET_SRC (pat)) != GET_MODE (SET_DEST (pat)))
	continue;
      int vs = node->uses[0].value, ds = node->uses[0].dist;
      if (vs < 0 || node->uses[0].pred || ds > 1 || vs == vc)
	continue;
      e2k_ms_value &src = l->values[vs], &cp = l->values[vc];
      if (ds == 1 && cp.carried2)
	continue;
      bool ok = true;
      for (int j = 0; j < l->n && ok; j++)
	for (int k = 0; k < l->nodes[j].nuses; k++)
	  if (!l->nodes[j].uses[k].pred && l->nodes[j].uses[k].value == vc
	      && l->nodes[j].uses[k].dist + ds > 2)
	    ok = false;
      for (e2k_ms_out &o : l->outs)
	if (o.value == vc && o.dist + ds > 2)
	  ok = false;
      /* The copy's instances -1 and -2 become the source's -1 - DS and
	 -2 - DS.  */
      for (int k = 0; k < 2 && ok; k++)
	if (k == 0 ? cp.carried : cp.carried2)
	  {
	    int t = k + ds;
	    bool need = t == 0 ? src.carried : src.carried2;
	    if (t > 1 || (need && src.init[t] != cp.init[k]))
	      ok = false;
	  }
      /* The source's instance -1 is the register it is in, which the
	 copy read in the first iteration.  */
      if (ds == 1 && src.init[0] != src.regno)
	ok = false;
      if (!ok)
	continue;
      for (int j = 0; j < l->n; j++)
	for (int k = 0; k < l->nodes[j].nuses; k++)
	  if (!l->nodes[j].uses[k].pred && l->nodes[j].uses[k].value == vc)
	    {
	      l->nodes[j].uses[k].value = vs;
	      l->nodes[j].uses[k].dist += ds;
	    }
      for (e2k_ms_out &o : l->outs)
	if (o.value == vc)
	  {
	    o.value = vs;
	    o.dist += ds;
	  }
      for (int k = 0; k < 2; k++)
	if (k == 0 ? cp.carried : cp.carried2)
	  {
	    if (k + ds == 0)
	      src.carried = true;
	    else
	      src.carried2 = true;
	    src.init[k + ds] = cp.init[k];
	  }
      if (cp.out_dist >= 0)
	src.out_dist = MAX (src.out_dist, cp.out_dist + ds);
      node->dead = true;
      folded[REGNO (SET_DEST (pat))] = true;
      any = true;
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: copy insn %d folded\n",
		 INSN_UID (node->insn));
    }
  if (!any)
    return;
  /* What reads the source a later iteration now.  */
  for (int i = 0; i < l->n; i++)
    if (!l->nodes[i].dead)
      for (int k = 0; k < l->nodes[i].nuses; k++)
	{
	  e2k_ms_use *u = &l->nodes[i].uses[k];
	  if (u->pred || u->value < 0)
	    continue;
	  if (u->dist == 1)
	    l->values[u->value].carried = true;
	  else if (u->dist == 2)
	    l->values[u->value].carried2 = true;
	}
  for (e2k_ms_out &o : l->outs)
    if (o.dist == 1)
      l->values[o.value].carried = true;
    else if (o.dist == 2)
      l->values[o.value].carried2 = true;

  /* Renumber the nodes and values left.  */
  int nmap[E2K_MS_MAX_NODES], n = 0;
  for (int i = 0; i < l->n; i++)
    nmap[i] = l->nodes[i].dead ? -1 : n++;
  int nv = l->values.length ();
  auto_vec<int> vmap (nv);
  auto_vec<e2k_ms_value> values (nv);
  for (int v = 0; v < nv; v++)
    if (l->nodes[l->values[v].node].dead)
      vmap.quick_push (-1);
    else
      {
	vmap.quick_push (values.length ());
	e2k_ms_value val = l->values[v];
	val.node = nmap[val.node];
	values.quick_push (val);
      }
  int nh = 0;
  for (int i = 0; i < l->n; i++)
    {
      if (nmap[i] < 0)
	continue;
      if (i < l->nh)
	nh++;
      e2k_ms_node node = l->nodes[i];
      if (node.value >= 0)
	node.value = vmap[node.value];
      for (int k = 0; k < node.nuses; k++)
	if (node.uses[k].pred)
	  node.uses[k].value = nmap[node.uses[k].value];
	else if (node.uses[k].value >= 0)
	  node.uses[k].value = vmap[node.uses[k].value];
      l->nodes[nmap[i]] = node;
    }
  for (e2k_ms_out &o : l->outs)
    o.value = vmap[o.value];
  if (l->stay >= 0)
    l->stay = nmap[l->stay];
  if (l->c1 >= 0)
    l->c1 = nmap[l->c1];
  for (int &c : l->c1s)
    c = nmap[c];
  l->nh = nh;
  l->n = n;
  l->values.truncate (0);
  for (e2k_ms_value &val : values)
    l->values.safe_push (val);
}

/* The condition of a loop end "if (P op 0) goto L", possibly with a
   (use CTPR): the (op P 0) rtx in the pattern, or NULL.  */
static rtx
e2k_ms_jump_cond (rtx_insn *jump)
{
  rtx pat = PATTERN (jump);
  if (GET_CODE (pat) == PARALLEL)
    pat = XVECEXP (pat, 0, 0);
  if (GET_CODE (pat) != SET || SET_DEST (pat) != pc_rtx
      || GET_CODE (SET_SRC (pat)) != IF_THEN_ELSE
      || GET_CODE (XEXP (SET_SRC (pat), 1)) != LABEL_REF
      || XEXP (SET_SRC (pat), 2) != pc_rtx)
    return NULL_RTX;
  rtx cond = XEXP (SET_SRC (pat), 0);
  if ((GET_CODE (cond) != NE && GET_CODE (cond) != EQ)
      || !REG_P (XEXP (cond, 0)) || !PRED_REGNO_P (REGNO (XEXP (cond, 0)))
      || XEXP (cond, 1) != const0_rtx)
    return NULL_RTX;
  return cond;
}

/* The instances that use what node FROM of one iteration computes, in
   DEP: bit D of DEP[N] when node N of D iterations later does (D < 32),
   through values and predicates.  */
static void
e2k_ms_dependents (e2k_ms_loop *l, int from, unsigned *dep)
{
  for (int i = 0; i < l->n; i++)
    dep[i] = 0;
  dep[from] = 1;
  for (bool changed = true; changed; )
    {
      changed = false;
      for (int i = 0; i < l->n; i++)
	for (int k = 0; k < l->nodes[i].nuses; k++)
	  {
	    const e2k_ms_use &u = l->nodes[i].uses[k];
	    int m = u.pred ? u.value : u.value >= 0 ? l->values[u.value].node : -1;
	    if (m < 0)
	      continue;
	    unsigned add = (dep[m] << u.dist) & ~dep[i];
	    if (add)
	      {
		dep[i] |= add;
		changed = true;
	      }
	  }
    }
}

/* Make the load L->dam_deps name a lock load that may move above the
   stores they name, with a check load of its own (spec/isa/
   speculation.md: the check reloads into the same register, and its
   rbranch is taken, if a store touched the bytes since).  */
static bool
e2k_ms_add_dam (e2k_ms_loop *l)
{
  if (l->dam_deps.is_empty ())
    return e2k_ms_why ("no load to speculate");
  /* The compensation code reruns what depends on the load, not the
     compares of the predicates it reads, which the ring may have given
     to another compare by then (GMP's in-place mpn_bdiv_dbm1c).  */
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].dpred)
      return e2k_ms_why ("predicates and a lock load");
  int ld = l->dam_deps[0].to;
  for (e2k_ms_dep &d : l->dam_deps)
    if (d.to != ld)
      return e2k_ms_why ("more than one load to speculate");
  if (e2k_ov_mem_p (l->nodes[ld].mem))
    return e2k_ms_why ("a load of a copy for overlapping arrays");
  /* Its check would reload unconditionally, from an address valid only
     under the predicate e2k_unpredicate_loads took away.  */
  if (e2k_unpred_cond_of (l->nodes[ld].insn))
    return e2k_ms_why ("a load run without its predicate");
  e2k_ms_node *ln = &l->nodes[ld];
  rtx dest, src;
  if (l->n == E2K_MS_MAX_NODES || ln->value < 0
      || ln->nuses == E2K_MS_MAX_USES
      || !e2k_spec_load_parts (ln->insn, &dest, &src))
    return e2k_ms_why ("a load without a lock form");
  rtx lpat = gen_rtx_PARALLEL (VOIDmode,
			       gen_rtvec (2, copy_rtx (PATTERN (ln->insn)),
					  gen_rtx_UNSPEC (VOIDmode,
							  gen_rtvec (1, const0_rtx),
							  UNSPEC_LDLOCK)));
  rtx_insn *lk = make_insn_raw (lpat);
  INSN_LOCATION (lk) = INSN_LOCATION (ln->insn);
  machine_mode mode = GET_MODE (dest);
  rtx test = gen_rtx_NE (VOIDmode,
			 gen_rtx_UNSPEC (VOIDmode, gen_rtvec (1, dest),
					 UNSPEC_LDCHK),
			 const0_rtx);
  rtx_insn *ck
    = make_insn_raw (gen_rtx_SET (dest,
				  gen_rtx_IF_THEN_ELSE (mode, test,
							copy_rtx (src), dest)));
  INSN_LOCATION (ck) = INSN_LOCATION (ln->insn);
  if (recog_memoized (lk) < 0 || recog_memoized (ck) < 0)
    return e2k_ms_why ("a load without a lock form");
  ln->insn = lk;
  ln->lock = true;
  int k = l->n++;
  e2k_ms_node *kn = &l->nodes[k];
  memset (kn, 0, sizeof *kn);
  kn->insn = ck;
  kn->value = -1;
  kn->chk = ld;
  kn->mem = ln->mem;
  /* The load's address operands, then its value (last, so that an
     address register of the same number gets the address's name).  */
  kn->nuses = ln->nuses;
  memcpy (kn->uses, ln->uses, sizeof ln->uses);
  e2k_ms_use u = { REGNO (dest), ln->value, 0, false };
  kn->uses[kn->nuses++] = u;
  l->dam = ld;
  l->kchk = k;
  e2k_ms_add_dep (l, ld, k, 3, 0);
  /* A check sees a store of the cycle before (lock, store and check a
     cycle apart: spec/isa/speculation.md, "Distances").  */
  for (e2k_ms_dep &d : l->dam_deps)
    e2k_ms_add_dep (l, d.from, k, 1, d.dist);
  /* The check reads the memory again, so it too goes before the stores
     the load goes before, and before the stores of what the load
     gave.  */
  unsigned nd = l->deps.length ();
  for (unsigned q = 0; q < nd; q++)
    {
      e2k_ms_dep d = l->deps[q];
      if (d.from == ld && l->nodes[d.to].store)
	e2k_ms_add_dep (l, k, d.to, 1, d.dist);
    }
  unsigned dep[E2K_MS_MAX_NODES];
  e2k_ms_dependents (l, ld, dep);
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].store)
      for (int d = 0; d < 32; d++)
	if (dep[i] & (1u << d))
	  e2k_ms_add_dep (l, k, i, 1, d);
  if (dump_file)
    fprintf (dump_file, ";; e2k_modsched: insn %d a lock load\n",
	     INSN_UID (ln->insn));
  return true;
}

static rtx e2k_ms_set (rtx);

/* Whether INSN is an FP operation, which may raise an FP exception.  */
static bool
e2k_fp_class_p (rtx_insn *insn)
{
  if (recog_memoized (insn) < 0)
    return false;
  switch (get_attr_type (insn))
    {
    case TYPE_FP: case TYPE_FMA: case TYPE_FFMA: case TYPE_FCVT:
    case TYPE_FDIV: case TYPE_FCMP:
      return true;
    default:
      return false;
    }
}

/* Find the nodes, values and dependences of the loop whose body is
   L->insns; EXIT is where it goes when done.  */
static bool
e2k_ms_analyze (e2k_ms_loop *l, basic_block exit)
{
  basic_block bb = l->bb;
  l->n = 0;
  l->exit = exit;
  l->npred = 0;
  /* A register set under a predicate, "if (p) r = x", keeps r when p
     is false, which a renamed instance can't: it becomes "t = x" and
     the merge "r = p ? t : r", t a register the loop doesn't use and
     that is dead around it (it only names the value, which gets a ring
     name).  */
  auto_vec<rtx_insn *> body;
  l->nh = l->nh0;
  {
    HARD_REG_SET used;
    CLEAR_HARD_REG_SET (used);
    for (rtx_insn *insn : l->insns)
      e2k_note_regs (PATTERN (insn), &used);
    e2k_note_regs (PATTERN (l->jump), &used);
    bitmap lh = df_get_live_in (bb), lx = df_get_live_in (exit);
    bitmap l1 = l->x1 ? df_get_live_in (l->x1) : lx;
    unsigned next_t = 0;
    for (unsigned k = 0; k < l->insns.length (); k++)
      {
	rtx_insn *insn = l->insns[k];
	rtx pat = PATTERN (insn);
	if (GET_CODE (pat) != COND_EXEC
	    || GET_CODE (COND_EXEC_CODE (pat)) != SET
	    || !REG_P (SET_DEST (COND_EXEC_CODE (pat))))
	  {
	    body.safe_push (insn);
	    continue;
	  }
	rtx set = COND_EXEC_CODE (pat), r = SET_DEST (set);
	machine_mode m = GET_MODE (r);
	unsigned t = INVALID_REGNUM;
	for (; next_t < FIRST_PSEUDO_REGISTER && t == INVALID_REGNUM; next_t++)
	  if (GPR_REGNO_P (next_t) && !BX_REGNO_P (next_t) && !B_REGNO_P (next_t)
	      && !fixed_regs[next_t] && !TEST_HARD_REG_BIT (used, next_t)
	      && !bitmap_bit_p (lh, next_t) && !bitmap_bit_p (lx, next_t)
	      && !bitmap_bit_p (l1, next_t)
	      && targetm.hard_regno_mode_ok (next_t, m))
	    t = next_t;
	if (t == INVALID_REGNUM || !REG_P (r) || REG_NREGS (r) != 1
	    || (m != SImode && m != DImode && m != SFmode && m != DFmode))
	  {
	    body.safe_push (insn);
	    continue;
	  }
	rtx tr = gen_rtx_REG (m, t);
	rtx_insn *a = make_insn_raw (gen_rtx_SET (tr, copy_rtx (SET_SRC (set))));
	rtx test = copy_rtx (COND_EXEC_TEST (pat));
	rtx_insn *b = make_insn_raw (gen_rtx_SET (r, gen_rtx_IF_THEN_ELSE
						 (m, test, tr, r)));
	INSN_LOCATION (a) = INSN_LOCATION (b) = INSN_LOCATION (insn);
	if (recog_memoized (a) < 0 || recog_memoized (b) < 0)
	  {
	    body.safe_push (insn);
	    continue;
	  }
	body.safe_push (a);
	body.safe_push (b);
	if ((int) k < l->nh0)
	  l->nh++;
      }
  }
  for (rtx_insn *insn : body)
    {
      /* A pipelined loop runs every operation but the stores for
	 iterations past the end too, speculatively; an FP one would then
	 give a diagnostic value where the flags are clear
	 (spec/isa/speculation.md, "What lcc speculates").  */
      if (!e2k_spec_fp && e2k_fp_class_p (insn))
	return e2k_ms_why ("an FP operation would run speculatively "
			   "(-mno-spec-fp)");
      if (l->n == E2K_MS_MAX_NODES)
	{
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: more than %d operations\n",
		     E2K_MS_MAX_NODES);
	  return false;
	}
      if (!e2k_ms_insn_ok (insn, l->wl))
	{
	  if (dump_file)
	    {
	      fprintf (dump_file, ";; e2k_modsched: can't pipeline\n");
	      print_rtl_single (dump_file, insn);
	    }
	  return false;
	}
      e2k_ms_node *node = &l->nodes[l->n++];
      memset (node, 0, sizeof *node);
      node->insn = insn;
      node->value = -1;
      node->chk = -1;
      rtx pat = e2k_ms_set (PATTERN (insn));
      rtx dest = SET_DEST (pat);
      if (GET_CODE (PATTERN (insn)) == COND_EXEC
	  && !e2k_ms_note_uses (node, COND_EXEC_TEST (PATTERN (insn))))
	return e2k_ms_why ("too many registers");
      if (MEM_P (dest))
	{
	  node->store = true;
	  node->mem = dest;
	  if (!e2k_ms_note_uses (node, XEXP (dest, 0)))
	    return e2k_ms_why ("too many registers");
	}
      else
	node->pred = PRED_REGNO_P (REGNO (dest));
      if (!e2k_ms_note_uses (node, SET_SRC (pat)))
	return e2k_ms_why ("too many registers");
      subrtx_iterator::array_type array;
      FOR_EACH_SUBRTX (iter, array, SET_SRC (pat), NONCONST)
	if (MEM_P (*iter))
	  node->mem = const_cast<rtx> (*iter);
    }
  if (l->n < 2)
    return e2k_ms_why ("fewer than 2 insns");

  /* Values: one per definition of a register (predicates are not
     values: they stay in their registers).  CUR[r] is the value of r so
     far in this iteration, LAST[r] the body's last, LASTH[r] the last of
     a two-block loop's first block.  */
  int cur[FIRST_PSEUDO_REGISTER], last[FIRST_PSEUDO_REGISTER];
  int lasth[FIRST_PSEUDO_REGISTER], pcur[FIRST_PSEUDO_REGISTER];
  for (int r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    cur[r] = last[r] = lasth[r] = pcur[r] = -1;
  bitmap live_head = df_get_live_in (bb);
  bitmap live_exit = df_get_live_in (exit);
  bitmap live_x1 = l->x1 ? df_get_live_in (l->x1) : live_exit;
  for (int i = 0; i < l->n; i++)
    {
      rtx dest = SET_DEST (e2k_ms_set (PATTERN (l->nodes[i].insn)));
      if (!REG_P (dest))
	continue;
      unsigned r = REGNO (dest);
      if (l->nodes[i].pred)
	{
	  /* Set once, and not needed before or after the loop.  */
	  for (int j = 0; j < i; j++)
	    if (l->nodes[j].pred
		&& REGNO (SET_DEST (e2k_ms_set (PATTERN (l->nodes[j].insn))))
		   == r)
	      return e2k_ms_why ("a predicate set twice");
	  if (bitmap_bit_p (live_head, r) || bitmap_bit_p (live_exit, r)
	      || bitmap_bit_p (live_x1, r))
	    return e2k_ms_why ("a predicate live around the loop");
	  continue;
	}
      e2k_ms_value v;
      memset (&v, 0, sizeof v);
      v.node = i;
      v.regno = r;
      v.init[0] = r;
      v.init[1] = INVALID_REGNUM;
      v.mode = GET_MODE (dest);
      v.out_dist = -1;
      l->nodes[i].value = l->values.length ();
      last[r] = l->values.length ();
      if (i < l->nh)
	lasth[r] = l->values.length ();
      l->values.safe_push (v);
    }
  /* setbn renames %b[0..7] for the loop, but the ring lies below the
     registers they name outside it: a value there may pass through the
     loop, but the loop can't read one in or leave one behind.  */
  for (unsigned r = B0_REGNUM; r < B0_REGNUM + 8; r++)
    if (last[r] >= 0
	&& (bitmap_bit_p (live_head, r) || bitmap_bit_p (live_exit, r)
	    || bitmap_bit_p (live_x1, r)))
      {
	if (dump_file)
	  fprintf (dump_file, ";; e2k_modsched: %s live%s%s%s\n",
		   reg_names[r], bitmap_bit_p (live_head, r) ? " in" : "",
		   bitmap_bit_p (live_exit, r) ? " out" : "",
		   bitmap_bit_p (live_x1, r) ? " out of the first block" : "");
	return e2k_ms_why ("%b[0..7] live into or after the loop");
      }
  for (int i = 0; i < l->n; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      for (int k = 0; k < node->nuses; k++)
	{
	  e2k_ms_use *u = &node->uses[k];
	  if (PRED_REGNO_P (u->regno))
	    {
	      /* The exit test, merges and predicated stores read
		 predicates, set before them in the same iteration.  */
	      if (pcur[u->regno] < 0)
		{
		  if (dump_file)
		    print_rtl_single (dump_file, node->insn);
		  return e2k_ms_why ("a predicate from outside the iteration");
		}
	      u->pred = true;
	      u->value = pcur[u->regno];
	      continue;
	    }
	  if (cur[u->regno] >= 0)
	    u->value = cur[u->regno];
	  else if (last[u->regno] >= 0)
	    {
	      u->value = last[u->regno];
	      u->dist = 1;
	      l->values[u->value].carried = true;
	    }
	  /* setbn renames %b[0..7] for the loop: they can only hold
	     values local to an iteration (no copies in or out either:
	     live_head and live_exit above), or an invariant the kernel
	     reads from a register of its own (L->binv).  */
	  if (B_REGNO_P (u->regno) && u->value < 0
	      && !(l->binv & (1u << (u->regno - B0_REGNUM))))
	    return e2k_ms_why ("%b[0..7] invariant in the loop");
	}
      if (node->value >= 0)
	cur[l->values[node->value].regno] = node->value;
      if (node->pred)
	pcur[REGNO (SET_DEST (e2k_ms_set (PATTERN (node->insn))))] = i;
    }

  /* Compares that merges and predicated stores read are data: scheduled
     as any operation, their predicates named in the ring
     (e2k_ms_assign_pnames).  The exit test reads only its own.  */
  for (int i = 0; i < l->n; i++)
    {
      enum attr_type t = get_attr_type (l->nodes[i].insn);
      if (t == TYPE_CMP || t == TYPE_FCMP || t == TYPE_PLOG)
	continue;
      for (int k = 0; k < l->nodes[i].nuses; k++)
	if (l->nodes[i].uses[k].pred)
	  {
	    int c = l->nodes[i].uses[k].value;
	    enum attr_type tc = get_attr_type (l->nodes[c].insn);
	    if (tc != TYPE_CMP && tc != TYPE_FCMP)
	      return e2k_ms_why ("a merge or store on a landp");
	    l->nodes[c].dpred = true;
	  }
    }
  for (int i = 0; i < l->n; i++)
    {
      for (int k = 0; k < l->nodes[i].nuses; k++)
	if (l->nodes[i].uses[k].pred
	    && l->nodes[l->nodes[i].uses[k].value].dpred
	    && get_attr_type (l->nodes[i].insn) == TYPE_PLOG)
	  return e2k_ms_why ("a predicate both data and exit test");
      if (l->nodes[i].dpred)
	l->nodes[i].pred = false;
      else if (l->nodes[i].pred && !l->wl)
	return e2k_ms_why ("a predicate nothing reads");
    }

  /* A while loop's exit test.  */
  if (l->wl)
    {
      rtx pstay = l->pstay ? l->pstay : XEXP (e2k_ms_jump_cond (l->jump), 0);
      l->stay = pcur[REGNO (pstay)];
      if (l->stay < 0)
	return e2k_ms_why ("the loop end's predicate is not set in the loop");
      if (l->p1)
	{
	  l->c1 = pcur[REGNO (l->p1)];
	  l->c1s.truncate (0);
	  if (l->c1 < 0 || l->c1 >= l->nh)
	    return e2k_ms_why ("the first block's exit test");
	  /* The compares and the landps over them, in the first block.  */
	  bool in[E2K_MS_MAX_NODES] = { false };
	  auto_vec<int, 8> work;
	  work.safe_push (l->c1);
	  while (!work.is_empty ())
	    {
	      int i = work.pop ();
	      if (in[i])
		continue;
	      in[i] = true;
	      enum attr_type t = get_attr_type (l->nodes[i].insn);
	      if (i >= l->nh
		  || (t != TYPE_CMP && t != TYPE_FCMP && t != TYPE_PLOG))
		return e2k_ms_why ("the first block's exit test");
	      for (int k = 0; k < l->nodes[i].nuses; k++)
		if (l->nodes[i].uses[k].pred)
		  {
		    if (t != TYPE_PLOG)
		      return e2k_ms_why ("the first block's exit test");
		    work.safe_push (l->nodes[i].uses[k].value);
		  }
	    }
	  for (int i = 0; i < l->nh; i++)
	    if (in[i])
	      {
		if (l->nodes[i].dpred)
		  return e2k_ms_why ("a predicate both data and exit test");
		l->c1s.safe_push (i);
	      }
	}
      for (int i = 0; i < l->n; i++)
	for (int k = 0; k < l->nodes[i].nuses; k++)
	  if (l->nodes[i].uses[k].pred && l->nodes[i].uses[k].value == l->stay)
	    return e2k_ms_why ("the loop end's predicate read in the loop");
    }

  /* Registers read after the loop.  */
  auto add_out = [&] (unsigned r, int v, int dist, bool hend)
    {
      e2k_ms_out o = { r, l->values[v].mode, v, dist, hend };
      l->outs.safe_push (o);
      l->values[v].out_dist = MAX (l->values[v].out_dist, dist);
      if (dist > 0)
	l->values[v].carried = true;
    };
  for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    if (last[r] >= 0)
      {
	bool at2 = (bitmap_bit_p (live_exit, r)
		    || TEST_HARD_REG_BIT (e2k_ms_live_out_extra, r));
	/* With one exit, a register e2k_ms_move_b gave a %b[] value is
	   live there too (its copy back is still on the edge).  */
	bool at1 = (l->c1 >= 0
		    && (bitmap_bit_p (live_x1, r)
			|| (!l->x1
			    && TEST_HARD_REG_BIT (e2k_ms_live_out_extra, r))));
	if (at2)
	  add_out (r, last[r], 0, false);
	/* Left by the first block's exit, the register holds its value
	   at the end of that block: set there, or else from the last
	   iteration.  */
	if (at1 && (l->x1 || lasth[r] != last[r]))
	  add_out (r, lasth[r] >= 0 ? lasth[r] : last[r],
		   lasth[r] >= 0 ? 0 : 1, true);
      }
  /* That exit's test runs again after the loop.  */
  for (int c : l->c1s)
    for (int k = 0; k < l->nodes[c].nuses; k++)
      {
	e2k_ms_use *u = &l->nodes[c].uses[k];
	if (u->value >= 0 && !u->pred)
	  l->values[u->value].out_dist
	    = MAX (l->values[u->value].out_dist, u->dist);
      }

  /* How many times each register is set (before folding).  */
  int ndefs[FIRST_PSEUDO_REGISTER];
  bool folded[FIRST_PSEUDO_REGISTER];
  for (int r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    {
      ndefs[r] = 0;
      folded[r] = false;
    }
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].value >= 0)
      ndefs[l->values[l->nodes[i].value].regno]++;
  e2k_ms_fold_copies (l, folded);

  /* Register dependences.  */
  for (int i = 0; i < l->n; i++)
    for (int k = 0; k < l->nodes[i].nuses; k++)
      {
	e2k_ms_use *u = &l->nodes[i].uses[k];
	if (u->pred)
	  {
	    /* Compare -> landp 1 (spec/isa/timing.md); to a merge or a
	       predicated store as the scheduler has it.  */
	    rtx_insn *def = l->nodes[u->value].insn;
	    e2k_ms_add_dep (l, u->value, i,
			    get_attr_type (l->nodes[i].insn) == TYPE_PLOG
			    ? 1 : MAX (insn_latency (def, l->nodes[i].insn), 1),
			    0);
	    continue;
	  }
	if (u->value < 0)
	  continue;
	rtx_insn *def = l->nodes[l->values[u->value].node].insn;
	/* gas picks the channels, so a value may cross between ALC0-2 and
	   ALC3-5, which costs 1 cycle more (2 for an FP result;
	   spec/isa/timing.md).  In the kernel a late operand stalls every
	   iteration, while slack only adds stages.  */
	enum attr_type dt = get_attr_type (def);
	int cross = (dt == TYPE_FP || dt == TYPE_FMA || dt == TYPE_FFMA
		     || dt == TYPE_FCVT || dt == TYPE_FDIV
		     || dt == TYPE_MUL ? 2 : 1);
	/* A v6 load reaches either cluster at its 5.  */
	if (E2K_LAT6
	    && (dt == TYPE_LOAD || dt == TYPE_LDLOCK || dt == TYPE_LDCHK))
	  cross = 0;
	int lat = MAX (insn_latency (def, l->nodes[i].insn), 1);
	/* A packed result costs 4 in the other cluster, as it does to an
	   integer operation (which the bypass gives).  */
	if (e2k_packed_type_p (dt))
	  cross = MAX (4 - lat, 0);
	/* An operation that uses its own last result stays in its
	   channel.  */
	if (def == l->nodes[i].insn)
	  cross = 0;
	e2k_ms_add_dep (l, l->values[u->value].node, i, lat + cross,
			u->dist, cross);
      }

  /* Induction registers: defined once, as r = r + C, and carried.  A
     register a folded copy set varies.  */
  HOST_WIDE_INT step[FIRST_PSEUDO_REGISTER];
  int ivdef[FIRST_PSEUDO_REGISTER];
  for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    {
      step[r] = folded[r] ? HOST_WIDE_INT_MIN : 0;
      ivdef[r] = -1;
    }
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].value >= 0)
      {
	unsigned r = l->values[l->nodes[i].value].regno;
	rtx src = SET_SRC (PATTERN (l->nodes[i].insn));
	/* r = r + C in 32 bits, extended (an unsigned counter under dbl):
	   as for the registers derived below, a wrap is no nearer.  */
	if ((GET_CODE (src) == ZERO_EXTEND || GET_CODE (src) == SIGN_EXTEND)
	    && GET_CODE (XEXP (src, 0)) == PLUS)
	  src = XEXP (src, 0);
	if (step[r] == 0 && ivdef[r] < 0 && ndefs[r] == 1
	    && GET_CODE (src) == PLUS && REG_P (XEXP (src, 0))
	    && REGNO (XEXP (src, 0)) == r && CONST_INT_P (XEXP (src, 1))
	    && INTVAL (XEXP (src, 1)) != 0)
	  {
	    step[r] = INTVAL (XEXP (src, 1));
	    ivdef[r] = i;
	  }
	else
	  step[r] = HOST_WIDE_INT_MIN;
      }
  bool derived[FIRST_PSEUDO_REGISTER] = { false };
  /* Registers computed once from an induction register X: X + INV, the
     same in 32 bits zero-extended (dbl, or a zero extension of it), X * C
     and X << C step by a constant too.  A 32-bit sum that wraps puts the
     address about 2^32 elements away, never as near as another
     iteration's of the few in flight: for the dependences between
     iterations, the step holds (xz's opts[cur + len] in its trailing
     array, which ivopts can't make an induction variable).  */
  for (bool more = true; more; )
    {
      more = false;
      for (int i = 0; i < l->n; i++)
	{
	  if (l->nodes[i].value < 0)
	    continue;
	  unsigned r = l->values[l->nodes[i].value].regno;
	  if (step[r] != HOST_WIDE_INT_MIN || ndefs[r] != 1 || folded[r]
	      || ivdef[r] >= 0)
	    continue;
	  rtx src = SET_SRC (PATTERN (l->nodes[i].insn));
	  bool wide = GET_MODE (SET_DEST (PATTERN (l->nodes[i].insn))) == DImode;
	  if (GET_CODE (src) == ZERO_EXTEND || GET_CODE (src) == SIGN_EXTEND)
	    src = XEXP (src, 0);
	  else if (!wide && !e2k_dbl_p ())
	    continue;
	  rtx x = NULL_RTX;
	  HOST_WIDE_INT mul = 1;
	  if (GET_CODE (src) == PLUS && REG_P (XEXP (src, 0))
	      && (CONST_INT_P (XEXP (src, 1))
		  || (REG_P (XEXP (src, 1)) && step[REGNO (XEXP (src, 1))] == 0)))
	    x = XEXP (src, 0);
	  else if (GET_CODE (src) == PLUS && REG_P (XEXP (src, 1))
		   && REG_P (XEXP (src, 0)) && step[REGNO (XEXP (src, 0))] == 0)
	    x = XEXP (src, 1);
	  else if (GET_CODE (src) == MULT && REG_P (XEXP (src, 0))
		   && CONST_INT_P (XEXP (src, 1))
		   && IN_RANGE (INTVAL (XEXP (src, 1)), -4096, 4096))
	    x = XEXP (src, 0), mul = INTVAL (XEXP (src, 1));
	  else if (GET_CODE (src) == ASHIFT && REG_P (XEXP (src, 0))
		   && CONST_INT_P (XEXP (src, 1))
		   && IN_RANGE (INTVAL (XEXP (src, 1)), 0, 12))
	    x = XEXP (src, 0), mul = HOST_WIDE_INT_1 << INTVAL (XEXP (src, 1));
	  else if (REG_P (src))
	    x = src;
	  if (!x || REGNO (x) == r)
	    continue;
	  /* Every use after the def: an earlier one would read the last
	     iteration's, in iteration 0 whatever came in.  */
	  bool before = false;
	  for (int k = 0; k <= i && !before; k++)
	    for (int u = 0; u < l->nodes[k].nuses; u++)
	      if (l->nodes[k].uses[u].regno == r && !l->nodes[k].uses[u].pred)
		before = true;
	  if (before)
	    continue;
	  HOST_WIDE_INT sx = step[REGNO (x)];
	  if (sx == 0 || sx == HOST_WIDE_INT_MIN || mul == 0
	      || !IN_RANGE (sx, -65536, 65536))
	    continue;
	  step[r] = sx * mul;
	  ivdef[r] = i;
	  derived[r] = true;
	  more = true;
	}
    }
  CLEAR_HARD_REG_SET (l->fix_free);
  for (unsigned r = 16; r < R0_REGNUM + 64; r++)
    if (!fixed_regs[r] && !bitmap_bit_p (live_head, r)
	&& !bitmap_bit_p (live_exit, r) && !bitmap_bit_p (live_x1, r))
      SET_HARD_REG_BIT (l->fix_free, r);
  for (int i = 0; i < l->n; i++)
    for (int k = 0; k < l->nodes[i].nuses; k++)
      if (!l->nodes[i].uses[k].pred && l->nodes[i].uses[k].value < 0)
	CLEAR_HARD_REG_BIT (l->fix_free, l->nodes[i].uses[k].regno);
  for (int k = 0; k < 8; k++)
    if (l->binv & (1u << k))
      {
	unsigned g = INVALID_REGNUM;
	for (int pass = 0; pass < 2 && g == INVALID_REGNUM; pass++)
	  for (unsigned r = 16; r < R0_REGNUM + 64 && g == INVALID_REGNUM; r++)
	    if (TEST_HARD_REG_BIT (l->fix_free, r) && r != l->apb_tmp
		&& (pass || df_regs_ever_live_p (r)))
	      g = r;
	if (g == INVALID_REGNUM)
	  return e2k_ms_why ("no free register for a %b[] invariant");
	CLEAR_HARD_REG_BIT (l->fix_free, g);
	l->bmap[k] = g;
	if (dump_file)
	  fprintf (dump_file, ";; e2k_modsched: loop bb %d: invariant %%b[%d] "
		   "read from %s\n", l->bb->index, k, reg_names[g]);
      }
  e2k_ms_mark_apb (l, step, ivdef, derived);
  e2k_ms_mark_staa (l, step, ivdef, derived);
  e2k_ms_mem_deps (l, step, ivdef);
  if (l->want_dam && !e2k_ms_add_dam (l))
    return false;
  e2k_ms_mark_kdead (l);
  return true;
}

/* Sort ORDER[0..N) stably by KEY[ORDER[i]].  */
static void
e2k_ms_sort (int *order, int n, const int *key)
{
  for (int i = 1; i < n; i++)
    for (int k = i; k > 0 && key[order[k - 1]] > key[order[k]]; k--)
      std::swap (order[k - 1], order[k]);
}

/* An instruction of the prologue: node NODE of iteration J, or the copy
   of carried value VALUE into the ring (NODE -1), at time T.  */
struct e2k_ms_item { int t; int node; int j; int value; };

static int
e2k_ms_item_cmp (const void *a, const void *b, void *)
{
  return (((const e2k_ms_item *) a)->t - ((const e2k_ms_item *) b)->t);
}

/* Whether node I of L at time T would issue a divide a cycle before or
   after another one placed: a row's DFA state sees only its own cycle,
   and the divider stays busy the next (spec/isa/timing.md, "Divider":
   divides 1 cycle apart stall 4).  */
static bool
e2k_ms_div_clash (e2k_ms_loop *l, int ii, int i, int t)
{
  if (get_attr_type (l->nodes[i].insn) != TYPE_FDIV)
    return false;
  for (int j = 0; j < l->n; j++)
    if (j != i && l->nodes[j].time != INT_MIN
	&& get_attr_type (l->nodes[j].insn) == TYPE_FDIV)
      {
	int d = ((t - l->nodes[j].time) % ii + ii) % ii;
	if (d == 1 || d == ii - 1)
	  return true;
      }
  return false;
}

/* Try to put node I of L at time T in the reservation rows ROWS.  */
static bool
e2k_ms_place (e2k_ms_loop *l, int ii, char *rows, state_t tmp, int i, int t)
{
  char *row = rows + (((t % ii) + ii) % ii) * dfa_state_size;
  if (e2k_ms_div_clash (l, ii, i, t))
    return false;
  memcpy (tmp, row, dfa_state_size);
  if (state_transition (tmp, l->nodes[i].insn) >= 0)
    return false;
  memcpy (row, tmp, dfa_state_size);
  l->nodes[i].time = t;
  return true;
}

/* Place a while loop's exit test after its other nodes: the loop end
   is in the last row of the last stage, no node later, and it reads the
   predicate of node L->stay 3 cycles or more after it is set
   (spec/isa/timing.md).  Predicates don't rotate, so each one lives at
   most II cycles: the next iteration sets it II later, which a read in
   that same cycle doesn't see yet.  The exit test is a tree of nodes
   setting predicates: compares at the leaves, landps above them (a
   two-block loop's, and those of merged chains), each read 1 cycle or
   more after it is set.  Sets *TJUMP to the loop end's time.  */
static bool
e2k_ms_place_exit (e2k_ms_loop *l, int ii, char *rows, state_t tmp,
		   int *tjump)
{
  int n = l->n, s = l->stay, maxt = 0;
  int early[E2K_MS_MAX_NODES];
  for (int i = 0; i < n; i++)
    {
      early[i] = 0;
      if (!l->nodes[i].pred)
	maxt = MAX (maxt, l->nodes[i].time);
    }
  for (e2k_ms_dep &d : l->deps)
    if (l->nodes[d.to].pred && !l->nodes[d.from].pred)
      early[d.to] = MAX (early[d.to],
			 l->nodes[d.from].time + d.lat - ii * d.dist);
  /* Through the landps (a node's predicates come from nodes before it
     in the body).  */
  for (int i = 0; i < n; i++)
    for (e2k_ms_dep &d : l->deps)
      if (d.to == i && l->nodes[i].pred && l->nodes[d.from].pred)
	early[i] = MAX (early[i], early[d.from] + d.lat);
  int es = early[s];
  int tj = MAX (maxt, es + 3);
  tj += ((ii - 1 - tj % ii) % ii + ii) % ii;
  char *save = XALLOCAVEC (char, ii * dfa_state_size);
  memcpy (save, rows, ii * dfa_state_size);
  int pt[E2K_MS_MAX_NODES];
  /* With rotating predicates (e2k_ms_assign_pnames) one may live longer
     than II: then the stay node and the others go as late as they can,
     for short lives in the ring.  */
  bool rot = e2k_rotate_preds;
  for (int tries = 0; tries < 3; tries++, tj += ii)
    for (int ts = tj - 3; ts >= (rot ? es : MAX (tj - ii, es)); ts--)
      {
	memcpy (rows, save, ii * dfa_state_size);
	if (!e2k_ms_place (l, ii, rows, tmp, s, ts))
	  continue;
	for (int i = 0; i < n; i++)
	  pt[i] = INT_MIN;
	pt[s] = ts;
	/* The others from the top down: after their own predicates (as
	   early as that allows), before every reader, and at most II
	   before the last of them.  */
	bool ok = true;
	for (int c = n - 1; ok && c >= 0; c--)
	  {
	    if (c == s || !l->nodes[c].pred)
	      continue;
	    int hi = INT_MAX, last = INT_MIN;
	    for (e2k_ms_dep &d : l->deps)
	      if (d.from == c && l->nodes[d.to].pred && pt[d.to] != INT_MIN)
		{
		  hi = MIN (hi, pt[d.to] - d.lat);
		  last = MAX (last, pt[d.to]);
		}
	    if (last == INT_MIN)
	      continue;
	    int lo = rot ? early[c] : MAX (early[c], last - ii);
	    int t;
	    if (rot)
	      {
		for (t = hi; t >= lo; t--)
		  if (e2k_ms_place (l, ii, rows, tmp, c, t))
		    break;
		if (t < lo)
		  ok = false;
		else
		  pt[c] = t;
		continue;
	      }
	    for (t = lo; t <= hi; t++)
	      if (e2k_ms_place (l, ii, rows, tmp, c, t))
		break;
	    if (t > hi)
	      ok = false;
	    else
	      pt[c] = t;
	  }
	if (ok)
	  {
	    *tjump = tj;
	    return true;
	  }
      }
  memcpy (rows, save, ii * dfa_state_size);
  return false;
}

/* Modulo schedule L with initiation interval II.  EST: order the nodes
   by their earliest start at II over every dependence, carried ones
   included (a longest path weighing a dependence LAT - II * DIST), and
   start none before it.  The body's order puts a node that only reads
   the last iteration's value of a recurrence (xz's crc64: the shift of
   the carried CRC) at the top, which leaves the recurrence's last node
   too little room at every II.  BAL: put each node in the cycle of its
   window whose row has the fewest ALU operations so far, not the first
   that fits: Linpack's unrolled daxpy (v5, fmul_add) had its four
   multiply-adds ready in one cycle, and the row that took them all kept
   room for one store of the two the II needed.  */
static bool
e2k_ms_schedule (e2k_ms_loop *l, int ii, bool est, bool bal = false)
{
  int n = l->n;
  state_t rows = XALLOCAVEC (char, ii * dfa_state_size);
  state_t tmp = alloca (dfa_state_size);
  for (int r = 0; r < ii; r++)
    state_reset ((char *) rows + r * dfa_state_size);
  /* The loop end takes the last cycle.  */
  if (state_transition ((char *) rows + (ii - 1) * dfa_state_size,
			l->jump) >= 0)
    return false;

  /* ALU operations placed in each row (BAL).  */
  int *nalu = XALLOCAVEC (int, ii);
  for (int r = 0; r < ii; r++)
    nalu[r] = 0;

  /* Order: earliest start within an iteration, then body order.  */
  int asap[E2K_MS_MAX_NODES], order[E2K_MS_MAX_NODES];
  for (int i = 0; i < n; i++)
    {
      asap[i] = 0;
      order[i] = i;
      l->nodes[i].time = INT_MIN;
    }
  for (int i = 0; i < n; i++)
    for (e2k_ms_dep &d : l->deps)
      if (d.to == i && d.dist == 0 && d.from < i)
	asap[i] = MAX (asap[i], asap[d.from] + d.lat);
  if (est)
    {
      /* Bellman-Ford; still changing after N rounds, a recurrence is
	 longer than II.  The exit test is placed apart.  */
      for (int i = 0; i < n; i++)
	asap[i] = 0;
      bool changed = true;
      for (int round = 0; changed; round++)
	{
	  if (round > n)
	    return false;
	  changed = false;
	  for (e2k_ms_dep &d : l->deps)
	    if (!l->nodes[d.from].pred && !l->nodes[d.to].pred
		&& asap[d.from] + d.lat - ii * d.dist > asap[d.to])
	      {
		asap[d.to] = asap[d.from] + d.lat - ii * d.dist;
		changed = true;
	      }
	}
    }
  e2k_ms_sort (order, n, asap);
  /* A check right after its lock load: it is the most constrained of
     what moves to the last stage.  */
  if (l->kchk >= 0)
    {
      int pk = 0, pl = 0;
      for (int k = 0; k < n; k++)
	{
	  if (order[k] == l->kchk)
	    pk = k;
	  if (order[k] == l->dam)
	    pl = k;
	}
      for (int k = pk; k > pl + 1; k--)
	order[k] = order[k - 1];
      if (pk > pl)
	order[pl + 1] = l->kchk;
    }

  for (int k = 0; k < n; k++)
    {
      int i = order[k];
      /* A while loop's exit test goes last (e2k_ms_place_exit).  */
      if (l->nodes[i].pred)
	continue;
      /* Stores and a check move to the last stage afterwards, keeping
	 their rows: between two of them only the rows count, and a
	 successor that moves later bounds nothing now.  */
      auto movable = [&] (int x) { return l->nodes[x].store || x == l->kchk; };
      auto rowof = [&] (int x) { return ((l->nodes[x].time % ii) + ii) % ii; };
      bool mov = movable (i);
      int early = INT_MIN, late = INT_MAX, rlo = INT_MIN, rhi = INT_MAX;
      for (e2k_ms_dep &d : l->deps)
	{
	  if (d.to == i && l->nodes[d.from].time != INT_MIN)
	    {
	      if (mov && movable (d.from))
		rlo = MAX (rlo, rowof (d.from) + d.lat - ii * d.dist);
	      else
		early = MAX (early,
			     l->nodes[d.from].time + d.lat - ii * d.dist);
	    }
	  if (d.from == i && l->nodes[d.to].time != INT_MIN)
	    {
	      if (mov && movable (d.to))
		rhi = MIN (rhi, rowof (d.to) - d.lat + ii * d.dist);
	      else if (!movable (d.to))
		late = MIN (late, l->nodes[d.to].time - d.lat + ii * d.dist);
	    }
	}
      /* Only successors placed: as late as they allow (an induction
	 step before the loads of the next iteration that use it).  */
      if (early == INT_MIN)
	early = late == INT_MAX ? 0 : late - (ii - 1);
      if (est)
	early = MAX (early, asap[i]);
      enum attr_type ty = get_attr_type (l->nodes[i].insn);
      bool alu = ty != TYPE_PLOG && ty != TYPE_MOVA;
      /* What only the prologue runs takes no channel.  */
      bool kdead = l->nodes[i].kdead;
      int t, best = INT_MIN;
      for (t = early; t < early + ii && t <= late; t++)
	{
	  int r = ((t % ii) + ii) % ii;
	  if (kdead)
	    {
	      best = t;
	      break;
	    }
	  if (r < rlo || r > rhi || e2k_ms_div_clash (l, ii, i, t))
	    continue;
	  char *row = (char *) rows + r * dfa_state_size;
	  memcpy (tmp, row, dfa_state_size);
	  if (state_transition (tmp, l->nodes[i].insn) < 0)
	    {
	      if (!bal || !alu)
		{
		  best = t;
		  break;
		}
	      if (best == INT_MIN
		  || nalu[r] < nalu[((best % ii) + ii) % ii])
		best = t;
	    }
	}
      if (best != INT_MIN)
	{
	  t = best;
	  int r = ((t % ii) + ii) % ii;
	  char *row = (char *) rows + r * dfa_state_size;
	  if (!kdead && state_transition (row, l->nodes[i].insn) >= 0)
	    gcc_unreachable ();
	  nalu[r] += alu && !kdead;
	}
      else
	{
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: II %d: no cycle for insn %d "
		     "in %d..%d (rows %d..%d)\n", ii,
		     INSN_UID (l->nodes[i].insn), early,
		     MIN (early + ii - 1, late), rlo, rhi);
	  return false;
	}
      l->nodes[i].time = t;
    }

  /* Start at stage 0, keeping the rows (the loop end is in the last).  */
  int mint = INT_MAX;
  for (int i = 0; i < n; i++)
    if (!l->nodes[i].pred)
      mint = MIN (mint, l->nodes[i].time);
  int shift = (mint >= 0 ? mint / ii : -((-mint + ii - 1) / ii)) * ii;
  for (int i = 0; i < n; i++)
    if (!l->nodes[i].pred)
      l->nodes[i].time -= shift;

  /* Every store goes to the last stage, the same row.  */
  int maxt = 0;
  for (int i = 0; i < n; i++)
    maxt = MAX (maxt, l->nodes[i].time);
  if (l->wl)
    {
      if (!e2k_ms_place_exit (l, ii, (char *) rows, tmp, &maxt))
	{
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: II %d: no place for the "
		     "exit test\n", ii);
	  return false;
	}
    }
  int stages = maxt / ii + 1;

  /* A lock load per stage is in flight, and the DAM has 32 entries
     (spec/isa/speculation.md).  */
  if (l->kchk >= 0 && stages > 16)
    return false;
  /* So does the check of a lock load, which the DFA keeps out of the
     loop end's row (its rbranch and the ct both take SS).  */
  for (int i = 0; i < n; i++)
    if (l->nodes[i].store || i == l->kchk)
      l->nodes[i].time += (stages - 1 - l->nodes[i].time / ii) * ii;
  for (e2k_ms_dep &d : l->deps)
    if (l->nodes[d.to].time + ii * d.dist < l->nodes[d.from].time + d.lat)
      {
	if (dump_file)
	  fprintf (dump_file, ";; e2k_modsched: II %d: stores in the last "
		   "stage break insn %d -> %d\n", ii,
		   INSN_UID (l->nodes[d.from].insn),
		   INSN_UID (l->nodes[d.to].insn));
	return false;
      }
  l->ii = ii;
  l->stages = stages;
  return stages > 1;
}

/* What a failed check redoes, in L->rec, and the lifetimes that takes,
   in L->ext.  The check of iteration I runs at its time TK; node N of
   iteration I + D ran at D * II + T_N.  Redo, in time order, what ran
   after the lock load and before the check and used its value, through
   values or predicates; and then every instance of the exit test in
   that span, since a predicate holds the last instance's value.  What
   those read and write must still be in its register then.  */
static void
e2k_ms_dam_plan (e2k_ms_loop *l)
{
  l->rec.truncate (0);
  l->ext.truncate (0);
  if (l->kchk < 0)
    return;
  int ii = l->ii, s = l->stages;
  int tk = l->nodes[l->kchk].time, tl = l->nodes[l->dam].time;
  unsigned dep[E2K_MS_MAX_NODES];
  e2k_ms_dependents (l, l->dam, dep);
  bool preds = false;
  for (int n = 0; n < l->n; n++)
    for (int d = 0; d <= s; d++)
      if (l->nodes[n].pred && (dep[n] & (1u << d))
	  && d * ii + l->nodes[n].time > tl && d * ii + l->nodes[n].time <= tk)
	preds = true;
  for (int n = 0; n < l->n; n++)
    {
      if (n == l->kchk || l->nodes[n].store)
	continue;
      for (int d = -s; d <= s; d++)
	{
	  int t = d * ii + l->nodes[n].time;
	  if (t <= tl || t > tk)
	    continue;
	  if (l->nodes[n].pred ? preds : d >= 0 && (dep[n] & (1u << d)))
	    l->rec.safe_push (std::make_pair (n, d));
	}
    }
  /* In time order.  */
  for (unsigned a = 1; a < l->rec.length (); a++)
    for (unsigned b = a; b > 0; b--)
      {
	std::pair<int, int> &x = l->rec[b - 1], &y = l->rec[b];
	if (x.second * ii + l->nodes[x.first].time
	    <= y.second * ii + l->nodes[y.first].time)
	  break;
	std::swap (x, y);
      }
  for (std::pair<int, int> &r : l->rec)
    {
      e2k_ms_node *node = &l->nodes[r.first];
      int d = r.second;
      if (node->value >= 0)
	l->ext.safe_push (std::make_pair (node->value, tk - d * ii));
      for (int k = 0; k < node->nuses; k++)
	if (!node->uses[k].pred && node->uses[k].value >= 0)
	  l->ext.safe_push (std::make_pair (node->uses[k].value,
					    tk - (d - node->uses[k].dist) * ii));
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: a failed check redoes insn %d "
		 "of iteration +%d\n", INSN_UID (node->insn), d);
    }
}

/* Give the values their names in the ring; false if it gets too big.

   Rotation makes the ring a cylinder: with P pairs per lane (even and
   odd names), the instance of value V from iteration I sits in physical
   pair (C_V - I) mod P from its definition to its last use, at times
   I * II + [START, END).  Values are packed first-fit: V and W of one
   lane clash when instances I and I + D, D = C_W - C_V (mod P), are
   alive at once.  */
static bool
e2k_ms_assign_names (e2k_ms_loop *l, int gap)
{
  int ii = l->ii, s = l->stages, nv = l->values.length ();
  auto_vec<int> st (nv), en (nv), order (nv), lane (nv), slot (nv);
  for (int v = 0; v < nv; v++)
    {
      const e2k_ms_value &val = l->values[v];
      rtx_insn *def = l->nodes[val.node].insn;
      st.quick_push (l->nodes[val.node].time);
      /* Until the value lands, at least.  */
      en.quick_push (st[v] + MAX (insn_default_latency (def), 1));
      /* Until after the loop, for the iteration OUT_DIST before the
	 last.  */
      if (val.out_dist >= 0)
	en[v] = MAX (en[v], (s + val.out_dist) * ii);
      /* Until a failed check has redone what used it: the compensation
	 code runs after the check's wide instruction, whose results are
	 written by then, so through that instruction (a value it wrote
	 into the same pair was the operand the compensation read;
	 gcc.dg/vect/vect-alias-check-18.c).  */
      for (std::pair<int, int> &x : l->ext)
	if (x.first == v)
	  en[v] = MAX (en[v], x.second + 1);
      order.quick_push (v);
      lane.quick_push (-1);
      slot.quick_push (-1);
    }
  for (int i = 0; i < l->n; i++)
    for (int k = 0; k < l->nodes[i].nuses; k++)
      {
	e2k_ms_use *u = &l->nodes[i].uses[k];
	if (u->value >= 0 && !u->pred)
	  en[u->value] = MAX (en[u->value],
			      l->nodes[i].time + u->dist * ii);
      }
  for (int a = 1; a < nv; a++)
    for (int b = a; b > 0 && st[order[b - 1]] > st[order[b]]; b--)
      std::swap (order[b - 1], order[b]);

  /* A value whose last use issues no later than the next iteration's
     def needs no ring: it gets a register of its own outside it (NPB
     SP's 140-operation loops have 135 values, for what were the ring's
     62 names), one the loop leaves free (L->fix_free), shared by values
     whose lifetimes, modulo II, don't meet; registers the function uses
     already first, which don't widen the window.  Not a value carried
     or read after the loop, nor in a loop that reads an earlier
     iteration's instances after the kernel (a while loop's exits, a
     failed check's compensation).  */
  auto_vec<int> freg (nv);
  for (int v = 0; v < nv; v++)
    freg.quick_push (-1);
  if (e2k_ms_fixed && !l->wl && l->kchk < 0)
    {
      uint64_t occ[R0_REGNUM + 64] = { 0 };
      for (int k = 0; k < nv; k++)
	{
	  int v = order[k];
	  const e2k_ms_value &val = l->values[v];
	  if (val.carried || val.carried2 || val.out_dist >= 0
	      || en[v] + gap - st[v] > ii)
	    continue;
	  uint64_t m = 0;
	  for (int t = st[v]; t < en[v] + gap; t++)
	    m |= HOST_WIDE_INT_1U << (((t % ii) + ii) % ii);
	  for (int pass = 0; pass < 2 && freg[v] < 0; pass++)
	    for (unsigned r = 16; r < R0_REGNUM + 64; r++)
	      if (TEST_HARD_REG_BIT (l->fix_free, r) && r != l->apb_tmp
		  && !(occ[r] & m) && (pass || df_regs_ever_live_p (r)))
		{
		  occ[r] |= m;
		  freg[v] = r;
		  break;
		}
	}
    }

  /* Whether V in pair C clashes with W in pair CW, both of one lane.  */
  auto clash = [&] (int v, int c, int w, int cw, int p)
    {
      int d0 = ((cw - c) % p + p) % p;
      for (int d = d0 - (s + 2) * p; d <= (s + 2) * p; d += p)
	{
	  if (v == w && d == 0)
	    continue;
	  if (!(st[w] + d * ii >= en[v] + gap
		|| en[w] + d * ii + gap <= st[v]))
	    return true;
	}
      return false;
    };

  for (int p = 1; p <= E2K_ROT_MAX / 2 - 1; p++)
    {
      bool ok = true;
      for (int k = 0; k < nv && ok; k++)
	{
	  int v = order[k];
	  lane[v] = slot[v] = -1;
	  if (freg[v] >= 0)
	    continue;
	  for (int ln = 0; ln < 2 && slot[v] < 0; ln++)
	    for (int c = 0; c < p && slot[v] < 0; c++)
	      {
		bool bad = clash (v, c, v, c, p);
		for (int k2 = 0; k2 < k && !bad; k2++)
		  {
		    int w = order[k2];
		    bad = (freg[w] < 0 && lane[w] == ln
			   && clash (v, c, w, slot[w], p));
		  }
		if (!bad)
		  {
		    lane[v] = ln;
		    slot[v] = c;
		  }
	      }
	  ok = slot[v] >= 0;
	}
      if (!ok)
	continue;
      l->pairs = p;
      for (int v = 0; v < nv; v++)
	{
	  int sd = l->nodes[l->values[v].node].time / ii;
	  int n = ((slot[v] + sd - (s - 1)) % p + p) % p;
	  l->values[v].name = freg[v] >= 0 ? -1 - freg[v] : 2 * n + lane[v];
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: value %d (r%d, insn %d) "
		     "alive %d..%d, lane %d pair %d, name %d%s%s\n", v,
		     l->values[v].regno, INSN_UID (l->nodes[l->values[v].node].insn),
		     st[v], en[v], lane[v], slot[v], l->values[v].name,
		     l->values[v].carried ? " carried" : "",
		     l->values[v].out_dist >= 0 ? " live-out" : "");
	}
      return true;
    }
  /* Up to 63 pairs (rsz, 6 bits); e2k_compute_window keeps rbs within
     its 6 bits.  */
  if (dump_file)
    {
      int sum = 0;
      for (int v = 0; v < nv; v++)
	if (freg[v] < 0)
	  {
	    sum += en[v] + gap - st[v];
	    fprintf (dump_file, ";; e2k_modsched: ring: value %d (insn %d) "
		     "%d..%d\n", v, INSN_UID (l->nodes[l->values[v].node].insn),
		     st[v], en[v]);
	  }
      fprintf (dump_file, ";; e2k_modsched: ring: %d cycles of values at "
	       "II %d\n", sum, ii);
    }
  return false;
}

/* The predicates of a while loop's exit test in a ring of their own
   (spec/isa/loops.md, "Rotation"): setbp psz = R - 1 makes %pred0 ..
   %pred(R - 1) rotate, and abp at the loop end makes the old %pred0 the
   new %pred1, so each iteration's predicates get fresh names as its
   %b[] values do, and may live longer than II (lcc leaves its while
   loops through "ct ? %pred1").  Packed like the values, one name per
   rotation.  No predicate below R may be live around the loop.  The
   predicates merges and predicated stores read (of a counted loop too)
   go in the same ring, and need it: a store is in the last stage.
   False if that can't be.  */
static bool
e2k_ms_assign_pnames (e2k_ms_loop *l)
{
  l->npred = 0;
  bool data = false;
  for (int i = 0; i < l->n; i++)
    data |= l->nodes[i].dpred;
  if (!e2k_rotate_preds)
    return !data;
  if (!l->wl && !data)
    return true;
  int ii = l->ii, s = l->stages, n = l->n;
  int st[E2K_MS_MAX_NODES], en[E2K_MS_MAX_NODES], slot[E2K_MS_MAX_NODES];
  int order[E2K_MS_MAX_NODES], np = 0;
  for (int i = 0; i < n; i++)
    if (l->nodes[i].pred || l->nodes[i].dpred)
      {
	st[i] = l->nodes[i].time;
	en[i] = st[i] + 1;
	order[np++] = i;
      }
  if (!np)
    return true;
  for (int i = 0; i < n; i++)
    for (int k = 0; k < l->nodes[i].nuses; k++)
      if (l->nodes[i].uses[k].pred)
	{
	  int c = l->nodes[i].uses[k].value;
	  en[c] = MAX (en[c], l->nodes[i].time + l->nodes[i].uses[k].dist * ii);
	}
  /* The loop end reads the stay predicate in the last cycle, and no
     other predicate may take its name there: the jump comes after the
     cycle's other operations in the insn stream, so dataflow would see
     it read their value (and delete the prologue's).  */
  if (l->stay >= 0)
    en[l->stay] = MAX (en[l->stay], s * ii);
  for (int a = 1; a < np; a++)
    for (int b = a; b > 0 && st[order[b - 1]] > st[order[b]]; b--)
      std::swap (order[b - 1], order[b]);
  auto clash = [&] (int v, int c, int w, int cw, int p)
    {
      int d0 = ((cw - c) % p + p) % p;
      for (int d = d0 - (s + 2) * p; d <= (s + 2) * p; d += p)
	{
	  if (v == w && d == 0)
	    continue;
	  if (!(st[w] + d * ii >= en[v] || en[w] + d * ii <= st[v]))
	    return true;
	}
      return false;
    };
  bitmap lh = df_get_live_in (l->bb), lx = df_get_live_in (l->exit);
  bitmap l1 = l->x1 ? df_get_live_in (l->x1) : lx;
  for (int p = 1; p <= 32; p++)
    {
      if (fixed_regs[PRED0_REGNUM + p - 1]
	  || bitmap_bit_p (lh, PRED0_REGNUM + p - 1)
	  || bitmap_bit_p (lx, PRED0_REGNUM + p - 1)
	  || bitmap_bit_p (l1, PRED0_REGNUM + p - 1))
	return false;
      bool ok = true;
      for (int k = 0; k < np && ok; k++)
	{
	  int v = order[k];
	  slot[v] = -1;
	  for (int c = 0; c < p && slot[v] < 0; c++)
	    {
	      bool bad = clash (v, c, v, c, p);
	      for (int k2 = 0; k2 < k && !bad; k2++)
		bad = clash (v, c, order[k2], slot[order[k2]], p);
	      if (!bad)
		slot[v] = c;
	    }
	  ok = slot[v] >= 0;
	}
      if (!ok)
	continue;
      l->npred = p;
      for (int k = 0; k < np; k++)
	{
	  int v = order[k], sd = l->nodes[v].time / ii;
	  l->nodes[v].pname = ((slot[v] + sd - (s - 1)) % p + p) % p;
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: predicate of insn %d alive "
		     "%d..%d, name %d of %d\n", INSN_UID (l->nodes[v].insn),
		     st[v], en[v], l->nodes[v].pname, p);
	}
      return true;
    }
  return false;
}

/* The ring name, in the frame of kernel iteration FRAME, of predicate
   node I's instance from iteration J (as e2k_ms_name).  */
static int
e2k_ms_pname (e2k_ms_loop *l, int i, int j, int frame)
{
  int kdef = j + l->nodes[i].time / l->ii - (l->stages - 1);
  int name = (l->nodes[i].pname + (frame - kdef)) % l->npred;
  return name < 0 ? name + l->npred : name;
}

/* The %b[] name, in the frame of kernel iteration FRAME, of value V's
   instance from iteration J (iteration 0 is the first stage of kernel
   iteration -(S - 1)).  */
static int
e2k_ms_name (e2k_ms_loop *l, int v, int j, int frame)
{
  const e2k_ms_value &val = l->values[v];
  if (val.name < 0)
    return val.name;
  int kdef = j + l->nodes[val.node].time / l->ii - (l->stages - 1);
  int ring = 2 * l->pairs;
  int name = (val.name + 2 * (frame - kdef)) % ring;
  return name < 0 ? name + ring : name;
}

/* The register of NAME: a %b[] one, or (below 0) the fixed register of a
   value outside the ring (e2k_ms_assign_names).  */
static rtx
e2k_ms_reg (machine_mode mode, int name)
{
  return gen_rtx_REG (mode, name < 0 ? -1 - name : E2K_ROT_REGNO (name));
}

static bool e2k_ms_reads_p (rtx, unsigned);

/* A clocked prologue's own schedule.  The modulo schedule's times put
   the copies in and the first iterations where the kernel would have
   them, slack and all (a copy in at its value's time in a virtual
   earlier iteration, the first load three cycles after it).  Instead
   place the items PATS, in their emission order SEQ, each in the first
   cycle (from 2, after setbn) where its operands are there at the
   pipeliner's latencies (e2k_ms_analyze: crossings counted) and the
   DFA takes it, keeping a register's reads before a write of it and
   its writes in order.  The hardware interlocks registers: a late
   operand costs a stall, never a wrong value.  Fills CLOCK (by item)
   and *LAST; false (keep the modulo times) when an item stores, locks
   or checks, or no cycle near its old one takes it.  OC is each item's
   clock by the modulo schedule.  */
static bool
e2k_ms_list_prologue (const vec<rtx> &pats, const vec<int> &seq,
		      const vec<int> &oc, vec<int> *clock, int *last)
{
  int ni = pats.length ();
  auto_vec<rtx_insn *> xi (ni);
  auto_vec<HARD_REG_SET> sets (ni);
  for (int k = 0; k < ni; k++)
    {
      rtx_insn *x = make_insn_raw (copy_rtx (pats[k]));
      if (recog_memoized (x) < 0 || volatile_insn_p (PATTERN (x)))
	return false;
      enum attr_type t = get_attr_type (x);
      if (t == TYPE_STORE || t == TYPE_LDLOCK || t == TYPE_LDCHK
	  || MEM_P (SET_DEST (e2k_ms_set (pats[k]))))
	return false;
      xi.quick_push (x);
      HARD_REG_SET h;
      CLEAR_HARD_REG_SET (h);
      note_stores (x, record_hard_reg_sets, &h);
      sets.quick_push (h);
    }
  clock->truncate (0);
  clock->safe_grow_cleared (ni);
  /* DFA states of the cycles so far.  */
  auto_vec<state_t> states;
  auto state_of = [&] (int c)
    {
      while ((int) states.length () <= c)
	{
	  state_t st = xmalloc (dfa_state_size);
	  state_reset (st);
	  states.safe_push (st);
	}
      return states[c];
    };
  bool ok = true;
  state_t tmp = alloca (dfa_state_size);
  for (int p = 0; p < ni && ok; p++)
    {
      int k = seq[p], e = 2;
      for (int q = 0; q < p; q++)
	{
	  int m = seq[q];
	  for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
	    {
	      if (TEST_HARD_REG_BIT (sets[m], r)
		  && e2k_ms_reads_p (pats[k], r))
		{
		  enum attr_type dt = get_attr_type (xi[m]);
		  int cross = (dt == TYPE_FP || dt == TYPE_FMA
			       || dt == TYPE_FFMA || dt == TYPE_FCVT
			       || dt == TYPE_FDIV || dt == TYPE_MUL ? 2 : 1);
		  if (E2K_LAT6 && dt == TYPE_LOAD)
		    cross = 0;
		  int lat = MAX (insn_latency (xi[m], xi[k]), 1);
		  if (e2k_packed_type_p (dt))
		    cross = MAX (4 - lat, 0);
		  /* No more than the modulo schedule gave it, which keeps
		     a recurrence in one cluster (e2k_ms_pipeline).  */
		  lat = MAX (MIN (lat + cross, oc[k] - oc[m]), 1);
		  e = MAX (e, (*clock)[m] + lat);
		}
	      if (TEST_HARD_REG_BIT (sets[k], r))
		{
		  if (e2k_ms_reads_p (pats[m], r))
		    e = MAX (e, (*clock)[m]);
		  if (TEST_HARD_REG_BIT (sets[m], r))
		    e = MAX (e, (*clock)[m] + 1);
		}
	    }
	}
      int c = e;
      for (;; c++)
	{
	  if (c > oc[k] + 64)
	    {
	      ok = false;
	      break;
	    }
	  memcpy (tmp, state_of (c), dfa_state_size);
	  if (state_transition (tmp, xi[k]) < 0)
	    {
	      memcpy (state_of (c), tmp, dfa_state_size);
	      break;
	    }
	}
      (*clock)[k] = c;
    }
  for (state_t st : states)
    free (st);
  if (!ok)
    return false;
  *last = 0;
  for (int k = 0; k < ni; k++)
    *last = MAX (*last, (*clock)[k]);
  return true;
}

/* The SET of a node's pattern (a lock load's is in a PARALLEL, a
   predicated store's in a COND_EXEC).  */
static rtx
e2k_ms_set (rtx pat)
{
  if (GET_CODE (pat) == COND_EXEC)
    pat = COND_EXEC_CODE (pat);
  return GET_CODE (pat) == PARALLEL ? XVECEXP (pat, 0, 0) : pat;
}

/* Node I's pattern for iteration J, with names in the frame of kernel
   iteration FRAME.  */
static rtx
e2k_ms_instance (e2k_ms_loop *l, int i, int j, int frame)
{
  e2k_ms_node *node = &l->nodes[i];
  rtx pat = copy_rtx (PATTERN (node->insn));
  rtx set = e2k_ms_set (pat);
  auto subst = [&] (rtx *loc)
    {
      subrtx_ptr_iterator::array_type array;
      FOR_EACH_SUBRTX_PTR (iter, array, loc, NONCONST)
	if (REG_P (**iter) && B_REGNO_P (REGNO (**iter))
	    && (l->binv & (1u << (REGNO (**iter) - B0_REGNUM))))
	  **iter = gen_rtx_REG (GET_MODE (**iter),
				l->bmap[REGNO (**iter) - B0_REGNUM]);
	else if (REG_P (**iter))
	  for (int k = 0; k < node->nuses; k++)
	    if (node->uses[k].regno == REGNO (**iter)
		&& node->uses[k].value >= 0 && !node->uses[k].pred)
	      {
		rtx *slot = *iter;
		*slot = e2k_ms_reg (GET_MODE (**iter),
				  e2k_ms_name (l, node->uses[k].value,
					       j - node->uses[k].dist,
					       frame));
		break;
	      }
	    else if (node->uses[k].regno == REGNO (**iter)
		     && node->uses[k].pred && l->npred)
	      {
		rtx *slot = *iter;
		*slot = gen_rtx_REG (BImode,
				     PRED0_REGNUM
				     + e2k_ms_pname (l, node->uses[k].value,
						     j - node->uses[k].dist,
						     frame));
		break;
	      }
    };
  if (node->chk >= 0)
    {
      /* A check: the lock load's address, into its register.  */
      rtx ite = SET_SRC (set);
      subst (&XEXP (ite, 1));
      rtx r = e2k_ms_reg (GET_MODE (SET_DEST (set)),
			  e2k_ms_name (l, l->nodes[node->chk].value, j, frame));
      SET_DEST (set) = r;
      XEXP (ite, 2) = r;
      XVECEXP (XEXP (XEXP (ite, 0), 0), 0, 0) = r;
      return pat;
    }
  subst (&SET_SRC (set));
  if (GET_CODE (pat) == COND_EXEC)
    subst (&COND_EXEC_TEST (pat));
  if (MEM_P (SET_DEST (set)) && node->rebase_off)
    SET_DEST (set) = adjust_address_nv (SET_DEST (set),
					GET_MODE (SET_DEST (set)),
					-node->rebase_off);
  if (MEM_P (SET_DEST (set)))
    subst (&XEXP (SET_DEST (set), 0));
  else if (!node->pred && !node->dpred)
    SET_DEST (set) = e2k_ms_reg (GET_MODE (SET_DEST (set)),
				 e2k_ms_name (l, node->value, j, frame));
  else if (l->npred)
    SET_DEST (set) = gen_rtx_REG (BImode,
				  PRED0_REGNUM + e2k_ms_pname (l, i, j, frame));
  return pat;
}

/* The %b[] name, after the loop, of value V's instance from the
   iteration BACK before the last.  The kernel ran once more after the
   last iteration's def stage D, so it rotated S - D times since.  */
static int
e2k_ms_exit_name (e2k_ms_loop *l, int v, int back)
{
  const e2k_ms_value &val = l->values[v];
  if (val.name < 0)
    return val.name;
  return ((val.name + 2 * (l->stages - l->nodes[val.node].time / l->ii
			   + back))
	  % (2 * l->pairs));
}

/* Node I's pattern run after the loop on the last iteration's values.  */
static rtx
e2k_ms_exit_instance (e2k_ms_loop *l, int i)
{
  e2k_ms_node *node = &l->nodes[i];
  rtx pat = copy_rtx (PATTERN (node->insn));
  subrtx_ptr_iterator::array_type array;
  FOR_EACH_SUBRTX_PTR (iter, array, &SET_SRC (pat), NONCONST)
    if (REG_P (**iter))
      for (int k = 0; k < node->nuses; k++)
	if (node->uses[k].regno == REGNO (**iter)
	    && node->uses[k].value >= 0 && !node->uses[k].pred)
	  {
	    rtx *slot = *iter;
	    *slot = e2k_ms_reg (GET_MODE (**iter),
				e2k_ms_exit_name (l, node->uses[k].value,
						  node->uses[k].dist));
	    break;
	  }
  return pat;
}

/* The first block's exit test run again after the loop: its nodes in
   order, after AFTER, or at the end of the sequence being built if
   AFTER is null.  Returns the last.  Its compares are speculative: in a
   merged chain a compare's operands may come from loads whose guard,
   an earlier condition, didn't hold, and the landps ignore them.  */
static rtx_insn *
e2k_ms_emit_exit_test (e2k_ms_loop *l, rtx_insn *after)
{
  rtx_insn *x = after;
  for (int c : l->c1s)
    {
      rtx pat = e2k_ms_exit_instance (l, c);
      x = x ? emit_insn_after (pat, x) : emit_insn (pat);
      if (recog_memoized (x) < 0)
	gcc_unreachable ();
      if (get_attr_type (x) == TYPE_CMP || get_attr_type (x) == TYPE_FCMP)
	e2k_ms_set_flag (x, E2K_MS_SM);
    }
  return x;
}

/* A mode for copying a register of MODE whole: one of the predicable
   moves.  */
static machine_mode
e2k_ms_copy_mode (machine_mode mode)
{
  if (mode == SImode || mode == DImode || mode == SFmode || mode == DFmode)
    return mode;
  return GET_MODE_SIZE (mode) <= 4 ? SImode : DImode;
}

/* Whether pattern X reads hard register R.  */
static bool
e2k_ms_reads_p (rtx x, unsigned r)
{
  if (PRED_REGNO_P (r))
    {
      if (GET_CODE (x) == COND_EXEC
	  && refers_to_regno_p (r, r + 1, COND_EXEC_TEST (x), NULL))
	return true;
      return refers_to_regno_p (r, r + 1, SET_SRC (e2k_ms_set (x)), NULL);
    }
  x = e2k_ms_set (x);
  rtx dest = SET_DEST (x);
  if (reg_overlap_mentioned_p (gen_rtx_REG (DImode, r), SET_SRC (x)))
    return true;
  return (MEM_P (dest)
	  && reg_overlap_mentioned_p (gen_rtx_REG (DImode, r),
				      XEXP (dest, 0)));
}

/* Put PATS[G..GE), which run in one cycle (reading before writing), in
   an order that means the same run one after another: an instruction
   that writes a register another one reads goes after it.  Appends the
   indices to SEQ; false if there is no such order.  */
static bool
e2k_ms_order_cycle (const vec<rtx> &pats, int g, int ge, vec<int> *seq)
{
  auto_vec<bool> done (ge - g);
  for (int k = g; k < ge; k++)
    done.quick_push (false);
  for (int left = ge - g; left > 0; left--)
    {
      int pick = -1;
      for (int a = g; a < ge && pick < 0; a++)
	{
	  if (done[a - g])
	    continue;
	  rtx da = SET_DEST (e2k_ms_set (pats[a]));
	  bool read = false;
	  for (int b = g; b < ge && !read; b++)
	    read = (b != a && !done[b - g] && REG_P (da)
		    && e2k_ms_reads_p (pats[b], REGNO (da)));
	  if (!read)
	    pick = a;
	}
      if (pick < 0)
	return false;
      done[pick - g] = true;
      seq->safe_push (pick);
    }
  return true;
}

/* What a two-block while loop's blocks become one with: the second
   block B, the first one's exit jump HJUMP and its disp HDISP (or NULL),
   the predicate PSTAY of the landp the loop end now tests, and P1 the
   first block's exit predicate.  */
/* JUMP, a prepared conditional transfer at the end of its block: the
   disp in the same block that prepares its CTPR, if nothing else in
   between touches it, or NULL.  An entry edge along it can then take a
   prologue: the disp is pointed at the new block (e2k_ms_split_entry).
   One prepared elsewhere (an outer loop's latch whose disp is in its
   preheader) can't be.  */
static rtx_insn *
e2k_ms_local_disp (rtx_insn *jump)
{
  if (!JUMP_P (jump) || recog_memoized (jump) < 0
      || get_attr_type (jump) != TYPE_CT
      || GET_CODE (PATTERN (jump)) != PARALLEL)
    return NULL;
  rtx ctpr = XEXP (XVECEXP (PATTERN (jump), 0, 1), 0);
  basic_block bb = BLOCK_FOR_INSN (jump);
  for (rtx_insn *x = PREV_INSN (jump); x && x != PREV_INSN (BB_HEAD (bb));
       x = PREV_INSN (x))
    {
      if (!NONDEBUG_INSN_P (x))
	continue;
      if (CALL_P (x))
	return NULL;
      if (reg_mentioned_p (ctpr, PATTERN (x)))
	return (recog_memoized (x) == CODE_FOR_e2k_disp_label
		&& reg_set_p (ctpr, x) ? x : NULL);
    }
  return NULL;
}

/* Split entry edge E for a prologue; a prepared conditional transfer
   along it has its disp moved to the new block.  */
static basic_block
e2k_ms_split_entry (edge e)
{
  rtx_insn *disp = NULL;
  if (!(e->flags & EDGE_FALLTHRU) && !single_succ_p (e->src))
    disp = e2k_ms_local_disp (BB_END (e->src));
  basic_block p = split_edge (e);
  if (disp)
    {
      rtx label = block_label (p);
      rtx un = SET_SRC (PATTERN (disp));
      rtx old = label_ref_label (XVECEXP (un, 0, 0));
      XVECEXP (un, 0, 0) = gen_rtx_LABEL_REF (Pmode, label);
      LABEL_NUSES (old)--;
      LABEL_NUSES (label)++;
      if (rtx note = find_reg_note (disp, REG_LABEL_OPERAND, old))
	remove_note (disp, note);
      add_reg_note (disp, REG_LABEL_OPERAND, label);
      INSN_CODE (disp) = -1;
      if (recog_memoized (disp) < 0)
	gcc_unreachable ();
      df_insn_rescan (disp);
    }
  return p;
}

struct e2k_ms_wl
{
  basic_block b;
  rtx_insn *hjump, *hdisp;
  /* The loop end's disp, when the second block has it (the loop end
     prepared like any branch, its loop not innermost to GCC): it goes
     to the start of each prologue.  */
  rtx_insn *bdisp;
  rtx pstay, p1;
};

/* Make a two-block while loop one block: drop the first block's exit
   and let the loop end test the landp.  */
static void
e2k_ms_wl_merge (e2k_ms_loop *l, const e2k_ms_wl *w)
{
  basic_block h = l->bb;
  edge ex = NULL, e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, h->succs)
    if (e->dest != w->b)
      ex = e;
  if (w->hdisp)
    delete_insn (w->hdisp);
  if (w->bdisp)
    delete_insn (w->bdisp);
  delete_insn (w->hjump);
  remove_edge (ex);
  e = single_succ_edge (h);
  e->flags |= EDGE_FALLTHRU;
  e->probability = profile_probability::always ();
  rtx cond = e2k_ms_jump_cond (l->jump);
  PUT_CODE (cond, NE);
  XEXP (cond, 0) = w->pstay;
  INSN_CODE (l->jump) = -1;
  if (recog_memoized (l->jump) < 0)
    gcc_unreachable ();
  df_insn_rescan (l->jump);
  merge_blocks (h, w->b);
}

/* Emit the pipelined loop: prologue before each of PRE_ENDS (a counted
   loop) or on each of ENTRIES (a while loop), kernel, copies out on
   EXIT_EDGE.  W: a two-block while loop's merge, else NULL.  False,
   with nothing changed, if the prologue can't be put in order.  */
/* Give the movas of L their channels and areas, and queue the
   program, .LAPB<N>; returns N.  Channels: each kernel row's movas in order, 0 and
   1 reading areas of the buffer's left half, 2 and 3 its right half
   (spec/isa/apb.md, "What a mova reads").  An area holds the movas of
   one descriptor, element size and stage in one half, within 32 bytes
   (mrng) of its first: a stage reads its own iteration, so it needs a
   position of its own, which the area's last mova in the kernel
   advances (am = 1) after the others have read it; IND is the offset
   in the step.  It starts where the kernel's first instance reads
   (stage U of iteration S - 1 - U): DISP from the descriptor's base,
   the address on the way in.  An area is named by its program
   instruction; each half's 2 KiB are shared by its areas.  As lcc
   reads adler32's 16 bytes an iteration: two areas, 8 bytes each.  */
static int
e2k_ms_apb_assign (e2k_ms_loop *l)
{
  int ii = l->ii, s = l->stages;
  for (int r = 0; r < ii; r++)
    {
      int ch = 0;
      for (int i = 0; i < l->n; i++)
	if (l->nodes[i].apb && l->nodes[i].time % ii == r)
	  l->nodes[i].apb_chan = ch++;
    }
  struct area
  {
    int d, size, stage, half, last, incr;
    HOST_WIDE_INT lo, hi, step;
  };
  auto_vec<area> areas;
  /* Movas by offset, so that a window takes the nearest.  */
  int order[E2K_MS_MAX_NODES], n = 0;
  HOST_WIDE_INT key[E2K_MS_MAX_NODES];
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].apb)
      {
	order[n++] = i;
	key[i] = l->nodes[i].apb_off;
      }
  for (int a = 1; a < n; a++)
    for (int b = a; b > 0 && key[order[b - 1]] > key[order[b]]; b--)
      std::swap (order[b - 1], order[b]);
  for (int k = 0; k < n; k++)
    {
      e2k_ms_node *node = &l->nodes[order[k]];
      int stage = node->time / ii, half = node->apb_chan >= 2;
      unsigned a = 0;
      for (; a < areas.length (); a++)
	if (areas[a].d == node->apb_d && areas[a].size == node->apb_size
	    && areas[a].stage == stage && areas[a].half == half
	    && areas[a].step == node->apb_step
	    && node->apb_off + node->apb_size - areas[a].lo <= 32)
	  break;
      if (a == areas.length ())
	{
	  area ar = { node->apb_d, node->apb_size, stage, half, order[k], 0,
		      node->apb_off, node->apb_off, node->apb_step };
	  areas.safe_push (ar);
	}
      area &ar = areas[a];
      ar.hi = MAX (ar.hi, node->apb_off + node->apb_size);
      if (node->time > l->nodes[ar.last].time)
	ar.last = order[k];
      node->apb_area = a;
      node->apb_ind = node->apb_off - ar.lo;
    }
  /* The left half must hold at least as many areas as the right: an
     instruction's left half describes one (and ends the program).  */
  int nh[2] = { 0, 0 };
  for (area &ar : areas)
    nh[ar.half]++;
  if (nh[1] > nh[0])
    {
      for (area &ar : areas)
	ar.half ^= 1;
      std::swap (nh[0], nh[1]);
      for (int k = 0; k < n; k++)
	l->nodes[order[k]].apb_chan ^= 2;
    }
  /* Areas in each half in order; increments.  */
  int idx[2] = { 0, 0 }, num[64];
  l->apb_nincr = 0;
  for (unsigned a = 0; a < areas.length (); a++)
    {
      area &ar = areas[a];
      num[a] = idx[ar.half]++;
      HOST_WIDE_INT e = ar.step / ar.size;
      if (e != 1)
	{
	  int k = 1;
	  while (k <= l->apb_nincr && l->apb_incr[k] != e)
	    k++;
	  if (k > l->apb_nincr)
	    l->apb_incr[++l->apb_nincr] = e;
	  ar.incr = k;
	}
    }
  gcc_assert (l->apb_nincr <= 7 && nh[0] <= 32);
  for (int k = 0; k < n; k++)
    {
      e2k_ms_node *node = &l->nodes[order[k]];
      node->apb_am = areas[node->apb_area].last == order[k];
      node->apb_area = num[node->apb_area];
    }
  auto asz = [] (int k)
    {
      int a = 5;
      while (a > 0 && (k << a) > 32)
	a--;
      return a;
    };
  int as[2] = { asz (nh[0]), asz (MAX (nh[1], 1)) };
  /* disp is 32 bits that lcc never makes negative (it starts its areas
     through %aaind): a descriptor with an area that would start below
     its base (one read backwards) gets a base that much lower.  */
  for (int d = 0; d < 32; d++)
    l->apb_adj[d] = 0;
  for (area &ar : areas)
    l->apb_adj[ar.d] = MIN (l->apb_adj[ar.d],
			    ar.lo + (s - 1 - ar.stage) * ar.step);
  int m = ++e2k_apb_labelno;
  char buf[16384];
  int len = snprintf (buf, sizeof buf, "\t.align\t8\n.LAPB%d:\n", m);
  auto entry = [&] (const area &ar, int last)
    {
      int fmt = (ar.size == 1 ? 1 : ar.size == 2 ? 2 : ar.size == 4 ? 3
		 : 4);
      HOST_WIDE_INT disp = (ar.lo + (s - 1 - ar.stage) * ar.step
			    - l->apb_adj[ar.d]);
      int a = as[ar.half];
      int mrng = ar.hi - ar.lo;
      len += snprintf (buf + len, sizeof buf - len,
		       "\t  fapb\t%s=%d, dcd=0, fmt=%d, mrng=%d, d=%d, incr=%d, "
		       "ind=0, asz=%d, abs=%d, disp=%d\n",
		       ar.half ? "dpl" : "ct", last, fmt, mrng == 32 ? 0 : mrng,
		       ar.d, ar.incr, a, num[&ar - areas.address ()] << a,
		       (int) disp);
    };
  for (int k = 0; k < nh[0]; k++)
    {
      len += snprintf (buf + len, sizeof buf - len, "\t{\n");
      for (area &ar : areas)
	if (ar.half == 0 && num[&ar - areas.address ()] == k)
	  entry (ar, k == nh[0] - 1);
      for (area &ar : areas)
	if (ar.half == 1 && num[&ar - areas.address ()] == k)
	  entry (ar, 0);
      len += snprintf (buf + len, sizeof buf - len, "\t}\n");
    }
  gcc_assert (len < (int) sizeof buf);
  e2k_apb_progs.safe_push (xstrdup (buf));
  return m;
}

/* The increment registers of L's AAU stores, after those of array
   prefetch (e2k_ms_apb_assign), and their descriptors' adjustments: the
   offset, so that the base is the element of iteration 0.  */
static void
e2k_ms_staa_assign (e2k_ms_loop *l)
{
  if (!l->napb)
    l->apb_nincr = 0;
  for (int i = 0; i < l->n; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      if (!node->staa)
	continue;
      HOST_WIDE_INT e = node->apb_step / node->apb_size;
      int k = 0;
      if (e != 1)
	{
	  k = 1;
	  while (k <= l->apb_nincr && l->apb_incr[k] != e)
	    k++;
	  if (k > l->apb_nincr)
	    l->apb_incr[++l->apb_nincr] = e;
	}
      node->staa_incr = k;
      l->apb_adj[node->apb_d] = node->apb_off;
    }
  gcc_assert (l->apb_nincr <= 7);
}

static bool
e2k_ms_emit (e2k_ms_loop *l, const vec<rtx_insn *> &pre_ends,
	     const vec<edge> &entries, edge exit_edge, const e2k_ms_wl *w)
{
  int ii = l->ii, s = l->stages;

  /* Prologue: the copies in and the first S - 1 stages of iterations
     0 .. S - 2, in the order the kernel would run them.  */
  auto_vec<e2k_ms_item> items;
  for (unsigned v = 0; v < l->values.length (); v++)
    for (int k = 1; k <= 2; k++)
      if (k == 1 ? l->values[v].carried : l->values[v].carried2)
	{
	  e2k_ms_item it = { -k * ii + l->nodes[l->values[v].node].time, -1,
			     -k, (int) v };
	  items.safe_push (it);
	}
  for (int j = 0; j < s - 1; j++)
    for (int i = 0; i < l->n; i++)
      if (l->nodes[i].time / ii < s - 1 - j)
	{
	  e2k_ms_item it = { j * ii + l->nodes[i].time, i, j, -1 };
	  items.safe_push (it);
	}
  items.stablesort (e2k_ms_item_cmp, NULL);
  int ni = items.length ();
  auto_vec<rtx> pats (ni);
  for (e2k_ms_item &it : items)
    {
      if (it.node < 0)
	{
	  const e2k_ms_value &v = l->values[it.value];
	  unsigned r = v.init[-it.j - 1];
	  gcc_assert (r != INVALID_REGNUM);
	  pats.quick_push (gen_rtx_SET (e2k_ms_reg (v.mode,
						    e2k_ms_name (l, it.value,
								 it.j, 0)),
					gen_rtx_REG (v.mode, r)));
	}
      else
	{
	  /* The prologue keeps an array prefetch node's load.  */
	  e2k_ms_node *nd = &l->nodes[it.node];
	  rtx_insn *keep = nd->insn;
	  if (nd->apb)
	    nd->insn = nd->orig;
	  pats.quick_push (e2k_ms_instance (l, it.node, it.j, 0));
	  nd->insn = keep;
	}
    }
  /* The kernel runs what one cycle holds at once, reading before
     writing; here one cycle's instructions run one after another, so
     an instruction that writes a name another one reads goes last.  */
  auto_vec<int> seq (ni);
  for (int g = 0; g < ni; )
    {
      int ge = g;
      while (ge < ni && items[ge].t == items[g].t)
	ge++;
      if (!e2k_ms_order_cycle (pats, g, ge, &seq))
	return false;
      g = ge;
    }

  /* Kernel: row by row; names in the frame of the current iteration,
     which runs stage U of iteration S - 1 - U.  The same order within a
     row, so that dataflow sees what the wide instruction does.  */
  int korder[E2K_MS_MAX_NODES], krow[E2K_MS_MAX_NODES], nk = 0;
  for (int i = 0; i < l->n; i++)
    {
      krow[i] = l->nodes[i].time % ii;
      if (!l->nodes[i].kdead)
	korder[nk++] = i;
    }
  e2k_ms_sort (korder, nk, krow);
  int apbno = l->napb ? e2k_ms_apb_assign (l) : 0;
  if (l->nstaa)
    e2k_ms_staa_assign (l);
  /* A failure from here on drops the program it queued.  */
  auto apb_fail = [&] ()
    {
      if (apbno)
	free (e2k_apb_progs.pop ());
      return false;
    };
  auto_vec<rtx> kpats (nk);
  for (int k = 0; k < nk; k++)
    {
      int i = korder[k];
      kpats.quick_push (e2k_ms_instance (l, i, s - 1 - l->nodes[i].time / ii,
					 0));
      e2k_ms_node *nd = &l->nodes[i];
      if (nd->apb)
	{
	  rtx u = SET_SRC (e2k_ms_set (kpats[k]));
	  XVECEXP (u, 0, 0) = GEN_INT (nd->apb_area);
	  XVECEXP (u, 0, 1) = GEN_INT (nd->apb_chan);
	  XVECEXP (u, 0, 3) = GEN_INT (nd->apb_ind);
	  XVECEXP (u, 0, 4) = GEN_INT (nd->apb_am);
	}
      if (nd->staa)
	{
	  rtx u = XEXP (SET_DEST (e2k_ms_set (kpats[k])), 0);
	  XVECEXP (u, 0, 0) = GEN_INT (nd->apb_d);
	  XVECEXP (u, 0, 1) = GEN_INT (nd->staa_sti);
	  XVECEXP (u, 0, 2) = GEN_INT (nd->apb_off - l->apb_adj[nd->apb_d]);
	  XVECEXP (u, 0, 3) = GEN_INT (nd->staa_incr);
	}
    }
  auto_vec<int> kseq (nk);
  for (int g = 0; g < nk; )
    {
      int ge = g;
      while (ge < nk && krow[korder[ge]] == krow[korder[g]])
	ge++;
      if (!e2k_ms_order_cycle (kpats, g, ge, &kseq))
	return apb_fail ();
      /* A check ends its wide instruction (and its block): last, after
	 what reads its register, and nothing after it may write what it
	 reads.  */
      for (int a = g; a < ge; a++)
	if (korder[kseq[a]] == l->kchk)
	  {
	    int kk = kseq[a];
	    for (int b = a; b + 1 < ge; b++)
	      {
		kseq[b] = kseq[b + 1];
		rtx db = SET_DEST (e2k_ms_set (kpats[kseq[b]]));
		if (REG_P (db) && e2k_ms_reads_p (kpats[kk], REGNO (db)))
		  return apb_fail ();
	      }
	    kseq[ge - 1] = kk;
	    break;
	  }
      g = ge;
    }

  /* What a failed check redoes: in time order, one time's instances as
     the kernel orders them.  */
  auto_vec<rtx> rpats (l->rec.length ());
  auto_vec<int> rseq (l->rec.length ());
  for (std::pair<int, int> &r : l->rec)
    rpats.quick_push (e2k_ms_instance (l, r.first, r.second, 0));
  for (unsigned g = 0; g < l->rec.length (); )
    {
      unsigned ge = g;
      auto t = [&] (unsigned x)
	{
	  return l->rec[x].second * ii + l->nodes[l->rec[x].first].time;
	};
      while (ge < l->rec.length () && t (ge) == t (g))
	ge++;
      if (!e2k_ms_order_cycle (rpats, g, ge, &rseq))
	return apb_fail ();
      g = ge;
    }

  /* The loop end's disp, if it was in the loop: each prologue starts
     with it.  */
  rtx ldisp = (w && w->bdisp ? copy_rtx (PATTERN (w->bdisp))
	       : l->edisp ? copy_rtx (PATTERN (l->edisp)) : NULL_RTX);
  auto emit_ldisp = [&] (rtx_insn *after)
    {
      rtx_insn *d = (after ? emit_insn_after (copy_rtx (ldisp), after)
		     : emit_insn (copy_rtx (ldisp)));
      rtx label = label_ref_label (XVECEXP (SET_SRC (ldisp), 0, 0));
      add_reg_note (d, REG_LABEL_OPERAND, label);
      LABEL_NUSES (label)++;
      if (recog_memoized (d) < 0)
	gcc_unreachable ();
      return d;
    };

  if (w)
    e2k_ms_wl_merge (l, w);

  /* Operations that print ",sm": all but stores, predicate logic, and
     lock and check loads (which print their own).  */
  auto spec_p = [&] (int i, bool kernel = false)
    {
      /* An array prefetch node: its load in the prologue, its mova
	 (which never traps) in the kernel.  */
      if (l->nodes[i].apb)
	return !kernel;
      enum attr_type t = get_attr_type (l->nodes[i].insn);
      return (!l->nodes[i].store && t != TYPE_PLOG && t != TYPE_LDLOCK
	      && t != TYPE_LDCHK);
    };

  /* The same prologue before each way into the loop.  */
  auto_vec<std::pair<rtx_insn *, int> > pro_insns;
  auto emit_prologue = [&] (bool copy)
    {
      emit_insn (e2k_ms_gen_setbn_enter (l));
      if (ldisp)
	emit_ldisp (NULL);
      for (int k : seq)
	{
	  rtx_insn *insn = emit_insn (copy ? copy_rtx (pats[k]) : pats[k]);
	  if (items[k].node >= 0)
	    {
	      INSN_LOCATION (insn)
		= INSN_LOCATION (l->nodes[items[k].node].insn);
	      if (spec_p (items[k].node))
		e2k_ms_set_flag (insn, E2K_MS_SM);
	      pro_insns.safe_push (std::make_pair (insn, items[k].node));
	    }
	  else
	    /* A copy in of a value the loop may leave with unchanged:
	       the register may hold a diagnostic value from a speculative
	       load that nothing reads on this way (xz's index_tree_next,
	       a register e2k_ms_move_b counts live at the first exit).  */
	    e2k_ms_set_flag (insn, E2K_MS_SM);
	  recog_memoized (insn);
	}
    };
  /* Better, a block of its own on each way in, with the cycles of the
     modulo schedule, which count the crossings between the clusters
     that sched-ebb doesn't; if each cycle holds what it gets, the
     copies in included.  setbn has a wide instruction of its own, and
     empty ones follow up to the kernel's first cycle if it comes
     next.  */
  int tmin = INT_MAX, tlast = INT_MIN;
  for (e2k_ms_item &it : items)
    {
      tmin = MIN (tmin, it.t);
      tlast = MAX (tlast, it.t);
    }
  bool clocked = ni > 0 && e2k_ms_clock_prologue;
  if (clocked)
    {
      state_t st = alloca (dfa_state_size);
      for (int g = 0; g < ni && clocked; )
	{
	  int ge = g;
	  state_reset (st);
	  for (; ge < ni && items[ge].t == items[g].t; ge++)
	    {
	      rtx_insn *x = (items[ge].node >= 0
			     ? (l->nodes[items[ge].node].apb
				? l->nodes[items[ge].node].orig
				: l->nodes[items[ge].node].insn)
			     : make_insn_raw (copy_rtx (pats[ge])));
	      if (recog_memoized (x) < 0 || state_transition (st, x) >= 0)
		clocked = false;
	    }
	  g = ge;
	}
    }
  int kstart = (s - 1) * ii;
  /* Where the clocked prologue's items go: their modulo times, or a
     list schedule of their own (e2k_ms_list_prologue) that starts the
     kernel PDELTA cycles sooner.  */
  auto_vec<int> pclock, oc, pseq;
  int pdelta = 0, plast = 1 + tlast - tmin + 1;
  for (int k = 0; k < ni; k++)
    oc.safe_push (items[k].t - tmin + 2);
  /* Only with v6 timing: on the 2C3 CoreMark ran 0.5% faster and
     zlib -9 0.6%, on the 8C2 zlib -9 1.1% slower (its loads cross
     between the clusters, which the prologue's channels don't model).  */
  bool listed = (clocked && e2k_ms_list_pro && E2K_LAT6
		 && e2k_ms_list_prologue (pats, seq, oc, &pclock, &plast));
  /* The kernel starts PDELTA cycles sooner: as soon as every value it
     reads from the prologue comes in time at the pipeliner's latencies
     (a copy in counts as its value's node).  What the prologue reads
     of the kernel's names it reads before the kernel runs.  */
  if (listed)
    {
      pdelta = INT_MAX;
      for (int k = 0; k < ni; k++)
	{
	  int i = (items[k].node >= 0 ? items[k].node
		   : l->values[items[k].value].node);
	  /* The kernel's channels keep a recurrence in one cluster
	     (e2k_ms_pipeline drops its crossing), the prologue's need
	     not: count the crossing on every edge into the kernel, as a
	     cycle late costs a 4-cycle stall.  */
	  enum attr_type pt = get_attr_type (l->nodes[i].insn);
	  int full = (pt == TYPE_FP || pt == TYPE_FMA || pt == TYPE_FFMA
		      || pt == TYPE_FCVT || pt == TYPE_MUL ? 2 : 1);
	  if (E2K_LAT6
	      && (pt == TYPE_LOAD || pt == TYPE_LDLOCK || pt == TYPE_LDCHK))
	    full = 0;
	  for (e2k_ms_dep &d : l->deps)
	    if (d.from == i)
	      {
		int jc = items[k].j + d.dist, tc = l->nodes[d.to].time;
		if (jc <= s - 2 && tc / ii < s - 1 - jc)
		  continue;
		int lat = d.lat - d.cross + full;
		pdelta = MIN (pdelta,
			      jc * ii + tc - tmin + 2 - lat - pclock[k]);
	      }
	}
      /* The kernel comes after the prologue's last cycle.  */
      pdelta = MIN (pdelta, (kstart - tmin + 2) - plast - 1);
    }
  if (!listed || pdelta <= 0)
    {
      pclock.truncate (0);
      for (int k = 0; k < ni; k++)
	pclock.safe_push (oc[k]);
      pdelta = 0;
      plast = 1 + tlast - tmin + 1;
    }
  for (int k : seq)
    pseq.safe_push (k);
  /* Emitted in clock order; within a cycle as SEQ has them.  */
  for (int a = 1; a < ni; a++)
    for (int b = a; b > 0 && pclock[pseq[b - 1]] > pclock[pseq[b]]; b--)
      std::swap (pseq[b - 1], pseq[b]);
  auto_vec<std::pair<basic_block, rtx_insn *> > pblocks;
  auto emit_clocked = [&] (edge e, bool copy)
    {
      basic_block p = e2k_ms_split_entry (e);
      p->flags |= BB_DISABLE_SCHEDULE;
      rtx_insn *x = BB_END (p);
      if (JUMP_P (x))
	x = PREV_INSN (x);
      x = emit_insn_after (e2k_ms_gen_setbn_enter (l), x);
      e2k_ms_clock c0 = { x, 1 };
      e2k_ms_clocks.safe_push (c0);
      /* With the first cycle: nothing else of a loop uses CS0.  */
      if (ldisp)
	{
	  x = emit_ldisp (x);
	  e2k_ms_clock cd = { x, 2 };
	  e2k_ms_clocks.safe_push (cd);
	}
      for (int k : pseq)
	{
	  x = emit_insn_after (copy ? copy_rtx (pats[k]) : pats[k], x);
	  if (items[k].node >= 0)
	    {
	      INSN_LOCATION (x) = INSN_LOCATION (l->nodes[items[k].node].insn);
	      if (spec_p (items[k].node))
		e2k_ms_set_flag (x, E2K_MS_SM);
	      pro_insns.safe_push (std::make_pair (x, items[k].node));
	    }
	  else
	    /* A copy in, as in emit_prologue.  */
	    e2k_ms_set_flag (x, E2K_MS_SM);
	  recog_memoized (x);
	  e2k_ms_clock c = { x, pclock[k] };
	  e2k_ms_clocks.safe_push (c);
	}
      pblocks.safe_push (std::make_pair (p, x));
      return plast;
    };
  /* Array prefetch: on each way in, after rwd %lsr (the unit follows
     the count after a trap), each descriptor's base, the address there
     (an area's DISP adds the rest), and the increments; the program
     into %ctpr2; bap.  The prologue's cycles count towards the 22 a
     first mova would wait.  */
  auto_vec<basic_block> apb_pre;
  for (rtx_insn *pre_end : pre_ends)
    apb_pre.safe_push (BLOCK_FOR_INSN (pre_end));
  /* A descriptor's base is its induction variable, written as it is, or
     that plus an invariant or an adjustment (apb_adj), which goes
     through the temporary; so does each increment.  The AAU writes are
     barriers to the scheduler: when the temporary takes one value, set
     it before the first of them.  */
  rtx t = gen_rtx_REG (DImode, l->apb_tmp);
  /* AAU stores' descriptors follow array prefetch's; their store
     indices start at 0, which goes through the temporary too.  */
  int ndesc = l->napb_d + l->nstaa_d;
  auto aau_p = [&] (int i) { return l->nodes[i].apb || l->nodes[i].staa; };
  int ntmp = l->apb_nincr + (l->nstaa > 0), d_tmp = -1;
  for (int d = 0; d < ndesc; d++)
    for (int i = 0; i < l->n; i++)
      if (aau_p (i) && l->nodes[i].apb_d == d)
	{
	  if (l->nodes[i].apb_inv != INVALID_REGNUM || l->apb_adj[d])
	    ntmp++, d_tmp = i;
	  break;
	}
  bool early = ntmp == 1;
  /* The base of NODE's descriptor into the temporary.  */
  auto apb_base = [&] (e2k_ms_node *node)
      {
	rtx iv = gen_rtx_REG (DImode, node->apb_iv);
	HOST_WIDE_INT adj = l->apb_adj[node->apb_d];
	if (node->apb_inv != INVALID_REGNUM)
	  {
	    emit_insn (gen_adddi3 (t, iv,
				   gen_rtx_REG (DImode, node->apb_inv)));
	    if (adj)
	      emit_insn (gen_adddi3 (t, t, gen_int_mode (adj, DImode)));
	  }
	else
	  emit_insn (gen_adddi3 (t, iv, gen_int_mode (adj, DImode)));
      };
  /* The temporary's one value.  */
  auto apb_early = [&] ()
      {
	start_sequence ();
	if (d_tmp >= 0)
	  apb_base (&l->nodes[d_tmp]);
	else if (l->apb_nincr)
	  emit_move_insn (t, gen_int_mode (l->apb_incr[1], DImode));
	else
	  emit_move_insn (t, const0_rtx);
	return end_sequence ();
      };
  /* The setup, with ldisp if LDISP, after the temporary's value if
     SET_EARLY.  */
  auto apb_seq = [&] (bool ldisp, bool set_early)
      {
	rtx_insn *pre = early && set_early ? apb_early () : NULL;
	start_sequence ();
	if (pre)
	  emit_insn (pre);
	for (int d = 0; d < ndesc; d++)
	  for (int i = 0; i < l->n; i++)
	    if (aau_p (i) && l->nodes[i].apb_d == d)
	      {
		e2k_ms_node *node = &l->nodes[i];
		rtx iv = gen_rtx_REG (DImode, node->apb_iv);
		if (node->apb_inv == INVALID_REGNUM && !l->apb_adj[d])
		  emit_insn (gen_e2k_aaurwd (iv, GEN_INT (d)));
		else
		  {
		    if (!early)
		      apb_base (node);
		    emit_insn (gen_e2k_aaurwd (t, GEN_INT (d)));
		  }
		break;
	      }
	for (int k = 1; k <= l->apb_nincr; k++)
	  {
	    if (!early)
	      emit_move_insn (t, gen_int_mode (l->apb_incr[k], DImode));
	    emit_insn (gen_e2k_aaurw_incr (t, GEN_INT (k)));
	  }
	if (l->nstaa)
	  {
	    if (!early)
	      emit_move_insn (t, const0_rtx);
	    for (int k = 0; k < l->nstaa; k++)
	      emit_insn (gen_e2k_aaurw_sti (t, GEN_INT (k)));
	  }
	if (l->napb)
	  {
	    if (ldisp)
	      emit_insn (gen_e2k_ldisp_apb (GEN_INT (apbno)));
	    emit_insn (gen_e2k_bap ());
	  }
	rtx_insn *seq = end_sequence ();
	for (rtx_insn *x = seq; x; x = NEXT_INSN (x))
	  if (recog_memoized (x) < 0)
	    gcc_unreachable ();
	return seq;
      };
  auto apb_setup = [&] (edge e)
      {
	/* In a block of its own on the way in: the block of rwd %lsr may
	   end in a branch through %ctpr2.  */
	basic_block q = split_edge (e);
	emit_insn_after (apb_seq (true, true), BB_END (q));
      };
  /* %b[] invariants into their registers before setbn renames %b[].  */
  for (int k = 0; k < 8; k++)
    if (l->binv & (1u << k))
      for (rtx_insn *pre_end : pre_ends)
	recog_memoized (emit_insn_before
			(gen_rtx_SET (gen_rtx_REG (DImode, l->bmap[k]),
				      gen_rtx_REG (DImode, B0_REGNUM + k)),
			 pre_end));
  for (unsigned p = 0; p < pre_ends.length (); p++)
    if (clocked)
      {
	rtx_insn *pre_end = pre_ends[p];
	basic_block pb = BLOCK_FOR_INSN (pre_end);
	int cycles = emit_clocked (find_edge (pb, l->bb), p > 0);
	/* The prologue gives %lsr its 4 cycles after rwd.  */
	if (cycles >= 4 && single_succ_p (pb))
	  delete_insn (pre_end);
      }
    else
      {
	start_sequence ();
	emit_prologue (p > 0);
	rtx_insn *pro = end_sequence ();
	emit_insn_before (pro, pre_ends[p]);
      }
  for (unsigned p = 0; p < entries.length (); p++)
    if (clocked)
      emit_clocked (entries[p], p > 0 || pre_ends.length () > 0);
    else
      {
	start_sequence ();
	emit_prologue (p > 0 || pre_ends.length () > 0);
	rtx_insn *pro = end_sequence ();
	edge e = entries[p];
	if (!(e->flags & EDGE_FALLTHRU) && !single_succ_p (e->src))
	  {
	    basic_block nb = e2k_ms_split_entry (e);
	    emit_insn_after (pro, BB_END (nb));
	  }
	else
	  insert_insn_on_edge (pro, e);
      }
  /* The array prefetch setup on each way in: between the block of rwd
     %lsr and the prologue (or the loop).  A prologue in that block
     itself (not clocked) would then run before bap, and the kernel's
     first movas wait out bap's 22 cycles (Linpack's daxpy, about 20
     cycles a call): there right after rwd %lsr, unless something after
     it uses %ctpr2, which ldisp sets.  */
  if (l->napb || l->nstaa)
    for (basic_block pb : apb_pre)
      {
	rtx_insn *rwd = NULL;
	if (!clocked)
	  {
	    rtx ctpr2 = gen_rtx_REG (DImode, CTPR2_REGNUM);
	    for (rtx_insn *x = BB_END (pb); x != PREV_INSN (BB_HEAD (pb));
		 x = PREV_INSN (x))
	      if (NONDEBUG_INSN_P (x))
		{
		  if (recog_memoized (x) == CODE_FOR_e2k_rwd_lsr)
		    {
		      rwd = x;
		      break;
		    }
		  if (CALL_P (x) || reg_mentioned_p (ctpr2, PATTERN (x))
		      || reg_set_p (ctpr2, x))
		    break;
		}
	  }
	if (rwd)
	  {
	    /* ldisp at the block's head, where it has the count's chain
	       to cover its 5 cycles to bap, if nothing before rwd uses
	       %ctpr2 or calls.  */
	    rtx ctpr2 = gen_rtx_REG (DImode, CTPR2_REGNUM);
	    bool head = l->napb > 0;
	    for (rtx_insn *x = BB_HEAD (pb); x != rwd; x = NEXT_INSN (x))
	      if (NONDEBUG_INSN_P (x)
		  && (CALL_P (x) || reg_mentioned_p (ctpr2, PATTERN (x))
		      || reg_set_p (ctpr2, x)))
		head = false;
	    if (head)
	      emit_insn_after (gen_e2k_ldisp_apb (GEN_INT (apbno)),
			       bb_note (pb));
	    /* After the copies e2k_ms_move_b put after rwd into registers
	       the setup reads (NPB SP: a %b[] invariant moved into the
	       register that had held the count).  */
	    rtx_insn *after = rwd;
	    for (rtx_insn *x = NEXT_INSN (rwd); x != NEXT_INSN (BB_END (pb));
		 x = NEXT_INSN (x))
	      if (NONDEBUG_INSN_P (x))
		for (int i = 0; i < l->n; i++)
		  if (aau_p (i)
		      && (reg_set_p (gen_rtx_REG (DImode, l->nodes[i].apb_iv), x)
			  || (l->nodes[i].apb_inv != INVALID_REGNUM
			      && reg_set_p (gen_rtx_REG (DImode,
							 l->nodes[i].apb_inv),
					    x))))
		    {
		      after = x;
		      break;
		    }
	    /* rwd is a barrier too: set the temporary before it, unless
	       it is the register rwd reads (e2k_ms_apb_ok may take one
	       the loop's way in uses), or its value comes after.  */
	    bool before = (early && after == rwd
			   && !reg_overlap_mentioned_p (t, PATTERN (rwd)));
	    if (before)
	      emit_insn_before (apb_early (), rwd);
	    emit_insn_after (apb_seq (!head, !before), after);
	    continue;
	  }
	edge e, way = NULL;
	edge_iterator ei;
	FOR_EACH_EDGE (e, ei, pb->succs)
	  {
	    if (e->dest == l->bb)
	      way = e;
	    for (std::pair<basic_block, rtx_insn *> &b : pblocks)
	      if (e->dest == b.first)
		way = e;
	  }
	gcc_assert (way);
	apb_setup (way);
      }
  /* The prologue that falls into the kernel waits for its first cycle;
     the others jump there through the CTPR the loop end uses, which
     holds the kernel's address already (an ibranch costs 6 cycles).  */
  rtx lctpr = NULL_RTX;
  {
    subrtx_iterator::array_type array;
    FOR_EACH_SUBRTX (iter, array, PATTERN (l->jump), NONCONST)
      if (REG_P (*iter) && CTPR_REGNO_P (REGNO (*iter)))
	lctpr = const_cast<rtx> (*iter);
  }
  for (std::pair<basic_block, rtx_insn *> &pb : pblocks)
    {
      basic_block p = pb.first;
      rtx_insn *end = BB_END (p);
      if (!JUMP_P (end))
	{
	  int gap = (kstart - tmin + 2 - pdelta) - plast - 1;
	  if (gap > 0)
	    emit_insn_after (gen_e2k_nop_bundle (GEN_INT (MIN (gap, 8) - 1)),
			     pb.second);
	}
      else if (lctpr && simplejump_p (end))
	{
	  rtx label = JUMP_LABEL (end);
	  PATTERN (end)
	    = gen_rtx_PARALLEL (VOIDmode,
				gen_rtvec (2, gen_rtx_SET (pc_rtx,
							   gen_rtx_LABEL_REF
							   (Pmode, label)),
					   gen_rtx_USE (VOIDmode, lctpr)));
	  INSN_CODE (end) = -1;
	  if (recog_memoized (end) < 0)
	    gcc_unreachable ();
	  df_insn_rescan (end);
	}
    }

  /* Empty first cycles of the kernel are an empty wide instruction.  */
  int row0 = ii;
  for (int i = 0; i < l->n; i++)
    if (!l->nodes[i].kdead)
      row0 = MIN (row0, l->nodes[i].time % ii);
  /* The loop end may read its predicate in the wide instruction that
     sets it for the next iteration: tell dataflow it comes in.  */
  if (l->wl && l->npred)
    {
      /* The loop end reads the stay predicate of the iteration whose
	 last stage this is, under its name now; dataflow doesn't know
	 the ring rotates (uses of all of it at the loop end, below).  */
      rtx cond = e2k_ms_jump_cond (l->jump);
      XEXP (cond, 0) = gen_rtx_REG (BImode,
				    PRED0_REGNUM + e2k_ms_pname (l, l->stay,
								 0, 0));
      INSN_CODE (l->jump) = -1;
      if (recog_memoized (l->jump) < 0)
	gcc_unreachable ();
      df_insn_rescan (l->jump);
    }
  else if (l->wl)
    emit_insn_before (gen_rtx_USE (VOIDmode,
				   SET_DEST (PATTERN (l->nodes[l->stay].insn))),
		      l->jump);
  if (row0 > 0)
    emit_insn_before (gen_e2k_nop_bundle (GEN_INT (row0 - 1)), l->jump);
  rtx_code_label *rlabel = l->kchk >= 0 ? gen_label_rtx () : NULL;
  rtx_insn *kinsn = NULL;
  rtx_insn *kins[E2K_MS_MAX_NODES];
  for (int k : kseq)
    {
      int i = korder[k];
      rtx_insn *insn;
      if (i == l->kchk)
	{
	  /* The check, with its rbranch to the compensation code.  */
	  rtx br = gen_rtx_SET (pc_rtx,
				gen_rtx_IF_THEN_ELSE
				(VOIDmode,
				 gen_rtx_NE (VOIDmode,
					     gen_rtx_UNSPEC (VOIDmode,
							     gen_rtvec (1, const0_rtx),
							     UNSPEC_MLOCK),
					     const0_rtx),
				 gen_rtx_LABEL_REF (Pmode, rlabel), pc_rtx));
	  insn = emit_jump_insn_before (gen_rtx_PARALLEL
					(VOIDmode,
					 gen_rtvec (2, e2k_ms_set (kpats[k]), br)),
					l->jump);
	  JUMP_LABEL (insn) = rlabel;
	  LABEL_NUSES (rlabel)++;
	  kinsn = insn;
	}
      else
	insn = emit_insn_before (kpats[k], l->jump);
      INSN_LOCATION (insn) = INSN_LOCATION (l->nodes[i].insn);
      if (recog_memoized (insn) < 0)
	gcc_unreachable ();
      if (spec_p (i, true))
	e2k_ms_set_flag (insn, E2K_MS_SM);
      e2k_ms_clock c = { insn, l->nodes[i].time % ii + 1 };
      e2k_ms_clocks.safe_push (c);
      kins[i] = insn;
    }
  for (std::pair<rtx_insn *, int> &pi : pro_insns)
    {
      if (l->nodes[pi.second].kdead)
	continue;
      unsigned uid = INSN_UID (pi.first);
      if (uid >= e2k_ms_twin.length ())
	e2k_ms_twin.safe_grow_cleared (uid + 64);
      e2k_ms_twin[uid] = INSN_UID (kins[pi.second]);
    }
  /* Dataflow doesn't know that the old %b[N] is the new %b[N + 2]: to
     it, the values the next iteration reads under another name are
     dead (and the prologue's too).  Use every name at the loop end.  */
  for (int name = 0; name < 2 * l->pairs; name++)
    emit_insn_before (gen_rtx_USE (VOIDmode, e2k_ms_reg (DImode, name)),
		      l->jump);
  for (int name = 0; name < l->npred; name++)
    emit_insn_before (gen_rtx_USE (VOIDmode,
				   gen_rtx_REG (BImode, PRED0_REGNUM + name)),
		      l->jump);
  e2k_ms_clock c = { l->jump, ii };
  e2k_ms_clocks.safe_push (c);
  e2k_ms_set_flag (l->jump, E2K_MS_ABN | (l->npred ? E2K_MS_ABP : 0));
  for (rtx_insn *insn : l->insns)
    delete_insn (insn);
  if (l->edisp)
    delete_insn (l->edisp);
  rtx_insn *insn, *next;
  for (insn = BB_HEAD (l->bb); insn != NEXT_INSN (BB_END (l->bb));
       insn = next)
    {
      next = NEXT_INSN (insn);
      if (DEBUG_INSN_P (insn))
	delete_insn (insn);
    }
  l->bb->flags |= BB_DISABLE_SCHEDULE;
  if (!kinsn)
    {
      e2k_ms_kernels.safe_push (std::make_pair (l->bb->index, -1));
      e2k_ms_kernel_rings.safe_push (2 * l->pairs);
    }

  if (kinsn)
    {
      /* The check ends a block of the kernel; the compensation code,
	 at the end of the function, jumps back to the rest.  */
      basic_block k1 = l->bb;
      basic_block k2 = split_block (k1, kinsn)->dest;
      k2->flags |= BB_DISABLE_SCHEDULE;
      e2k_ms_kernels.safe_push (std::make_pair (k1->index, k2->index));
      e2k_ms_kernel_rings.safe_push (2 * l->pairs);
      rtx_code_label *k2label = block_label (k2);
      /* Empty rows between the check and the next instruction.  */
      int krow0 = l->nodes[l->kchk].time % ii, first = ii - 1;
      for (int i = 0; i < l->n; i++)
	if (l->nodes[i].time % ii > krow0)
	  first = MIN (first, l->nodes[i].time % ii);
      if (first > krow0 + 1)
	emit_insn_after (gen_e2k_nop_bundle (GEN_INT (first - krow0 - 2)),
			 NEXT_INSN (BB_HEAD (k2)));
      /* As at the kernel's start, the loop end's predicate comes in
	 (from the compensation code too).  */
      if (l->wl)
	emit_insn_after (gen_rtx_USE (VOIDmode,
				      SET_DEST (PATTERN (l->nodes[l->stay].insn))),
			 NEXT_INSN (BB_HEAD (k2)));
      rtx_insn *last = get_last_insn ();
      if (!BARRIER_P (last))
	last = emit_barrier_after (last);
      rtx_insn *head = emit_label_after (rlabel, last);
      rtx_insn *cur = head;
      for (unsigned q : rseq)
	{
	  int n = l->rec[q].first;
	  cur = emit_insn_after (rpats[q], cur);
	  INSN_LOCATION (cur) = INSN_LOCATION (l->nodes[n].insn);
	  if (recog_memoized (cur) < 0)
	    gcc_unreachable ();
	  if (spec_p (n))
	    e2k_ms_set_flag (cur, E2K_MS_SM);
	}
      rtx_insn *j = emit_jump_insn_after (gen_jump (k2label), cur);
      JUMP_LABEL (j) = k2label;
      LABEL_NUSES (k2label)++;
      emit_barrier_after (j);
      basic_block r
	= create_basic_block (head, j, EXIT_BLOCK_PTR_FOR_FN (cfun)->prev_bb);
      r->count = profile_count::zero ();
      make_edge (k1, r, 0)->probability = profile_probability::never ();
      make_edge (r, k2, 0);
    }

  /* After the loop: the last iteration's values, then the outgoing
     registers back.  The kernel ran n times, so a value defined in
     stage D of iteration n - 1 has rotated S - D times since.  A
     two-block while loop's values at the end of its second block may be
     diagnostic when its first block's exit was taken (copied with ,sm);
     its first block's exit compare runs again and its values there are
     copied over them under its condition.  */
  /* Every copy out is speculative: what it copies may be a diagnostic
     value nothing reads after this exit (a value copied in that the
     loop left unchanged, xz's index_tree_next).  */
  auto copy_out = [&] (e2k_ms_out &o)
    {
      machine_mode m = o.mode;
      rtx_insn *cp
	= emit_insn (gen_rtx_SET (gen_rtx_REG (m, o.regno),
				  e2k_ms_reg (m, e2k_ms_exit_name (l, o.value,
								   o.dist))));
      e2k_ms_set_flag (cp, E2K_MS_SM);
      return cp;
    };
  if (l->x1)
    {
      /* The exits go to different places: run the first block's exit
	 test again and branch, each way with its own copies.  */
      gcc_assert (!exit_edge->insns.r);
      basic_block x2 = exit_edge->dest;
      basic_block d = split_edge (exit_edge);
      rtx_insn *cmp = e2k_ms_emit_exit_test (l, BB_END (d));
      rtx label = block_label (l->x1);
      rtx cond = gen_rtx_fmt_ee (l->e1, VOIDmode, w->p1, const0_rtx);
      rtx_insn *j
	= emit_jump_insn_after (gen_rtx_SET (pc_rtx,
					     gen_rtx_IF_THEN_ELSE
					     (VOIDmode, cond,
					      gen_rtx_LABEL_REF (Pmode, label),
					      pc_rtx)), cmp);
      JUMP_LABEL (j) = label;
      LABEL_NUSES (label)++;
      if (recog_memoized (cmp) < 0 || recog_memoized (j) < 0)
	gcc_unreachable ();
      edge e2 = single_succ_edge (d);
      edge e1 = make_edge (d, l->x1, 0);
      e1->probability = profile_probability::even ();
      e2->probability = profile_probability::even ();
      for (int way = 1; way <= 2; way++)
	{
	  start_sequence ();
	  for (e2k_ms_out &o : l->outs)
	    if (o.hend == (way == 1))
	      copy_out (o);
	  emit_insn (gen_e2k_setbn_leave ());
	  rtx_insn *seq = end_sequence ();
	  for (rtx_insn *x = seq; x; x = NEXT_INSN (x))
	    if (recog_memoized (x) < 0)
	      gcc_unreachable ();
	  insert_insn_on_edge (seq, way == 1 ? e1 : find_edge (d, x2));
	}
      return true;
    }
  start_sequence ();
  /* The end of the array prefetch program, as lcc ends one.  */
  if (l->napb)
    {
      /* aaurw takes a register (gas); the setup's is dead here too.  */
      rtx t = gen_rtx_REG (DImode, l->apb_tmp);
      emit_move_insn (t, const0_rtx);
      emit_insn (gen_e2k_apb_stop ());
      emit_insn (gen_e2k_aabf (t));
    }
  for (e2k_ms_out &o : l->outs)
    if (!o.hend)
      copy_out (o);
  if (w)
    {
      bool any = false;
      for (e2k_ms_out &o : l->outs)
	any |= o.hend;
      if (any)
	{
	  e2k_ms_emit_exit_test (l, NULL);
	  for (e2k_ms_out &o : l->outs)
	    if (o.hend)
	      {
		machine_mode m = e2k_ms_copy_mode (o.mode);
		rtx cond = gen_rtx_fmt_ee (l->e1, VOIDmode, w->p1, const0_rtx);
		rtx set
		  = gen_rtx_SET (gen_rtx_REG (m, o.regno),
				 e2k_ms_reg (m, e2k_ms_exit_name (l, o.value,
								  o.dist)));
		e2k_ms_set_flag (emit_insn (gen_rtx_COND_EXEC (VOIDmode, cond,
							       set)),
				 E2K_MS_SM);
	      }
	}
    }
  emit_insn (gen_e2k_setbn_leave ());
  rtx_insn *after = end_sequence ();
  for (insn = after; insn; insn = NEXT_INSN (insn))
    if (recog_memoized (insn) < 0)
      gcc_unreachable ();
  /* Before what e2k_ms_move_b put on the edge.  */
  rtx_insn *old = exit_edge->insns.r;
  exit_edge->insns.r = NULL;
  insert_insn_on_edge (after, exit_edge);
  if (old)
    insert_insn_on_edge (old, exit_edge);
  return true;
}

static bool e2k_ms_fail (basic_block, const char *);

/* Stores run in the last stage only (never in the prologue), long after
   the step of the register their address is in: that register's value
   then lives through every stage, a name of the ring for each cycle in
   II.  Let a store read instead the instance of the latest iteration
   whose step it may, with its offset that many steps lower, and that
   value lives a stage.  Linpack's unrolled daxpy (v5, II 2): eleven
   names fewer, II 3 -> 2.  Only when the ring is too big without it:
   in the generic v3 daxpy, whose ring fits anyway, the same addresses
   at the same times ran 28% slower on the 8C2 (4.8 -> 6.1 cycles an
   iteration, cause unknown).  UNDO puts the uses back for another II.
   Not with a lock load, whose check's plan follows uses
   (e2k_ms_dam_plan).  */
static void
e2k_ms_rebase_stores (e2k_ms_loop *l, bool undo)
{
  for (int i = 0; i < l->n; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      if (undo)
	{
	  if (node->rebase_off)
	    node->uses[node->rebase_use].dist = node->rebase_dist0;
	  node->rebase_off = 0;
	  continue;
	}
      if (!node->store || l->kchk >= 0 || GET_CODE (PATTERN (node->insn)) != SET)
	continue;
      rtx set = PATTERN (node->insn), addr = XEXP (SET_DEST (set), 0);
      rtx base = GET_CODE (addr) == PLUS ? XEXP (addr, 0) : addr;
      if (!REG_P (base)
	  || (GET_CODE (addr) == PLUS && !CONST_INT_P (XEXP (addr, 1)))
	  || reg_mentioned_p (base, SET_SRC (set)))
	continue;
      int k = 0;
      while (k < node->nuses
	     && (node->uses[k].regno != REGNO (base) || node->uses[k].pred))
	k++;
      if (k == node->nuses || node->uses[k].value < 0)
	continue;
      int v = node->uses[k].value, dn = l->values[v].node;
      e2k_ms_node *def = &l->nodes[dn];
      rtx dset = single_set (def->insn);
      /* An induction step: r = r + C, reading nothing else of the loop.  */
      if (!dset || dset != PATTERN (def->insn) || !REG_P (SET_DEST (dset))
	  || REGNO (SET_DEST (dset)) != REGNO (base)
	  || GET_CODE (SET_SRC (dset)) != PLUS
	  || !rtx_equal_p (XEXP (SET_SRC (dset), 0), SET_DEST (dset))
	  || !CONST_INT_P (XEXP (SET_SRC (dset), 1)))
	continue;
      bool own = true;
      for (int u = 0; u < def->nuses; u++)
	if (def->uses[u].pred
	    || (def->uses[u].value >= 0 && def->uses[u].value != v))
	  own = false;
      if (!own)
	continue;
      int lat = 1;
      for (e2k_ms_dep &d : l->deps)
	if (d.from == dn && d.to == i)
	  lat = MAX (lat, d.lat);
      /* Iteration n's store at T + n II may read the instance of
	 iteration n + A, stepped at TD + (n + A) II + LAT.  */
      int a = (node->time - def->time - lat) / l->ii;
      int d0 = node->uses[k].dist, adv = d0 + a;
      if (node->time - def->time - lat < 0 || adv <= 0)
	continue;
      HOST_WIDE_INT off = adv * INTVAL (XEXP (SET_SRC (dset), 1));
      if (off == 0)
	continue;
      /* Not for a literal more.  */
      rtx nm = adjust_address_nv (SET_DEST (set), GET_MODE (SET_DEST (set)),
				  -off);
      rtx_insn *ni = make_insn_raw (gen_rtx_SET (nm, SET_SRC (set)));
      if (recog_memoized (ni) < 0
	  || e2k_insn_lits (ni) > e2k_insn_lits (node->insn))
	continue;
      node->rebase_use = k;
      node->rebase_dist0 = d0;
      node->rebase_off = off;
      node->uses[k].dist = -a;
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: store %d reads its address "
		 "%d iterations on, offset %d\n", INSN_UID (node->insn), adv,
		 (int) -off);
    }
}

/* Whether the function refers to a declared object of at least
   E2K_APB_BIG bytes (the streams of its pipelined loops then likely come
   from memory, even those of short loops: NPB SP's 34-iteration loops
   over 2 MB arrays, 25.8 -> 24.4 s on the 8C2 with array prefetch, where
   short ones over data that stays in the caches pay its setup for
   nothing: Linpack's 320 KB matrix, 2.7% slower).  The loops' own
   addresses no longer name their arrays after ivopts.  */
#define E2K_APB_BIG (1 << 20)
static bool
e2k_ms_apb_big_p (void)
{
  machine_function *m = cfun->machine;
  if (m->apb_big < 0)
    {
      m->apb_big = 0;
      for (rtx_insn *insn = get_insns (); insn && !m->apb_big;
	   insn = NEXT_INSN (insn))
	if (NONDEBUG_INSN_P (insn))
	  {
	    subrtx_iterator::array_type array;
	    FOR_EACH_SUBRTX (iter, array, PATTERN (insn), ALL)
	      {
		tree d = NULL_TREE;
		if (GET_CODE (*iter) == SYMBOL_REF)
		  d = SYMBOL_REF_DECL (*iter);
		else if (MEM_P (*iter) && MEM_EXPR (*iter))
		  d = get_base_address (MEM_EXPR (*iter));
		if (d && VAR_P (d) && DECL_SIZE_UNIT (d)
		    && tree_fits_uhwi_p (DECL_SIZE_UNIT (d))
		    && tree_to_uhwi (DECL_SIZE_UNIT (d)) >= E2K_APB_BIG)
		  {
		    m->apb_big = 1;
		    break;
		  }
	      }
	  }
    }
  return m->apb_big;
}

/* Whether L is known to run at least E2K_MS_LONG iterations: by the
   profile, else by the count the doloop pass knew.  */
static bool
e2k_ms_long_p (e2k_ms_loop *l)
{
  basic_block bb = l->bb;
  profile_count entry = profile_count::zero ();
  edge e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, bb->preds)
    if (e->src != bb)
      entry += e->count ();
  if (bb->count.reliable_p () && entry.reliable_p () && entry.nonzero_p ())
    return (bb->count.to_gcov_type () / MAX (entry.to_gcov_type (), 1)
	    >= E2K_MS_LONG);
  return e2k_loop_exact_iters (l->jump) >= E2K_MS_LONG;
}

/* When set, e2k_ms_pipeline only finds the II, stores it here and emits
   nothing (e2k_ms_try).  */
static int *e2k_ms_probe_ii;

/* Schedule and emit the analyzed loop L (e2k_ms_emit has the other
   arguments).  */
static bool
e2k_ms_pipeline (e2k_ms_loop *l, const vec<rtx_insn *> &pre_ends,
		 const vec<edge> &entries, edge exit_edge, const e2k_ms_wl *w)
{
  basic_block bb = l->bb;
  /* The dependences given far loads' latency, and what they had.  */
  auto_vec<std::pair<unsigned, int> > far;
  /* In a recurrence the crossing would set II (adler32's 16 chained
     adds: 34 cycles instead of 16); e2k_assign_channels keeps such a
     chain in one cluster when it can (each operation goes where its
     operands cost no stall).  */
  {
    sbitmap *reach = sbitmap_vector_alloc (l->n, l->n);
    bitmap_vector_clear (reach, l->n);
    for (e2k_ms_dep &d : l->deps)
      bitmap_set_bit (reach[d.from], d.to);
    for (int k = 0; k < l->n; k++)
      for (int i = 0; i < l->n; i++)
	if (bitmap_bit_p (reach[i], k))
	  bitmap_ior (reach[i], reach[i], reach[k]);
    for (e2k_ms_dep &d : l->deps)
      if (d.cross && bitmap_bit_p (reach[d.to], d.from))
	{
	  d.lat -= d.cross;
	  d.cross = 0;
	}
    /* A load the array prefetch unit doesn't serve, and that no
       recurrence goes through, read E2K_MS_LOAD_FAR cycles on: so that
       the misses of several iterations are in flight at once, as lcc's
       kernels have them (its v3 mvt reads a column 22 iterations
       ahead; scheduled for L1, each miss stalls the whole kernel: 278
       cycles an element against lcc's 45 on the 4C).  Only in a loop
       known to run long, or bounded (the doloop pass's bound, from the
       loops around it or its arrays' types) somewhere between that and
       a million: the stages cost every way in, which short loops over
       data in L1 pay for nothing (CoreMark's matrix loops, bounded only
       by their counter's type, 50% slower; CoreMark 18%, xz -c 28%,
       with every pipelined loop's loads far), while PolyBench's
       triangular loops run up to N.  */
    HOST_WIDE_INT bound = e2k_loop_max_iters (l->jump);
    if (e2k_ms_load_far > 0
	&& (e2k_ms_long_p (l)
	    || (bound >= E2K_MS_LONG && bound <= (1 << 20))))
      for (e2k_ms_dep &d : l->deps)
	{
	  e2k_ms_node *ld = &l->nodes[d.from];
	  if (ld->store || !ld->mem || ld->apb || ld->lock || ld->chk >= 0
	      || ld->value < 0 || bitmap_bit_p (reach[d.from], d.from)
	      || get_attr_type (ld->insn) != TYPE_LOAD)
	    continue;
	  bool reads = false;
	  for (int k = 0; k < l->nodes[d.to].nuses; k++)
	    if (!l->nodes[d.to].uses[k].pred
		&& l->nodes[d.to].uses[k].value == ld->value)
	      reads = true;
	  if (reads && d.lat < (int) e2k_ms_load_far)
	    far.safe_push (std::make_pair ((unsigned) (&d - l->deps.address ()),
					   d.lat));
	}
    sbitmap_vector_free (reach);
  }
  int far_lat = e2k_ms_load_far;
  auto set_far = [&] (bool on)
    {
      for (auto &f : far)
	l->deps[f.first].lat = on ? MAX (far_lat, f.second) : f.second;
    };
  /* Half as far, or not at all below 8 cycles.  */
  auto nearer = [&] ()
    {
      far_lat /= 2;
      set_far (far_lat >= 8);
      if (far_lat < 8)
	far.truncate (0);
    };
  /* Lower bounds: operations per cycle, then the length of one
     iteration when not pipelined.  */
  int loads = 0, stores = 0, alu = 0, c03 = 0, c14 = 0, c0134 = 0, divs = 0;
  int kalu = 0;
  for (int i = 0; i < l->n; i++)
    {
      /* landp runs in the PLS, a mova in an AAS channel, not in an ALU
	 channel.  */
      enum attr_type t = get_attr_type (l->nodes[i].insn);
      /* Not in the kernel (e2k_ms_mark_kdead).  */
      if (l->nodes[i].kdead)
	{
	  kalu += t != TYPE_PLOG && t != TYPE_MOVA;
	  continue;
	}
      loads += !l->nodes[i].store && l->nodes[i].mem && !l->nodes[i].apb;
      stores += l->nodes[i].store;
      divs += t == TYPE_FDIV;
      alu += t != TYPE_PLOG && t != TYPE_MOVA;
      /* Packed operations, two or four channels.  */
      c03 += t == TYPE_PINT;
      c14 += t == TYPE_PINT14 || t == TYPE_PMUL || t == TYPE_ALU14;
      c0134 += e2k_packed_type_p (t) || t == TYPE_ALU14 || t == TYPE_ALU0134;
    }
  /* A store in ALC2 or ALC5 keeps a load out of ALC3 or ALC0 (gas,
     spec/isa/bundle.md), so an instruction holds 4 - 2 * stores loads.  */
  auto mii_of = [&] (int alu)
    {
      int m = MAX (CEIL (alu, 6), MAX (CEIL (loads + 2 * stores, 4),
				       CEIL (stores, 2)));
      m = MAX (m, MAX (CEIL (c03, 2), MAX (CEIL (c14, 2), CEIL (c0134, 4))));
      /* A divide every 2 cycles.  */
      return MAX (m, 2 * divs);
    };
  int mii = mii_of (alu);
  /* AAU stores pay for their setup (two AAU writes each, on every way
     in) only by the operations they take out of the kernel: where those
     wouldn't raise the bound, store as before (Linpack's daxpy, II 1
     either way: 1.2% slower on the 8C2 with them).  */
  if (l->nstaa && mii_of (alu + kalu) == mii)
    {
      l->staa_unwanted = true;
      return e2k_ms_why ("AAU stores would not pay");
    }
  if (l->napb)
    {
      /* Array prefetch costs about 20 cycles a run (the setup, and bap's
	 22 to the first mova, spec/isa/apb.md, "Timing") and takes the
	 memory latency out of the loop: a stream from memory without it
	 stalls on every cache line (PolyBench's jacobi-2d on the 8C2: 21.8
	 cycles an iteration for 2.0 modelled, 9 times slower).  lcc uses
	 it in every counted loop it can (apb.md, "How lcc uses APB"); so
	 here too, except where the movas don't shorten the kernel and the
	 profile, or else the count the doloop pass knew, says the loop runs
	 fewer than E2K_APB_MIN_TRIP times.  */
      int mii_apb = MAX (mii, CEIL (l->napb, 4));
      int mii_ld = MAX (mii, MAX (CEIL (alu + l->napb, 6),
				  CEIL (loads + l->napb + 2 * stores, 4)));
      gcov_type iters;
      profile_count entry = profile_count::zero ();
      edge e;
      edge_iterator ei;
      FOR_EACH_EDGE (e, ei, bb->preds)
	if (e->src != bb)
	  entry += e->count ();
      if (bb->count.reliable_p () && entry.reliable_p () && entry.nonzero_p ())
	iters = bb->count.to_gcov_type () / MAX (entry.to_gcov_type (), 1);
      else
	iters = e2k_loop_max_iters (l->jump);
      if (iters < 0 && !e2k_apb_unknown)
	iters = 0;
      if (mii_ld <= mii_apb && iters >= 0 && iters < E2K_APB_MIN_TRIP
	  && !e2k_apb_force && !e2k_ms_apb_big_p ())
	return e2k_ms_why ("array prefetch would not pay");
      mii = mii_apb;
    }
  /* A while loop's exit predicate lives 3 cycles at least, and without
     rotation (e2k_ms_assign_pnames) at most II.  */
  if (l->wl && !e2k_rotate_preds)
    mii = MAX (mii, 3);
  /* One iteration alone: its critical path (through dependences
     within the iteration) or its operations at 6 per cycle; with loads
     read at their latency.  */
  int asap[E2K_MS_MAX_NODES], len = CEIL (l->n, 6);
  for (int i = 0; i < l->n; i++)
    {
      asap[i] = 0;
      for (e2k_ms_dep &d : l->deps)
	if (d.to == i && d.dist == 0 && d.from < i)
	  asap[i] = MAX (asap[i], asap[d.from] + d.lat);
    }
  for (e2k_ms_dep &d : l->deps)
    if (d.dist == 0)
      len = MAX (len, asap[d.from] + d.lat + 1);
  for (int i = 0; i < l->n; i++)
    len = MAX (len, asap[i] + 1);
  if (l->wl)
    len = MAX (len, asap[l->stay] + 3 + 1);
  set_far (true);
  /* Where the body's order fails at an II, the earliest starts at that
     II (e2k_ms_schedule); not in a first attempt that a lock load may
     still improve (e2k_ms_try retries with the DAM).  */
  bool est_ok = e2k_ms_est && (!l->may_dam || l->want_dam || !e2k_dam);
  int ii = MAX (mii, 1);
  /* Worth a prologue, a ring and two setbn only if the kernel is
     clearly shorter than one iteration; or shorter at all when the loop
     is known to run long (PolyBench's seidel-2d: II 38 for an iteration
     of 49 cycles, as lcc's, 1998 times).  */
  bool longrun = e2k_ms_long && e2k_ms_long_p (l);
  auto worth = [&] (int ii)
    {
      return (ii + 2 <= len && (longrun || 4 * ii <= 3 * len)
	      && ii <= E2K_MS_MAX_II);
    };
  for (;;)
    {
      bool ok = false, est = false;
      for (; worth (ii); ii++)
	{
	  if (e2k_ms_schedule (l, ii, false))
	    ok = true;
	  else if (est_ok && e2k_ms_schedule (l, ii, true))
	    ok = est = true;
	  else if (est_ok && e2k_ms_schedule (l, ii, true, true))
	    ok = est = true;
	  if (ok)
	    break;
	}
      if (ok && dump_file)
	fprintf (dump_file, ";; e2k_modsched: loop bb %d: %d insns, "
		 "II %d, %d stages, unpipelined %d%s%s\n", bb->index, l->n,
		 l->ii, l->stages, len, l->wl ? ", while loop" : "",
		 est ? ", by earliest start" : "");
      /* Far loads cost stages and names, never II: nearer before a
	 longer II (PolyBench's deriche on v3: its II-1 loops need 56
	 stages with them, more names than the ring has).  */
      if (!ok && !far.is_empty ())
	{
	  nearer ();
	  ii = MAX (mii, 1);
	  continue;
	}
      if (!ok)
	return e2k_ms_fail (bb, "no schedule shorter than one iteration");
      if (e2k_ms_probe_ii)
	{
	  *e2k_ms_probe_ii = l->ii;
	  return false;
	}
      e2k_ms_dam_plan (l);
      const char *why = NULL;
      if (!e2k_ms_assign_names (l, 0)
	  && (e2k_ms_rebase_stores (l, false), !e2k_ms_assign_names (l, 0)))
	why = "ring too big";
      else if (!e2k_ms_assign_pnames (l))
	why = "predicate ring";
      /* Lifetimes that touch let two instructions of one cycle each write
	 what the other reads, which the prologue can't do in sequence;
	 then keep a cycle between them.  (e2k_ms_emit fails before it
	 emits anything.)  */
      else if (!e2k_ms_emit (l, pre_ends, entries, exit_edge, w)
	       && (!e2k_ms_assign_names (l, 1)
		   || !e2k_ms_emit (l, pre_ends, entries, exit_edge, w)))
	why = "prologue order";
      if (!why)
	break;
      if (!far.is_empty ())
	{
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: II %d: %s; loads %d cycles "
		     "on\n", ii, why, far_lat / 2 >= 8 ? far_lat / 2 : 0);
	  e2k_ms_rebase_stores (l, true);
	  nearer ();
	  continue;
	}
      /* A longer II needs fewer names: try it while the kernel is still
	 clearly shorter than one iteration.  With array prefetch that
	 beats the same II without it (fdtd-2d's first loop: 25 stages at
	 II 1 needed 64 names; at II 2 it fits, and the movas keep the
	 memory latency out of the loop); and the body's order at a longer
	 II may fit where the earliest starts didn't.  */
      if (!est && !(ii + 3 <= len && worth (ii + 1)))
	return e2k_ms_fail (bb, why);
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: II %d%s: %s\n", ii,
		 est ? " by earliest start" : "", why);
      e2k_ms_rebase_stores (l, true);
      ii++;
    }
  cfun->machine->rot_pairs = MAX (cfun->machine->rot_pairs, l->pairs);
  if (l->npred)
    cfun->machine->rot_preds = true;
  return true;
}

/* Analyze and pipeline L (e2k_ms_emit has the other arguments); if
   that fails for loads that may read what the loop's stores write, try
   again with a lock load (DAM).  Deletes L.  */
static bool
e2k_ms_try (e2k_ms_loop *l, basic_block exit, const vec<rtx_insn *> &pre_ends,
	    const vec<edge> &entries, edge exit_edge, const e2k_ms_wl *w)
{
  basic_block bb = l->bb;
  int retries = 0;
  /* L's loop again, analyzed afresh with WANT_DAM, APB_OK and STAA_OK.  */
  auto again_with = [&] (bool want_dam, bool apb_ok, bool staa_ok)
    {
      e2k_ms_loop *l2 = new e2k_ms_loop;
      l2->bb = l->bb;
      l2->jump = l->jump;
      for (rtx_insn *insn : l->insns)
	l2->insns.safe_push (insn);
      l2->wl = l->wl;
      l2->stay = l2->c1 = -1;
      l2->nh = l2->nh0 = l->nh0;
      l2->p1 = l->p1;
      l2->pstay = l->pstay;
      l2->e1 = l->e1;
      l2->x1 = l->x1;
      l2->edisp = l->edisp;
      l2->want_dam = want_dam;
      l2->may_dam = false;
      l2->dam = l2->kchk = -1;
      l2->apb_ok = apb_ok;
      l2->staa_ok = staa_ok;
      l2->apb_tmp = l->apb_tmp;
      l2->binv = l->binv;
      delete l;
      l = l2;
    };
  bool dam_first = false, probed = false;
  bool apb0 = l->apb_ok, staa0 = l->staa_ok;
  for (int attempt = 0; ; attempt++)
    {
      bool ok = e2k_ms_analyze (l, exit);
      /* A recurrence through memory can set the II where a lock load
	 would not (NPB IS's histogram, "prv_buff1[key_buff2[i]]++": II 5
	 a key, each load waiting for the last store; lcc takes about 1.3
	 cycles): find the II both ways, and take data speculation first
	 when it is clearly shorter.  */
      if (ok && !probed && !l->want_dam && l->may_dam && e2k_dam)
	{
	  int ii0 = INT_MAX, ii1 = INT_MAX;
	  probed = true;
	  e2k_ms_probe_ii = &ii0;
	  e2k_ms_pipeline (l, pre_ends, entries, exit_edge, w);
	  again_with (true, false, false);
	  if (e2k_ms_analyze (l, exit))
	    {
	      e2k_ms_probe_ii = &ii1;
	      e2k_ms_pipeline (l, pre_ends, entries, exit_edge, w);
	    }
	  e2k_ms_probe_ii = NULL;
	  dam_first = ii1 < INT_MAX && (ii0 == INT_MAX || 3 * ii1 <= 2 * ii0);
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: loop bb %d: II %d, with "
		     "DAM %d%s\n", bb->index, ii0 == INT_MAX ? -1 : ii0,
		     ii1 == INT_MAX ? -1 : ii1, dam_first ? ": DAM first" : "");
	  again_with (dam_first, dam_first ? false : apb0,
		      dam_first ? false : staa0);
	  ok = e2k_ms_analyze (l, exit);
	}
      if (!ok)
	e2k_ms_fail (bb, "body");
      else
	ok = e2k_ms_pipeline (l, pre_ends, entries, exit_edge, w);
      /* Data speculation first failed: as before, without it.  */
      if (!ok && dam_first)
	{
	  dam_first = false;
	  again_with (false, apb0, staa0);
	  attempt--;
	  continue;
	}
      /* The same without AAU stores, if they wouldn't pay.  */
      if (!ok && l->staa_unwanted)
	{
	  again_with (l->want_dam, l->apb_ok, false);
	  attempt--;
	  continue;
	}
      /* Without array prefetch, if that failed with it; then without
	 AAU stores.  */
      bool apb_again = !ok && l->napb > 0;
      bool again = apb_again || (!ok && l->nstaa > 0);
      if (!again && (ok || attempt > retries || !l->may_dam || !e2k_dam))
	{
	  delete l;
	  return ok;
	}
      retries += again;
      again_with (!again, false, apb_again && l->staa_ok);
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: loop bb %d again with%s\n",
		 bb->index, apb_again ? "out array prefetch"
		 : again ? "out AAU stores" : " DAM");
    }
}

/* Pipeline the loop that BB is, ending in the hardware loop end JUMP.  */
/* %b[0..7] can't hold a value a pipelined loop uses: setbn renames
   them.  Give each one the loop uses a register free around and in the
   loop, for the loop: copied there before it if live into it,
   back after it (after the setbn that gives the outgoing registers
   back) if live after it.  False if there's none free.  Under high
   register pressure (main of Linpack, everything inlined) allocation
   puts loop invariants there once the window is full; for an invariant
   with no register free, BINV (when not null) gets bit K instead (see
   e2k_ms_loop).  */
static bool
e2k_ms_move_b (const vec<basic_block> &bbs, const vec<rtx_insn *> &pre_ends,
	       const vec<edge> &entries, edge exit_edge, unsigned *binv)
{
  CLEAR_HARD_REG_SET (e2k_ms_live_out_extra);
  bool used[8] = { false };
  HARD_REG_SET body;
  CLEAR_HARD_REG_SET (body);
  rtx_insn *insn;
  for (basic_block bb : bbs)
    FOR_BB_INSNS (bb, insn)
      if (INSN_P (insn))
	{
	  subrtx_iterator::array_type array;
	  FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
	    if (REG_P (*iter) && REGNO (*iter) < FIRST_PSEUDO_REGISTER)
	      {
		if (B_REGNO_P (REGNO (*iter)))
		  {
		    if (REG_NREGS (*iter) != 1)
		      return false;
		    used[REGNO (*iter) - B0_REGNUM] = true;
		  }
		add_to_hard_reg_set (&body, GET_MODE (*iter), REGNO (*iter));
	      }
	}
  basic_block bb = bbs[0];
  bitmap lh = df_get_live_in (bb), lx = df_get_live_in (exit_edge->dest);
  /* An entry by a prepared conditional transfer can't be split (its
     disp would send it past the new block): the copies go before its
     jump, so their registers must be dead on its other way too.  */
  auto cond_entry = [] (edge e)
    {
      return (!(e->flags & EDGE_FALLTHRU) && !single_succ_p (e->src)
	      && JUMP_P (BB_END (e->src)));
    };
  auto_bitmap lo;
  for (edge e : entries)
    if (cond_entry (e))
      {
	edge o;
	edge_iterator ei;
	FOR_EACH_EDGE (o, ei, e->src->succs)
	  if (o != e)
	    bitmap_ior_into (lo, df_get_live_in (o->dest));
      }
  /* One the loop only sets and reads within an iteration needs nothing:
     the pipeliner renames its value (NPB SP's eta-direction fluxes, with
     every other register taken).  */
  for (int k = 0; k < 8; k++)
    if (used[k] && !bitmap_bit_p (lh, B0_REGNUM + k)
	&& !bitmap_bit_p (lx, B0_REGNUM + k))
      used[k] = false;
  unsigned map[8];
  int n = 0;
  for (int k = 0; k < 8; k++)
    if (used[k])
      {
	auto free_p = [&] (unsigned g)
	  {
	    for (int k2 = 0; k2 < k; k2++)
	      if (used[k2] && map[k2] == g)
		return false;
	    return (!fixed_regs[g] && !TEST_HARD_REG_BIT (body, g)
		    && !bitmap_bit_p (lh, g) && !bitmap_bit_p (lx, g)
		    && !bitmap_bit_p (lo, g));
	  };
	/* A global (%g16..%g31), else a window register the function
	   has, else one that grows the window (e2k_compute_window sizes
	   it from what the insns use).  */
	unsigned g = INVALID_REGNUM;
	for (unsigned r = 0; r < 32 && g == INVALID_REGNUM; r++)
	  if (free_p (r))
	    g = r;
	for (unsigned r = R0_REGNUM; r < R0_REGNUM + 64 && g == INVALID_REGNUM;
	     r++)
	  if (df_regs_ever_live_p (r) && free_p (r))
	    g = r;
	for (unsigned r = R0_REGNUM; r < R0_REGNUM + 64 && g == INVALID_REGNUM;
	     r++)
	  if (free_p (r))
	    g = r;
	if (g == INVALID_REGNUM)
	  {
	    /* An invariant the loop only reads: the pipeliner may give it a
	       register its renamed values leave free (BINV; NPB SP's
	       eta- and zeta-direction fluxes, every register taken).  */
	    bool set = false;
	    rtx reg = gen_rtx_REG (DImode, B0_REGNUM + k);
	    for (basic_block b : bbs)
	      FOR_BB_INSNS (b, insn)
		if (INSN_P (insn) && reg_set_p (reg, insn))
		  set = true;
	    if (!binv || set || !bitmap_bit_p (lh, B0_REGNUM + k))
	      return false;
	    *binv |= 1u << k;
	    used[k] = false;
	    continue;
	  }
	map[k] = g;
	n++;
      }
  if (!n)
    return true;
  if (dump_file)
    for (int k = 0; k < 8; k++)
      if (used[k])
	fprintf (dump_file, ";; e2k_modsched: loop bb %d: %%b[%d] -> %s%s%s\n",
		 bb->index, k, reg_names[map[k]],
		 bitmap_bit_p (lh, B0_REGNUM + k) ? ", copied in" : "",
		 bitmap_bit_p (lx, B0_REGNUM + k) ? ", copied out" : "");
  for (rtx_insn *pre_end : pre_ends)
    for (int k = 0; k < 8; k++)
      if (used[k] && bitmap_bit_p (lh, B0_REGNUM + k))
	{
	  rtx_insn *c = emit_insn_before
	    (gen_rtx_SET (gen_rtx_REG (DImode, map[k]),
			  gen_rtx_REG (DImode, B0_REGNUM + k)), pre_end);
	  recog_memoized (c);
	}
  for (edge e : entries)
    {
      start_sequence ();
      for (int k = 0; k < 8; k++)
	if (used[k] && bitmap_bit_p (lh, B0_REGNUM + k))
	  recog_memoized (emit_insn (gen_rtx_SET (gen_rtx_REG (DImode, map[k]),
						  gen_rtx_REG (DImode,
							       B0_REGNUM + k))));
      rtx_insn *seq = end_sequence ();
      if (seq && cond_entry (e))
	emit_insn_before (seq, BB_END (e->src));
      else if (seq)
	insert_insn_on_edge (seq, e);
    }
  for (basic_block bb2 : bbs)
    FOR_BB_INSNS (bb2, insn)
      if (INSN_P (insn))
	{
	  bool changed = false;
	  subrtx_ptr_iterator::array_type array;
	  FOR_EACH_SUBRTX_PTR (iter, array, &PATTERN (insn), NONCONST)
	    {
	      rtx *loc = *iter;
	      if (REG_P (*loc) && B_REGNO_P (REGNO (*loc))
		  && used[REGNO (*loc) - B0_REGNUM])
		{
		  *loc = gen_rtx_REG (GET_MODE (*loc),
				      map[REGNO (*loc) - B0_REGNUM]);
		  changed = true;
		}
	    }
	  if (REG_NOTES (insn))
	    FOR_EACH_SUBRTX_PTR (iter, array, &REG_NOTES (insn), NONCONST)
	      {
		rtx *loc = *iter;
		if (*loc && REG_P (*loc) && B_REGNO_P (REGNO (*loc))
		    && used[REGNO (*loc) - B0_REGNUM])
		  *loc = gen_rtx_REG (GET_MODE (*loc),
				      map[REGNO (*loc) - B0_REGNUM]);
	      }
	  if (changed)
	    {
	      INSN_CODE (insn) = -1;
	      df_insn_rescan (insn);
	    }
	}
  start_sequence ();
  for (int k = 0; k < 8; k++)
    if (used[k] && bitmap_bit_p (lx, B0_REGNUM + k))
      {
	emit_insn (gen_rtx_SET (gen_rtx_REG (DImode, B0_REGNUM + k),
				gen_rtx_REG (DImode, map[k])));
	SET_HARD_REG_BIT (e2k_ms_live_out_extra, map[k]);
      }
  rtx_insn *after = end_sequence ();
  if (after)
    insert_insn_on_edge (after, exit_edge);
  df_analyze ();
  return true;
}

static bool
e2k_ms_fail (basic_block bb, const char *why)
{
  if (dump_file)
    fprintf (dump_file, ";; e2k_modsched: loop bb %d not pipelined: %s\n",
	     bb->index, why);
  return false;
}

/* Whether L, a counted loop, may read through array prefetch (spec/isa/
   apb.md): a hardware loop end through %ctpr1 (not the strip-mined one,
   whose next chunk would restart the count the unit's positions follow
   after a trap), and %ctpr2, which holds the program, free on the way
   into the loop (the setup goes after what ends the blocks of
   PRE_ENDS, the waits after rwd %lsr), through it, and after it (EXIT).
   Also picks the register the setup computes the areas' addresses in:
   a window register dead on every way in.  Sets L->staa_ok if the loop
   may store through the AAU (e2k_ms_mark_staa), which needs that
   register but not %ctpr2.  */
static bool
e2k_ms_apb_ok (e2k_ms_loop *l, const vec<rtx_insn *> &pre_ends,
	       basic_block exit)
{
  l->staa_ok = false;
  if (!e2k_apb && !e2k_staa)
    return false;
  if (recog_memoized (l->jump) != CODE_FOR_e2k_hwloop_end)
    return e2k_ms_why ("no array prefetch: not a plain counted loop");
  HARD_REG_SET used, tail;
  CLEAR_HARD_REG_SET (used);
  CLEAR_HARD_REG_SET (tail);
  for (rtx_insn *insn : l->insns)
    e2k_note_regs (PATTERN (insn), &used);
  for (rtx_insn *pre_end : pre_ends)
    {
      basic_block pb = BLOCK_FOR_INSN (pre_end);
      for (rtx_insn *x = NEXT_INSN (pre_end); x && x != NEXT_INSN (BB_END (pb));
	   x = NEXT_INSN (x))
	if (INSN_P (x))
	  e2k_note_regs (PATTERN (x), &tail);
    }
  used |= tail;
  l->apb_tmp = INVALID_REGNUM;
  /* The setup runs where the loop starts and the end of the program
     where it has ended: a register dead at both will do.  First one the
     loop doesn't touch; failing that, one only the loop's own values use
     (Linpack's main has all 64 in use): the kernel and the prologue hold
     those in the ring, and the copies out write theirs after the end.  */
  for (int pass = 0; pass < 2 && l->apb_tmp == INVALID_REGNUM; pass++)
    for (unsigned r = R0_REGNUM; r < R0_REGNUM + 64; r++)
      {
	if (fixed_regs[r] || TEST_HARD_REG_BIT (pass ? tail : used, r))
	  continue;
	bool dead = !(pass && REGNO_REG_SET_P (df_get_live_in (exit), r));
	for (rtx_insn *pre_end : pre_ends)
	  if (REGNO_REG_SET_P (df_get_live_out (BLOCK_FOR_INSN (pre_end)), r))
	    dead = false;
	if (!dead)
	  continue;
	/* One the function uses already doesn't grow the window.  */
	if (l->apb_tmp == INVALID_REGNUM || df_regs_ever_live_p (r))
	  l->apb_tmp = r;
	if (df_regs_ever_live_p (r))
	  break;
      }
  if (l->apb_tmp == INVALID_REGNUM)
    return e2k_ms_why ("no array prefetch: no free register");
  /* AAU stores need no program in %ctpr2.  */
  l->staa_ok = e2k_staa;
  if (!e2k_apb)
    return false;
  rtx ctpr2 = gen_rtx_REG (DImode, CTPR2_REGNUM);
  if (reg_mentioned_p (ctpr2, PATTERN (l->jump)))
    return e2k_ms_why ("no array prefetch: %ctpr2 ends the loop");
  if (REGNO_REG_SET_P (df_get_live_in (l->bb), CTPR2_REGNUM)
      || REGNO_REG_SET_P (df_get_live_in (exit), CTPR2_REGNUM))
    return e2k_ms_why ("no array prefetch: %ctpr2 live around the loop");
  for (rtx_insn *insn : l->insns)
    if (reg_mentioned_p (ctpr2, PATTERN (insn)))
      return e2k_ms_why ("no array prefetch: %ctpr2 in the loop");
  return true;
}

static bool
e2k_ms_loop_1 (basic_block bb, rtx_insn *jump)
{
  if (EDGE_COUNT (bb->succs) != 2)
    return e2k_ms_fail (bb, "edges");
  edge exit_edge = NULL, e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, bb->succs)
    if (e->dest != bb)
      exit_edge = e;
  if (!exit_edge || (exit_edge->flags & EDGE_COMPLEX))
    return e2k_ms_fail (bb, "edges");
  /* Each way in ends with the wait after rwd %lsr (hw-doloop sets %lsr
     up on every incoming edge); the prologue goes in front of it.  */
  auto_vec<rtx_insn *> pre_ends;
  FOR_EACH_EDGE (e, ei, bb->preds)
    if (e->src != bb)
      {
	/* Past a jump to the loop and a disp that loop branch preparation
	   may have put on the same edge.  */
	rtx_insn *pre_end = BB_END (e->src);
	while (pre_end
	       && (!NONDEBUG_INSN_P (pre_end)
		   || (JUMP_P (pre_end) && JUMP_LABEL (pre_end) == BB_HEAD (bb)
		       && pre_end == BB_END (e->src))
		   || recog_memoized (pre_end) == CODE_FOR_e2k_disp_label))
	  pre_end = PREV_INSN (pre_end);
	if ((e->flags & EDGE_COMPLEX)
	    || !pre_end || recog_memoized (pre_end) != CODE_FOR_e2k_lsr_wait)
	  return e2k_ms_fail (bb, "preheader");
	pre_ends.safe_push (pre_end);
      }
  if (pre_ends.is_empty () || pre_ends.length () > 4)
    return e2k_ms_fail (bb, "preheader");

  auto_vec<basic_block> bbs;
  bbs.safe_push (bb);
  auto_vec<edge> no_entries;
  unsigned binv = 0;
  if (!e2k_ms_move_b (bbs, pre_ends, no_entries, exit_edge, &binv))
    return e2k_ms_fail (bb, "no free register for a %b[] value");

  e2k_ms_loop *l = new e2k_ms_loop;
  l->bb = bb;
  l->jump = jump;
  l->wl = false;
  l->stay = l->c1 = -1;
  l->p1 = l->pstay = NULL_RTX;
  l->x1 = NULL;
  l->edisp = NULL;
  l->nh = l->nh0 = 0;
  l->want_dam = l->may_dam = false;
  l->dam = l->kchk = -1;
  l->binv = binv;
  rtx_insn *insn;
  FOR_BB_INSNS (bb, insn)
    if (NONDEBUG_INSN_P (insn) && insn != jump)
      l->insns.safe_push (insn);
  l->apb_ok = e2k_ms_apb_ok (l, pre_ends, exit_edge->dest);
  return e2k_ms_try (l, exit_edge->dest, pre_ends, no_entries, exit_edge,
		     NULL);
}

/* While loops (spec/isa/loops.md, "Early exits and while loops"): a
   block H that ends "if (p) goto H" (or "if (!p)"), with p set in it,
   or two blocks, H ending "if (p1) goto X" and the one it falls through
   to, B, ending "if (p2) goto H" and falling through to X too, as
   "while (list && list->x != k) list = list->next" becomes.  Pipelined
   like a counted loop, but the kernel runs until the test says stop:
   every operation is speculative (the kernel runs the early stages of
   iterations past the end), the loop end "abn; ct %ctprN ? p" is in the
   last row of the last stage, and every other node is before it, so
   the iteration the loop ends with is complete (stores in the last
   stage too).  Two blocks become one: B's operations also run when H's
   exit is taken, speculatively (so B must not store), and "landp ~p1,
   p2" (lazy: p2's diagnostic tag doesn't count when p1 is set) is the
   loop end's test.  After the loop, H's exit compare runs again on the
   last iteration's values, and the registers live at X get H's values
   under it, B's otherwise.  The test needs no rotating predicates as
   long as II is 3 or more (e2k_ms_place_exit).  */
static bool
e2k_ms_wloop (basic_block h)
{
  rtx_insn *jump = BB_END (h);
  rtx cond = e2k_ms_jump_cond (jump);
  if (!cond || recog_memoized (jump) < 0 || get_attr_type (jump) != TYPE_CT)
    return false;
  basic_block b = NULL, last = h, x1 = NULL;
  bool diff_exits = false;
  rtx_insn *ljump = jump, *hdisp = NULL;
  e2k_ms_wl w;
  memset (&w, 0, sizeof w);
  if (JUMP_LABEL (jump) != BB_HEAD (h))
    {
      /* Two blocks: H exits, B loops.  */
      edge f = find_fallthru_edge (h->succs);
      if (!f || EDGE_COUNT (h->succs) != 2)
	return false;
      b = f->dest;
      if (b == h || !single_pred_p (b) || EDGE_COUNT (b->succs) != 2
	  || !JUMP_P (BB_END (b)))
	return false;
      ljump = BB_END (b);
      if (JUMP_LABEL (ljump) != BB_HEAD (h) || !e2k_ms_jump_cond (ljump)
	  || recog_memoized (ljump) < 0 || get_attr_type (ljump) != TYPE_CT)
	return false;
      edge fb = find_fallthru_edge (b->succs);
      x1 = BLOCK_FOR_INSN (JUMP_LABEL (jump));
      if (!fb || x1 == h || x1 == b)
	return false;
      if (fb->dest != x1)
	{
	  /* Copies out of the %b[0..7] e2k_ms_move_b renames go on the
	     second block's exit only.  */
	  rtx_insn *insn;
	  for (basic_block bb : { h, b })
	    FOR_BB_INSNS (bb, insn)
	      if (INSN_P (insn))
		{
		  subrtx_iterator::array_type array;
		  FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
		    if (REG_P (*iter) && B_REGNO_P (REGNO (*iter)))
		      return e2k_ms_fail (h, "%b[0..7] in a loop of two exits");
		}
	  diff_exits = true;
	}
      last = b;
      /* The disp of H's exit, if nothing else reads its CTPR.  */
      rtx ctpr = XEXP (XVECEXP (PATTERN (jump), 0, 1), 0);
      rtx_insn *insn;
      FOR_BB_INSNS (h, insn)
	if (NONDEBUG_INSN_P (insn) && insn != jump
	    && reg_mentioned_p (ctpr, PATTERN (insn)))
	  {
	    if (hdisp || recog_memoized (insn) != CODE_FOR_e2k_disp_label)
	      return e2k_ms_fail (h, "the exit's CTPR");
	    hdisp = insn;
	  }
      FOR_BB_INSNS (b, insn)
	if (NONDEBUG_INSN_P (insn) && insn != ljump
	    && reg_mentioned_p (ctpr, PATTERN (insn)))
	  return e2k_ms_fail (h, "the exit's CTPR");
      if (bitmap_bit_p (df_get_live_in (x1), REGNO (ctpr)))
	return e2k_ms_fail (h, "the exit's CTPR");
      if (!diff_exits)
	x1 = NULL;
    }
  else if (EDGE_COUNT (h->succs) != 2)
    return false;

  edge exit_edge = find_fallthru_edge (last->succs);
  if (!exit_edge || exit_edge->dest == h || (exit_edge->flags & EDGE_COMPLEX))
    return e2k_ms_fail (h, "edges");
  auto_vec<edge> entries;
  edge e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, h->preds)
    if (e->src != last)
      {
	if (e->flags & EDGE_COMPLEX)
	  return e2k_ms_fail (h, "entry edges");
	/* The prologue goes on the edge.  A prepared conditional
	   transfer along it goes where its CTPR says: only one whose disp
	   is in its own block can be pointed at the prologue
	   (e2k_ms_split_entry), not another latch of an outer loop.  */
	rtx_insn *j = BB_END (e->src);
	if (!(e->flags & EDGE_FALLTHRU) && JUMP_P (j) && recog_memoized (j) >= 0
	    && get_attr_type (j) == TYPE_CT && !single_succ_p (e->src)
	    && !e2k_ms_local_disp (j))
	  return e2k_ms_fail (h, "entered by a prepared conditional transfer");
	entries.safe_push (e);
      }
  if (entries.is_empty () || entries.length () > 4)
    return e2k_ms_fail (h, "entry edges");
  /* The loop end's CTPR is prepared before the loop and kept, or by a
     disp of the second block, which then goes to the prologues.  */
  rtx lctpr = XEXP (XVECEXP (PATTERN (ljump), 0, 1), 0);
  rtx_insn *insn, *bdisp = NULL;
  for (basic_block bb : { h, b })
    if (bb)
      FOR_BB_INSNS (bb, insn)
	if (NONDEBUG_INSN_P (insn) && insn != ljump
	    && reg_mentioned_p (lctpr, PATTERN (insn)))
	  {
	    if ((bb == b || (!b && bb == h)) && !bdisp
		&& recog_memoized (insn) == CODE_FOR_e2k_disp_label
		&& reg_set_p (lctpr, insn)
		&& (label_ref_label (XVECEXP (SET_SRC (PATTERN (insn)), 0, 0))
		    == JUMP_LABEL (ljump)))
	      {
		bdisp = insn;
		continue;
	      }
	    if (dump_file)
	      print_rtl_single (dump_file, insn);
	    return e2k_ms_fail (h, "the loop end's CTPR");
	  }
  /* Nothing that can't be pipelined, before e2k_ms_move_b changes the
     loop: a call reads and sets %b[0..7] (pcre2's name table scan lost
     its strcmp arguments).  */
  for (basic_block bb : { h, b })
    if (bb)
      FOR_BB_INSNS (bb, insn)
	if (NONDEBUG_INSN_P (insn)
	    && (CALL_P (insn) || e2k_asm_insn_p (insn)
		|| volatile_insn_p (PATTERN (insn))))
	  return e2k_ms_fail (h, "a call or asm");
  /* B runs speculatively: no stores.  */
  if (b)
    FOR_BB_INSNS (b, insn)
      if (NONDEBUG_INSN_P (insn) && insn != ljump)
	{
	  rtx set = single_set (insn);
	  if (!set || MEM_P (SET_DEST (set)))
	    return e2k_ms_fail (h, "the second block stores");
	}

  auto_vec<basic_block> bbs;
  bbs.safe_push (h);
  if (b)
    bbs.safe_push (b);
  auto_vec<rtx_insn *> no_pre_ends;
  if (!e2k_ms_move_b (bbs, no_pre_ends, entries, exit_edge, NULL))
    return e2k_ms_fail (h, "no free register for a %b[] value");

  e2k_ms_loop *l = new e2k_ms_loop;
  l->bb = h;
  l->jump = ljump;
  l->wl = true;
  l->stay = l->c1 = -1;
  l->p1 = l->pstay = NULL_RTX;
  l->x1 = x1;
  l->nh = 0;
  l->want_dam = l->may_dam = false;
  l->dam = l->kchk = -1;
  l->edisp = b ? NULL : bdisp;
  FOR_BB_INSNS (h, insn)
    if (NONDEBUG_INSN_P (insn) && insn != jump && insn != hdisp
	&& insn != bdisp)
      l->insns.safe_push (insn);
  l->nh = l->nh0 = l->insns.length ();
  rtx_insn *landp = NULL;
  if (b)
    {
      FOR_BB_INSNS (b, insn)
	if (NONDEBUG_INSN_P (insn) && insn != ljump && insn != bdisp)
	  l->insns.safe_push (insn);
      /* A free predicate for "landp ~p1, p2".  */
      HARD_REG_SET used;
      CLEAR_HARD_REG_SET (used);
      for (basic_block bb : bbs)
	FOR_BB_INSNS (bb, insn)
	  if (INSN_P (insn))
	    e2k_note_regs (PATTERN (insn), &used);
      bitmap lh = df_get_live_in (h), lx = df_get_live_in (exit_edge->dest);
      unsigned r;
      for (r = PRED0_REGNUM; PRED_REGNO_P (r); r++)
	if (!fixed_regs[r] && !TEST_HARD_REG_BIT (used, r)
	    && !bitmap_bit_p (lh, r) && !bitmap_bit_p (lx, r)
	    && !(x1 && bitmap_bit_p (df_get_live_in (x1), r)))
	  break;
      if (!PRED_REGNO_P (r))
	{
	  delete l;
	  return e2k_ms_fail (h, "no free predicate");
	}
      rtx c2 = e2k_ms_jump_cond (ljump);
      w.b = b;
      w.hjump = jump;
      w.hdisp = hdisp;
      w.bdisp = bdisp;
      w.p1 = XEXP (cond, 0);
      w.pstay = gen_rtx_REG (BImode, r);
      l->p1 = w.p1;
      l->pstay = w.pstay;
      l->e1 = GET_CODE (cond);
      rtx pat = gen_rtx_SET (w.pstay,
			     gen_rtx_AND (BImode,
					  gen_rtx_fmt_ee (reverse_condition
							  (l->e1), BImode,
							  w.p1, const0_rtx),
					  gen_rtx_fmt_ee (GET_CODE (c2), BImode,
							  XEXP (c2, 0),
							  const0_rtx)));
      landp = emit_insn_before (pat, ljump);
      if (recog_memoized (landp) < 0)
	gcc_unreachable ();
      l->insns.safe_push (landp);
    }
  bool ok = e2k_ms_try (l, exit_edge->dest, no_pre_ends, entries, exit_edge,
			b ? &w : NULL);
  if (!ok && landp)
    delete_insn (landp);
  return ok;
}

/* In a function without calls nothing needs %b[0..7], which register
   allocation may still have used: a pipelined loop can't keep a value
   in them across setbn.  Give each one a window register above all the
   used ones instead, in the whole function.  */
static void
e2k_ms_free_b (void)
{
  rtx_insn *insn;
  int maxr = -1;
  bool used[8] = { false };
  for (insn = get_insns (); insn; insn = NEXT_INSN (insn))
    {
      if (!INSN_P (insn))
	continue;
      if (CALL_P (insn))
	return;
      subrtx_iterator::array_type array;
      FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
	if (REG_P (*iter) && REGNO (*iter) < FIRST_PSEUDO_REGISTER)
	  for (unsigned r = REGNO (*iter); r < END_REGNO (*iter); r++)
	    {
	      if (W_REGNO_P (r))
		maxr = MAX (maxr, (int) (r - R0_REGNUM));
	      else if (B_REGNO_P (r))
		{
		  if (REG_NREGS (*iter) != 1)
		    return;
		  used[r - B0_REGNUM] = true;
		}
	    }
    }
  unsigned map[8];
  int next = maxr + 1, n = 0;
  for (int k = 0; k < 8; k++)
    if (used[k])
      {
	while (next <= 63 && fixed_regs[R0_REGNUM + next])
	  next++;
	if (next > 63)
	  return;
	map[k] = R0_REGNUM + next++;
	n++;
      }
  if (!n)
    return;
  for (insn = get_insns (); insn; insn = NEXT_INSN (insn))
    {
      if (!INSN_P (insn))
	continue;
      bool changed = false;
      subrtx_ptr_iterator::array_type array;
      FOR_EACH_SUBRTX_PTR (iter, array, &PATTERN (insn), NONCONST)
	{
	  rtx *loc = *iter;
	  if (REG_P (*loc) && B_REGNO_P (REGNO (*loc)))
	    {
	      *loc = gen_rtx_REG (GET_MODE (*loc),
				  map[REGNO (*loc) - B0_REGNUM]);
	      changed = true;
	    }
	}
      if (REG_NOTES (insn))
	FOR_EACH_SUBRTX_PTR (iter, array, &REG_NOTES (insn), NONCONST)
	  {
	    rtx *loc = *iter;
	    if (*loc && REG_P (*loc) && B_REGNO_P (REGNO (*loc)))
	      *loc = gen_rtx_REG (GET_MODE (*loc),
				  map[REGNO (*loc) - B0_REGNUM]);
	  }
      if (changed)
	{
	  INSN_CODE (insn) = -1;
	  remove_reg_equal_equiv_notes (insn);
	  df_insn_rescan (insn);
	}
    }
}

static void
e2k_modsched (void)
{
  e2k_ms_free_b ();
  df_analyze ();
  /* The memory dependences ask may_alias_p, whose base terms of hard
     registers come from the last init_alias_analysis: some pass before
     this one, before the loop versions and copies made since
     (gcc.dg/vect/vect-alias-check-18.c: a store and the next vector
     iteration's load of the same bytes were "independent").  */
  init_alias_analysis ();
  dfa_start ();
  /* Only haifa's sched_init sets it: in the first function of a file
     that sched2 skips (gcc.dg/vect/vect-div-bitmask-5.c's fun1, at
     -O1), the rows were empty and the states random.  */
  dfa_state_size = state_size ();
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *jump = BB_END (bb);
      if (!JUMP_P (jump) || recog_memoized (jump) < 0)
	continue;
      if ((recog_memoized (jump) == CODE_FOR_e2k_hwloop_end
	   || recog_memoized (jump) == CODE_FOR_e2k_hwloop_end_wide)
	  && JUMP_LABEL (jump) == BB_HEAD (bb))
	e2k_ms_loop_1 (bb, jump);
      else if (e2k_pipeline_while)
	e2k_ms_wloop (bb);
    }
  dfa_finish ();
  end_alias_analysis ();
  /* Also when no loop was pipelined: e2k_ms_move_b puts its copies back
     on the exit edge before the schedule is tried (left there, they are
     lost, and the edge points at insns the garbage collector later
     reads as GIMPLE).  */
  commit_edge_insertions ();
}

const char *
e2k_output_setbn (int pairs, int npred)
{
  static char buf[160];
  machine_function *m = cfun->machine;
  e2k_compute_window ();
  int n = 0;
  /* The ring's own window: from the loop's setbn to the one after it,
     which the copies out of the ring precede (e2k_ms_emit).  The
     same wide instruction already uses the new window.  */
  if (m->ring_setwd)
    n = snprintf (buf, sizeof buf, "setwd\twsz = %d, nfx = 1, dbl = %d\n\t",
		  pairs ? m->ring_base + pairs : m->wsz,
		  e2k_dbl_p () ? 1 : 0);
  if (pairs == 0 && m->use_b)
    n += snprintf (buf + n, sizeof buf - n,
		   "setbn\trsz = 3, rbs = %d, rcur = 0", m->wbase);
  else
    n += snprintf (buf + n, sizeof buf - n,
		   "setbn\trsz = %d, rbs = %d, rcur = 0",
		   (pairs ? pairs : m->rot_pairs) - 1, m->ring_base);
  /* The predicate ring of a pipelined while loop, %pred0 .. NPRED - 1
     (e2k_ms_assign_pnames); size 1 again when the loop is left.  */
  if (npred > 0)
    snprintf (buf + n, sizeof buf - n, "\n\tsetbp\tpsz = %d", npred - 1);
  else if (pairs == 0 && m->rot_preds)
    snprintf (buf + n, sizeof buf - n, "\n\tsetbp\tpsz = 0");
  return buf;
}

/* A prepared conditional transfer; the loop end of a pipelined while
   loop also rotates the ring.  */
const char *
e2k_output_ct_pred (rtx_insn *insn)
{
  if (e2k_ms_flag (insn) & E2K_MS_ABP)
    return "abn\tabnf=1, abnt=1\n\tabp\tabpf=1, abpt=1\n\tct\t%3 ? %C0%1";
  if (e2k_ms_flag (insn) & E2K_MS_ABN)
    return "abn\tabnf=1, abnt=1\n\tct\t%3 ? %C0%1";
  return "ct\t%3 ? %C0%1";
}

const char *
e2k_output_hwloop_end (rtx_insn *insn)
{
  if (e2k_ms_flag (insn) & E2K_MS_ABP)
    return "alc\talcf=1, alct=1\n\tabn\tabnf=1, abnt=1\n\t"
	   "abp\tabpf=1, abpt=1\n\tct\t%0 ? %%NOT_LOOP_END";
  if (e2k_ms_flag (insn) & E2K_MS_ABN)
    return "alc\talcf=1, alct=1\n\tabn\tabnf=1, abnt=1\n\t"
	   "ct\t%0 ? %%NOT_LOOP_END";
  return "alc\talcf=1, alct=1\n\tct\t%0 ? %%NOT_LOOP_END";
}

/* ------------------------------------------------------------------ */
/* Loop versioning for aliasing                                        */
/* ------------------------------------------------------------------ */

/* lcc runs a loop whose arrays may overlap in two versions: a test of
   the address ranges picks a copy that may assume they don't (seen in
   its daxpy: the disjoint copy is a one-instruction pipelined loop).
   This GIMPLE pass, after the vectorizer (and again after complete
   unrolling, for the loops that it makes innermost), does the same for
   innermost counted loops without calls, with GCC's runtime alias
   checks (as loop distribution uses them).  In the disjoint copy, every memory
   reference gets a base in a new dependence clique, one per base
   address, as restrict would give: references with the same base keep
   the same base number and so claim nothing about each other, and a
   pair with different bases either was proved independent or is
   covered by the test.  Alias analysis in RTL, the scheduler (and its
   data speculation) and the modulo scheduler then see the copy's
   arrays as disjoint.  */

/* If NITERS is an unsigned X / K (converted to sizetype) and STEP a
   multiple of K, return STEP / K and set *X to X in sizetype; else 0.
   (STEP / K) * X exceeds STEP * (X / K) by (STEP / K) * (X % K), less
   than one step, so a segment built from it still covers every access,
   without the divide (zlib's inflate_fast: "len -= 3" loops, niters
   (len - 3) / 3, whose umulx chain made the check 20 cycles).  */
static HOST_WIDE_INT
e2k_av_undivided (tree niters, HOST_WIDE_INT step, tree *x)
{
  tree q = niters;
  if (CONVERT_EXPR_P (q))
    q = TREE_OPERAND (q, 0);
  if ((TREE_CODE (q) != TRUNC_DIV_EXPR && TREE_CODE (q) != EXACT_DIV_EXPR)
      || !INTEGRAL_TYPE_P (TREE_TYPE (q))
      || !TYPE_UNSIGNED (TREE_TYPE (q))
      || TYPE_PRECISION (TREE_TYPE (q)) > TYPE_PRECISION (sizetype)
      || !tree_fits_uhwi_p (TREE_OPERAND (q, 1)))
    return 0;
  unsigned HOST_WIDE_INT k = tree_to_uhwi (TREE_OPERAND (q, 1));
  if (k < 2 || k > (unsigned HOST_WIDE_INT) HOST_WIDE_INT_MAX
      || absu_hwi (step) % k != 0)
    return 0;
  HOST_WIDE_INT f = step / (HOST_WIDE_INT) k;
  /* F * X can wrap only for an X as wide as sizetype (and could for a
     32-bit X only with |F| >= 2^32, which no access step reaches).  */
  if (TYPE_PRECISION (TREE_TYPE (q)) == TYPE_PRECISION (sizetype)
      && f != 1 && f != -1)
    return 0;
  *x = fold_convert (sizetype, TREE_OPERAND (q, 0));
  return f;
}

/* Bytes from the first to the last access of DR over NITERS + 1
   iterations, as tree-loop-distribution.cc computes them; up to one
   step more when NITERS is a division (e2k_av_undivided).  */
static tree
e2k_av_segment (class loop *loop, data_reference *dr, tree niters)
{
  bool last = dominated_by_p (CDI_DOMINATORS, single_exit (loop)->src,
			      gimple_bb (DR_STMT (dr)));
  tree step = fold_convert (sizetype, DR_STEP (dr));
  tree x = NULL_TREE;
  HOST_WIDE_INT f = (tree_fits_shwi_p (DR_STEP (dr))
		     ? e2k_av_undivided (niters, tree_to_shwi (DR_STEP (dr)),
					 &x)
		     : 0);
  if (f)
    {
      tree seg = size_binop (MULT_EXPR, size_int (f), x);
      return last ? seg : size_binop (MINUS_EXPR, seg, step);
    }
  if (last)
    niters = size_binop (PLUS_EXPR, niters, size_one_node);
  niters = size_binop (MINUS_EXPR, niters, size_one_node);
  return size_binop (MULT_EXPR, step, niters);
}

/* The MEM_REF or TARGET_MEM_REF through a pointer that DR accesses, or
   NULL.  */
static tree
e2k_av_base_ref (data_reference *dr)
{
  tree base = get_base_address (DR_REF (dr));
  if (base
      && (TREE_CODE (base) == MEM_REF || TREE_CODE (base) == TARGET_MEM_REF)
      && TREE_CODE (TREE_OPERAND (base, 0)) == SSA_NAME)
    return base;
  return NULL_TREE;
}

/* The slot of DR's reference that holds its base, an array (or a
   structure) of static storage the function names directly, or NULL.
   Reached through MEM[&decl], which GCC doesn't fold back into the decl
   while it carries a dependence clique, such a reference can take one:
   NPB SP's lhs, rhs and u are global arrays it updates in place, plane
   i from planes i + 1 and i + 2.  */
static tree *
e2k_av_decl_slot (data_reference *dr)
{
  tree t = DR_REF (dr), *slot = NULL;
  while (handled_component_p (t))
    {
      slot = &TREE_OPERAND (t, 0);
      t = *slot;
    }
  /* Already MEM[&decl] (an earlier instance of the pass, or a loop
     versioned before its inner loops were unrolled).  */
  if (slot && TREE_CODE (t) == MEM_REF
      && TREE_CODE (TREE_OPERAND (t, 0)) == ADDR_EXPR
      && integer_zerop (TREE_OPERAND (t, 1)))
    t = TREE_OPERAND (TREE_OPERAND (t, 0), 0);
  if (!slot || !VAR_P (t) || !is_global_var (t) || TREE_THIS_VOLATILE (t)
      || DECL_HARD_REGISTER (t) || DECL_THREAD_LOCAL_P (t))
    return NULL;
  return slot;
}

/* Whether array references A and B, through one object with the same
   array types, never touch the same element in LOOP: in some dimension
   both indices are invariant in it and differ by a constant (NPB SP's
   "rhs[m][i][j][k]" against "rhs[m][i1][j][k]", i1 = i + 1 set outside
   the loop, which the dependence test, reading the loop alone, takes for
   two unrelated values).  Other dimensions can't make up the difference
   when the indices stay in bounds, as the dependence test assumes.  */
static bool
e2k_av_apart_p (class loop *loop, tree a, tree b,
		hash_map<tree, name_expansion *> **cache)
{
  bool apart = false;
  while (TREE_CODE (a) == ARRAY_REF && TREE_CODE (b) == ARRAY_REF)
    {
      tree ia = TREE_OPERAND (a, 1), ib = TREE_OPERAND (b, 1);
      tree type = TREE_TYPE (ia);
      if (!types_compatible_p (TREE_TYPE (TREE_OPERAND (a, 0)),
			       TREE_TYPE (TREE_OPERAND (b, 0))))
	return false;
      if (!apart && INTEGRAL_TYPE_P (type)
	  && types_compatible_p (type, TREE_TYPE (ib))
	  && expr_invariant_in_loop_p (loop, ia)
	  && expr_invariant_in_loop_p (loop, ib))
	{
	  aff_tree fa, fb;
	  tree_to_aff_combination_expand (ia, type, &fa, cache);
	  tree_to_aff_combination_expand (ib, type, &fb, cache);
	  aff_combination_scale (&fb, -1);
	  aff_combination_add (&fa, &fb);
	  apart = fa.n == 0 && !fa.rest && maybe_ne (fa.offset, 0);
	}
      a = TREE_OPERAND (a, 0);
      b = TREE_OPERAND (b, 0);
    }
  /* MEM[&decl] as an earlier instance of the pass left it: its clique
     and base keep operand_equal_p from seeing the same object.  */
  auto obj = [] (tree t)
    {
      if (TREE_CODE (t) == MEM_REF
	  && TREE_CODE (TREE_OPERAND (t, 0)) == ADDR_EXPR
	  && integer_zerop (TREE_OPERAND (t, 1)))
	return TREE_OPERAND (TREE_OPERAND (t, 0), 0);
      return t;
    };
  return apart && operand_equal_p (obj (a), obj (b), 0);
}

/* In a one-block loop, a load from an address the loop doesn't step
   (DR_STEP 0) that one store of the loop may write, an element of the
   same type, can be a register instead: loaded before the loop, and
   after the store given the stored value when the store's address is
   its own (PolyBench's floyd-warshall, "path[i][j] = min (path[i][j],
   path[i][k] + path[k][j])": path[i][k] is written once, at j == k).
   The memory dependence that made every iteration wait for the last
   one's store becomes a compare and a select; the loop can then be
   versioned for the other pairs (e2k_av_loop) and pipelined.  lcc
   speculates such loads instead (lock loads checked each iteration).
   LOOP is innermost; its body is its header, with an empty latch or as
   the latch.  True if it changed the loop.  */
static bool
e2k_av_forward (class loop *loop)
{
  basic_block h = loop->header;
  if (loop->num_nodes > 2
      || (loop->num_nodes == 2 && !empty_block_p (loop->latch))
      || !single_succ_p (loop_preheader_edge (loop)->src))
    return false;
  auto_vec<loop_p, 3> nest;
  auto_vec<data_reference_p> drs;
  auto_vec<ddr_p> ddrs;
  if (!compute_data_dependences_for_loop (loop, false, &nest, &drs, &ddrs))
    {
      free_dependence_relations (ddrs);
      free_data_refs (drs);
      return false;
    }
  /* Statement order in the block.  */
  hash_map<gimple *, int> pos;
  int n = 0;
  for (gimple_stmt_iterator g = gsi_start_bb (h); !gsi_end_p (g); gsi_next (&g))
    pos.put (gsi_stmt (g), n++);
  gimple *ls = NULL, *ss = NULL;
  for (data_reference_p ld : drs)
    {
      gimple *s = DR_STMT (ld);
      if (!DR_IS_READ (ld) || !DR_STEP (ld) || !integer_zerop (DR_STEP (ld))
	  || gimple_bb (s) != h || !gimple_assign_single_p (s)
	  || TREE_CODE (gimple_assign_lhs (s)) != SSA_NAME
	  || gimple_has_volatile_ops (s))
	continue;
      tree lref = gimple_assign_rhs1 (s);
      tree type = TREE_TYPE (lref);
      unsigned HOST_WIDE_INT size;
      if (!expr_invariant_in_loop_p (loop, build_fold_addr_expr
				     (unshare_expr (lref)))
	  || !tree_fits_uhwi_p (TYPE_SIZE_UNIT (type))
	  || (size = tree_to_uhwi (TYPE_SIZE_UNIT (type))) == 0
	  || get_object_alignment (lref) < size * BITS_PER_UNIT)
	continue;
      /* The one store that may write it, after it in the block, of the
	 same type and alignment: it writes the whole element or none.  */
      gimple *st = NULL;
      bool ok = true;
      for (ddr_p ddr : ddrs)
	{
	  data_reference_p o = (DDR_A (ddr) == ld ? DDR_B (ddr)
				: DDR_B (ddr) == ld ? DDR_A (ddr) : NULL);
	  if (!o || !DR_IS_WRITE (o) || DDR_ARE_DEPENDENT (ddr) == chrec_known)
	    continue;
	  /* Only a store stepping through the element's own array (the same
	     base): a run-time check against it would always fail.  Others
	     are versioning's, whose disjoint copy then keeps the element in
	     a register with no recurrence (PolyBench's gemm, A[i][k]
	     against C[i][j]: 20 times slower this way), as is a store to
	     the element itself each iteration (a sum kept in memory, which
	     the copy's LIM keeps in a register).  */
	  if (st && st != DR_STMT (o))
	    ok = false;
	  if (!DR_STEP (o) || integer_zerop (DR_STEP (o))
	      || !DR_BASE_ADDRESS (o) || !DR_BASE_ADDRESS (ld)
	      || !operand_equal_p (DR_BASE_ADDRESS (o), DR_BASE_ADDRESS (ld), 0))
	    ok = false;
	  st = DR_STMT (o);
	}
      if (!ok || !st)
	continue;
      tree sref = gimple_assign_lhs (st);
      tree val = gimple_assign_rhs1 (st);
      if (gimple_bb (st) != h || !gimple_assign_single_p (st)
	  || gimple_has_volatile_ops (st)
	  || !types_compatible_p (TREE_TYPE (sref), type)
	  || get_object_alignment (sref) < size * BITS_PER_UNIT
	  || (TREE_CODE (val) != SSA_NAME && !is_gimple_min_invariant (val))
	  || *pos.get (st) <= *pos.get (s))
	continue;
      ls = s;
      ss = st;
      break;
    }
  free_dependence_relations (ddrs);
  free_data_refs (drs);
  if (!ls)
    return false;

  tree lref = gimple_assign_rhs1 (ls), type = TREE_TYPE (lref);
  tree sref = gimple_assign_lhs (ss), val = gimple_assign_rhs1 (ss);
  /* Before the loop: the element and its address.  */
  edge pe = loop_preheader_edge (loop);
  gimple_seq pre = NULL;
  tree la = force_gimple_operand (build_fold_addr_expr (unshare_expr (lref)),
				  &pre, true, NULL_TREE);
  tree r0 = make_ssa_name (type);
  gimple_seq_add_stmt (&pre, gimple_build_assign (r0, unshare_expr (lref)));
  gsi_insert_seq_on_edge_immediate (pe, pre);
  pe = loop_preheader_edge (loop);
  /* The register through the iterations.  */
  tree r = make_ssa_name (type);
  tree rn = make_ssa_name (type);
  gphi *phi = create_phi_node (r, h);
  add_phi_arg (phi, r0, pe, UNKNOWN_LOCATION);
  add_phi_arg (phi, rn, loop_latch_edge (loop), UNKNOWN_LOCATION);
  /* The load reads it.  */
  gimple_stmt_iterator gl = gsi_for_stmt (ls);
  gimple_assign_set_rhs_from_tree (&gl, r);
  update_stmt (gsi_stmt (gl));
  /* After the store: its value if it wrote the element.  */
  gimple_stmt_iterator gs = gsi_for_stmt (ss);
  gimple_seq post = NULL;
  tree sa = force_gimple_operand (build_fold_addr_expr (unshare_expr (sref)),
				  &post, true, NULL_TREE);
  tree c = make_ssa_name (boolean_type_node);
  gimple_seq_add_stmt (&post, gimple_build_assign (c, EQ_EXPR, sa, la));
  gimple_seq_add_stmt (&post, gimple_build_assign (rn, COND_EXPR, c, val, r));
  gsi_insert_seq_after (&gs, post, GSI_SAME_STMT);
  mark_virtual_operands_for_renaming (cfun);
  update_ssa (TODO_update_ssa_only_virtuals);
  scev_reset_htab ();

  if (dump_file)
    fprintf (dump_file, "e2k: loop %d: a load into a register its store "
	     "updates\n", loop->num);
  return true;
}

/* Whether integer T is computed from no pointer: constants, integers
   narrower than a pointer, and arithmetic on such values, through
   PHIs (DEPTH bounds the search).  */
static bool
e2k_pointer_free_p (tree t, hash_set<tree> &seen, int depth)
{
  if (TREE_CODE (t) == INTEGER_CST)
    return true;
  if (TREE_CODE (t) != SSA_NAME || !INTEGRAL_TYPE_P (TREE_TYPE (t))
      || depth > 12)
    return false;
  if (TYPE_PRECISION (TREE_TYPE (t)) < POINTER_SIZE)
    return true;
  if (seen.add (t))
    return true;
  gimple *d = SSA_NAME_DEF_STMT (t);
  if (gphi *phi = dyn_cast <gphi *> (d))
    {
      for (unsigned k = 0; k < gimple_phi_num_args (phi); k++)
	if (!e2k_pointer_free_p (gimple_phi_arg_def (phi, k), seen, depth + 1))
	  return false;
      return true;
    }
  if (!is_gimple_assign (d) || gimple_assign_load_p (d))
    return false;
  switch (gimple_assign_rhs_code (d))
    {
    case PLUS_EXPR: case MINUS_EXPR: case MULT_EXPR: case LSHIFT_EXPR:
    CASE_CONVERT:
      for (unsigned k = 1; k < gimple_num_ops (d); k++)
	if (!e2k_pointer_free_p (gimple_op (d, k), seen, depth + 1))
	  return false;
      return true;
    default:
      return false;
    }
}

/* LIM rewrites the pointer arithmetic it hoists into unsigned integer
   arithmetic (rewrite_to_defined_unconditional), and the pointers it
   then converts the sums to point anywhere: NPB FT's evolve, inlined
   with its arrays u0 and u1, reads "(dcomplex (*)[256][256])
   ((unsigned long) &u0 + k * 1048576)", to which PRE adds "nonlocal",
   so that the pipeliner took it to alias every store through u1 (ivopts
   passes the set on).  Give back what the pointer arithmetic had, the
   object alone, to a pointer converted from &DECL plus an integer
   computed from no pointer.  */
static void
e2k_restore_pt (function *fun)
{
  unsigned i;
  tree name;
  auto addr_decl = [] (tree t) -> tree
    {
      if (TREE_CODE (t) != SSA_NAME)
	return NULL_TREE;
      gimple *d = SSA_NAME_DEF_STMT (t);
      if (!is_gimple_assign (d)
	  || !CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (d)))
	return NULL_TREE;
      tree a = gimple_assign_rhs1 (d);
      if (TREE_CODE (a) != ADDR_EXPR)
	return NULL_TREE;
      tree v = TREE_OPERAND (a, 0);
      return VAR_P (v) && !DECL_EXTERNAL (v) ? v : NULL_TREE;
    };
  FOR_EACH_SSA_NAME (i, name, fun)
    {
      if (!POINTER_TYPE_P (TREE_TYPE (name)))
	continue;
      gimple *d = SSA_NAME_DEF_STMT (name);
      if (!is_gimple_assign (d)
	  || !CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (d))
	  || TREE_CODE (gimple_assign_rhs1 (d)) != SSA_NAME)
	continue;
      gimple *dx = SSA_NAME_DEF_STMT (gimple_assign_rhs1 (d));
      if (!is_gimple_assign (dx) || gimple_assign_rhs_code (dx) != PLUS_EXPR)
	continue;
      tree a = gimple_assign_rhs1 (dx), b = gimple_assign_rhs2 (dx);
      tree decl = addr_decl (a), off = b;
      if (!decl)
	{
	  decl = addr_decl (b);
	  off = a;
	}
      hash_set<tree> seen;
      if (!decl || !e2k_pointer_free_p (off, seen, 0))
	continue;
      /* PRE adds "nonlocal" to what LIM's pointer had (NPB FT); keep a
	 set that doesn't hold the object, which something else gave.  */
      struct ptr_info_def *pi = SSA_NAME_PTR_INFO (name);
      if (pi && !pi->pt.anything
	  && (!pi->pt.vars || !bitmap_bit_p (pi->pt.vars, DECL_PT_UID (decl))))
	continue;
      pi = get_ptr_info (name);
      pt_solution_set_var (&pi->pt, decl);
      if (dump_file)
	{
	  fprintf (dump_file, "e2k: ");
	  print_generic_expr (dump_file, name);
	  fprintf (dump_file, " points to ");
	  print_generic_expr (dump_file, decl);
	  fprintf (dump_file, "\n");
	}
    }
}

/* In an innermost loop, a branch around loads from memory that the
   join then stores to on every path (lame's count_bits, "ix[k] = (xr[k]
   >= roundfac) ? ix[k] : 0": GIMPLE loads ix[k] only where the condition
   holds and stores the PHI of it and 0).  The loads can't fault, so they
   may run always: they move above the branch, the PHIs become selects
   and the loop one block, which RTL if-conversion doesn't make (it can't
   tell the loads are safe) and e2k_modsched can pipeline; branchy and
   unrolled, the loop took 13 cycles an element on the 8C2.  True if it
   changed LOOP; the caller cleans up the CFG.  */
static bool
e2k_cond_loads (class loop *loop)
{
  bool changed = false;
  basic_block *bbs = get_loop_body (loop);
  for (unsigned i = 0; i < loop->num_nodes; i++)
    {
      basic_block c = bbs[i];
      gcond *cs = safe_dyn_cast <gcond *> (*gsi_last_bb (c));
      if (!cs || EDGE_COUNT (c->succs) != 2)
	continue;
      /* A: the arm; J: the join.  */
      edge ea = NULL, ej = NULL;
      for (int k = 0; k < 2 && !ea; k++)
	{
	  edge e = EDGE_SUCC (c, k), o = EDGE_SUCC (c, 1 - k);
	  if (single_pred_p (e->dest) && single_succ_p (e->dest)
	      && single_succ (e->dest) == o->dest)
	    {
	      ea = e;
	      ej = o;
	    }
	}
      if (!ea)
	continue;
      basic_block a = ea->dest, j = ej->dest;
      if (!flow_bb_inside_loop_p (loop, a) || !flow_bb_inside_loop_p (loop, j)
	  || EDGE_COUNT (j->preds) != 2
	  || ((ea->flags | ej->flags | single_succ_edge (a)->flags)
	      & EDGE_COMPLEX))
	continue;
      bool ok = true;
      for (gphi_iterator gp = gsi_start_phis (j); !gsi_end_p (gp); gsi_next (&gp))
	if (virtual_operand_p (gimple_phi_result (gp.phi ())))
	  ok = false;
      /* A: only loads, each from memory J stores to before any call.  */
      int nl = 0;
      for (gimple_stmt_iterator g = gsi_start_bb (a); ok && !gsi_end_p (g);
	   gsi_next (&g))
	{
	  gimple *s = gsi_stmt (g);
	  if (is_gimple_debug (s))
	    continue;
	  if (!gimple_assign_load_p (s) || gimple_has_volatile_ops (s)
	      || gimple_vdef (s)
	      || TREE_CODE (gimple_assign_lhs (s)) != SSA_NAME)
	    {
	      ok = false;
	      break;
	    }
	  tree ref = gimple_assign_rhs1 (s);
	  bool stored = false;
	  for (gimple_stmt_iterator t = gsi_start_bb (j); !gsi_end_p (t);
	       gsi_next (&t))
	    {
	      gimple *u = gsi_stmt (t);
	      if (is_gimple_call (u) || gimple_has_volatile_ops (u))
		break;
	      if (gimple_store_p (u) && gimple_assign_single_p (u)
		  && operand_equal_p (gimple_assign_lhs (u), ref, 0))
		{
		  stored = true;
		  break;
		}
	    }
	  ok = stored;
	  nl++;
	}
      if (!ok || nl == 0)
	continue;

      /* The condition as a value, then the loads before the branch.  */
      tree cv = make_ssa_name (boolean_type_node);
      gimple_stmt_iterator gc = gsi_for_stmt (cs);
      gsi_insert_before (&gc, gimple_build_assign (cv, gimple_cond_code (cs),
						   gimple_cond_lhs (cs),
						   gimple_cond_rhs (cs)),
			 GSI_SAME_STMT);
      for (gimple_stmt_iterator g = gsi_start_bb (a); !gsi_end_p (g); )
	{
	  gimple *s = gsi_stmt (g);
	  if (is_gimple_debug (s))
	    {
	      gsi_remove (&g, true);
	      continue;
	    }
	  gsi_move_before (&g, &gc);
	}
      /* The PHIs: the arm's value where the branch went to it.  */
      bool to_a = (ea->flags & EDGE_TRUE_VALUE) != 0;
      edge fa = single_succ_edge (a);
      gimple_stmt_iterator gj = gsi_after_labels (j);
      for (gphi_iterator gp = gsi_start_phis (j); !gsi_end_p (gp); )
	{
	  gphi *phi = gp.phi ();
	  tree res = gimple_phi_result (phi);
	  tree va = PHI_ARG_DEF_FROM_EDGE (phi, fa);
	  tree vc = PHI_ARG_DEF_FROM_EDGE (phi, ej);
	  remove_phi_node (&gp, false);
	  gimple *sel = gimple_build_assign (res, COND_EXPR, cv,
					     to_a ? va : vc, to_a ? vc : va);
	  SSA_NAME_DEF_STMT (res) = sel;
	  gsi_insert_before (&gj, sel, GSI_SAME_STMT);
	}
      /* Always to J; the cleanup removes A.  */
      if (ej->flags & EDGE_TRUE_VALUE)
	gimple_cond_make_true (cs);
      else
	gimple_cond_make_false (cs);
      update_stmt (cs);
      changed = true;
      if (dump_enabled_p ())
	dump_printf_loc (MSG_OPTIMIZED_LOCATIONS, cs,
			 "loop %d: %d loads of bb %d run always\n",
			 loop->num, nl, a->index);
    }
  free (bbs);
  return changed;
}

static bool
e2k_av_loop (function *fun, class loop *loop)
{
  if (loop->inner || !single_exit (loop) || !optimize_loop_for_speed_p (loop)
      || loop->dont_vectorize
      || fun->machine->n_av_cliques == ARRAY_SIZE (fun->machine->av_cliques)
      || fun->machine->n_ov_cliques == ARRAY_SIZE (fun->machine->ov_cliques))
    return false;
  auto why = [&] (const char *w)
    {
      if (dump_file)
	fprintf (dump_file, "e2k: loop %d not versioned: %s\n", loop->num, w);
      return false;
    };
  tree niters = number_of_latch_executions (loop);
  if (!niters || niters == chrec_dont_know)
    return why ("count unknown");

  basic_block *bbs = get_loop_body (loop);
  bool call = false;
  for (unsigned i = 0; i < loop->num_nodes && !call; i++)
    for (gimple_stmt_iterator gsi = gsi_start_bb (bbs[i]); !gsi_end_p (gsi);
	 gsi_next (&gsi))
      if (is_gimple_call (gsi_stmt (gsi))
	  || gimple_has_volatile_ops (gsi_stmt (gsi)))
	{
	  call = true;
	  break;
	}
  free (bbs);
  if (call)
    return why ("a call");

  auto_vec<loop_p, 3> nest;
  auto_vec<data_reference_p> drs;
  auto_vec<ddr_p> ddrs;
  /* With read-read pairs too, for the subgroups below.  */
  bool ok = compute_data_dependences_for_loop (loop, true, &nest, &drs, &ddrs);
  /* Group the references by base address.  A declared array (MG's
     local u1[]) can't take a clique, but needs none if the dependence
     test has told it apart from every other array already (DECL).  */
  auto_vec<int> group;
  auto_vec<bool> decl, tag;
  bool write = false;
  for (unsigned i = 0; ok && i < drs.length (); i++)
    {
      data_reference *dr = drs[i];
      tree b = get_base_address (DR_REF (dr));
      decl.safe_push (b && DECL_P (b));
      tag.safe_push (!decl[i] || e2k_av_decl_slot (dr));
      /* A step of 0 too: an element the loop keeps adding to
	 (PolyBench's 2mm, "tmp[i][j] += alpha * A[i][k] * B[k][j]"),
	 which the copy's LIM then keeps in a register, stored after the
	 loop, as lcc's disjoint copy does.  */
      if (!DR_BASE_ADDRESS (dr) || !DR_STEP (dr)
	  || TREE_CODE (DR_STEP (dr)) != INTEGER_CST
	  || (!e2k_av_base_ref (dr) && !decl[i])
	  || !tree_fits_uhwi_p (TYPE_SIZE_UNIT (TREE_TYPE (DR_REF (dr)))))
	{
	  if (dump_file)
	    {
	      fprintf (dump_file, "e2k: loop %d: reference ", loop->num);
	      print_generic_expr (dump_file, DR_REF (dr));
	      fprintf (dump_file, "\n");
	    }
	  ok = false;
	  break;
	}
      write |= DR_IS_WRITE (dr);
      /* An element the loop doesn't step through is a group of its own
	 (PolyBench's cholesky, "A[i][j] -= A[i][k] * A[j][k]": A[i][j]
	 against the row it reads), checked against the rest of its
	 array like another array.  */
      bool z = integer_zerop (DR_STEP (dr));
      unsigned g = i;
      for (unsigned k = 0; k < i; k++)
	if (operand_equal_p (DR_BASE_ADDRESS (drs[k]), DR_BASE_ADDRESS (dr), 0)
	    && z == (bool) integer_zerop (DR_STEP (drs[k]))
	    && (!z
		|| (operand_equal_p (DR_OFFSET (drs[k]), DR_OFFSET (dr), 0)
		    && operand_equal_p (DR_INIT (drs[k]), DR_INIT (dr), 0))))
	  {
	    g = group[k];
	    break;
	  }
      group.safe_push (g);
    }
  ok &= write;

  hash_map<data_reference_p, unsigned> index;
  for (unsigned i = 0; ok && i < drs.length (); i++)
    index.put (drs[i], i);
  /* Within a group, the references the dependence test told apart over
     the whole loop get bases of their own: a subgroup is a set of
     references that may depend on each other (PolyBench's seidel-2d
     updates A in place, "A[i][j] = (A[i-1][j-1] + ... + A[i+1][j+1]) /
     9": the store to row i never writes rows i-1 and i+1, which lcc
     loads with no checks, while e2k_ms_dam checked them after every
     store).  SPLIT if one separates a store from another reference.  */
  auto_vec<unsigned> sub;
  for (unsigned i = 0; ok && i < drs.length (); i++)
    sub.safe_push (i);
  auto find = [&] (unsigned i)
    {
      while (sub[i] != i)
	i = sub[i] = sub[sub[i]];
      return i;
    };
  hash_map<tree, name_expansion *> *cache = NULL;
  for (unsigned i = 0; ok && i < ddrs.length (); i++)
    {
      unsigned ia = *index.get (DDR_A (ddrs[i]));
      unsigned ib = *index.get (DDR_B (ddrs[i]));
      if (DDR_ARE_DEPENDENT (ddrs[i]) != chrec_known
	  && group[ia] == group[ib]
	  && !e2k_av_apart_p (loop, DR_REF (drs[ia]), DR_REF (drs[ib]),
			      &cache))
	{
	  unsigned ra = find (ia), rb = find (ib);
	  sub[MAX (ra, rb)] = MIN (ra, rb);
	}
    }
  free_affine_expand_cache (&cache);
  bool split = false;
  for (unsigned i = 0; ok && i < drs.length (); i++)
    for (unsigned k = 0; k < drs.length (); k++)
      if (DR_IS_WRITE (drs[i]) && tag[i] && tag[k]
	  && group[i] == group[k] && find (i) != find (k))
	split = true;

  /* Give reference I base FIND (I) + 1 in CLIQUE (a declared array's
     through MEM[&decl]).  */
  auto tag_ref = [&] (unsigned i, unsigned short clique)
    {
      tree base;
      if (decl[i])
	{
	  tree *slot = e2k_av_decl_slot (drs[i]);
	  if (!slot)
	    return;
	  tree d = *slot;
	  if (TREE_CODE (d) == MEM_REF)
	    base = d;
	  else
	    {
	      TREE_ADDRESSABLE (d) = 1;
	      base = build2 (MEM_REF, TREE_TYPE (d), build_fold_addr_expr (d),
			     build_int_cst (reference_alias_ptr_type (d), 0));
	      *slot = base;
	      update_stmt (DR_STMT (drs[i]));
	    }
	}
      else
	base = e2k_av_base_ref (drs[i]);
      MR_DEPENDENCE_CLIQUE (base) = clique;
      MR_DEPENDENCE_BASE (base) = find (i) + 1;
    };

  auto_vec<dr_with_seg_len_pair_t> pairs;
  tree n = fold_convert (sizetype, niters);
  for (unsigned i = 0; ok && i < ddrs.length (); i++)
    {
      ddr_p ddr = ddrs[i];
      data_reference *a = DDR_A (ddr), *b = DDR_B (ddr);
      if (DDR_ARE_DEPENDENT (ddr) == chrec_known)
	continue;
      unsigned ia = *index.get (a), ib = *index.get (b);
      if (group[ia] == group[ib])
	continue;
      if (!DR_IS_WRITE (a) && !DR_IS_WRITE (b))
	continue;
      if (decl[ia] || decl[ib])
	{
	  why ("a declared array that may overlap another");
	  ok = false;
	  break;
	}
      /* Different bases that are known to depend on each other; but
	 an element against the rest of its array may well not overlap
	 it (the dependence test can't tell "k < j" there).  */
      bool same = operand_equal_p (DR_BASE_ADDRESS (a), DR_BASE_ADDRESS (b), 0);
      if (DDR_ARE_DEPENDENT (ddr) != chrec_dont_know && !same)
	{
	  why ("dependent references");
	  ok = false;
	  break;
	}
      unsigned HOST_WIDE_INT sa
	= tree_to_uhwi (TYPE_SIZE_UNIT (TREE_TYPE (DR_REF (a))));
      unsigned HOST_WIDE_INT sb
	= tree_to_uhwi (TYPE_SIZE_UNIT (TREE_TYPE (DR_REF (b))));
      pairs.safe_push (dr_with_seg_len_pair_t
		       (dr_with_seg_len (a, e2k_av_segment (loop, a, n), sa,
					 TYPE_ALIGN_UNIT (TREE_TYPE (DR_REF (a)))),
			dr_with_seg_len (b, e2k_av_segment (loop, b, n), sb,
					 TYPE_ALIGN_UNIT (TREE_TYPE (DR_REF (b)))),
			dr_with_seg_len_pair_t::REORDERED));
    }
  if (ok && !pairs.is_empty ())
    {
      /* One pass merges neighbours only: zlib's from[0..2] against
	 out[0..2] come out as three checks of out[k] against from[0..2];
	 a second pass makes them one.  */
      unsigned before;
      do
	{
	  before = pairs.length ();
	  prune_runtime_alias_test_list (&pairs, tree_fits_uhwi_p (niters)
					 ? tree_to_uhwi (niters) : 1);
	}
      while (pairs.length () < before);
      /* MG's resid: its rows against a[0], a[2] and a[3] (a step of 0,
	 each a group of its own) and two other rows, 5.  */
      ok = pairs.length () <= 8;
      if (!ok)
	why ("more than 8 checks");
    }
  else if (ok && split)
    {
      /* Nothing to check: the subgroups as bases of a clique of the loop
	 itself.  */
      unsigned short clique = get_new_clique (fun);
      loop->owned_clique = clique;
      machine_function *m = fun->machine;
      m->av_cliques[m->n_av_cliques++] = clique;
      for (unsigned i = 0; i < drs.length (); i++)
	tag_ref (i, clique);
      if (dump_file)
	fprintf (dump_file, "e2k: loop %d: references told apart\n",
		 loop->num);
      ok = false;
    }
  else
    {
      if (ok)
	why ("nothing to check");
      ok = false;
    }

  if (ok)
    {
      tree cond = NULL_TREE;
      gimple_seq stmts = NULL;
      create_runtime_alias_checks (loop, &pairs, &cond);
      cond = force_gimple_operand_1 (cond, &stmts, is_gimple_val, NULL_TREE);
      profile_probability prob
	= profile_probability::guessed_always ().apply_scale (9, 10);
      basic_block cond_bb;
      initialize_original_copy_tables ();
      class loop *nloop = loop_version (loop, cond, &cond_bb, prob,
					prob.invert (), prob, prob.invert (),
					true);
      free_original_copy_tables ();
      if (!nloop)
	ok = false;
      else
	{
	  nloop->dont_vectorize = true;
	  loop->dont_vectorize = true;
	  if (stmts)
	    {
	      gimple_stmt_iterator gsi = gsi_last_bb (cond_bb);
	      gsi_insert_seq_before (&gsi, stmts, GSI_SAME_STMT);
	    }
	  update_ssa (TODO_update_ssa_no_phi);
	  /* LOOP is the copy the test chose for disjoint arrays.  */
	  unsigned short clique = get_new_clique (fun);
	  loop->owned_clique = clique;
	  machine_function *m = fun->machine;
	  m->av_cliques[m->n_av_cliques++] = clique;
	  for (unsigned i = 0; i < drs.length (); i++)
	    tag_ref (i, clique);
	  /* NLOOP runs when the arrays may overlap, as they then mostly
	     do (zlib's copies of distance 1 or 2): a clique of its own,
	     one base for all, which tells the alias oracle nothing.  */
	  unsigned short ov = get_new_clique (fun);
	  nloop->owned_clique = ov;
	  m->ov_cliques[m->n_ov_cliques++] = ov;
	  basic_block *bbs = get_loop_body (nloop);
	  for (unsigned b = 0; b < nloop->num_nodes; b++)
	    for (gimple_stmt_iterator gsi = gsi_start_bb (bbs[b]);
		 !gsi_end_p (gsi); gsi_next (&gsi))
	      if (is_gimple_assign (gsi_stmt (gsi)))
		for (unsigned k = 0; k < gimple_num_ops (gsi_stmt (gsi)); k++)
		  {
		    tree op = gimple_op (gsi_stmt (gsi), k);
		    tree base = op ? get_base_address (op) : NULL_TREE;
		    if (base && (TREE_CODE (base) == MEM_REF
				 || TREE_CODE (base) == TARGET_MEM_REF))
		      {
			MR_DEPENDENCE_CLIQUE (base) = ov;
			MR_DEPENDENCE_BASE (base) = 1;
		      }
		  }
	  free (bbs);
	  if (dump_file)
	    fprintf (dump_file, "e2k: versioned loop %d for aliasing "
		     "(%u checks), copy %d\n", loop->num, pairs.length (),
		     nloop->num);
	}
    }
  free_dependence_relations (ddrs);
  free_data_refs (drs);
  return ok;
}

namespace {

const pass_data pass_data_e2k_alias_version =
{
  GIMPLE_PASS,
  "e2k_alias_version",
  OPTGROUP_LOOP,
  TV_NONE,
  (PROP_cfg | PROP_ssa),
  0, 0, 0, 0
};

const pass_data pass_data_e2k_alias_version_late =
{
  GIMPLE_PASS,
  "e2k_alias_version_late",
  OPTGROUP_LOOP,
  TV_NONE,
  (PROP_cfg | PROP_ssa),
  0, 0, 0, 0
};

/* The innermost loops (by number) of function E2K_AV_FN at the end of
   the early instance, which the late one leaves alone.  */
static function *e2k_av_fn;
static bitmap e2k_av_seen;
static bitmap_obstack e2k_av_obstack;

/* The pass runs twice: after the vectorizer, before predictive commoning
   and complete unrolling (PolyBench's adi, jacobi-2d and heat-3d pipeline
   only so), and after SLP for the loops that became innermost since,
   once cunroll unrolled their small inner loops (NPB SP's sweeps over
   five planes: their "for (m = 0; m < 3; m++)" loops, innermost early,
   got a clique each, and the k loop around them none, so that its
   references told nothing about each other).  */
class pass_e2k_alias_version : public gimple_opt_pass
{
  bool late;
public:
  pass_e2k_alias_version (gcc::context *ctxt, bool late)
    : gimple_opt_pass (late ? pass_data_e2k_alias_version_late
		       : pass_data_e2k_alias_version, ctxt),
      late (late)
  {}

  bool gate (function *) final override
  {
    return e2k_alias_version && optimize >= 2 && flag_tree_loop_optimize;
  }

  unsigned int execute (function *fun) final override
  {
    if (!e2k_av_seen)
      {
	bitmap_obstack_initialize (&e2k_av_obstack);
	e2k_av_seen = BITMAP_ALLOC (&e2k_av_obstack);
      }
    if (late && e2k_av_fn != fun)
      return 0;
    if (!late)
      {
	e2k_av_fn = fun;
	bitmap_clear (e2k_av_seen);
      }
    if (number_of_loops (fun) <= 1)
      return 0;
    bool changed = false;
    if (!late)
      {
	e2k_restore_pt (fun);
	if (e2k_cond_loads_p)
	  {
	    bool cl = false;
	    for (auto loop : loops_list (fun, LI_ONLY_INNERMOST))
	      if (optimize_loop_for_speed_p (loop))
		cl |= e2k_cond_loads (loop);
	    if (cl)
	      {
		cleanup_tree_cfg ();
		scev_reset ();
		changed = true;
	      }
	  }
      }
    calculate_dominance_info (CDI_DOMINATORS);
    for (auto loop : loops_list (fun, LI_ONLY_INNERMOST))
      {
	if (late && bitmap_bit_p (e2k_av_seen, loop->num))
	  continue;
	if (optimize_loop_for_speed_p (loop))
	  changed |= e2k_av_forward (loop);
	changed |= e2k_av_loop (fun, loop);
      }
    /* What this instance saw or made (the copies), for the late one.  */
    if (!late)
      for (auto loop : loops_list (fun, LI_ONLY_INNERMOST))
	bitmap_set_bit (e2k_av_seen, loop->num);
    if (!changed)
      return 0;
    scev_reset ();
    rewrite_into_loop_closed_ssa (NULL, TODO_update_ssa);
    return TODO_cleanup_cfg;
  }
};

} // anon namespace

static gimple_opt_pass *
make_pass_e2k_alias_version (gcc::context *ctxt, bool late)
{
  return new pass_e2k_alias_version (ctxt, late);
}

/* lcc versions straight-line code the same way: NPB BT's binvcrhs, a
   block of 5x5 matrix updates through three pointer arguments, tests
   whether the 200-byte ranges of lhs and c overlap and runs a copy that
   loads everything up front if they don't, the block as written (with
   data speculation) if they do.  Our scheduler could only lock-load each
   load above the stores before it and check it after them, one check a
   wide instruction (spec/isa/speculation.md): 973 instructions a call.
   This late GIMPLE pass versions a block outside loops whose loads
   follow stores through other pointers that may alias them.  The
   pointers are set before the block, the offsets constant; a test of
   the byte ranges the block touches through each picks a copy whose
   references get a base per pointer in a new dependence clique, as
   restrict would give.  Outside loops the block runs once for one set
   of pointer values, so the clique holds wherever later passes copy
   it.  */

/* Loads that must follow a store through another pointer before a
   block is worth two copies.  */
#define E2K_AVB_MIN_LOADS 8

/* A pointer through which a block accesses memory, and the bytes
   [LO, HI) from it that the block touches.  */
struct e2k_avb_group
{
  tree ptr;
  HOST_WIDE_INT lo, hi;
  bool store;
};

/* For a memory reference REF in BB: its MEM_REF, through a pointer no
   statement of BB sets, and the bytes [*LO, *LO + *SIZE) from the
   pointer it touches; else NULL.  */
static tree
e2k_avb_ref (tree ref, basic_block bb, HOST_WIDE_INT *lo, HOST_WIDE_INT *size)
{
  if (TREE_THIS_VOLATILE (ref)
      || (TREE_CODE (ref) == COMPONENT_REF
	  && DECL_BIT_FIELD (TREE_OPERAND (ref, 1)))
      || !tree_fits_uhwi_p (TYPE_SIZE_UNIT (TREE_TYPE (ref))))
    return NULL_TREE;
  poly_int64 off;
  tree base = get_addr_base_and_unit_offset (ref, &off);
  if (!base || TREE_CODE (base) != MEM_REF || !off.is_constant (lo))
    return NULL_TREE;
  tree p = TREE_OPERAND (base, 0);
  if (TREE_CODE (p) != SSA_NAME || !POINTER_TYPE_P (TREE_TYPE (p)))
    return NULL_TREE;
  gimple *d = SSA_NAME_DEF_STMT (p);
  if (!SSA_NAME_IS_DEFAULT_DEF (p) && gimple_code (d) != GIMPLE_PHI
      && gimple_bb (d) == bb)
    return NULL_TREE;
  poly_offset_int mo = mem_ref_offset (base);
  HOST_WIDE_INT m;
  if (!mo.is_constant () || !wi::fits_shwi_p (mo.to_constant ()))
    return NULL_TREE;
  m = mo.to_constant ().to_shwi ();
  *lo += m;
  *size = tree_to_uhwi (TYPE_SIZE_UNIT (TREE_TYPE (ref)));
  if (*size == 0 || *size > 64 || absu_hwi (*lo) > (1 << 20))
    return NULL_TREE;
  return base;
}

/* The memory reference of statement S, and whether it stores.  */
static tree
e2k_avb_stmt_ref (gimple *s, bool *store)
{
  if (!gimple_assign_single_p (s) || gimple_has_volatile_ops (s))
    return NULL_TREE;
  if (gimple_store_p (s))
    {
      *store = true;
      return gimple_assign_lhs (s);
    }
  if (gimple_assign_load_p (s))
    {
      *store = false;
      return gimple_assign_rhs1 (s);
    }
  return NULL_TREE;
}

/* Version block BB of FUN for aliasing; true if it did.  */
static bool
e2k_av_block (function *fun, basic_block bb)
{
  if (bb->loop_father != loops_for_fn (fun)->tree_root
      || !optimize_bb_for_speed_p (bb)
      || fun->machine->n_av_cliques == ARRAY_SIZE (fun->machine->av_cliques))
    return false;
  /* The references in order, each with its group (or -1).  */
  auto_vec<tree> refs;
  auto_vec<int> grp;
  auto_vec<bool> st;
  auto_vec<e2k_avb_group> groups;
  hash_map<tree, int> index;
  unsigned nstmts = 0;
  for (gimple_stmt_iterator g = gsi_start_bb (bb); !gsi_end_p (g); gsi_next (&g))
    {
      gimple *s = gsi_stmt (g);
      if (is_gimple_debug (s))
	continue;
      if (is_gimple_call (s) || gimple_code (s) == GIMPLE_ASM
	  || stmt_could_throw_p (fun, s) || ++nstmts > 4000)
	return false;
      bool store;
      tree ref = e2k_avb_stmt_ref (s, &store);
      if (!ref)
	{
	  if (gimple_vuse (s) && gimple_code (s) != GIMPLE_RETURN)
	    return false;
	  continue;
	}
      HOST_WIDE_INT lo, size;
      tree base = e2k_avb_ref (ref, bb, &lo, &size);
      int k = -1;
      if (base)
	{
	  tree p = TREE_OPERAND (base, 0);
	  bool existed;
	  int &slot = index.get_or_insert (p, &existed);
	  if (!existed)
	    {
	      slot = groups.length ();
	      groups.safe_push ({ p, lo, lo + size, store });
	    }
	  k = slot;
	  e2k_avb_group &gr = groups[k];
	  gr.lo = MIN (gr.lo, lo);
	  gr.hi = MAX (gr.hi, lo + (HOST_WIDE_INT) size);
	  gr.store |= store;
	}
      refs.safe_push (ref);
      grp.safe_push (k);
      st.safe_push (store);
    }
  if (groups.length () < 2 || refs.length () > 2048)
    return false;

  /* Pairs of groups the test must cover: a store through one may touch
     what the other accesses.  Loads that follow such a store are what
     the copy frees.  */
  unsigned ng = groups.length ();
  auto_sbitmap need (ng * ng);
  bitmap_clear (need);
  unsigned freed = 0;
  for (unsigned i = 0; i < refs.length (); i++)
    {
      if (grp[i] < 0)
	continue;
      bool counted = false;
      for (unsigned k = 0; k < refs.length (); k++)
	{
	  if (grp[k] < 0 || grp[k] == grp[i] || !(st[i] || st[k]))
	    continue;
	  unsigned a = MIN (grp[i], grp[k]), b = MAX (grp[i], grp[k]);
	  bool known = bitmap_bit_p (need, a * ng + b);
	  /* A load after a store.  */
	  bool frees = !st[i] && st[k] && k < i && !counted;
	  if (known && !frees)
	    continue;
	  if (!refs_may_alias_p (refs[i], refs[k], true))
	    continue;
	  bitmap_set_bit (need, a * ng + b);
	  if (frees)
	    {
	      freed++;
	      counted = true;
	    }
	}
    }
  unsigned checks = bitmap_count_bits (need);
  if (dump_file)
    fprintf (dump_file, "e2k: block %d: %u pointers, %u loads to free, "
	     "%u checks\n", bb->index, ng, freed, checks);
  if (freed < E2K_AVB_MIN_LOADS || checks == 0 || checks > 8)
    return false;

  /* The test: for each pair, one range ends before the other starts.  */
  auto addr = [&] (unsigned g, HOST_WIDE_INT k)
    {
      return fold_build2 (PLUS_EXPR, sizetype,
			  fold_convert (sizetype, groups[g].ptr), size_int (k));
    };
  tree cond = boolean_true_node;
  for (unsigned a = 0; a < ng; a++)
    for (unsigned b = a + 1; b < ng; b++)
      if (bitmap_bit_p (need, a * ng + b))
	{
	  tree t = fold_build2 (TRUTH_OR_EXPR, boolean_type_node,
				fold_build2 (LE_EXPR, boolean_type_node,
					     addr (a, groups[a].hi),
					     addr (b, groups[b].lo)),
				fold_build2 (LE_EXPR, boolean_type_node,
					     addr (b, groups[b].hi),
					     addr (a, groups[a].lo)));
	  cond = fold_build2 (TRUTH_AND_EXPR, boolean_type_node, cond, t);
	}

  /* BB keeps its labels and PHIs; BODY, the rest, is copied; COND_BB,
     between them, picks one.  */
  basic_block body = split_block_after_labels (bb)->dest;
  basic_block cond_bb = split_edge (single_pred_edge (body));
  basic_block copy;
  if (!gimple_duplicate_seme_region (single_succ_edge (cond_bb), NULL,
				     &body, 1, &copy, false))
    return false;
  edge te = single_succ_edge (cond_bb);
  te->flags = (te->flags & ~EDGE_FALLTHRU) | EDGE_TRUE_VALUE;
  edge fe = make_edge (cond_bb, body, EDGE_FALSE_VALUE);
  te->probability = profile_probability::guessed_always ().apply_scale (9, 10);
  fe->probability = te->probability.invert ();
  copy->count = te->count ();
  body->count = fe->count ();
  gimple_seq stmts = NULL;
  cond = force_gimple_operand (cond, &stmts, true, NULL_TREE);
  gimple_stmt_iterator gsi = gsi_last_bb (cond_bb);
  gsi_insert_seq_after (&gsi, stmts, GSI_CONTINUE_LINKING);
  gsi_insert_after (&gsi, gimple_build_cond (NE_EXPR, cond, boolean_false_node,
					    NULL_TREE, NULL_TREE),
		    GSI_CONTINUE_LINKING);
  free_dominance_info (CDI_DOMINATORS);
  update_ssa (TODO_update_ssa);

  /* The copy's references: a base per pointer.  */
  unsigned short clique = get_new_clique (fun);
  machine_function *m = fun->machine;
  m->av_cliques[m->n_av_cliques++] = clique;
  for (gimple_stmt_iterator g = gsi_start_bb (copy); !gsi_end_p (g);
       gsi_next (&g))
    {
      bool store;
      tree ref = e2k_avb_stmt_ref (gsi_stmt (g), &store);
      HOST_WIDE_INT lo, size;
      tree base = ref ? e2k_avb_ref (ref, copy, &lo, &size) : NULL_TREE;
      int *k = base ? index.get (TREE_OPERAND (base, 0)) : NULL;
      if (k)
	{
	  MR_DEPENDENCE_CLIQUE (base) = clique;
	  MR_DEPENDENCE_BASE (base) = *k + 1;
	}
    }
  if (dump_enabled_p ())
    dump_printf_loc (MSG_OPTIMIZED_LOCATIONS,
		     dump_user_location_t::from_location_t
		     (gimple_location (last_nondebug_stmt (copy))),
		     "versioned block %d for aliasing (%u checks, %u loads "
		     "freed), copy %d\n", body->index, checks, freed,
		     copy->index);
  return true;
}

namespace {

const pass_data pass_data_e2k_block_version =
{
  GIMPLE_PASS,
  "e2k_block_version",
  OPTGROUP_OTHER,
  TV_NONE,
  (PROP_cfg | PROP_ssa),
  0, 0, 0, 0
};

class pass_e2k_block_version : public gimple_opt_pass
{
public:
  pass_e2k_block_version (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_e2k_block_version, ctxt)
  {}

  bool gate (function *) final override
  {
    return e2k_alias_version_block && optimize >= 2;
  }

  unsigned int execute (function *fun) final override
  {
    if (!current_loops || !optimize_function_for_speed_p (fun))
      return 0;
    auto_vec<basic_block> bbs;
    basic_block bb;
    FOR_EACH_BB_FN (bb, fun)
      bbs.safe_push (bb);
    bool changed = false;
    for (basic_block b : bbs)
      changed |= e2k_av_block (fun, b);
    return changed ? TODO_cleanup_cfg : 0;
  }
};

} // anon namespace

static gimple_opt_pass *
make_pass_e2k_block_version (gcc::context *ctxt)
{
  return new pass_e2k_block_version (ctxt);
}

/* ------------------------------------------------------------------ */
/* Copies in the latch                                                 */
/* ------------------------------------------------------------------ */

/* Out-of-SSA leaves the copies of a loop's rotating values in its
   latch, after the exit test (PolyBench's deriche, "xp2 = xp1; yp2 =
   yp1"): the doloop pass then won't count the loop (its latch isn't
   empty), the unroller unrolls it, and e2k_modsched doesn't pipeline it.
   Move them before the exit jump, as e2k_ms_fold_latches does later for
   while loops: each sets a register dead where the loop exits and that
   the jump doesn't read, so running them on the way out too changes
   nothing.  Before the RTL unroller and doloop.  */
static unsigned int
e2k_latch_copies (void)
{
  if (!current_loops)
    return 0;
  df_analyze ();
  for (auto loop : loops_list (cfun, LI_ONLY_INNERMOST))
    {
      basic_block latch = loop->latch;
      if (!latch || latch == loop->header || !single_pred_p (latch)
	  || !single_succ_p (latch))
	continue;
      basic_block p = single_pred (latch);
      rtx_insn *jump = BB_END (p);
      if (!any_condjump_p (jump) || EDGE_COUNT (p->succs) != 2)
	continue;
      edge out = (EDGE_SUCC (p, 0)->dest == latch
		  ? EDGE_SUCC (p, 1) : EDGE_SUCC (p, 0));
      if (flow_bb_inside_loop_p (loop, out->dest)
	  || (out->flags & EDGE_COMPLEX))
	continue;
      bitmap live = df_get_live_in (out->dest);
      auto_vec<rtx_insn *> copies;
      bool ok = true;
      rtx_insn *insn;
      FOR_BB_INSNS (latch, insn)
	{
	  if (!NONDEBUG_INSN_P (insn))
	    continue;
	  if (JUMP_P (insn) && simplejump_p (insn))
	    continue;
	  rtx set = single_set (insn);
	  if (!NONJUMP_INSN_P (insn) || !set
	      || GET_CODE (PATTERN (insn)) != SET
	      || !REG_P (SET_DEST (set)) || !REG_P (SET_SRC (set))
	      || REGNO_REG_SET_P (live, REGNO (SET_DEST (set)))
	      || reg_overlap_mentioned_p (SET_DEST (set), PATTERN (jump)))
	    {
	      ok = false;
	      break;
	    }
	  copies.safe_push (insn);
	}
      if (!ok || copies.is_empty ())
	continue;
      for (rtx_insn *c : copies)
	{
	  rtx_insn *n = emit_insn_before (copy_rtx (PATTERN (c)), jump);
	  INSN_LOCATION (n) = INSN_LOCATION (c);
	  delete_insn (c);
	}
      if (dump_file)
	fprintf (dump_file, ";; e2k_latch_copies: loop %d, %u copies before "
		 "the exit test\n", loop->num, copies.length ());
    }
  return 0;
}

namespace {

const pass_data pass_data_e2k_latch_copies =
{
  RTL_PASS,
  "e2k_latch_copies",
  OPTGROUP_LOOP,
  TV_LOOP,
  0, 0, 0, 0,
  TODO_df_finish
};

class pass_e2k_latch_copies : public rtl_opt_pass
{
public:
  pass_e2k_latch_copies (gcc::context *ctxt)
    : rtl_opt_pass (pass_data_e2k_latch_copies, ctxt)
  {}

  bool gate (function *) final override
  {
    return optimize >= 2 && e2k_latch_copies_p;
  }

  unsigned int execute (function *) final override
  {
    return e2k_latch_copies ();
  }
};

} // anon namespace

static rtl_opt_pass *
make_pass_e2k_latch_copies (gcc::context *ctxt)
{
  return new pass_e2k_latch_copies (ctxt);
}

/* ------------------------------------------------------------------ */
/* Zero extensions under setwd dbl = 1                                 */
/* ------------------------------------------------------------------ */

/* Under dbl = 1 every 32-bit integer ALU operation zero-extends its
   result into the whole register, and loads always do (probed on the 4C
   and the 8C2; FP to integer conversions and movts don't).  After
   register allocation, a zero extension of a register that an operation
   with such a form ("*addsi3_zext" and the like) set earlier in the
   block becomes a copy: the operation is rewritten to set the 64-bit
   register, and the extension copies it, or goes when it extends the
   register in place.  cprop_hardreg then forwards most copies and DCE
   removes them.  REE does part of this, but it takes a 32-bit merge for
   a conditional copy (x86's cmov doesn't extend) and leaves the
   extension in place when it writes another register.  Runs after REE,
   with it (-free).  */

/* The source DEF's SET would have as a 64-bit zero-extended value, or
   NULL.  */
static rtx
e2k_dbl_wide_src (rtx src)
{
  if (GET_CODE (src) == ZERO_EXTEND && MEM_P (XEXP (src, 0)))
    return gen_rtx_ZERO_EXTEND (DImode, XEXP (src, 0));
  if (CONST_INT_P (src))
    return gen_int_mode (UINTVAL (src) & 0xffffffff, DImode);
  if (REG_P (src) || SUBREG_P (src))
    return NULL_RTX;
  return gen_rtx_ZERO_EXTEND (DImode, src);
}

static unsigned int
e2k_dbl_zext (void)
{
  basic_block bb;
  int n = 0;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *insn, *next;
      FOR_BB_INSNS_SAFE (bb, insn, next)
	{
	  if (!NONDEBUG_INSN_P (insn))
	    continue;
	  rtx pat = PATTERN (insn), *setp = &PATTERN (insn);
	  if (GET_CODE (pat) == COND_EXEC)
	    setp = &COND_EXEC_CODE (pat);
	  rtx set = *setp;
	  if (GET_CODE (set) != SET || !REG_P (SET_DEST (set))
	      || GET_MODE (SET_DEST (set)) != DImode
	      || GET_CODE (SET_SRC (set)) != ZERO_EXTEND
	      || !REG_P (XEXP (SET_SRC (set), 0))
	      || GET_MODE (XEXP (SET_SRC (set), 0)) != SImode)
	    continue;
	  rtx narrow = XEXP (SET_SRC (set), 0);
	  unsigned s = REGNO (narrow);
	  if (!GPR_REGNO_P (s))
	    continue;
	  rtx wide = gen_rtx_REG (DImode, s);
	  /* The last insn before that sets S, in this block.  */
	  rtx_insn *def;
	  for (def = PREV_INSN (insn);
	       def && def != PREV_INSN (BB_HEAD (bb)); def = PREV_INSN (def))
	    if (NONDEBUG_INSN_P (def) && reg_set_p (wide, def))
	      break;
	  if (!def || def == PREV_INSN (BB_HEAD (bb)) || CALL_P (def))
	    continue;
	  rtx dset = single_set (def);
	  if (!dset || GET_CODE (PATTERN (def)) == COND_EXEC
	      || !REG_P (SET_DEST (dset)) || REGNO (SET_DEST (dset)) != s)
	    continue;
	  if (GET_MODE (SET_DEST (dset)) == SImode)
	    {
	      rtx src = e2k_dbl_wide_src (SET_SRC (dset));
	      if (!src)
		continue;
	      validate_change (def, &SET_DEST (dset), wide, 1);
	      validate_change (def, &SET_SRC (dset), src, 1);
	    }
	  /* A 64-bit zero extension (a load, or one done already).  */
	  else if (GET_MODE (SET_DEST (dset)) != DImode
		   || GET_CODE (SET_SRC (dset)) != ZERO_EXTEND)
	    continue;
	  /* In place, predicated or not, the extension does nothing now.  */
	  if (REGNO (SET_DEST (set)) == s)
	    {
	      if (!apply_change_group ())
		continue;
	      delete_insn (insn);
	    }
	  else
	    {
	      validate_change (insn, &SET_SRC (set), wide, 1);
	      if (!apply_change_group ())
		continue;
	      remove_reg_equal_equiv_notes (insn);
	      df_insn_rescan (insn);
	    }
	  remove_reg_equal_equiv_notes (def);
	  df_insn_rescan (def);
	  n++;
	}
    }
  if (dump_file)
    fprintf (dump_file, ";; e2k_dbl_zext: %d extensions folded\n", n);
  return 0;
}

namespace {

const pass_data pass_data_e2k_dbl_zext =
{
  RTL_PASS,
  "e2k_dbl_zext",
  OPTGROUP_NONE,
  TV_REE,
  0, 0, 0, 0,
  TODO_df_finish
};

class pass_e2k_dbl_zext : public rtl_opt_pass
{
public:
  pass_e2k_dbl_zext (gcc::context *ctxt)
    : rtl_opt_pass (pass_data_e2k_dbl_zext, ctxt)
  {}

  bool gate (function *) final override
  {
    return optimize >= 2 && flag_ree && e2k_dbl_p ();
  }

  unsigned int execute (function *) final override
  {
    return e2k_dbl_zext ();
  }
};

} // anon namespace

static rtl_opt_pass *
make_pass_e2k_dbl_zext (gcc::context *ctxt)
{
  return new pass_e2k_dbl_zext (ctxt);
}

/* ------------------------------------------------------------------ */
/* Extensions nothing reads the upper half of                          */
/* ------------------------------------------------------------------ */

/* An int lives in a 64-bit register, sign-extended (PROMOTE_MODE), so a
   32-bit operation on it is followed by an extension; ext-dce keeps
   every one whose register is read through a promoted subreg (it takes
   the subreg's promise for a read of the whole register).  A reduction
   then pays a cycle more an iteration than lcc's, which stays in 32
   bits: PolyBench's nussinov, "table[i][j] = max_score (table[i][j],
   table[i][k] + table[k+1][j])", ran cmplsb, merges and sxt, 3 cycles an
   iteration on the 2C3, lcc's cmplsb and merges 2.  After register
   allocation, an extension of a 32-bit register into a 64-bit one whose
   every use (by the DU chains) reads at most its low 32 bits becomes a
   32-bit copy, which cprop_hardreg forwards and the pipeliner folds, or
   goes when it extends in place.  When the only other uses are after
   the loop the extension is in (a sum the function returns), it moves
   to the loop's exits where its register is live: whatever else reaches
   them there is the same variable, extended already, which extending
   again doesn't change.  A call, or anything else in the loop that reads
   the whole register, keeps it.  */
static unsigned int
e2k_narrow_ext (void)
{
  df_chain_add_problem (DF_DU_CHAIN);
  df_rd_add_problem ();
  df_analyze ();
  bool loops = !current_loops;
  bool dom = dom_info_available_p (CDI_DOMINATORS);
  if (loops)
    loop_optimizer_init (AVOID_CFG_MODIFICATIONS);
  basic_block bb;
  int n = 0, moved = 0;
  /* Insns from here on are this pass's, which the chains don't know.  */
  int new_uids = get_max_uid ();
  /* Exit blocks given an extension already, by register.  */
  hash_set<int_hash<int, -1, -2> > done;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *insn, *next;
      FOR_BB_INSNS_SAFE (bb, insn, next)
	{
	  if (!NONDEBUG_INSN_P (insn) || INSN_UID (insn) >= new_uids)
	    continue;
	  rtx set = PATTERN (insn);
	  if (GET_CODE (set) != SET || !REG_P (SET_DEST (set))
	      || GET_MODE (SET_DEST (set)) != DImode
	      || !GPR_REGNO_P (REGNO (SET_DEST (set)))
	      || (GET_CODE (SET_SRC (set)) != SIGN_EXTEND
		  && GET_CODE (SET_SRC (set)) != ZERO_EXTEND)
	      || !REG_P (XEXP (SET_SRC (set), 0))
	      || GET_MODE (XEXP (SET_SRC (set), 0)) != SImode
	      || !GPR_REGNO_P (REGNO (XEXP (SET_SRC (set), 0))))
	    continue;
	  unsigned d = REGNO (SET_DEST (set));
	  df_ref def = NULL, ref;
	  FOR_EACH_INSN_DEF (ref, insn)
	    if (DF_REF_REGNO (ref) == d)
	      def = ref;
	  if (!def)
	    continue;
	  class loop *loop = bb->loop_father;
	  bool in_loop = loop && loop_outer (loop);
	  bool narrow = true, after = false;
	  for (df_link *u = DF_REF_CHAIN (def); u && narrow; u = u->next)
	    {
	      df_ref use = u->ref;
	      rtx_insn *ui = (DF_REF_IS_ARTIFICIAL (use) ? NULL
			      : DF_REF_INSN (use));
	      if (ui && DEBUG_INSN_P (ui))
		continue;
	      /* (DF_REF_REG of a hard register is its natural mode's.)  */
	      rtx r = ui && DF_REF_LOC (use) ? *DF_REF_LOC (use) : NULL_RTX;
	      if (r && !CALL_P (ui)
		  && GET_CODE (PATTERN (ui)) != USE
		  && GET_CODE (PATTERN (ui)) != CLOBBER
		  && known_le (GET_MODE_SIZE (GET_MODE (r)), 4)
		  && (!SUBREG_P (r) || subreg_lowpart_p (r)))
		continue;
	      basic_block ub = DF_REF_BB (use);
	      if (in_loop && ub && !flow_bb_inside_loop_p (loop, ub))
		after = true;
	      else
		narrow = false;
	    }
	  if (!narrow)
	    continue;
	  /* The exits to extend at, where every definition that reaches
	     them is this one or the same extension (a constant that is its
	     own), which extending again doesn't change (a 64-bit variable
	     set from an int here and from a long elsewhere is not).  */
	  auto_vec<basic_block> at;
	  enum rtx_code code = GET_CODE (SET_SRC (set));
	  if (after)
	    for (edge e : get_loop_exit_edges (loop))
	      if (narrow && bitmap_bit_p (df_get_live_in (e->dest), d))
		{
		  if (!single_pred_p (e->dest)
		      || e->dest == EXIT_BLOCK_PTR_FOR_FN (cfun)
		      || (e->flags & EDGE_ABNORMAL))
		    narrow = false;
		  bitmap in = &DF_RD_BB_INFO (e->dest)->in;
		  for (df_ref o = DF_REG_DEF_CHAIN (d); o && narrow;
		       o = DF_REF_NEXT_REG (o))
		    {
		      if (!bitmap_bit_p (in, DF_REF_ID (o)) || o == def)
			continue;
		      rtx os = (DF_REF_IS_ARTIFICIAL (o) ? NULL_RTX
				: single_set (DF_REF_INSN (o)));
		      rtx v = os ? SET_SRC (os) : NULL_RTX;
		      narrow = (os && GET_CODE (PATTERN (DF_REF_INSN (o))) == SET
				&& REG_P (SET_DEST (os))
				&& REGNO (SET_DEST (os)) == d
				&& GET_MODE (SET_DEST (os)) == DImode
				&& ((GET_CODE (v) == code
				     && GET_MODE (XEXP (v, 0)) == SImode)
				    || (CONST_INT_P (v)
					&& INTVAL (v) == (code == SIGN_EXTEND
							  ? (HOST_WIDE_INT) (int32_t) INTVAL (v)
							  : (HOST_WIDE_INT) (uint32_t) INTVAL (v)))));
		    }
		  at.safe_push (e->dest);
		}
	  if (!narrow)
	    continue;
	  rtx src = XEXP (SET_SRC (set), 0);
	  rtx ext = gen_rtx_SET (SET_DEST (set),
				 gen_rtx_fmt_e (GET_CODE (SET_SRC (set)), DImode,
						gen_rtx_REG (SImode, d)));
	  if (REGNO (src) == d)
	    delete_insn (insn);
	  else if (!validate_change (insn, &PATTERN (insn),
				     gen_rtx_SET (gen_rtx_REG (SImode, d), src),
				     0))
	    continue;
	  for (basic_block x : at)
	    if (!done.add (x->index * FIRST_PSEUDO_REGISTER + d))
	      {
		rtx_insn *first = BB_HEAD (x);
		while (first != BB_END (x)
		       && (LABEL_P (first) || NOTE_INSN_BASIC_BLOCK_P (first)))
		  first = NEXT_INSN (first);
		if (LABEL_P (first) || NOTE_INSN_BASIC_BLOCK_P (first))
		  emit_insn_after (copy_rtx (ext), first);
		else
		  emit_insn_before (copy_rtx (ext), first);
		moved++;
	      }
	  n++;
	}
    }
  if (loops)
    loop_optimizer_finalize ();
  /* (The loops' dominators: later passes change the CFG.)  */
  if (!dom)
    free_dominance_info (CDI_DOMINATORS);
  if (dump_file)
    fprintf (dump_file, ";; e2k_narrow_ext: %d extensions narrowed, %d put "
	     "at loop exits\n", n, moved);
  return 0;
}

namespace {

const pass_data pass_data_e2k_narrow_ext =
{
  RTL_PASS,
  "e2k_narrow_ext",
  OPTGROUP_NONE,
  TV_REE,
  0, 0, 0, 0,
  TODO_df_finish
};

class pass_e2k_narrow_ext : public rtl_opt_pass
{
public:
  pass_e2k_narrow_ext (gcc::context *ctxt)
    : rtl_opt_pass (pass_data_e2k_narrow_ext, ctxt)
  {}

  bool gate (function *) final override
  {
    return optimize >= 2 && e2k_narrow_ext_p;
  }

  unsigned int execute (function *) final override
  {
    return e2k_narrow_ext ();
  }
};

} // anon namespace

static rtl_opt_pass *
make_pass_e2k_narrow_ext (gcc::context *ctxt)
{
  return new pass_e2k_narrow_ext (ctxt);
}

/* The same before register allocation, for a 32-bit pseudo that is also
   used as it is, which combine can't fold into its extension: PROMOTE_MODE
   keeps "unsigned len" in a 64-bit pseudo, so "len + 1" compared with a
   limit and assigned back (xz's lzma_memcmplen) is an addition, a compare
   of its 32-bit result and an extension into the variable, an operation
   more on the loop's recurrence.  When the pseudo's only definition has
   a zero-extending form and reads the variable, a 64-bit pseudo takes
   the definition in that form, the extensions copy it, and the other
   uses read its low part; RA then ties the copy.  */
static unsigned int
e2k_dbl_widen (void)
{
  df_analyze ();
  auto_vec<rtx_insn *> zexts;
  basic_block bb;
  rtx_insn *insn;
  FOR_EACH_BB_FN (bb, cfun)
    FOR_BB_INSNS (bb, insn)
      if (NONDEBUG_INSN_P (insn))
	{
	  rtx set = single_set (insn);
	  if (set && GET_CODE (PATTERN (insn)) == SET
	      && REG_P (SET_DEST (set)) && GET_MODE (SET_DEST (set)) == DImode
	      && GET_CODE (SET_SRC (set)) == ZERO_EXTEND
	      && REG_P (XEXP (SET_SRC (set), 0))
	      && GET_MODE (XEXP (SET_SRC (set), 0)) == SImode
	      && !HARD_REGISTER_P (XEXP (SET_SRC (set), 0)))
	    zexts.safe_push (insn);
	}
  int n = 0;
  auto_bitmap done;
  for (rtx_insn *z : zexts)
    {
      /* A copy now if an earlier one widened its register.  */
      if (GET_CODE (SET_SRC (PATTERN (z))) != ZERO_EXTEND)
	continue;
      rtx narrow = XEXP (SET_SRC (PATTERN (z)), 0);
      unsigned s = REGNO (narrow);
      if (bitmap_bit_p (done, s) || DF_REG_DEF_COUNT (s) != 1)
	continue;
      df_ref def = DF_REG_DEF_CHAIN (s);
      if (DF_REF_IS_ARTIFICIAL (def) || DF_REF_FLAGS (def)
	  & (DF_REF_PARTIAL | DF_REF_CONDITIONAL | DF_REF_MAY_CLOBBER))
	continue;
      rtx_insn *x = DF_REF_INSN (def);
      rtx xset = PATTERN (x);
      if (GET_CODE (xset) != SET || SET_DEST (xset) != narrow)
	continue;
      /* Only a recurrence, the definition reading the variable the
	 extension sets (an induction step): elsewhere the extension is
	 off the critical path, and the changed allocation cost Linpack
	 0.27% on the 4C.  */
      rtx src = e2k_dbl_wide_src (SET_SRC (xset));
      if (!src || !reg_mentioned_p (SET_DEST (PATTERN (z)), SET_SRC (xset)))
	continue;
      rtx wide = gen_reg_rtx (DImode);
      rtx low = gen_lowpart_SUBREG (SImode, wide);
      validate_change (x, &SET_DEST (xset), wide, 1);
      validate_change (x, &SET_SRC (xset), src, 1);
      bool ok = true;
      for (df_ref use = DF_REG_USE_CHAIN (s); use && ok;
	   use = DF_REF_NEXT_REG (use))
	{
	  if (DF_REF_IS_ARTIFICIAL (use))
	    {
	      ok = false;
	      break;
	    }
	  rtx_insn *u = DF_REF_INSN (use);
	  rtx uset = single_set (u);
	  if (u == x)
	    ok = false;
	  else if (uset && GET_CODE (PATTERN (u)) == SET
		   && GET_CODE (SET_SRC (uset)) == ZERO_EXTEND
		   && XEXP (SET_SRC (uset), 0) == narrow
		   && GET_MODE (SET_DEST (uset)) == DImode)
	    validate_change (u, &SET_SRC (uset), wide, 1);
	  else
	    validate_replace_rtx_group (narrow, low, u);
	}
      if (!ok || !apply_change_group ())
	{
	  cancel_changes (0);
	  continue;
	}
      bitmap_set_bit (done, s);
      if (dump_file)
	fprintf (dump_file, ";; e2k_dbl_widen: r%u (insn %d) as r%u\n", s,
		 INSN_UID (x), REGNO (wide));
      df_insn_rescan (x);
      for (df_ref use = DF_REG_USE_CHAIN (s), next; use; use = next)
	{
	  next = DF_REF_NEXT_REG (use);
	  df_insn_rescan (DF_REF_INSN (use));
	}
      n++;
    }
  if (dump_file)
    fprintf (dump_file, ";; e2k_dbl_widen: %d pseudos widened\n", n);
  return 0;
}

namespace {

const pass_data pass_data_e2k_dbl_widen =
{
  RTL_PASS,
  "e2k_dbl_widen",
  OPTGROUP_NONE,
  TV_REE,
  0, 0, 0, 0,
  TODO_df_finish
};

class pass_e2k_dbl_widen : public rtl_opt_pass
{
public:
  pass_e2k_dbl_widen (gcc::context *ctxt)
    : rtl_opt_pass (pass_data_e2k_dbl_widen, ctxt)
  {}

  bool gate (function *) final override
  {
    return optimize >= 2 && flag_ree && e2k_dbl_p ();
  }

  unsigned int execute (function *) final override
  {
    return e2k_dbl_widen ();
  }
};

} // anon namespace

static rtl_opt_pass *
make_pass_e2k_dbl_widen (gcc::context *ctxt)
{
  return new pass_e2k_dbl_widen (ctxt);
}

/* Address height.  An E2K access adds a register to a register or a
   constant, and expand builds the address of p->a[x][y] as the chain
   ((x << 7) + y + C) << 2 + p, every operation after the one before:
   five after x, where x is often the last value ready (LZMA's
   GetOptimum: a length clamped to 3 the cycle before).  This pass
   rebuilds such an address from its terms, adding the ones ready
   first and leaving the last one as the access's second register:
   x << 9 alone after x.  Ready times count latencies along the
   definitions within the loop of the access (roughly: loads 3,
   multiplications 4); a register set more than once, as an induction
   variable, or outside the loop is ready at the start.  The terms set
   nowhere in the loop are summed with the constant on the loop's entry
   edge, p + 4C here.  */

struct e2k_ah_term
{
  rtx reg;
  unsigned HOST_WIDE_INT scale;
  int ready;
};

struct e2k_ah_val
{
  int ready;
  rtx x;
};

struct e2k_ah_memo_entry
{
  int loop;
  int ready;
};

static unsigned e2k_ah_max_regno;
static vec<e2k_ah_memo_entry> e2k_ah_memo;

static int e2k_ah_ready (rtx, class loop *, int);

/* The latency of the operation computing SRC, roughly.  */

static int
e2k_ah_latency (rtx src)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, src, NONCONST)
    if (MEM_P (*iter))
      return E2K_LAT6 ? 5 : 3;
  if (FLOAT_MODE_P (GET_MODE (src)))
    return 4;
  switch (GET_CODE (src))
    {
    case MULT:
      return 4;
    case DIV: case UDIV: case MOD: case UMOD:
      return 15;
    case IF_THEN_ELSE: case SMIN: case SMAX: case UMIN: case UMAX:
      return 2;
    default:
      return 1;
    }
}

/* When pseudo X is ready in an iteration of LOOP.  */

static int
e2k_ah_reg_ready (rtx x, class loop *loop, int depth)
{
  if (!REG_P (x) || HARD_REGISTER_P (x) || REGNO (x) >= e2k_ah_max_regno
      || depth > 12)
    return 0;
  unsigned regno = REGNO (x);
  e2k_ah_memo_entry &m = e2k_ah_memo[regno];
  if (m.loop == loop->num)
    return MAX (m.ready, 0);
  if (DF_REG_DEF_COUNT (regno) != 1)
    return 0;
  df_ref def = DF_REG_DEF_CHAIN (regno);
  if (DF_REF_IS_ARTIFICIAL (def)
      || !flow_bb_inside_loop_p (loop, DF_REF_BB (def)))
    return 0;
  rtx set = single_set (DF_REF_INSN (def));
  if (!set)
    return 0;
  /* -1 while in progress: a register defined from itself.  */
  e2k_ah_memo[regno].loop = loop->num;
  e2k_ah_memo[regno].ready = -1;
  int r = (e2k_ah_latency (SET_SRC (set))
	   + e2k_ah_ready (SET_SRC (set), loop, depth + 1));
  e2k_ah_memo[regno].ready = r;
  return r;
}

/* When all the registers X reads are ready.  */

static int
e2k_ah_ready (rtx x, class loop *loop, int depth)
{
  int r = 0;
  subrtx_var_iterator::array_type array;
  FOR_EACH_SUBRTX_VAR (iter, array, x, NONCONST)
    if (REG_P (*iter))
      r = MAX (r, e2k_ah_reg_ready (*iter, loop, depth));
  return r;
}

/* Whether pseudo X has one use outside debug insns.  */

static bool
e2k_ah_single_use_p (rtx x)
{
  int n = 0;
  for (df_ref use = DF_REG_USE_CHAIN (REGNO (x)); use;
       use = DF_REF_NEXT_REG (use))
    if (DF_REF_IS_ARTIFICIAL (use)
	|| (NONDEBUG_INSN_P (DF_REF_INSN (use)) && ++n > 1))
      return false;
  return n == 1;
}

/* Add X times SCALE to TERMS and CST: through pseudos set once in BB by
   an addition, a shift or a multiplication by a power of 2 and used
   once, whose definitions go to INNER; other registers are terms.  */

static bool
e2k_ah_flatten (rtx x, unsigned HOST_WIDE_INT scale, basic_block bb,
		vec<e2k_ah_term> &terms, unsigned HOST_WIDE_INT &cst,
		vec<rtx_insn *> &inner, int depth)
{
  if (CONST_INT_P (x))
    {
      cst += UINTVAL (x) * scale;
      return true;
    }
  if (GET_MODE (x) != DImode || depth > 16)
    return false;
  switch (GET_CODE (x))
    {
    case PLUS:
      return (e2k_ah_flatten (XEXP (x, 0), scale, bb, terms, cst, inner,
			      depth + 1)
	      && e2k_ah_flatten (XEXP (x, 1), scale, bb, terms, cst, inner,
				 depth + 1));
    case ASHIFT:
      if (!CONST_INT_P (XEXP (x, 1)) || !IN_RANGE (INTVAL (XEXP (x, 1)), 0, 31))
	return false;
      return e2k_ah_flatten (XEXP (x, 0), scale << INTVAL (XEXP (x, 1)), bb,
			     terms, cst, inner, depth + 1);
    case MULT:
      if (!CONST_INT_P (XEXP (x, 1))
	  || !IN_RANGE (exact_log2 (INTVAL (XEXP (x, 1))), 0, 31))
	return false;
      return e2k_ah_flatten (XEXP (x, 0), scale * INTVAL (XEXP (x, 1)), bb,
			     terms, cst, inner, depth + 1);
    case REG:
      break;
    default:
      return false;
    }
  if (!HARD_REGISTER_P (x) && REGNO (x) < e2k_ah_max_regno
      && DF_REG_DEF_COUNT (REGNO (x)) == 1 && e2k_ah_single_use_p (x))
    {
      df_ref def = DF_REG_DEF_CHAIN (REGNO (x));
      rtx_insn *d = DF_REF_INSN (def);
      if (!DF_REF_IS_ARTIFICIAL (def) && DF_REF_BB (def) == bb
	  && GET_CODE (PATTERN (d)) == SET && SET_DEST (PATTERN (d)) == x
	  && (GET_CODE (SET_SRC (PATTERN (d))) == PLUS
	      || GET_CODE (SET_SRC (PATTERN (d))) == ASHIFT
	      || GET_CODE (SET_SRC (PATTERN (d))) == MULT))
	{
	  unsigned nterms = terms.length (), ninner = inner.length ();
	  unsigned HOST_WIDE_INT ocst = cst;
	  inner.safe_push (d);
	  if (e2k_ah_flatten (SET_SRC (PATTERN (d)), scale, bb, terms, cst,
			      inner, depth + 1))
	    return true;
	  /* Not a sum after all: the register is a term.  */
	  terms.truncate (nterms);
	  inner.truncate (ninner);
	  cst = ocst;
	}
    }
  for (e2k_ah_term &t : terms)
    if (rtx_equal_p (t.reg, x))
      {
	t.scale += scale;
	return true;
      }
  terms.safe_push ({ x, scale, 0 });
  return true;
}

static int
e2k_ah_regno_cmp (const void *a, const void *b)
{
  return ((int) REGNO (((const e2k_ah_term *) a)->reg)
	  - (int) REGNO (((const e2k_ah_term *) b)->reg));
}

static int
e2k_ah_int_cmp (const void *a, const void *b)
{
  return *(const int *) a - *(const int *) b;
}

static int
e2k_ah_val_cmp (const void *a, const void *b)
{
  return (((const e2k_ah_val *) a)->ready
	  - ((const e2k_ah_val *) b)->ready);
}

/* A sum of terms set nowhere in a loop, computed on its entry edge.  */

struct e2k_ah_hoisted
{
  int loop;
  rtx key;
  rtx reg;
};

static vec<e2k_ah_hoisted> e2k_ah_hoisted_sums;

/* Whether pseudo X is set nowhere in LOOP.  */

static bool
e2k_ah_invariant_p (rtx x, class loop *loop)
{
  if (HARD_REGISTER_P (x) || REGNO (x) >= e2k_ah_max_regno)
    return false;
  for (df_ref def = DF_REG_DEF_CHAIN (REGNO (x)); def;
       def = DF_REF_NEXT_REG (def))
    if (DF_REF_IS_ARTIFICIAL (def)
	|| flow_bb_inside_loop_p (loop, DF_REF_BB (def)))
      return false;
  return true;
}

/* The one edge entering LOOP from outside, or null.  */

static edge
e2k_ah_entry (class loop *loop)
{
  if (!loop_outer (loop))
    return NULL;
  edge entry = NULL, e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, loop->header->preds)
    if (!flow_bb_inside_loop_p (loop, e->src))
      {
	if (entry || (e->flags & EDGE_COMPLEX)
	    || e->src == ENTRY_BLOCK_PTR_FOR_FN (cfun))
	  return NULL;
	entry = e;
      }
  return entry;
}

/* Emit TERMS shifted by their scales into VALS.  */

static void
e2k_ah_shifted (vec<e2k_ah_term> &terms, vec<e2k_ah_val> &vals)
{
  for (e2k_ah_term &t : terms)
    {
      rtx v = t.reg;
      if (t.scale != 1)
	v = force_reg (DImode,
		       expand_simple_binop (DImode, ASHIFT, v,
					    GEN_INT (exact_log2 (t.scale)),
					    NULL_RTX, 0, OPTAB_DIRECT));
      vals.safe_push ({ t.ready, v });
    }
}

/* Emit additions of VALS, the two first ready first, until KEEP are
   left.  */

static void
e2k_ah_sum (vec<e2k_ah_val> &vals, unsigned keep)
{
  while (vals.length () > keep)
    {
      vals.qsort (e2k_ah_val_cmp);
      rtx s = force_reg (DImode,
			 expand_simple_binop (DImode, PLUS, vals[0].x,
					      vals[1].x, NULL_RTX, 0,
					      OPTAB_DIRECT));
      int r = MAX (vals[0].ready, vals[1].ready) + 1;
      vals.ordered_remove (0);
      vals[0] = { r, s };
    }
}

/* Rebuild the address of MEM, accessed by INSN in BB of LOOP.  */

static bool
e2k_ah_rebuild (rtx_insn *insn, rtx mem, basic_block bb, class loop *loop)
{
  rtx addr = XEXP (mem, 0);
  auto_vec<e2k_ah_term, 8> terms;
  auto_vec<rtx_insn *, 8> inner;
  unsigned HOST_WIDE_INT cst = 0;
  if (GET_MODE (addr) != DImode
      || !e2k_ah_flatten (addr, 1, bb, terms, cst, inner, 0)
      || inner.is_empty () || terms.length () < 2 || terms.length () > 6)
    return false;
  for (e2k_ah_term &t : terms)
    {
      int k = exact_log2 (t.scale);
      if (!IN_RANGE (k, 0, 31))
	return false;
      /* The terms must still hold their values at INSN.  */
      for (rtx_insn *d : inner)
	if (reg_overlap_mentioned_p (t.reg, PATTERN (d))
	    && reg_set_between_p (t.reg, d, insn))
	  return false;
      t.ready = e2k_ah_reg_ready (t.reg, loop, 0) + (k != 0);
    }

  /* Terms set nowhere in the loop go with the constant into one register
     computed on the loop's entry edge, as loop-invariant motion would
     have done (computed in the loop, it would also cost the modulo
     scheduler a rotating register over a whole iteration).  */
  edge entry = e2k_ah_entry (loop);
  auto_vec<e2k_ah_term, 8> inv, var;
  for (e2k_ah_term &t : terms)
    if (entry && e2k_ah_invariant_p (t.reg, loop))
      inv.safe_push (t);
    else
      var.safe_push (t);
  bool hoist = (inv.length () + (cst != 0) >= 2
		|| (inv.length () == 1 && inv[0].scale != 1));
  if (!hoist)
    {
      var.truncate (0);
      var.safe_splice (terms);
      inv.truncate (0);
    }
  unsigned HOST_WIDE_INT lcst = hoist ? 0 : cst;

  /* In the loop: the constant goes to the first value ready (to the access
     when one value is left), then the two first ready are added until two
     are left, which the access adds.  */
  auto_vec<int, 8> ready;
  int ops = 0;
  for (e2k_ah_term &t : var)
    {
      ready.safe_push (t.ready);
      ops += t.scale != 1;
    }
  if (hoist)
    ready.safe_push (0);
  ready.qsort (e2k_ah_int_cmp);
  if (lcst && ready.length () > 1)
    {
      ready[0]++;
      ops++;
    }
  while (ready.length () > 2)
    {
      ready.qsort (e2k_ah_int_cmp);
      int r = MAX (ready[0], ready[1]) + 1;
      ready.ordered_remove (0);
      ready[0] = r;
      ops++;
    }
  int now = ready.length () == 1 ? ready[0] : MAX (ready[0], ready[1]);
  int before = e2k_ah_ready (addr, loop, 0);
  int old = inner.length ();
  if (!((now < before && ops <= old + 1) || (now <= before && ops < old)))
    return false;

  rtx h = NULL_RTX, key = NULL_RTX;
  if (hoist)
    {
      auto_vec<e2k_ah_term, 8> sorted;
      sorted.safe_splice (inv);
      sorted.qsort (e2k_ah_regno_cmp);
      for (e2k_ah_term &t : sorted)
	{
	  rtx x = (t.scale == 1 ? t.reg
		   : gen_rtx_ASHIFT (DImode, t.reg,
				     GEN_INT (exact_log2 (t.scale))));
	  key = key ? gen_rtx_PLUS (DImode, key, x) : x;
	}
      if (cst)
	key = gen_rtx_PLUS (DImode, key, gen_int_mode (cst, DImode));
      for (e2k_ah_hoisted &e : e2k_ah_hoisted_sums)
	if (e.loop == loop->num && rtx_equal_p (e.key, key))
	  h = e.reg;
    }
  bool new_h = hoist && !h;
  if (new_h)
    h = gen_reg_rtx (DImode);

  start_sequence ();
  auto_vec<e2k_ah_val, 8> vals;
  e2k_ah_shifted (var, vals);
  if (hoist)
    vals.safe_push ({ 0, h });
  if (lcst && vals.length () > 1)
    {
      vals.qsort (e2k_ah_val_cmp);
      vals[0].x = force_reg (DImode,
			     expand_simple_binop (DImode, PLUS, vals[0].x,
						  gen_int_mode (lcst, DImode),
						  NULL_RTX, 0, OPTAB_DIRECT));
      vals[0].ready++;
      lcst = 0;
    }
  e2k_ah_sum (vals, 2);
  rtx naddr = (vals.length () == 1 ? plus_constant (DImode, vals[0].x, lcst)
	       : gen_rtx_PLUS (DImode, vals[0].x, vals[1].x));
  rtx_insn *seq = end_sequence ();
  if (!validate_change (insn, &XEXP (mem, 0), naddr, 0))
    return false;
  emit_insn_before (seq, insn);
  if (new_h)
    {
      start_sequence ();
      auto_vec<e2k_ah_val, 8> ivals;
      e2k_ah_shifted (inv, ivals);
      e2k_ah_sum (ivals, 1);
      rtx v = ivals[0].x;
      if (cst)
	v = expand_simple_binop (DImode, PLUS, v, gen_int_mode (cst, DImode),
				 h, 0, OPTAB_DIRECT);
      if (v != h)
	emit_move_insn (h, v);
      insert_insn_on_edge (end_sequence (), entry);
      e2k_ah_hoisted_sums.safe_push ({ loop->num, key, h });
    }
  if (dump_file)
    fprintf (dump_file, ";; insn %d: address ready %d -> %d, %d -> %d "
	     "operations%s\n", INSN_UID (insn), before, now, old, ops,
	     hoist ? (new_h ? ", invariants hoisted" : ", invariants shared")
	     : "");
  return true;
}

static unsigned int
e2k_addr_height (void)
{
  df_analyze ();
  loop_optimizer_init (AVOID_CFG_MODIFICATIONS);
  e2k_ah_max_regno = max_reg_num ();
  e2k_ah_memo.create (e2k_ah_max_regno);
  e2k_ah_memo.quick_grow (e2k_ah_max_regno);
  for (e2k_ah_memo_entry &m : e2k_ah_memo)
    m.loop = -1;
  int n = 0;
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    {
      if (!optimize_bb_for_speed_p (bb))
	continue;
      rtx_insn *insn;
      FOR_BB_INSNS (bb, insn)
	{
	  if (!NONDEBUG_INSN_P (insn) || !single_set (insn)
	      || asm_noperands (PATTERN (insn)) >= 0)
	    continue;
	  auto_vec<rtx, 2> mems;
	  subrtx_var_iterator::array_type array;
	  FOR_EACH_SUBRTX_VAR (iter, array, PATTERN (insn), NONCONST)
	    if (MEM_P (*iter))
	      mems.safe_push (*iter);
	  for (rtx mem : mems)
	    n += e2k_ah_rebuild (insn, mem, bb, bb->loop_father);
	}
    }
  e2k_ah_memo.release ();
  e2k_ah_hoisted_sums.release ();
  commit_edge_insertions ();
  loop_optimizer_finalize ();
  /* The old chains are dead now.  */
  if (n)
    delete_trivially_dead_insns (get_insns (), max_reg_num ());
  if (dump_file)
    fprintf (dump_file, ";; e2k_addr_height: %d addresses rebuilt\n", n);
  return 0;
}

namespace {

const pass_data pass_data_e2k_addr_height =
{
  RTL_PASS,
  "e2k_addr_height",
  OPTGROUP_NONE,
  TV_NONE,
  0, 0, 0, 0,
  TODO_df_finish
};

class pass_e2k_addr_height : public rtl_opt_pass
{
public:
  pass_e2k_addr_height (gcc::context *ctxt)
    : rtl_opt_pass (pass_data_e2k_addr_height, ctxt)
  {}

  bool gate (function *) final override
  {
    return optimize >= 2 && e2k_addr_height_p;
  }

  unsigned int execute (function *) final override
  {
    return e2k_addr_height ();
  }
};

} // anon namespace

static rtl_opt_pass *
make_pass_e2k_addr_height (gcc::context *ctxt)
{
  return new pass_e2k_addr_height (ctxt);
}

/* Control speculation the way lcc does it: an operation moved above a
   branch runs speculatively (",sm"), a load giving a diagnostic value
   instead of a fault on an invalid address, any other operation passing
   a diagnostic operand on (spec/isa/speculation.md).  Only a
   non-speculative use of a diagnostic value traps, and on the path the
   operation came from its operands were valid; on the other path its
   result is dead (sched-ebb moves nothing above a branch whose other
   path needs the register).  So loads lose their dependences on the
   branches before them (e2k_spec_pin), and whatever sched-ebb moves
   above a branch gets ",sm" afterwards; operations without a safe
   speculative form stay below the branches before them.  FP operations
   among those: a speculative one that would raise a flag not yet set
   gives a diagnostic value instead.  */

/* For each insn UID, its block's place in the layout before scheduling,
   or -1.  */
static vec<int> e2k_spec_from;

/* Whether INSN may run above a branch, and how: 1 with ",sm", 2 as it
   is, 0 not.  */
static int
e2k_spec_kind (rtx_insn *insn)
{
  if (!NONDEBUG_INSN_P (insn) || recog_memoized (insn) < 0
      || e2k_asm_insn_p (insn) || GET_CODE (PATTERN (insn)) == COND_EXEC)
    return 0;
  switch (get_attr_type (insn))
    {
    case TYPE_ALU: case TYPE_ALU14: case TYPE_ALU0134: case TYPE_CMP:
    case TYPE_MUL:
    case TYPE_LOAD: case TYPE_PINT: case TYPE_PINT14: case TYPE_PMUL:
    case TYPE_PANY:
      return 1;
    /* A lock load prints its own ",sm".  */
    case TYPE_LDLOCK: case TYPE_DISP: case TYPE_RET: case TYPE_GHOST:
      return 2;
    default:
      return 0;
    }
}

static void
e2k_spec_prepare (void)
{
  e2k_spec_from.truncate (0);
  e2k_spec_from.safe_grow (get_max_uid () + 1);
  for (int &k : e2k_spec_from)
    k = -1;
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *insn;
      FOR_BB_INSNS (bb, insn)
	{
	  if (!NONDEBUG_INSN_P (insn))
	    continue;
	  e2k_spec_from[INSN_UID (insn)] = bb->index;
	}
    }
}

/* Whether a register INSN sets is live where JUMP may go other than
   falling through.  */
static bool
e2k_spec_sets_live_p (rtx_insn *insn, rtx_insn *jump)
{
  edge e;
  edge_iterator ei;
  df_ref def;
  FOR_EACH_EDGE (e, ei, BLOCK_FOR_INSN (jump)->succs)
    if (!(e->flags & EDGE_FALLTHRU))
      {
	bitmap live = df_get_live_in (e->dest);
	FOR_EACH_INSN_DEF (def, insn)
	  if (bitmap_bit_p (live, DF_REF_REGNO (def)))
	    return true;
      }
  return false;
}

/* sched-ebb's dependence hook.  A load depends on every jump before it
   (sched-deps keeps possibly trapping loads below jumps, by their
   address only: GCC marks jump-table loads MEM_NOTRAP_P, and those trap
   above their range check); here that dependence goes when the load's
   register isn't needed on the jump's other path, and the load moves
   up as ld,sm.  What has no speculative form stays below the jumps
   before it.  */
/* A register written under a predicate before a return under the same
   predicate (e2k_cond_returns: the result into %r0, where the function
   may still keep an argument) is as it was for what reads it after the
   return: past it the predicate was false.  Drop those dependences, so
   that the reads may go ahead of the write (reading the old value then:
   in the same wide instruction reads come first, and above the return
   only what has a speculative form and sets nothing the return needs
   goes, e2k_spec_pin).  */
static void
e2k_cond_ret_deps (rtx_insn *head, rtx_insn *tail)
{
  auto_vec<rtx_insn *, 16> rets;
  rtx_insn *prep = NULL;
  for (rtx_insn *insn = head; insn != NEXT_INSN (tail);
       insn = NEXT_INSN (insn))
    {
      if (!NONDEBUG_INSN_P (insn))
	continue;
      if (recog_memoized (insn) == CODE_FOR_e2k_return_prep)
	prep = insn;
      if (JUMP_P (insn) && recog_memoized (insn) == CODE_FOR_e2k_cond_return)
	{
	  /* It reads %ctpr3 (its pattern can't say so: GCC wants a
	     conditional return to be a plain SET), and sched-deps gives the
	     registers live at a jump's target a latency of 0: not in the
	     prepare's wide instruction (gas), 6 cycles after it.  */
	  if (prep)
	    add_dependence (insn, prep, REG_DEP_TRUE);
	  rets.safe_push (insn);
	  continue;
	}
      if (rets.is_empty ())
	continue;
      sd_iterator_def it;
      dep_t dep;
      for (it = sd_iterator_start (insn, SD_LIST_BACK);
	   sd_iterator_cond (&it, &dep);)
	{
	  rtx_insn *w = DEP_PRO (dep);
	  bool drop = false;
	  if (DEP_TYPE (dep) == REG_DEP_TRUE && NONJUMP_INSN_P (w)
	      && GET_CODE (PATTERN (w)) == COND_EXEC
	      && GET_CODE (COND_EXEC_CODE (PATTERN (w))) == SET
	      && REG_P (SET_DEST (COND_EXEC_CODE (PATTERN (w)))))
	    {
	      rtx test = COND_EXEC_TEST (PATTERN (w));
	      for (rtx_insn *r : rets)
		if (INSN_LUID (r) > INSN_LUID (w)
		    && rtx_equal_p (XEXP (SET_SRC (PATTERN (r)), 0), test)
		    && !reg_set_between_p (XEXP (test, 0), w, r))
		  drop = true;
	      /* One dependence stands for all the pair has: not if INSN
		 also writes what W reads or writes (xz's
		 lzma_stream_flags_compare: a load into the register W
		 copied the result from went above it).  */
	      subrtx_iterator::array_type array;
	      FOR_EACH_SUBRTX (iter, array, PATTERN (w), NONCONST)
		if (REG_P (*iter) && reg_set_p (*iter, insn))
		  drop = false;
	    }
	  if (drop)
	    sd_delete_dep (it);
	  else
	    sd_iterator_next (&it);
	}
    }
}

/* A load e2k_unpredicate_loads ran without its condition, and that the
   DAM may move above a store (a speculative dependence on it), gets one
   on the setter of its predicate too, and on every jump before it: the
   check, which takes the load's dependences and runs under the
   condition, waits for them, while the lock load, which drops the
   speculative ones, need not.  Not on a jump to where the load's
   register is live: the lock load writes it whatever the condition, so
   it stays below that jump and out of its wide instruction (xz's
   bt_find_func, where the loaded cur_match shared a register with the
   delta that the match path reads).  (Other loads are speculated only once
   the jumps before them are scheduled, e2k_speculate_insn, which haifa
   asks again only when another dependence is resolved: for the match
   finders' loads, the store they wait for.)  */
static void
e2k_unpred_cond_deps (rtx_insn *head, rtx_insn *tail)
{
  if (e2k_unpred_cond.is_empty ())
    return;
  for (rtx_insn *insn = head; insn != NEXT_INSN (tail);
       insn = NEXT_INSN (insn))
    {
      rtx cond;
      if (!NONDEBUG_INSN_P (insn) || !(cond = e2k_unpred_cond_of (insn)))
	continue;
      sd_iterator_def it;
      dep_t dep;
      ds_t ds = 0;
      rtx pred = XEXP (cond, 0);
      /* A store under the opposite condition, sharing no register with
	 the load: when the condition holds it doesn't run, and when it
	 doesn't the loaded value is not used, so the two may go in either
	 order (7-Zip's "*ptr1 = curMatch" and the load of pair[0]).  */
      auto other_store_p = [&] (rtx_insn *x)
	{
	  rtx pat = PATTERN (x);
	  if (GET_CODE (pat) != COND_EXEC
	      || XEXP (COND_EXEC_TEST (pat), 0) != pred
	      || (GET_CODE (COND_EXEC_TEST (pat))
		  != reversed_comparison_code (cond, NULL)))
	    return false;
	  rtx set = COND_EXEC_CODE (pat);
	  if (GET_CODE (set) != SET || !MEM_P (SET_DEST (set)))
	    return false;
	  subrtx_iterator::array_type array;
	  FOR_EACH_SUBRTX (iter, array, pat, NONCONST)
	    if (REG_P (*iter) && reg_set_p (*iter, insn))
	      return false;
	  return true;
	};
      for (int back = 0; back < 2; back++)
	for (it = sd_iterator_start (insn, back ? SD_LIST_BACK
						: SD_LIST_FORW);
	     sd_iterator_cond (&it, &dep);)
	  if (other_store_p (back ? DEP_PRO (dep) : DEP_CON (dep)))
	    sd_delete_dep (it);
	  else
	    sd_iterator_next (&it);
      FOR_EACH_DEP (insn, SD_LIST_BACK, it, dep)
	if (DEP_STATUS (dep) & BEGIN_DATA)
	  ds = DEP_STATUS (dep);
      if (!ds)
	continue;
      bool setter = false;
      for (rtx_insn *p = PREV_INSN (insn); p && p != PREV_INSN (head);
	   p = PREV_INSN (p))
	if ((JUMP_P (p) && !e2k_spec_sets_live_p (insn, p))
	    || (!setter && NONDEBUG_INSN_P (p) && !JUMP_P (p)
		&& reg_set_p (pred, p)))
	  {
	    /* A true dependence, the only kind haifa speculates on data.  */
	    setter |= !JUMP_P (p);
	    dep_def d;
	    init_dep_1 (&d, p, insn, REG_DEP_TRUE,
			(ds & ~DEP_TYPES) | DEP_TRUE);
	    sd_add_or_update_dep (&d, false);
	  }
    }
}

static void
e2k_spec_pin (rtx_insn *head, rtx_insn *tail)
{
  e2k_cond_ret_deps (head, tail);
  /* After the jumps' dependences below are dropped.  */
  auto done = [&] () { e2k_unpred_cond_deps (head, tail); };
  if (!e2k_control_spec || e2k_spec_from.is_empty ())
    return done ();
  rtx_insn *jump = NULL;
  for (rtx_insn *insn = head; insn != NEXT_INSN (tail);
       insn = NEXT_INSN (insn))
    {
      if (!NONDEBUG_INSN_P (insn))
	continue;
      if (jump && !JUMP_P (insn) && e2k_spec_kind (insn) == 0)
	add_dependence (insn, jump, REG_DEP_ANTI);
      if (jump && e2k_spec_kind (insn) == 1
	  && get_attr_type (insn) == TYPE_LOAD
	  && !volatile_refs_p (PATTERN (insn)))
	{
	  sd_iterator_def it;
	  dep_t dep;
	  for (it = sd_iterator_start (insn, SD_LIST_BACK);
	       sd_iterator_cond (&it, &dep);)
	    if (JUMP_P (DEP_PRO (dep))
		&& DEP_TYPE (dep) == REG_DEP_ANTI
		&& !e2k_spec_sets_live_p (insn, DEP_PRO (dep)))
	      sd_delete_dep (it);
	    else
	      sd_iterator_next (&it);
	}
      if (JUMP_P (insn))
	jump = insn;
    }
  done ();
}

/* Whether X reads or writes hard register REG (reg_overlap_mentioned_p
   leaves out registers only set).  */
static bool
e2k_hard_reg_in_p (rtx reg, rtx x)
{
  unsigned lo = REGNO (reg), hi = END_REGNO (reg);
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, x, NONCONST)
    if (REG_P (*iter) && REGNO (*iter) < hi && END_REGNO (*iter) > lo)
      return true;
  return false;
}

/* A register for a value of mode M that BB sets at INSN and reads up to
   LAST: one the function uses, dead after INSN, and mentioned nowhere
   in BB up to LAST (so nothing earlier keeps INSN there); AVOID too is
   not taken.  -1 if none.  */
static int
e2k_free_reg (basic_block bb, rtx_insn *insn, rtx_insn *last,
	      machine_mode m, int avoid)
{
  auto_bitmap live;
  bitmap_copy (live, df_get_live_out (bb));
  df_simulate_initialize_backwards (bb, live);
  for (rtx_insn *i = BB_END (bb); i != insn; i = PREV_INSN (i))
    if (NONDEBUG_INSN_P (i))
      df_simulate_one_insn_backwards (bb, i, live);
  for (int k = 0; k < 80; k++)
    {
      int r = k < 16 ? 16 + k : R0_REGNUM + k - 16;
      if (fixed_regs[r] || !df_regs_ever_live_p (r) || r == avoid
	  || !targetm.hard_regno_mode_ok (r, m) || bitmap_bit_p (live, r))
	continue;
      rtx nr = gen_rtx_REG (m, r);
      bool free = true;
      for (rtx_insn *j = BB_HEAD (bb); free && j != NEXT_INSN (last);
	   j = NEXT_INSN (j))
	if (NONDEBUG_INSN_P (j) && e2k_hard_reg_in_p (nr, PATTERN (j)))
	  free = false;
      if (free)
	return r;
    }
  return -1;
}

/* Give the register load INSN of BB writes (DEST, read by the insns in
   RANGE) another one, used in the function but not in BB up to the end of
   RANGE and dead after INSN: one mentioned before INSN would keep the
   load there.  */
static bool
e2k_unpred_rename (basic_block bb, rtx_insn *insn, rtx dest,
		   vec<rtx_insn *> &range)
{
  machine_mode m = GET_MODE (dest);
  if (hard_regno_nregs (REGNO (dest), m) != 1)
    return false;
  auto_bitmap live;
  bitmap_copy (live, df_get_live_out (bb));
  df_simulate_initialize_backwards (bb, live);
  for (rtx_insn *i = BB_END (bb); i != insn; i = PREV_INSN (i))
    if (NONDEBUG_INSN_P (i))
      df_simulate_one_insn_backwards (bb, i, live);
  rtx_insn *last = range.is_empty () ? insn : range.last ();
  for (int k = 0; k < 80; k++)
    {
      int r = k < 16 ? 16 + k : R0_REGNUM + k - 16;
      if (fixed_regs[r] || !df_regs_ever_live_p (r) || r == (int) REGNO (dest)
	  || !targetm.hard_regno_mode_ok (r, m) || bitmap_bit_p (live, r))
	continue;
      rtx nr = gen_rtx_REG (m, r);
      bool free = true;
      for (rtx_insn *j = BB_HEAD (bb); free && j != NEXT_INSN (last);
	   j = NEXT_INSN (j))
	if (NONDEBUG_INSN_P (j) && e2k_hard_reg_in_p (nr, PATTERN (j)))
	  free = false;
      if (!free)
	continue;
      auto rename = [&] (rtx_insn *j)
	{
	  subrtx_ptr_iterator::array_type array;
	  FOR_EACH_SUBRTX_PTR (iter, array, &PATTERN (j), NONCONST)
	    if (REG_P (**iter) && REGNO (**iter) == REGNO (dest))
	      validate_change (j, *iter, gen_rtx_REG (GET_MODE (**iter), r), 1);
	};
      /* The load itself only as its destination: it may read the old
	 register for its address.  */
      validate_change (insn, &SET_DEST (PATTERN (insn)),
		       gen_rtx_REG (m, r), 1);
      for (rtx_insn *j : range)
	rename (j);
      if (dump_file)
	fprintf (dump_file, ";; e2k_unpred_rename: insn %d, %s -> %s\n",
		 INSN_UID (insn), reg_names[REGNO (dest)], reg_names[r]);
      return apply_change_group ();
    }
  return false;
}

/* Loads e2k_unpredicate_loads changed, for -munpred-limit.  */
static int e2k_unpred_total;

/* The load of INSN if it is one e2k_unpredicate_loads may run without
   its predicate: under COND_EXEC, into a whole general register, not
   volatile and without a MAS.  */
static rtx
e2k_unpred_load_set (rtx_insn *insn)
{
  if (!NONDEBUG_INSN_P (insn) || GET_CODE (PATTERN (insn)) != COND_EXEC
      || recog_memoized (insn) < 0 || get_attr_type (insn) != TYPE_LOAD
      || get_attr_mas (insn) == MAS_YES)
    return NULL_RTX;
  rtx set = COND_EXEC_CODE (PATTERN (insn));
  if (GET_CODE (set) != SET || !REG_P (SET_DEST (set))
      || !GPR_REGNO_P (REGNO (SET_DEST (set)))
      || hard_regno_nregs (REGNO (SET_DEST (set)),
			   GET_MODE (SET_DEST (set))) != 1)
    return NULL_RTX;
  rtx src = SET_SRC (set);
  if (GET_CODE (src) == ZERO_EXTEND || GET_CODE (src) == SIGN_EXTEND)
    src = XEXP (src, 0);
  if (!MEM_P (src) || MEM_VOLATILE_P (src))
    return NULL_RTX;
  return set;
}

/* If-conversion's choice between two loads, "r = p ? *a : *b" (7-Zip's
   and xz's match finders: the next tree node, which waited for a compare
   waiting for a miss): I1 loads R under P, a later I2 under not P.  Both
   run unpredicated as ld,sm into free registers T1 and T2, the insns
   under P between them read T1, and a merge after I2 sets R, which keeps
   its old value until then for what runs under not P.  */
static int
e2k_unpred_pairs (basic_block bb)
{
  int n = 0;
  rtx_insn *i1;
  FOR_BB_INSNS (bb, i1)
    {
      rtx set1 = e2k_unpred_load_set (i1);
      if (!set1 || e2k_unpred_total >= e2k_unpred_limit)
	continue;
      rtx cond = COND_EXEC_TEST (PATTERN (i1));
      rtx dest = SET_DEST (set1), pred = XEXP (cond, 0);
      machine_mode m = GET_MODE (dest);
      rtx_insn *i2 = NULL;
      auto_vec<rtx_insn *, 8> range;
      bool ok = true;
      for (rtx_insn *j = NEXT_INSN (i1);
	   ok && !i2 && j && j != NEXT_INSN (BB_END (bb)); j = NEXT_INSN (j))
	{
	  if (!NONDEBUG_INSN_P (j))
	    continue;
	  rtx pat = PATTERN (j);
	  bool ce = GET_CODE (pat) == COND_EXEC;
	  rtx set2 = e2k_unpred_load_set (j);
	  if (set2 && REGNO (SET_DEST (set2)) == REGNO (dest)
	      && GET_MODE (SET_DEST (set2)) == m
	      && XEXP (COND_EXEC_TEST (pat), 0) == pred
	      && (GET_CODE (COND_EXEC_TEST (pat))
		  == reversed_comparison_code (cond, NULL)))
	    i2 = j;
	  else if (CALL_P (j) || reg_set_p (pred, j) || reg_set_p (dest, j))
	    ok = false;
	  else if (e2k_hard_reg_in_p (dest, pat))
	    {
	      /* Under P it reads I1's value; under not P the old one, still
		 there; otherwise either, which only R gives.  */
	      if (!ce)
		ok = false;
	      else if (rtx_equal_p (COND_EXEC_TEST (pat), cond))
		range.safe_push (j);
	      else if (XEXP (COND_EXEC_TEST (pat), 0) != pred)
		ok = false;
	    }
	}
      if (!ok || !i2)
	continue;
      int t1 = e2k_free_reg (bb, i2, i2, m, REGNO (dest));
      if (t1 < 0)
	continue;
      int t2 = e2k_free_reg (bb, i2, i2, m, t1);
      if (t2 < 0 || t2 == (int) REGNO (dest))
	continue;
      rtx r1 = gen_rtx_REG (m, t1), r2 = gen_rtx_REG (m, t2);
      rtx set2 = COND_EXEC_CODE (PATTERN (i2));
      rtx mrg = gen_rtx_SET (dest, gen_rtx_IF_THEN_ELSE
				       (m, copy_rtx (cond), r1, r2));
      rtx_insn *mi = emit_insn_after (mrg, i2);
      if (recog_memoized (mi) < 0)
	{
	  delete_insn (mi);
	  continue;
	}
      rtx cond2 = COND_EXEC_TEST (PATTERN (i2));
      rtx n1 = copy_rtx (set1), n2 = copy_rtx (set2);
      SET_DEST (n1) = r1;
      SET_DEST (n2) = r2;
      validate_change (i1, &PATTERN (i1), n1, 1);
      validate_change (i2, &PATTERN (i2), n2, 1);
      for (rtx_insn *j : range)
	{
	  subrtx_ptr_iterator::array_type array;
	  FOR_EACH_SUBRTX_PTR (iter, array, &PATTERN (j), NONCONST)
	    if (REG_P (**iter) && REGNO (**iter) == REGNO (dest))
	      validate_change (j, *iter,
			       gen_rtx_REG (GET_MODE (**iter), t1), 1);
	}
      if (!apply_change_group ())
	{
	  delete_insn (mi);
	  continue;
	}
      e2k_ms_set_flag (i1, E2K_MS_SM);
      e2k_ms_set_flag (i2, E2K_MS_SM);
      if (e2k_unpred_dam >= 1)
	{
	  e2k_set_unpred_cond (i1, cond);
	  e2k_set_unpred_cond (i2, cond2);
	}
      e2k_unpred_total++;
      n++;
      if (dump_file)
	fprintf (dump_file, ";; e2k_unpred_pairs: insns %d and %d into %s "
		 "and %s, merged into %s\n", INSN_UID (i1), INSN_UID (i2),
		 reg_names[t1], reg_names[t2], reg_names[REGNO (dest)]);
    }
  return n;
}

/* The arms of an if-converted "if" (LZMA's bit decoding: range, code
   and the probability updated under opposite predicates) wait for the
   compare, operation after operation.  An integer operation of an arm
   whose value only operations under the same predicate read can run
   before the compare, as ",sm" (e2k_unpred_arms); the last operations
   of each arm stay predicated and select the result.  */

/* An integer operation under a predicate that can run without it: a
   whole-register SET of one GPR the function may change, by an operation
   that can't trap (e2k.md's predicable ALU patterns).  */
static bool
e2k_arm_alu_p (rtx_insn *insn)
{
  if (!NONJUMP_INSN_P (insn) || GET_CODE (PATTERN (insn)) != COND_EXEC
      || recog_memoized (insn) < 0)
    return false;
  enum attr_type t = get_attr_type (insn);
  if (t != TYPE_ALU && t != TYPE_ALU14 && t != TYPE_ALU0134)
    return false;
  rtx set = COND_EXEC_CODE (PATTERN (insn));
  if (GET_CODE (set) != SET || !REG_P (SET_DEST (set)))
    return false;
  unsigned r = REGNO (SET_DEST (set));
  return (GPR_REGNO_P (r) && !B_REGNO_P (r) && !BX_REGNO_P (r)
	  && REG_NREGS (SET_DEST (set)) == 1
	  && !fixed_regs[r] && !global_regs[r]
	  && r != HARD_FRAME_POINTER_REGNUM
	  && !side_effects_p (SET_SRC (set))
	  && !contains_mem_rtx_p (SET_SRC (set)));
}

/* Whether a use PAT (under the operation's predicate) of the value of
   register R, written in mode M, can read it from another register: one
   SET, R only in its source, in a stored address, or as its whole
   destination (an update of R), each mention R itself, not wider.  */
static bool
e2k_arm_use_ok (rtx pat, unsigned r, machine_mode m)
{
  if (GET_CODE (pat) == COND_EXEC)
    pat = COND_EXEC_CODE (pat);
  if (GET_CODE (pat) != SET || side_effects_p (pat))
    return false;
  rtx dest = SET_DEST (pat), reg = regno_reg_rtx[r];
  if (!REG_P (dest) && !MEM_P (dest) && reg_overlap_mentioned_p (reg, dest))
    return false;
  if (REG_P (dest) && REGNO (dest) <= r && END_REGNO (dest) > r
      && (REGNO (dest) != r || REG_NREGS (dest) != 1))
    return false;
  rtx parts[2] = { SET_SRC (pat), MEM_P (dest) ? XEXP (dest, 0) : NULL_RTX };
  for (rtx x : parts)
    if (x)
      {
	subrtx_iterator::array_type array;
	FOR_EACH_SUBRTX (iter, array, x, NONCONST)
	  if (REG_P (*iter) && REGNO (*iter) <= r && END_REGNO (*iter) > r
	      && (REGNO (*iter) != r || REG_NREGS (*iter) != 1
		  || (GET_MODE_SIZE (GET_MODE (*iter))
		      > GET_MODE_SIZE (m))))
	    return false;
      }
  return true;
}

/* Reads of R in USE (accepted by e2k_arm_use_ok) from T instead.  */
static void
e2k_arm_rename_use (rtx_insn *use, unsigned r, unsigned t)
{
  rtx pat = PATTERN (use);
  rtx set = GET_CODE (pat) == COND_EXEC ? COND_EXEC_CODE (pat) : pat;
  rtx *locs[2] = { &SET_SRC (set),
		   MEM_P (SET_DEST (set)) ? &XEXP (SET_DEST (set), 0) : NULL };
  for (rtx *loc : locs)
    if (loc)
      {
	subrtx_ptr_iterator::array_type array;
	FOR_EACH_SUBRTX_PTR (iter, array, loc, NONCONST)
	  if (REG_P (**iter) && REGNO (**iter) == r)
	    validate_change (use, *iter, gen_rtx_REG (GET_MODE (**iter), t), 1);
      }
  remove_note (use, find_reg_equal_equiv_note (use));
}

/* What follows INSN (under COND, writing R in mode M) in BB does with its
   value: USES, the insns under COND that read it and can read it from
   another register; ESCAPE, something else may read it (not under COND,
   or live out); NEED_OLD, something where COND is false reads R's old
   value.  */
struct e2k_arm_scan
{
  auto_vec<rtx_insn *, 8> uses;
  bool escape, need_old;
};

static void
e2k_arm_scan_value (basic_block bb, rtx_insn *insn, rtx cond, unsigned r,
		    machine_mode m, e2k_arm_scan *s)
{
  rtx pred = XEXP (cond, 0), reg = regno_reg_rtx[r];
  rtx_code rc = reversed_comparison_code (cond, NULL);
  bool c_live = true, n_live = true;
  int budget = 400;
  s->escape = s->need_old = false;
  for (rtx_insn *j = NEXT_INSN (insn); j != NEXT_INSN (BB_END (bb));
       j = NEXT_INSN (j))
    {
      if (!NONDEBUG_INSN_P (j))
	continue;
      if (--budget == 0 || CALL_P (j) || reg_set_p (pred, j))
	{
	  s->escape |= c_live;
	  s->need_old |= n_live;
	  return;
	}
      rtx pat = PATTERN (j);
      if (!e2k_hard_reg_in_p (reg, pat))
	continue;
      bool ce = GET_CODE (pat) == COND_EXEC;
      rtx test = ce ? COND_EXEC_TEST (pat) : NULL_RTX;
      bool same = ce && rtx_equal_p (test, cond);
      bool opp = (ce && REG_P (XEXP (test, 0))
		  && REGNO (XEXP (test, 0)) == REGNO (pred)
		  && GET_CODE (test) == rc);
      rtx body = ce ? COND_EXEC_CODE (pat) : pat;
      bool whole = (GET_CODE (body) == SET && REG_P (SET_DEST (body))
		    && REGNO (SET_DEST (body)) == r
		    && REG_NREGS (SET_DEST (body)) == 1);
      bool reads = !whole || e2k_hard_reg_in_p (reg, SET_SRC (body));
      if (reads)
	{
	  if (same)
	    {
	      if (c_live && e2k_arm_use_ok (pat, r, m))
		s->uses.safe_push (j);
	      else if (c_live)
		s->escape = true, c_live = false;
	    }
	  else if (opp)
	    s->need_old |= n_live;
	  else
	    {
	      if (c_live)
		s->escape = true, c_live = false;
	      s->need_old |= n_live;
	    }
	}
      if (whole)
	{
	  if (!ce)
	    c_live = n_live = false;
	  else if (same)
	    c_live = false;
	  else if (opp)
	    n_live = false;
	  /* Under another predicate: where both hold, a later reader
	     under COND reads that value, not ours.  */
	  else if (c_live)
	    s->escape = true, c_live = false;
	}
      if (!c_live && !n_live)
	return;
    }
  if (REGNO_REG_SET_P (df_get_live_out (bb), r))
    {
      s->escape |= c_live;
      s->need_old |= n_live;
    }
}

/* A register for a value set at or after FIRST and read up to LAST in
   BB: dead after LAST, mentioned nowhere in FIRST .. LAST, one the window
   has anyway (e2k_rename_free_p), not AVOID; of those the one whose last
   mention before FIRST is the farthest up, so that nothing earlier holds
   the moved operation down.  -1 if none.  */
static int
e2k_free_reg_lru (basic_block bb, rtx_insn *first, rtx_insn *last,
		  machine_mode m, int avoid)
{
  auto_bitmap live;
  bitmap_copy (live, df_get_live_out (bb));
  df_simulate_initialize_backwards (bb, live);
  for (rtx_insn *i = BB_END (bb); i != last; i = PREV_INSN (i))
    if (NONDEBUG_INSN_P (i))
      df_simulate_one_insn_backwards (bb, i, live);
  HARD_REG_SET busy;
  CLEAR_HARD_REG_SET (busy);
  for (rtx_insn *j = first; j != NEXT_INSN (last); j = NEXT_INSN (j))
    if (NONDEBUG_INSN_P (j))
      e2k_note_regs (PATTERN (j), &busy);
  int age[FIRST_PSEUDO_REGISTER];
  for (int &a : age)
    a = INT_MAX;
  int d = 0;
  for (rtx_insn *j = PREV_INSN (first); j && j != PREV_INSN (BB_HEAD (bb));
       j = PREV_INSN (j))
    if (NONDEBUG_INSN_P (j))
      {
	HARD_REG_SET mj;
	CLEAR_HARD_REG_SET (mj);
	e2k_note_regs (PATTERN (j), &mj);
	unsigned r;
	hard_reg_set_iterator hrsi;
	EXECUTE_IF_SET_IN_HARD_REG_SET (mj, 0, r, hrsi)
	  if (age[r] == INT_MAX)
	    age[r] = d;
	d++;
      }
  int best = -1;
  for (int k = 0; k < 80; k++)
    {
      int r = k < 16 ? 16 + k : R0_REGNUM + k - 16;
      if (r == avoid || hard_regno_nregs (r, m) != 1
	  || !e2k_rename_free_p (r, m, live, busy))
	continue;
      if (best < 0 || age[r] > age[best])
	best = r;
    }
  return best;
}

/* Reset the debug binds in FROM .. TO that mention REG.  */
static void
e2k_arm_reset_debug (rtx_insn *from, rtx_insn *to, rtx reg)
{
  for (rtx_insn *u = from; u && u != NEXT_INSN (to); u = NEXT_INSN (u))
    if (DEBUG_BIND_INSN_P (u) && e2k_hard_reg_in_p (reg, PATTERN (u)))
      {
	INSN_VAR_LOCATION_LOC (u) = gen_rtx_UNKNOWN_VAR_LOC ();
	df_insn_rescan_debug_internal (u);
      }
}

/* Run the arms' operations of BB early (see above): each one whose value
   operations under its predicate read goes up to just before the
   setter of the predicate, or the first insn it can't cross, as ,sm;
   into its own register when nothing where the predicate is false needs
   the old one, else into a free register its uses then read, with a
   copy back under the predicate where something else may read it.  */
static int
e2k_unpred_arms (basic_block bb)
{
  auto_vec<rtx_insn *, 32> cands;
  rtx_insn *insn;
  FOR_BB_INSNS (bb, insn)
    if (e2k_arm_alu_p (insn) && cands.length () < 256)
      cands.safe_push (insn);
  int n = 0;
  for (rtx_insn *i : cands)
    {
      if (e2k_unpred_total >= e2k_unpred_limit)
	break;
      rtx cond = COND_EXEC_TEST (PATTERN (i));
      rtx set = COND_EXEC_CODE (PATTERN (i));
      rtx dest = SET_DEST (set), pred = XEXP (cond, 0);
      rtx_code rc = reversed_comparison_code (cond, NULL);
      unsigned r = REGNO (dest);
      machine_mode m = GET_MODE (dest);
      e2k_arm_scan s;
      e2k_arm_scan_value (bb, i, cond, r, m, &s);
      /* A last operation of an arm waits for the compare anyway.  */
      if (s.uses.is_empty ())
	continue;
      /* How far up: not above a call, a barrier, a jump or an insn that
	 may run where I runs and changes an operand of it (the other
	 arm's never ran there); above the predicate's setter only to
	 just before it.  */
      rtx_insn *after = bb_note (bb);
      for (rtx_insn *p = PREV_INSN (i); p != bb_note (bb); p = PREV_INSN (p))
	{
	  if (!NONDEBUG_INSN_P (p))
	    continue;
	  rtx pp = PATTERN (p);
	  bool other = (GET_CODE (pp) == COND_EXEC
			&& REG_P (XEXP (COND_EXEC_TEST (pp), 0))
			&& REGNO (XEXP (COND_EXEC_TEST (pp), 0)) == REGNO (pred)
			&& GET_CODE (COND_EXEC_TEST (pp)) == rc);
	  if (CALL_P (p) || JUMP_P (p) || volatile_insn_p (pp)
	      || e2k_asm_insn_p (p) || e2k_raw_insn_p (p)
	      || (!other && modified_in_p (SET_SRC (set), p)))
	    {
	      after = p;
	      break;
	    }
	  if (reg_set_p (pred, p))
	    {
	      after = PREV_INSN (p);
	      break;
	    }
	}
      if (after == PREV_INSN (i))
	continue;
      rtx_insn *first = NEXT_INSN (after);
      bool inplace = !s.need_old;
      for (rtx_insn *p = first; inplace && p != i; p = NEXT_INSN (p))
	if (NONDEBUG_INSN_P (p) && e2k_hard_reg_in_p (dest, PATTERN (p)))
	  inplace = false;
      int t = -1;
      if (!inplace
	  && (t = e2k_free_reg_lru (bb, first, s.uses.last (), m, r)) < 0)
	continue;
      rtx_insn *copy = NULL;
      if (t >= 0 && s.escape)
	{
	  copy = emit_insn_after (gen_rtx_COND_EXEC
				  (VOIDmode, copy_rtx (cond),
				   gen_rtx_SET (copy_rtx (dest),
						gen_rtx_REG (m, t))), i);
	  INSN_LOCATION (copy) = INSN_LOCATION (i);
	  if (recog_memoized (copy) < 0)
	    {
	      delete_insn (copy);
	      continue;
	    }
	}
      rtx nset = copy_rtx (set);
      if (t >= 0)
	SET_DEST (nset) = gen_rtx_REG (m, t);
      validate_change (i, &PATTERN (i), nset, 1);
      if (t >= 0)
	for (rtx_insn *j : s.uses)
	  e2k_arm_rename_use (j, r, t);
      if (!apply_change_group ())
	{
	  if (copy)
	    delete_insn (copy);
	  continue;
	}
      /* Debug binds of R where it now holds another value.  */
      if (t >= 0)
	e2k_arm_reset_debug (NEXT_INSN (i), s.uses.last (), dest);
      else
	e2k_arm_reset_debug (first, i, dest);
      reorder_insns (i, i, after);
      e2k_ms_set_flag (i, E2K_MS_SM);
      if (t >= 0 && !df_regs_ever_live_p (t))
	df_set_regs_ever_live (t, true);
      e2k_unpred_total++;
      n++;
      if (dump_file)
	fprintf (dump_file, ";; e2k_unpred_arms: insn %d, %s%s%s%s\n",
		 INSN_UID (i), reg_names[r], t >= 0 ? " -> " : " in place",
		 t >= 0 ? reg_names[t] : "", copy ? ", copied back" : "");
    }
  return n;
}

/* A load that if-conversion put under a predicate waits for the compare
   that sets it; run as ld,sm it needn't (as lcc runs LZMA's refills,
   "if (range < kTopValue) code = (code << 8) | *buf++").  That is so
   when nothing reads the register it writes but operations under the
   same predicate: in its block, until the register is written again
   without a predicate or under the opposite one, or the block ends with
   it dead, and with the predicate unchanged meanwhile.  */
static void
e2k_unpredicate_loads (void)
{
  int &total = e2k_unpred_total;
  df_analyze ();
  basic_block bb;
  int n = 0;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *insn;
      if (e2k_unpred_loads_p)
	n += e2k_unpred_pairs (bb);
      FOR_BB_INSNS (bb, insn)
	{
	  if (!e2k_unpred_loads_p)
	    break;
	  if (!NONDEBUG_INSN_P (insn) || GET_CODE (PATTERN (insn)) != COND_EXEC
	      || recog_memoized (insn) < 0 || get_attr_type (insn) != TYPE_LOAD
	      || get_attr_mas (insn) == MAS_YES)
	    continue;
	  rtx cond = COND_EXEC_TEST (PATTERN (insn));
	  rtx set = COND_EXEC_CODE (PATTERN (insn));
	  if (GET_CODE (set) != SET || !REG_P (SET_DEST (set))
	      || !GPR_REGNO_P (REGNO (SET_DEST (set))))
	    continue;
	  rtx src = SET_SRC (set);
	  if (GET_CODE (src) == ZERO_EXTEND || GET_CODE (src) == SIGN_EXTEND)
	    src = XEXP (src, 0);
	  if (!MEM_P (src) || MEM_VOLATILE_P (src))
	    continue;
	  rtx dest = SET_DEST (set), pred = XEXP (cond, 0);
	  bool ok = true, done = false, opposite = false;
	  auto_vec<rtx_insn *, 8> range;
	  for (rtx_insn *j = NEXT_INSN (insn);
	       ok && !done && j && j != NEXT_INSN (BB_END (bb));
	       j = NEXT_INSN (j))
	    {
	      if (!NONDEBUG_INSN_P (j))
		continue;
	      rtx pat = PATTERN (j);
	      bool ce = GET_CODE (pat) == COND_EXEC;
	      rtx body = ce ? COND_EXEC_CODE (pat) : pat;
	      bool same = ce && rtx_equal_p (COND_EXEC_TEST (pat), cond);
	      if (same && e2k_hard_reg_in_p (dest, pat))
		range.safe_push (j);
	      if (CALL_P (j)
		  || (reg_referenced_p (dest, body) && !same)
		  || reg_set_p (pred, j))
		ok = false;
	      else if (reg_set_p (dest, j) && !same)
		{
		  rtx s = single_set (j);
		  /* The whole register, on both ways from here.  */
		  done = (s && REG_P (SET_DEST (s))
			  && REGNO (SET_DEST (s)) == REGNO (dest)
			  && (!ce
			      || (XEXP (COND_EXEC_TEST (pat), 0) == pred
				  && (GET_CODE (COND_EXEC_TEST (pat))
				      == reversed_comparison_code (cond, NULL)))));
		  opposite = ce;
		  ok = done;
		}
	    }
	  if (!ok
	      || (!done && REGNO_REG_SET_P (df_get_live_out (bb), REGNO (dest))))
	    continue;
	  if (total >= e2k_unpred_limit)
	    continue;
	  if (!validate_change (insn, &PATTERN (insn), copy_rtx (set), 0))
	    continue;
	  total++;
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_unpredicate_loads: insn %d (%d)\n",
		     INSN_UID (insn), total);
	  e2k_ms_set_flag (insn, E2K_MS_SM);
	  if (e2k_unpred_dam >= 2)
	    e2k_set_unpred_cond (insn, cond);
	  n++;
	  /* Regrename ran while it was predicated, which counts as reading
	     the register's old value.  Not when a write under the opposite
	     predicate ends the range: what follows reads the value of either
	     in the register.  */
	  for (rtx_insn *j = BB_HEAD (bb); !opposite && j != insn;
	       j = NEXT_INSN (j))
	    if (NONDEBUG_INSN_P (j) && e2k_hard_reg_in_p (dest, PATTERN (j)))
	      {
		e2k_unpred_rename (bb, insn, dest, range);
		break;
	      }
	}
      /* After the loads: an arm operation run early first would make the
	 reader of a load in its arm unconditional, and the load would stay
	 predicated.  */
      if (e2k_unpred_arms_p)
	n += e2k_unpred_arms (bb);
    }
  if (n)
    {
      df_note_add_problem ();
      df_analyze ();
    }
  if (dump_file)
    fprintf (dump_file, ";; e2k_unpredicate_loads: %d\n", n);
}

/* After scheduling: ",sm" for what moved to another block, above a
   branch.  By block, not by place in the layout, which the scheduler
   may change: a load moved two blocks up kept no ",sm" in zstd's tree
   search.  (One moved down past a branch, which runs only where it
   ran, takes ",sm" harmlessly.)  */
static void
e2k_spec_mark (void)
{
  basic_block bb;
  /* The cycle and superblock of the last jump: what follows it in its
     cycle shares its wide instruction and runs when it is taken.  */
  int jclock = 0, jebb = 0;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *insn;
      FOR_BB_INSNS (bb, insn)
	{
	  unsigned uid = INSN_UID (insn);
	  if (!NONDEBUG_INSN_P (insn))
	    continue;
	  int clock = uid < e2k_insn_clock.length () ? e2k_insn_clock[uid] : 0;
	  int ebb = uid < e2k_insn_ebb.length () ? e2k_insn_ebb[uid] : 0;
	  if (JUMP_P (insn))
	    {
	      jclock = clock;
	      jebb = ebb;
	      continue;
	    }
	  bool moved = (uid < e2k_spec_from.length ()
			&& e2k_spec_from[uid] >= 0
			&& e2k_spec_from[uid] != bb->index);
	  bool shares = clock != 0 && ebb != 0 && clock == jclock
			&& ebb == jebb;
	  if ((moved || shares) && e2k_spec_kind (insn) == 1)
	    e2k_ms_set_flag (insn, E2K_MS_SM);
	}
    }
  e2k_spec_from.truncate (0);
}

/* ",sm" only where it is needed.  The passes that run an operation
   where the program might not have (above its guard, in a jump's wide
   instruction, before a conditional return, in a merged chain) flag it
   whatever it reads; an integer operation can trap only on a diagnostic
   operand, so it needs ",sm" only if one of its inputs may be
   diagnostic.  Forward over the CFG: a value may be diagnostic when a
   speculative load, FP operation or division made it, or anything that
   read such a value.  Loads, FP operations, divisions and DAM checks
   keep the flag (they may fail themselves); so do pipelined kernels and
   whatever touches the rotating registers, whose names move.  */

/* The register of R for the analysis: the rotating ones are one.  */
static unsigned
e2k_diag_reg (unsigned r)
{
  return B_REGNO_P (r) || BX_REGNO_P (r) ? (unsigned) B0_REGNUM : r;
}

static bool
e2k_diag_reads_p (rtx x, const HARD_REG_SET &diag)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, x, NONCONST)
    if (REG_P (*iter) && HARD_REGISTER_P (*iter))
      for (unsigned r = REGNO (*iter); r < END_REGNO (*iter); r++)
	if (TEST_HARD_REG_BIT (diag, e2k_diag_reg (r)))
	  return true;
  return false;
}

/* What INSN reads, but the registers it sets.  */
static bool
e2k_diag_insn_reads_p (rtx_insn *insn, const HARD_REG_SET &diag)
{
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) == COND_EXEC)
    {
      if (e2k_diag_reads_p (COND_EXEC_TEST (pat), diag))
	return true;
      pat = COND_EXEC_CODE (pat);
    }
  int n = GET_CODE (pat) == PARALLEL ? XVECLEN (pat, 0) : 1;
  for (int k = 0; k < n; k++)
    {
      rtx x = GET_CODE (pat) == PARALLEL ? XVECEXP (pat, 0, k) : pat;
      if (GET_CODE (x) == SET)
	{
	  if (e2k_diag_reads_p (SET_SRC (x), diag))
	    return true;
	  rtx d = SET_DEST (x);
	  if (MEM_P (d) && e2k_diag_reads_p (XEXP (d, 0), diag))
	    return true;
	}
      else if (GET_CODE (x) != CLOBBER && e2k_diag_reads_p (x, diag))
	return true;
    }
  return false;
}

/* Whether INSN may fail by itself when speculative.  */
static bool
e2k_diag_source_p (rtx_insn *insn)
{
  if (recog_memoized (insn) < 0)
    return true;
  switch (get_attr_type (insn))
    {
    case TYPE_ALU: case TYPE_ALU14: case TYPE_ALU0134: case TYPE_CMP:
    case TYPE_MUL: case TYPE_PINT: case TYPE_PINT14: case TYPE_PMUL:
    case TYPE_PANY: case TYPE_PLOG:
      return false;
    default:
      return true;
    }
}

/* The effect of INSN on DIAG.  */
static void
e2k_diag_step (rtx_insn *insn, HARD_REG_SET *diag)
{
  if (!NONDEBUG_INSN_P (insn) || CALL_P (insn))
    return;
  bool sm = (e2k_ms_flag (insn) & E2K_MS_SM) != 0;
  bool d = e2k_diag_insn_reads_p (insn, *diag)
	   || (sm && e2k_diag_source_p (insn))
	   || (recog_memoized (insn) >= 0
	       && get_attr_type (insn) == TYPE_LDLOCK);
  rtx pat = PATTERN (insn);
  bool partial = GET_CODE (pat) == COND_EXEC;
  if (partial)
    pat = COND_EXEC_CODE (pat);
  int n = GET_CODE (pat) == PARALLEL ? XVECLEN (pat, 0) : 1;
  for (int k = 0; k < n; k++)
    {
      rtx x = GET_CODE (pat) == PARALLEL ? XVECEXP (pat, 0, k) : pat;
      if (GET_CODE (x) != SET && GET_CODE (x) != CLOBBER)
	continue;
      rtx dst = SET_DEST (x);
      bool part = partial;
      if (GET_CODE (dst) == STRICT_LOW_PART || GET_CODE (dst) == ZERO_EXTRACT)
	{
	  dst = XEXP (dst, 0);
	  part = true;
	}
      if (GET_CODE (dst) == SUBREG)
	{
	  dst = SUBREG_REG (dst);
	  part = true;
	}
      if (!REG_P (dst) || !HARD_REGISTER_P (dst))
	continue;
      for (unsigned r = REGNO (dst); r < END_REGNO (dst); r++)
	{
	  unsigned q = e2k_diag_reg (r);
	  if (d && GET_CODE (x) == SET)
	    SET_HARD_REG_BIT (*diag, q);
	  else if (!part && q != (unsigned) B0_REGNUM)
	    CLEAR_HARD_REG_BIT (*diag, q);
	}
    }
}

static void
e2k_spec_prune (void)
{
  int nb = last_basic_block_for_fn (cfun);
  auto_vec<HARD_REG_SET> out;
  out.safe_grow_cleared (nb);
  bool changed = true;
  while (changed)
    {
      changed = false;
      basic_block bb;
      FOR_EACH_BB_FN (bb, cfun)
	{
	  HARD_REG_SET d;
	  CLEAR_HARD_REG_SET (d);
	  edge e;
	  edge_iterator ei;
	  FOR_EACH_EDGE (e, ei, bb->preds)
	    if (e->src != ENTRY_BLOCK_PTR_FOR_FN (cfun))
	      d |= out[e->src->index];
	  rtx_insn *insn;
	  FOR_BB_INSNS (bb, insn)
	    e2k_diag_step (insn, &d);
	  if (d != out[bb->index])
	    {
	      out[bb->index] = d;
	      changed = true;
	    }
	}
    }
  int n = 0;
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    {
      HARD_REG_SET d;
      CLEAR_HARD_REG_SET (d);
      edge e;
      edge_iterator ei;
      FOR_EACH_EDGE (e, ei, bb->preds)
	if (e->src != ENTRY_BLOCK_PTR_FOR_FN (cfun))
	  d |= out[e->src->index];
      rtx_insn *insn;
      FOR_BB_INSNS (bb, insn)
	{
	  if (NONDEBUG_INSN_P (insn)
	      && (e2k_ms_flag (insn) & E2K_MS_SM)
	      && !(bb->flags & BB_DISABLE_SCHEDULE)
	      && !e2k_diag_source_p (insn)
	      && !e2k_diag_insn_reads_p (insn, d))
	    {
	      HARD_REG_SET regs;
	      CLEAR_HARD_REG_SET (regs);
	      e2k_note_regs (PATTERN (insn), &regs);
	      bool rot = false;
	      unsigned r;
	      hard_reg_set_iterator hrsi;
	      EXECUTE_IF_SET_IN_HARD_REG_SET (regs, 0, r, hrsi)
		rot |= B_REGNO_P (r) || BX_REGNO_P (r);
	      if (!rot)
		{
		  e2k_ms_flags[INSN_UID (insn)] &= ~E2K_MS_SM;
		  n++;
		}
	    }
	  e2k_diag_step (insn, &d);
	}
    }
  if (dump_file)
    fprintf (dump_file, ";; e2k_spec_prune: %d without ,sm\n", n);
}

/* Chains of branches to one place, merged as lcc does (zlib's
   longest_match: "if (a != x || b != y || c != z) continue"; the end
   of a loop of such tests): blocks B1 ... Bk, each entered only by
   falling through from the one before and each ending in a branch to
   T, become one block that computes every condition and branches once,
   on their landp (spec/isa/bundle.md, "PLS").  The operations of B2 ...
   Bk then run before the branches that guarded them, speculatively
   (",sm"): a load whose guard didn't hold gives a diagnostic value and
   its compare a diagnostic predicate, which landp ignores as its second
   operand when the first is false (probed on the 4C and the 8C2,
   relcc2 findings I18), so the chain "c1 && c2 && c3" of landps with
   the conditions so far first decides as C does.  The last block may
   instead branch elsewhere (L) and fall through to T: the merged block
   then branches to L when no earlier condition held and its own did.
   Only blocks of operations that have a speculative form, none setting
   a register live at T or a predicate an earlier condition reads.  */

/* The (eq|ne pred 0) on which JUMP, a plain conditional branch, takes
   its label, or NULL.  */
static rtx
e2k_chain_test (rtx_insn *jump)
{
  if (!JUMP_P (jump) || recog_memoized (jump) < 0
      || get_attr_type (jump) != TYPE_BRANCH)
    return NULL_RTX;
  rtx pat = PATTERN (jump);
  if (GET_CODE (pat) != SET || SET_DEST (pat) != pc_rtx)
    return NULL_RTX;
  rtx src = SET_SRC (pat);
  if (GET_CODE (src) != IF_THEN_ELSE || GET_CODE (XEXP (src, 1)) != LABEL_REF
      || XEXP (src, 2) != pc_rtx)
    return NULL_RTX;
  rtx c = XEXP (src, 0);
  if ((GET_CODE (c) != EQ && GET_CODE (c) != NE) || !REG_P (XEXP (c, 0))
      || !PRED_REGNO_P (REGNO (XEXP (c, 0))) || XEXP (c, 1) != const0_rtx)
    return NULL_RTX;
  return c;
}

/* Whether block BB, but its last jump, may run above the branches
   before it: operations with a speculative form only (and landps, with
   PLOG), at most MAXN.  Its registers set go to SETS.  */
static bool
e2k_chain_block_ok (basic_block bb, int maxn, HARD_REG_SET *sets,
		    bool plog = false)
{
  int n = 0;
  rtx_insn *insn;
  CLEAR_HARD_REG_SET (*sets);
  FOR_BB_INSNS (bb, insn)
    {
      if (!NONDEBUG_INSN_P (insn) || insn == BB_END (bb))
	continue;
      if (++n > maxn || GET_CODE (PATTERN (insn)) != SET
	  || (e2k_spec_kind (insn) != 1
	      && !(plog && recog_memoized (insn) >= 0
		   && get_attr_type (insn) == TYPE_PLOG))
	  || !REG_P (SET_DEST (PATTERN (insn)))
	  || side_effects_p (PATTERN (insn))
	  || volatile_refs_p (PATTERN (insn)))
	return false;
      rtx d = SET_DEST (PATTERN (insn));
      add_to_hard_reg_set (sets, GET_MODE (d), REGNO (d));
    }
  return true;
}

static void
e2k_merge_chains (void)
{
  df_analyze ();
  basic_block b1;
  bool changed = false;
  /* The landps' predicates, each set once in the function: two merged
     chains may make one loop, which the pipeliner takes only with every
     predicate set once.  */
  HARD_REG_SET taken;
  CLEAR_HARD_REG_SET (taken);
  FOR_EACH_BB_FN (b1, cfun)
    {
      rtx c1 = e2k_chain_test (BB_END (b1));
      if (!c1 || EDGE_COUNT (b1->succs) != 2)
	continue;
      basic_block t = BRANCH_EDGE (b1)->dest;
      if (t == EXIT_BLOCK_PTR_FOR_FN (cfun) || t == b1)
	continue;
      bitmap live_t = df_get_live_in (t);
      auto_vec<basic_block, 8> chain;
      auto_vec<rtx, 8> conds;	/* Each "stay in the chain".  */
      chain.safe_push (b1);
      conds.safe_push (gen_rtx_fmt_ee (reverse_condition (GET_CODE (c1)),
				       BImode, XEXP (c1, 0), const0_rtx));
      HARD_REG_SET preds, all_sets;
      CLEAR_HARD_REG_SET (preds);
      CLEAR_HARD_REG_SET (all_sets);
      SET_HARD_REG_BIT (preds, REGNO (XEXP (c1, 0)));
      basic_block l = NULL;	/* Variant B: where the last one goes.  */
      int moved = 0;
      basic_block y = FALLTHRU_EDGE (b1)->dest;
      while (chain.length () < 10)
	{
	  if (y == EXIT_BLOCK_PTR_FOR_FN (cfun) || y == t || y == b1
	      || !single_pred_p (y) || EDGE_COUNT (y->succs) != 2)
	    break;
	  rtx cy = e2k_chain_test (BB_END (y));
	  HARD_REG_SET sets;
	  if (!cy || !e2k_chain_block_ok (y, 8, &sets)
	      || hard_reg_set_intersect_p (sets, preds))
	    break;
	  unsigned r;
	  hard_reg_set_iterator hrsi;
	  bool live = false;
	  EXECUTE_IF_SET_IN_HARD_REG_SET (sets, 0, r, hrsi)
	    if (bitmap_bit_p (live_t, r))
	      live = true;
	  if (live)
	    break;
	  edge taken = BRANCH_EDGE (y), fall = FALLTHRU_EDGE (y);
	  if (taken->dest == t)
	    conds.safe_push (gen_rtx_fmt_ee (reverse_condition (GET_CODE (cy)),
					     BImode, XEXP (cy, 0),
					     const0_rtx));
	  else if (fall->dest == t && taken->dest != y)
	    {
	      conds.safe_push (gen_rtx_fmt_ee (GET_CODE (cy), BImode,
					       XEXP (cy, 0), const0_rtx));
	      l = taken->dest;
	    }
	  else
	    break;
	  chain.safe_push (y);
	  all_sets |= sets;
	  SET_HARD_REG_BIT (preds, REGNO (XEXP (cy, 0)));
	  moved++;
	  if (l)
	    break;
	  y = fall->dest;
	}
      unsigned k = chain.length ();
      if (k < 2)
	continue;

      /* Free predicates for the landps: neither live at the chain's
	 ends nor touched in it.  */
      basic_block bk = chain[k - 1];
      HARD_REG_SET used = preds;
      for (basic_block bb : chain)
	{
	  rtx_insn *insn;
	  FOR_BB_INSNS (bb, insn)
	    if (INSN_P (insn))
	      e2k_note_regs (PATTERN (insn), &used);
	}
      bitmap lin = df_get_live_in (b1), lout = df_get_live_out (bk);
      auto_vec<unsigned, 4> free_preds;
      unsigned ngroups = k <= 4 ? 1 : 1 + (k - 4 + 2) / 3;
      for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER
	   && free_preds.length () < ngroups; r++)
	if (PRED_REGNO_P (r) && !fixed_regs[r] && !TEST_HARD_REG_BIT (used, r)
	    && !TEST_HARD_REG_BIT (taken, r)
	    && !bitmap_bit_p (lin, r) && !bitmap_bit_p (lout, r)
	    && !bitmap_bit_p (live_t, r))
	  free_preds.safe_push (r);
      /* Short of them, share.  */
      for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER
	   && free_preds.length () < ngroups; r++)
	if (PRED_REGNO_P (r) && !fixed_regs[r] && !TEST_HARD_REG_BIT (used, r)
	    && TEST_HARD_REG_BIT (taken, r)
	    && !bitmap_bit_p (lin, r) && !bitmap_bit_p (lout, r)
	    && !bitmap_bit_p (live_t, r))
	  free_preds.safe_push (r);
      if (free_preds.length () < ngroups)
	continue;
      for (unsigned r : free_preds)
	SET_HARD_REG_BIT (taken, r);

      /* The landps, before Bk's jump: the first takes up to four
	 conditions, each next one the result so far and up to three.  */
      rtx_insn *jk = BB_END (bk);
      rtx acc = NULL_RTX;
      unsigned i = 0, g = 0;
      bool ok = true;
      while (i < k)
	{
	  rtx ops[4];
	  int n = 0;
	  if (acc)
	    ops[n++] = acc;
	  while (n < 4 && i < k)
	    ops[n++] = conds[i++];
	  /* e2k_landp, e2k_landp3, e2k_landp4 (a tree).  */
	  rtx e = gen_rtx_AND (BImode, ops[0], ops[1]);
	  if (n == 3)
	    e = gen_rtx_AND (BImode, e, ops[2]);
	  else if (n == 4)
	    e = gen_rtx_AND (BImode, e, gen_rtx_AND (BImode, ops[2], ops[3]));
	  rtx dst = gen_rtx_REG (BImode, free_preds[g++]);
	  rtx_insn *li = emit_insn_before (gen_rtx_SET (dst, e), jk);
	  if (recog_memoized (li) < 0)
	    ok = false;
	  acc = gen_rtx_NE (BImode, dst, const0_rtx);
	}
      gcc_assert (ok);
      /* Bk's jump: to L when they all hold (B), else to T when they
	 don't (A).  */
      rtx src = SET_SRC (PATTERN (jk));
      rtx newc = gen_rtx_fmt_ee (l ? NE : EQ, VOIDmode, XEXP (acc, 0),
				 const0_rtx);
      XEXP (src, 0) = newc;
      INSN_CODE (jk) = -1;
      if (recog_memoized (jk) < 0)
	gcc_unreachable ();
      df_insn_rescan (jk);

      /* The probability of staying: the product of each one's.  */
      profile_probability stay = profile_probability::always ();
      for (unsigned j = 0; j < k; j++)
	{
	  edge f = FALLTHRU_EDGE (chain[j]);
	  edge b = BRANCH_EDGE (chain[j]);
	  if (l && j == k - 1)
	    stay = stay * b->probability;
	  else
	    stay = stay * f->probability;
	}
      edge to_t = l ? FALLTHRU_EDGE (bk) : BRANCH_EDGE (bk);
      edge on = l ? BRANCH_EDGE (bk) : FALLTHRU_EDGE (bk);
      on->probability = stay;
      to_t->probability = stay.invert ();
      if (rtx note = find_reg_note (jk, REG_BR_PROB, NULL_RTX))
	XINT (note, 0) = BRANCH_EDGE (bk)->probability.to_reg_br_prob_note ();

      /* The earlier jumps go, and the blocks become one.  */
      for (unsigned j = 0; j + 1 < k; j++)
	{
	  rtx_insn *jj = BB_END (chain[j]);
	  remove_edge (BRANCH_EDGE (chain[j]));
	  single_succ_edge (chain[j])->probability
	    = profile_probability::always ();
	  delete_insn (jj);
	}
      for (unsigned j = 1; j < k; j++)
	{
	  rtx_insn *insn;
	  FOR_BB_INSNS (chain[j], insn)
	    if (NONDEBUG_INSN_P (insn) && !JUMP_P (insn)
		&& e2k_spec_kind (insn) == 1)
	      e2k_ms_set_flag (insn, E2K_MS_SM);
	}
      for (unsigned j = 1; j < k; j++)
	{
	  gcc_assert (can_merge_blocks_p (b1, chain[j]));
	  merge_blocks (b1, chain[j]);
	}
      if (dump_file)
	fprintf (dump_file, ";; e2k_merge_chains: bb %d, %u branches%s\n",
		 b1->index, k, l ? " (last elsewhere)" : "");
      changed = true;
    }
  if (changed)
    df_analyze ();
}

/* A loop H that exits by a conditional jump and falls through into a
   block that only jumps back to H, as block reordering may leave a
   do-while (zlib's inflate_fast copy, whose unsigned count could wrap,
   so not a hardware loop): branch back to H on the inverted condition
   instead, and from the other block to the exit, the one-block while
   loop e2k_ms_wloop pipelines.  */
static void
e2k_ms_fold_latches (void)
{
  basic_block h;
  FOR_EACH_BB_FN (h, cfun)
    {
      rtx_insn *jump = BB_END (h);
      if (!e2k_chain_test (jump) || EDGE_COUNT (h->succs) != 2)
	continue;
      edge ex = BRANCH_EDGE (h), ft = FALLTHRU_EDGE (h);
      basic_block l = ft->dest, x = ex->dest;
      if (l == h || x == h || l == x || l == EXIT_BLOCK_PTR_FOR_FN (cfun)
	  || x == EXIT_BLOCK_PTR_FOR_FN (cfun) || !single_pred_p (l)
	  || !single_succ_p (l) || single_succ (l) != h
	  || (single_succ_edge (l)->flags & EDGE_COMPLEX)
	  || (ex->flags & EDGE_COMPLEX))
	continue;
      /* The other block's operations, register copies and the like
	 (zlib's has one), go into H before its jump: they must set a
	 register dead at the exit that the jump doesn't read, and run
	 speculatively, for they now run when the loop exits too (SQLite's
	 destroyTable: the next index's tnum loaded from a null pIdx).  */
      rtx_insn *lj = BB_END (l), *insn;
      bool ok = JUMP_P (lj) && simplejump_p (lj);
      auto_vec<rtx_insn *> moves;
      FOR_BB_INSNS (l, insn)
	if (NONDEBUG_INSN_P (insn) && insn != lj)
	  {
	    rtx set = single_set (insn);
	    if (!set || !REG_P (SET_DEST (set)) || side_effects_p (set)
		|| volatile_refs_p (set)
		|| GET_CODE (PATTERN (insn)) != SET
		|| REGNO_REG_SET_P (df_get_live_in (x), REGNO (SET_DEST (set)))
		|| reg_mentioned_p (SET_DEST (set), PATTERN (jump))
		|| e2k_spec_kind (insn) == 0)
	      ok = false;
	    moves.safe_push (insn);
	  }
      if (!ok || moves.length () > 4)
	continue;
      if (!invert_jump (as_a <rtx_jump_insn *> (jump), block_label (h), 0))
	continue;
      for (rtx_insn *m : moves)
	{
	  rtx_insn *c = emit_insn_before (copy_rtx (PATTERN (m)), jump);
	  INSN_LOCATION (c) = INSN_LOCATION (m);
	  if (e2k_spec_kind (c) == 1)
	    e2k_ms_set_flag (c, E2K_MS_SM);
	  delete_insn (m);
	}
      profile_probability pe = ex->probability;
      redirect_edge_succ (ex, h);
      ex->probability = ft->probability;
      ft->probability = pe;
      redirect_edge_and_branch (single_succ_edge (l), x);
      if (dump_file)
	fprintf (dump_file, ";; e2k_ms_fold_latches: bb %d loops on itself\n",
		 h->index);
    }
}

/* A while loop of two blocks, H exiting and B looping back to H (the
   form e2k_ms_wloop pipelines), whose B is entered from elsewhere too
   (zlib's longest_match: after a match the rare path comes back to the
   chain walk's step): B is copied for the other ways in, at the end of
   the function, so that the loop has one.  Only a small B of operations
   that can run speculatively, as the pipeliner needs anyway.  */
static void
e2k_ms_tail_dup (void)
{
  basic_block h;
  bool changed = false;
  FOR_EACH_BB_FN (h, cfun)
    {
      if (!e2k_chain_test (BB_END (h)) || EDGE_COUNT (h->succs) != 2)
	continue;
      edge f = FALLTHRU_EDGE (h);
      basic_block b = f->dest;
      if (b == h || b == EXIT_BLOCK_PTR_FOR_FN (cfun) || single_pred_p (b)
	  || EDGE_COUNT (b->succs) != 2 || BRANCH_EDGE (h)->dest == b)
	continue;
      rtx_insn *bj = BB_END (b);
      if (!e2k_chain_test (bj) || BRANCH_EDGE (b)->dest != h)
	continue;
      basic_block x = FALLTHRU_EDGE (b)->dest;
      HARD_REG_SET sets;
      if (x == EXIT_BLOCK_PTR_FOR_FN (cfun) || x == h
	  || !e2k_chain_block_ok (b, 12, &sets, true))
	continue;
      auto_vec<edge, 2> others;
      edge e;
      edge_iterator ei;
      bool bad = false;
      FOR_EACH_EDGE (e, ei, b->preds)
	if (e != f)
	  {
	    if ((e->flags & (EDGE_COMPLEX | EDGE_FALLTHRU))
		|| !JUMP_P (BB_END (e->src)))
	      bad = true;
	    others.safe_push (e);
	  }
      if (bad || others.length () > 2)
	continue;
      for (edge o : others)
	{
	  /* B': B's operations and its branch back to H; then a block
	     that goes to X.  */
	  rtx_insn *last = get_last_insn ();
	  rtx_code_label *l1 = gen_label_rtx ();
	  rtx_insn *x1 = emit_label_after (l1, last);
	  rtx_insn *head = x1;
	  rtx_insn *insn;
	  FOR_BB_INSNS (b, insn)
	    if (NONDEBUG_INSN_P (insn) && insn != bj)
	      {
		x1 = emit_insn_after (copy_rtx (PATTERN (insn)), x1);
		INSN_LOCATION (x1) = INSN_LOCATION (insn);
		e2k_ms_set_flag (x1, e2k_ms_flag (insn));
	      }
	  rtx hl = JUMP_LABEL (bj);
	  rtx_insn *cj = emit_jump_insn_after (copy_rtx (PATTERN (bj)), x1);
	  JUMP_LABEL (cj) = hl;
	  LABEL_NUSES (hl)++;
	  INSN_LOCATION (cj) = INSN_LOCATION (bj);
	  rtx xl = block_label (x);
	  rtx_insn *j2 = emit_jump_insn_after (gen_jump (xl), cj);
	  JUMP_LABEL (j2) = xl;
	  LABEL_NUSES (xl)++;
	  emit_barrier_after (j2);
	  /* The blocks only now: emitting after a block's end extends it.  */
	  basic_block nb = create_basic_block (head, cj,
					       EXIT_BLOCK_PTR_FOR_FN (cfun)
					       ->prev_bb);
	  basic_block nb2 = create_basic_block (j2, j2, nb);
	  for (rtx_insn *y = head; y != NEXT_INSN (j2); y = NEXT_INSN (y))
	    if (INSN_P (y) && recog_memoized (y) < 0)
	      gcc_unreachable ();
	  nb->count = o->count ();
	  nb2->count = nb->count.apply_probability
	    (FALLTHRU_EDGE (b)->probability);
	  edge eh = make_edge (nb, h, 0);
	  eh->probability = BRANCH_EDGE (b)->probability;
	  edge ef = make_edge (nb, nb2, EDGE_FALLTHRU);
	  ef->probability = FALLTHRU_EDGE (b)->probability;
	  make_single_succ_edge (nb2, x, 0);
	  if (!redirect_edge_and_branch (o, nb))
	    gcc_unreachable ();
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_ms_tail_dup: bb %d copied as bb %d "
		     "for bb %d\n", b->index, nb->index, o->src->index);
	  changed = true;
	}
    }
  if (changed)
    df_analyze ();
}

/* Conditional latches (bzip2's unRLE: the eq_one block, a join that
   stores the byte, updates the CRC and jumps back to the loop's top,
   entered from the avail test): a block B whose branch goes to a block J
   that ends in a jump to X, X dominating B, gets J's operations before
   its branch and branches to X itself.  Like e2k_cond_return_from:
   stores go under B's condition; a register dead on B's other way is
   written as it is (",sm"), one live there under the condition when it
   is J's last write of it and X needs it, else into a free register,
   copied back under the condition for X.  The cycle loses a block and a
   taken jump, and J's operations schedule with B's.  */

/* J's operations (but its jump) into BODY, if they qualify.  */
static bool
e2k_latch_body (basic_block j, vec<rtx_insn *> *body)
{
  rtx_insn *insn;
  FOR_BB_INSNS (j, insn)
    {
      if (!NONDEBUG_INSN_P (insn) || insn == BB_END (j))
	continue;
      rtx set = single_set (insn);
      if (!NONJUMP_INSN_P (insn) || !set || PATTERN (insn) != set
	  || recog_memoized (insn) < 0 || body->length () == 16
	  || volatile_insn_p (PATTERN (insn)) || side_effects_p (set)
	  || volatile_refs_p (set)
	  || e2k_asm_insn_p (insn) || get_attr_mas (insn) == MAS_YES)
	return false;
      rtx d = SET_DEST (set);
      enum attr_type t = get_attr_type (insn);
      if (MEM_P (d) ? t != TYPE_STORE : !REG_P (d) || REG_NREGS (d) > 1)
	return false;
      body->safe_push (insn);
    }
  return !body->is_empty ();
}

/* Copy BODY, J's operations, into B before its branch to J, under its
   condition where needed; B's branch then goes to X.  */
static bool
e2k_cond_latch_from (basic_block b, basic_block x,
		     const vec<rtx_insn *> &body, unsigned wtop)
{
  rtx_insn *jump = BB_END (b);
  rtx c = e2k_chain_test (jump);
  if (!c)
    return false;
  basic_block f = FALLTHRU_EDGE (b)->dest;
  if (f == x)
    return false;
  bitmap live_f = df_get_live_in (f), live_x = df_get_live_in (x);
  auto_bitmap live;
  bitmap_ior (live, df_get_live_out (b), live_f);
  bitmap_ior_into (live, live_x);
  HARD_REG_SET busy, ld;
  CLEAR_HARD_REG_SET (busy);
  CLEAR_HARD_REG_SET (ld);
  rtx_insn *insn;
  FOR_BB_INSNS (b, insn)
    if (NONDEBUG_INSN_P (insn))
      e2k_note_regs (PATTERN (insn), &busy);
  for (rtx_insn *i : body)
    e2k_note_regs (PATTERN (i), &busy);
  auto overlaps = [] (rtx r, bitmap set)
    {
      for (unsigned q = REGNO (r); q < END_REGNO (r); q++)
	if (bitmap_bit_p (set, q))
	  return true;
      return false;
    };
  auto reads = [] (rtx x, const HARD_REG_SET &set)
    {
      subrtx_iterator::array_type array;
      FOR_EACH_SUBRTX (iter, array, x, NONCONST)
	if (REG_P (*iter) && HARD_REGISTER_P (*iter)
	    && overlaps_hard_reg_set_p (set, GET_MODE (*iter), REGNO (*iter)))
	  return true;
      return false;
    };
  /* The last write of each register in BODY.  */
  int lastw[FIRST_PSEUDO_REGISTER];
  for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    lastw[r] = -1;
  for (unsigned k = 0; k < body.length (); k++)
    {
      rtx d = SET_DEST (PATTERN (body[k]));
      if (REG_P (d))
	lastw[REGNO (d)] = k;
    }
  rtx map[FIRST_PSEUDO_REGISTER];
  memset (map, 0, sizeof map);
  auto subst = [&] (rtx *loc)
    {
      subrtx_ptr_iterator::array_type array;
      FOR_EACH_SUBRTX_PTR (iter, array, loc, NONCONST)
	if (REG_P (**iter) && HARD_REGISTER_P (**iter) && map[REGNO (**iter)])
	  **iter = gen_rtx_REG (GET_MODE (**iter),
				REGNO (map[REGNO (**iter)]));
    };
  auto guarded = [&] (rtx set)
    {
      return gen_rtx_COND_EXEC (VOIDmode, copy_rtx (c), set);
    };
  auto recogs = [] (rtx pat)
    {
      return recog_memoized (make_insn_raw (pat)) >= 0;
    };
  auto_vec<unsigned, 8> as_is;
  start_sequence ();
  bool ok = true;
  for (unsigned k = 0; k < body.length () && ok; k++)
    {
      rtx_insn *i = body[k];
      rtx set = copy_rtx (PATTERN (i));
      subst (&SET_SRC (set));
      rtx d = SET_DEST (set);
      if (MEM_P (d))
	{
	  /* No store of what a copied load gave: under a false
	     predicate a diagnostic operand isn't known to be ignored.  */
	  subst (&XEXP (d, 0));
	  rtx ce = guarded (set);
	  if (reads (SET_SRC (set), ld) || reads (XEXP (d, 0), ld)
	      || !recogs (ce))
	    ok = false;
	  else
	    INSN_LOCATION (emit_insn (ce)) = INSN_LOCATION (i);
	  continue;
	}
      unsigned dr = REGNO (d);
      bool load = get_attr_type (i) == TYPE_LOAD;
      bool tainted = load || reads (SET_SRC (set), ld);
      bool spec = e2k_spec_kind (i) == 1;
      bool in_f = overlaps (d, live_f), in_x = overlaps (d, live_x);
      bool last = lastw[dr] == (int) k;
      bool must_rename = (reg_overlap_mentioned_p (d, PATTERN (jump))
			  || (load && reg_overlap_mentioned_p (d, SET_SRC (set))));
      rtx dest = d;
      if (!must_rename && !in_f && spec)
	{
	  INSN_LOCATION (emit_insn (set)) = INSN_LOCATION (i);
	  map[dr] = NULL_RTX;
	  as_is.safe_push (dr);
	}
      else if (!must_rename && in_f && last && in_x && recogs (guarded (set)))
	{
	  INSN_LOCATION (emit_insn (guarded (set))) = INSN_LOCATION (i);
	  map[dr] = NULL_RTX;
	}
      else if (spec)
	{
	  unsigned t = FIRST_PSEUDO_REGISTER;
	  for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
	    if (PRED_REGNO_P (r) == PRED_REGNO_P (dr)
		&& e2k_rename_free_p (r, GET_MODE (d), live, busy, wtop))
	      {
		t = r;
		break;
	      }
	  if (t == FIRST_PSEUDO_REGISTER)
	    {
	      ok = false;
	      break;
	    }
	  SET_HARD_REG_BIT (busy, t);
	  dest = gen_rtx_REG (GET_MODE (d), t);
	  SET_DEST (set) = dest;
	  INSN_LOCATION (emit_insn (set)) = INSN_LOCATION (i);
	  map[dr] = dest;
	  if (last && in_x)
	    {
	      /* The predicate B's jump reads can't be written before it.  */
	      if (reg_overlap_mentioned_p (d, PATTERN (jump)))
		{
		  ok = false;
		  break;
		}
	      rtx cb = guarded (gen_rtx_SET (d, dest));
	      if (!recogs (cb))
		{
		  ok = false;
		  break;
		}
	      INSN_LOCATION (emit_insn (cb)) = INSN_LOCATION (i);
	    }
	}
      else if (!must_rename && recogs (guarded (set)))
	{
	  INSN_LOCATION (emit_insn (guarded (set))) = INSN_LOCATION (i);
	  map[dr] = NULL_RTX;
	}
      else
	ok = false;
      if (tainted)
	add_to_hard_reg_set (&ld, GET_MODE (dest), REGNO (dest));
      else
	remove_from_hard_reg_set (&ld, GET_MODE (dest), REGNO (dest));
    }
  rtx_insn *seq = end_sequence ();
  if (!ok)
    return false;
  for (rtx_insn *y = seq; y; y = NEXT_INSN (y))
    if (recog_memoized (y) < 0)
      return false;
  for (rtx_insn *y = seq; y; y = NEXT_INSN (y))
    if (GET_CODE (PATTERN (y)) != COND_EXEC)
      e2k_ms_set_flag (y, E2K_MS_SM);
  emit_insn_before (seq, jump);
  /* What the copies write as they are, the other way still reads in
     debug binds.  */
  for (unsigned r : as_is)
    e2k_arm_reset_debug (BB_HEAD (f), BB_END (f), gen_rtx_REG (DImode, r));
  if (!redirect_edge_and_branch (BRANCH_EDGE (b), x))
    gcc_unreachable ();
  return true;
}

static void
e2k_cond_latches (void)
{
  df_analyze ();
  unsigned wtop = e2k_window_top ();
  struct cand { basic_block b, j, x; };
  auto_vec<cand, 16> cands;
  loop_optimizer_init (AVOID_CFG_MODIFICATIONS);
  calculate_dominance_info (CDI_DOMINATORS);
  basic_block j;
  FOR_EACH_BB_FN (j, cfun)
    {
      rtx_insn *r = BB_END (j);
      if (!JUMP_P (r) || !simplejump_p (r) || !single_succ_p (j))
	continue;
      basic_block x = single_succ (j);
      class loop *l = j->loop_father;
      if (x == j || x == EXIT_BLOCK_PTR_FOR_FN (cfun)
	  || (single_succ_edge (j)->flags & EDGE_COMPLEX)
	  || (l && l != current_loops->tree_root && !l->inner
	      && l->num_nodes <= 3))
	continue;
      int n = 0;
      edge e;
      edge_iterator ei;
      FOR_EACH_EDGE (e, ei, j->preds)
	{
	  basic_block b = e->src;
	  if (n == 2 || (e->flags & (EDGE_FALLTHRU | EDGE_COMPLEX))
	      || b == ENTRY_BLOCK_PTR_FOR_FN (cfun)
	      || EDGE_COUNT (b->succs) != 2 || BRANCH_EDGE (b) != e
	      || !e2k_chain_test (BB_END (b))
	      || FALLTHRU_EDGE (b)->dest == x
	      || !dominated_by_p (CDI_DOMINATORS, b, x))
	    continue;
	  cand cd = { b, j, x };
	  cands.safe_push (cd);
	  n++;
	}
    }
  loop_optimizer_finalize ();
  free_dominance_info (CDI_DOMINATORS);
  bool changed = false;
  for (cand &cd : cands)
    {
      /* An earlier conversion may have changed B or emptied J.  */
      if (EDGE_COUNT (cd.b->succs) != 2 || BRANCH_EDGE (cd.b)->dest != cd.j
	  || !single_succ_p (cd.j) || single_succ (cd.j) != cd.x)
	continue;
      auto_vec<rtx_insn *, 16> body;
      if (!e2k_latch_body (cd.j, &body))
	continue;
      if (!e2k_cond_latch_from (cd.b, cd.x, body, wtop))
	continue;
      if (dump_file)
	fprintf (dump_file, ";; e2k_cond_latches: bb %d does bb %d and goes "
		 "to bb %d\n", cd.b->index, cd.j->index, cd.x->index);
      changed = true;
      df_analyze ();
    }
  basic_block jn;
  for (j = ENTRY_BLOCK_PTR_FOR_FN (cfun)->next_bb;
       j != EXIT_BLOCK_PTR_FOR_FN (cfun); j = jn)
    {
      jn = j->next_bb;
      if (changed && EDGE_COUNT (j->preds) == 0)
	delete_basic_block (j);
    }
  if (changed)
    df_analyze ();
}

/* A small join block J entered by falling through from a conditional
   branch, and by jumps from elsewhere (xz's bt4_skip: the mismatch step
   of the tree walk, which the match path's ends jump back to): its
   label ends the extended block there, and the 3 cycles a ct waits for
   its compare stay empty, while J's loads and compares could fill them.
   Copy J for the jumps, at the end of the function, so that only the
   fall-through enters it and its label goes.  When the fall-through is
   the hotter way in; J of plain operations, ending in a jump or falling
   through.  */
static void
e2k_tail_dup_joins (void)
{
  df_analyze ();
  /* Innermost loops of up to three blocks keep their shape for the
     pipeliner (e2k_cond_returns' rule).  */
  auto_bitmap small;
  loop_optimizer_init (AVOID_CFG_MODIFICATIONS);
  {
    basic_block b;
    FOR_EACH_BB_FN (b, cfun)
      {
	class loop *l = b->loop_father;
	if (l && l != current_loops->tree_root && !l->inner
	    && l->num_nodes <= 3)
	  bitmap_set_bit (small, b->index);
      }
  }
  loop_optimizer_finalize ();
  free_dominance_info (CDI_DOMINATORS);
  int budget = 64;
  bool changed = false;
  /* Blocks from here on are copies and the jumps after them.  */
  int first_new = last_basic_block_for_fn (cfun);
  auto_bitmap had_label;
  {
    basic_block b;
    FOR_EACH_BB_FN (b, cfun)
      if (LABEL_P (BB_HEAD (b)))
	bitmap_set_bit (had_label, b->index);
  }
  auto_vec<basic_block> js;
  basic_block j;
  FOR_EACH_BB_FN (j, cfun)
    js.safe_push (j);
  for (basic_block j : js)
    {
      if (!LABEL_P (BB_HEAD (j)) || (j->flags & BB_DISABLE_SCHEDULE)
	  || bitmap_bit_p (small, j->index)
	  || EDGE_COUNT (j->preds) < 2 || EDGE_COUNT (j->preds) > 4
	  || EDGE_COUNT (j->succs) > 2)
	continue;
      edge f = NULL, e;
      edge_iterator ei;
      bool ok = true;
      FOR_EACH_EDGE (e, ei, j->preds)
	{
	  /* The jump after another copy, to the K it gave a label: copy K
	     too, so that the hot chain stays one extended block
	     (CoreMark's state machine, CoreMark 2.5% faster).  Not when K
	     was a join already: then only the way from that copy gets one
	     more jump (xz's bt4_skip, whose tree walk goes either way).  */
	  if (e->src == ENTRY_BLOCK_PTR_FOR_FN (cfun)
	      || (e->flags & EDGE_COMPLEX)
	      || (e->src->index >= first_new
		  && bitmap_bit_p (had_label, j->index))
	      || bitmap_bit_p (small, e->src->index))
	    ok = false;
	  else if (e->flags & EDGE_FALLTHRU)
	    f = e;
	  /* Plain branches only: not a counted loop's end (e2k_hwloop_end,
	     a conditional jump too), whose loop would get two ends.  */
	  else if (!JUMP_P (BB_END (e->src))
		   || (!e2k_chain_test (BB_END (e->src))
		       && !simplejump_p (BB_END (e->src)))
		   || (e->src->flags & BB_DISABLE_SCHEDULE))
	    ok = false;
	}
      if (!ok || !f || !e2k_chain_test (BB_END (f->src))
	  || (f->src->flags & BB_DISABLE_SCHEDULE))
	continue;
      /* The fall-through the hotter way in.  */
      profile_count others = profile_count::zero ();
      FOR_EACH_EDGE (e, ei, j->preds)
	if (e != f)
	  others += e->count ();
      if (!(f->count () > others))
	continue;
      /* Plain operations; a jump at the end, or a fall-through.  */
      rtx_insn *last = BB_END (j), *insn;
      int n = 0;
      FOR_BB_INSNS (j, insn)
	if (NONDEBUG_INSN_P (insn))
	  {
	    if (insn == last && JUMP_P (insn))
	      {
		if (!JUMP_LABEL (insn) || ANY_RETURN_P (JUMP_LABEL (insn))
		    || recog_memoized (insn) < 0
		    || (!e2k_chain_test (insn) && !simplejump_p (insn)))
		  ok = false;
		continue;
	      }
	    if (!NONJUMP_INSN_P (insn) || recog_memoized (insn) < 0
		|| e2k_asm_insn_p (insn) || volatile_insn_p (PATTERN (insn))
		|| GET_CODE (PATTERN (insn)) == USE)
	      ok = false;
	    n++;
	  }
      if (!ok || n == 0 || n > 16)
	continue;
      edge ft = find_fallthru_edge (j->succs);
      basic_block k = ft ? ft->dest : NULL;
      if (ft && (k == EXIT_BLOCK_PTR_FOR_FN (cfun) || (ft->flags & EDGE_COMPLEX)))
	continue;
      /* A copy that goes on to K jumps there: each way in from elsewhere
	 that does takes one more transfer (an unconditional ct waits 5
	 cycles for its disp), for the few cycles the fall-through's ct
	 waited.  Only when the fall-through is 4 times hotter than those
	 (bzip2's unRLE, a chain of such joins, ran 20% slower).  */
      if (k)
	{
	  profile_count extra = others;
	  if (JUMP_P (last))
	    extra = others.apply_probability (ft->probability);
	  if (!(f->count () > extra.apply_scale (4, 1)))
	    continue;
	}
      auto_vec<edge, 4> others_v;
      FOR_EACH_EDGE (e, ei, j->preds)
	if (e != f)
	  others_v.safe_push (e);
      if ((int) others_v.length () * n > budget)
	continue;
      budget -= others_v.length () * n;
      bool cond = JUMP_P (last) && e2k_chain_test (last);
      for (edge o : others_v)
	{
	  /* J': J's operations and its jump; then, if J falls through, a
	     block that jumps to where it went.  */
	  rtx_insn *end = get_last_insn ();
	  rtx_code_label *lab = gen_label_rtx ();
	  rtx_insn *x = emit_label_after (lab, end);
	  rtx_insn *head = x;
	  FOR_BB_INSNS (j, insn)
	    if (NONDEBUG_INSN_P (insn) && !(JUMP_P (insn) && insn == last))
	      {
		x = emit_insn_after (copy_rtx (PATTERN (insn)), x);
		INSN_LOCATION (x) = INSN_LOCATION (insn);
		e2k_ms_set_flag (x, e2k_ms_flag (insn));
	      }
	  rtx_insn *cj = NULL;
	  if (JUMP_P (last))
	    {
	      rtx tl = JUMP_LABEL (last);
	      cj = emit_jump_insn_after (copy_rtx (PATTERN (last)), x);
	      JUMP_LABEL (cj) = tl;
	      LABEL_NUSES (tl)++;
	      INSN_LOCATION (cj) = INSN_LOCATION (last);
	      x = cj;
	    }
	  rtx_insn *j2 = NULL;
	  if (k)
	    {
	      rtx kl = block_label (k);
	      j2 = emit_jump_insn_after (gen_jump (kl), x);
	      JUMP_LABEL (j2) = kl;
	      LABEL_NUSES (kl)++;
	      x = j2;
	    }
	  emit_barrier_after (x);
	  for (rtx_insn *y = head; y != NEXT_INSN (x); y = NEXT_INSN (y))
	    if (INSN_P (y) && recog_memoized (y) < 0)
	      gcc_unreachable ();
	  basic_block after = EXIT_BLOCK_PTR_FOR_FN (cfun)->prev_bb;
	  basic_block nb, nb2 = NULL;
	  if (cond && k)
	    {
	      nb = create_basic_block (head, cj, after);
	      nb2 = create_basic_block (j2, j2, nb);
	    }
	  else
	    nb = create_basic_block (head, x, after);
	  nb->count = o->count ();
	  edge je;
	  edge_iterator jei;
	  FOR_EACH_EDGE (je, jei, j->succs)
	    {
	      if (nb2 && (je->flags & EDGE_FALLTHRU))
		{
		  edge e1 = make_edge (nb, nb2, EDGE_FALLTHRU);
		  e1->probability = je->probability;
		  nb2->count = nb->count.apply_probability (je->probability);
		  make_single_succ_edge (nb2, k, 0);
		}
	      else
		{
		  edge e1 = make_edge (nb, je->dest, 0);
		  e1->probability = je->probability;
		}
	    }
	  if (!redirect_edge_and_branch (o, nb))
	    gcc_unreachable ();
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_tail_dup_joins: bb %d copied as bb %d "
		     "for bb %d\n", j->index, nb->index, o->src->index);
	  changed = true;
	}
      /* Only the fall-through left: no label to stop sched-ebb.  */
      if (LABEL_NUSES (BB_HEAD (j)) == 0 && !LABEL_PRESERVE_P (BB_HEAD (j))
	  && !LABEL_NAME (BB_HEAD (j)) && single_pred_p (j))
	delete_insn (BB_HEAD (j));
    }
  if (changed)
    df_analyze ();
}

/* Loop invariants that the middle end sank back into a loop (bzip2's
   unRLE: "bs * 100000", which lim2 hoisted and sink2 put back after
   jump threading had made the loop irreducible to it), moved onto the
   loop's ways in: a single set that can't trap and reads no memory,
   whose sources nothing in the loop writes, whose register nothing else
   in the loop sets and neither the loop's top nor any place it leaves
   to reads before.  */
/* The rwd %lsr of the block E comes from, when that sets up a
   hardware loop (an e2k_lsr_wait after it).  */
static rtx_insn *
e2k_hoist_rwd (edge e)
{
  rtx_insn *rwd = NULL, *insn;
  bool wait = false;
  if (e->src == ENTRY_BLOCK_PTR_FOR_FN (cfun))
    return NULL;
  FOR_BB_INSNS (e->src, insn)
    if (NONDEBUG_INSN_P (insn))
      {
	if (recog_memoized (insn) == CODE_FOR_e2k_rwd_lsr)
	  rwd = insn;
	else if (recog_memoized (insn) == CODE_FOR_e2k_lsr_wait)
	  wait = true;
      }
  return wait ? rwd : NULL;
}

static void
e2k_hoist_invariants (void)
{
  df_analyze ();
  loop_optimizer_init (AVOID_CFG_MODIFICATIONS);
  int n = 0;
  for (auto loop : loops_list (cfun, 0))
    {
      basic_block *bbs = get_loop_body (loop);
      HARD_REG_SET set_in_loop;
      CLEAR_HARD_REG_SET (set_in_loop);
      bool calls = false;
      for (unsigned k = 0; k < loop->num_nodes; k++)
	{
	  rtx_insn *insn;
	  FOR_BB_INSNS (bbs[k], insn)
	    if (NONDEBUG_INSN_P (insn))
	      {
		if (CALL_P (insn) || e2k_asm_insn_p (insn))
		  calls = true;
		df_ref def;
		FOR_EACH_INSN_DEF (def, insn)
		  if (DF_REF_REGNO (def) < FIRST_PSEUDO_REGISTER)
		    SET_HARD_REG_BIT (set_in_loop, DF_REF_REGNO (def));
	      }
	}
      auto_vec<edge> entries, exits;
      edge e;
      edge_iterator ei;
      bool ok = !calls;
      FOR_EACH_EDGE (e, ei, loop->header->preds)
	if (!flow_bb_inside_loop_p (loop, e->src))
	  {
	    if (e->flags & EDGE_COMPLEX)
	      ok = false;
	    entries.safe_push (e);
	  }
      for (edge x : get_loop_exit_edges (loop))
	exits.safe_push (x);
      if (!ok || entries.is_empty ())
	{
	  free (bbs);
	  continue;
	}
      for (unsigned k = 0; k < loop->num_nodes; k++)
	{
	  basic_block bb = bbs[k];
	  if (bb->loop_father != loop || (bb->flags & BB_DISABLE_SCHEDULE))
	    continue;
	  rtx_insn *insn, *next;
	  for (insn = BB_HEAD (bb); insn != NEXT_INSN (BB_END (bb)); insn = next)
	    {
	      next = NEXT_INSN (insn);
	      if (!NONJUMP_INSN_P (insn) || recog_memoized (insn) < 0)
		continue;
	      rtx set = single_set (insn);
	      if (!set || set != PATTERN (insn) || !REG_P (SET_DEST (set))
		  || e2k_spec_kind (insn) != 1
		  || get_attr_type (insn) == TYPE_LOAD
		  || side_effects_p (set) || volatile_refs_p (set))
		continue;
	      rtx d = SET_DEST (set);
	      /* Sources the loop doesn't write; the register set only
		 here.  */
	      bool inv = true;
	      subrtx_iterator::array_type array;
	      FOR_EACH_SUBRTX (iter, array, SET_SRC (set), NONCONST)
		if (MEM_P (*iter)
		    || (REG_P (*iter)
			&& overlaps_hard_reg_set_p (set_in_loop,
						    GET_MODE (*iter),
						    REGNO (*iter))))
		  inv = false;
	      if (!inv)
		continue;
	      int sets = 0;
	      for (unsigned q = 0; q < loop->num_nodes; q++)
		{
		  rtx_insn *y;
		  FOR_BB_INSNS (bbs[q], y)
		    if (NONDEBUG_INSN_P (y) && reg_set_p (d, y))
		      sets++;
		}
	      if (sets != 1)
		continue;
	      bool live = false;
	      for (unsigned r = REGNO (d); r < END_REGNO (d); r++)
		{
		  live |= bitmap_bit_p (df_get_live_in (loop->header), r);
		  for (edge x : exits)
		    live |= bitmap_bit_p (df_get_live_in (x->dest), r);
		}
	      if (live)
		continue;
	      /* A hardware loop's way in ends in rwd %lsr and its wait,
		 which the pipeliner looks for: before them there.  */
	      bool placed = true;
	      for (edge en : entries)
		if (e2k_hoist_rwd (en) && !single_succ_p (en->src))
		  placed = false;
	      if (!placed)
		continue;
	      for (edge en : entries)
		{
		  rtx_insn *rwd = e2k_hoist_rwd (en);
		  rtx_insn *c = (rwd ? emit_insn_before (copy_rtx (set), rwd)
				 : NULL);
		  if (c)
		    INSN_LOCATION (c) = INSN_LOCATION (insn);
		  else
		    insert_insn_on_edge (copy_rtx (set), en);
		}
	      if (dump_file)
		fprintf (dump_file, ";; e2k_hoist_invariants: insn %d out of "
			 "loop %d (header bb %d)\n", INSN_UID (insn), loop->num,
			 loop->header->index);
	      delete_insn (insn);
	      n++;
	    }
	}
      free (bbs);
    }
  loop_optimizer_finalize ();
  free_dominance_info (CDI_DOMINATORS);
  if (n)
    {
      commit_edge_insertions ();
      df_analyze ();
    }
}

/* Which of BODY, the operations e2k_rotate_headers would move into
   latch B before its jump, issue there no later than a cycle after the
   jump would, and have their result within 3 cycles of it (the longest
   chains of true register dependences, as e2k_jump_cycle counts them):
   those cost the latch nothing, and the header then gets their results
   about when it starts.  None when the jump would issue before cycle 6.
   Clears FIT[k] for the others.  */
static void
e2k_rotate_fit (basic_block b, const vec<rtx_insn *> &body, bool *fit)
{
  int ready[FIRST_PSEUDO_REGISTER];
  rtx_insn *def[FIRST_PSEUDO_REGISTER];
  memset (def, 0, sizeof def);
  rtx_insn *jump = JUMP_P (BB_END (b)) ? BB_END (b) : NULL;
  int n = 0, tj = 0;
  auto issue = [&] (rtx_insn *i)
    {
      int t = 0;
      df_ref ref;
      FOR_EACH_INSN_USE (ref, i)
	{
	  unsigned r = DF_REF_REGNO (ref);
	  if (r < FIRST_PSEUDO_REGISTER && def[r])
	    t = MAX (t, ready[r] + insn_latency (def[r], i));
	}
      return t;
    };
  auto record = [&] (rtx_insn *i, int t)
    {
      df_ref ref;
      FOR_EACH_INSN_DEF (ref, i)
	{
	  unsigned r = DF_REF_REGNO (ref);
	  if (r < FIRST_PSEUDO_REGISTER)
	    {
	      def[r] = i;
	      ready[r] = t;
	    }
	}
    };
  rtx_insn *i;
  FOR_BB_INSNS (b, i)
    if (NONDEBUG_INSN_P (i) && i != jump && recog_memoized (i) >= 0)
      {
	int t = issue (i);
	tj = MAX (tj, t);
	record (i, t);
	n++;
      }
  tj = MAX (jump ? MAX (issue (jump), tj) : tj, n / 6);
  if (dump_file)
    fprintf (dump_file, ";; e2k_rotate_fit: latch bb %d jump at %d:", b->index,
	     tj);
  /* A latch whose jump hardly waits has nothing to fill (bzip2's
     mainQSort3: its swap arm's test is ready at cycle 3, and even two
     operations of the header there made bzip2 -9 1% slower).  */
  if (tj < 6)
    for (unsigned k = 0; k < body.length (); k++)
      fit[k] = false;
  for (unsigned k = 0; k < body.length (); k++)
    if (fit[k])
      {
	int t = issue (body[k]);
	int done = t + MAX (insn_default_latency (body[k]), 1);
	if (dump_file)
	  fprintf (dump_file, " %d@%d-%d", INSN_UID (body[k]), t, done);
	if (t > tj + 1 || done > tj + 3)
	  fit[k] = false;
	else
	  record (body[k], t);
      }
  if (dump_file)
    fprintf (dump_file, "\n");
}

/* A loop whose latches test for the exit at their end (GCC's loop
   header copying puts the test there) starts each iteration's header
   only after that test: xz's tree walk (bt4_skip) spent about 7 cycles
   a step in the latch on "delta >= cyclic_size" before the header
   computed the next pair's address from delta.  lcc keeps the test at
   the top, beside the header's work.  Move the header's leading
   operations into the latches, before their jump, and onto the ways
   in: in a latch they run beside its test, speculatively (",sm"; their
   registers dead where the latch leaves the loop).  Those of them that
   nothing before them in the header needs to wait for: operations with
   a speculative form and predicated integer ones (lcc's "adds,sm ...
   ? %pred"), no FP operation under -mno-spec-fp, and no load: one in a
   latch also runs on the way out, for a node the walk never visits
   (with the loads, 7-Zip's GetMatches took 5% more cycles, and xz -6
   was 1% slower than without them).  Not in innermost loops of up to three blocks
   (the pipeliner's keep their shape); latches that end in a plain
   branch, a jump or a fall-through, and one of them in a branch.  */
static void
e2k_rotate_headers (void)
{
  df_analyze ();
  /* insn_latency, in e2k_rotate_fit.  */
  dfa_start ();
  loop_optimizer_init (AVOID_CFG_MODIFICATIONS);
  int n = 0;
  for (auto loop : loops_list (cfun, 0))
    {
      basic_block h = loop->header;
      if ((!loop->inner && loop->num_nodes <= 3)
	  || (h->flags & BB_DISABLE_SCHEDULE))
	continue;
      auto_vec<edge, 4> entries, latches;
      edge e;
      edge_iterator ei;
      bool ok = true, cond = false;
      FOR_EACH_EDGE (e, ei, h->preds)
	{
	  if ((e->flags & EDGE_COMPLEX)
	      || e->src == ENTRY_BLOCK_PTR_FOR_FN (cfun))
	    ok = false;
	  else if (flow_bb_inside_loop_p (loop, e->src))
	    latches.safe_push (e);
	  else
	    entries.safe_push (e);
	}
      if (!ok || latches.is_empty () || entries.is_empty ()
	  || latches.length () > 4 || entries.length () > 2)
	continue;
      /* Nor the while loops the pipeliner may take (e2k_ms_wloop): H, or
	 the block H falls into, looping to H, that block storing nothing
	 and neither calling (zlib's longest_match, also entered by the
	 copies e2k_ms_tail_dup made).  */
      edge hf = find_fallthru_edge (h->succs);
      if (hf && hf->dest != h && single_pred_p (hf->dest)
	  && JUMP_P (BB_END (hf->dest)) && LABEL_P (BB_HEAD (h))
	  && JUMP_LABEL (BB_END (hf->dest)) == BB_HEAD (h))
	{
	  bool pipe = true;
	  rtx_insn *insn;
	  for (basic_block bb : { h, hf->dest })
	    FOR_BB_INSNS (bb, insn)
	      if (NONDEBUG_INSN_P (insn) && !JUMP_P (insn))
		{
		  rtx set = single_set (insn);
		  if (CALL_P (insn) || e2k_asm_insn_p (insn)
		      || volatile_insn_p (PATTERN (insn))
		      || (bb != h && (!set || MEM_P (SET_DEST (set)))))
		    pipe = false;
		}
	  if (pipe)
	    continue;
	}
      for (edge l : latches)
	{
	  basic_block b = l->src;
	  rtx_insn *j = BB_END (b);
	  /* Not a latch that heads a loop inside this one, where the
	     operations would run on each of its iterations (zlib's
	     detect_data_type: a pipelined while loop).  */
	  if (b == h || b->loop_father != loop
	      || (b->flags & BB_DISABLE_SCHEDULE) || CALL_P (j))
	    ok = false;
	  else if (JUMP_P (j))
	    {
	      if (e2k_chain_test (j))
		cond = true;
	      else if (!simplejump_p (j))
		ok = false;
	    }
	  else if (!(l->flags & EDGE_FALLTHRU))
	    ok = false;
	}
      if (!ok || !cond)
	continue;
      /* The header's operations to move: each reads nothing an earlier
	 one that stays writes, and sets nothing such a one reads or
	 sets.  */
      auto_vec<rtx_insn *, 16> body;
      HARD_REG_SET stay_set, stay_used, moved_set;
      CLEAR_HARD_REG_SET (stay_set);
      CLEAR_HARD_REG_SET (stay_used);
      CLEAR_HARD_REG_SET (moved_set);
      rtx_insn *insn;
      FOR_BB_INSNS (h, insn)
	{
	  if (!NONDEBUG_INSN_P (insn) || JUMP_P (insn))
	    continue;
	  if (CALL_P (insn) || e2k_asm_insn_p (insn) || e2k_raw_insn_p (insn)
	      || volatile_insn_p (PATTERN (insn)))
	    break;
	  /* A predicated one too, but a load: it runs under its condition
	     there as it would here.  */
	  rtx pat = PATTERN (insn), set = pat;
	  bool ce = GET_CODE (pat) == COND_EXEC;
	  if (ce)
	    set = COND_EXEC_CODE (pat);
	  bool take = (NONJUMP_INSN_P (insn) && recog_memoized (insn) >= 0
		       && GET_CODE (set) == SET && REG_P (SET_DEST (set))
		       && (ce ? (get_attr_type (insn) == TYPE_ALU
				 || get_attr_type (insn) == TYPE_ALU14
				 || get_attr_type (insn) == TYPE_ALU0134)
			  : e2k_spec_kind (insn) == 1)
		       && !side_effects_p (pat) && !volatile_refs_p (pat)
		       && (e2k_spec_fp || !e2k_fp_class_p (insn))
		       && get_attr_type (insn) != TYPE_LOAD
		       && body.length () < 24);
	  df_ref ref;
	  if (take)
	    FOR_EACH_INSN_USE (ref, insn)
	      if (TEST_HARD_REG_BIT (stay_set, DF_REF_REGNO (ref)))
		take = false;
	  if (take)
	    FOR_EACH_INSN_DEF (ref, insn)
	      if (TEST_HARD_REG_BIT (stay_set, DF_REF_REGNO (ref))
		  || TEST_HARD_REG_BIT (stay_used, DF_REF_REGNO (ref)))
		take = false;
	  if (take)
	    {
	      body.safe_push (insn);
	      FOR_EACH_INSN_DEF (ref, insn)
		SET_HARD_REG_BIT (moved_set, DF_REF_REGNO (ref));
	      continue;
	    }
	  FOR_EACH_INSN_DEF (ref, insn)
	    SET_HARD_REG_BIT (stay_set, DF_REF_REGNO (ref));
	  FOR_EACH_INSN_USE (ref, insn)
	    SET_HARD_REG_BIT (stay_used, DF_REF_REGNO (ref));
	}
      if (body.is_empty ())
	continue;
      /* Only what fits in every latch beside its own work, so that no
	 latch gets longer (bzip2's mainQSort3: its swap arm's test is
	 short, and the header's two dependent loads, which overlapped
	 there with the next element's, waited in the arm).  What reads
	 or writes a register of one that stays stays too.  */
      {
	auto_vec<bool, 24> fit;
	fit.safe_grow (body.length ());
	for (bool &f : fit)
	  f = true;
	for (edge l : latches)
	  e2k_rotate_fit (l->src, body, fit.address ());
	HARD_REG_SET kept_set, kept_used;
	CLEAR_HARD_REG_SET (kept_set);
	CLEAR_HARD_REG_SET (kept_used);
	CLEAR_HARD_REG_SET (moved_set);
	unsigned w = 0;
	for (unsigned k = 0; k < body.length (); k++)
	  {
	    rtx_insn *i = body[k];
	    df_ref ref;
	    bool take = fit[k];
	    FOR_EACH_INSN_USE (ref, i)
	      if (TEST_HARD_REG_BIT (kept_set, DF_REF_REGNO (ref)))
		take = false;
	    FOR_EACH_INSN_DEF (ref, i)
	      if (TEST_HARD_REG_BIT (kept_set, DF_REF_REGNO (ref))
		  || TEST_HARD_REG_BIT (kept_used, DF_REF_REGNO (ref)))
		take = false;
	    if (take)
	      {
		body[w++] = i;
		FOR_EACH_INSN_DEF (ref, i)
		  SET_HARD_REG_BIT (moved_set, DF_REF_REGNO (ref));
		continue;
	      }
	    FOR_EACH_INSN_DEF (ref, i)
	      SET_HARD_REG_BIT (kept_set, DF_REF_REGNO (ref));
	    FOR_EACH_INSN_USE (ref, i)
	      SET_HARD_REG_BIT (kept_used, DF_REF_REGNO (ref));
	  }
	body.truncate (w);
      }
      if (body.is_empty ())
	continue;
      /* In a latch they run on its ways out too: their registers dead
	 there, and none its jump reads.  */
      for (edge l : latches)
	{
	  basic_block b = l->src;
	  FOR_EACH_EDGE (e, ei, b->succs)
	    if (e->dest != h)
	      {
		bitmap live = df_get_live_in (e->dest);
		unsigned r;
		bitmap_iterator bi;
		EXECUTE_IF_SET_IN_BITMAP (live, 0, r, bi)
		  if (r < FIRST_PSEUDO_REGISTER
		      && TEST_HARD_REG_BIT (moved_set, r))
		    ok = false;
	      }
	  rtx_insn *j = BB_END (b);
	  if (JUMP_P (j))
	    for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
	      if (TEST_HARD_REG_BIT (moved_set, r)
		  && refers_to_regno_p (r, PATTERN (j)))
		ok = false;
	}
      if (!ok)
	continue;
      for (edge l : latches)
	{
	  basic_block b = l->src;
	  rtx_insn *j = BB_END (b);
	  for (rtx_insn *i : body)
	    {
	      rtx_insn *x = (JUMP_P (j)
			     ? emit_insn_before (copy_rtx (PATTERN (i)), j)
			     : emit_insn_after (copy_rtx (PATTERN (i)),
						BB_END (b)));
	      INSN_LOCATION (x) = INSN_LOCATION (i);
	      e2k_ms_set_flag (x, e2k_ms_flag (i) | E2K_MS_SM);
	    }
	}
      for (edge en : entries)
	{
	  start_sequence ();
	  for (rtx_insn *i : body)
	    {
	      rtx_insn *x = emit_insn (copy_rtx (PATTERN (i)));
	      INSN_LOCATION (x) = INSN_LOCATION (i);
	      e2k_ms_set_flag (x, e2k_ms_flag (i));
	    }
	  insert_insn_on_edge (end_sequence (), en);
	}
      if (dump_file)
	fprintf (dump_file, ";; e2k_rotate_headers: %d operations of header "
		 "bb %d into %d latches, %d ways in\n", body.length (),
		 h->index, latches.length (), entries.length ());
      for (rtx_insn *i : body)
	delete_insn (i);
      n++;
    }
  loop_optimizer_finalize ();
  free_dominance_info (CDI_DOMINATORS);
  dfa_finish ();
  if (n)
    {
      commit_edge_insertions ();
      df_analyze ();
    }
}

/* Leaf functions return through %ctpr3, prepared once at their entry
   (e2k_expand_prologue), so their epilogue is "ct %ctpr3" alone, and a
   branch to a block that computes the result and returns can return
   itself, "ct %ctpr3 ? p", as lcc does.  A block J of a few register
   operations ending in the return is copied into each block P that
   branches to it, before P's branch.  An operation whose register is
   dead on P's other way runs as it is; one whose register is live there
   runs under P's condition (predicated) or, if it can't, into a free
   register, which then goes to its register under the condition if the
   return needs it; and the branch becomes the conditional return.  A P
   that falls into J and branches to the block after J does the same on
   the reversed condition once J has no other way in, and then falls
   through.  bzip2's mainGtU: twelve early exits each copied the bytes
   they compared to J's registers and branched there, which put J, and
   a taken branch, in the middle of the chain.  Not in the innermost
   loops of up to three blocks the pipeliner may take with their exits;
   after e2k_merge_chains and e2k_ms_tail_dup, which shape them.  */

/* Copy BODY, J's operations, into P before its branch, which goes to J
   (REV false) or to the block after J, J being where P falls (REV
   true), and make the branch a return under the condition of going to
   J.  */
static bool
e2k_cond_return_from (basic_block p, const vec<rtx_insn *> &body, bool rev,
		      HARD_REG_SET *taken)
{
  rtx_insn *jump = BB_END (p);
  rtx c = e2k_chain_test (jump);
  if (!c)
    return false;
  /* What isn't predicated runs speculatively there.  */
  if (!e2k_spec_fp)
    for (rtx_insn *i : body)
      if (e2k_fp_class_p (i))
	return false;
  rtx cond = (rev
	      ? gen_rtx_fmt_ee (reverse_condition (GET_CODE (c)), VOIDmode,
				XEXP (c, 0), const0_rtx)
	      : copy_rtx (c));
  rtx pr = XEXP (c, 0);
  basic_block other = rev ? BRANCH_EDGE (p)->dest : FALLTHRU_EDGE (p)->dest;
  bitmap live_o = df_get_live_in (other);
  bitmap live_x = df_get_live_in (EXIT_BLOCK_PTR_FOR_FN (cfun));
  auto_bitmap busy_live;
  bitmap_ior (busy_live, df_get_live_out (p), live_o);
  HARD_REG_SET busy;
  CLEAR_HARD_REG_SET (busy);
  for (rtx_insn *i : body)
    e2k_note_regs (PATTERN (i), &busy);
  e2k_note_regs (PATTERN (jump), &busy);

  rtx map[FIRST_PSEUDO_REGISTER];
  memset (map, 0, sizeof map);
  /* P copied what J reads to J's registers (the values of a phi): the
     copies read the sources instead, and the copies go if nothing else
     needs them.  */
  auto_vec<rtx_insn *, 4> dead_copies;
  {
    HARD_REG_SET reads;
    CLEAR_HARD_REG_SET (reads);
    for (rtx_insn *i : body)
      e2k_note_regs (SET_SRC (PATTERN (i)), &reads);
    for (rtx_insn *x = PREV_INSN (jump); x && x != PREV_INSN (BB_HEAD (p));
	 x = PREV_INSN (x))
      {
	if (!NONDEBUG_INSN_P (x))
	  continue;
	rtx xs = single_set (x);
	if (!xs || PATTERN (x) != xs || !REG_P (SET_DEST (xs))
	    || !REG_P (SET_SRC (xs)) || REG_NREGS (SET_DEST (xs)) != 1
	    || GET_MODE (SET_DEST (xs)) != GET_MODE (SET_SRC (xs)))
	  break;
	unsigned d = REGNO (SET_DEST (xs));
	rtx src = SET_SRC (xs);
	if (!TEST_HARD_REG_BIT (reads, d) || map[d]
	    || reg_set_between_p (src, x, jump))
	  break;
	map[d] = src;
	if (!bitmap_bit_p (live_o, d) && !reg_overlap_mentioned_p (SET_DEST (xs), pr))
	  dead_copies.safe_push (x);
      }
  }
  auto_vec<unsigned, 4> renamed;
  start_sequence ();
  for (rtx_insn *i : body)
    {
      rtx set = copy_rtx (PATTERN (i));
      subrtx_ptr_iterator::array_type array;
      FOR_EACH_SUBRTX_PTR (iter, array, &SET_SRC (set), NONCONST)
	if (REG_P (**iter) && map[REGNO (**iter)])
	  **iter = gen_rtx_REG (GET_MODE (**iter),
				REGNO (map[REGNO (**iter)]));
      rtx d = SET_DEST (set);
      unsigned dr = REGNO (d);
      map[dr] = NULL_RTX;
      bool live = reg_overlap_mentioned_p (d, pr);
      for (unsigned r = dr; r < END_REGNO (d); r++)
	live |= bitmap_bit_p (live_o, r);
      /* Everything into a register of its own if there is one (below):
	 the same register in every exit would tie the exits together.
	 Otherwise a register dead on the other way as it is, or a live
	 one under the condition.  */
      bool fresh = false;
      for (unsigned t = 0; t < FIRST_PSEUDO_REGISTER && !fresh; t++)
	fresh = (PRED_REGNO_P (t) == PRED_REGNO_P (dr) && REG_NREGS (d) == 1
		 && !TEST_HARD_REG_BIT (*taken, t)
		 && e2k_rename_free_p (t, GET_MODE (d), busy_live, busy));
      if (!live && !fresh)
	{
	  emit_insn (set);
	  continue;
	}
      if (live && !fresh && !reg_overlap_mentioned_p (d, pr))
	{
	  rtx ce = gen_rtx_COND_EXEC (VOIDmode, copy_rtx (cond),
				      copy_rtx (set));
	  if (recog_memoized (make_insn_raw (ce)) >= 0)
	    {
	      emit_insn (copy_rtx (ce));
	      continue;
	    }
	}
      /* One the other exits haven't taken if there is one: theirs would
	 tie them together (an exit's result is read after the next one's
	 is computed).  */
      unsigned t = FIRST_PSEUDO_REGISTER;
      for (int pass = 0; pass < 2 && t == FIRST_PSEUDO_REGISTER; pass++)
	for (t = 0; t < FIRST_PSEUDO_REGISTER; t++)
	  if (PRED_REGNO_P (t) == PRED_REGNO_P (dr)
	      && REG_NREGS (d) == 1
	      && (pass || !TEST_HARD_REG_BIT (*taken, t))
	      && e2k_rename_free_p (t, GET_MODE (d), busy_live, busy))
	    break;
      if (t == FIRST_PSEUDO_REGISTER)
	{
	  end_sequence ();
	  return false;
	}
      SET_HARD_REG_BIT (busy, t);
      SET_HARD_REG_BIT (*taken, t);
      map[dr] = gen_rtx_REG (GET_MODE (d), t);
      SET_DEST (set) = map[dr];
      emit_insn (set);
      if (bitmap_bit_p (live_x, dr))
	renamed.safe_push (dr);
    }
  for (unsigned dr : renamed)
    if (map[dr])
      emit_insn (gen_rtx_COND_EXEC (VOIDmode, copy_rtx (cond),
				    gen_rtx_SET (gen_rtx_REG
						 (GET_MODE (map[dr]), dr),
						 map[dr])));
  rtx_insn *seq = end_sequence ();
  for (rtx_insn *x = seq; x; x = NEXT_INSN (x))
    if (recog_memoized (x) < 0)
      return false;
  rtx ret = gen_rtx_SET (pc_rtx, gen_rtx_IF_THEN_ELSE (VOIDmode, cond,
						       ret_rtx, pc_rtx));
  rtx old_label = JUMP_LABEL (jump);
  if (!validate_change (jump, &PATTERN (jump), ret, 0))
    return false;
  /* What runs without the condition now also runs where the program
     returned earlier or went on, on values that may be diagnostic
     there (gcc.c-torture 20180226-1: a compare of a load through a
     null pointer that an earlier test guarded): speculative.  */
  for (rtx_insn *x = seq; x; x = NEXT_INSN (x))
    if (GET_CODE (PATTERN (x)) != COND_EXEC)
      e2k_ms_set_flag (x, E2K_MS_SM);
  emit_insn_before (seq, jump);
  for (rtx_insn *x : dead_copies)
    delete_insn (x);
  JUMP_LABEL (jump) = ret_rtx;
  if (old_label && LABEL_P (old_label))
    LABEL_NUSES (old_label)--;
  df_insn_rescan (jump);
  return true;
}

/* EPILOGUE_USES: a function that prepares its return at its entry keeps
   %ctpr3 to its end; its conditional returns use it too.  */
bool
e2k_epilogue_uses (unsigned regno)
{
  return (regno == CTPR3_REGNUM && reload_completed && cfun && cfun->machine
	  && cfun->machine->early_ret);
}

static void
e2k_cond_returns (void)
{
  machine_function *m = cfun->machine;
  if (!m->early_ret || m->sret_mem)
    return;
  /* %ctpr3 live to the end (EPILOGUE_USES), so that the conditional
     returns depend on its prepare.  */
  df_update_exit_block_uses ();
  df_analyze ();
  /* Innermost loops of up to three blocks keep their exits, for the
     pipeliner (after e2k_merge_chains and e2k_ms_tail_dup, which make
     zlib's longest_match a two-block while loop).  Found before anything
     changes, and the loops let go (the edits below would leave their
     dominators stale).  */
  auto_bitmap small;
  loop_optimizer_init (AVOID_CFG_MODIFICATIONS);
  {
    basic_block b;
    FOR_EACH_BB_FN (b, cfun)
      {
	class loop *l = b->loop_father;
	if (l && l != current_loops->tree_root && !l->inner
	    && l->num_nodes <= 3)
	  bitmap_set_bit (small, b->index);
      }
  }
  loop_optimizer_finalize ();
  free_dominance_info (CDI_DOMINATORS);
  auto pipelinable = [&] (basic_block b)
    {
      return bitmap_bit_p (small, b->index);
    };
  bool changed = false;
  basic_block j, jn;
  HARD_REG_SET taken;
  CLEAR_HARD_REG_SET (taken);
  /* The operations of block B but its last jump, if they qualify, to
     BODY.  */
  auto ops = [] (basic_block b, vec<rtx_insn *> *body)
    {
      rtx_insn *insn;
      FOR_BB_INSNS (b, insn)
	if (NONDEBUG_INSN_P (insn) && !(JUMP_P (insn) && insn == BB_END (b))
	    /* The epilogue's use of the return value.  */
	    && GET_CODE (PATTERN (insn)) != USE)
	  {
	    rtx set = single_set (insn);
	    if (!NONJUMP_INSN_P (insn) || !set || PATTERN (insn) != set
		|| !REG_P (SET_DEST (set)) || body->length () == 4
		|| side_effects_p (SET_SRC (set))
		|| may_trap_or_fault_p (SET_SRC (set))
		|| recog_memoized (insn) < 0)
	      return false;
	    body->safe_push (insn);
	  }
      return true;
    };
  /* Make the ways into J that branch to it, or fall into it from a
     block branching past it, returns, BODY being what J and the return
     block after it do.  */
  auto convert = [&] (basic_block j, const vec<rtx_insn *> &body)
    {
      auto_vec<edge, 16> in;
      edge e;
      edge_iterator ei;
      FOR_EACH_EDGE (e, ei, j->preds)
	if (!(e->flags & (EDGE_FALLTHRU | EDGE_COMPLEX))
	    && !pipelinable (e->src))
	  in.safe_push (e);
      for (edge e : in)
	{
	  basic_block p = e->src;
	  if (EDGE_COUNT (p->succs) != 2 || BRANCH_EDGE (p) != e
	      || !e2k_cond_return_from (p, body, false, &taken))
	    continue;
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_cond_returns: bb %d returns for "
		     "bb %d\n", p->index, j->index);
	  profile_probability pb = e->probability;
	  redirect_edge_succ (e, EXIT_BLOCK_PTR_FOR_FN (cfun));
	  e->probability = pb;
	  changed = true;
	}
      if (single_pred_p (j) && (single_pred_edge (j)->flags & EDGE_FALLTHRU)
	  && !pipelinable (single_pred (j)))
	{
	  basic_block p = single_pred (j);
	  basic_block after = j;
	  /* Past the return block J falls into.  */
	  if (!JUMP_P (BB_END (j)))
	    after = single_succ (j);
	  after = after->next_bb;
	  if (after != EXIT_BLOCK_PTR_FOR_FN (cfun)
	      && EDGE_COUNT (p->succs) == 2 && BRANCH_EDGE (p)->dest == after
	      && (after == j->next_bb
		  || (j->next_bb == single_succ (j)
		      && single_pred_p (single_succ (j))))
	      && e2k_cond_return_from (p, body, true, &taken))
	    {
	      if (dump_file)
		fprintf (dump_file, ";; e2k_cond_returns: bb %d returns for "
			 "bb %d, falling through\n", p->index, j->index);
	      edge f = FALLTHRU_EDGE (p), b = BRANCH_EDGE (p);
	      profile_probability pf = f->probability;
	      redirect_edge_succ (f, EXIT_BLOCK_PTR_FOR_FN (cfun));
	      f->flags &= ~EDGE_FALLTHRU;
	      f->probability = pf;
	      b->flags |= EDGE_FALLTHRU;
	      /* The return is taken the way the fall-through went.  */
	      if (rtx note = find_reg_note (BB_END (p), REG_BR_PROB, NULL_RTX))
		XINT (note, 0) = pf.to_reg_br_prob_note ();
	      changed = true;
	    }
	}
    };
  FOR_EACH_BB_FN (j, cfun)
    {
      rtx_insn *r = BB_END (j);
      if (!JUMP_P (r) || recog_memoized (r) != CODE_FOR_e2k_return)
	continue;
      auto_vec<rtx_insn *, 4> body;
      if (!ops (j, &body))
	continue;
      /* A block that falls into the return block and only computes:
	 its operations, then the return block's.  */
      edge e;
      edge_iterator ei;
      auto_vec<basic_block, 4> feeders;
      FOR_EACH_EDGE (e, ei, j->preds)
	if ((e->flags & EDGE_FALLTHRU) && single_succ_p (e->src)
	    && !JUMP_P (BB_END (e->src)) && e->src != ENTRY_BLOCK_PTR_FOR_FN (cfun))
	  feeders.safe_push (e->src);
      for (basic_block f : feeders)
	{
	  auto_vec<rtx_insn *, 4> fbody;
	  if (!ops (f, &fbody))
	    continue;
	  for (rtx_insn *i : body)
	    fbody.safe_push (i);
	  if (fbody.length () <= 4)
	    convert (f, fbody);
	}
      convert (j, body);
    }
  /* Blocks no way leads to any more, and labels nothing uses any more,
     which would end sched-ebb's superblocks there.  */
  for (j = ENTRY_BLOCK_PTR_FOR_FN (cfun)->next_bb;
       j != EXIT_BLOCK_PTR_FOR_FN (cfun); j = jn)
    {
      jn = j->next_bb;
      if (EDGE_COUNT (j->preds) == 0)
	delete_basic_block (j);
      else if (changed && LABEL_P (BB_HEAD (j)) && LABEL_NUSES (BB_HEAD (j)) == 0
	       && !LABEL_PRESERVE_P (BB_HEAD (j)) && !LABEL_NAME (BB_HEAD (j))
	       && single_pred_p (j)
	       && (single_pred_edge (j)->flags & EDGE_FALLTHRU))
	delete_insn (BB_HEAD (j));
    }
  if (changed)
    df_analyze ();
}

static void
e2k_reorg (void)
{
  compute_bb_for_insn ();
  e2k_bundling = false;
  e2k_ms_flags.truncate (0);
  e2k_unpred_cond.truncate (0);
  e2k_ms_clocks.truncate (0);
  e2k_ms_twin.truncate (0);
  e2k_ms_kernels.truncate (0);
  e2k_ms_kernel_rings.truncate (0);

  /* SMS marks the loops it pipelined so that sched2 keeps its order;
     here the scheduler also forms the wide instructions, so every
     block goes through it (but the kernels of e2k_modsched).  */
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    bb->flags &= ~BB_DISABLE_SCHEDULE;

  if (optimize)
    {
      if (e2k_loop_iters)
	e2k_loop_iters->empty ();
      reorg_loops (false, &e2k_doloop_hooks);
      commit_edge_insertions ();
    }

  if (optimize >= 2 && e2k_merge_chains_p && e2k_control_spec)
    e2k_merge_chains ();
  if (optimize && flag_schedule_insns_after_reload && e2k_bundle
      && e2k_pipeline && e2k_pipeline_while)
    {
      e2k_ms_fold_latches ();
      e2k_ms_tail_dup ();
    }
  if (optimize >= 2 && e2k_control_spec && e2k_cond_latches_p)
    e2k_cond_latches ();
  if (optimize >= 2 && e2k_control_spec && e2k_tail_dup_joins_p)
    e2k_tail_dup_joins ();
  if (optimize >= 2 && e2k_hoist_inv_p)
    e2k_hoist_invariants ();
  if (optimize >= 2 && e2k_control_spec && e2k_rotate_headers_p)
    e2k_rotate_headers ();
  if (optimize >= 2 && e2k_cond_returns_p)
    e2k_cond_returns ();
  if (optimize && e2k_loop_ct)
    e2k_prepare_loop_branches ();
  if (optimize && e2k_prepare_br)
    e2k_prepare_branches (false);
  if (optimize && e2k_control_spec && e2k_spec_rename_p)
    e2k_spec_rename ();

  if (optimize && flag_schedule_insns_after_reload && e2k_bundle)
    {
      split_all_insns ();
      if (optimize >= 2 && e2k_control_spec
	  && (e2k_unpred_loads_p || e2k_unpred_arms_p))
	e2k_unpredicate_loads ();
      if (e2k_pipeline)
	e2k_modsched ();
      if (e2k_prepare_br)
	{
	  if (e2k_pipeline)
	    e2k_prepare_branches (true);
	  e2k_share_ctprs ();
	  e2k_lift_prepares ();
	  if (e2k_hoist_prep_p)
	    e2k_hoist_prepares ();
	}
      e2k_sched_init_global (NULL, 0, 0);
      if (e2k_control_spec)
	e2k_spec_prepare ();
      timevar_push (TV_SCHED2);
      schedule_ebbs ();
      timevar_pop (TV_SCHED2);
      if (e2k_control_spec)
	e2k_spec_mark ();
      if (e2k_control_spec && e2k_spec_prune_p)
	e2k_spec_prune ();
      /* The kernels keep the clocks of their modulo schedule.  */
      for (e2k_ms_clock &c : e2k_ms_clocks)
	{
	  unsigned uid = INSN_UID (c.insn);
	  if (uid >= e2k_insn_clock.length ())
	    e2k_insn_clock.safe_grow_cleared (uid + 1);
	  e2k_insn_clock[uid] = c.clock;
	}
      e2k_gen_bundles ();
      e2k_bundling = true;
    }

  df_analyze ();
  if (flag_var_tracking)
    {
      timevar_push (TV_VAR_TRACKING);
      variable_tracking_main ();
      timevar_pop (TV_VAR_TRACKING);
    }
  df_finish_pass (false);
  e2k_unpred_cond.truncate (0);
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

static void e2k_init_fp_state_builtins (void);

static void
e2k_init_builtins (void)
{
  tree f80 = make_node (REAL_TYPE);
  TYPE_PRECISION (f80) = 80;
  layout_type (f80);
  SET_TYPE_MODE (f80, XFmode);
  lang_hooks.types.register_builtin_type (f80, "__float80");
  /* As on x86: for C++, __float128 is a type distinct from _Float128 that
     mangles as "g".  */
  if (float128t_type_node == NULL_TREE)
    {
      float128t_type_node = make_node (REAL_TYPE);
      TYPE_PRECISION (float128t_type_node)
	= TYPE_PRECISION (float128_type_node);
      SET_TYPE_MODE (float128t_type_node, TYPE_MODE (float128_type_node));
      layout_type (float128t_type_node);
    }
  lang_hooks.types.register_builtin_type (float128t_type_node, "__float128");
  e2k_init_fp_state_builtins ();
}

/* Nonlocal goto and __builtin_setjmp/__builtin_longjmp.  A frame is
   reentered through the chain stack, which only the kernel can unwind, so
   use glibc: the function that receives a nonlocal goto keeps a jmp_buf
   (80 bytes) in its frame and calls _setjmp on it wherever GCC saves the
   stack level (at entry, after alloca, at __builtin_setjmp); the save
   area holds the jmp_buf's address.  A nonlocal goto writes the target
   label into the jmp_buf's return IP (offset 8, the saved %cr0.hi; see
   glibc's setjmp_tmpl.S) and calls longjmp, so the kernel's e2k_longjmp2
   returns into the frame at the label rather than after the _setjmp
   call.  The registers are those of the frame's latest call, as after
   any return.  */

#define E2K_JMPBUF_SIZE 80
#define E2K_JMPBUF_IP 8

static GTY(()) rtx e2k_setjmp_libfunc;
static GTY(()) rtx e2k_longjmp_libfunc;

void
e2k_expand_save_stack_nonlocal (rtx save_area)
{
  if (!cfun->machine->nonlocal_jmpbuf)
    cfun->machine->nonlocal_jmpbuf
      = assign_stack_local (BLKmode, E2K_JMPBUF_SIZE, BITS_PER_WORD);
  if (!e2k_setjmp_libfunc)
    e2k_setjmp_libfunc = init_one_libfunc ("_setjmp");
  rtx addr = force_reg (Pmode, XEXP (cfun->machine->nonlocal_jmpbuf, 0));
  emit_move_insn (save_area, addr);
  emit_library_call (e2k_setjmp_libfunc, LCT_NORMAL, VOIDmode, addr, Pmode);
}

void
e2k_expand_nonlocal_goto (rtx label, rtx save_area)
{
  if (!e2k_longjmp_libfunc)
    e2k_longjmp_libfunc = init_one_libfunc ("longjmp");
  rtx lab = force_reg (Pmode, label);
  rtx jb = force_reg (Pmode, save_area);
  emit_move_insn (gen_rtx_MEM (Pmode, plus_constant (Pmode, jb,
						     E2K_JMPBUF_IP)), lab);
  emit_library_call (e2k_longjmp_libfunc, LCT_NORETURN, VOIDmode,
		     jb, Pmode, const1_rtx, SImode);
  emit_barrier ();
}

/* Builtins that read and write the FP control and status registers, for
   e2k_atomic_assign_expand_fenv.  They are not documented for users.  */
enum e2k_builtin
{
  E2K_BUILTIN_RRS_PFPFR,
  E2K_BUILTIN_RRS_FPCR,
  E2K_BUILTIN_RRS_FPSR,
  E2K_BUILTIN_RWS_PFPFR,
  E2K_BUILTIN_RWS_FPCR,
  E2K_BUILTIN_RWS_FPSR,
  E2K_BUILTIN_MAX
};

static GTY(()) tree e2k_builtins[E2K_BUILTIN_MAX];

static void
e2k_init_fp_state_builtins (void)
{
  static const char *const names[E2K_BUILTIN_MAX] = {
    "__builtin_e2k_rrs_pfpfr", "__builtin_e2k_rrs_fpcr",
    "__builtin_e2k_rrs_fpsr", "__builtin_e2k_rws_pfpfr",
    "__builtin_e2k_rws_fpcr", "__builtin_e2k_rws_fpsr"
  };
  tree get = build_function_type_list (unsigned_type_node, NULL_TREE);
  tree set = build_function_type_list (void_type_node, unsigned_type_node,
				       NULL_TREE);
  for (int i = 0; i < E2K_BUILTIN_MAX; i++)
    e2k_builtins[i]
      = add_builtin_function (names[i], i < E2K_BUILTIN_RWS_PFPFR ? get : set,
			      i, BUILT_IN_MD, NULL, NULL_TREE);
}

static tree
e2k_builtin_decl (unsigned code, bool)
{
  return code < E2K_BUILTIN_MAX ? e2k_builtins[code] : error_mark_node;
}

static rtx
e2k_expand_builtin (tree exp, rtx target, rtx, machine_mode, int)
{
  tree fndecl = TREE_OPERAND (CALL_EXPR_FN (exp), 0);
  unsigned code = DECL_MD_FUNCTION_CODE (fndecl);
  if (code < E2K_BUILTIN_RWS_PFPFR)
    {
      if (!target || !register_operand (target, SImode))
	target = gen_reg_rtx (SImode);
      emit_insn (gen_e2k_rrs (target, GEN_INT (code)));
      return target;
    }
  rtx val = force_reg (SImode,
		       gen_lowpart (SImode,
				    expand_normal (CALL_EXPR_ARG (exp, 0))));
  emit_insn (gen_e2k_rws (GEN_INT (code - E2K_BUILTIN_RWS_PFPFR), val));
  return const0_rtx;
}

/* Atomic compound assignment of a floating type: like glibc's feholdexcept,
   feclearexcept and feupdateenv (sysdeps/e2k/fpu), which keep float and
   double flags in %pfpfr and 80-bit ones in %fpsr, with the same FE_*
   bits.  The masks in %pfpfr are the flag bits shifted left by 7; those
   in %fpcr are the flag bits.  */
static void
e2k_atomic_assign_expand_fenv (tree *hold, tree *clear, tree *update)
{
  const unsigned HOST_WIDE_INT fe_all = 0x3d;
  tree uns = unsigned_type_node;
  tree get_pfpfr = e2k_builtins[E2K_BUILTIN_RRS_PFPFR];
  tree get_fpcr = e2k_builtins[E2K_BUILTIN_RRS_FPCR];
  tree get_fpsr = e2k_builtins[E2K_BUILTIN_RRS_FPSR];
  tree set_pfpfr = e2k_builtins[E2K_BUILTIN_RWS_PFPFR];
  tree set_fpcr = e2k_builtins[E2K_BUILTIN_RWS_FPCR];
  tree set_fpsr = e2k_builtins[E2K_BUILTIN_RWS_FPSR];

  tree pfpfr = create_tmp_var_raw (uns);
  tree fpcr = create_tmp_var_raw (uns);
  tree fpsr = create_tmp_var_raw (uns);
  tree held_pfpfr = create_tmp_var_raw (uns);
  tree held_fpsr = create_tmp_var_raw (uns);

  /* hold: save the three registers, then mask every exception and clear
     the flags.  */
  tree ld_pfpfr = build4 (TARGET_EXPR, uns, pfpfr,
			  build_call_expr (get_pfpfr, 0), NULL_TREE,
			  NULL_TREE);
  tree ld_fpcr = build4 (TARGET_EXPR, uns, fpcr,
			 build_call_expr (get_fpcr, 0), NULL_TREE, NULL_TREE);
  tree ld_fpsr = build4 (TARGET_EXPR, uns, fpsr,
			 build_call_expr (get_fpsr, 0), NULL_TREE, NULL_TREE);
  tree v_pfpfr
    = build2 (BIT_IOR_EXPR, uns,
	      build2 (BIT_AND_EXPR, uns, pfpfr,
		      build_int_cst (uns, ~fe_all)),
	      build_int_cst (uns, fe_all << 7));
  tree v_fpsr = build2 (BIT_AND_EXPR, uns, fpsr,
			build_int_cst (uns, ~fe_all));
  tree mk_held_pfpfr = build4 (TARGET_EXPR, uns, held_pfpfr, v_pfpfr,
			       NULL_TREE, NULL_TREE);
  tree mk_held_fpsr = build4 (TARGET_EXPR, uns, held_fpsr, v_fpsr,
			      NULL_TREE, NULL_TREE);
  tree v_fpcr = build2 (BIT_IOR_EXPR, uns, fpcr, build_int_cst (uns, fe_all));
  *hold = build2 (COMPOUND_EXPR, void_type_node,
		  build2 (COMPOUND_EXPR, void_type_node, ld_pfpfr, ld_fpcr),
		  ld_fpsr);
  *hold = build2 (COMPOUND_EXPR, void_type_node, *hold,
		  build2 (COMPOUND_EXPR, void_type_node, mk_held_pfpfr,
			  mk_held_fpsr));
  *hold = build2 (COMPOUND_EXPR, void_type_node, *hold,
		  build_call_expr (set_pfpfr, 1, held_pfpfr));
  *hold = build2 (COMPOUND_EXPR, void_type_node, *hold,
		  build_call_expr (set_fpcr, 1, v_fpcr));
  *hold = build2 (COMPOUND_EXPR, void_type_node, *hold,
		  build_call_expr (set_fpsr, 1, held_fpsr));

  /* clear: clear the flags again.  */
  *clear = build2 (COMPOUND_EXPR, void_type_node,
		   build_call_expr (set_pfpfr, 1, held_pfpfr),
		   build_call_expr (set_fpsr, 1, held_fpsr));

  /* update: collect the new flags, restore the environment and raise
     them.  */
  tree exc = create_tmp_var_raw (uns);
  tree v_exc = build2 (BIT_AND_EXPR, uns,
		       build2 (BIT_IOR_EXPR, uns,
			       build_call_expr (get_pfpfr, 0),
			       build_call_expr (get_fpsr, 0)),
		       build_int_cst (uns, fe_all));
  tree mk_exc = build4 (TARGET_EXPR, uns, exc, v_exc, NULL_TREE, NULL_TREE);
  tree raise = builtin_decl_implicit (BUILT_IN_ATOMIC_FERAISEEXCEPT);
  *update = build2 (COMPOUND_EXPR, void_type_node, mk_exc,
		    build_call_expr (set_pfpfr, 1, pfpfr));
  *update = build2 (COMPOUND_EXPR, void_type_node, *update,
		    build_call_expr (set_fpcr, 1, fpcr));
  *update = build2 (COMPOUND_EXPR, void_type_node, *update,
		    build_call_expr (set_fpsr, 1, fpsr));
  *update = build2 (COMPOUND_EXPR, void_type_node, *update,
		    build_call_expr (raise, 1, fold_convert (integer_type_node,
							     exc)));
}

/* ------------------------------------------------------------------ */
/* 64-bit vectors (e2k-vect.md)                                        */
/* ------------------------------------------------------------------ */

/* The vector modes live in the integer registers, 8 bytes like
   DImode.  */
static bool
e2k_vector_mode_supported_p (machine_mode mode)
{
  return (mode == V8QImode || mode == V4HImode || mode == V2SImode
	  || mode == V2SFmode);
}

/* What the vectorizer works in.  Packed integer operations issue in two
   channels (four for shifts and shuffles) where scalar ones take six, so
   the gain is in the lanes and in memory: 8 bytes to an ldd and an std,
   whose channels (4 loads, 2 stores) bound most loops.  */
static machine_mode
e2k_preferred_simd_mode (scalar_mode mode)
{
  switch (mode)
    {
    case E_QImode:
      return V8QImode;
    case E_HImode:
      return V4HImode;
    case E_SImode:
      return V2SImode;
    case E_SFmode:
      return V2SFmode;
    default:
      return word_mode;
    }
}

/* DEST = (A CODE B), lanes all ones where true: the hardware compares
   equal and signed greater; the rest by swapping, inverting, or (for
   unsigned) through max.  */
void
e2k_expand_vec_cmp (rtx dest, enum rtx_code code, rtx a, rtx b)
{
  machine_mode mode = GET_MODE (dest);
  bool inv = false;
  rtx x;
  switch (code)
    {
    case EQ: x = gen_rtx_EQ (mode, a, b); break;
    case NE: x = gen_rtx_EQ (mode, a, b); inv = true; break;
    case GT: x = gen_rtx_GT (mode, a, b); break;
    case LT: x = gen_rtx_GT (mode, b, a); break;
    case GE: x = gen_rtx_GT (mode, b, a); inv = true; break;
    case LE: x = gen_rtx_GT (mode, a, b); inv = true; break;
    case GEU: case LTU: case LEU: case GTU:
      {
	/* a >=u b iff umax (a, b) == a.  */
	rtx m = gen_reg_rtx (mode);
	emit_insn (gen_rtx_SET (m, gen_rtx_UMAX (mode, a, b)));
	bool ge = code == GEU || code == LTU;
	x = gen_rtx_EQ (mode, m, ge ? a : b);
	inv = code == LTU || code == GTU;
	break;
      }
    default:
      gcc_unreachable ();
    }
  if (!inv)
    {
      emit_insn (gen_rtx_SET (dest, x));
      return;
    }
  rtx t = gen_reg_rtx (mode);
  emit_insn (gen_rtx_SET (t, x));
  emit_insn (gen_rtx_SET (dest, gen_rtx_NOT (mode, t)));
}

/* TARGET = pshufb taking result byte i from byte SEL[i] of OP1:OP0 (OP0
   the low 8 bytes), or zero for SEL[i] 0x80.  */
static void
e2k_emit_pshufb (rtx target, rtx op0, rtx op1, const unsigned char *sel)
{
  machine_mode mode = GET_MODE (target);
  unsigned HOST_WIDE_INT c = 0;
  for (int i = 7; i >= 0; i--)
    /* Bit 3 picks pshufb's first operand, OP1.  */
    c = (c << 8) | sel[i];
  rtx m = force_reg (DImode, gen_int_mode (c, DImode));
  rtx pat = gen_rtx_UNSPEC (mode, gen_rtvec (3, op1, op0, m), UNSPEC_PSHUFB);
  emit_insn (gen_rtx_SET (target, pat));
}

static bool
e2k_vectorize_vec_perm_const (machine_mode vmode, machine_mode op_mode,
			      rtx target, rtx op0, rtx op1,
			      const vec_perm_indices &sel)
{
  if (vmode != op_mode || !e2k_vector_mode_supported_p (vmode))
    return false;
  if (!target)
    return true;
  int nelt = GET_MODE_NUNITS (vmode);
  int esize = 8 / nelt;
  unsigned char bytes[8];
  for (int i = 0; i < nelt; i++)
    {
      int e = sel[i].to_constant () % (2 * nelt);
      for (int k = 0; k < esize; k++)
	bytes[i * esize + k] = e * esize + k;
    }
  e2k_emit_pshufb (target, force_reg (vmode, op0), force_reg (vmode, op1),
		   bytes);
  return true;
}

/* TARGET = X in every lane: a pshufb of the low lane.  */
void
e2k_expand_vec_duplicate (rtx target, rtx x)
{
  machine_mode mode = GET_MODE (target);
  machine_mode emode = GET_MODE_INNER (mode);
  int esize = GET_MODE_SIZE (emode);
  if (FLOAT_MODE_P (emode))
    {
      rtx t = gen_reg_rtx (SImode);
      emit_move_insn (t, gen_lowpart (SImode, force_reg (emode, x)));
      x = t;
    }
  /* The value's bits in the low lane; the rest don't matter.  */
  rtx v = gen_reg_rtx (DImode);
  emit_move_insn (v, convert_to_mode (DImode, x, 1));
  unsigned char bytes[8];
  for (int i = 0; i < 8; i++)
    bytes[i] = i % esize;
  rtx vv = gen_lowpart (mode, v);
  e2k_emit_pshufb (target, vv, vv, bytes);
}

/* TARGET = the lanes of PARALLEL VALS.  */
void
e2k_expand_vec_init (rtx target, rtx vals)
{
  machine_mode mode = GET_MODE (target);
  int nelt = GET_MODE_NUNITS (mode);
  int bits = 64 / nelt;
  bool all_const = true;
  for (int i = 0; i < nelt; i++)
    if (!CONSTANT_P (XVECEXP (vals, 0, i)))
      all_const = false;
  if (all_const)
    {
      emit_move_insn (target, gen_rtx_CONST_VECTOR (mode, XVEC (vals, 0)));
      return;
    }
  machine_mode emode = GET_MODE_INNER (mode);
  scalar_int_mode imode = int_mode_for_mode (emode).require ();
  rtx acc = NULL_RTX;
  for (int i = nelt - 1; i >= 0; i--)
    {
      rtx e = XVECEXP (vals, 0, i);
      if (emode != imode)
	{
	  rtx t = gen_reg_rtx (imode);
	  emit_move_insn (t, gen_lowpart (imode, force_reg (emode, e)));
	  e = t;
	}
      rtx z = force_reg (DImode, convert_to_mode (DImode, e, 1));
      if (acc)
	{
	  rtx s = expand_simple_binop (DImode, ASHIFT, acc, GEN_INT (bits),
				       NULL_RTX, 1, OPTAB_LIB_WIDEN);
	  acc = expand_simple_binop (DImode, IOR, s, z, NULL_RTX, 1,
				     OPTAB_LIB_WIDEN);
	}
      else
	acc = z;
    }
  emit_move_insn (target, gen_lowpart (mode, force_reg (DImode, acc)));
}

/* TARGET = lane N of V.  */
void
e2k_expand_vec_extract (rtx target, rtx v, int n)
{
  machine_mode mode = GET_MODE (v);
  machine_mode emode = GET_MODE_INNER (mode);
  int bits = GET_MODE_BITSIZE (emode);
  rtx d = gen_lowpart (DImode, force_reg (mode, v));
  if (n)
    d = expand_simple_binop (DImode, LSHIFTRT, d, GEN_INT (n * bits),
			     NULL_RTX, 1, OPTAB_LIB_WIDEN);
  d = force_reg (DImode, d);
  if (FLOAT_MODE_P (emode))
    {
      rtx t = gen_reg_rtx (SImode);
      emit_move_insn (t, gen_lowpart (SImode, d));
      emit_move_insn (target, gen_lowpart (emode, t));
    }
  else
    emit_move_insn (target, gen_lowpart (emode, d));
}

/* TARGET = the low (HI false) or high half of V's lanes widened, with
   their signs (SIGNED_P) or zeros: an unpack of V with its sign mask or
   zero.  */
void
e2k_expand_vec_unpack (rtx target, rtx v, bool signed_p, bool hi)
{
  machine_mode mode = GET_MODE (v);
  rtx ext = CONST0_RTX (mode);
  if (signed_p)
    {
      ext = gen_reg_rtx (mode);
      emit_insn (gen_rtx_SET (ext, gen_rtx_GT (mode, CONST0_RTX (mode), v)));
    }
  rtx pat = gen_rtx_UNSPEC (GET_MODE (target), gen_rtvec (2, ext, v),
			    hi ? UNSPEC_PUNPCKH : UNSPEC_PUNPCKL);
  emit_insn (gen_rtx_SET (target, pat));
}

/* TARGET = A's and B's lanes cut to half their width, A's low.  */
void
e2k_expand_vec_pack_trunc (rtx target, rtx a, rtx b)
{
  machine_mode tmode = GET_MODE (target);
  int esize = 8 / GET_MODE_NUNITS (GET_MODE (a));
  int half = esize / 2, per = 8 / esize;
  unsigned char bytes[8];
  for (int i = 0; i < 8; i++)
    {
      int lane = i / half, k = i % half;
      bytes[i] = (lane < per ? 0 : 8) + (lane % per) * esize + k;
    }
  e2k_emit_pshufb (target, gen_lowpart (tmode, a), gen_lowpart (tmode, b),
		   bytes);
}

/* Field operations (getf, insf; spec/isa/semantics.md).  */

/* Whether a field of LEN bits at POS of a MODE value is one getf takes.  */
bool
e2k_getf_field_p (machine_mode mode, rtx len, rtx pos)
{
  if (!CONST_INT_P (len) || !CONST_INT_P (pos))
    return false;
  HOST_WIDE_INT l = INTVAL (len), p = INTVAL (pos);
  return l >= 1 && l <= 63 && p >= 0
	 && p + l <= GET_MODE_BITSIZE (mode);
}

/* getfd OPERANDS[1] of the field (OPERANDS[2] bits at OPERANDS[3]):
   offset, length, sign, and BYTE naming the field's top byte, which v1-v4
   take the sign from.  */
const char *
e2k_output_getf (rtx *operands, bool sign)
{
  static char buf[64];
  HOST_WIDE_INT l = INTVAL (operands[2]), p = INTVAL (operands[3]);
  HOST_WIDE_INT d = p | l << 6;
  if (sign)
    d |= 1 << 12 | (((p + l - 1) & 63) / 8) << 13;
  snprintf (buf, sizeof buf, "getfd\t%%1, %#" PRIx64 ", %%0", (uint64_t) d);
  return buf;
}

/* getfs of a 32-bit field sign-extended in 32 bits (BYTE for the 32-bit
   value), which dbl = 1 zero-extends.  */
const char *
e2k_output_getfs (rtx *operands)
{
  static char buf[64];
  HOST_WIDE_INT l = INTVAL (operands[2]), p = INTVAL (operands[3]);
  HOST_WIDE_INT d = p | l << 6 | 1 << 12 | (((p + l - 1) & 31) / 8) << 13;
  snprintf (buf, sizeof buf, "getfs\t%%1, %#" PRIx64 ", %%0", (uint64_t) d);
  return buf;
}

/* N if C is 2^N - 1 (N 1..63), else 0.  */
int
e2k_lowmask_bits (rtx c)
{
  if (!CONST_INT_P (c))
    return 0;
  unsigned HOST_WIDE_INT v = INTVAL (c);
  if (v == 0 || (v & (v + 1)) != 0 || v == HOST_WIDE_INT_M1U)
    return 0;
  return exact_log2 (v + 1);
}

const char *
e2k_output_lowmask (rtx *operands)
{
  static char buf[64];
  snprintf (buf, sizeof buf, "getfd\t%%1, %#x, %%0",
	    e2k_lowmask_bits (operands[2]) << 6);
  return buf;
}

/* Whether (a << K) | (c & MASK) is one insf in MODE: MASK = 2^K - 1.  */
bool
e2k_insf_mask_p (machine_mode mode, rtx k, rtx mask)
{
  if (!CONST_INT_P (k))
    return false;
  HOST_WIDE_INT n = INTVAL (k);
  return (n >= 1 && n < GET_MODE_BITSIZE (mode)
	  && e2k_lowmask_bits (mask) == n);
}

/* insf of OPERANDS[1] shifted left by OPERANDS[2] and OPERANDS[3]'s low
   bits: rotate right by WIDTH - K, K bits.  insfd's bit 15 as lcc sets
   it (it picks where tags come from; untagged values don't care).  */
const char *
e2k_output_insf (rtx *operands, machine_mode mode)
{
  static char buf[64];
  int w = GET_MODE_BITSIZE (mode);
  HOST_WIDE_INT k = INTVAL (operands[2]);
  HOST_WIDE_INT d = (w - k) | k << 6 | (mode == DImode ? 1 << 15 : 0);
  snprintf (buf, sizeof buf, "insf%c\t%%1, %#" PRIx64 ", %%3, %%0%%?",
	    mode == DImode ? 'd' : 's', (uint64_t) d);
  return buf;
}

/* Whether PAT is one of the field operations above, which take one
   16-bit literal (the descriptor) whatever their operands.  */
static bool
e2k_field_insn_p (rtx pat)
{
  if (GET_CODE (pat) != SET)
    return false;
  rtx s = SET_SRC (pat);
  switch (GET_CODE (s))
    {
    case ZERO_EXTRACT:
    case SIGN_EXTRACT:
      return true;
    case AND:
      return (GET_MODE (s) == DImode && e2k_lowmask_bits (XEXP (s, 1)) > 32);
    case ZERO_EXTEND:
      return e2k_field_insn_p (gen_rtx_SET (SET_DEST (pat), XEXP (s, 0)));
    case IOR:
      return ((GET_CODE (XEXP (s, 0)) == ASHIFT
	       && GET_CODE (XEXP (s, 1)) == ZERO_EXTEND)
	      || (GET_CODE (XEXP (s, 0)) == AND
		  && GET_CODE (XEXP (s, 1)) == ASHIFT
		  && CONST_INT_P (XEXP (XEXP (s, 0), 1))));
    default:
      return false;
    }
}

/* Whether MEM may be accessed byte-swapped through MAS bit 3: not
   volatile, and known aligned to its size (else SIGBUS, where a plain
   access works; e2k_known_aligned_p).  lcc folds bswap only under
   -ffast, and then traps on a misaligned cast too.  */
bool
e2k_bswap_mem_p (rtx mem)
{
  return (MEM_P (mem) && !MEM_VOLATILE_P (mem)
	  && e2k_known_aligned_p (mem, GET_MODE_SIZE (GET_MODE (mem))));
}

/* After reload: DEST = the bytes of SRC (hard registers, SImode or
   DImode) reversed, through pshufb with a mask in SCRATCH (spec/isa/
   semantics.md, "Packed operations of v3"); the upper half 0 for 32
   bits, which reads only SRC's low half.  */
void
e2k_split_bswap (rtx dest, rtx src, rtx scratch)
{
  machine_mode mode = GET_MODE (dest);
  HOST_WIDE_INT mask = (mode == DImode ? HOST_WIDE_INT_C (0x0001020304050607)
			: HOST_WIDE_INT_C (0x8080808000010203));
  emit_move_insn (scratch, gen_int_mode (mask, DImode));
  rtx v = gen_rtx_REG (V8QImode, REGNO (src));
  emit_insn (gen_e2k_pshufbv8qi (gen_rtx_REG (V8QImode, REGNO (dest)), v, v,
				 scratch));
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
  if (TREE_CODE (type) == REAL_TYPE && TYPE_MODE (type) == XFmode)
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

#undef TARGET_LEGITIMATE_ADDRESS_P
#define TARGET_LEGITIMATE_ADDRESS_P e2k_legitimate_address_hook
#undef TARGET_LEGITIMATE_CONSTANT_P
#define TARGET_LEGITIMATE_CONSTANT_P e2k_legitimate_constant_hook
#undef TARGET_CANNOT_FORCE_CONST_MEM
#define TARGET_CANNOT_FORCE_CONST_MEM e2k_cannot_force_const_mem
#undef TARGET_LEGITIMIZE_ADDRESS
#define TARGET_LEGITIMIZE_ADDRESS e2k_legitimize_address

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

#include "gt-e2k.h"
