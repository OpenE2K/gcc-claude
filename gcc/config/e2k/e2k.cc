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
#include "tree-into-ssa.h"
#include "cfgloopmanip.h"

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
  bool dbl_known, dbl;		/* setwd dbl, once decided (e2k_dbl_p) */
  int ring_base;		/* its first pair: below the outgoing ones */
  /* Dependence cliques of loops versioned for aliasing: they hold for
     every iteration (e2k_av_loop).  Not a range: copying a loop gives
     its references new cliques too.  */
  unsigned short av_cliques[8];
  int n_av_cliques;

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
  return ggc_cleared_alloc<machine_function> ();
}

static gimple_opt_pass *make_pass_e2k_alias_version (gcc::context *);
static rtl_opt_pass *make_pass_e2k_dbl_zext (gcc::context *);
static rtl_opt_pass *make_pass_e2k_dbl_widen (gcc::context *);

static void
e2k_option_override (void)
{
  init_machine_status = e2k_init_machine_status;

  static bool passes_done;
  if (!passes_done)
    {
      passes_done = true;
      struct register_pass_info info
	= { make_pass_e2k_alias_version (g), "vect", 1,
	    PASS_POS_INSERT_AFTER };
      register_pass (&info);
      struct register_pass_info zinfo
	= { make_pass_e2k_dbl_zext (g), "ree", 1, PASS_POS_INSERT_AFTER };
      register_pass (&zinfo);
      struct register_pass_info winfo
	= { make_pass_e2k_dbl_widen (g), "combine", 1,
	    PASS_POS_INSERT_AFTER };
      register_pass (&winfo);
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
  bool use_b = false;
  for (rtx_insn *insn = get_insns (); insn; insn = NEXT_INSN (insn))
    {
      if (!INSN_P (insn))
	continue;
      if (CALL_P (insn))
	use_b = true;
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
     so calls keep handing over just the 4 outgoing pairs.  */
  m->ring_base = (maxr + 2) / 2;
  m->wbase = m->ring_base + m->rot_pairs;
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
      return outer != SET;
    case MULT:
      *total = COSTS_N_INSNS (FLOAT_MODE_P (mode) ? 4 : 4);
      return false;
    case DIV:
    case UDIV:
    case MOD:
    case UMOD:
      *total = COSTS_N_INSNS (FLOAT_MODE_P (mode) ? 14 : 11);
      return false;
    case PLUS:
    case MINUS:
      *total = COSTS_N_INSNS (FLOAT_MODE_P (mode) ? 4 : 1);
      return false;
    default:
      return false;
    }
}

static int
e2k_address_cost (rtx, machine_mode, addr_space_t, bool)
{
  return 0;
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
   address apart from a constant less than 8 bytes.  */
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
  return rtx_equal_p (ba, bb) && oa - ob < 8 && ob - oa < 8;
}

static int e2k_spec_kind (rtx_insn *);
static bool e2k_spec_sets_live_p (rtx_insn *, rtx_insn *);

static int
e2k_adjust_cost (rtx_insn *con, int dep_type, rtx_insn *pro, int cost,
		 unsigned int)
{
  /* A taken transfer's whole wide instruction runs, and a call's too
     before the callee does.  So what depends on a call, and what depends
     on a jump because it has no speculative form or sets a register live
     where the jump goes, can't share their instruction.  Rewriting what
     the jump only reads (its predicate) can: the jump reads the old
     value.  e2k_spec_mark makes what does share it speculative.  */
  if ((JUMP_P (pro) || CALL_P (pro)) && INSN_P (con) && cost < 1
      && (CALL_P (pro) || e2k_spec_kind (con) == 0
	  || e2k_spec_sets_live_p (con, pro)))
    return 1;
  /* Operations in the wide instruction with setwd already use the new
     window (spec/abi/registers.md), as lcc's prologues do; %b[] in the
     one with setbn still uses the old rotating base.  setwd is volatile,
     so everything after it depends on it, and on the prologue's
     blockage after it, which only keeps the body below the frame's
     setup (registers carry the rest).  */
  if (INSN_P (pro) && (recog_memoized (pro) == CODE_FOR_e2k_setwd
			|| recog_memoized (pro) == CODE_FOR_blockage)
      && INSN_P (con) && !CALL_P (con) && !JUMP_P (con))
    {
      bool b = false;
      subrtx_iterator::array_type array;
      FOR_EACH_SUBRTX (iter, array, PATTERN (con), NONCONST)
	if (REG_P (*iter) && (B_REGNO_P (REGNO (*iter))
			      || BX_REGNO_P (REGNO (*iter))))
	  b = true;
      return b ? MAX (cost, 1) : 0;
    }
  if (INSN_P (pro) && INSN_P (con)
      && recog_memoized (pro) >= 0 && recog_memoized (con) >= 0)
    {
      enum attr_type pt = get_attr_type (pro), ct = get_attr_type (con);
      /* A conditional ct waits for its disp only 2 cycles when not
	 taken; taken, 5 minus the distance, still less than an ibranch
	 (spec/isa/control-transfer.md, "Costs").  Don't stretch the
	 fall-through path for it (e2k_prepare_branches).  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_DISP && ct == TYPE_CT)
	return MIN (cost, 2);
      /* v1-v5 can't prepare and transfer through one CTPR in one wide
	 instruction.  */
      if (dep_type == REG_DEP_ANTI && ct == TYPE_DISP && cost < 1
	  && (pt == TYPE_CT || pt == TYPE_CALL || pt == TYPE_BRANCH))
	return 1;
      /* A load of a doubleword stored in the wide instruction just before
	 gets its value about 8 cycles late; one cycle between them is
	 enough (spec/isa/timing.md, "Store to load").  Only for the same
	 doubleword: a store and a load that merely may alias keep 1.  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_STORE
	  && (ct == TYPE_LOAD || ct == TYPE_LDLOCK || ct == TYPE_LDCHK)
	  && e2k_same_dword_p (pro, con))
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
  if (uid < e2k_insn_clock.length ())
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

static void
e2k_gen_bundles (void)
{
  e2k_marks.truncate (0);
  e2k_marks.safe_grow_cleared (get_max_uid () + 1);

  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *end = NEXT_INSN (BB_END (bb));
      rtx_insn *prev = NULL;
      int prev_clock = -1;
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
		       || CALL_P (prev) || JUMP_P (prev)
		       || (recog_memoized (insn) >= 0
			   && get_attr_type (insn) == TYPE_MULTI)
		       || (recog_memoized (prev) >= 0
			   && get_attr_type (prev) == TYPE_MULTI));
	  if (open)
	    {
	      if (prev)
		{
		  e2k_marks[INSN_UID (prev)].close = true;
		  if (e2k_nops && clock > 0 && prev_clock > 0
		      && clock > prev_clock + 1 && !JUMP_P (prev)
		      && !CALL_P (prev))
		    e2k_marks[INSN_UID (prev)].nops
		      = MIN (clock - prev_clock - 1, 7);
		}
	      e2k_marks[uid].open = true;
	    }
	  new_cycle = false;
	  prev = insn;
	  if (clock > 0)
	    prev_clock = clock;
	}
      if (prev)
	e2k_marks[INSN_UID (prev)].close = true;
    }
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
	  e2k_marks[lu].post_nops = MIN (gap, 8);
	else
	  e2k_marks[lu].nops = MAX (e2k_marks[lu].nops, MIN (gap, 7));
      }

  /* The jumps into a block are not scheduled with it: if its first wide
     instruction transfers control and also reads a predicate in another
     operation (a merge, a predicated operation), that read doesn't wait
     for a compare in the jump's wide instruction (spec/isa/timing.md).
     Put an empty one before it.  */
  FOR_EACH_BB_FN (bb, cfun)
    {
      edge e;
      edge_iterator ei;
      bool jumped = false;
      FOR_EACH_EDGE (e, ei, bb->preds)
	jumped |= !(e->flags & EDGE_FALLTHRU);
      /* Not in a pipelined loop's kernel: its compensation code jumps
	 back into it from far away.  */
      if (!jumped || (bb->flags & BB_DISABLE_SCHEDULE))
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
    case TYPE_CMP:
      return 0x1b;
    case TYPE_MUL:
    case TYPE_FP:
    case TYPE_FMA:
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
};

struct e2k_chan_use_data
{
  int regs[16];
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

/* The table of e2k_assign_channels.  */
static e2k_chan_prod e2k_chan_tab[FIRST_PSEUDO_REGISTER];

/* Pipelined loops (e2k_modsched): for each prologue insn's UID, its
   node's insn in the kernel (whose channel it takes, so that a value
   an operation passes to its own next instance doesn't cross between
   the clusters on the way into the kernel); and the kernels' blocks
   (the second -1, or the block after a check that splits it).  */
static vec<int> e2k_ms_twin;
static vec<std::pair<int, int> > e2k_ms_kernels;

static void
e2k_chan_note_def (rtx x, const_rtx, void *data)
{
  if (SUBREG_P (x))
    x = SUBREG_REG (x);
  if (!REG_P (x) || !HARD_REGISTER_P (x))
    return;
  for (unsigned r = REGNO (x); r < END_REGNO (x); r++)
    e2k_chan_tab[r] = *(e2k_chan_prod *) data;
}

/* Cycles a consumer in channel C at position POS waits for register R,
   rounded up to the 4-cycle stall steps (spec/isa/timing.md).  */
static int
e2k_chan_stall (const e2k_chan_prod *tab, int r, int c, int pos, bool fp)
{
  const e2k_chan_prod &p = tab[r];
  if (p.kind == E2K_RK_NONE || p.cl < 0)
    return 0;
  bool other = c / 3 != p.cl;
  int lat = p.lat;
  if (p.kind == E2K_RK_FP)
    lat += (other || !fp) ? 2 : 0;
  else if (p.kind == E2K_RK_PACKED)
    lat = (other || !fp) ? MAX (lat, 4) : lat;
  else
    lat += other;
  int e = lat - (pos - p.pos);
  return e > 0 ? 4 * ((e + 3) / 4) : 0;
}

static void
e2k_chan_bundle (rtx_insn **ops, int n, int pos, e2k_chan_prod *tab)
{
  int set[8], fixed[8], cost[8][6], chan[8];
  bool load[8], store[8];
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
      bool fp = (t == TYPE_FP || t == TYPE_FMA || t == TYPE_FCVT
		 || t == TYPE_MUL || t == TYPE_FCMP || t == TYPE_FDIV
		 || e2k_packed_type_p (t));
      e2k_chan_use_data d;
      d.n = 0;
      note_uses (&PATTERN (ops[i]), e2k_chan_note_use, &d);
      for (int c = 0; c < 6; c++)
	{
	  cost[i][c] = 0;
	  if (set[i] & (1 << c))
	    for (int k = 0; k < d.n; k++)
	      cost[i][c] += e2k_chan_stall (tab, d.regs[k], c, pos, fp);
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

  /* Record the results.  */
  for (int i = 0; i < n; i++)
    {
      rtx_insn *insn = ops[i];
      if (CALL_P (insn))
	{
	  for (int r = 0; r < FIRST_PSEUDO_REGISTER; r++)
	    tab[r].kind = E2K_RK_NONE;
	  continue;
	}
      int f, b;
      enum e2k_rkind kind;
      if (e2k_chan_set (insn, &f, &b, &kind) < 0)
	kind = E2K_RK_NONE;
      int cl = ok && chan[i] >= 0 ? chan[i] / 3 : -1;
      int lat = recog_memoized (insn) >= 0 ? insn_default_latency (insn) : 1;
      e2k_chan_prod p = { pos, lat, cl, kind };
      note_stores (insn, e2k_chan_note_def, &p);
    }
}

/* Assign the channels of the wide instructions from FROM to before TO,
   the first at position *POS.  */
static void
e2k_chan_range (rtx_insn *from, rtx_insn *to, int *pos, e2k_chan_prod *tab)
{
  rtx_insn *ops[8];
  int n = 0;
  bool over = false;
  for (rtx_insn *insn = from; insn != to; insn = NEXT_INSN (insn))
    {
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
	  if (!over)
	    e2k_chan_bundle (ops, n, *pos, tab);
	  *pos += 1 + m.nops;
	  n = 0;
	}
    }
}

static void
e2k_assign_channels (void)
{
  e2k_chan_prod *tab = e2k_chan_tab;
  /* Kernels first, in their steady state: twice round, the second time
     with what the first left in the table.  */
  for (std::pair<int, int> &k : e2k_ms_kernels)
    {
      basic_block b1 = BASIC_BLOCK_FOR_FN (cfun, k.first);
      basic_block b2 = k.second >= 0 ? BASIC_BLOCK_FOR_FN (cfun, k.second) : b1;
      if (!b1 || !b2)
	continue;
      rtx_insn *from = BB_HEAD (b1), *to = NEXT_INSN (BB_END (b2));
      for (int r = 0; r < FIRST_PSEUDO_REGISTER; r++)
	tab[r].kind = E2K_RK_NONE;
      int pos = 0;
      for (int round = 0; round < 2; round++)
	{
	  if (round)
	    for (rtx_insn *insn = from; insn != to; insn = NEXT_INSN (insn))
	      e2k_marks[INSN_UID (insn)].chan1 = 0;
	  e2k_chan_range (from, to, &pos, tab);
	}
    }
  for (int r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    tab[r].kind = E2K_RK_NONE;
  int pos = 0;
  e2k_chan_range (get_insns (), NULL, &pos, tab);
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
   function as lcc places them; loops that the profile says run fewer
   than E2K_APB_MIN_TRIP times use it only when it shortens the kernel
   (e2k_ms_pipeline).  */
#define E2K_APB_MIN_TRIP 256
static int e2k_apb_labelno;
static vec<char *> e2k_apb_progs;

/* vlc: the count is valid (spec/isa/loops.md, %lsr bit 37).  */
#define E2K_LSR_VLC (HOST_WIDE_INT_1 << 37)

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
      if (e2k_marks[uid].nops)
	fprintf (f, "\tnop\t%d\n", e2k_marks[uid].nops);
      fputs ("\t}\n", f);
      e2k_in_bundle = false;
      e2k_dam_print_pending (f);
      if (e2k_marks[uid].post_nops)
	fprintf (f, "\t{\n\tnop\t%d\n\t}\n", e2k_marks[uid].post_nops - 1);
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
   CTPRs taken in turn so that it can pass the transfers before.  */
static void
e2k_prepare_branches (void)
{
  df_analyze ();
  basic_block bb;
  int next = 0;
  bool changed = false;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *jump = BB_END (bb);
      if (!JUMP_P (jump) || recog_memoized (jump) < 0
	  || get_attr_type (jump) != TYPE_BRANCH)
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

static bool
e2k_rename_free_p (unsigned r, machine_mode mode, bitmap live,
		   const HARD_REG_SET &busy)
{
  if (fixed_regs[r] || TEST_HARD_REG_BIT (busy, r)
      || bitmap_bit_p (live, r) || !targetm.hard_regno_mode_ok (r, mode))
    return false;
  if (PRED_REGNO_P (r))
    return true;
  /* A global, or a window register the function has anyway.  */
  return G_REGNO_P (r) || (W_REGNO_P (r) && df_regs_ever_live_p (r));
}

static void
e2k_note_regs (rtx x, HARD_REG_SET *set)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, x, NONCONST)
    if (REG_P (*iter) && HARD_REGISTER_P (*iter))
      add_to_hard_reg_set (set, GET_MODE (*iter), REGNO (*iter));
}

static void
e2k_spec_rename (void)
{
  df_analyze ();
  basic_block x;
  bool changed = false;
  FOR_EACH_BB_FN (x, cfun)
    {
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
      HARD_REG_SET jregs, busy;
      CLEAR_HARD_REG_SET (jregs);
      e2k_note_regs (PATTERN (jump), &jregs);
      busy = jregs;
      /* Nor anything X touches: the computation is to move up there.
	 What X reads is in the way too: a value of Y into a register X
	 reads (the same variable in each step of a chain of exits) can't
	 go above the read.  */
      HARD_REG_SET xreads;
      CLEAR_HARD_REG_SET (xreads);
      rtx_insn *insn;
      FOR_BB_INSNS (x, insn)
	if (INSN_P (insn))
	  {
	    e2k_note_regs (PATTERN (insn), &busy);
	    rtx xs = single_set (insn);
	    if (xs)
	      e2k_note_regs (SET_SRC (xs), &xreads);
	  }
      FOR_BB_INSNS (y, insn)
	if (INSN_P (insn))
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
	  bool conflict = (bitmap_bit_p (xlive, dr)
			   || TEST_HARD_REG_BIT (jregs, dr)
			   || TEST_HARD_REG_BIT (xreads, dr));
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
	  if (movable && conflict && !(copy && PRED_REGNO_P (dr)))
	    for (unsigned c = 0; c < FIRST_PSEUDO_REGISTER; c++)
	      if ((PRED_REGNO_P (c) == PRED_REGNO_P (dr))
		  && e2k_rename_free_p (c, mode, xlive, busy))
		{
		  r = c;
		  break;
		}
	  if (r == INVALID_REGNUM)
	    {
	      add_to_hard_reg_set (&ydefs, mode, dr);
	      /* A value that moves up as it is (an address computed for a
		 load) is available at the jump too.  */
	      if (movable && !conflict)
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
	  SET_HARD_REG_BIT (busy, r);
	  SET_HARD_REG_BIT (renamed, r);
	  add_to_hard_reg_set (&ydefs, mode, dr);
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_spec_rename: insn %d in bb %d: %s -> "
		     "%s%s\n", INSN_UID (insn), y->index, reg_names[dr],
		     reg_names[r], copy ? ", copied back" : "");
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

/* Print a lock load (LOCK) or a check load.  */
/* An array prefetch read (e2k_mova<mode>): OPERANDS[1] the area (its
   program instruction), [2] the channel, [3] the element size.  */
const char *
e2k_output_mova (rtx *operands)
{
  static char buf[80];
  int size = INTVAL (operands[3]);
  snprintf (buf, sizeof buf, "mova%c,%d\tarea=%d, ind=0, am=1, be=0, %%0",
	    size == 1 ? 'b' : size == 2 ? 'h' : size == 4 ? 'w' : 'd',
	    (int) INTVAL (operands[2]), (int) INTVAL (operands[1]));
  return buf;
}

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
  if (lock)
    snprintf (buf, sizeof buf, "ld%c,0,sm\t%%2, %%0, mas=0x4", sz);
  else
    {
      int n = ++e2k_dam_labelno;
      e2k_dam_pending.safe_push (n);
      e2k_dam_stubs.safe_push (n);
      snprintf (buf, sizeof buf,
		"ld%c,5\t%%2, %%0, mas=0x3\n\trbranch\t.LDAM%d", sz, n);
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
	      fp |= (ty == TYPE_FP || ty == TYPE_FMA || ty == TYPE_FCVT
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

static int
e2k_speculate_insn (rtx_insn *insn, ds_t ts, rtx *new_pat)
{
  rtx dest, src;
  if ((ts & ~BEGIN_DATA) != 0 || !e2k_spec_load_parts (insn, &dest, &src))
    return -1;
  if (e2k_ldlock_p (PATTERN (insn)))
    return 0;
  /* A pipelined loop's prologue is speculative already.  */
  if (e2k_ms_flag (insn))
    return -1;
  /* Its check, a plain load, takes the load's dependences, and loads
     have none on branches (e2k_spec_prepare): not before every branch
     the load followed is scheduled, or the check could rise above one
     and fault on an address valid only past it.  */
  for (rtx_insn *p = PREV_INSN (insn);
       p && p != current_sched_info->prev_head; p = PREV_INSN (p))
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
  return gen_rtx_SET (copy_rtx (dest),
		      gen_rtx_IF_THEN_ELSE (mode, test, copy_rtx (src),
					    copy_rtx (dest)));
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

/* Only innermost loops: %lsr is one register.  Its counter has 32 bits
   (v3); a loop whose count may not fit (iterations_max 0: unknown) is
   strip-mined (e2k_doloop_end_wide).  */
static bool
e2k_can_use_doloop_p (const widest_int &, const widest_int &iterations_max,
		      unsigned int loop_depth, bool entered_at_top)
{
  e2k_doloop_wide = (wi::eq_p (iterations_max, 0)
		     || !wi::leu_p (iterations_max, 0xffffffffU));
  return loop_depth == 1 && entered_at_top;
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
static unsigned
e2k_loop_unroll_adjust (unsigned nunroll, class loop *loop)
{
  if (!e2k_pipeline || loop->inner)
    return nunroll;
  basic_block *bbs = get_loop_body (loop);
  int full = 0;
  bool ok = true;
  auto_bitmap set, stepped;
  for (unsigned i = 0; i < loop->num_nodes; i++)
    {
      rtx_insn *insn;
      bool any = false;
      FOR_BB_INSNS (bbs[i], insn)
	if (NONDEBUG_INSN_P (insn))
	  {
	    any = true;
	    if (CALL_P (insn))
	      ok = false;
	    rtx pat = single_set (insn);
	    if (pat && REG_P (SET_DEST (pat)))
	      {
		unsigned r = REGNO (SET_DEST (pat));
		rtx src = SET_SRC (pat);
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
  if (!store && ok && (full <= 1 || (full <= 3 && !single_exit (loop))))
    {
      free (bbs);
      return 1;
    }
  for (unsigned i = 0; ok && i < loop->num_nodes; i++)
    {
      rtx_insn *insn;
      FOR_BB_INSNS (bbs[i], insn)
	if (NONDEBUG_INSN_P (insn))
	  {
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
				 || bitmap_bit_p (stepped, REGNO (t[k])))))
		      ok = false;
		}
	  }
    }
  free (bbs);
  return full - merged <= 1 && ok ? 1 : nunroll;
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
      else
	emit_insn (gen_iordi3 (lsr, lsr, gen_int_mode (E2K_LSR_VLC, DImode)));
      emit_insn (gen_e2k_rwd_lsr (lsr));
      rtx_insn *disp = emit_insn (gen_e2k_disp_label (ctpr,
						      loop->start_label));
      add_reg_note (disp, REG_LABEL_OPERAND, loop->start_label);
      LABEL_NUSES (loop->start_label)++;
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
  delete_insn (loop->loop_end);
  return true;
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

enum { E2K_MS_SM = 1, E2K_MS_ABN = 2, E2K_MS_ABP = 4 };

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

#define E2K_MS_MAX_NODES 64
#define E2K_MS_MAX_USES 4
#define E2K_MS_MAX_II 32

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
     mova, ORIG the load, which the prologue keeps.  Its area streams
     APB_SIZE-byte elements from APB_IV + APB_INV + APB_OFF in iteration
     0 (APB_INV INVALID_REGNUM if none), descriptor APB_D; channel and
     area once scheduled.  */
  bool apb;
  rtx_insn *orig;
  int apb_size, apb_d, apb_chan, apb_area;
  unsigned apb_iv, apb_inv;
  HOST_WIDE_INT apb_off;
  int time;
  int pname;			/* a predicate's ring name in its iteration */
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
  /* The part of LAT for a packed result crossing clusters, dropped in
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
     NAPB loads that do, APB_TMP a register free on the ways in.  */
  bool apb_ok = false;
  int napb = 0;
  unsigned apb_tmp = INVALID_REGNUM;
};

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
      if (t != TYPE_CMP && (t != TYPE_PLOG || !wl))
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
    case TYPE_ALU: case TYPE_ALU14: case TYPE_MUL: case TYPE_FP:
    case TYPE_FMA: case TYPE_FCVT: case TYPE_LOAD: case TYPE_STORE:
    case TYPE_PINT: case TYPE_PINT14: case TYPE_PMUL: case TYPE_PANY:
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

/* Whether memory references A and B may conflict in any two iterations.
   may_alias_p ignores offsets, but believes dependence cliques, and
   those of an inlined function's restrict pointers only hold within one
   call (one iteration; gcc.dg/torture/pr90328.c): trust only clique 1
   (the function's own restrict pointers) and those of loops versioned
   for aliasing, and else ask again without the trees.  */
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
	if (aa.ok && ab.ok && aa.inv == ab.inv && aa.iv == ab.iv
	    && aa.iv != INVALID_REGNUM)
	  {
	    /* Both step through one array: the access of B in iteration
	       I + D starts at (ob - oa) + D * C bytes from A's in I.  */
	    HOST_WIDE_INT c = step[aa.iv];
	    HOST_WIDE_INT oa = aa.offset + (ivdef[aa.iv] < a ? c : 0);
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

/* Array prefetch (spec/isa/apb.md) for the loads of L, a loop counted
   by %lsr: those that read consecutive aligned elements (a step of one
   element: the always-1 %aaincr0) through an address the loop steps,
   and whose elements no store of the loop writes before they are read
   (the buffer doesn't see stores): a store may write the element the
   load read in the same iteration, after it, or one behind.  Each
   becomes a mova (latency 5, an AAS channel, no ALU channel) in the
   kernel; the prologue keeps the load.  At most four, two to a half of
   the buffer at 1 KiB each.  STEP and IVDEF as for e2k_ms_mem_deps;
   DERIVED the stepped registers the loop computes from another.  */
static void
e2k_ms_mark_apb (e2k_ms_loop *l, const HOST_WIDE_INT *step,
		 const int *ivdef, const bool *derived)
{
  l->napb = 0;
  if (!l->apb_ok || l->want_dam)
    return;
  for (int i = 0; i < l->n && l->napb < 4; i++)
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
      if (!a.ok || a.iv == INVALID_REGNUM || step[a.iv] != size
	  || derived[a.iv])
	continue;
      HOST_WIDE_INT oa = a.offset + (ivdef[a.iv] < i ? size : 0);
      bool ok = true;
      for (int k = 0; k < l->n && ok; k++)
	{
	  e2k_ms_node *st = &l->nodes[k];
	  if (!st->store || !e2k_ms_may_alias (st->mem, src))
	    continue;
	  e2k_ms_addr b = e2k_ms_decompose (st->mem, step);
	  HOST_WIDE_INT sb = GET_MODE_SIZE (GET_MODE (st->mem));
	  HOST_WIDE_INT ob = b.offset + (b.iv != INVALID_REGNUM
					 && ivdef[b.iv] < k ? size : 0);
	  ok = (b.ok && b.inv == a.inv && b.iv == a.iv
		&& (ob + sb <= oa || (ob == oa && sb == size && k > i)));
	}
      if (!ok)
	continue;
      rtx mova = gen_e2k_mova (dm, SET_DEST (pat), const0_rtx, const0_rtx,
			       GEN_INT (size));
      rtx_insn *mi = make_insn_raw (mova);
      INSN_LOCATION (mi) = INSN_LOCATION (node->insn);
      if (recog_memoized (mi) < 0)
	continue;
      node->apb = true;
      node->orig = node->insn;
      node->insn = mi;
      node->apb_size = size;
      node->apb_d = l->napb++;
      node->apb_iv = a.iv;
      node->apb_inv = a.inv;
      node->apb_off = oa;
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
  for (e2k_ms_dep &d : l->dam_deps)
    e2k_ms_add_dep (l, d.from, k, 2, d.dist);
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
      if (l->n == E2K_MS_MAX_NODES || !e2k_ms_insn_ok (insn, l->wl))
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
      return e2k_ms_why ("%b[0..7] live into or after the loop");
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
		return e2k_ms_why ("a predicate from outside the iteration");
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
	     live_head and live_exit above).  */
	  if (B_REGNO_P (u->regno) && u->value < 0)
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
      if (t == TYPE_CMP || t == TYPE_PLOG)
	continue;
      for (int k = 0; k < l->nodes[i].nuses; k++)
	if (l->nodes[i].uses[k].pred)
	  {
	    int c = l->nodes[i].uses[k].value;
	    if (get_attr_type (l->nodes[c].insn) != TYPE_CMP)
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
	      if (i >= l->nh || (t != TYPE_CMP && t != TYPE_PLOG))
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
	int cross = (dt == TYPE_FP || dt == TYPE_FMA || dt == TYPE_FCVT
		     || dt == TYPE_MUL ? 2 : 1);
	int lat = MAX (insn_latency (def, l->nodes[i].insn), 1);
	/* A packed result costs 4 in the other cluster, as it does to an
	   integer operation (which the bypass gives).  */
	bool packed = e2k_packed_type_p (dt);
	if (packed)
	  cross = MAX (4 - lat, 0);
	/* An operation that uses its own last result stays in its
	   channel.  */
	if (def == l->nodes[i].insn)
	  cross = 0;
	e2k_ms_add_dep (l, l->values[u->value].node, i, lat + cross,
			u->dist, packed ? cross : 0);
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
  e2k_ms_mark_apb (l, step, ivdef, derived);
  e2k_ms_mem_deps (l, step, ivdef);
  if (l->want_dam && !e2k_ms_add_dam (l))
    return false;
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

/* Try to put node I of L at time T in the reservation rows ROWS.  */
static bool
e2k_ms_place (e2k_ms_loop *l, int ii, char *rows, state_t tmp, int i, int t)
{
  char *row = rows + (((t % ii) + ii) % ii) * dfa_state_size;
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

/* Modulo schedule L with initiation interval II.  */
static bool
e2k_ms_schedule (e2k_ms_loop *l, int ii)
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
      int t;
      for (t = early; t < early + ii && t <= late; t++)
	{
	  int r = ((t % ii) + ii) % ii;
	  if (r < rlo || r > rhi)
	    continue;
	  char *row = (char *) rows + r * dfa_state_size;
	  memcpy (tmp, row, dfa_state_size);
	  if (state_transition (tmp, l->nodes[i].insn) < 0)
	    {
	      memcpy (row, tmp, dfa_state_size);
	      break;
	    }
	}
      if (t >= early + ii || t > late)
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

  for (int p = 1; p <= 31; p++)
    {
      bool ok = true;
      for (int k = 0; k < nv && ok; k++)
	{
	  int v = order[k];
	  lane[v] = slot[v] = -1;
	  for (int ln = 0; ln < 2 && slot[v] < 0; ln++)
	    for (int c = 0; c < p && slot[v] < 0; c++)
	      {
		bool bad = clash (v, c, v, c, p);
		for (int k2 = 0; k2 < k && !bad; k2++)
		  {
		    int w = order[k2];
		    bad = lane[w] == ln && clash (v, c, w, slot[w], p);
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
	  l->values[v].name = 2 * n + lane[v];
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
  /* The outgoing pairs follow the ring and gas takes rbs <= 63; the
     window registers take up to 32 pairs.  */
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
  int kdef = j + l->nodes[val.node].time / l->ii - (l->stages - 1);
  int ring = 2 * l->pairs;
  int name = (val.name + 2 * (frame - kdef)) % ring;
  return name < 0 ? name + ring : name;
}

static rtx
e2k_ms_reg (machine_mode mode, int name)
{
  return gen_rtx_REG (mode, E2K_ROT_REGNO (name));
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
	if (REG_P (**iter))
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
      if (get_attr_type (x) == TYPE_CMP)
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
/* Give the movas of L their channels and areas: each kernel row's in
   channel order, channels 0 and 1 reading areas of the buffer's left
   half, 2 and 3 its right half (spec/isa/apb.md, "What a mova reads"),
   an area named by its program instruction; and queue the program,
   .LAPB<N>, each half's 2 KiB shared by its areas.  Returns N.  */
static int
e2k_ms_apb_assign (e2k_ms_loop *l)
{
  int left[4], right[4], nl = 0, nr = 0;
  for (int r = 0; r < l->ii; r++)
    {
      int ch = 0;
      for (int i = 0; i < l->n; i++)
	if (l->nodes[i].apb && l->nodes[i].time % l->ii == r)
	  {
	    e2k_ms_node *node = &l->nodes[i];
	    node->apb_chan = ch++;
	    if (node->apb_chan < 2)
	      {
		node->apb_area = nl;
		left[nl++] = i;
	      }
	    else
	      {
		node->apb_area = nr;
		right[nr++] = i;
	      }
	  }
    }
  auto asz = [] (int k)
    {
      int a = 5;
      while (a > 0 && (k << a) > 32)
	a--;
      return a;
    };
  int al = asz (nl), ar = asz (MAX (nr, 1));
  int n = ++e2k_apb_labelno;
  char buf[1024];
  int len = snprintf (buf, sizeof buf, "\t.align\t8\n.LAPB%d:\n", n);
  auto entry = [&] (int i, bool right_half, int last, int a, int idx)
    {
      e2k_ms_node *node = &l->nodes[i];
      int size = node->apb_size;
      int fmt = size == 1 ? 1 : size == 2 ? 2 : size == 4 ? 3 : 4;
      len += snprintf (buf + len, sizeof buf - len,
		       "\t  fapb\t%s=%d, dcd=0, fmt=%d, mrng=%d, d=%d, incr=0, "
		       "ind=0, asz=%d, abs=%d, disp=0\n",
		       right_half ? "dpl" : "ct", last, fmt, size, node->apb_d,
		       a, idx << a);
    };
  for (int k = 0; k < nl; k++)
    {
      len += snprintf (buf + len, sizeof buf - len, "\t{\n");
      entry (left[k], false, k == nl - 1, al, k);
      if (k < nr)
	entry (right[k], true, 0, ar, k);
      len += snprintf (buf + len, sizeof buf - len, "\t}\n");
    }
  e2k_apb_progs.safe_push (xstrdup (buf));
  return n;
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
  int korder[E2K_MS_MAX_NODES], krow[E2K_MS_MAX_NODES];
  for (int i = 0; i < l->n; i++)
    {
      korder[i] = i;
      krow[i] = l->nodes[i].time % ii;
    }
  e2k_ms_sort (korder, l->n, krow);
  int apbno = l->napb ? e2k_ms_apb_assign (l) : 0;
  auto_vec<rtx> kpats (l->n);
  for (int k = 0; k < l->n; k++)
    {
      int i = korder[k];
      kpats.quick_push (e2k_ms_instance (l, i, s - 1 - l->nodes[i].time / ii,
					 0));
      if (l->nodes[i].apb)
	{
	  rtx u = SET_SRC (e2k_ms_set (kpats[k]));
	  XVECEXP (u, 0, 0) = GEN_INT (l->nodes[i].apb_area);
	  XVECEXP (u, 0, 1) = GEN_INT (l->nodes[i].apb_chan);
	}
    }
  auto_vec<int> kseq (l->n);
  for (int g = 0; g < l->n; )
    {
      int ge = g;
      while (ge < l->n && krow[korder[ge]] == krow[korder[g]])
	ge++;
      if (!e2k_ms_order_cycle (kpats, g, ge, &kseq))
	return false;
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
		  return false;
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
	return false;
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
      emit_insn (gen_e2k_setbn_enter (GEN_INT (l->pairs),
				      GEN_INT (l->npred)));
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
  auto_vec<std::pair<basic_block, rtx_insn *> > pblocks;
  auto emit_clocked = [&] (edge e, bool copy)
    {
      basic_block p = e2k_ms_split_entry (e);
      p->flags |= BB_DISABLE_SCHEDULE;
      rtx_insn *x = BB_END (p);
      if (JUMP_P (x))
	x = PREV_INSN (x);
      x = emit_insn_after (gen_e2k_setbn_enter (GEN_INT (l->pairs),
						GEN_INT (l->npred)), x);
      e2k_ms_clock c0 = { x, 1 };
      e2k_ms_clocks.safe_push (c0);
      /* With the first cycle: nothing else of a loop uses CS0.  */
      if (ldisp)
	{
	  x = emit_ldisp (x);
	  e2k_ms_clock cd = { x, 2 };
	  e2k_ms_clocks.safe_push (cd);
	}
      for (int k : seq)
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
	  e2k_ms_clock c = { x, items[k].t - tmin + 2 };
	  e2k_ms_clocks.safe_push (c);
	}
      pblocks.safe_push (std::make_pair (p, x));
      return 1 + tlast - tmin + 1;
    };
  /* Array prefetch: on each way in, after rwd %lsr (the unit follows
     the count after a trap), each area's first element, that of the
     iteration the kernel's first instance reads (stage U of iteration
     S - 1 - U), into its descriptor; the program into %ctpr2; bap.  The
     prologue's cycles count towards the 22 a first mova would wait.  */
  auto_vec<basic_block> apb_pre;
  for (rtx_insn *pre_end : pre_ends)
    apb_pre.safe_push (BLOCK_FOR_INSN (pre_end));
  auto apb_setup = [&] (edge e)
      {
	start_sequence ();
	rtx t = gen_rtx_REG (DImode, l->apb_tmp);
	for (int i = 0; i < l->n; i++)
	  if (l->nodes[i].apb)
	    {
	      e2k_ms_node *node = &l->nodes[i];
	      HOST_WIDE_INT k = (node->apb_off
				 + (s - 1 - node->time / ii) * node->apb_size);
	      emit_insn (gen_adddi3 (t, gen_rtx_REG (DImode, node->apb_iv),
				     gen_int_mode (k, DImode)));
	      if (node->apb_inv != INVALID_REGNUM)
		emit_insn (gen_adddi3 (t, t,
				       gen_rtx_REG (DImode, node->apb_inv)));
	      emit_insn (gen_e2k_aaurwd (t, GEN_INT (node->apb_d)));
	    }
	emit_insn (gen_e2k_ldisp_apb (GEN_INT (apbno)));
	emit_insn (gen_e2k_bap ());
	rtx_insn *seq = end_sequence ();
	for (rtx_insn *x = seq; x; x = NEXT_INSN (x))
	  if (recog_memoized (x) < 0)
	    gcc_unreachable ();
	/* In a block of its own on the way in: the block of rwd %lsr may
	   end in a branch through %ctpr2.  */
	basic_block q = split_edge (e);
	emit_insn_after (seq, BB_END (q));
      };
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
     %lsr and the prologue (or the loop).  */
  if (l->napb)
    for (basic_block pb : apb_pre)
      {
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
	  int gap = kstart - tlast - 1;
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
    e2k_ms_kernels.safe_push (std::make_pair (l->bb->index, -1));

  if (kinsn)
    {
      /* The check ends a block of the kernel; the compensation code,
	 at the end of the function, jumps back to the rest.  */
      basic_block k1 = l->bb;
      basic_block k2 = split_block (k1, kinsn)->dest;
      k2->flags |= BB_DISABLE_SCHEDULE;
      e2k_ms_kernels.safe_push (std::make_pair (k1->index, k2->index));
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
      emit_insn (gen_e2k_apb_stop ());
      emit_move_insn (t, const0_rtx);
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

/* Schedule and emit the analyzed loop L (e2k_ms_emit has the other
   arguments).  */
static bool
e2k_ms_pipeline (e2k_ms_loop *l, const vec<rtx_insn *> &pre_ends,
		 const vec<edge> &entries, edge exit_edge, const e2k_ms_wl *w)
{
  basic_block bb = l->bb;
  /* In a recurrence of packed operations the crossing would set II;
     e2k_assign_channels keeps such a chain in one cluster when it can
     (each operation goes where its operands cost no stall).  */
  {
    uint64_t reach[E2K_MS_MAX_NODES];
    for (int i = 0; i < l->n; i++)
      reach[i] = 0;
    for (e2k_ms_dep &d : l->deps)
      reach[d.from] |= HOST_WIDE_INT_1U << d.to;
    for (int k = 0; k < l->n; k++)
      for (int i = 0; i < l->n; i++)
	if (reach[i] & (HOST_WIDE_INT_1U << k))
	  reach[i] |= reach[k];
    for (e2k_ms_dep &d : l->deps)
      if (d.cross && (reach[d.to] & (HOST_WIDE_INT_1U << d.from)))
	{
	  d.lat -= d.cross;
	  d.cross = 0;
	}
  }
  /* Lower bounds: operations per cycle, then the length of one
     iteration when not pipelined.  */
  int loads = 0, stores = 0, alu = 0, c03 = 0, c14 = 0, c0134 = 0;
  for (int i = 0; i < l->n; i++)
    {
      loads += !l->nodes[i].store && l->nodes[i].mem && !l->nodes[i].apb;
      stores += l->nodes[i].store;
      /* landp runs in the PLS, a mova in an AAS channel, not in an ALU
	 channel.  */
      enum attr_type t = get_attr_type (l->nodes[i].insn);
      alu += t != TYPE_PLOG && t != TYPE_MOVA;
      /* Packed operations, two or four channels.  */
      c03 += t == TYPE_PINT;
      c14 += t == TYPE_PINT14 || t == TYPE_PMUL || t == TYPE_ALU14;
      c0134 += e2k_packed_type_p (t) || t == TYPE_ALU14;
    }
  /* A store in ALC2 or ALC5 keeps a load out of ALC3 or ALC0 (gas,
     spec/isa/bundle.md), so an instruction holds 4 - 2 * stores loads.  */
  int mii = MAX (CEIL (alu, 6), MAX (CEIL (loads + 2 * stores, 4),
				     CEIL (stores, 2)));
  mii = MAX (mii, MAX (CEIL (c03, 2), MAX (CEIL (c14, 2), CEIL (c0134, 4))));
  if (l->napb)
    {
      /* Array prefetch costs about 20 cycles a run (the setup, and bap's
	 22 to the first mova, spec/isa/apb.md, "Timing"): worth it when
	 the movas, out of the ALU and load channels, shorten the kernel,
	 or when the loop is known to run long (it also takes the memory
	 latency out of the loop).  */
      int mii_apb = MAX (mii, CEIL (l->napb, 4));
      int mii_ld = MAX (mii, MAX (CEIL (alu + l->napb, 6),
				  CEIL (loads + l->napb + 2 * stores, 4)));
      gcov_type iters = 0;
      profile_count entry = profile_count::zero ();
      edge e;
      edge_iterator ei;
      FOR_EACH_EDGE (e, ei, bb->preds)
	if (e->src != bb)
	  entry += e->count ();
      if (bb->count.reliable_p () && entry.reliable_p () && entry.nonzero_p ())
	iters = bb->count.to_gcov_type () / MAX (entry.to_gcov_type (), 1);
      if (mii_ld <= mii_apb && iters < E2K_APB_MIN_TRIP && !e2k_apb_force)
	return e2k_ms_why ("array prefetch would not pay");
      mii = mii_apb;
    }
  /* A while loop's exit predicate lives 3 cycles at least, and without
     rotation (e2k_ms_assign_pnames) at most II.  */
  if (l->wl && !e2k_rotate_preds)
    mii = MAX (mii, 3);
  /* One iteration alone: its critical path (through dependences
     within the iteration) or its operations at 6 per cycle.  */
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
  int ii;
  bool ok = false;
  /* Worth a prologue, a ring and two setbn only if the kernel is
     clearly shorter than one iteration.  */
  for (ii = MAX (mii, 1);
       ii + 2 <= len && 4 * ii <= 3 * len && ii <= E2K_MS_MAX_II; ii++)
    if (e2k_ms_schedule (l, ii))
      {
	ok = true;
	break;
      }
  if (ok && dump_file)
    fprintf (dump_file, ";; e2k_modsched: loop bb %d: %d insns, "
	     "II %d, %d stages, unpipelined %d%s\n", bb->index, l->n,
	     l->ii, l->stages, len, l->wl ? ", while loop" : "");
  if (!ok)
    return e2k_ms_fail (bb, "no schedule shorter than one iteration");
  e2k_ms_dam_plan (l);
  if (!e2k_ms_assign_names (l, 0))
    return e2k_ms_fail (bb, "ring too big");
  if (!e2k_ms_assign_pnames (l))
    return e2k_ms_fail (bb, "predicate ring");
  /* Lifetimes that touch let two instructions of one cycle each write
     what the other reads, which the prologue can't do in sequence; then
     keep a cycle between them.  */
  if (!e2k_ms_emit (l, pre_ends, entries, exit_edge, w)
      && (!e2k_ms_assign_names (l, 1)
	  || !e2k_ms_emit (l, pre_ends, entries, exit_edge, w)))
    return e2k_ms_fail (bb, "prologue order");
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
  bool apb_retry = false;
  for (int attempt = 0; ; attempt++)
    {
      bool ok = e2k_ms_analyze (l, exit);
      if (!ok)
	e2k_ms_fail (bb, "body");
      else
	ok = e2k_ms_pipeline (l, pre_ends, entries, exit_edge, w);
      /* Without array prefetch, if that failed with it.  */
      bool apb_again = !ok && l->napb > 0;
      if (!apb_again
	  && (ok || attempt > (apb_retry ? 1 : 0) || !l->may_dam || !e2k_dam))
	{
	  delete l;
	  return ok;
	}
      apb_retry |= apb_again;
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
      l2->want_dam = !apb_again;
      l2->may_dam = false;
      l2->dam = l2->kchk = -1;
      l2->apb_ok = false;
      delete l;
      l = l2;
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: loop bb %d again with%s\n",
		 bb->index, apb_again ? "out array prefetch" : " DAM");
    }
}

/* Pipeline the loop that BB is, ending in the hardware loop end JUMP.  */
/* %b[0..7] can't hold a value a pipelined loop uses: setbn renames
   them.  Give each one the loop uses a global register free around and
   in the loop, for the loop: copied there before it if live into it,
   back after it (after the setbn that gives the outgoing registers
   back) if live after it.  False if there's none free.  Under high
   register pressure (main of Linpack, everything inlined) allocation
   puts loop invariants there once the window is full.  */
static bool
e2k_ms_move_b (const vec<basic_block> &bbs, const vec<rtx_insn *> &pre_ends,
	       const vec<edge> &entries, edge exit_edge)
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
  unsigned map[8];
  int n = 0;
  for (int k = 0; k < 8; k++)
    if (used[k])
      {
	unsigned g;
	for (g = 0; g < 24; g++)
	  {
	    bool taken = false;
	    for (int k2 = 0; k2 < k; k2++)
	      taken |= used[k2] && map[k2] == g;
	    if (!taken && !fixed_regs[g] && !TEST_HARD_REG_BIT (body, g)
		&& !bitmap_bit_p (lh, g) && !bitmap_bit_p (lx, g)
		&& !bitmap_bit_p (lo, g))
	      break;
	  }
	if (g == 24)
	  return false;
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
   a window register dead on every way in.  */
static bool
e2k_ms_apb_ok (e2k_ms_loop *l, const vec<rtx_insn *> &pre_ends,
	       basic_block exit)
{
  if (!e2k_apb)
    return false;
  if (recog_memoized (l->jump) != CODE_FOR_e2k_hwloop_end)
    return e2k_ms_why ("no array prefetch: not a plain counted loop");
  rtx ctpr2 = gen_rtx_REG (DImode, CTPR2_REGNUM);
  if (reg_mentioned_p (ctpr2, PATTERN (l->jump))
      || REGNO_REG_SET_P (df_get_live_in (l->bb), CTPR2_REGNUM)
      || REGNO_REG_SET_P (df_get_live_in (exit), CTPR2_REGNUM))
    return e2k_ms_why ("no array prefetch: %ctpr2 in use");
  HARD_REG_SET used;
  CLEAR_HARD_REG_SET (used);
  for (rtx_insn *insn : l->insns)
    {
      if (reg_mentioned_p (ctpr2, PATTERN (insn)))
	return e2k_ms_why ("no array prefetch: %ctpr2 in the loop");
      e2k_note_regs (PATTERN (insn), &used);
    }
  for (rtx_insn *pre_end : pre_ends)
    {
      basic_block pb = BLOCK_FOR_INSN (pre_end);
      for (rtx_insn *x = NEXT_INSN (pre_end); x && x != NEXT_INSN (BB_END (pb));
	   x = NEXT_INSN (x))
	if (INSN_P (x))
	  e2k_note_regs (PATTERN (x), &used);
    }
  l->apb_tmp = INVALID_REGNUM;
  for (unsigned r = R0_REGNUM; r < R0_REGNUM + 64; r++)
    {
      if (fixed_regs[r] || TEST_HARD_REG_BIT (used, r))
	continue;
      bool dead = true;
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
  if (!e2k_ms_move_b (bbs, pre_ends, no_entries, exit_edge))
    return e2k_ms_fail (bb, "no global register for a %b[] value");

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
  if (!e2k_ms_move_b (bbs, no_pre_ends, entries, exit_edge))
    return e2k_ms_fail (h, "no global register for a %b[] value");

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
  static char buf[96];
  machine_function *m = cfun->machine;
  e2k_compute_window ();
  int n;
  if (pairs == 0 && m->use_b)
    n = snprintf (buf, sizeof buf, "setbn\trsz = 3, rbs = %d, rcur = 0",
		  m->wbase);
  else
    n = snprintf (buf, sizeof buf, "setbn\trsz = %d, rbs = %d, rcur = 0",
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
   This GIMPLE pass, after the vectorizer, does the same for innermost
   counted loops without calls, with GCC's runtime alias checks (as loop
   distribution uses them).  In the disjoint copy, every memory
   reference gets a base in a new dependence clique, one per base
   address, as restrict would give: references with the same base keep
   the same base number and so claim nothing about each other, and a
   pair with different bases either was proved independent or is
   covered by the test.  Alias analysis in RTL, the scheduler (and its
   data speculation) and the modulo scheduler then see the copy's
   arrays as disjoint.  */

/* Bytes from the first to the last access of DR over NITERS + 1
   iterations, as tree-loop-distribution.cc computes them.  */
static tree
e2k_av_segment (class loop *loop, data_reference *dr, tree niters)
{
  if (dominated_by_p (CDI_DOMINATORS, single_exit (loop)->src,
		      gimple_bb (DR_STMT (dr))))
    niters = size_binop (PLUS_EXPR, niters, size_one_node);
  niters = size_binop (MINUS_EXPR, niters, size_one_node);
  return size_binop (MULT_EXPR, fold_convert (sizetype, DR_STEP (dr)),
		     niters);
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

static bool
e2k_av_loop (function *fun, class loop *loop)
{
  if (loop->inner || !single_exit (loop) || !optimize_loop_for_speed_p (loop)
      || loop->dont_vectorize
      || fun->machine->n_av_cliques == ARRAY_SIZE (fun->machine->av_cliques))
    return false;
  tree niters = number_of_latch_executions (loop);
  if (!niters || niters == chrec_dont_know)
    return false;

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
    return false;

  auto_vec<loop_p, 3> nest;
  auto_vec<data_reference_p> drs;
  auto_vec<ddr_p> ddrs;
  bool ok = compute_data_dependences_for_loop (loop, false, &nest, &drs, &ddrs);
  /* Group the references by base address.  */
  auto_vec<int> group;
  bool write = false;
  for (unsigned i = 0; ok && i < drs.length (); i++)
    {
      data_reference *dr = drs[i];
      if (!DR_BASE_ADDRESS (dr) || !DR_STEP (dr)
	  || TREE_CODE (DR_STEP (dr)) != INTEGER_CST
	  || integer_zerop (DR_STEP (dr))
	  || !e2k_av_base_ref (dr)
	  || !tree_fits_uhwi_p (TYPE_SIZE_UNIT (TREE_TYPE (DR_REF (dr)))))
	{
	  ok = false;
	  break;
	}
      write |= DR_IS_WRITE (dr);
      unsigned g = i;
      for (unsigned k = 0; k < i; k++)
	if (operand_equal_p (DR_BASE_ADDRESS (drs[k]), DR_BASE_ADDRESS (dr), 0))
	  {
	    g = group[k];
	    break;
	  }
      group.safe_push (g);
    }
  ok &= write;

  auto_vec<dr_with_seg_len_pair_t> pairs;
  tree n = fold_convert (sizetype, niters);
  for (unsigned i = 0; ok && i < ddrs.length (); i++)
    {
      ddr_p ddr = ddrs[i];
      data_reference *a = DDR_A (ddr), *b = DDR_B (ddr);
      if (DDR_ARE_DEPENDENT (ddr) == chrec_known)
	continue;
      unsigned ia = 0, ib = 0;
      for (unsigned k = 0; k < drs.length (); k++)
	{
	  if (drs[k] == a)
	    ia = k;
	  if (drs[k] == b)
	    ib = k;
	}
      if (group[ia] == group[ib])
	continue;
      /* Different bases that are known to depend on each other.  */
      if (DDR_ARE_DEPENDENT (ddr) != chrec_dont_know)
	{
	  ok = false;
	  break;
	}
      if (!DR_IS_WRITE (a) && !DR_IS_WRITE (b))
	continue;
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
      prune_runtime_alias_test_list (&pairs, tree_fits_uhwi_p (niters)
				     ? tree_to_uhwi (niters) : 1);
      ok = pairs.length () <= 4;
    }
  else
    ok = false;

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
	    {
	      tree base = e2k_av_base_ref (drs[i]);
	      MR_DEPENDENCE_CLIQUE (base) = clique;
	      MR_DEPENDENCE_BASE (base) = group[i] + 1;
	    }
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

class pass_e2k_alias_version : public gimple_opt_pass
{
public:
  pass_e2k_alias_version (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_e2k_alias_version, ctxt)
  {}

  bool gate (function *) final override
  {
    return e2k_alias_version && optimize >= 2 && flag_tree_loop_optimize;
  }

  unsigned int execute (function *fun) final override
  {
    if (number_of_loops (fun) <= 1)
      return 0;
    bool changed = false;
    calculate_dominance_info (CDI_DOMINATORS);
    for (auto loop : loops_list (fun, LI_ONLY_INNERMOST))
      changed |= e2k_av_loop (fun, loop);
    if (!changed)
      return 0;
    scev_reset ();
    rewrite_into_loop_closed_ssa (NULL, TODO_update_ssa);
    return TODO_cleanup_cfg;
  }
};

} // anon namespace

static gimple_opt_pass *
make_pass_e2k_alias_version (gcc::context *ctxt)
{
  return new pass_e2k_alias_version (ctxt);
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
    case TYPE_ALU: case TYPE_ALU14: case TYPE_CMP: case TYPE_MUL:
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

static void
e2k_spec_pin (rtx_insn *head, rtx_insn *tail)
{
  e2k_cond_ret_deps (head, tail);
  if (!e2k_control_spec || e2k_spec_from.is_empty ())
    return;
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
  e2k_ms_clocks.truncate (0);
  e2k_ms_twin.truncate (0);
  e2k_ms_kernels.truncate (0);

  /* SMS marks the loops it pipelined so that sched2 keeps its order;
     here the scheduler also forms the wide instructions, so every
     block goes through it (but the kernels of e2k_modsched).  */
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    bb->flags &= ~BB_DISABLE_SCHEDULE;

  if (optimize)
    {
      reorg_loops (false, &e2k_doloop_hooks);
      commit_edge_insertions ();
    }

  if (optimize >= 2 && e2k_merge_chains_p && e2k_control_spec)
    e2k_merge_chains ();
  if (optimize && flag_schedule_insns_after_reload && e2k_bundle
      && e2k_pipeline && e2k_pipeline_while)
    e2k_ms_tail_dup ();
  if (optimize >= 2 && e2k_cond_returns_p)
    e2k_cond_returns ();
  if (optimize && e2k_loop_ct)
    e2k_prepare_loop_branches ();
  if (optimize && e2k_prepare_br)
    e2k_prepare_branches ();
  if (optimize && e2k_control_spec && e2k_spec_rename_p)
    e2k_spec_rename ();

  if (optimize && flag_schedule_insns_after_reload && e2k_bundle)
    {
      split_all_insns ();
      if (e2k_pipeline)
	e2k_modsched ();
      if (e2k_prepare_br)
	e2k_share_ctprs ();
      e2k_sched_init_global (NULL, 0, 0);
      if (e2k_control_spec)
	e2k_spec_prepare ();
      timevar_push (TV_SCHED2);
      schedule_ebbs ();
      timevar_pop (TV_SCHED2);
      if (e2k_control_spec)
	e2k_spec_mark ();
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
