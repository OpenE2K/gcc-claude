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
};

static struct machine_function *
e2k_init_machine_status (void)
{
  return ggc_cleared_alloc<machine_function> ();
}

static gimple_opt_pass *make_pass_e2k_alias_version (gcc::context *);

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
  if (COMPLEX_MODE_P (mode) || VECTOR_MODE_P (mode))
    return false;

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
  return code == '#' || code == '<' || code == '>' || code == ',';
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
      || INSN_CODE (insn) == CODE_FOR_e2k_disp_label)
    return 0;

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
static int
e2k_adjust_cost (rtx_insn *con, int dep_type, rtx_insn *pro, int cost,
		 unsigned int)
{
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

static void
e2k_sched_init_global (FILE *, int, int)
{
  e2k_insn_clock.truncate (0);
  e2k_insn_clock.safe_grow_cleared (get_max_uid () + 1);
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

static int
e2k_variable_issue (FILE *, int, rtx_insn *insn, int more)
{
  unsigned uid = INSN_UID (insn);
  if (uid < e2k_insn_clock.length ())
    e2k_insn_clock[uid] = e2k_sched_clock + 1;
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

enum e2k_rkind { E2K_RK_NONE, E2K_RK_INT, E2K_RK_LOAD, E2K_RK_FP };

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
      enum attr_type t = get_attr_type (ops[i]);
      load[i] = t == TYPE_LOAD;
      store[i] = t == TYPE_STORE;
      bool fp = (t == TYPE_FP || t == TYPE_FMA || t == TYPE_FCVT
		 || t == TYPE_MUL || t == TYPE_FCMP || t == TYPE_FDIV);
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

static void
e2k_assign_channels (void)
{
  e2k_chan_prod *tab = e2k_chan_tab;
  for (int r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    tab[r].kind = E2K_RK_NONE;
  rtx_insn *ops[8];
  int n = 0, pos = 0;
  bool over = false;
  for (rtx_insn *insn = get_insns (); insn; insn = NEXT_INSN (insn))
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
	    e2k_chan_bundle (ops, n, pos, tab);
	  pos += 1 + m.nops;
	  n = 0;
	}
    }
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
      /* Nor anything X touches: the computation is to move up there.  */
      rtx_insn *insn;
      FOR_BB_INSNS (x, insn)
	if (INSN_P (insn))
	  e2k_note_regs (PATTERN (insn), &busy);
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
			   || TEST_HARD_REG_BIT (jregs, dr));
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
	      CLEAR_HARD_REG_BIT (renamed, dr);
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

/* Don't unroll what e2k_modsched will pipeline well (an innermost loop
   of one block without calls, whose addresses its dependence test
   understands: registers that the loop steps by a constant or doesn't
   change, plus a constant): its kernel overlaps iterations anyway, and
   an unrolled body needs a longer kernel and more rotating registers
   for the same speed or worse.  lcc doesn't unroll those either.
   Other loops keep their unrolling for the scheduler.  */
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
  /* Without stores there are no memory dependences to understand.  */
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
  if (!store && full <= 1 && ok)
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
  return full <= 1 && ok ? 1 : nunroll;
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

  /* Before the loop: %lsr = count | vlc, at least 4 cycles ahead, and
     the CTPR.  The iteration register is dead once the loop doesn't
     count it down, or holds the iterations after the first chunk:
     ((count - 1) & -CHUNK).  The first chunk is ((count - 1) &
     (CHUNK - 1)) + 1.  */
  edge e;
  edge_iterator ei;
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
static void
e2k_hwloop_fail (hwloop_info)
{
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

enum { E2K_MS_SM = 1, E2K_MS_ABN = 2 };

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
  int value;
  int dist;			/* 0: this iteration's value; 1: the last */
};

struct e2k_ms_node
{
  rtx_insn *insn;
  int value;			/* value defined, or -1 */
  int nuses;
  e2k_ms_use uses[E2K_MS_MAX_USES];
  rtx mem;			/* memory reference, if any */
  bool store;
  int time;
};

struct e2k_ms_value
{
  int node;			/* defining node */
  unsigned regno;
  machine_mode mode;
  bool carried;			/* read by the next iteration */
  bool live_out;		/* the last iteration's value is used after */
  int span;			/* rotations from the def to the last use */
  int name;			/* %b[] name in the defining iteration */
};

struct e2k_ms_dep
{
  int from, to, lat, dist;
};

struct e2k_ms_loop
{
  basic_block bb;
  rtx_insn *jump;
  int n;
  e2k_ms_node nodes[E2K_MS_MAX_NODES];
  auto_vec<e2k_ms_value> values;
  auto_vec<e2k_ms_dep> deps;
  int ii, stages, pairs;
};

/* Whether a loop body insn can be pipelined: one SET of a register or
   memory, of a kind that has a speculative form.  */
static bool
e2k_ms_insn_ok (rtx_insn *insn)
{
  if (!NONJUMP_INSN_P (insn) || recog_memoized (insn) < 0)
    return false;
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) != SET || volatile_refs_p (pat)
      || side_effects_p (SET_SRC (pat)))
    return false;
  switch (get_attr_type (insn))
    {
    case TYPE_ALU: case TYPE_ALU14: case TYPE_MUL: case TYPE_FP:
    case TYPE_FMA: case TYPE_FCVT: case TYPE_LOAD: case TYPE_STORE:
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
e2k_ms_add_dep (e2k_ms_loop *l, int from, int to, int lat, int dist)
{
  for (e2k_ms_dep &d : l->deps)
    if (d.from == from && d.to == to && d.dist == dist)
      {
	d.lat = MAX (d.lat, lat);
	return;
      }
  e2k_ms_dep d = { from, to, lat, dist };
  l->deps.safe_push (d);
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
	bool alias = e2k_ms_may_alias (na->mem, nb->mem);
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
		  e2k_ms_add_dep (l, a, b, 1, d);
		diff = oa - ob + d * c;			/* A(I+D) - B(I) */
		if (d > 0 && diff > -sa && diff < sb)
		  e2k_ms_add_dep (l, b, a, 1, d);
	      }
	  }
	else if (aa.ok && ab.ok && aa.inv == ab.inv && aa.iv == ab.iv)
	  {
	    /* The same invariant address every iteration.  */
	    e2k_ms_add_dep (l, a, b, 1, 0);
	    e2k_ms_add_dep (l, b, a, 1, 1);
	  }
	else
	  {
	    e2k_ms_add_dep (l, a, b, 1, 0);
	    e2k_ms_add_dep (l, b, a, 1, 1);
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

/* Find the nodes, values and dependences of the loop in L->bb.  */
static bool
e2k_ms_analyze (e2k_ms_loop *l, basic_block exit)
{
  basic_block bb = l->bb;
  l->n = 0;
  rtx_insn *insn;
  FOR_BB_INSNS (bb, insn)
    {
      if (!NONDEBUG_INSN_P (insn) || insn == l->jump)
	continue;
      if (l->n == E2K_MS_MAX_NODES || !e2k_ms_insn_ok (insn))
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
      rtx pat = PATTERN (insn);
      rtx dest = SET_DEST (pat);
      if (MEM_P (dest))
	{
	  node->store = true;
	  node->mem = dest;
	  if (!e2k_ms_note_uses (node, XEXP (dest, 0)))
	    return e2k_ms_why ("too many registers");
	}
      if (!e2k_ms_note_uses (node, SET_SRC (pat)))
	return e2k_ms_why ("too many registers");
      subrtx_iterator::array_type array;
      FOR_EACH_SUBRTX (iter, array, SET_SRC (pat), NONCONST)
	if (MEM_P (*iter))
	  node->mem = const_cast<rtx> (*iter);
    }
  if (l->n < 2)
    return e2k_ms_why ("fewer than 2 insns");

  /* Values: one per definition.  CUR[r] is the value of r so far in this
     iteration, LAST[r] the body's last.  */
  int cur[FIRST_PSEUDO_REGISTER], last[FIRST_PSEUDO_REGISTER];
  for (int r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    cur[r] = last[r] = -1;
  for (int i = 0; i < l->n; i++)
    {
      rtx dest = SET_DEST (PATTERN (l->nodes[i].insn));
      if (REG_P (dest))
	{
	  e2k_ms_value v;
	  memset (&v, 0, sizeof v);
	  v.node = i;
	  v.regno = REGNO (dest);
	  v.mode = GET_MODE (dest);
	  l->nodes[i].value = l->values.length ();
	  last[v.regno] = l->values.length ();
	  l->values.safe_push (v);
	}
    }
  bitmap live_head = df_get_live_in (bb);
  bitmap live_exit = df_get_live_in (exit);
  /* setbn renames %b[0..7] for the loop, but the ring lies below the
     registers they name outside it: a value there may pass through the
     loop, but the loop can't read one in or leave one behind.  */
  for (unsigned r = B0_REGNUM; r < B0_REGNUM + 8; r++)
    if (last[r] >= 0
	&& (bitmap_bit_p (live_head, r) || bitmap_bit_p (live_exit, r)))
      return e2k_ms_why ("%b[0..7] live into or after the loop");
  for (int i = 0; i < l->n; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      for (int k = 0; k < node->nuses; k++)
	{
	  e2k_ms_use *u = &node->uses[k];
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
    }
  for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    if (last[r] >= 0
	&& (bitmap_bit_p (live_exit, r)
	    || TEST_HARD_REG_BIT (e2k_ms_live_out_extra, r)))
      l->values[last[r]].live_out = true;

  /* Register dependences.  */
  for (int i = 0; i < l->n; i++)
    for (int k = 0; k < l->nodes[i].nuses; k++)
      {
	e2k_ms_use *u = &l->nodes[i].uses[k];
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
	/* An operation that uses its own last result stays in its
	   channel.  */
	if (def == l->nodes[i].insn)
	  cross = 0;
	e2k_ms_add_dep (l, l->values[u->value].node, i,
			MAX (insn_latency (def, l->nodes[i].insn), 1) + cross,
			u->dist);
      }

  /* Induction registers: defined once, as r = r + C, and carried.  */
  HOST_WIDE_INT step[FIRST_PSEUDO_REGISTER];
  int ivdef[FIRST_PSEUDO_REGISTER];
  for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    {
      step[r] = 0;
      ivdef[r] = -1;
    }
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].value >= 0)
      {
	unsigned r = l->values[l->nodes[i].value].regno;
	rtx src = SET_SRC (PATTERN (l->nodes[i].insn));
	if (step[r] == 0 && ivdef[r] < 0 && last[r] == l->nodes[i].value
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
  e2k_ms_mem_deps (l, step, ivdef);
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

  for (int k = 0; k < n; k++)
    {
      int i = order[k];
      int early = INT_MIN, late = INT_MAX;
      for (e2k_ms_dep &d : l->deps)
	{
	  if (d.to == i && l->nodes[d.from].time != INT_MIN)
	    early = MAX (early, l->nodes[d.from].time + d.lat - ii * d.dist);
	  if (d.from == i && l->nodes[d.to].time != INT_MIN)
	    late = MIN (late, l->nodes[d.to].time - d.lat + ii * d.dist);
	}
      /* Only successors placed: as late as they allow (an induction
	 step before the loads of the next iteration that use it).  */
      if (early == INT_MIN)
	early = late == INT_MAX ? 0 : late - (ii - 1);
      int t;
      for (t = early; t < early + ii && t <= late; t++)
	{
	  char *row = (char *) rows + (((t % ii) + ii) % ii) * dfa_state_size;
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
		     "in %d..%d\n", ii, INSN_UID (l->nodes[i].insn), early,
		     MIN (early + ii - 1, late));
	  return false;
	}
      l->nodes[i].time = t;
    }

  /* Start at stage 0, keeping the rows (the loop end is in the last).  */
  int mint = INT_MAX;
  for (int i = 0; i < n; i++)
    mint = MIN (mint, l->nodes[i].time);
  int shift = (mint >= 0 ? mint / ii : -((-mint + ii - 1) / ii)) * ii;
  for (int i = 0; i < n; i++)
    l->nodes[i].time -= shift;

  /* Every store goes to the last stage, the same row.  */
  int maxt = 0;
  for (int i = 0; i < n; i++)
    maxt = MAX (maxt, l->nodes[i].time);
  int stages = maxt / ii + 1;
  for (int i = 0; i < n; i++)
    if (l->nodes[i].store)
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
      if (val.live_out)
	en[v] = MAX (en[v], s * ii);
      order.quick_push (v);
      lane.quick_push (-1);
      slot.quick_push (-1);
    }
  for (int i = 0; i < l->n; i++)
    for (int k = 0; k < l->nodes[i].nuses; k++)
      {
	e2k_ms_use *u = &l->nodes[i].uses[k];
	if (u->value >= 0)
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
		     l->values[v].live_out ? " live-out" : "");
	}
      return true;
    }
  /* The outgoing pairs follow the ring and gas takes rbs <= 63; the
     window registers take up to 32 pairs.  */
  return false;
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

/* Node I's pattern for iteration J, with names in the frame of kernel
   iteration FRAME.  */
static rtx
e2k_ms_instance (e2k_ms_loop *l, int i, int j, int frame)
{
  e2k_ms_node *node = &l->nodes[i];
  rtx pat = copy_rtx (PATTERN (node->insn));
  auto subst = [&] (rtx *loc)
    {
      subrtx_ptr_iterator::array_type array;
      FOR_EACH_SUBRTX_PTR (iter, array, loc, NONCONST)
	if (REG_P (**iter))
	  for (int k = 0; k < node->nuses; k++)
	    if (node->uses[k].regno == REGNO (**iter)
		&& node->uses[k].value >= 0)
	      {
		rtx *slot = *iter;
		*slot = e2k_ms_reg (GET_MODE (**iter),
				  e2k_ms_name (l, node->uses[k].value,
					       j - node->uses[k].dist,
					       frame));
		break;
	      }
    };
  subst (&SET_SRC (pat));
  if (MEM_P (SET_DEST (pat)))
    subst (&XEXP (SET_DEST (pat), 0));
  else
    SET_DEST (pat) = e2k_ms_reg (GET_MODE (SET_DEST (pat)),
				 e2k_ms_name (l, node->value, j, frame));
  return pat;
}

/* Whether pattern X reads hard register R.  */
static bool
e2k_ms_reads_p (rtx x, unsigned r)
{
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
	  rtx da = SET_DEST (pats[a]);
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

/* Emit the pipelined loop: prologue before PRE_END, kernel, copies out
   on EXIT_EDGE.  False, with nothing changed, if the prologue can't be
   put in order.  */
static bool
e2k_ms_emit (e2k_ms_loop *l, const vec<rtx_insn *> &pre_ends, edge exit_edge)
{
  int ii = l->ii, s = l->stages;

  /* Prologue: the copies in and the first S - 1 stages of iterations
     0 .. S - 2, in the order the kernel would run them.  */
  auto_vec<e2k_ms_item> items;
  for (unsigned v = 0; v < l->values.length (); v++)
    if (l->values[v].carried)
      {
	e2k_ms_item it = { -ii + l->nodes[l->values[v].node].time, -1, -1,
			   (int) v };
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
	  pats.quick_push (gen_rtx_SET (e2k_ms_reg (v.mode,
						    e2k_ms_name (l, it.value,
								 -1, 0)),
					gen_rtx_REG (v.mode, v.regno)));
	}
      else
	pats.quick_push (e2k_ms_instance (l, it.node, it.j, 0));
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
  auto_vec<rtx> kpats (l->n);
  for (int k = 0; k < l->n; k++)
    {
      int i = korder[k];
      kpats.quick_push (e2k_ms_instance (l, i, s - 1 - l->nodes[i].time / ii,
					 0));
    }
  auto_vec<int> kseq (l->n);
  for (int g = 0; g < l->n; )
    {
      int ge = g;
      while (ge < l->n && krow[korder[ge]] == krow[korder[g]])
	ge++;
      if (!e2k_ms_order_cycle (kpats, g, ge, &kseq))
	return false;
      g = ge;
    }
  /* The same prologue before each way into the loop.  */
  for (unsigned p = 0; p < pre_ends.length (); p++)
    {
      rtx_insn *pre_end = pre_ends[p];
      emit_insn_before (gen_e2k_setbn_enter (GEN_INT (l->pairs)), pre_end);
      for (int k : seq)
	{
	  rtx_insn *insn
	    = emit_insn_before (p ? copy_rtx (pats[k]) : pats[k], pre_end);
	  if (items[k].node >= 0)
	    {
	      INSN_LOCATION (insn)
		= INSN_LOCATION (l->nodes[items[k].node].insn);
	      e2k_ms_set_flag (insn, E2K_MS_SM);
	    }
	  recog_memoized (insn);
	}
    }

  /* Empty first cycles of the kernel are an empty wide instruction.  */
  int row0 = ii;
  for (int i = 0; i < l->n; i++)
    row0 = MIN (row0, l->nodes[i].time % ii);
  if (row0 > 0)
    emit_insn_before (gen_e2k_nop_bundle (GEN_INT (row0 - 1)), l->jump);
  for (int k : kseq)
    {
      int i = korder[k];
      rtx_insn *insn = emit_insn_before (kpats[k], l->jump);
      INSN_LOCATION (insn) = INSN_LOCATION (l->nodes[i].insn);
      recog_memoized (insn);
      if (!l->nodes[i].store)
	e2k_ms_set_flag (insn, E2K_MS_SM);
      e2k_ms_clock c = { insn, l->nodes[i].time % ii + 1 };
      e2k_ms_clocks.safe_push (c);
    }
  /* Dataflow doesn't know that the old %b[N] is the new %b[N + 2]: to
     it, the values the next iteration reads under another name are
     dead (and the prologue's too).  Use every name at the loop end.  */
  for (int name = 0; name < 2 * l->pairs; name++)
    emit_insn_before (gen_rtx_USE (VOIDmode, e2k_ms_reg (DImode, name)),
		      l->jump);
  e2k_ms_clock c = { l->jump, ii };
  e2k_ms_clocks.safe_push (c);
  e2k_ms_set_flag (l->jump, E2K_MS_ABN);
  for (int i = 0; i < l->n; i++)
    delete_insn (l->nodes[i].insn);
  rtx_insn *insn, *next;
  for (insn = BB_HEAD (l->bb); insn != NEXT_INSN (BB_END (l->bb));
       insn = next)
    {
      next = NEXT_INSN (insn);
      if (DEBUG_INSN_P (insn))
	delete_insn (insn);
    }
  l->bb->flags |= BB_DISABLE_SCHEDULE;

  /* After the loop: the last iteration's values, then the outgoing
     registers back.  The kernel ran n times, so a value defined in
     stage D of iteration n - 1 has rotated S - D times since.  */
  start_sequence ();
  for (unsigned v = 0; v < l->values.length (); v++)
    if (l->values[v].live_out)
      {
	const e2k_ms_value &val = l->values[v];
	int name = (val.name + 2 * (s - l->nodes[val.node].time / ii))
		   % (2 * l->pairs);
	emit_insn (gen_rtx_SET (gen_rtx_REG (val.mode, val.regno),
				e2k_ms_reg (val.mode, name)));
      }
  emit_insn (gen_e2k_setbn_leave ());
  rtx_insn *after = end_sequence ();
  /* Before what e2k_ms_move_b put on the edge.  */
  rtx_insn *old = exit_edge->insns.r;
  exit_edge->insns.r = NULL;
  insert_insn_on_edge (after, exit_edge);
  if (old)
    insert_insn_on_edge (old, exit_edge);
  return true;
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
e2k_ms_move_b (basic_block bb, const vec<rtx_insn *> &pre_ends,
	       edge exit_edge)
{
  CLEAR_HARD_REG_SET (e2k_ms_live_out_extra);
  bool used[8] = { false };
  HARD_REG_SET body;
  CLEAR_HARD_REG_SET (body);
  rtx_insn *insn;
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
  bitmap lh = df_get_live_in (bb), lx = df_get_live_in (exit_edge->dest);
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
		&& !bitmap_bit_p (lh, g) && !bitmap_bit_p (lx, g))
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
  FOR_BB_INSNS (bb, insn)
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

  if (!e2k_ms_move_b (bb, pre_ends, exit_edge))
    return e2k_ms_fail (bb, "no global register for a %b[] value");

  e2k_ms_loop *l = new e2k_ms_loop;
  l->bb = bb;
  l->jump = jump;
  bool ok = e2k_ms_analyze (l, exit_edge->dest);
  if (!ok)
    e2k_ms_fail (bb, "body");
  if (ok)
    {
      /* Lower bounds: operations per cycle, then the length of one
	 iteration when not pipelined.  */
      int loads = 0, stores = 0;
      for (int i = 0; i < l->n; i++)
	{
	  loads += !l->nodes[i].store && l->nodes[i].mem;
	  stores += l->nodes[i].store;
	}
      int mii = MAX (CEIL (l->n, 6), MAX (CEIL (loads, 4), CEIL (stores, 2)));
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
      int ii;
      ok = false;
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
		 "II %d, %d stages, unpipelined %d\n", bb->index, l->n,
		 l->ii, l->stages, len);
      if (!ok)
	e2k_ms_fail (bb, "no schedule shorter than one iteration");
      else if (!e2k_ms_assign_names (l, 0))
	ok = e2k_ms_fail (bb, "ring too big");
      /* Lifetimes that touch let two instructions of one cycle each
	 write what the other reads, which the prologue can't do in
	 sequence; then keep a cycle between them.  */
      if (ok && !e2k_ms_emit (l, pre_ends, exit_edge)
	  && (!e2k_ms_assign_names (l, 1)
	      || !e2k_ms_emit (l, pre_ends, exit_edge)))
	ok = e2k_ms_fail (bb, "prologue order");
      if (ok)
	cfun->machine->rot_pairs = MAX (cfun->machine->rot_pairs, l->pairs);
    }
  delete l;
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
  dfa_start ();
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *jump = BB_END (bb);
      if (!JUMP_P (jump)
	  || (recog_memoized (jump) != CODE_FOR_e2k_hwloop_end
	      && recog_memoized (jump) != CODE_FOR_e2k_hwloop_end_wide)
	  || JUMP_LABEL (jump) != BB_HEAD (bb))
	continue;
      e2k_ms_loop_1 (bb, jump);
    }
  dfa_finish ();
  /* Also when no loop was pipelined: e2k_ms_move_b puts its copies back
     on the exit edge before the schedule is tried (left there, they are
     lost, and the edge points at insns the garbage collector later
     reads as GIMPLE).  */
  commit_edge_insertions ();
}

const char *
e2k_output_setbn (int pairs)
{
  static char buf[64];
  machine_function *m = cfun->machine;
  e2k_compute_window ();
  if (pairs == 0 && m->use_b)
    snprintf (buf, sizeof buf, "setbn\trsz = 3, rbs = %d, rcur = 0",
	      m->wbase);
  else
    snprintf (buf, sizeof buf, "setbn\trsz = %d, rbs = %d, rcur = 0",
	      (pairs ? pairs : m->rot_pairs) - 1, m->ring_base);
  return buf;
}

const char *
e2k_output_hwloop_end (rtx_insn *insn)
{
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

/* Control speculation the way lcc does it: an operation moved above a
   branch runs speculatively (",sm"), a load giving a diagnostic value
   instead of a fault on an invalid address, any other operation passing
   a diagnostic operand on (spec/isa/speculation.md).  Only a
   non-speculative use of a diagnostic value traps, and on the path the
   operation came from its operands were valid; on the other path its
   result is dead (sched-ebb moves nothing above a branch whose other
   path needs the register).  So sched-ebb is told loads can't trap, and
   whatever it moves above a branch gets ",sm" afterwards; operations
   without a safe speculative form stay below the branches before them
   (e2k_spec_pin).  FP operations among those: a speculative one that
   would raise a flag not yet set gives a diagnostic value instead.  */

/* For each insn UID, its block's place in the layout before scheduling,
   or -1.  */
static vec<int> e2k_spec_from;

/* Whether INSN may run above a branch, and how: 1 with ",sm", 2 as it
   is, 0 not.  */
static int
e2k_spec_kind (rtx_insn *insn)
{
  if (!NONDEBUG_INSN_P (insn) || recog_memoized (insn) < 0
      || e2k_asm_insn_p (insn))
    return 0;
  switch (get_attr_type (insn))
    {
    case TYPE_ALU: case TYPE_ALU14: case TYPE_CMP: case TYPE_MUL:
    case TYPE_LOAD:
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
  int place = 0;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *insn;
      FOR_BB_INSNS (bb, insn)
	{
	  if (!NONDEBUG_INSN_P (insn))
	    continue;
	  e2k_spec_from[INSN_UID (insn)] = place;
	  if (e2k_spec_kind (insn) != 1)
	    continue;
	  rtx set = single_set (insn);
	  if (!set)
	    continue;
	  rtx *loc = &SET_SRC (set);
	  if (GET_CODE (*loc) == ZERO_EXTEND || GET_CODE (*loc) == SIGN_EXTEND)
	    loc = &XEXP (*loc, 0);
	  if (MEM_P (*loc) && !MEM_VOLATILE_P (*loc) && !MEM_NOTRAP_P (*loc))
	    {
	      /* A copy (a store may share the MEM), put in place directly:
		 validate_change ignores a change only of flags.  */
	      rtx mem = copy_rtx (*loc);
	      MEM_NOTRAP_P (mem) = 1;
	      *loc = mem;
	    }
	}
      place++;
    }
}

/* sched-ebb's dependence hook: keep what has no speculative form below
   the branches before it.  */
static void
e2k_spec_pin (rtx_insn *head, rtx_insn *tail)
{
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
      if (JUMP_P (insn))
	jump = insn;
    }
}

/* After scheduling: ",sm" for what moved above a branch.  */
static void
e2k_spec_mark (void)
{
  basic_block bb;
  int place = 0;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *insn;
      FOR_BB_INSNS (bb, insn)
	{
	  unsigned uid = INSN_UID (insn);
	  if (NONDEBUG_INSN_P (insn) && uid < e2k_spec_from.length ()
	      && e2k_spec_from[uid] > place)
	    {
	      int k = e2k_spec_kind (insn);
	      gcc_assert (k != 0);
	      if (k == 1)
		e2k_ms_set_flag (insn, E2K_MS_SM);
	    }
	}
      place++;
    }
  e2k_spec_from.truncate (0);
}

static void
e2k_reorg (void)
{
  compute_bb_for_insn ();
  e2k_bundling = false;
  e2k_ms_flags.truncate (0);
  e2k_ms_clocks.truncate (0);

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
