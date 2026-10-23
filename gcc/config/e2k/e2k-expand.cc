/* Expanders and splitters for the Elbrus (E2K) port (e2k.md,
   e2k-vect.md): moves, compares, conditional moves and stores, 64-bit
   vectors, field extracts and inserts (getf, insf), byte-swapped loads
   and stores.
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

/* Expand a move; return true if done.  */
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
bool e2k_laying_out_parms;

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

  /* x86 OF, (f & 0x800) != 0 (e2k_emit_of_branch): cctopo, which a
     flag operation's result reaches in 2 cycles in its channel, an
     integer compare in 4 (spec/isa/timing.md).  */
  if (e2k_flag_ops && (code == EQ || code == NE) && b == const0_rtx
      && GET_CODE (a) == AND && GET_MODE (a) == SImode
      && REG_P (XEXP (a, 0)) && CONST_INT_P (XEXP (a, 1))
      && INTVAL (XEXP (a, 1)) == 0x800)
    {
      emit_insn (gen_e2k_cctopo (pred, XEXP (a, 0)));
      *invert = code == EQ;
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

/* Jump to LABEL if the x86 flags F (SImode, from a flag operation) have
   OF set.  The and goes into a register of its own, so that
   if-conversion sees a plain comparison (and makes a store-flag of the
   flag of a value); combine folds it into the branch's bit test,
   *cbranchsi4_and, which e2k_emit_cmp makes a cctopo.  */
void
e2k_emit_of_branch (rtx f, rtx label)
{
  rtx t = gen_reg_rtx (SImode);
  emit_insn (gen_andsi3 (t, f, GEN_INT (0x800)));
  emit_jump_insn (gen_cbranchsi4 (gen_rtx_NE (VOIDmode, t, const0_rtx), t,
				  const0_rtx, label));
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

/* ------------------------------------------------------------------ */
/* 64-bit vectors (e2k-vect.md)                                        */
/* ------------------------------------------------------------------ */

/* The vector modes live in the integer registers, 8 bytes like
   DImode, and from v5 also 16 bytes in one register (e2k_v16_mode_p).  */
bool
e2k_vector_mode_supported_p (machine_mode mode)
{
  return (mode == V8QImode || mode == V4HImode || mode == V2SImode
	  || mode == V2SFmode || e2k_v16_mode_p (mode));
}

/* ------------------------------------------------------------------ */
/* 128-bit vectors, v5 and later (e2k-vect.md)                         */
/* ------------------------------------------------------------------ */

/* OPERANDS[0] = OPERANDS[1] shifted by the register OPERANDS[2] (0 to
   127), CODE ASHIFT, LSHIFTRT or ASHIFTRT, in 64-bit operations and
   without a branch.  For a count S below 64 one half takes the bits the
   other loses, (x >> 1) >> (63 - S) for x >> (64 - S), which S = 0 would
   make a shift by 64; from 64 on the result is one half shifted across,
   and a mask made from bit 6 of the count picks.  */
void
e2k_expand_ti_shift (enum rtx_code code, rtx *operands)
{
  rtx src = force_reg (TImode, operands[1]);
  rtx lo = force_reg (DImode, simplify_gen_subreg (DImode, src, TImode, 0));
  rtx hi = force_reg (DImode, simplify_gen_subreg (DImode, src, TImode, 8));
  rtx cnt = force_reg (DImode, operands[2]);
  auto op = [] (rtx_code c, rtx a, rtx b)
    {
      return expand_simple_binop (DImode, c, a, b, NULL_RTX, 1,
				  OPTAB_DIRECT);
    };
  rtx s = op (AND, cnt, GEN_INT (63));
  rtx inv = op (XOR, s, GEN_INT (63));
  rtx m = expand_simple_unop (DImode, NEG,
			      op (AND, op (LSHIFTRT, cnt, GEN_INT (6)),
				  const1_rtx),
			      NULL_RTX, 0);
  rtx nm = expand_simple_unop (DImode, NOT, m, NULL_RTX, 0);
  rtx rlo, rhi;
  if (code == ASHIFT)
    {
      rtx los = op (ASHIFT, lo, s);
      rtx carry = op (LSHIFTRT, op (LSHIFTRT, lo, const1_rtx), inv);
      rtx hsmall = op (IOR, op (ASHIFT, hi, s), carry);
      rhi = op (IOR, op (AND, los, m), op (AND, hsmall, nm));
      rlo = op (AND, los, nm);
    }
  else
    {
      rtx his = op (code, hi, s);
      rtx carry = op (ASHIFT, op (ASHIFT, hi, const1_rtx), inv);
      rtx lsmall = op (IOR, op (LSHIFTRT, lo, s), carry);
      rlo = op (IOR, op (AND, his, m), op (AND, lsmall, nm));
      rhi = op (AND, his, nm);
      if (code == ASHIFTRT)
	rhi = op (IOR, rhi, op (AND, op (ASHIFTRT, hi, GEN_INT (63)), m));
    }
  rtx t = gen_reg_rtx (TImode);
  emit_move_insn (simplify_gen_subreg (DImode, t, TImode, 0), rlo);
  emit_move_insn (simplify_gen_subreg (DImode, t, TImode, 8), rhi);
  emit_move_insn (operands[0], t);
}

/* Whether MODE is a 16-byte vector mode, which takes one register.  */
bool
e2k_v16_mode_p (machine_mode mode)
{
  return (e2k_arch >= 5 && VECTOR_MODE_P (mode)
	  && known_eq (GET_MODE_SIZE (mode), 16));
}

/* The low (HI false) or high half of V as a DImode register.  */
static rtx
e2k_v16_half (rtx v, bool hi)
{
  machine_mode mode = GET_MODE (v);
  rtx t = gen_reg_rtx (DImode);
  v = force_reg (mode, v);
  emit_insn (hi ? gen_e2k_qphi (mode, t, v) : gen_e2k_qplo (mode, t, v));
  return t;
}

/* TARGET = HI:LO.  */
static void
e2k_v16_pack (rtx target, rtx hi, rtx lo)
{
  machine_mode mode = GET_MODE (target);
  if (!e2k_src1_operand (hi, DImode))
    hi = force_reg (DImode, hi);
  if (!e2k_src2_operand (lo, DImode))
    lo = force_reg (DImode, lo);
  emit_insn (gen_e2k_qppack (mode, target, hi, lo));
}

/* The 64-bit vector mode of half the lanes of MODE.  */
static machine_mode
e2k_v16_half_mode (machine_mode mode)
{
  return mode_for_vector (as_a <scalar_mode> (GET_MODE_INNER (mode)),
			  GET_MODE_NUNITS (mode) / 2).require ();
}

/* A move of a 16-byte vector; true if done.  Constants are built from
   their halves; loads on v5 are two ldd and qppackdl (ldqp is served by
   L2, 11 cycles: spec/isa/timing.md, "Elbrus-8C2"; lcc's way); a store
   to an address not known to be 16-byte aligned is two std on v5, where
   stqp needs that alignment (else SIGBUS).  */
/* MEM, a 16-byte vector access, with the alignment its type promises:
   the vectorizer gives an access it knows to be misaligned a type of
   lesser alignment, and C requires a vector type's own, but expand
   believes a pointer's weaker known alignment over the type's
   (get_object_alignment), and ivopts' new pointers keep the array's
   8 bytes, not the 16 the vectorizer found by peeling (PolyBench's
   heat-3d: every load two ldd, none a movaqp).  */
static rtx
e2k_v16_type_align (rtx mem)
{
  tree e = MEM_EXPR (mem);
  if (MEM_ALIGN (mem) >= 128 || !e
      || (TREE_CODE (e) != MEM_REF && TREE_CODE (e) != TARGET_MEM_REF)
      || !VECTOR_TYPE_P (TREE_TYPE (e))
      || TYPE_ALIGN (TREE_TYPE (e)) < 128
      || !MEM_OFFSET_KNOWN_P (mem) || maybe_ne (MEM_OFFSET (mem), 0))
    return mem;
  mem = copy_rtx (mem);
  set_mem_align (mem, 128);
  return mem;
}

bool
e2k_expand_move_v16 (rtx *operands)
{
  rtx dst = operands[0], src = operands[1];
  machine_mode mode = GET_MODE (dst);
  if (!can_create_pseudo_p ())
    return false;
  if (MEM_P (src))
    src = operands[1] = e2k_v16_type_align (src);
  if (MEM_P (dst))
    dst = operands[0] = e2k_v16_type_align (dst);
  /* To or from a 16-byte value of another mode in a register pair: GCC
     moves a vector between its two argument or result slots and a
     register through such a value (emit_group_store, emit_group_load),
     and the subreg between them can't be a register's
     (e2k_can_change_mode_class), so it went through memory.  Through
     the halves instead.  */
  auto pair_p = [&] (rtx x)
    {
      return (SUBREG_P (x) && SUBREG_BYTE (x) == 0
	      && REG_P (SUBREG_REG (x))
	      && !e2k_v16_mode_p (GET_MODE (SUBREG_REG (x)))
	      && known_eq (GET_MODE_SIZE (GET_MODE (SUBREG_REG (x))), 16));
    };
  if (pair_p (src))
    {
      rtx inner = SUBREG_REG (src);
      machine_mode im = GET_MODE (inner);
      rtx t = REG_P (dst) ? dst : gen_reg_rtx (mode);
      e2k_v16_pack (t, simplify_gen_subreg (DImode, inner, im, 8),
		    simplify_gen_subreg (DImode, inner, im, 0));
      if (t != dst)
	emit_move_insn (dst, t);
      return true;
    }
  if (pair_p (dst))
    {
      rtx inner = SUBREG_REG (dst);
      machine_mode im = GET_MODE (inner);
      rtx v = force_reg (mode, src);
      emit_move_insn (simplify_gen_subreg (DImode, inner, im, 0),
		      e2k_v16_half (v, false));
      emit_move_insn (simplify_gen_subreg (DImode, inner, im, 8),
		      e2k_v16_half (v, true));
      return true;
    }
  if (GET_CODE (src) == CONST_VECTOR && src != CONST0_RTX (mode))
    {
      rtx lo = simplify_gen_subreg (DImode, src, mode, 0);
      rtx hi = simplify_gen_subreg (DImode, src, mode, 8);
      rtx t = REG_P (dst) ? dst : gen_reg_rtx (mode);
      e2k_v16_pack (t, hi, lo);
      if (t != dst)
	emit_move_insn (dst, t);
      return true;
    }
  if (MEM_P (dst) && src != CONST0_RTX (mode))
    src = operands[1] = force_reg (mode, src);
  if (MEM_P (src) && e2k_arch == 5)
    {
      rtx lo = gen_reg_rtx (DImode), hi = gen_reg_rtx (DImode);
      emit_move_insn (lo, adjust_address (src, DImode, 0));
      emit_move_insn (hi, adjust_address (src, DImode, 8));
      rtx t = REG_P (dst) ? dst : gen_reg_rtx (mode);
      e2k_v16_pack (t, hi, lo);
      if (t != dst)
	emit_move_insn (dst, t);
      return true;
    }
  if (MEM_P (dst) && MEM_ALIGN (dst) < 128 && e2k_arch == 5)
    {
      if (src == CONST0_RTX (mode))
	src = force_reg (mode, src);
      emit_move_insn (adjust_address (dst, DImode, 0),
		      e2k_v16_half (src, false));
      emit_move_insn (adjust_address (dst, DImode, 8),
		      e2k_v16_half (src, true));
      return true;
    }
  return false;
}

/* TARGET = the lanes of PARALLEL VALS: each half built as a 64-bit
   value, then the two packed.  */
void
e2k_expand_vec_init_v16 (rtx target, rtx vals)
{
  machine_mode mode = GET_MODE (target);
  int nelt = GET_MODE_NUNITS (mode);
  machine_mode emode = GET_MODE_INNER (mode);
  bool all_const = true;
  for (int i = 0; i < nelt; i++)
    if (!CONSTANT_P (XVECEXP (vals, 0, i)))
      all_const = false;
  if (all_const)
    {
      emit_move_insn (target, gen_rtx_CONST_VECTOR (mode, XVEC (vals, 0)));
      return;
    }
  rtx half[2];
  for (int h = 0; h < 2; h++)
    if (nelt == 2)
      half[h] = gen_lowpart (DImode, force_reg (emode, XVECEXP (vals, 0, h)));
    else
      {
	machine_mode hmode = e2k_v16_half_mode (mode);
	rtvec v = rtvec_alloc (nelt / 2);
	for (int i = 0; i < nelt / 2; i++)
	  RTVEC_ELT (v, i) = XVECEXP (vals, 0, h * nelt / 2 + i);
	rtx hv = gen_reg_rtx (hmode);
	e2k_expand_vec_init (hv, gen_rtx_PARALLEL (hmode, v));
	half[h] = gen_lowpart (DImode, hv);
      }
  e2k_v16_pack (target, half[1], half[0]);
}

/* TARGET = lane N of V.  */
void
e2k_expand_vec_extract_v16 (rtx target, rtx v, int n)
{
  machine_mode mode = GET_MODE (v);
  int nelt = GET_MODE_NUNITS (mode);
  bool hi = n >= nelt / 2;
  rtx half = e2k_v16_half (v, hi);
  if (nelt == 2)
    emit_move_insn (target, gen_lowpart (GET_MODE_INNER (mode), half));
  else
    e2k_expand_vec_extract (target,
			    gen_lowpart (e2k_v16_half_mode (mode), half),
			    n - (hi ? nelt / 2 : 0));
}

/* TARGET = X in every lane.  */
void
e2k_expand_vec_duplicate_v16 (rtx target, rtx x)
{
  machine_mode mode = GET_MODE (target);
  rtx d;
  if (GET_MODE_NUNITS (mode) == 2)
    d = gen_lowpart (DImode, force_reg (GET_MODE_INNER (mode), x));
  else
    {
      rtx hv = gen_reg_rtx (e2k_v16_half_mode (mode));
      e2k_expand_vec_duplicate (hv, x);
      d = gen_lowpart (DImode, hv);
    }
  d = force_reg (DImode, d);
  e2k_v16_pack (target, d, d);
}

/* DST = -SRC (ABS_P false) or |SRC| on FP lanes: the sign bits flipped
   or cleared through V2DImode.  */
void
e2k_expand_v16_signop (rtx dst, rtx src, bool abs_p)
{
  machine_mode mode = GET_MODE (dst);
  HOST_WIDE_INT m = (GET_MODE_INNER (mode) == SFmode
		     ? (HOST_WIDE_INT) 0x8000000080000000ULL
		     : HOST_WIDE_INT_MIN);
  rtx mk = force_reg (DImode, gen_int_mode (m, DImode));
  rtx mask = gen_reg_rtx (V2DImode);
  emit_insn (gen_e2k_qppack (V2DImode, mask, mk, mk));
  rtx x = gen_lowpart (V2DImode, force_reg (mode, src));
  rtx r = gen_reg_rtx (V2DImode);
  if (abs_p)
    emit_insn (gen_rtx_SET (r, gen_rtx_AND (V2DImode,
					    gen_rtx_NOT (V2DImode, mask), x)));
  else
    emit_insn (gen_xorv2di3 (r, x, mask));
  emit_move_insn (dst, gen_lowpart (mode, r));
}

/* The FP compare into lane masks, by its number in UNSPEC_QPFCMP.  */
const char *
e2k_output_qpfcmp (rtx *operands, bool single)
{
  static const char *const names[] = { "eq", "lt", "le", "uod",
				       "neq", "nlt", "nle", "od" };
  static char buf[48];
  snprintf (buf, sizeof buf, "qpfcmp%s%c\t%%1, %%2, %%0%%?",
	    names[INTVAL (operands[3])], single ? 's' : 'd');
  return buf;
}

/* DEST = lane masks of A CODE B on FP lanes: what the hardware has
   directly, or with the operands swapped, or two of them combined.  */
void
e2k_expand_vec_fcmp_v16 (rtx dest, enum rtx_code code, rtx a, rtx b)
{
  machine_mode mode = GET_MODE (a), mmode = GET_MODE (dest);
  enum { EQ_ = 0, LT_, LE_, UOD_, NEQ_, NLT_, NLE_, OD_ };
  auto cmp = [&] (rtx d, int k, rtx x, rtx y)
    {
      emit_insn (gen_e2k_qpfcmp (mode, d, force_reg (mode, x),
				 force_reg (mode, y), GEN_INT (k)));
    };
  switch (code)
    {
    case EQ: cmp (dest, EQ_, a, b); return;
    case LT: cmp (dest, LT_, a, b); return;
    case LE: cmp (dest, LE_, a, b); return;
    case GT: cmp (dest, LT_, b, a); return;
    case GE: cmp (dest, LE_, b, a); return;
    case NE: cmp (dest, NEQ_, a, b); return;
    case UNORDERED: cmp (dest, UOD_, a, b); return;
    case ORDERED: cmp (dest, OD_, a, b); return;
    case UNGE: cmp (dest, NLT_, a, b); return;
    case UNGT: cmp (dest, NLE_, a, b); return;
    case UNLE: cmp (dest, NLT_, b, a); return;
    case UNLT: cmp (dest, NLE_, b, a); return;
    case UNEQ: case LTGT:
      {
	rtx t1 = gen_reg_rtx (mmode), t2 = gen_reg_rtx (mmode);
	cmp (t1, code == UNEQ ? EQ_ : NEQ_, a, b);
	cmp (t2, code == UNEQ ? UOD_ : OD_, a, b);
	emit_insn (gen_rtx_SET (dest, code == UNEQ
				? gen_rtx_IOR (mmode, t1, t2)
				: gen_rtx_AND (mmode, t1, t2)));
	return;
      }
    default:
      gcc_unreachable ();
    }
}

/* TARGET = the sum of V's lanes: the halves added, then their lanes.  */
void
e2k_expand_reduc_plus_v16 (rtx target, rtx v)
{
  machine_mode mode = GET_MODE (v);
  machine_mode emode = GET_MODE_INNER (mode);
  rtx lo = e2k_v16_half (v, false), hi = e2k_v16_half (v, true);
  if (GET_MODE_NUNITS (mode) == 2)
    {
      rtx s = expand_simple_binop (emode, PLUS, gen_lowpart (emode, lo),
				   gen_lowpart (emode, hi), target, 0,
				   OPTAB_LIB_WIDEN);
      if (s != target)
	emit_move_insn (target, s);
      return;
    }
  machine_mode hmode = e2k_v16_half_mode (mode);
  rtx s = expand_simple_binop (hmode, PLUS, gen_lowpart (hmode, lo),
			       gen_lowpart (hmode, hi), NULL_RTX, 0,
			       OPTAB_LIB_WIDEN);
  s = force_reg (hmode, s);
  insn_code icode = optab_handler (reduc_plus_scal_optab, hmode);
  if (icode != CODE_FOR_nothing)
    {
      emit_insn (GEN_FCN (icode) (target, s));
      return;
    }
  int n = GET_MODE_NUNITS (hmode);
  rtx acc = NULL_RTX;
  for (int i = 0; i < n; i++)
    {
      rtx e = gen_reg_rtx (emode);
      e2k_expand_vec_extract (e, s, i);
      acc = acc ? expand_simple_binop (emode, PLUS, acc, e, NULL_RTX, 0,
				       OPTAB_LIB_WIDEN) : e;
    }
  emit_move_insn (target, acc);
}

/* What the vectorizer works in.  Packed integer operations issue in two
   channels (four for shifts and shuffles) where scalar ones take six, so
   the gain is in the lanes and in memory: 8 bytes to an ldd and an std,
   whose channels (4 loads, 2 stores) bound most loops.  */
machine_mode
e2k_preferred_simd_mode (scalar_mode mode)
{
  /* 16-byte vectors on v5+ (-mvect128).  */
  if (e2k_vect128 && e2k_arch >= 5)
    switch (mode)
      {
      case E_QImode:
	return V16QImode;
      case E_HImode:
	return V8HImode;
      case E_SImode:
	return V4SImode;
      case E_DImode:
	return V2DImode;
      case E_SFmode:
	return V4SFmode;
      case E_DFmode:
	return V2DFmode;
      default:
	return word_mode;
      }
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

/* What the vectorizer counts with -mvect128 on v5+, for a pipelined
   loop's kernel, in halves of an ALU channel slot (six a cycle): an
   operation 2; a load 1 (array prefetch reads in an AAS channel, an
   ldd in a load channel), a store 1 (an AAU store or st in channel 2
   or 5).  A 16-byte vector is an aligned movaqp or staaqp, or as two
   halves: two loads and a qppackdl, or addd, qpswitchd and two stores
   (e2k_expand_move_v16).  Integer qp arithmetic issues in ALC0 and 3
   only (qpaddw, qpcmp*), FP in all six.  Otherwise GCC's.  */
int
e2k_builtin_vectorization_cost (enum vect_cost_for_stmt kind, tree vectype,
				int misalign)
{
  if (!e2k_vect128 || e2k_arch < 5)
    return default_builtin_vectorization_cost (kind, vectype, misalign);
  bool fp = vectype && FLOAT_TYPE_P (TREE_TYPE (vectype));
  int n = vectype ? TYPE_VECTOR_SUBPARTS (vectype).to_constant () : 1;
  switch (kind)
    {
    case scalar_stmt:
      return 2;
    case scalar_load:
    case scalar_store:
    case vector_store:
      return 1;
    case vector_stmt:
      return fp ? 2 : 3;
    case vector_load:
      return 2;
    /* v6 loads and stores 16 bytes at any address in one operation
       (ldqp, stqp; spec/isa/semantics.md), so peeling for alignment
       buys nothing there.  */
    case unaligned_load:
      return e2k_arch >= 6 ? 2 : 4;
    case unaligned_store:
      return e2k_arch >= 6 ? 1 : 6;
    case vec_to_scalar:
    case scalar_to_vec:
      return 2;
    case vec_perm:
      return 3;
    case vec_promote_demote:
      return 4;
    case vec_construct:
    case vec_deconstruct:
      return n == 2 ? 2 : 2 * n;
    case vector_gather_load:
    case vector_scatter_store:
      return 3 * n + 2;
    case cond_branch_not_taken:
      return 1;
    case cond_branch_taken:
      return 4;
    default:
      return default_builtin_vectorization_cost (kind, vectype, misalign);
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
      if (mode == V2DImode)
	{
	  /* No unsigned max of 64-bit lanes: flip the sign bits and
	     compare signed.  */
	  rtx sb = force_reg (mode, gen_const_vec_duplicate
				      (mode, gen_int_mode (HOST_WIDE_INT_MIN,
							   DImode)));
	  rtx fa = gen_reg_rtx (mode), fb = gen_reg_rtx (mode);
	  emit_insn (gen_xorv2di3 (fa, force_reg (mode, a), sb));
	  emit_insn (gen_xorv2di3 (fb, force_reg (mode, b), sb));
	  e2k_expand_vec_cmp (dest, signed_condition (code), fa, fb);
	  return;
	}
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
  /* Through the optab: a 16-byte vector's NOT is an xor with all ones.  */
  rtx r = expand_simple_unop (mode, NOT, t, dest, 1);
  if (r != dest)
    emit_move_insn (dest, r);
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

bool
e2k_vectorize_vec_perm_const (machine_mode vmode, machine_mode op_mode,
			      rtx target, rtx op0, rtx op1,
			      const vec_perm_indices &sel)
{
  if (vmode != op_mode || !e2k_vector_mode_supported_p (vmode))
    return false;
  if (e2k_v16_mode_p (vmode))
    {
      if (!target)
	return true;
      /* qppermb a, b, c: byte c[i] & 15 of a where c[i] bit 4 is set,
	 else of b: OP1 as a, OP0 as b.  */
      int nelt = GET_MODE_NUNITS (vmode);
      int esize = 16 / nelt;
      rtvec v = rtvec_alloc (16);
      for (int i = 0; i < nelt; i++)
	{
	  int e = sel[i].to_constant () % (2 * nelt);
	  int base = e < nelt ? e * esize : 16 + (e - nelt) * esize;
	  for (int k = 0; k < esize; k++)
	    RTVEC_ELT (v, i * esize + k) = GEN_INT (base + k);
	}
      rtx m = force_reg (V16QImode, gen_rtx_CONST_VECTOR (V16QImode, v));
      emit_insn (gen_e2k_qppermb (vmode, target, force_reg (vmode, op1),
				  force_reg (vmode, op0), m));
      return true;
    }
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
      rtx z = force_reg (DImode, convert_modes (DImode, imode, e, 1));
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

/* Whether a field of LEN bits at POS of a MODE value is one getf takes
   (getfs keeps at most 31 bits).  */
bool
e2k_getf_field_p (machine_mode mode, rtx len, rtx pos)
{
  if (!CONST_INT_P (len) || !CONST_INT_P (pos))
    return false;
  HOST_WIDE_INT l = INTVAL (len), p = INTVAL (pos);
  return l >= 1 && l < GET_MODE_BITSIZE (mode) && p >= 0
	 && p + l <= GET_MODE_BITSIZE (mode);
}

/* getfd OPERANDS[1] of the field (OPERANDS[2] bits at OPERANDS[3]):
   offset, length, sign, and BYTE naming the field's top byte, which v1-v4
   take the sign from; getfs for a 32-bit value.  Not getfd there: under
   dbl = 0 a 32-bit operation's result reaches a 64-bit reader 3 cycles
   late (spec/isa/timing.md), and its upper half may hold a diagnostic
   value, which a 64-bit read traps on (e2k_partial_subreg_p).  */
const char *
e2k_output_getf (rtx *operands, bool sign)
{
  static char buf[64];
  HOST_WIDE_INT l = INTVAL (operands[2]), p = INTVAL (operands[3]);
  bool s32 = GET_MODE (operands[0]) == SImode;
  int w = s32 ? 32 : 64;
  HOST_WIDE_INT d = p | l << 6;
  if (sign)
    d |= 1 << 12 | (((p + l - 1) & (w - 1)) / 8) << 13;
  snprintf (buf, sizeof buf, "getf%c\t%%1, %#" PRIx64 ", %%0",
	    s32 ? 's' : 'd', (uint64_t) d);
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

/* OPERANDS[0] = OPERANDS[1] + OPERANDS[2] (PLUS) or - in TImode on v5:
   the low halves with addd or subd, the carry or borrow out of them
   with addcd_c or subcd_c, and the high halves with addcd or subcd
   taking it in (e2k_addcd and the others).  */
void
e2k_expand_addsub_ti (rtx *operands, bool plus)
{
  rtx half[3][2];
  for (int k = 0; k < 3; k++)
    for (int h = 0; h < 2; h++)
      half[k][h] = simplify_gen_subreg (DImode, operands[k], TImode, 8 * h);
  rtx zero = force_reg (DImode, const0_rtx);
  rtx a0 = force_reg (DImode, half[1][0]), b0 = force_reg (DImode, half[2][0]);
  rtx a1 = force_reg (DImode, half[1][1]), b1 = force_reg (DImode, half[2][1]);
  rtx lo = gen_reg_rtx (DImode), c = gen_reg_rtx (DImode);
  rtx hi = gen_reg_rtx (DImode);
  if (plus)
    {
      emit_insn (gen_adddi3 (lo, a0, b0));
      emit_insn (gen_e2k_addcd_c (c, a0, b0, zero));
      emit_insn (gen_e2k_addcd (hi, a1, b1, c));
    }
  else
    {
      emit_insn (gen_subdi3 (lo, a0, b0));
      emit_insn (gen_e2k_subcd_c (c, a0, b0, zero));
      emit_insn (gen_e2k_subcd (hi, a1, b1, c));
    }
  emit_move_insn (half[0][0], lo);
  emit_move_insn (half[0][1], hi);
}

/* v5's getfz (spec/isa/semantics.md, "Field extract"): getf, then the
   result's low BYTE bits cleared.  The descriptor that makes it
   (X >> K) & M in MODE (RIGHT), or (X << K) & M, for M a run of ones
   from bit 1 to 7 up: a field scaled by 2 to 128 in one operation (an
   index into an array of such elements, as lcc's Lua interpreter has
   them), where v3 takes a shift and an AND.  -1 if there is none.  */
HOST_WIDE_INT
e2k_getfz_desc (machine_mode mode, bool right, rtx k, rtx m)
{
  if (e2k_arch < 5 || !CONST_INT_P (k) || !CONST_INT_P (m))
    return -1;
  int w = GET_MODE_BITSIZE (mode);
  unsigned HOST_WIDE_INT mask = UINTVAL (m) & GET_MODE_MASK (mode);
  HOST_WIDE_INT s = INTVAL (k);
  if (mask == 0 || s <= 0 || s >= w)
    return -1;
  int z = ctz_hwi (mask);
  unsigned HOST_WIDE_INT run = mask >> z;
  if (z < 1 || z > 7 || (run & (run + 1)) != 0)
    return -1;
  int top = z + popcount_hwi (run);
  int off;
  if (right)
    {
      /* X >> K has no bits from W - K up, where the rotate would bring
	 in X's low ones.  */
      top = MIN (top, w - s);
      off = s;
    }
  else
    {
      /* X << K has no bits below K; the rotate puts X's top ones
	 there, which the cleared low bits must cover.  */
      if (z < s)
	return -1;
      off = w - s;
    }
  if (top <= z || top >= w)
    return -1;
  return off | top << 6 | z << 13;
}

/* getfz for OPERANDS[0] = (OPERANDS[1] shifted by OPERANDS[2]) &
   OPERANDS[3] (e2k_getfz_desc).  Bits 16 and up of a descriptor don't
   matter: one with bit 15 set goes as a negative 16-bit literal (lcc
   gives it a 32-bit one).  */
const char *
e2k_output_getfz (rtx *operands, bool right)
{
  static char buf[64];
  machine_mode mode = GET_MODE (operands[0]);
  HOST_WIDE_INT d = e2k_getfz_desc (mode, right, operands[2], operands[3]);
  gcc_assert (d >= 0);
  if (d >= 0x8000)
    d -= 0x10000;
  snprintf (buf, sizeof buf, "getfz%c\t%%1, " HOST_WIDE_INT_PRINT_DEC
	    ", %%0", mode == SImode ? 's' : 'd', d);
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
bool
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
      /* v5's getfz of a scaled field (*getfz<mode>_lshr, _ashl, not
	 predicable): counted from its operands, a shift and a mask both
	 below 16 took no literal, and the scheduler packed a fifth into
	 the wide instruction (gas: "literals cannot be packed").  */
      if ((GET_CODE (XEXP (s, 0)) == LSHIFTRT
	   || GET_CODE (XEXP (s, 0)) == ASHIFT)
	  && e2k_getfz_desc (GET_MODE (s), GET_CODE (XEXP (s, 0)) == LSHIFTRT,
			     XEXP (XEXP (s, 0), 1), XEXP (s, 1)) >= 0)
	return true;
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
