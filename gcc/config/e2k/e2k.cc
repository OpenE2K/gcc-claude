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

  /* glibc jmp_buf for nonlocal gotos and __builtin_longjmp to this
     function (e2k_expand_save_stack_nonlocal).  */
  rtx nonlocal_jmpbuf;
};

static struct machine_function *
e2k_init_machine_status (void)
{
  return ggc_cleared_alloc<machine_function> ();
}

static void
e2k_option_override (void)
{
  init_machine_status = e2k_init_machine_status;

  /* We schedule and bundle in machine reorg ourselves.  */
  if (flag_var_tracking)
    flag_var_tracking_assignments = 0;
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
bool
e2k_expand_move (machine_mode mode, rtx *operands)
{
  rtx dst = operands[0], src = operands[1];

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

  m->wbase = (maxr + 2) / 2;
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
	      m->wsz, e2k_dbl ? 1 : 0, m->wbase);
  else
    snprintf (buf, sizeof buf, "setwd\twsz = %d, nfx = 1, dbl = %d",
	      m->wsz, e2k_dbl ? 1 : 0);
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

static void
e2k_print_operand (FILE *f, rtx x, int code)
{
  switch (code)
    {
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
  return code == '#' || code == '<' || code == '>';
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
}

/* Data speculation labels (see e2k_output_spec_load).  */
static int e2k_dam_labelno;
static vec<int> e2k_dam_pending;	/* labels to print after the bundle */
static vec<int> e2k_dam_stubs;		/* stubs to print at the end */

static void
e2k_dam_print_pending (FILE *f)
{
  for (int n : e2k_dam_pending)
    fprintf (f, ".LDAMB%d:\n", n);
  e2k_dam_pending.truncate (0);
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
e2k_asm_output_opcode (FILE *, const char *code)
{
  return code;
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
e2k_ldlock_p (const_rtx x)
{
  return GET_CODE (x) == UNSPEC && XINT (x, 1) == UNSPEC_LDLOCK;
}

/* Only after reload, in the EBB scheduler of machine reorg, and only
   data speculation: a semi-speculative load needs no check at all, and
   control speculation is a separate step.  */
static void
e2k_set_sched_flags (spec_info_t spec_info)
{
  unsigned int *flags = &current_sched_info->flags;
  if (e2k_dam && optimize > 0 && reload_completed && (*flags & SCHED_EBB))
    {
      spec_info->mask = BEGIN_DATA;
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
  if (GET_CODE (pat) != SET)
    return false;
  *dest = SET_DEST (pat);
  *src = SET_SRC (pat);
  if (e2k_ldlock_p (*src))
    *src = XVECEXP (*src, 0, 0);
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
  if (e2k_ldlock_p (SET_SRC (PATTERN (insn))))
    return 0;
  /* A failed check reloads from the address; it must still be there.  */
  if (reg_overlap_mentioned_p (dest, src))
    return -1;
  /* Nor speculate a load whose address the scheduler may rewrite to move
     it past an increment of its base: the check is a copy of the load,
     and the dependences of the rewrite don't cover it (an assertion in
     schedule_insn, gcc.c-torture/execute/920302-1.c).  */
  sd_iterator_def sd_it;
  dep_t dep;
  FOR_EACH_DEP (insn, SD_LIST_BACK | SD_LIST_FORW | SD_LIST_RES_BACK, sd_it, dep)
    if (DEP_REPLACE (dep) != NULL)
      return -1;
  machine_mode mode = GET_MODE (dest);
  *new_pat = gen_rtx_SET (copy_rtx (dest),
			  gen_rtx_UNSPEC (mode, gen_rtvec (1, copy_rtx (src)),
					  UNSPEC_LDLOCK));
  return 1;
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
  rtx pat = PATTERN (insn);
  return (GET_CODE (pat) == SET && e2k_ldlock_p (SET_SRC (pat))
	  ? BEGIN_DATA : 0);
}

static bool
e2k_skip_rtx_p (const_rtx x)
{
  return e2k_ldlock_p (x);
}

/* Counted loops on %lsr (see the "Counted loops" section of e2k.md).  */

/* Only innermost loops: %lsr is one register.  Its counter has 32 bits
   (v3), so the iteration count must be known to fit; lcc strip-mines
   longer loops into chunks, which the port doesn't do yet.  */
static bool
e2k_can_use_doloop_p (const widest_int &, const widest_int &iterations_max,
		      unsigned int loop_depth, bool entered_at_top)
{
  return (loop_depth == 1 && entered_at_top
	  && wi::ne_p (iterations_max, 0)
	  && wi::leu_p (iterations_max, 0xffffffffU));
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
  if (!JUMP_P (insn) || recog_memoized (insn) != CODE_FOR_e2k_doloop_end)
    return NULL_RTX;
  rtx reg = SET_DEST (XVECEXP (PATTERN (insn), 0, 1));
  return REG_P (reg) ? reg : NULL_RTX;
}

/* vlc: the count is valid (spec/isa/loops.md, %lsr bit 37).  */
#define E2K_LSR_VLC (HOST_WIDE_INT_1 << 37)

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

  /* Before the loop: %lsr = count | vlc, at least 4 cycles ahead, and
     the CTPR.  The iteration register is dead once the loop doesn't
     count it down.  */
  edge e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, loop->incoming)
    {
      start_sequence ();
      emit_insn (gen_iordi3 (loop->iter_reg, loop->iter_reg,
			     gen_int_mode (E2K_LSR_VLC, DImode)));
      emit_insn (gen_e2k_rwd_lsr (loop->iter_reg));
      rtx_insn *disp = emit_insn (gen_e2k_disp_label (ctpr,
						      loop->start_label));
      add_reg_note (disp, REG_LABEL_OPERAND, loop->start_label);
      LABEL_NUSES (loop->start_label)++;
      emit_insn (gen_e2k_lsr_wait ());
      rtx_insn *seq = end_sequence ();
      insert_insn_on_edge (seq, e);
    }

  rtx_insn *jump
    = emit_jump_insn_before (gen_e2k_hwloop_end (ctpr, loop->start_label),
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

static void
e2k_reorg (void)
{
  compute_bb_for_insn ();
  e2k_bundling = false;

  if (optimize)
    {
      reorg_loops (false, &e2k_doloop_hooks);
      commit_edge_insertions ();
    }

  if (optimize && e2k_loop_ct)
    e2k_prepare_loop_branches ();

  if (optimize && flag_schedule_insns_after_reload && e2k_bundle)
    {
      split_all_insns ();
      e2k_sched_init_global (NULL, 0, 0);
      timevar_push (TV_SCHED2);
      schedule_ebbs ();
      timevar_pop (TV_SCHED2);
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
#undef TARGET_SCHED_SKIP_RTX_P
#define TARGET_SCHED_SKIP_RTX_P e2k_skip_rtx_p
#undef TARGET_CAN_USE_DOLOOP_P
#define TARGET_CAN_USE_DOLOOP_P e2k_can_use_doloop_p
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
