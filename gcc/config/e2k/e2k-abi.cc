/* The ABI for the Elbrus (E2K) port (spec/abi): PIC and TLS
   addresses, argument passing and results, the frame, prologue and
   epilogue (setwd, getsp, the window's size), calls, inline asm operands,
   atomics' memory references, builtins and nonlocal gotos.
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

void
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
rtx
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
rtx
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

rtx
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

/* N_NAMED is expand_call's count of named arguments, which takes in
   GCC's hidden result pointer (slot 0) when a C++ result that is not
   trivially copyable has one (e2k_hidden_sret_p): the type's list
   doesn't, and the last named argument, which a variadic call also
   stores, was then the one before it.  */
void
e2k_init_cumulative_args (CUMULATIVE_ARGS *cum, tree fntype, rtx, tree,
			  int n_named, bool incoming)
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
	cum->nnamed = MAX (n_named, list_length (TYPE_ARG_TYPES (fntype)));
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

rtx
e2k_function_arg (cumulative_args_t cum, const function_arg_info &arg)
{
  return e2k_function_arg_1 (cum, arg, false);
}

rtx
e2k_function_incoming_arg (cumulative_args_t cum,
			   const function_arg_info &arg)
{
  return e2k_function_arg_1 (cum, arg, true);
}

void
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

unsigned int
e2k_function_arg_boundary (machine_mode mode, const_tree type)
{
  HOST_WIDE_INT size = type ? int_size_in_bytes (type)
			    : GET_MODE_SIZE (mode);
  return size > 8 ? 128 : PARM_BOUNDARY;
}

bool
e2k_strict_argument_naming (cumulative_args_t)
{
  return true;
}

/* Callers extend narrow integer arguments and results to 64 bits.  */
machine_mode
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

bool
e2k_return_in_memory (const_tree type, const_tree)
{
  HOST_WIDE_INT size = int_size_in_bytes (type);
  return size < 0 || size > 64;
}

rtx
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

rtx
e2k_libcall_value (machine_mode mode, const_rtx)
{
  return gen_rtx_REG (mode, B0_REGNUM);
}

bool
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
void
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
rtx
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

/* Whether something in the function takes %ctpr3 before the return:
   an asm that clobbers it ("ctpr3", or a system call's clobbers) or
   that makes a call, which empties every CTPR.  A return prepared in
   the prologue would then be dead at the asm, and deleted.  */
static bool
e2k_ctpr3_taken_p (void)
{
  rtx ctpr3 = gen_rtx_REG (DImode, CTPR3_REGNUM);
  for (rtx_insn *insn = get_topmost_sequence ()->first; insn;
       insn = NEXT_INSN (insn))
    if (INSN_P (insn)
	&& (e2k_asm_call_p (insn) || reg_set_p (ctpr3, insn)))
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
		  && !crtl->calls_eh_return && !cfun->has_nonlocal_label
		  && !e2k_ctpr3_taken_p ());

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
void
e2k_compute_window (void)
{
  machine_function *m = cfun->machine;
  if (m->window_done)
    return;

  int maxr = -1;
  bool use_b = false, calls = false, asm_call = false;
  for (rtx_insn *insn = get_insns (); insn; insn = NEXT_INSN (insn))
    {
      if (!INSN_P (insn))
	continue;
      if (CALL_P (insn))
	use_b = calls = true;
      if (e2k_asm_call_p (insn))
	use_b = calls = asm_call = true;
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
  /* A system call (an asm that calls) needs wbs >= 4 for entries 3 and
     6, else SIGSEGV, also with the 4 pairs handed over (relcc2 findings
     A25; lcc's wbs there is 5, 4 at -O0).  */
  if (asm_call)
    top = MAX (top, 4);
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

/* Whether this function runs with setwd dbl, so that 32-bit
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

/* setwd's nfx: 0 in a function that operates on long double, as lcc
   (spec/abi/registers.md, "nfx"). The operations hold the value in an
   extended register from movif to movfi, and an "x" asm operand across
   the asm; with nfx = 1 a spill of the window, which a deep call or a
   signal at any point causes, loses the 16-bit part (relcc2 findings
   A26).  Not for moves: the PoC keeps long double in a register pair,
   which has no extended part (lcc too keeps nfx = 1 in a function that
   only passes one on).  Decided once, from the insns.  */
int
e2k_nfx (void)
{
  machine_function *m = cfun->machine;
  if (m->nfx_known)
    return m->nfx;
  m->nfx_known = true;
  m->nfx = 1;
  for (rtx_insn *insn = get_insns (); insn && m->nfx;
       insn = NEXT_INSN (insn))
    if (NONDEBUG_INSN_P (insn) && GET_CODE (PATTERN (insn)) != USE
	&& GET_CODE (PATTERN (insn)) != CLOBBER)
      {
	rtx set = single_set (insn);
	if (set && GET_MODE (SET_DEST (set)) == XFmode
	    && (REG_P (SET_SRC (set)) || MEM_P (SET_SRC (set))
		|| GET_CODE (SET_SRC (set)) == SUBREG
		|| CONST_DOUBLE_P (SET_SRC (set))))
	  continue;
	subrtx_iterator::array_type array;
	FOR_EACH_SUBRTX (iter, array, PATTERN (insn), ALL)
	  if (GET_MODE (*iter) == XFmode)
	    {
	      m->nfx = 0;
	      break;
	    }
      }
  return m->nfx;
}

const char *
e2k_output_setwd (void)
{
  static char buf[160];
  machine_function *m = cfun->machine;
  e2k_compute_window ();
  if (m->use_b)
    snprintf (buf, sizeof buf,
	      "setwd\twsz = %d, nfx = %d, dbl = %d\n\t"
	      "setbn\trsz = 3, rbs = %d, rcur = 0",
	      m->wsz, e2k_nfx (), e2k_dbl_p () ? 1 : 0, m->wbase);
  else
    snprintf (buf, sizeof buf, "setwd\twsz = %d, nfx = %d, dbl = %d",
	      m->wsz, e2k_nfx (), e2k_dbl_p () ? 1 : 0);
  return buf;
}

const char *
e2k_output_call (void)
{
  static char buf[64];
  snprintf (buf, sizeof buf, "call\t%%%%ctpr1, wbs = %d%%?",
	    e2k_window_base ());
  return buf;
}

bool
e2k_frame_pointer_required (void)
{
  return cfun->calls_alloca || cfun->has_nonlocal_label;
}

bool
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

/* The result of the last inline root (sqrt in MODE) emitted before the
   call being expanded, or NULL.  Looks through the enclosing sequences
   and back across blocks, a few hundred insns at most.  */
static rtx
e2k_last_root (machine_mode mode)
{
  int n = 0;
  for (sequence_stack *seq = get_current_sequence (); seq; seq = seq->next)
    for (rtx_insn *insn = seq->last; insn && n < 400;
	 insn = PREV_INSN (insn), n++)
      {
	if (CALL_P (insn))
	  return NULL_RTX;
	if (!NONJUMP_INSN_P (insn))
	  continue;
	rtx pat = PATTERN (insn);
	if (GET_CODE (pat) == PARALLEL)
	  pat = XVECEXP (pat, 0, 0);
	if (GET_CODE (pat) == SET && GET_CODE (SET_SRC (pat)) == SQRT
	    && GET_MODE (SET_SRC (pat)) == mode && REG_P (SET_DEST (pat)))
	  return SET_DEST (pat);
      }
  return NULL_RTX;
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

  /* sqrt's call for errno (tree-call-cdce, CDCE_UNCONDITIONAL_IFN) must
     come after the inline root: that raises invalid for a negative
     operand, and MCST's libm, whose FP code is speculative, traps where
     the flag isn't set yet (relcc2 findings A23).  Nothing else orders
     them (FP flags aren't in the RTL), and the call's guard is ready
     before fsqrttd: make the call read the root's result, copied to
     %b[1] (sqrt has one argument, in %b[0]).  A hard register, as
     CALL_INSN_FUNCTION_USAGE takes no pseudos.  */
  rtx root = NULL_RTX;
  tree decl = GET_CODE (addr) == SYMBOL_REF ? SYMBOL_REF_DECL (addr) : NULL_TREE;
  if (decl && TREE_CODE (decl) == FUNCTION_DECL
      && fndecl_built_in_p (decl, BUILT_IN_NORMAL))
    switch (DECL_FUNCTION_CODE (decl))
      {
      case BUILT_IN_SQRT:
	root = e2k_last_root (DFmode);
	break;
      case BUILT_IN_SQRTF:
	root = e2k_last_root (SFmode);
	break;
      default:
	break;
      }

  rtx dep = NULL_RTX;
  if (root)
    {
      dep = gen_rtx_REG (GET_MODE (root), B0_REGNUM + 1);
      emit_move_insn (dep, root);
    }

  rtx target = gen_rtx_MEM (DImode, gen_rtx_REG (DImode, CTPR1_REGNUM));
  rtx call = gen_rtx_CALL (VOIDmode, target, argsize);
  if (retval)
    call = gen_rtx_SET (retval, call);
  rtx_insn *ci = emit_call_insn (call);
  if (dep)
    use_reg (&CALL_INSN_FUNCTION_USAGE (ci), dep);

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

bool
e2k_function_ok_for_sibcall (tree, tree)
{
  return false;
}

/* MCST's gdb has no DWARF CFI unwinder: it walks the chain stack, and
   its "frame base" for DW_OP_call_frame_cfa is an offset in the
   procedure stack, not a data address.  So no .debug_frame, and
   DW_AT_frame_base becomes a register expression built from our CFI
   (%r8 + size after getsp, %r9 with a frame pointer), as lcc's is.  */
enum unwind_info_type
e2k_debug_unwind_info (void)
{
  return UI_NONE;
}

/* ------------------------------------------------------------------ */
/* Inline assembly                                                     */
/* ------------------------------------------------------------------ */

/* Whether INSN is an asm that makes a call, as lcc treats one (spec/abi/
   source-compat.md, "Clobber names" and "%#"): it clobbers one of
   %b[0..7] (lcc's "b[N]" clobbers, or "call", which e2k_md_asm_adjust
   turns into a call's clobbers) or its template has %#, the window
   base for a call.  */
bool
e2k_asm_call_p (rtx_insn *insn)
{
  if (!INSN_P (insn))
    return false;
  rtx pat = PATTERN (insn);
  rtx body = GET_CODE (pat) == PARALLEL ? XVECEXP (pat, 0, 0) : pat;
  if (GET_CODE (body) == SET)
    body = SET_SRC (body);
  if (GET_CODE (body) != ASM_OPERANDS)
    return false;
  for (const char *p = ASM_OPERANDS_TEMPLATE (body); *p; p++)
    if (p[0] == '%' && p[1] == '%')
      p++;
    else if (p[0] == '%' && p[1] == '#')
      return true;
  if (GET_CODE (pat) == PARALLEL)
    for (int i = 0; i < XVECLEN (pat, 0); i++)
      {
	rtx x = XVECEXP (pat, 0, i);
	if (GET_CODE (x) == CLOBBER && REG_P (XEXP (x, 0))
	    && B_REGNO_P (REGNO (XEXP (x, 0))))
	  return true;
      }
  return false;
}

/* ASM_CLOBBER_MEMORY_P: whether clobber NAME makes an asm a call, so
   that it also clobbers memory: "call" or one of "b[0]"-"b[7]", with or
   without a leading %.  */
bool
e2k_asm_clobber_memory_p (const char *name)
{
  if (name[0] == '%')
    name++;
  return (strcmp (name, "call") == 0
	  || (name[0] == 'b' && name[1] == '[' && name[2] >= '0'
	      && name[2] <= '7' && name[3] == ']' && name[4] == 0));
}

/* lcc's "call" clobber and its "b[0]"-"b[7]" make an asm a call (spec/
   abi/source-compat.md, "Clobber names"): glibc's system calls list
   "call" and "memory", the kernel's uapi macros the CTPRs and
   %b[0..7], and both enter the kernel, which returns with %g16-%g31
   emptied (kernel-interface.md, "System calls").  Such an asm clobbers
   what a call does, and memory, as lcc assumes; not the registers its
   operands are in (a "register asm" variable may name one of
   %b[0..7]).  "call" arrives as a clobber of the argument pointer
   (ADDITIONAL_REGISTER_NAMES), which is dropped.  */
static void
e2k_asm_call_clobbers (vec<rtx> &outputs, vec<rtx> &inputs,
		       vec<rtx> &clobbers, HARD_REG_SET &clobbered_regs)
{
  bool call = TEST_HARD_REG_BIT (clobbered_regs, AP_REGNUM);
  bool bclob = false;
  for (int k = 0; k < 8; k++)
    bclob |= TEST_HARD_REG_BIT (clobbered_regs, B0_REGNUM + k);
  if (call)
    {
      CLEAR_HARD_REG_BIT (clobbered_regs, AP_REGNUM);
      for (unsigned i = 0; i < clobbers.length (); i++)
	if (REG_P (clobbers[i]) && REGNO (clobbers[i]) == AP_REGNUM)
	  {
	    clobbers.ordered_remove (i);
	    break;
	  }
    }
  if (!call && !bclob)
    return;

  HARD_REG_SET ops;
  CLEAR_HARD_REG_SET (ops);
  for (rtx x : outputs)
    if (REG_P (x) && HARD_REGISTER_P (x))
      add_to_hard_reg_set (&ops, GET_MODE (x), REGNO (x));
  for (rtx x : inputs)
    if (REG_P (x) && HARD_REGISTER_P (x))
      add_to_hard_reg_set (&ops, GET_MODE (x), REGNO (x));
  for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    if (((TEST_HARD_REG_BIT (regs_invalidated_by_call, r) && !fixed_regs[r])
	 || CTPR_REGNO_P (r))
	&& !TEST_HARD_REG_BIT (clobbered_regs, r)
	&& !TEST_HARD_REG_BIT (ops, r))
      {
	SET_HARD_REG_BIT (clobbered_regs, r);
	clobbers.safe_push (gen_rtx_REG (reg_raw_mode[r], r));
      }
  for (rtx x : clobbers)
    if (MEM_P (x))
      return;
  clobbers.safe_push (gen_rtx_MEM (BLKmode, gen_rtx_SCRATCH (VOIDmode)));
}

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
rtx_insn *
e2k_md_asm_adjust (vec<rtx> &outputs, vec<rtx> &inputs,
		   vec<machine_mode> &input_modes,
		   vec<const char *> &constraints, vec<rtx> &,
		   vec<rtx> &clobbers, HARD_REG_SET &clobbered_regs,
		   location_t loc)
{
  e2k_asm_call_clobbers (outputs, inputs, clobbers, clobbered_regs);

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

static void e2k_init_fp_state_builtins (void);

void
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

tree
e2k_builtin_decl (unsigned code, bool)
{
  return code < E2K_BUILTIN_MAX ? e2k_builtins[code] : error_mark_node;
}

rtx
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
void
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

#include "gt-e2k-abi.h"
