/* Small RTL passes for the Elbrus (E2K) port: copies in a loop's
   latch, zero extensions under setwd dbl = 1, extensions nothing reads
   the upper half of, and address height reduction.
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

rtl_opt_pass *
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

rtl_opt_pass *
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

rtl_opt_pass *
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

rtl_opt_pass *
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

rtl_opt_pass *
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
vec<int> e2k_spec_from;
