/* Prepared control transfers for the Elbrus (E2K) port
   (spec/isa/control-transfer.md): a disp into a CTPR early enough before
   each branch and loop back edge, CTPRs shared by branches to one target,
   prepares moved up into earlier blocks.
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

void
e2k_prepare_loop_branches (void)
{
  loop_optimizer_init (AVOID_CFG_MODIFICATIONS);
  bool changed = false;

  for (auto loop : loops_list (cfun, LI_ONLY_INNERMOST))
    {
      basic_block header = loop->header;
      rtx label = block_label (header);

      /* Pick a CTPR nothing in the loop touches; calls clobber them all.
	 Not %ctpr2 around a hardware loop, whose array prefetch program
	 e2k_modsched loads there: an outer loop whose back edge goes to
	 the inner one's header is one loop to GCC (NPB FT's cffts2, SP's
	 x_solve: 9 loops without array prefetch), and lcc keeps %ctpr2
	 free there too.  */
      bool has_call = false, uses[3] = { false, false, false };
      bool hwloop = false;
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
	      if (JUMP_P (insn)
		  && (recog_memoized (insn) == CODE_FOR_e2k_hwloop_end
		      || recog_memoized (insn) == CODE_FOR_e2k_hwloop_end_wide))
		hwloop = true;
	      for (int k = 0; k < 3; k++)
		if (reg_mentioned_p (gen_rtx_REG (DImode, CTPR1_REGNUM + k),
				     PATTERN (insn)))
		  uses[k] = true;
	    }
	}
      free (body);
      if (hwloop && e2k_loop_ctpr2_free)
	uses[1] = true;
      int k = (!uses[1] && !e2k_ctpr_reserved[1] ? 1
	       : !uses[0] && !e2k_ctpr_reserved[0] ? 0 : -1);
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
void
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
	  || (after_ms && (bb->flags & BB_DISABLE_SCHEDULE))
	  || (e2k_ms_flag (jump) & E2K_MS_IBRANCH))
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
	  if (!bitmap_bit_p (live, CTPR1_REGNUM + c) && !e2k_ctpr_reserved[c])
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
void
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
void
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

void
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
	  if ((c == 2 && cfun->machine->early_ret)
	      || (c != kn && e2k_ctpr_reserved[c]))
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

/* Where INSN, a call, keeps its CTPR (the address of its MEM).  */
static rtx *
e2k_call_ctpr_loc (rtx_insn *insn)
{
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) == COND_EXEC)
    pat = COND_EXEC_CODE (pat);
  if (GET_CODE (pat) == SET)
    pat = SET_SRC (pat);
  if (GET_CODE (pat) != CALL || !MEM_P (XEXP (pat, 0)))
    return NULL;
  rtx *loc = &XEXP (XEXP (pat, 0), 0);
  return REG_P (*loc) && CTPR_REGNO_P (REGNO (*loc)) ? loc : NULL;
}

/* Whether something after INSN in BB reads CTPR K before it is set
   again, or K is live out of BB.  */
static bool
e2k_ctpr_read_after_p (basic_block bb, rtx_insn *insn, rtx k)
{
  for (rtx_insn *i = NEXT_INSN (insn); i && i != NEXT_INSN (BB_END (bb));
       i = NEXT_INSN (i))
    {
      if (!NONDEBUG_INSN_P (i))
	continue;
      if (reg_referenced_p (k, PATTERN (i))
	  || (CALL_P (i) && e2k_call_ctpr_loc (i)
	      && rtx_equal_p (*e2k_call_ctpr_loc (i), k)))
	return true;
      if (reg_set_p (k, i) && GET_CODE (PATTERN (i)) != COND_EXEC)
	return false;
    }
  return bitmap_bit_p (df_get_live_out (bb), REGNO (k));
}

/* The disp e2k_expand_call put before the first call of BB, when nothing
   between them touches its CTPR: the disp, and in *CALL the call.  */
static rtx_insn *
e2k_call_prep_pair (basic_block bb, rtx_insn **call)
{
  rtx_insn *c = NULL, *insn;
  FOR_BB_INSNS (bb, insn)
    if (CALL_P (insn))
      {
	c = insn;
	break;
      }
  rtx *loc = c ? e2k_call_ctpr_loc (c) : NULL;
  if (!loc)
    return NULL;
  for (rtx_insn *i = PREV_INSN (c); i && i != PREV_INSN (BB_HEAD (bb));
       i = PREV_INSN (i))
    {
      if (!NONDEBUG_INSN_P (i))
	continue;
      if (recog_memoized (i) == CODE_FOR_e2k_disp
	  && GET_CODE (PATTERN (i)) == SET
	  && rtx_equal_p (SET_DEST (PATTERN (i)), *loc))
	{
	  *call = c;
	  return i;
	}
      if (e2k_touches_ctpr_p (i, *loc))
	return NULL;
    }
  return NULL;
}

/* A call issues no earlier than 5 cycles after its disp, which
   e2k_expand_call puts in the call's block, and the scheduler can move
   no further up than the top of the extended block, or the previous
   call (which empties the CTPRs).  For the first call of a block whose
   other work there takes fewer than 5 cycles, the disp goes up into the
   extended block's predecessors, as e2k_hoist_prepares does for a jump's
   (lcc prepares calls in earlier blocks in the same way), in a CTPR
   that nothing on the way uses, and the call reads that one.  */
void
e2k_hoist_call_prepares (void)
{
  df_analyze ();
  dfa_start ();
  int n = 0;
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *call, *d;
      if ((bb->flags & BB_DISABLE_SCHEDULE)
	  || !(d = e2k_call_prep_pair (bb, &call)))
	continue;
      basic_block h = e2k_ebb_head (bb);
      if ((h->flags & BB_DISABLE_SCHEDULE) || !LABEL_P (BB_HEAD (h))
	  || e2k_jump_cycle (h, call, d) >= 5)
	continue;
      rtx sym = XVECEXP (SET_SRC (PATTERN (d)), 0, 0);
      rtx k = SET_DEST (PATTERN (d));
      unsigned kn = REGNO (k) - CTPR1_REGNUM;
      for (unsigned t = 0; t < 3; t++)
	{
	  unsigned c = (kn + t) % 3;
	  rtx cr = gen_rtx_REG (DImode, CTPR1_REGNUM + c);
	  if ((c == 2 && cfun->machine->early_ret)
	      || (c != kn && e2k_ctpr_reserved[c]))
	    continue;
	  if (!e2k_ctpr_clear_p (h, call, d, cr))
	    continue;
	  /* Another CTPR only if nothing else reads the disp's: if-conversion
	     leaves one disp for two calls of one function under opposite
	     predicates, and a predicated call doesn't empty the CTPRs to
	     dataflow (the second of those then went through an empty
	     %ctpr1: SIGILL in SQLite's vdbeColumnFromOverflow).  */
	  if (c != kn && e2k_ctpr_read_after_p (bb, call, k))
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
	  if (c != kn
	      && !validate_change (call, e2k_call_ctpr_loc (call), cr, 0))
	    continue;
	  for (basic_block p : ps)
	    {
	      rtx_insn *at = e2k_ctpr_quiet_from (p, cr);
	      rtx pat = gen_e2k_disp (cr, copy_rtx (sym));
	      rtx_insn *x = (at ? emit_insn_before (pat, at)
			     : emit_insn_after (pat, BB_END (p)));
	      INSN_LOCATION (x) = INSN_LOCATION (d);
	    }
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_hoist_call_prepares: disp %d of bb %d "
		     "into %d predecessor(s) of bb %d, %%ctpr%u\n",
		     INSN_UID (d), bb->index, ps.length (), h->index, c + 1);
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
