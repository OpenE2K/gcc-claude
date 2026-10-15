/* The machine-dependent reorg pass of the Elbrus (E2K) port
   (e2k_reorg), which runs the back end's last steps in order: control
   flow reshaping, the pipeliner (e2k-ms.cc), prepared transfers
   (e2k-branch.cc), speculation (e2k-spec.cc), the list scheduler
   (e2k-sched.cc) and bundling (e2k-bundle.cc); and the reshaping
   itself: hash chain tests merged, latches folded and tails duplicated,
   loop headers rotated, invariants and %lsr writes hoisted, conditional
   returns, dispatch blocks copied, loads hoisted above taken branches,
   jump blocks skipped.
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
      /* invert_jump inverted the note, which matches the swapped edges
	 only where they summed to one (not in code never run, where both
	 can be never: 7-Zip's GzHandler.cpp).  */
      if (rtx note = find_reg_note (jump, REG_BR_PROB, NULL_RTX))
	XINT (note, 0) = ex->probability.to_reg_br_prob_note ();
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
	if (e2k_rwd_lsr_p (insn))
	  rwd = insn;
	else if (recog_memoized (insn) == CODE_FOR_e2k_lsr_wait)
	  wait = true;
      }
  return wait ? rwd : NULL;
}

/* Loop invariants that the middle end sank back into a loop (bzip2's
   unRLE: "bs * 100000", which lim2 hoisted and sink2 put back after
   jump threading had made the loop irreducible to it), moved onto the
   loop's ways in: a single set that can't trap and reads no memory,
   whose sources nothing in the loop writes, whose register nothing else
   in the loop sets and neither the loop's top nor any place it leaves
   to reads before.  */
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
		 which the pipeliner looks for: before them there.  Not when
		 the rwd reads the register: a strip-mined loop computes its
		 %lsr value in the scratch of its loop end, which RA may give
		 the register this set fills inside the loop, and the set
		 would then overwrite that value (verify_insn_changes in a
		 native stage 2 got the address of a local in %lsr).  */
	      bool placed = true;
	      for (edge en : entries)
		if (rtx_insn *rwd = e2k_hoist_rwd (en))
		  if (!single_succ_p (en->src)
		      || reg_overlap_mentioned_p (d, PATTERN (rwd)))
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
      /* The return's prepare (a function that calls): %ctpr3 only, so
	 only where the other way has no use for it.  */
      if (dr == CTPR3_REGNUM)
	{
	  if (live)
	    {
	      end_sequence ();
	      return false;
	    }
	  emit_insn (set);
	  continue;
	}
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
    if (GET_CODE (PATTERN (x)) != COND_EXEC
	&& !reg_set_p (gen_rtx_REG (DImode, CTPR3_REGNUM), x))
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
	  && (cfun->machine->early_ret || cfun->machine->cond_ret_calls));
}

/* A return prepared on every way into a later prepare of it still holds
   there unless a call came between (a ct not taken, a conditional return
   too, leaves its CTPR as it was; spec/isa/control-transfer.md): drop
   the later one, which costs a return 6 more cycles.  lcc's early exits
   after a call share the prepare right after it.  */
static void
e2k_share_return_preps (void)
{
  rtx ctpr3 = gen_rtx_REG (DImode, CTPR3_REGNUM);
  auto step = [&] (rtx_insn *insn, bool held)
    {
      if (!NONDEBUG_INSN_P (insn))
	return held;
      if (recog_memoized (insn) == CODE_FOR_e2k_return_prep)
	return true;
      if (CALL_P (insn) || reg_set_p (ctpr3, insn))
	return false;
      return held;
    };
  auto_sbitmap out (last_basic_block_for_fn (cfun));
  bitmap_ones (out);
  int *rpo = XNEWVEC (int, n_basic_blocks_for_fn (cfun));
  int n = pre_and_rev_post_order_compute (NULL, rpo, false);
  auto held_in = [&] (basic_block bb)
    {
      edge e;
      edge_iterator ei;
      FOR_EACH_EDGE (e, ei, bb->preds)
	if (e->src == ENTRY_BLOCK_PTR_FOR_FN (cfun)
	    || !bitmap_bit_p (out, e->src->index))
	  return false;
      return true;
    };
  for (bool more = true; more; )
    {
      more = false;
      for (int i = 0; i < n; i++)
	{
	  basic_block bb = BASIC_BLOCK_FOR_FN (cfun, rpo[i]);
	  bool held = held_in (bb);
	  rtx_insn *insn;
	  FOR_BB_INSNS (bb, insn)
	    held = step (insn, held);
	  if (held != bitmap_bit_p (out, bb->index))
	    {
	      bitmap_set_bit (out, bb->index);
	      if (!held)
		bitmap_clear_bit (out, bb->index);
	      more = true;
	    }
	}
    }
  bool changed = false;
  for (int i = 0; i < n; i++)
    {
      basic_block bb = BASIC_BLOCK_FOR_FN (cfun, rpo[i]);
      bool held = held_in (bb);
      rtx_insn *insn, *next;
      FOR_BB_INSNS_SAFE (bb, insn, next)
	{
	  if (held && NONDEBUG_INSN_P (insn)
	      && recog_memoized (insn) == CODE_FOR_e2k_return_prep)
	    {
	      if (dump_file)
		fprintf (dump_file, ";; e2k_share_return_preps: insn %d "
			 "goes, the return is prepared\n", INSN_UID (insn));
	      delete_insn (insn);
	      changed = true;
	      continue;
	    }
	  held = step (insn, held);
	}
    }
  free (rpo);
  if (changed)
    df_analyze ();
}

static void
e2k_cond_returns (void)
{
  machine_function *m = cfun->machine;
  if ((!m->early_ret && !e2k_cond_returns_calls) || m->sret_mem)
    return;
  if (!m->early_ret)
    m->cond_ret_calls = true;
  /* %ctpr3 live to the end (EPILOGUE_USES), so that the conditional
     returns depend on its prepare.  In a function that calls, which
     prepares its returns after its calls, the return block's prepare
     comes along into each block that returns for it (a register set,
     which may run where %ctpr3 is dead on the other way), as lcc
     prepares a return right after the last call.  */
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
  if (changed && m->cond_ret_calls)
    e2k_share_return_preps ();
}

/* A small block ending in a computed jump that conditional branches go
   to: a copy for each, there on the branch's taken way, which
   e2k_hoist_taken_loads can then start in the branch's own block.  Lua's
   interpreter dispatches through one such block (vmfetch's "if (trap)"
   ends every handler, so GCC's duplicate_computed_gotos, which takes
   only unconditional jumps, left it shared): 205 handlers branch to it,
   and each instruction then waits after its branch for the next one's
   load, its opcode, the table load and movtd, about 22 cycles.  lcc
   loads the next opcode and its table entry in each handler,
   speculatively, before the branch (relcc2 findings P72).  */
static void
e2k_dup_dispatch (void)
{
  auto_vec<basic_block> ds;
  basic_block d;
  FOR_EACH_BB_FN (d, cfun)
    {
      rtx_insn *j = BB_END (d);
      if (!JUMP_P (j) || !computed_jump_p (j) || tablejump_p (j, NULL, NULL)
	  || (d->flags & BB_DISABLE_SCHEDULE) || EDGE_COUNT (d->preds) < 2)
	continue;
      int n = 0;
      bool ok = true;
      rtx_insn *x;
      FOR_BB_INSNS (d, x)
	if (NONDEBUG_INSN_P (x) && x != j)
	  {
	    if (!NONJUMP_INSN_P (x) || recog_memoized (x) < 0
		|| e2k_asm_insn_p (x) || volatile_insn_p (PATTERN (x))
		|| GET_CODE (PATTERN (x)) == USE
		|| GET_CODE (PATTERN (x)) == CLOBBER)
	      ok = false;
	    n++;
	  }
      if (ok && n > 0 && n <= 10)
	ds.safe_push (d);
    }
  int copies = 0;
  for (basic_block d : ds)
    {
      auto_vec<edge> es;
      edge e;
      edge_iterator ei;
      FOR_EACH_EDGE (e, ei, d->preds)
	if (!(e->flags & (EDGE_COMPLEX | EDGE_FALLTHRU))
	    && e->src != ENTRY_BLOCK_PTR_FOR_FN (cfun) && e->src != d
	    && !(e->src->flags & BB_DISABLE_SCHEDULE)
	    && any_condjump_p (BB_END (e->src))
	    && EDGE_COUNT (e->src->succs) == 2)
	  es.safe_push (e);
      /* D keeps one way in.  */
      if (es.length () == EDGE_COUNT (d->preds))
	es.pop ();
      for (edge e : es)
	{
	  if (copies >= 512)
	    break;
	  basic_block nb = split_edge (e);
	  /* NB falls into D: D's operations and its jump instead.  */
	  rtx_insn *x = BB_END (nb), *last = BB_END (d), *insn;
	  FOR_BB_INSNS (d, insn)
	    if (NONDEBUG_INSN_P (insn) && insn != last)
	      {
		x = emit_insn_after (copy_rtx (PATTERN (insn)), x);
		INSN_LOCATION (x) = INSN_LOCATION (insn);
		e2k_ms_set_flag (x, e2k_ms_flag (insn));
	      }
	  rtx_insn *cj = emit_jump_insn_after (copy_rtx (PATTERN (last)), x);
	  INSN_LOCATION (cj) = INSN_LOCATION (last);
	  if (recog_memoized (cj) < 0)
	    gcc_unreachable ();
	  emit_barrier_after (cj);
	  BB_END (nb) = cj;
	  for (rtx_insn *y = BB_HEAD (nb); y != NEXT_INSN (cj);
	       y = NEXT_INSN (y))
	    {
	      set_block_for_insn (y, nb);
	      if (INSN_P (y))
		df_insn_rescan (y);
	    }
	  remove_edge (single_succ_edge (nb));
	  edge s;
	  edge_iterator si;
	  FOR_EACH_EDGE (s, si, d->succs)
	    {
	      edge c = make_edge (nb, s->dest, s->flags);
	      c->probability = s->probability;
	    }
	  copies++;
	}
    }
  if (copies)
    {
      df_analyze ();
      if (dump_file)
	fprintf (dump_file, ";; e2k_dup_dispatch: %d copies\n", copies);
    }
}

/* A block every way into which ends in a conditional branch, one at
   least taken to it, starts with loads whose addresses are ready before
   the branches: run them above each, speculatively (",sm"), where the
   list scheduler can start them early.  sched-ebb speculates only along
   fall-throughs into a block with no other way in: Lua's luaH_getshortstr
   tests a node's key type and branches to load and compare its value,
   9 cycles a test on the 2C3 (a 5-cycle load after the branch) where
   lcc loads the value beside the type and takes 3.  A load moves when
   each branch goes to B at least a fifth of the time, its register is
   dead on each branch's other way and nothing before it
   in its block sets its address or reads or sets its register, and no
   store, call or volatile operation comes before it there.  With
   -mhoist-alu the operations with a speculative form among them move
   too (up to 8 in all), so that a load whose address they compute (an
   interpreter's next opcode, its table entry) can follow.  */
static void
e2k_hoist_taken_loads (void)
{
  df_analyze ();
  int n = 0;
  basic_block b;
  FOR_EACH_BB_FN (b, cfun)
    {
      if ((b->flags & BB_DISABLE_SCHEDULE) || EDGE_COUNT (b->preds) > 4)
	continue;
      /* Every way in a conditional branch, to B or past it into B, whose
	 other way doesn't need the loaded register; at least one taken
	 to B (a fall-through alone is sched-ebb's).  */
      auto_vec<rtx_insn *, 4> js;
      auto_vec<bitmap, 4> fls;
      edge e;
      edge_iterator ei;
      bool ok = true, taken = false, likely = true;
      FOR_EACH_EDGE (e, ei, b->preds)
	{
	  basic_block a = e->src;
	  /* Not along a branch rarely taken: the copies would run on the
	     other, usual way for nothing (CoreMark's list search, a load
	     for its "not found" arm at 11%: 0.4% slower).  Operations only
	     along a likely one (below).  */
	  if (!e->probability.initialized_p ()
	      || e->probability < profile_probability::unlikely ())
	    ok = false;
	  likely &= (e->probability.initialized_p ()
		     && e->probability >= profile_probability::likely ());
	  rtx_insn *j = BB_END (a);
	  if (a == b || a == ENTRY_BLOCK_PTR_FOR_FN (cfun) || !JUMP_P (j)
	      || !any_condjump_p (j) || EDGE_COUNT (a->succs) != 2
	      || (a->flags & BB_DISABLE_SCHEDULE)
	      || (e->flags & EDGE_COMPLEX)
	      || EDGE_SUCC (a, 0)->dest == EDGE_SUCC (a, 1)->dest)
	    {
	      ok = false;
	      break;
	    }
	  taken |= BRANCH_EDGE (a) == e;
	  edge other = BRANCH_EDGE (a) == e ? FALLTHRU_EDGE (a) : BRANCH_EDGE (a);
	  js.safe_push (j);
	  fls.safe_push (df_get_live_in (other->dest));
	}
      if (!ok || !taken || js.is_empty ())
	continue;
      HARD_REG_SET set, used, mdefs;
      CLEAR_HARD_REG_SET (set);
      CLEAR_HARD_REG_SET (used);
      CLEAR_HARD_REG_SET (mdefs);
      int moved = 0;
      bool loads = false;
      auto_vec<rtx_insn *, 8> mv;
      rtx_insn *x, *next;
      for (x = BB_HEAD (b); x && x != NEXT_INSN (BB_END (b)); x = next)
	{
	  next = NEXT_INSN (x);
	  if (!NONDEBUG_INSN_P (x))
	    continue;
	  rtx s = single_set (x);
	  rtx m = s ? SET_SRC (s) : NULL_RTX;
	  if (m && (GET_CODE (m) == ZERO_EXTEND || GET_CODE (m) == SIGN_EXTEND))
	    m = XEXP (m, 0);
	  bool load = (recog_memoized (x) >= 0
		       && get_attr_type (x) == TYPE_LOAD && s
		       && REG_P (SET_DEST (s)) && MEM_P (m)
		       && !volatile_refs_p (PATTERN (x))
		       && GET_CODE (PATTERN (x)) != COND_EXEC
		       && !find_reg_note (x, REG_EH_REGION, NULL_RTX));
	  /* And what feeds a later load from them (an index into a table,
	     as an interpreter's dispatch computes): operations with a
	     speculative form that read no memory.  One that reads what
	     another moved operation sets is a chain, which holds the branch
	     until it issues, on the other way too: only where every branch
	     to B is likely taken (Lua's "if (l_unlikely (trap))" before
	     each dispatch; CoreMark lost 1% with chains along any branch,
	     bzip2's compression 3.4% with no operation along them).  */
	  bool alu = (!load && e2k_hoist_alu_p && s
		      && REG_P (SET_DEST (s))
		      && e2k_spec_kind (x) == 1
		      && !volatile_refs_p (PATTERN (x))
		      && !find_reg_note (x, REG_EH_REGION, NULL_RTX));
	  if (alu)
	    {
	      subrtx_iterator::array_type array;
	      FOR_EACH_SUBRTX (iter, array, SET_SRC (s), NONCONST)
		if (MEM_P (*iter))
		  alu = false;
	    }
	  if (load || alu)
	    {
	      rtx d = SET_DEST (s);
	      unsigned r = REGNO (d);
	      bool can = moved < (e2k_hoist_alu_p ? 8 : 4)
			 && HARD_REGISTER_NUM_P (r)
			 && !TEST_HARD_REG_BIT (set, r)
			 && !TEST_HARD_REG_BIT (used, r)
			 && !reg_overlap_mentioned_p (d, SET_SRC (s));
	      for (unsigned k = 0; can && k < js.length (); k++)
		if (bitmap_bit_p (fls[k], r)
		    || reg_overlap_mentioned_p (d, PATTERN (js[k])))
		  can = false;
	      /* Its address: nothing before it in B sets a register of it.  */
	      subrtx_iterator::array_type array;
	      FOR_EACH_SUBRTX (iter, array, SET_SRC (s), NONCONST)
		if (REG_P (*iter)
		    && (overlaps_hard_reg_set_p (set, GET_MODE (*iter),
						 REGNO (*iter))
			|| (alu && !likely
			    && overlaps_hard_reg_set_p (mdefs, GET_MODE (*iter),
							REGNO (*iter)))))
		  can = false;
	      if (can)
		{
		  add_to_hard_reg_set (&mdefs, GET_MODE (d), r);
		  mv.safe_push (x);
		  loads |= load;
		  moved++;
		  continue;
		}
	    }
	  /* What later loads must not cross.  */
	  if (CALL_P (x) || JUMP_P (x) || volatile_insn_p (PATTERN (x))
	      || !s || MEM_P (SET_DEST (s)))
	    break;
	  /* What stays: nothing after it that moves may set what it reads
	     or read or set what it sets.  */
	  note_stores (x, record_hard_reg_sets, &set);
	  e2k_note_regs (PATTERN (x), &used);
	}
      /* Operations only where a load moves with them, and nothing out of
	 a block it would leave with only its jump: that block would cost a
	 transfer more than what it gave away (a copy or a load on one
	 branch's edge; lapi.c had 35 such blocks).  */
      if (!loads)
	continue;
      bool rest = false;
      FOR_BB_INSNS (b, x)
	if (NONDEBUG_INSN_P (x) && !JUMP_P (x) && !mv.contains (x)
	    && (recog_memoized (x) < 0 || get_attr_type (x) != TYPE_DISP))
	  rest = true;
      if (!rest && JUMP_P (BB_END (b)) && single_succ_p (b)
	  && single_succ (b) != EXIT_BLOCK_PTR_FOR_FN (cfun))
	continue;
      for (rtx_insn *y : mv)
	{
	  for (rtx_insn *j : js)
	    {
	      rtx_insn *c = emit_insn_before (copy_rtx (PATTERN (y)), j);
	      INSN_LOCATION (c) = INSN_LOCATION (y);
	      if (recog_memoized (c) < 0)
		gcc_unreachable ();
	      e2k_ms_set_flag (c, E2K_MS_SM);
	    }
	  /* B now reads Y's register from its predecessors: a later block
	     whose branches' other way is B must not set it there.  */
	  rtx d = SET_DEST (single_set (y));
	  bitmap_set_range (df_get_live_in (b), REGNO (d), REG_NREGS (d));
	  delete_insn (y);
	  n++;
	}
    }
  if (n)
    df_analyze ();
  if (dump_file && n)
    fprintf (dump_file, ";; e2k_hoist_taken_loads: %d operations\n", n);
}

/* A block of disps and a ct through a CTPR prepared before it, entered
   by one prepared branch: e2k_prepare_loop_branches puts a loop's disp on
   each way in, which splits a branch's taken edge into such a block, and
   e2k_hoist_prepares moves the block's own disp up into the branch's
   (Lua's luaH_getshortstr enters its chain walk so on every lookup).
   The branch can take that CTPR to the target itself, the disps going
   before it where their CTPRs are dead on its other way: one transfer
   instead of two.  */
static void
e2k_skip_jump_blocks (void)
{
  auto_vec<basic_block> dead;
  auto_bitmap gone;
  basic_block j;
  FOR_EACH_BB_FN (j, cfun)
    {
      rtx_insn *jj = BB_END (j);
      if (!JUMP_P (jj) || !single_succ_p (j) || !single_pred_p (j)
	  || (j->flags & BB_DISABLE_SCHEDULE))
	continue;
      rtx pat = PATTERN (jj);
      if (GET_CODE (pat) != PARALLEL || XVECLEN (pat, 0) != 2
	  || GET_CODE (XVECEXP (pat, 0, 0)) != SET
	  || SET_DEST (XVECEXP (pat, 0, 0)) != pc_rtx
	  || GET_CODE (SET_SRC (XVECEXP (pat, 0, 0))) != LABEL_REF
	  || GET_CODE (XVECEXP (pat, 0, 1)) != USE
	  || !REG_P (XEXP (XVECEXP (pat, 0, 1), 0)))
	continue;
      rtx ctx = XEXP (XVECEXP (pat, 0, 1), 0);
      edge e = single_pred_edge (j);
      basic_block p = e->src, t = single_succ (j);
      if (p == ENTRY_BLOCK_PTR_FOR_FN (cfun) || p == j || t == j
	  || t == EXIT_BLOCK_PTR_FOR_FN (cfun)
	  || (e->flags & (EDGE_FALLTHRU | EDGE_COMPLEX))
	  || (p->flags & BB_DISABLE_SCHEDULE) || bitmap_bit_p (gone, p->index))
	continue;
      /* J: disps of other CTPRs, then the jump.  */
      auto_vec<rtx_insn *, 3> disps;
      bool ok = true;
      rtx_insn *x;
      FOR_BB_INSNS (j, x)
	if (NONDEBUG_INSN_P (x) && x != jj)
	  {
	    int c = recog_memoized (x);
	    if ((c == CODE_FOR_e2k_disp_label || c == CODE_FOR_e2k_disp)
		&& REGNO (SET_DEST (PATTERN (x))) != REGNO (ctx))
	      disps.safe_push (x);
	    else
	      ok = false;
	  }
      /* P: a prepared branch to J through another CTPR, its disp in P.  */
      rtx_insn *pj = BB_END (p);
      rtx ppat = PATTERN (pj);
      if (!ok || !JUMP_P (pj) || JUMP_LABEL (pj) != BB_HEAD (j)
	  || !LABEL_P (BB_HEAD (j))
	  || GET_CODE (ppat) != PARALLEL || XVECLEN (ppat, 0) != 2
	  || GET_CODE (XVECEXP (ppat, 0, 1)) != USE
	  || !REG_P (XEXP (XVECEXP (ppat, 0, 1), 0))
	  || REGNO (XEXP (XVECEXP (ppat, 0, 1), 0)) == REGNO (ctx))
	continue;
      rtx cty = XEXP (XVECEXP (ppat, 0, 1), 0);
      rtx_insn *pd = NULL;
      for (x = PREV_INSN (pj); x && x != PREV_INSN (BB_HEAD (p));
	   x = PREV_INSN (x))
	if (NONDEBUG_INSN_P (x))
	  {
	    if (CALL_P (x) || reg_mentioned_p (ctx, PATTERN (x)))
	      break;
	    if (reg_set_p (cty, x))
	      {
		if (recog_memoized (x) == CODE_FOR_e2k_disp_label
		    && (label_ref_label (XVECEXP (SET_SRC (PATTERN (x)), 0, 0))
			== BB_HEAD (j)))
		  pd = x;
		break;
	      }
	  }
      if (!pd)
	continue;
      /* The disps run on P's other ways too.  */
      edge s;
      edge_iterator si;
      FOR_EACH_EDGE (s, si, p->succs)
	if (s != e)
	  for (rtx_insn *d : disps)
	    if (bitmap_bit_p (df_get_live_in (s->dest),
			      REGNO (SET_DEST (PATTERN (d)))))
	      ok = false;
      if (!ok)
	continue;
      rtx tl = block_label (t);
      for (rtx_insn *d : disps)
	{
	  rtx_insn *c = emit_insn_before (copy_rtx (PATTERN (d)), pj);
	  INSN_LOCATION (c) = INSN_LOCATION (d);
	  if (rtx note = find_reg_note (d, REG_LABEL_OPERAND, NULL_RTX))
	    {
	      add_reg_note (c, REG_LABEL_OPERAND, XEXP (note, 0));
	      LABEL_NUSES (XEXP (note, 0))++;
	    }
	  recog_memoized (c);
	}
      delete_insn (pd);
      if (!redirect_jump (as_a <rtx_jump_insn *> (pj), tl, 0))
	gcc_unreachable ();
      XEXP (XVECEXP (PATTERN (pj), 0, 1), 0) = ctx;
      INSN_CODE (pj) = -1;
      if (recog_memoized (pj) < 0)
	gcc_unreachable ();
      df_insn_rescan (pj);
      redirect_edge_succ_nodup (e, t);
      dead.safe_push (j);
      bitmap_set_bit (gone, j->index);
      if (dump_file)
	fprintf (dump_file, ";; e2k_skip_jump_blocks: bb %d -> bb %d past "
		 "bb %d\n", p->index, t->index, j->index);
    }
  for (basic_block d : dead)
    delete_basic_block (d);
  if (!dead.is_empty ())
    df_analyze ();
}

/* schedule_ebbs moves a debug insn with the operations around it, and
   one at the head of a block, after the block's note, depends on
   nothing before it (sched-deps.cc ties a debug insn to the insn just
   before it only when that is not a note): it can rise above the jump
   that enters its block, into the block before.  A statement marker
   then gave its line a breakpoint before the branch, and a bind gave
   its variable the value on the other path too (guality's pr55665.C: a
   breakpoint on "foo (p)" stopped before the branch to the static's
   initialization, and read it as 0).  x86 schedules within blocks, so
   GCC never sees it there.  Record each debug insn's block before
   scheduling; after it, put those that left their block back at its
   head, in order.  */
static vec<int> e2k_debug_bb;

static void
e2k_record_debug_blocks (void)
{
  e2k_debug_bb.truncate (0);
  if (!MAY_HAVE_DEBUG_INSNS)
    return;
  e2k_debug_bb.safe_grow_cleared (get_max_uid () + 1);
  basic_block bb;
  rtx_insn *insn;
  FOR_EACH_BB_FN (bb, cfun)
    FOR_BB_INSNS (bb, insn)
      if (DEBUG_INSN_P (insn))
	e2k_debug_bb[INSN_UID (insn)] = bb->index + 1;
}

static void
e2k_restore_debug_blocks (void)
{
  if (e2k_debug_bb.is_empty ())
    return;
  auto_vec<rtx_insn *> moved;
  for (rtx_insn *insn = get_insns (); insn; insn = NEXT_INSN (insn))
    {
      unsigned uid = INSN_UID (insn);
      if (!DEBUG_INSN_P (insn) || uid >= e2k_debug_bb.length ()
	  || !e2k_debug_bb[uid])
	continue;
      basic_block was = BASIC_BLOCK_FOR_FN (cfun, e2k_debug_bb[uid] - 1);
      if (was && BLOCK_FOR_INSN (insn) != was)
	moved.safe_push (insn);
    }
  hash_map<int_hash<int, -1, -2>, rtx_insn *> last;
  for (rtx_insn *insn : moved)
    {
      basic_block bb
	= BASIC_BLOCK_FOR_FN (cfun, e2k_debug_bb[INSN_UID (insn)] - 1);
      rtx_insn **l = last.get (bb->index);
      reorder_insns (insn, insn, l ? *l : bb_note (bb));
      last.put (bb->index, insn);
    }
  e2k_debug_bb.truncate (0);
}

void
e2k_reorg (void)
{
  e2k_note_depth ();
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
      if (e2k_loop_vect)
	e2k_loop_vect->empty ();
      if (e2k_hwloop_unspill_p)
	{
	  df_analyze ();
	  e2k_hwloop_unspill ();
	}
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
  if (optimize >= 2 && e2k_control_spec && e2k_dup_dispatch_p)
    e2k_dup_dispatch ();
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
      if (e2k_control_spec && e2k_hoist_taken_p)
	e2k_hoist_taken_loads ();
      if (e2k_prepare_br && e2k_skip_jumps_p)
	e2k_skip_jump_blocks ();
      e2k_sched_init_global (NULL, 0, 0);
      if (e2k_control_spec)
	e2k_spec_prepare ();
      e2k_record_debug_blocks ();
      timevar_push (TV_SCHED2);
      schedule_ebbs ();
      timevar_pop (TV_SCHED2);
      e2k_restore_debug_blocks ();
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
      e2k_bundle_var_notes ();
      e2k_bundle_stmt_notes ();
      e2k_bundle_scopes ();
      e2k_bundle_dup_blocks ();
    }
  df_finish_pass (false);
  e2k_unpred_cond.truncate (0);
}
