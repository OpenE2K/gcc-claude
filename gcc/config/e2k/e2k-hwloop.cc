/* Counted loops on %lsr for the Elbrus (E2K) port
   (spec/isa/loops.md): which loops the doloop pass converts, the
   unrolling of loops the pipeliner takes, setting up the count, and
   loops whose count register allocation spilled.
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
static bool e2k_fold_vlc (basic_block, rtx);

/* Whether INSN writes a hardware loop's count: rwd %lsr, or on v5+ also
   %lsr1 (e2k_rwd_lsr_wide).  */
bool
e2k_rwd_lsr_p (rtx_insn *insn)
{
  int code = recog_memoized (insn);
  return code == CODE_FOR_e2k_rwd_lsr || code == CODE_FOR_e2k_rwd_lsr_wide;
}

/* Only innermost loops: %lsr is one register.  Its counter has 32 bits
   (v3); a loop whose count may not fit (iterations_max 0: unknown) is
   strip-mined (e2k_doloop_end_wide), and on v5+ gets the count in %lsr1
   instead (e2k_rwd_lsr_wide).  */
bool
e2k_can_use_doloop_p (const widest_int &iterations,
		      const widest_int &iterations_max,
		      unsigned int loop_depth, bool entered_at_top)
{
  e2k_doloop_wide = (e2k_arch < 5
		     && (wi::eq_p (iterations_max, 0)
			 || !wi::leu_p (iterations_max, 0xffffffffU)));
  e2k_doloop_iters = -1;
  if (wi::ne_p (iterations, 0) && wi::fits_shwi_p (iterations))
    e2k_doloop_iters = iterations.to_shwi ();
  else if (wi::ne_p (iterations_max, 0)
	   && wi::les_p (iterations_max, HOST_WIDE_INT_MAX / 2))
    e2k_doloop_iters = -2 - iterations_max.to_shwi ();
  return loop_depth == 1 && entered_at_top;
}

/* The most iterations of the hardware loop that JUMP ends, or -1.  */
HOST_WIDE_INT
e2k_loop_max_iters (rtx_insn *jump)
{
  HOST_WIDE_INT *p = e2k_loop_iters ? e2k_loop_iters->get (INSN_UID (jump))
		     : NULL;
  return !p ? -1 : *p >= 0 ? *p : -2 - *p;
}

/* Its iterations if constant, or -1.  */
HOST_WIDE_INT
e2k_loop_exact_iters (rtx_insn *jump)
{
  HOST_WIDE_INT *p = e2k_loop_iters ? e2k_loop_iters->get (INSN_UID (jump))
		     : NULL;
  return p && *p >= 0 ? *p : -1;
}

/* Whether the vectorizer made the loop starting at LABEL
   (e2k_vect_made_p): operand 3 of the doloop_end patterns.  */
bool
e2k_doloop_vect_p (rtx label)
{
  if (!current_loops || !LABEL_P (label) || !BLOCK_FOR_INSN (label))
    return false;
  class loop *loop = BLOCK_FOR_INSN (label)->loop_father;
  if (!loop || loop == current_loops->tree_root || !e2k_vect_made_p (loop))
    return false;
  if (dump_file)
    fprintf (dump_file, "e2k: loop %d made by the vectorizer\n", loop->num);
  return true;
}

/* Whether the vectorizer made the hardware loop that JUMP ends.  */
bool
e2k_loop_vect_made_p (rtx_insn *jump)
{
  return e2k_loop_vect && e2k_loop_vect->contains (INSN_UID (jump));
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
  bool fp = false, store = false;
  rtx_insn *insn;
  FOR_BB_INSNS (bb, insn)
    if (NONDEBUG_INSN_P (insn))
      {
	rtx set = single_set (insn);
	if (!NONJUMP_INSN_P (insn) || !set || ++n > MAX_CONDITIONAL_EXECUTE
	    || side_effects_p (PATTERN (insn)))
	  return false;
	fp |= FLOAT_MODE_P (GET_MODE (SET_DEST (set)));
	store |= MEM_P (SET_DEST (set));
      }
  /* An FP arm as e2k_ifcvt_modify_tests takes it: with loads but no
     stores under -mifcvt-fp-loads, and after an FP compare only if it
     runs at least -mifcvt-fp-prob=N percent of the time.  */
  if (fp)
    {
      if (!e2k_ifcvt_fp_loads || store)
	return false;
      rtx jset = any_condjump_p (BB_END (p)) ? pc_set (BB_END (p)) : NULL_RTX;
      rtx cond = jset ? XEXP (SET_SRC (jset), 0) : NULL_RTX;
      if (!cond || !COMPARISON_P (cond))
	return false;
      if (FLOAT_MODE_P (GET_MODE (XEXP (cond, 0))))
	{
	  edge e = find_edge (p, bb);
	  int prob = (e && e->probability.initialized_p ()
		      ? e->probability.to_reg_br_prob_base () * 100
			/ REG_BR_PROB_BASE : 50);
	  if (e2k_ifcvt_fp_prob == 0 || prob < e2k_ifcvt_fp_prob)
	    return false;
	}
    }
  return n > 0;
}


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
unsigned
e2k_loop_unroll_adjust (unsigned nunroll, class loop *loop)
{
  if (!e2k_pipeline || loop->inner)
    return nunroll;
  basic_block *bbs = get_loop_body (loop);
  int full = 0;
  bool ok = true, nocall = true;
  auto_bitmap set, stepped, multi, derived;
  hash_map<int_hash<unsigned, -1U, -2U>, HOST_WIDE_INT> steps;
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
		  {
		    bitmap_set_bit (stepped, r);
		    steps.put (r, INTVAL (XEXP (src, 1)));
		  }
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
	    {
	      bitmap_set_bit (derived, REGNO (SET_DEST (pat)));
	      HOST_WIDE_INT *sp = steps.get (REGNO (st (a) ? a : b));
	      if (sp)
		steps.put (REGNO (SET_DEST (pat)), *sp);
	    }
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
  /* A load stepping a line or more an iteration (a column): an array
     prefetch area fetches a line every 2 cycles at most (spec/isa/
     apb.md, "Area size is the prefetch depth"), so a loop at II 1 waits
     on it; two copies, whose loads e2k_ms_apb_assign gives areas of
     their own, run twice as fast, as lcc unrolls them.  PolyBench's
     syrk 1.05 -> 0.66 s, cholesky's init_array 30% fewer cycles on the
     8C2; streams from memory, which share a line every 3.2 cycles
     whatever the areas, lose nothing.  */
  bool wide = false;
  if (e2k_apb_wide_unroll && nunroll >= 2)
    for (unsigned i = 0; i < loop->num_nodes && !wide; i++)
      {
	rtx_insn *insn;
	FOR_BB_INSNS (bbs[i], insn)
	  {
	    rtx sset = NONDEBUG_INSN_P (insn) ? single_set (insn) : NULL_RTX;
	    if (!sset || !MEM_P (SET_SRC (sset)))
	      continue;
	    rtx a = XEXP (SET_SRC (sset), 0);
	    if (GET_CODE (a) == PLUS)
	      a = XEXP (a, 0);
	    HOST_WIDE_INT *sp = REG_P (a) ? steps.get (REGNO (a)) : NULL;
	    if (sp && (*sp >= 64 || *sp <= -64))
	      wide = true;
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
  if (wide && full - merged <= 1 && ok && !rec)
    return 2;
  return full - merged <= 1 && (ok || one_load) && !rec ? 1 : nunroll;
}

/* A callee may run a loop of its own, which leaves %lsr finished.  */
const char *
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

/* Set while e2k_hwloop_unspill converts a loop whose count is in this
   stack slot: the way in loads it into the iteration register, which
   is free there but not in the loop.  */
static rtx e2k_hwloop_count_mem;

static bool
e2k_hwloop_opt (hwloop_info loop)
{
  if (loop->depth > 1 || loop->has_call || loop->has_asm
      || loop->iter_reg_used || loop->iter_reg_used_outside
      || loop->incoming == NULL || loop->start_label == NULL)
    return false;
  if (!GPR_REGNO_P (REGNO (loop->iter_reg)))
    return false;
  /* An inner loop e2k_hwloop_unspill made a hardware loop isn't one of
     hw-doloop's, so it doesn't count in DEPTH.  */
  {
    basic_block bb;
    unsigned i;
    FOR_EACH_VEC_ELT (loop->blocks, i, bb)
      if (JUMP_P (BB_END (bb))
	  && (recog_memoized (BB_END (bb)) == CODE_FOR_e2k_hwloop_end
	      || recog_memoized (BB_END (bb)) == CODE_FOR_e2k_hwloop_end_wide))
	return false;
  }

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
      if (!used && !e2k_ctpr_reserved[k])
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

  /* hw-doloop takes the blocks where the counter is live for the loop:
     with the register reused around the loop it takes in others,
     entered elsewhere than at the head, and only says so in
     incoming_dest (xz's main, once predicated calls joined the blocks
     around a loop: 7 entries, all redirected to the head).  */
  edge e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, loop->incoming)
    if (e->dest != loop->head)
      return false;

  /* Many ways in (a vectorized loop after its peeled, fully unrolled
     alignment prologue has eight) share one block, so that the setup
     below and a pipelined loop's prologue (e2k_modsched copies it onto
     each way in) are emitted once.  */
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

  /* A count that may not fit 32 bits, on v5+: %lsr1 (above).  */
  HOST_WIDE_INT niters = INTVAL (XVECEXP (XVECEXP (pat, 0, 2), 0, 1));
  bool lsr1 = (!wide && e2k_arch >= 5
	       && (niters == -1
		   || (niters >= 0 ? niters : -2 - niters) > 0xffffffffLL));

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
      if (e2k_hwloop_count_mem)
	emit_move_insn (lsr, copy_rtx (e2k_hwloop_count_mem));
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
      else if (lsr1)
	;
      else if (e2k_hwloop_count_mem || !e2k_fold_vlc (e->src, lsr))
	emit_insn (gen_iordi3 (lsr, lsr, gen_int_mode (E2K_LSR_VLC, DImode)));
      if (lsr1)
	emit_insn (gen_e2k_rwd_lsr_wide (lsr));
      else
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
  if (INTVAL (XVECEXP (XVECEXP (pat, 0, 2), 0, 2)))
    {
      if (!e2k_loop_vect)
	e2k_loop_vect = new hash_set<int_hash<int, 0, -1> >;
      e2k_loop_vect->add (INSN_UID (jump));
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

/* e2k_hwloop_unspill's second way: make the innermost loop BLOCKS
   (BODY as a bitmap), from HEAD to END in TAIL, whose count is in MEM,
   a hardware loop with e2k_hwloop_opt, the count loaded on the way in
   into a register dead there.  */
static bool
e2k_hwloop_unspill_direct (rtx_insn *end, basic_block head, basic_block tail,
			   const vec<basic_block> &blocks, bitmap body,
			   rtx mem)
{
  if (recog_memoized (end) != CODE_FOR_e2k_doloop_end
      || EDGE_COUNT (tail->succs) != 2)
    return false;
  for (basic_block b : blocks)
    if (b != tail && JUMP_P (BB_END (b))
	&& (recog_memoized (BB_END (b)) == CODE_FOR_e2k_doloop_end
	    || recog_memoized (BB_END (b)) == CODE_FOR_e2k_doloop_end_wide
	    || recog_memoized (BB_END (b)) == CODE_FOR_e2k_hwloop_end
	    || recog_memoized (BB_END (b)) == CODE_FOR_e2k_hwloop_end_wide))
      return false;
  bitmap live = df_get_live_in (head);
  unsigned reg = INVALID_REGNUM;
  for (int pass = 0; pass < 2 && reg == INVALID_REGNUM; pass++)
    for (unsigned r = 16; r < R0_REGNUM + 64 && reg == INVALID_REGNUM; r++)
      if (!fixed_regs[r] && !bitmap_bit_p (live, r)
	  && (pass || df_regs_ever_live_p (r)))
	reg = r;
  if (reg == INVALID_REGNUM)
    return false;
  hwloop_info_d info;
  memset (&info, 0, sizeof info);
  info.blocks.create (blocks.length ());
  for (basic_block b : blocks)
    info.blocks.quick_push (b);
  edge e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, head->preds)
    if (!bitmap_bit_p (body, e->src->index))
      vec_safe_push (info.incoming, e);
  info.head = head;
  info.tail = tail;
  info.successor = FALLTHRU_EDGE (tail)->dest;
  info.loop_end = end;
  info.last_insn = end;
  info.iter_reg = gen_rtx_REG (DImode, reg);
  info.start_label = as_a <rtx_insn *> (JUMP_LABEL (end));
  info.depth = 1;
  e2k_hwloop_count_mem = mem;
  bool ok = e2k_hwloop_opt (&info);
  e2k_hwloop_count_mem = NULL_RTX;
  info.blocks.release ();
  vec_free (info.incoming);
  if (ok)
    df_set_regs_ever_live (reg, true);
  if (ok && dump_file)
    fprintf (dump_file, ";; e2k_hwloop_unspill: loop end %d: a hardware "
	     "loop, its count loaded into %s\n", INSN_UID (end),
	     reg_names[reg]);
  return ok;
}

/* A loop end whose counter register allocation spilled (NPB LU's jacld
   on v3, whose loop wants every register) keeps e2k_doloop_end's
   memory alternative, which hw-doloop doesn't see: the loop counts in
   memory, with neither a hardware loop nor pipelining.  A hardware loop
   reads the count once, on the way in, so load it there into a
   register nothing in the loop touches or keeps live, and count that;
   if the loop then can't become a hardware loop, it counts in that
   register, which is still better.  As e2k_ms finds its free
   registers, one the function uses already comes first.  When the loop
   uses them all (jacld), an innermost loop becomes a hardware loop
   here, its count loaded into a register dead on the way in
   (e2k_hwloop_count_mem).  */
void
e2k_hwloop_unspill (void)
{
  bool changed = false;
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *end = BB_END (bb);
      if (!JUMP_P (end)
	  || (recog_memoized (end) != CODE_FOR_e2k_doloop_end
	      && recog_memoized (end) != CODE_FOR_e2k_doloop_end_wide))
	continue;
      rtx pat = PATTERN (end);
      rtx mem = SET_DEST (XVECEXP (pat, 0, 1));
      if (!MEM_P (mem) || !JUMP_LABEL (end) || !LABEL_P (JUMP_LABEL (end)))
	continue;
      basic_block head = BLOCK_FOR_INSN (JUMP_LABEL (end));
      if (!head)
	continue;
      /* The body: the blocks that reach BB without passing HEAD, and
	 nothing else enters it but at HEAD.  */
      auto_bitmap body;
      auto_vec<basic_block> blocks, work;
      bitmap_set_bit (body, head->index);
      blocks.safe_push (head);
      if (bitmap_set_bit (body, bb->index))
	{
	  blocks.safe_push (bb);
	  work.safe_push (bb);
	}
      bool bad = false;
      while (!work.is_empty () && !bad)
	{
	  basic_block b = work.pop ();
	  edge e;
	  edge_iterator ei;
	  FOR_EACH_EDGE (e, ei, b->preds)
	    if (e->src == ENTRY_BLOCK_PTR_FOR_FN (cfun))
	      bad = true;
	    else if (bitmap_set_bit (body, e->src->index))
	      {
		blocks.safe_push (e->src);
		work.safe_push (e->src);
	      }
	}
      HARD_REG_SET used;
      CLEAR_HARD_REG_SET (used);
      for (basic_block b : blocks)
	{
	  edge e;
	  edge_iterator ei;
	  if (b != head)
	    FOR_EACH_EDGE (e, ei, b->preds)
	      if (!bitmap_bit_p (body, e->src->index))
		bad = true;
	  bitmap_iterator bi;
	  unsigned r;
	  EXECUTE_IF_SET_IN_BITMAP (df_get_live_in (b), 0, r, bi)
	    if (r < FIRST_PSEUDO_REGISTER)
	      SET_HARD_REG_BIT (used, r);
	  rtx_insn *insn;
	  FOR_BB_INSNS (b, insn)
	    {
	      if (!NONDEBUG_INSN_P (insn))
		continue;
	      if (CALL_P (insn) || asm_noperands (PATTERN (insn)) >= 0
		  || GET_CODE (PATTERN (insn)) == ASM_INPUT)
		bad = true;
	      df_ref ref;
	      FOR_EACH_INSN_DEF (ref, insn)
		add_to_hard_reg_set (&used, GET_MODE (DF_REF_REG (ref)),
				     DF_REF_REGNO (ref));
	      FOR_EACH_INSN_USE (ref, insn)
		add_to_hard_reg_set (&used, GET_MODE (DF_REF_REG (ref)),
				     DF_REF_REGNO (ref));
	    }
	}
      /* The slot's address must hold on the way in.  */
      subrtx_iterator::array_type array;
      FOR_EACH_SUBRTX (iter, array, XEXP (mem, 0), NONCONST)
	if (REG_P (*iter)
	    && overlaps_hard_reg_set_p (used, GET_MODE (*iter), REGNO (*iter))
	    && REGNO (*iter) != SP_REGNUM && REGNO (*iter) != HFP_REGNUM)
	  {
	    rtx_insn *insn;
	    for (basic_block b : blocks)
	      FOR_BB_INSNS (b, insn)
		if (insn != end && NONDEBUG_INSN_P (insn)
		    && reg_set_p (*iter, insn))
		  bad = true;
	  }
      if (bad)
	{
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_hwloop_unspill: loop end %d: not a "
		     "simple loop\n", INSN_UID (end));
	  continue;
	}
      unsigned reg = INVALID_REGNUM;
      for (int pass = 0; pass < 2 && reg == INVALID_REGNUM; pass++)
	for (unsigned r = 16; r < R0_REGNUM + 64 && reg == INVALID_REGNUM; r++)
	  if (!fixed_regs[r] && !TEST_HARD_REG_BIT (used, r)
	      && (pass || df_regs_ever_live_p (r)))
	    reg = r;
      if (reg == INVALID_REGNUM)
	{
	  if (e2k_hwloop_unspill_direct (end, head, bb, blocks, body, mem))
	    changed = true;
	  else if (dump_file)
	    fprintf (dump_file, ";; e2k_hwloop_unspill: loop end %d: no "
		     "free register\n", INSN_UID (end));
	  continue;
	}
      rtx count = gen_rtx_REG (DImode, reg);
      rtx newpat = simplify_replace_rtx (copy_rtx (pat), mem, count);
      if (!validate_change (end, &PATTERN (end), newpat, false))
	{
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_hwloop_unspill: loop end %d: not "
		     "recognized\n", INSN_UID (end));
	  continue;
	}
      edge e;
      edge_iterator ei;
      FOR_EACH_EDGE (e, ei, head->preds)
	if (!bitmap_bit_p (body, e->src->index))
	  {
	    start_sequence ();
	    emit_move_insn (count, copy_rtx (mem));
	    insert_insn_on_edge (end_sequence (), e);
	  }
      df_set_regs_ever_live (reg, true);
      changed = true;
      if (dump_file)
	fprintf (dump_file, ";; e2k_hwloop_unspill: loop end %d counts in "
		 "%s\n", INSN_UID (end), reg_names[reg]);
    }
  if (changed)
    commit_edge_insertions ();
}

struct hw_doloop_hooks e2k_doloop_hooks =
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
vec<unsigned char> e2k_ms_flags;

/* Registers read after the loop by copies still waiting on the exit
   edge (e2k_ms_move_b), which dataflow doesn't see yet.  */
HARD_REG_SET e2k_ms_live_out_extra;

vec<e2k_ms_clock> e2k_ms_clocks;
