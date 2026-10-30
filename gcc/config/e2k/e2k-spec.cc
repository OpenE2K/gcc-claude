/* Speculation around list scheduling for the Elbrus (E2K) port:
   which operations may run above a branch, dependences the scheduler
   must add, loads run without if-conversion's predicate, ",sm" marks
   after scheduling, and pruning what would read a diagnostic value.
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

/* Whether INSN may run above a branch, and how: 1 with ",sm", 2 as it
   is, 0 not.  Not a volatile access: it would happen on a path where
   the program makes none (a volatile load beside the jump that skips
   it).  Nor an insn that may throw (-fnon-call-exceptions): it ends its
   block on an EH edge, its exception belongs where the program has it,
   and sched-ebb moves no such insn into a block that ends in a jump
   (advance_target_bb's assertion, sched-ebb.cc:699; g++.dg/opt/
   pr100254.C, g++.dg/ipa/pr80205.C: a vtable load).  */
int
e2k_spec_kind (rtx_insn *insn)
{
  if (!NONDEBUG_INSN_P (insn) || recog_memoized (insn) < 0
      || e2k_asm_insn_p (insn) || GET_CODE (PATTERN (insn)) == COND_EXEC
      || control_flow_insn_p (insn))
    return 0;
  switch (get_attr_type (insn))
    {
    case TYPE_ALU: case TYPE_ALU14: case TYPE_ALU0134: case TYPE_CMP:
    case TYPE_MUL:
    case TYPE_LOAD: case TYPE_PINT: case TYPE_PINT14: case TYPE_PMUL:
    case TYPE_PANY:
    /* The x86 flag operations and cctop: integer, no exceptions; gas
       takes ",sm" on them.  */
    case TYPE_FLAG: case TYPE_FLAGMUL: case TYPE_CCTOP:
      return volatile_refs_p (PATTERN (insn)) ? 0 : 1;
    /* A lock load prints its own ",sm".  */
    case TYPE_LDLOCK: case TYPE_DISP: case TYPE_RET: case TYPE_GHOST:
      return 2;
    default:
      return 0;
    }
}

void
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
bool
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

/* bap reads %ctpr2 5 cycles after its ldisp; an AAU write between them
   is a barrier, which takes over the ldisp's dependences and, being an
   AAU write after a disp, waits for nothing (e2k_adjust_cost), so the
   5 cycles went missing once the ldisp came first (lcc's order, which
   lets the writes fill them).  Make each bap depend on its ldisp again.  */
static void
e2k_bap_deps (rtx_insn *head, rtx_insn *tail)
{
  rtx ctpr2 = gen_rtx_REG (DImode, CTPR2_REGNUM);
  rtx_insn *ldisp = NULL;
  for (rtx_insn *insn = head; insn != NEXT_INSN (tail);
       insn = NEXT_INSN (insn))
    {
      if (!NONDEBUG_INSN_P (insn))
	continue;
      if (recog_memoized (insn) == CODE_FOR_e2k_bap)
	{
	  if (ldisp)
	    add_dependence (insn, ldisp, REG_DEP_TRUE);
	}
      else if (reg_set_p (ctpr2, insn))
	ldisp = recog_memoized (insn) == CODE_FOR_e2k_ldisp_apb ? insn : NULL;
    }
}

/* A read of the FP state (e2k_rrs) is volatile, so a later one is a
   barrier that takes over its register dependences: a reader of the
   first then waited for the second only (e2k_adjust_cost lets what
   doesn't read a result follow at once), and an operation 3 cycles
   after rrs %pfpfr stalled for its 11.  Make each reader of an rrs
   result depend on that rrs again.  */
static void
e2k_rrs_deps (rtx_insn *head, rtx_insn *tail)
{
  for (rtx_insn *insn = head; insn != NEXT_INSN (tail);
       insn = NEXT_INSN (insn))
    if (NONDEBUG_INSN_P (insn) && recog_memoized (insn) == CODE_FOR_e2k_rrs)
      {
	rtx d = SET_DEST (PATTERN (insn));
	for (rtx_insn *x = NEXT_INSN (insn); x != NEXT_INSN (tail);
	     x = NEXT_INSN (x))
	  {
	    if (!NONDEBUG_INSN_P (x))
	      continue;
	    if (reg_overlap_mentioned_p (d, PATTERN (x))
		&& !(single_set (x)
		     && rtx_equal_p (SET_DEST (single_set (x)), d)
		     && !reg_overlap_mentioned_p (d,
						  SET_SRC (single_set (x)))))
	      add_dependence (x, insn, REG_DEP_TRUE);
	    if (reg_set_p (d, x))
	      break;
	  }
      }
}

/* -Og: every operation of a source line depends on every operation of
   the line before it (e2k_og_stmt; e2k_adjust_cost gives the dependence
   a cycle), so the scheduler keeps the lines in order and apart, and a
   breakpoint on a line sees the lines before it done and none of its own
   operations run.  Operations without a line go with the line before.  */
static void
e2k_og_stmt_deps (rtx_insn *head, rtx_insn *tail)
{
  if (!optimize_debug)
    return;
  auto_vec<rtx_insn *> prev, cur;
  int line = 0;
  for (rtx_insn *insn = head; insn != NEXT_INSN (tail);
       insn = NEXT_INSN (insn))
    {
      if (!NONDEBUG_INSN_P (insn))
	continue;
      int l = e2k_og_stmt (insn);
      if (l && l != line)
	{
	  if (line)
	    {
	      prev.truncate (0);
	      prev.safe_splice (cur);
	      cur.truncate (0);
	    }
	  line = l;
	}
      for (rtx_insn *p : prev)
	add_dependence (insn, p, REG_DEP_ANTI);
      cur.safe_push (insn);
    }
}

/* sched-ebb's dependence hook.  A load depends on every jump before it
   (sched-deps keeps possibly trapping loads below jumps, by their
   address only: GCC marks jump-table loads MEM_NOTRAP_P, and those trap
   above their range check); here that dependence goes when the load's
   register isn't needed on the jump's other path, and the load moves
   up as ld,sm.  What has no speculative form stays below the jumps
   before it.  */
void
e2k_spec_pin (rtx_insn *head, rtx_insn *tail)
{
  e2k_bap_deps (head, tail);
  e2k_rrs_deps (head, tail);
  e2k_cond_ret_deps (head, tail);
  /* After the jumps' dependences below are dropped.  */
  auto done = [&] ()
    {
      e2k_unpred_cond_deps (head, tail);
      e2k_og_stmt_deps (head, tail);
    };
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
		   vec<rtx_insn *> &range, rtx_insn *src_only = NULL)
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
      /* A global costs nothing; a window register only if the window
	 has it anyway.  */
      if (fixed_regs[r] || (!G_REGNO_P (r) && !df_regs_ever_live_p (r))
	  || r == (int) REGNO (dest)
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
      if (!df_regs_ever_live_p (r))
	df_set_regs_ever_live (r, true);
      auto rename = [&] (rtx_insn *j)
	{
	  /* SRC_ONLY keeps writing DEST, from the new register.  */
	  rtx *loc = &PATTERN (j);
	  if (j == src_only)
	    loc = &SET_SRC (COND_EXEC_CODE (PATTERN (j)));
	  subrtx_ptr_iterator::array_type array;
	  FOR_EACH_SUBRTX_PTR (iter, array, loc, NONCONST)
	    if (REG_P (**iter) && REGNO (**iter) == REGNO (dest))
	      validate_change (j, *iter, gen_rtx_REG (GET_MODE (**iter), r), 1);
	};
      /* The load itself only as its destination: it may read the old
	 register for its address.  */
      rtx lp = PATTERN (insn);
      if (GET_CODE (lp) == COND_EXEC)
	lp = COND_EXEC_CODE (lp);
      validate_change (insn, &SET_DEST (lp), gen_rtx_REG (m, r), 1);
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
void
e2k_arm_reset_debug (rtx_insn *from, rtx_insn *to, rtx reg)
{
  for (rtx_insn *u = from; u && u != NEXT_INSN (to); u = NEXT_INSN (u))
    if (DEBUG_BIND_INSN_P (u) && e2k_hard_reg_in_p (reg, PATTERN (u)))
      {
	INSN_VAR_LOCATION_LOC (u) = gen_rtx_UNKNOWN_VAR_LOC ();
	df_insn_rescan_debug_internal (u);
      }
}

/* Whether an insn other than a debug insn lies between AFTER and I, so
   that moving I to just after AFTER moves it at all (with -g or
   without).  */
static bool
e2k_nondebug_between_p (rtx_insn *after, rtx_insn *i)
{
  for (rtx_insn *p = PREV_INSN (i); p != after; p = PREV_INSN (p))
    if (NONDEBUG_INSN_P (p))
      return true;
  return false;
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
      if (!e2k_nondebug_between_p (after, i))
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

/* A load that if-conversion put under a predicate as the last write of
   a register read on both ways after its arm ("x = c ? b[i] : x"):
   e2k_unpredicate_loads leaves it, as the other way reads the old value.
   Run it early, as ld,sm into a free register, and copy that under the
   predicate, as lcc does: then only the copy waits for the compare, 1
   cycle after the predicate instead of the load's 3 (5 on v6).  As
   e2k_unpred_arms, it goes up to just before the predicate's setter or
   the first insn that may change its address or memory.  */
static int
e2k_unpred_load_copies (basic_block bb)
{
  auto_vec<rtx_insn *, 16> cands;
  rtx_insn *insn;
  FOR_BB_INSNS (bb, insn)
    if (NONDEBUG_INSN_P (insn) && GET_CODE (PATTERN (insn)) == COND_EXEC
	&& recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_LOAD
	&& get_attr_mas (insn) != MAS_YES && cands.length () < 256)
      cands.safe_push (insn);
  int n = 0;
  for (rtx_insn *i : cands)
    {
      if (e2k_unpred_total >= e2k_unpred_limit)
	break;
      rtx cond = COND_EXEC_TEST (PATTERN (i));
      rtx set = COND_EXEC_CODE (PATTERN (i));
      if (GET_CODE (set) != SET || !REG_P (SET_DEST (set))
	  || !GPR_REGNO_P (REGNO (SET_DEST (set)))
	  || !REG_P (XEXP (cond, 0)))
	continue;
      rtx src = SET_SRC (set), mem = src;
      if (GET_CODE (mem) == ZERO_EXTEND || GET_CODE (mem) == SIGN_EXTEND)
	mem = XEXP (mem, 0);
      if (!MEM_P (mem) || MEM_VOLATILE_P (mem))
	continue;
      rtx dest = SET_DEST (set), pred = XEXP (cond, 0);
      rtx_code rc = reversed_comparison_code (cond, NULL);
      machine_mode m = GET_MODE (dest);
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
	      || (!other && modified_in_p (src, p)))
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
      if (!e2k_nondebug_between_p (after, i))
	continue;
      rtx_insn *first = NEXT_INSN (after);
      /* Preferably a register nothing after the copy writes either: the
	 next load into the one the copy reads would wait for it (an
	 unrolled chain's next element).  */
      int t = e2k_free_reg_lru (bb, first, BB_END (bb), m, REGNO (dest));
      if (t < 0)
	t = e2k_free_reg_lru (bb, first, i, m, REGNO (dest));
      if (t < 0)
	continue;
      rtx treg = gen_rtx_REG (m, t);
      rtx_insn *ld = emit_insn_after (gen_rtx_SET (treg, copy_rtx (src)),
				      after);
      INSN_LOCATION (ld) = INSN_LOCATION (i);
      if (recog_memoized (ld) < 0
	  || !validate_change (i, &PATTERN (i),
			       gen_rtx_COND_EXEC (VOIDmode, copy_rtx (cond),
						  gen_rtx_SET (copy_rtx (dest),
							       treg)), 0))
	{
	  delete_insn (ld);
	  continue;
	}
      e2k_arm_reset_debug (first, i, treg);
      e2k_ms_set_flag (ld, E2K_MS_SM);
      if (!df_regs_ever_live_p (t))
	df_set_regs_ever_live (t, true);
      e2k_unpred_total++;
      n++;
      if (dump_file)
	fprintf (dump_file, ";; e2k_unpred_load_copies: insn %d, %s -> %s\n",
		 INSN_UID (i), reg_names[t], reg_names[REGNO (dest)]);
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
void
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
	  rtx_insn *last = NULL;
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
	      /* The arm's last operation writes all of DEST under the same
		 predicate ("o = &G(L)->nilvalue" in Lua's index2value: a load
		 and an add): what follows reads either way's value, so the
		 load may go to another register only the arm reads.  */
	      if (same && e2k_unpred_last_p && !CALL_P (j)
		  && GET_CODE (body) == SET && REG_P (SET_DEST (body))
		  && REGNO (SET_DEST (body)) == REGNO (dest)
		  && GET_MODE (SET_DEST (body)) == GET_MODE (dest)
		  && j != insn)
		{
		  last = j;
		  done = true;
		  break;
		}
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
	  if (last && !e2k_unpred_rename (bb, insn, dest, range, last))
	    continue;
	  if (last)
	    {
	      set = COND_EXEC_CODE (PATTERN (insn));
	      dest = SET_DEST (set);
	    }
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
	  for (rtx_insn *j = BB_HEAD (bb); !opposite && !last && j != insn;
	       j = NEXT_INSN (j))
	    if (NONDEBUG_INSN_P (j) && e2k_hard_reg_in_p (dest, PATTERN (j)))
	      {
		e2k_unpred_rename (bb, insn, dest, range);
		break;
	      }
	}
      if (e2k_unpred_copy_p)
	n += e2k_unpred_load_copies (bb);
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
void
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
   read such a value.  So may a register nothing has set yet on some
   path into the insn, or one a call may have changed: what the
   function's entry doesn't define, or a call clobbers, can hold
   anything, a diagnostic value too (one a caller or callee left from
   its own speculative loads), and an operation run ahead of its guard
   may read such a register where the guard would have kept it from
   being read (gfortran's bind-c-contiguous-4: a compare of an absent
   argument's extent, after a call).  Loads, FP operations, divisions
   and DAM checks
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
    case TYPE_FLAG: case TYPE_FLAGMUL: case TYPE_CCTOP:
      return false;
    default:
      return true;
    }
}

/* The effect of INSN on DIAG.  */
static void
e2k_diag_step (rtx_insn *insn, HARD_REG_SET *diag)
{
  if (CALL_P (insn))
    {
      HARD_REG_SET clob = (insn_callee_abi (insn).full_reg_clobbers ()
			   & ~fixed_reg_set);
      unsigned r;
      hard_reg_set_iterator hrsi;
      EXECUTE_IF_SET_IN_HARD_REG_SET (clob, 0, r, hrsi)
	SET_HARD_REG_BIT (*diag, e2k_diag_reg (r));
      return;
    }
  if (!NONDEBUG_INSN_P (insn))
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

void
e2k_spec_prune (void)
{
  /* What may be diagnostic on entry: all but what the entry defines
     (the arguments, the stack pointer) and the fixed registers.  */
  HARD_REG_SET entry;
  SET_HARD_REG_SET (entry);
  entry &= ~fixed_reg_set;
  {
    bitmap_iterator bi;
    unsigned r;
    EXECUTE_IF_SET_IN_BITMAP (df->entry_block_defs, 0, r, bi)
      if (r < FIRST_PSEUDO_REGISTER && !B_REGNO_P (r) && !BX_REGNO_P (r))
	CLEAR_HARD_REG_BIT (entry, r);
  }
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
	    if (e->src == ENTRY_BLOCK_PTR_FOR_FN (cfun))
	      d |= entry;
	    else
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
	if (e->src == ENTRY_BLOCK_PTR_FOR_FN (cfun))
	  d |= entry;
	else
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
