/* Register renaming for the Elbrus (E2K) port: which window
   registers regrename may take without growing the window (and how deep
   the calls below a function go), and renaming that lets operations of
   an extended block run above its branches.
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

/* WTOP: the window registers below it (from %r0, as e2k_compute_window
   counts them, by pairs) cost the function nothing.  */
bool
e2k_rename_free_p (unsigned r, machine_mode mode, bitmap live,
		   const HARD_REG_SET &busy, unsigned wtop)
{
  if (fixed_regs[r] || TEST_HARD_REG_BIT (busy, r)
      || bitmap_bit_p (live, r) || !targetm.hard_regno_mode_ok (r, mode))
    return false;
  if (PRED_REGNO_P (r))
    return true;
  /* A global, or a window register the window has anyway.  */
  return (G_REGNO_P (r)
	  || (W_REGNO_P (r)
	      && (df_regs_ever_live_p (r) || r - R0_REGNUM < wtop)));
}

/* The first window register above every one the insns use, rounded up
   to its pair (e2k_compute_window's measure, now).  */
unsigned
e2k_window_top (void)
{
  int maxr = -1;
  for (rtx_insn *insn = get_insns (); insn; insn = NEXT_INSN (insn))
    if (NONDEBUG_INSN_P (insn))
      {
	subrtx_iterator::array_type array;
	FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
	  if (REG_P (*iter) && HARD_REGISTER_P (*iter))
	    for (unsigned r = REGNO (*iter); r < END_REGNO (*iter); r++)
	      if (W_REGNO_P (r))
		maxr = MAX (maxr, (int) (r - R0_REGNUM));
      }
  return maxr < 0 ? 0 : (maxr | 1) + 1;
}

/* How deep the calls below each function compiled so far go (0: a
   leaf, E2K_DEEP: unknown), by DECL_UID (e2k_note_depth): GCC compiles
   callees first.  */
#define E2K_DEEP 8
static hash_map<int_hash<int, -1, -2>, int> *e2k_fn_depths;

static int
e2k_callee_depth (tree decl)
{
  if (!decl)
    return E2K_DEEP;
  if (fndecl_built_in_p (decl, BUILT_IN_NORMAL))
    switch (DECL_FUNCTION_CODE (decl))
      {
      case BUILT_IN_MEMCPY: case BUILT_IN_MEMMOVE: case BUILT_IN_MEMSET:
      case BUILT_IN_MEMCMP: case BUILT_IN_BCMP: case BUILT_IN_MEMCHR:
      case BUILT_IN_STRLEN: case BUILT_IN_STRCMP: case BUILT_IN_STRNCMP:
      case BUILT_IN_STRCHR: case BUILT_IN_STRCPY:
	return 0;
      default:
	break;
      }
  int *d = e2k_fn_depths ? e2k_fn_depths->get (DECL_UID (decl)) : NULL;
  return d ? *d : E2K_DEEP;
}

void
e2k_note_depth (void)
{
  int depth = 0;
  for (rtx_insn *insn = get_insns (); insn; insn = NEXT_INSN (insn))
    if (CALL_P (insn) && !SIBLING_CALL_P (insn))
      depth = MAX (depth, MIN (e2k_callee_depth (get_call_fndecl (insn)) + 1,
			       E2K_DEEP));
  if (!e2k_fn_depths)
    e2k_fn_depths = new hash_map<int_hash<int, -1, -2>, int>;
  e2k_fn_depths->put (DECL_UID (current_function_decl), depth);
}

/* HARD_REGNO_RENAME_OK: whether regrename may move a value from FROM
   to TO.  Not into the outgoing registers: values there block software
   pipelining (setbn renames them).  In a function that calls, not into
   a window register above those register allocation used either, unless
   its calls are rare: every pair more is one more that each call keeps
   below its callee, which a deep call chain spills and fills at every
   call and return (spec/abi/registers.md, "What windows cost"), and
   regrename takes the register used least recently, which is one never
   used.  Lua's precallC, which calls every C function, went from 7 pairs
   to 32 that way, and k-nucleotide spent 5% of its cycles on
   register-file spills on the 8C2 (lcc's 0.9%).  A leaf's window costs
   nothing while it fits (relcc2 findings I31), and neither does more
   window in a function whose hottest block runs e2k_rename_window_ratio
   times as often as its hottest call, leaving out calls to functions
   known to call no deeper than leaves (e2k_rename_window_shallow): the
   renaming wins more there (CoreMark's matrix_test, its kernels inlined,
   calls crc16 once per run of them, and ran 7% slower without; bzip2's
   mainSort calls mainQSort3, which calls only leaves).  */
bool
e2k_hard_regno_rename_ok (unsigned, unsigned to)
{
  if (B_REGNO_P (to))
    return false;
  if (!W_REGNO_P (to) || !e2k_rename_window || !cfun || crtl->is_leaf)
    return true;
  machine_function *m = cfun->machine;
  if (!m->rename_top)
    {
      m->rename_top = e2k_window_top () + 1;
      /* Calls much colder than the function's hottest code (CoreMark's
	 matrix_test, its kernels inlined, calls crc16 once per run of
	 them) cost less than the renaming would win there.  */
      profile_count hot = profile_count::uninitialized ();
      profile_count call = profile_count::uninitialized ();
      basic_block bb;
      FOR_EACH_BB_FN (bb, cfun)
	{
	  hot = profile_count::max_prefer_initialized (hot, bb->count);
	  rtx_insn *insn;
	  FOR_BB_INSNS (bb, insn)
	    if (CALL_P (insn))
	      {
		tree fn = get_call_fndecl (insn);
		int depth = e2k_callee_depth (fn);
		if (dump_file)
		  {
		    fprintf (dump_file, ";; e2k window: call to %s, depth %d, ",
			     fn ? IDENTIFIER_POINTER (DECL_NAME (fn)) : "?",
			     depth);
		    bb->count.dump (dump_file);
		    fprintf (dump_file, "\n");
		  }
		if (!e2k_rename_window_shallow || depth > 1)
		  call = profile_count::max_prefer_initialized (call,
								       bb->count);
	      }
	}
      m->rename_any = (e2k_rename_window_ratio && hot.initialized_p ()
		       && (!call.initialized_p ()
			   || (call.apply_scale (e2k_rename_window_ratio, 1)
			       < hot)));
      if (dump_file && call.initialized_p () && hot.initialized_p ())
	fprintf (dump_file, ";; e2k window: %d registers, hottest call at "
		 "%.3f of the hottest block: %s\n", m->rename_top - 1,
		 (double) call.to_gcov_type () / MAX (hot.to_gcov_type (), 1),
		 m->rename_any ? "any" : "kept");
      else if (dump_file)
	fprintf (dump_file, ";; e2k window: %d registers, no call below a "
		 "leaf's caller: %s\n", m->rename_top - 1,
		 m->rename_any ? "any" : "kept");
    }
  return m->rename_any || to - R0_REGNUM < (unsigned) m->rename_top - 1;
}

void
e2k_note_regs (rtx x, HARD_REG_SET *set)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, x, NONCONST)
    if (REG_P (*iter) && HARD_REGISTER_P (*iter))
      add_to_hard_reg_set (set, GET_MODE (*iter), REGNO (*iter));
}

/* The block after BB in its extended block as schedule_ebbs makes them
   (sched-ebb.cc): entered only by falling through from BB, no label, a
   fall-through not below the tracer's probability cutoff.  */
basic_block
e2k_chain_next (basic_block bb)
{
  basic_block n = bb->next_bb;
  if (n == EXIT_BLOCK_PTR_FOR_FN (cfun) || !single_pred_p (n)
      || single_pred (n) != bb
      || !(single_pred_edge (n)->flags & EDGE_FALLTHRU)
      || LABEL_P (BB_HEAD (n)))
    return NULL;
  edge e = single_pred_edge (n);
  int cutoff = (REG_BR_PROB_BASE / 100
		* (profile_status_for_fn (cfun) == PROFILE_READ
		   ? param_tracer_min_branch_probability_feedback
		   : param_tracer_min_branch_probability));
  if (e->probability.initialized_p ()
      && e->probability.to_reg_br_prob_base () <= cutoff)
    return NULL;
  return n;
}

/* Note in STAMP that BB, block POS of a chain, is in the way of each
   register it mentions, a call in it clobbers, or one of its jumps needs
   on the other path: a value of a block below written into such a
   register can't move above BB.  */
static void
e2k_chain_stamp (basic_block bb, int pos, int *stamp)
{
  rtx_insn *insn;
  FOR_BB_INSNS (bb, insn)
    if (NONDEBUG_INSN_P (insn))
      {
	subrtx_iterator::array_type array;
	FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
	  if (REG_P (*iter) && HARD_REGISTER_P (*iter))
	    for (unsigned r = REGNO (*iter); r < END_REGNO (*iter); r++)
	      stamp[r] = pos;
	if (CALL_P (insn))
	  {
	    HARD_REG_SET clob
	      = insn_callee_abi (insn).full_and_partial_reg_clobbers ();
	    for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
	      if (TEST_HARD_REG_BIT (clob, r))
		stamp[r] = pos;
	    for (rtx link = CALL_INSN_FUNCTION_USAGE (insn); link;
		 link = XEXP (link, 1))
	      FOR_EACH_SUBRTX (iter, array, XEXP (link, 0), NONCONST)
		if (REG_P (*iter) && HARD_REGISTER_P (*iter))
		  for (unsigned r = REGNO (*iter); r < END_REGNO (*iter); r++)
		    stamp[r] = pos;
	  }
      }
  edge e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, bb->succs)
    if (!(e->flags & EDGE_FALLTHRU))
      {
	unsigned r;
	bitmap_iterator bi;
	EXECUTE_IF_SET_IN_BITMAP (df_get_live_in (e->dest), 0, r, bi)
	  if (r < FIRST_PSEUDO_REGISTER)
	    stamp[r] = pos;
      }
}

static void
e2k_note_use_regs (rtx *loc, void *data)
{
  e2k_note_regs (*loc, (HARD_REG_SET *) data);
}

void
e2k_spec_rename (void)
{
  df_analyze ();
  basic_block x;
  bool changed = false;
  unsigned wtop = e2k_window_top ();
  /* Along a chain of blocks falling through into each other (an extended
     block), the last block that is in the way of each register
     (e2k_chain_stamp), from 1, and the last block it is live out of.  */
  int stamp[FIRST_PSEUDO_REGISTER], live_to[FIRST_PSEUDO_REGISTER];
  int pos = 0;
  basic_block prev = NULL;
  FOR_EACH_BB_FN (x, cfun)
    {
      if (!prev || e2k_chain_next (prev) != x)
	{
	  memset (stamp, 0, sizeof stamp);
	  memset (live_to, 0, sizeof live_to);
	  pos = 0;
	  int p = 0;
	  for (basic_block b = x; b; b = e2k_chain_next (b))
	    {
	      unsigned r;
	      bitmap_iterator bi;
	      p++;
	      EXECUTE_IF_SET_IN_BITMAP (df_get_live_out (b), 0, r, bi)
		if (r < FIRST_PSEUDO_REGISTER)
		  live_to[r] = p;
	    }
	}
      prev = x;
      e2k_chain_stamp (x, ++pos, stamp);
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
      /* What Y mentions, and what its values are renamed into; what X
	 reads (predicated copies and store addresses too): only a value
	 X reads or needs after it is worth a copy back.  */
      HARD_REG_SET busy, xreads;
      CLEAR_HARD_REG_SET (busy);
      CLEAR_HARD_REG_SET (xreads);
      rtx_insn *insn;
      FOR_BB_INSNS (x, insn)
	if (NONDEBUG_INSN_P (insn))
	  note_uses (&PATTERN (insn), e2k_note_use_regs, &xreads);
      FOR_BB_INSNS (y, insn)
	if (NONDEBUG_INSN_P (insn))
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
	  /* Where the register is in the way: X (its jump, its other path,
	     any insn of it), else the last block above that is; 0 for
	     nowhere.  */
	  bool near = bitmap_bit_p (xlive, dr) || stamp[dr] == pos;
	  int lim = near ? pos : stamp[dr];
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
	  /* Above the blocks before X only without a copy back, and with one
	     only for a value X reads or needs after it (a register X only
	     writes is no reason for an extra copy).  */
	  if (movable && lim
	      && (copy ? (bitmap_bit_p (xlive, dr)
			  || TEST_HARD_REG_BIT (xreads, dr))
		       && !PRED_REGNO_P (dr)
		  : true))
	    {
	      /* The register least recently used along the chain, so that
		 the value moves farthest up (bzip2's mainGtU: each step's
		 bytes went to the registers of the step two up and waited
		 for its compare); not one a block further down keeps
		 across its end; globals first.  */
	      unsigned best = UINT_MAX;
	      for (unsigned c = 0; c < FIRST_PSEUDO_REGISTER; c++)
		if (PRED_REGNO_P (c) == PRED_REGNO_P (dr)
		    && stamp[c] < lim
		    && e2k_rename_free_p (c, mode, xlive, busy, wtop))
		  {
		    unsigned key
		      = (((unsigned) (live_to[c] > pos + 1) << 24)
			 | ((unsigned) stamp[c] << 2)
			 | (G_REGNO_P (c) || PRED_REGNO_P (c) ? 0
			    : df_regs_ever_live_p (c) ? 1 : 2));
		    if (key < best)
		      best = key, r = c;
		  }
	    }
	  if (r == INVALID_REGNUM)
	    {
	      add_to_hard_reg_set (&ydefs, mode, dr);
	      /* A value that moves up as it is (an address computed for a
		 load) is available at the jump too.  */
	      if (movable && !near)
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
	  /* Debug binds of the new register in Y, or of the old one where
	     it was renamed, would show the wrong value.  */
	  {
	    bool in = false;
	    FOR_BB_INSNS (y, u)
	      {
		if (u == insn)
		  in = true;
		if (u == end)
		  in = false;
		if (DEBUG_BIND_INSN_P (u)
		    && (reg_mentioned_p (nreg, PATTERN (u))
			|| (in && reg_mentioned_p (dest, PATTERN (u)))))
		  {
		    INSN_VAR_LOCATION_LOC (u) = gen_rtx_UNKNOWN_VAR_LOC ();
		    df_insn_rescan_debug_internal (u);
		  }
	      }
	  }
	  if (!df_regs_ever_live_p (r))
	    df_set_regs_ever_live (r, true);
	  SET_HARD_REG_BIT (busy, r);
	  SET_HARD_REG_BIT (renamed, r);
	  add_to_hard_reg_set (&ydefs, mode, dr);
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_spec_rename: insn %d in bb %d: %s -> "
		     "%s, %d up%s\n", INSN_UID (insn), y->index, reg_names[dr],
		     reg_names[r], pos + 1 - lim, copy ? ", copied back" : "");
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
