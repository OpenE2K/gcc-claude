/* Software pipelining for the Elbrus (E2K) port (see e2k-ms.cc):
   writing a scheduled loop: its prologue, kernel and exits, the copies
   out of the ring, the array prefetch program and AAU stores.
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

static bool e2k_ms_reads_p (rtx, unsigned);

/* A clocked prologue's own schedule.  The modulo schedule's times put
   the copies in and the first iterations where the kernel would have
   them, slack and all (a copy in at its value's time in a virtual
   earlier iteration, the first load three cycles after it).  Instead
   place the items PATS, in their emission order SEQ, each in the first
   cycle (from 2, after setbn) where its operands are there at the
   pipeliner's latencies (e2k_ms_analyze: crossings counted) and the
   DFA takes it, keeping a register's reads before a write of it and
   its writes in order.  The hardware interlocks registers: a late
   operand costs a stall, never a wrong value.  Fills CLOCK (by item)
   and *LAST; false (keep the modulo times) when an item stores, locks
   or checks, or no cycle near its old one takes it.  OC is each item's
   clock by the modulo schedule.  */
static bool
e2k_ms_list_prologue (const vec<rtx> &pats, const vec<int> &seq,
		      const vec<int> &oc, vec<int> *clock, int *last)
{
  int ni = pats.length ();
  auto_vec<rtx_insn *> xi (ni);
  auto_vec<HARD_REG_SET> sets (ni);
  for (int k = 0; k < ni; k++)
    {
      rtx_insn *x = make_insn_raw (copy_rtx (pats[k]));
      if (recog_memoized (x) < 0 || volatile_insn_p (PATTERN (x)))
	return false;
      enum attr_type t = get_attr_type (x);
      if (t == TYPE_STORE || t == TYPE_LDLOCK || t == TYPE_LDCHK
	  || MEM_P (SET_DEST (e2k_ms_set (pats[k]))))
	return false;
      xi.quick_push (x);
      HARD_REG_SET h;
      CLEAR_HARD_REG_SET (h);
      note_stores (x, record_hard_reg_sets, &h);
      sets.quick_push (h);
    }
  clock->truncate (0);
  clock->safe_grow_cleared (ni);
  /* DFA states of the cycles so far.  */
  auto_vec<state_t> states;
  auto state_of = [&] (int c)
    {
      while ((int) states.length () <= c)
	{
	  state_t st = xmalloc (dfa_state_size);
	  state_reset (st);
	  states.safe_push (st);
	}
      return states[c];
    };
  bool ok = true;
  state_t tmp = alloca (dfa_state_size);
  for (int p = 0; p < ni && ok; p++)
    {
      int k = seq[p], e = 2;
      for (int q = 0; q < p; q++)
	{
	  int m = seq[q];
	  for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
	    {
	      if (TEST_HARD_REG_BIT (sets[m], r)
		  && e2k_ms_reads_p (pats[k], r))
		{
		  enum attr_type dt = get_attr_type (xi[m]);
		  int cross = (dt == TYPE_FP || dt == TYPE_FMA
			       || dt == TYPE_FFMA || dt == TYPE_FCVT
			       || dt == TYPE_FSCALE
			       || dt == TYPE_FDIV || dt == TYPE_MUL ? 2 : 1);
		  if (E2K_LAT6 && dt == TYPE_LOAD)
		    cross = 0;
		  int lat = MAX (insn_latency (xi[m], xi[k]), 1);
		  if (e2k_packed_type_p (dt))
		    cross = MAX (4 - lat, 0);
		  if (dt == TYPE_FLAG || dt == TYPE_FLAGMUL)
		    cross = MAX (insn_default_latency (xi[m]) - lat, 0);
		  if (dt == TYPE_FCMP)
		    cross = 0;
		  /* No more than the modulo schedule gave it, which keeps
		     a recurrence in one cluster (e2k_ms_pipeline).  */
		  lat = MAX (MIN (lat + cross, oc[k] - oc[m]), 1);
		  e = MAX (e, (*clock)[m] + lat);
		}
	      if (TEST_HARD_REG_BIT (sets[k], r))
		{
		  if (e2k_ms_reads_p (pats[m], r))
		    e = MAX (e, (*clock)[m]);
		  if (TEST_HARD_REG_BIT (sets[m], r))
		    e = MAX (e, (*clock)[m] + 1);
		}
	    }
	}
      int c = e;
      for (;; c++)
	{
	  if (c > oc[k] + 64)
	    {
	      ok = false;
	      break;
	    }
	  memcpy (tmp, state_of (c), dfa_state_size);
	  if (state_transition (tmp, xi[k]) < 0)
	    {
	      memcpy (state_of (c), tmp, dfa_state_size);
	      break;
	    }
	}
      (*clock)[k] = c;
    }
  for (state_t st : states)
    free (st);
  if (!ok)
    return false;
  *last = 0;
  for (int k = 0; k < ni; k++)
    *last = MAX (*last, (*clock)[k]);
  return true;
}

/* The SET of a node's pattern (a lock load's is in a PARALLEL, a
   predicated store's in a COND_EXEC).  */
rtx
e2k_ms_set (rtx pat)
{
  if (GET_CODE (pat) == COND_EXEC)
    pat = COND_EXEC_CODE (pat);
  return GET_CODE (pat) == PARALLEL ? XVECEXP (pat, 0, 0) : pat;
}

/* Node I's pattern for iteration J, with names in the frame of kernel
   iteration FRAME.  */
static rtx
e2k_ms_instance (e2k_ms_loop *l, int i, int j, int frame)
{
  e2k_ms_node *node = &l->nodes[i];
  rtx pat = copy_rtx (PATTERN (node->insn));
  rtx set = e2k_ms_set (pat);
  auto subst = [&] (rtx *loc)
    {
      subrtx_ptr_iterator::array_type array;
      FOR_EACH_SUBRTX_PTR (iter, array, loc, NONCONST)
	if (REG_P (**iter) && B_REGNO_P (REGNO (**iter))
	    && (l->binv & (1u << (REGNO (**iter) - B0_REGNUM))))
	  **iter = gen_rtx_REG (GET_MODE (**iter),
				l->bmap[REGNO (**iter) - B0_REGNUM]);
	else if (REG_P (**iter))
	  for (int k = 0; k < node->nuses; k++)
	    if (node->uses[k].regno == REGNO (**iter)
		&& node->uses[k].value >= 0 && !node->uses[k].pred)
	      {
		rtx *slot = *iter;
		*slot = e2k_ms_reg (GET_MODE (**iter),
				  e2k_ms_name (l, node->uses[k].value,
					       j - node->uses[k].dist,
					       frame));
		break;
	      }
	    else if (node->uses[k].regno == REGNO (**iter)
		     && node->uses[k].pred && l->npred)
	      {
		rtx *slot = *iter;
		*slot = gen_rtx_REG (BImode,
				     PRED0_REGNUM
				     + e2k_ms_pname (l, node->uses[k].value,
						     j - node->uses[k].dist,
						     frame));
		break;
	      }
    };
  if (node->chk >= 0)
    {
      /* A check: the lock load's address, into its register.  */
      rtx ite = SET_SRC (set);
      subst (&XEXP (ite, 1));
      rtx r = e2k_ms_reg (GET_MODE (SET_DEST (set)),
			  e2k_ms_name (l, l->nodes[node->chk].value, j, frame));
      SET_DEST (set) = r;
      XEXP (ite, 2) = r;
      XVECEXP (XEXP (XEXP (ite, 0), 0), 0, 0) = r;
      return pat;
    }
  subst (&SET_SRC (set));
  if (GET_CODE (pat) == COND_EXEC)
    subst (&COND_EXEC_TEST (pat));
  if (MEM_P (SET_DEST (set)) && node->rebase_off)
    SET_DEST (set) = adjust_address_nv (SET_DEST (set),
					GET_MODE (SET_DEST (set)),
					-node->rebase_off);
  if (MEM_P (SET_DEST (set)))
    subst (&XEXP (SET_DEST (set), 0));
  else if (!node->pred && !node->dpred)
    SET_DEST (set) = e2k_ms_reg (GET_MODE (SET_DEST (set)),
				 e2k_ms_name (l, node->value, j, frame));
  else if (l->npred)
    SET_DEST (set) = gen_rtx_REG (BImode,
				  PRED0_REGNUM + e2k_ms_pname (l, i, j, frame));
  return pat;
}

/* The %b[] name, after the loop, of value V's instance from the
   iteration BACK before the last.  The kernel ran once more after the
   last iteration's def stage D, so it rotated S - D times since.  */
static int
e2k_ms_exit_name (e2k_ms_loop *l, int v, int back)
{
  const e2k_ms_value &val = l->values[v];
  if (val.name < 0)
    return val.name;
  return ((val.name + 2 * (l->stages - l->nodes[val.node].time / l->ii
			   + back))
	  % (2 * l->pairs));
}

/* Node I's pattern run after the loop on the last iteration's values.  */
static rtx
e2k_ms_exit_instance (e2k_ms_loop *l, int i)
{
  e2k_ms_node *node = &l->nodes[i];
  rtx pat = copy_rtx (PATTERN (node->insn));
  subrtx_ptr_iterator::array_type array;
  FOR_EACH_SUBRTX_PTR (iter, array, &SET_SRC (pat), NONCONST)
    if (REG_P (**iter))
      for (int k = 0; k < node->nuses; k++)
	if (node->uses[k].regno == REGNO (**iter)
	    && node->uses[k].value >= 0 && !node->uses[k].pred)
	  {
	    rtx *slot = *iter;
	    *slot = e2k_ms_reg (GET_MODE (**iter),
				e2k_ms_exit_name (l, node->uses[k].value,
						  node->uses[k].dist));
	    break;
	  }
  return pat;
}

/* The first block's exit test run again after the loop: its nodes in
   order, after AFTER, or at the end of the sequence being built if
   AFTER is null.  Returns the last.  Its compares are speculative: in a
   merged chain a compare's operands may come from loads whose guard,
   an earlier condition, didn't hold, and the landps ignore them.  */
static rtx_insn *
e2k_ms_emit_exit_test (e2k_ms_loop *l, rtx_insn *after)
{
  rtx_insn *x = after;
  for (int c : l->c1s)
    {
      rtx pat = e2k_ms_exit_instance (l, c);
      x = x ? emit_insn_after (pat, x) : emit_insn (pat);
      if (recog_memoized (x) < 0)
	gcc_unreachable ();
      if (get_attr_type (x) == TYPE_CMP || get_attr_type (x) == TYPE_FCMP
	  || get_attr_type (x) == TYPE_CCTOP)
	e2k_ms_set_flag (x, E2K_MS_SM);
    }
  return x;
}

/* A mode for copying a register of MODE whole: one of the predicable
   moves.  */
static machine_mode
e2k_ms_copy_mode (machine_mode mode)
{
  if (mode == SImode || mode == DImode || mode == SFmode || mode == DFmode)
    return mode;
  return GET_MODE_SIZE (mode) <= 4 ? SImode : DImode;
}

/* Whether pattern X reads hard register R.  */
static bool
e2k_ms_reads_p (rtx x, unsigned r)
{
  if (PRED_REGNO_P (r))
    {
      if (GET_CODE (x) == COND_EXEC
	  && refers_to_regno_p (r, r + 1, COND_EXEC_TEST (x), NULL))
	return true;
      return refers_to_regno_p (r, r + 1, SET_SRC (e2k_ms_set (x)), NULL);
    }
  x = e2k_ms_set (x);
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
	  rtx da = SET_DEST (e2k_ms_set (pats[a]));
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

/* JUMP, a prepared conditional transfer at the end of its block: the
   disp in the same block that prepares its CTPR, if nothing else in
   between touches it, or NULL.  An entry edge along it can then take a
   prologue: the disp is pointed at the new block (e2k_ms_split_entry).
   One prepared elsewhere (an outer loop's latch whose disp is in its
   preheader) can't be.  */
rtx_insn *
e2k_ms_local_disp (rtx_insn *jump)
{
  if (!JUMP_P (jump) || recog_memoized (jump) < 0
      || get_attr_type (jump) != TYPE_CT
      || GET_CODE (PATTERN (jump)) != PARALLEL)
    return NULL;
  rtx ctpr = XEXP (XVECEXP (PATTERN (jump), 0, 1), 0);
  basic_block bb = BLOCK_FOR_INSN (jump);
  for (rtx_insn *x = PREV_INSN (jump); x && x != PREV_INSN (BB_HEAD (bb));
       x = PREV_INSN (x))
    {
      if (!NONDEBUG_INSN_P (x))
	continue;
      if (CALL_P (x))
	return NULL;
      if (reg_mentioned_p (ctpr, PATTERN (x)))
	return (recog_memoized (x) == CODE_FOR_e2k_disp_label
		&& reg_set_p (ctpr, x) ? x : NULL);
    }
  return NULL;
}

/* Split entry edge E for a prologue; a prepared conditional transfer
   along it has its disp moved to the new block.  */
static basic_block
e2k_ms_split_entry (edge e)
{
  rtx_insn *disp = NULL;
  if (!(e->flags & EDGE_FALLTHRU) && !single_succ_p (e->src))
    disp = e2k_ms_local_disp (BB_END (e->src));
  basic_block p = split_edge (e);
  if (disp)
    {
      rtx label = block_label (p);
      rtx un = SET_SRC (PATTERN (disp));
      rtx old = label_ref_label (XVECEXP (un, 0, 0));
      XVECEXP (un, 0, 0) = gen_rtx_LABEL_REF (Pmode, label);
      LABEL_NUSES (old)--;
      LABEL_NUSES (label)++;
      if (rtx note = find_reg_note (disp, REG_LABEL_OPERAND, old))
	remove_note (disp, note);
      add_reg_note (disp, REG_LABEL_OPERAND, label);
      INSN_CODE (disp) = -1;
      if (recog_memoized (disp) < 0)
	gcc_unreachable ();
      df_insn_rescan (disp);
    }
  return p;
}


/* Make a two-block while loop one block: drop the first block's exit
   and let the loop end test the landp.  */
static void
e2k_ms_wl_merge (e2k_ms_loop *l, const e2k_ms_wl *w)
{
  basic_block h = l->bb;
  edge ex = NULL, e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, h->succs)
    if (e->dest != w->b)
      ex = e;
  if (w->hdisp)
    delete_insn (w->hdisp);
  if (w->bdisp)
    delete_insn (w->bdisp);
  delete_insn (w->hjump);
  remove_edge (ex);
  e = single_succ_edge (h);
  e->flags |= EDGE_FALLTHRU;
  e->probability = profile_probability::always ();
  rtx cond = e2k_ms_jump_cond (l->jump);
  PUT_CODE (cond, NE);
  XEXP (cond, 0) = w->pstay;
  INSN_CODE (l->jump) = -1;
  if (recog_memoized (l->jump) < 0)
    gcc_unreachable ();
  df_insn_rescan (l->jump);
  merge_blocks (h, w->b);
}

/* Give the movas of L their channels and areas, and queue the
   program, .LAPB<N>; returns N.  Channels 0 and 1 read areas of the
   buffer's left half, 2 and 3 its right half (spec/isa/apb.md, "What a
   mova reads"), so a kernel row holds at most two movas of each half.
   An area holds the movas of one descriptor, element size and stage in
   one half, within mrng bytes of its first (32; on v3 24 plus the
   element size, below): a stage reads its own iteration, so it needs a
   position of its own, which the area's last mova in the kernel
   advances (am = 1) after the others have read it; IND is the offset
   in the step.  It starts where the kernel's first instance reads
   (stage U of iteration S - 1 - U): DISP from the descriptor's base,
   the address on the way in.  An area is named by its program
   instruction; each half's 2 KiB are shared by its areas.  As lcc
   reads adler32's 16 bytes an iteration: two areas, 8 bytes each.

   The movas one area could hold form a group; each group goes to a
   half, the larger groups first, where its movas fit beside the ones
   already there, else in the half with fewer groups, and a mova that
   finds its row's two channels of that half taken goes to the other
   half (an area there).  Like lcc, which gives its two areas a half
   each, this spreads the areas over both halves: each gets twice the
   buffer, and the area's size is its prefetch depth (apb.md, "Area
   size is the prefetch depth"; PolyBench gramschmidt's column walks,
   a line per element, ran about 15% faster on the 8C2).  With
   -mno-ms-apb-spread, a row's movas take channels in order.  */
static int
e2k_ms_apb_assign (e2k_ms_loop *l)
{
  int ii = l->ii, s = l->stages;
  struct area
  {
    int d, size, stage, half, last, incr;
    HOST_WIDE_INT lo, hi, step;
  };
  /* Movas by offset, so that a window takes the nearest.  */
  int order[E2K_MS_MAX_NODES], n = 0;
  HOST_WIDE_INT key[E2K_MS_MAX_NODES];
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].apb)
      {
	order[n++] = i;
	key[i] = l->nodes[i].apb_off;
      }
  for (int a = 1; a < n; a++)
    for (int b = a; b > 0 && key[order[b - 1]] > key[order[b]]; b--)
      std::swap (order[b - 1], order[b]);
  auto_vec<area> groups;
  int grp[E2K_MS_MAX_NODES], half[E2K_MS_MAX_NODES];
  for (int k = 0; k < n; k++)
    {
      e2k_ms_node *node = &l->nodes[order[k]];
      int stage = node->time / ii;
      /* On v3 every mova from an area whose mrng exceeds 24 bytes plus
	 its element size is diagnostic (the 4C: words up to 28, bytes
	 up to 25); doublewords and v5 take 32.  LAME's 22-tap FIR read
	 words over 32 bytes and died of SIGILL.  */
      int mrng = e2k_arch < 5 ? MIN (24 + node->apb_size, 32) : 32;
      unsigned g = 0;
      for (; g < groups.length (); g++)
	if (groups[g].d == node->apb_d && groups[g].size == node->apb_size
	    && groups[g].stage == stage && groups[g].step == node->apb_step
	    && node->apb_off + node->apb_size - groups[g].lo <= mrng)
	  break;
      if (g == groups.length ())
	{
	  area ar = { node->apb_d, node->apb_size, stage, 0, order[k], 0,
		      node->apb_off, node->apb_off, node->apb_step };
	  groups.safe_push (ar);
	}
      grp[order[k]] = g;
    }
  int ng = groups.length ();
  /* USED[H * II + R]: movas of row R in half H.  */
  auto_vec<int> used;
  used.safe_grow_cleared (2 * ii);
  if (!e2k_ms_apb_spread)
    {
      for (int i = 0; i < l->n; i++)
	if (l->nodes[i].apb)
	  {
	    int r = l->nodes[i].time % ii;
	    int h = used[r] >= 2;
	    half[i] = h;
	    used[h * ii + r]++;
	  }
    }
  else
    {
      auto_vec<int> gsize, gorder;
      gsize.safe_grow_cleared (ng);
      for (int k = 0; k < n; k++)
	gsize[grp[order[k]]]++;
      for (int g = 0; g < ng; g++)
	{
	  int b = gorder.length ();
	  gorder.safe_push (g);
	  for (; b > 0 && gsize[gorder[b - 1]] < gsize[g]; b--)
	    std::swap (gorder[b - 1], gorder[b]);
	}
      int nhome[2] = { 0, 0 };
      auto_vec<int> need;
      need.safe_grow_cleared (ii);
      for (int g : gorder)
	{
	  for (int r = 0; r < ii; r++)
	    need[r] = 0;
	  for (int k = 0; k < n; k++)
	    if (grp[order[k]] == g)
	      need[l->nodes[order[k]].time % ii]++;
	  bool fit[2];
	  for (int h = 0; h < 2; h++)
	    {
	      fit[h] = true;
	      for (int r = 0; r < ii; r++)
		fit[h] &= used[h * ii + r] + need[r] <= 2;
	    }
	  int h = nhome[1] < nhome[0];
	  if (!fit[h] && fit[!h])
	    h = !h;
	  nhome[h]++;
	  for (int k = 0; k < n; k++)
	    if (grp[order[k]] == g)
	      {
		int i = order[k], r = l->nodes[i].time % ii;
		int hh = used[h * ii + r] < 2 ? h : !h;
		gcc_assert (used[hh * ii + r] < 2);
		half[i] = hh;
		used[hh * ii + r]++;
	      }
	}
    }
  /* Channels: a row's movas of the left half 0 and 1, of the right
     half 2 and 3.  */
  for (int r = 0; r < ii; r++)
    {
      int ch[2] = { 0, 2 };
      for (int i = 0; i < l->n; i++)
	if (l->nodes[i].apb && l->nodes[i].time % ii == r)
	  l->nodes[i].apb_chan = ch[half[i]]++;
    }
  /* The areas: a group's movas in one half.  */
  auto_vec<area> areas;
  int agrp[64];
  for (int k = 0; k < n; k++)
    {
      e2k_ms_node *node = &l->nodes[order[k]];
      int g = grp[order[k]], h = half[order[k]];
      unsigned a = 0;
      for (; a < areas.length (); a++)
	if (agrp[a] == g && areas[a].half == h)
	  break;
      if (a == areas.length ())
	{
	  gcc_assert (a < 64);
	  area ar = groups[g];
	  ar.half = h;
	  ar.last = order[k];
	  ar.lo = ar.hi = node->apb_off;
	  agrp[a] = g;
	  areas.safe_push (ar);
	}
      area &ar = areas[a];
      ar.hi = MAX (ar.hi, node->apb_off + node->apb_size);
      if (node->time > l->nodes[ar.last].time)
	ar.last = order[k];
      node->apb_area = a;
      node->apb_ind = node->apb_off - ar.lo;
    }
  /* The left half must hold at least as many areas as the right: an
     instruction's left half describes one (and ends the program).  */
  int nh[2] = { 0, 0 };
  for (area &ar : areas)
    nh[ar.half]++;
  if (nh[1] > nh[0])
    {
      for (area &ar : areas)
	ar.half ^= 1;
      std::swap (nh[0], nh[1]);
      for (int k = 0; k < n; k++)
	l->nodes[order[k]].apb_chan ^= 2;
    }
  /* Areas in each half in order; increments.  */
  int idx[2] = { 0, 0 }, num[64];
  l->apb_nincr = 0;
  for (unsigned a = 0; a < areas.length (); a++)
    {
      area &ar = areas[a];
      num[a] = idx[ar.half]++;
      HOST_WIDE_INT e = ar.step / ar.size;
      if (e != 1)
	{
	  int k = 1;
	  while (k <= l->apb_nincr && l->apb_incr[k] != e)
	    k++;
	  if (k > l->apb_nincr)
	    l->apb_incr[++l->apb_nincr] = e;
	  ar.incr = k;
	}
    }
  gcc_assert (l->apb_nincr <= 7 && nh[0] <= 32);
  for (int k = 0; k < n; k++)
    {
      e2k_ms_node *node = &l->nodes[order[k]];
      node->apb_am = areas[node->apb_area].last == order[k];
      node->apb_area = num[node->apb_area];
    }
  auto asz = [] (int k)
    {
      int a = 5;
      while (a > 0 && (k << a) > 32)
	a--;
      return a;
    };
  int as[2] = { asz (nh[0]), asz (MAX (nh[1], 1)) };
  /* disp is 32 bits that lcc never makes negative (it starts its areas
     through %aaind): a descriptor with an area that would start below
     its base (one read backwards) gets a base that much lower.  */
  for (int d = 0; d < 32; d++)
    l->apb_adj[d] = 0;
  for (area &ar : areas)
    l->apb_adj[ar.d] = MIN (l->apb_adj[ar.d],
			    ar.lo + (s - 1 - ar.stage) * ar.step);
  int m = ++e2k_apb_labelno;
  char buf[16384];
  int len = snprintf (buf, sizeof buf, "\t.align\t8\n.LAPB%d:\n", m);
  auto entry = [&] (const area &ar, int last)
    {
      int fmt = (ar.size == 1 ? 1 : ar.size == 2 ? 2 : ar.size == 4 ? 3
		 : 4);
      HOST_WIDE_INT disp = (ar.lo + (s - 1 - ar.stage) * ar.step
			    - l->apb_adj[ar.d]);
      int a = as[ar.half];
      int mrng = ar.hi - ar.lo;
      len += snprintf (buf + len, sizeof buf - len,
		       "\t  fapb\t%s=%d, dcd=0, fmt=%d, mrng=%d, d=%d, incr=%d, "
		       "ind=0, asz=%d, abs=%d, disp=%d\n",
		       ar.half ? "dpl" : "ct", last, fmt, mrng == 32 ? 0 : mrng,
		       ar.d, ar.incr, a, num[&ar - areas.address ()] << a,
		       (int) disp);
    };
  for (int k = 0; k < nh[0]; k++)
    {
      len += snprintf (buf + len, sizeof buf - len, "\t{\n");
      for (area &ar : areas)
	if (ar.half == 0 && num[&ar - areas.address ()] == k)
	  entry (ar, k == nh[0] - 1);
      for (area &ar : areas)
	if (ar.half == 1 && num[&ar - areas.address ()] == k)
	  entry (ar, 0);
      len += snprintf (buf + len, sizeof buf - len, "\t}\n");
    }
  gcc_assert (len < (int) sizeof buf);
  e2k_apb_progs.safe_push (xstrdup (buf));
  return m;
}

/* The increment registers of L's AAU stores, after those of array
   prefetch (e2k_ms_apb_assign), and their descriptors' adjustments: the
   offset, so that the base is the element of iteration 0.  */
static void
e2k_ms_staa_assign (e2k_ms_loop *l)
{
  if (!l->napb)
    l->apb_nincr = 0;
  for (int i = 0; i < l->n; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      if (!node->staa)
	continue;
      HOST_WIDE_INT e = node->apb_step / node->apb_size;
      int k = 0;
      if (e != 1)
	{
	  k = 1;
	  while (k <= l->apb_nincr && l->apb_incr[k] != e)
	    k++;
	  if (k > l->apb_nincr)
	    l->apb_incr[++l->apb_nincr] = e;
	}
      node->staa_incr = k;
      l->apb_adj[node->apb_d] = node->apb_off;
    }
  gcc_assert (l->apb_nincr <= 7);
}

/* Emit the pipelined loop: prologue before each of PRE_ENDS (a counted
   loop) or on each of ENTRIES (a while loop), kernel, copies out on
   EXIT_EDGE.  W: a two-block while loop's merge, else NULL.  False,
   with nothing changed, if the prologue can't be put in order.  */
bool
e2k_ms_emit (e2k_ms_loop *l, const vec<rtx_insn *> &pre_ends,
	     const vec<edge> &entries, edge exit_edge, const e2k_ms_wl *w)
{
  int ii = l->ii, s = l->stages;

  /* Prologue: the copies in and the first S - 1 stages of iterations
     0 .. S - 2, in the order the kernel would run them.  */
  auto_vec<e2k_ms_item> items;
  for (unsigned v = 0; v < l->values.length (); v++)
    for (int k = 1; k <= 2; k++)
      if (k == 1 ? l->values[v].carried : l->values[v].carried2)
	{
	  e2k_ms_item it = { -k * ii + l->nodes[l->values[v].node].time, -1,
			     -k, (int) v };
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
	  rtx dst = e2k_ms_reg (v.mode, e2k_ms_name (l, it.value, it.j, 0));
	  if (it.j == -1 && v.init_mem)
	    {
	      pats.quick_push (gen_rtx_SET (dst, copy_rtx (v.init_mem)));
	      continue;
	    }
	  unsigned r = v.init[-it.j - 1];
	  gcc_assert (r != INVALID_REGNUM);
	  pats.quick_push (gen_rtx_SET (dst, gen_rtx_REG (v.mode, r)));
	}
      else
	{
	  /* The prologue keeps an array prefetch node's load.  */
	  e2k_ms_node *nd = &l->nodes[it.node];
	  rtx_insn *keep = nd->insn;
	  if (nd->apb)
	    nd->insn = nd->orig;
	  pats.quick_push (e2k_ms_instance (l, it.node, it.j, 0));
	  nd->insn = keep;
	}
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
  int korder[E2K_MS_MAX_NODES], krow[E2K_MS_MAX_NODES], nk = 0;
  for (int i = 0; i < l->n; i++)
    {
      krow[i] = l->nodes[i].time % ii;
      if (!l->nodes[i].kdead)
	korder[nk++] = i;
    }
  e2k_ms_sort (korder, nk, krow);
  int apbno = l->napb ? e2k_ms_apb_assign (l) : 0;
  if (l->nstaa)
    e2k_ms_staa_assign (l);
  /* A failure from here on drops the program it queued.  */
  auto apb_fail = [&] ()
    {
      if (apbno)
	free (e2k_apb_progs.pop ());
      return false;
    };
  auto_vec<rtx> kpats (nk);
  for (int k = 0; k < nk; k++)
    {
      int i = korder[k];
      kpats.quick_push (e2k_ms_instance (l, i, s - 1 - l->nodes[i].time / ii,
					 0));
      e2k_ms_node *nd = &l->nodes[i];
      if (nd->apb)
	{
	  rtx u = SET_SRC (e2k_ms_set (kpats[k]));
	  XVECEXP (u, 0, 0) = GEN_INT (nd->apb_area);
	  XVECEXP (u, 0, 1) = GEN_INT (nd->apb_chan);
	  XVECEXP (u, 0, 3) = GEN_INT (nd->apb_ind);
	  XVECEXP (u, 0, 4) = GEN_INT (nd->apb_am);
	}
      if (nd->staa)
	{
	  rtx u = XEXP (SET_DEST (e2k_ms_set (kpats[k])), 0);
	  XVECEXP (u, 0, 0) = GEN_INT (nd->apb_d);
	  XVECEXP (u, 0, 1) = GEN_INT (nd->staa_sti);
	  XVECEXP (u, 0, 2) = GEN_INT (nd->apb_off - l->apb_adj[nd->apb_d]);
	  XVECEXP (u, 0, 3) = GEN_INT (nd->staa_incr);
	}
    }
  auto_vec<int> kseq (nk);
  for (int g = 0; g < nk; )
    {
      int ge = g;
      while (ge < nk && krow[korder[ge]] == krow[korder[g]])
	ge++;
      if (!e2k_ms_order_cycle (kpats, g, ge, &kseq))
	return apb_fail ();
      /* A check ends its wide instruction (and its block): last, after
	 what reads its register, and nothing after it may write what it
	 reads.  */
      for (int a = g; a < ge; a++)
	if (korder[kseq[a]] == l->kchk)
	  {
	    int kk = kseq[a];
	    for (int b = a; b + 1 < ge; b++)
	      {
		kseq[b] = kseq[b + 1];
		rtx db = SET_DEST (e2k_ms_set (kpats[kseq[b]]));
		if (REG_P (db) && e2k_ms_reads_p (kpats[kk], REGNO (db)))
		  return apb_fail ();
	      }
	    kseq[ge - 1] = kk;
	    break;
	  }
      g = ge;
    }

  /* What a failed check redoes: in time order, one time's instances as
     the kernel orders them.  */
  auto_vec<rtx> rpats (l->rec.length ());
  auto_vec<int> rseq (l->rec.length ());
  for (std::pair<int, int> &r : l->rec)
    rpats.quick_push (e2k_ms_instance (l, r.first, r.second, 0));
  for (unsigned g = 0; g < l->rec.length (); )
    {
      unsigned ge = g;
      auto t = [&] (unsigned x)
	{
	  return l->rec[x].second * ii + l->nodes[l->rec[x].first].time;
	};
      while (ge < l->rec.length () && t (ge) == t (g))
	ge++;
      if (!e2k_ms_order_cycle (rpats, g, ge, &rseq))
	return apb_fail ();
      g = ge;
    }

  /* The loop end's disp, if it was in the loop: each prologue starts
     with it.  */
  rtx ldisp = (w && w->bdisp ? copy_rtx (PATTERN (w->bdisp))
	       : l->edisp ? copy_rtx (PATTERN (l->edisp)) : NULL_RTX);
  auto emit_ldisp = [&] (rtx_insn *after)
    {
      rtx_insn *d = (after ? emit_insn_after (copy_rtx (ldisp), after)
		     : emit_insn (copy_rtx (ldisp)));
      rtx label = label_ref_label (XVECEXP (SET_SRC (ldisp), 0, 0));
      add_reg_note (d, REG_LABEL_OPERAND, label);
      LABEL_NUSES (label)++;
      if (recog_memoized (d) < 0)
	gcc_unreachable ();
      return d;
    };

  if (w)
    e2k_ms_wl_merge (l, w);

  /* Operations that print ",sm": all but stores, predicate logic, and
     lock and check loads (which print their own).  */
  auto spec_p = [&] (int i, bool kernel = false)
    {
      /* An array prefetch node: its load in the prologue, its mova
	 (which never traps) in the kernel.  */
      if (l->nodes[i].apb)
	return !kernel;
      enum attr_type t = get_attr_type (l->nodes[i].insn);
      return (!l->nodes[i].store && t != TYPE_PLOG && t != TYPE_LDLOCK
	      && t != TYPE_LDCHK);
    };

  /* The same prologue before each way into the loop.  */
  auto_vec<std::pair<rtx_insn *, int> > pro_insns;
  auto emit_prologue = [&] (bool copy)
    {
      emit_insn (e2k_ms_gen_setbn_enter (l));
      if (ldisp)
	emit_ldisp (NULL);
      for (int k : seq)
	{
	  rtx_insn *insn = emit_insn (copy ? copy_rtx (pats[k]) : pats[k]);
	  if (items[k].node >= 0)
	    {
	      INSN_LOCATION (insn)
		= INSN_LOCATION (l->nodes[items[k].node].insn);
	      if (spec_p (items[k].node))
		e2k_ms_set_flag (insn, E2K_MS_SM);
	      pro_insns.safe_push (std::make_pair (insn, items[k].node));
	    }
	  else
	    /* A copy in of a value the loop may leave with unchanged:
	       the register may hold a diagnostic value from a speculative
	       load that nothing reads on this way (xz's index_tree_next,
	       a register e2k_ms_move_b counts live at the first exit).  */
	    e2k_ms_set_flag (insn, E2K_MS_SM);
	  recog_memoized (insn);
	}
    };
  /* Better, a block of its own on each way in, with the cycles of the
     modulo schedule, which count the crossings between the clusters
     that sched-ebb doesn't; if each cycle holds what it gets, the
     copies in included.  setbn has a wide instruction of its own, and
     empty ones follow up to the kernel's first cycle if it comes
     next.  */
  int tmin = INT_MAX, tlast = INT_MIN;
  for (e2k_ms_item &it : items)
    {
      tmin = MIN (tmin, it.t);
      tlast = MAX (tlast, it.t);
    }
  bool clocked = ni > 0 && e2k_ms_clock_prologue;
  if (clocked)
    {
      state_t st = alloca (dfa_state_size);
      for (int g = 0; g < ni && clocked; )
	{
	  int ge = g;
	  state_reset (st);
	  for (; ge < ni && items[ge].t == items[g].t; ge++)
	    {
	      rtx_insn *x = (items[ge].node >= 0
			     ? (l->nodes[items[ge].node].apb
				? l->nodes[items[ge].node].orig
				: l->nodes[items[ge].node].insn)
			     : make_insn_raw (copy_rtx (pats[ge])));
	      if (recog_memoized (x) < 0 || state_transition (st, x) >= 0)
		clocked = false;
	    }
	  g = ge;
	}
    }
  int kstart = (s - 1) * ii;
  /* Where the clocked prologue's items go: their modulo times, or a
     list schedule of their own (e2k_ms_list_prologue) that starts the
     kernel PDELTA cycles sooner.  */
  auto_vec<int> pclock, oc, pseq;
  int pdelta = 0, plast = 1 + tlast - tmin + 1;
  for (int k = 0; k < ni; k++)
    oc.safe_push (items[k].t - tmin + 2);
  /* Only with v6 timing: on the 2C3 CoreMark ran 0.5% faster and
     zlib -9 0.6%, on the 8C2 zlib -9 1.1% slower (its loads cross
     between the clusters, which the prologue's channels don't model).  */
  bool listed = (clocked && e2k_ms_list_pro && E2K_LAT6
		 && e2k_ms_list_prologue (pats, seq, oc, &pclock, &plast));
  /* The kernel starts PDELTA cycles sooner: as soon as every value it
     reads from the prologue comes in time at the pipeliner's latencies
     (a copy in counts as its value's node).  What the prologue reads
     of the kernel's names it reads before the kernel runs.  */
  if (listed)
    {
      pdelta = INT_MAX;
      for (int k = 0; k < ni; k++)
	{
	  int i = (items[k].node >= 0 ? items[k].node
		   : l->values[items[k].value].node);
	  /* The kernel's channels keep a recurrence in one cluster
	     (e2k_ms_pipeline drops its crossing), the prologue's need
	     not: count the crossing on every edge into the kernel, as a
	     cycle late costs a 4-cycle stall.  */
	  enum attr_type pt = get_attr_type (l->nodes[i].insn);
	  int full = (pt == TYPE_FP || pt == TYPE_FMA || pt == TYPE_FFMA
		      || pt == TYPE_FCVT || pt == TYPE_FSCALE
		      || pt == TYPE_MUL || pt == TYPE_FLAG ? 2
		      : pt == TYPE_FLAGMUL || pt == TYPE_FCMP ? 0 : 1);
	  if (E2K_LAT6
	      && (pt == TYPE_LOAD || pt == TYPE_LDLOCK || pt == TYPE_LDCHK))
	    full = 0;
	  for (e2k_ms_dep &d : l->deps)
	    if (d.from == i)
	      {
		int jc = items[k].j + d.dist, tc = l->nodes[d.to].time;
		if (jc <= s - 2 && tc / ii < s - 1 - jc)
		  continue;
		int lat = d.lat - d.cross + full;
		pdelta = MIN (pdelta,
			      jc * ii + tc - tmin + 2 - lat - pclock[k]);
	      }
	}
      /* The kernel comes after the prologue's last cycle.  */
      pdelta = MIN (pdelta, (kstart - tmin + 2) - plast - 1);
    }
  if (!listed || pdelta <= 0)
    {
      pclock.truncate (0);
      for (int k = 0; k < ni; k++)
	pclock.safe_push (oc[k]);
      pdelta = 0;
      plast = 1 + tlast - tmin + 1;
    }
  for (int k : seq)
    pseq.safe_push (k);
  /* Emitted in clock order; within a cycle as SEQ has them.  */
  for (int a = 1; a < ni; a++)
    for (int b = a; b > 0 && pclock[pseq[b - 1]] > pclock[pseq[b]]; b--)
      std::swap (pseq[b - 1], pseq[b]);
  auto_vec<std::pair<basic_block, rtx_insn *> > pblocks;
  auto emit_clocked = [&] (edge e, bool copy)
    {
      basic_block p = e2k_ms_split_entry (e);
      p->flags |= BB_DISABLE_SCHEDULE;
      rtx_insn *x = BB_END (p);
      if (JUMP_P (x))
	x = PREV_INSN (x);
      x = emit_insn_after (e2k_ms_gen_setbn_enter (l), x);
      e2k_ms_clock c0 = { x, 1 };
      e2k_ms_clocks.safe_push (c0);
      /* With the first cycle: nothing else of a loop uses CS0.  */
      if (ldisp)
	{
	  x = emit_ldisp (x);
	  e2k_ms_clock cd = { x, 2 };
	  e2k_ms_clocks.safe_push (cd);
	}
      for (int k : pseq)
	{
	  x = emit_insn_after (copy ? copy_rtx (pats[k]) : pats[k], x);
	  if (items[k].node >= 0)
	    {
	      INSN_LOCATION (x) = INSN_LOCATION (l->nodes[items[k].node].insn);
	      if (spec_p (items[k].node))
		e2k_ms_set_flag (x, E2K_MS_SM);
	      pro_insns.safe_push (std::make_pair (x, items[k].node));
	    }
	  else
	    /* A copy in, as in emit_prologue.  */
	    e2k_ms_set_flag (x, E2K_MS_SM);
	  recog_memoized (x);
	  e2k_ms_clock c = { x, pclock[k] };
	  e2k_ms_clocks.safe_push (c);
	}
      pblocks.safe_push (std::make_pair (p, x));
      return plast;
    };
  /* Array prefetch: on each way in, after rwd %lsr (the unit follows
     the count after a trap), each descriptor's base, the address there
     (an area's DISP adds the rest), and the increments; the program
     into %ctpr2; bap.  The prologue's cycles count towards the 22 a
     first mova would wait.  */
  auto_vec<basic_block> apb_pre;
  for (rtx_insn *pre_end : pre_ends)
    apb_pre.safe_push (BLOCK_FOR_INSN (pre_end));
  /* A descriptor's base is its induction variable, written as it is, or
     that plus an invariant or an adjustment (apb_adj), which goes
     through the temporary; so does each increment.  The AAU writes are
     barriers to the scheduler: when the temporary takes one value, set
     it before the first of them.  */
  rtx t = gen_rtx_REG (DImode, l->apb_tmp);
  /* AAU stores' descriptors follow array prefetch's; their store
     indices start at 0, which goes through the temporary too.  */
  int ndesc = l->napb_d + l->nstaa_d;
  auto aau_p = [&] (int i) { return l->nodes[i].apb || l->nodes[i].staa; };
  int ntmp = l->apb_nincr + (l->nstaa > 0), d_tmp = -1;
  for (int d = 0; d < ndesc; d++)
    for (int i = 0; i < l->n; i++)
      if (aau_p (i) && l->nodes[i].apb_d == d)
	{
	  if (l->nodes[i].apb_inv != INVALID_REGNUM
	      || l->nodes[i].apb_inv2 != INVALID_REGNUM || l->apb_adj[d])
	    ntmp++, d_tmp = i;
	  break;
	}
  bool early = ntmp == 1;
  /* A register the setup reads: an invariant in %b[0..7] from the
     register it was copied to before setbn (L->bmap), as the setup may
     come after setbn: on v6 the listed prologue takes in the setup's
     block, and NPB LU's ssor then made a descriptor of a fresh ring
     register, a diagnostic value (SIGILL at the first store of a movad's
     data on the 2C3).  */
  auto setup_reg = [&] (unsigned r)
      {
	if (B_REGNO_P (r) && (l->binv & (1u << (r - B0_REGNUM))))
	  r = l->bmap[r - B0_REGNUM];
	gcc_assert (!B_REGNO_P (r) && !BX_REGNO_P (r));
	return gen_rtx_REG (DImode, r);
      };
  /* The base of NODE's descriptor into the temporary.  */
  auto apb_base = [&] (e2k_ms_node *node)
      {
	rtx iv = setup_reg (node->apb_iv);
	HOST_WIDE_INT adj = l->apb_adj[node->apb_d];
	if (node->apb_inv != INVALID_REGNUM)
	  {
	    emit_insn (gen_adddi3 (t, iv, setup_reg (node->apb_inv)));
	    if (node->apb_inv2 != INVALID_REGNUM)
	      emit_insn (gen_adddi3 (t, t, setup_reg (node->apb_inv2)));
	    if (adj)
	      emit_insn (gen_adddi3 (t, t, gen_int_mode (adj, DImode)));
	  }
	else
	  emit_insn (gen_adddi3 (t, iv, gen_int_mode (adj, DImode)));
      };
  /* The temporary's one value.  */
  auto apb_early = [&] ()
      {
	start_sequence ();
	if (d_tmp >= 0)
	  apb_base (&l->nodes[d_tmp]);
	else if (l->apb_nincr)
	  emit_move_insn (t, gen_int_mode (l->apb_incr[1], DImode));
	else
	  emit_move_insn (t, const0_rtx);
	return end_sequence ();
      };
  /* The setup, with ldisp if LDISP, after the temporary's value if
     SET_EARLY.  */
  auto apb_seq = [&] (bool ldisp, bool set_early)
      {
	rtx_insn *pre = early && set_early ? apb_early () : NULL;
	start_sequence ();
	/* The program first: bap waits 5 cycles for it, which the AAU
	   writes then fill (e2k_adjust_cost lets them share).  */
	if (ldisp && l->napb && e2k_aau_setup_war)
	  emit_insn (gen_e2k_ldisp_apb (GEN_INT (apbno)));
	if (pre)
	  emit_insn (pre);
	for (int d = 0; d < ndesc; d++)
	  for (int i = 0; i < l->n; i++)
	    if (aau_p (i) && l->nodes[i].apb_d == d)
	      {
		e2k_ms_node *node = &l->nodes[i];
		rtx iv = setup_reg (node->apb_iv);
		if (node->apb_inv == INVALID_REGNUM
		    && node->apb_inv2 == INVALID_REGNUM && !l->apb_adj[d])
		  emit_insn (gen_e2k_aaurwd (iv, GEN_INT (d)));
		else
		  {
		    if (!early)
		      apb_base (node);
		    emit_insn (gen_e2k_aaurwd (t, GEN_INT (d)));
		  }
		break;
	      }
	for (int k = 1; k <= l->apb_nincr; k++)
	  {
	    if (!early)
	      emit_move_insn (t, gen_int_mode (l->apb_incr[k], DImode));
	    emit_insn (gen_e2k_aaurw_incr (t, GEN_INT (k)));
	  }
	if (l->nstaa)
	  {
	    if (!early)
	      emit_move_insn (t, const0_rtx);
	    for (int k = 0; k < l->nstaa; k++)
	      emit_insn (gen_e2k_aaurw_sti (t, GEN_INT (k)));
	  }
	if (l->napb)
	  {
	    if (ldisp && !e2k_aau_setup_war)
	      emit_insn (gen_e2k_ldisp_apb (GEN_INT (apbno)));
	    emit_insn (gen_e2k_bap ());
	  }
	rtx_insn *seq = end_sequence ();
	for (rtx_insn *x = seq; x; x = NEXT_INSN (x))
	  if (recog_memoized (x) < 0)
	    gcc_unreachable ();
	return seq;
      };
  auto apb_setup = [&] (edge e)
      {
	/* In a block of its own on the way in: the block of rwd %lsr may
	   end in a branch through %ctpr2.  */
	basic_block q = split_edge (e);
	emit_insn_after (apb_seq (true, true), BB_END (q));
      };
  /* %b[] invariants into their registers before setbn renames %b[].  */
  for (int k = 0; k < 8; k++)
    if (l->binv & (1u << k))
      for (rtx_insn *pre_end : pre_ends)
	recog_memoized (emit_insn_before
			(gen_rtx_SET (gen_rtx_REG (DImode, l->bmap[k]),
				      gen_rtx_REG (DImode, B0_REGNUM + k)),
			 pre_end));
  for (unsigned p = 0; p < pre_ends.length (); p++)
    if (clocked)
      {
	rtx_insn *pre_end = pre_ends[p];
	basic_block pb = BLOCK_FOR_INSN (pre_end);
	int cycles = emit_clocked (find_edge (pb, l->bb), p > 0);
	/* The prologue gives %lsr its 4 cycles after rwd.  */
	if (cycles >= 4 && single_succ_p (pb))
	  delete_insn (pre_end);
      }
    else
      {
	start_sequence ();
	emit_prologue (p > 0);
	rtx_insn *pro = end_sequence ();
	emit_insn_before (pro, pre_ends[p]);
      }
  for (unsigned p = 0; p < entries.length (); p++)
    if (clocked)
      emit_clocked (entries[p], p > 0 || pre_ends.length () > 0);
    else
      {
	start_sequence ();
	emit_prologue (p > 0 || pre_ends.length () > 0);
	rtx_insn *pro = end_sequence ();
	edge e = entries[p];
	if (!(e->flags & EDGE_FALLTHRU) && !single_succ_p (e->src))
	  {
	    basic_block nb = e2k_ms_split_entry (e);
	    emit_insn_after (pro, BB_END (nb));
	  }
	else
	  insert_insn_on_edge (pro, e);
      }
  /* The array prefetch setup on each way in: between the block of rwd
     %lsr and the prologue (or the loop).  A prologue in that block
     itself (not clocked) would then run before bap, and the kernel's
     first movas wait out bap's 22 cycles (Linpack's daxpy, about 20
     cycles a call): there right after rwd %lsr, unless something after
     it uses %ctpr2, which ldisp sets.  */
  if (l->napb || l->nstaa)
    for (basic_block pb : apb_pre)
      {
	rtx_insn *rwd = NULL;
	if (!clocked)
	  {
	    rtx ctpr2 = gen_rtx_REG (DImode, CTPR2_REGNUM);
	    for (rtx_insn *x = BB_END (pb); x != PREV_INSN (BB_HEAD (pb));
		 x = PREV_INSN (x))
	      if (NONDEBUG_INSN_P (x))
		{
		  if (e2k_rwd_lsr_p (x))
		    {
		      rwd = x;
		      break;
		    }
		  if (CALL_P (x) || reg_mentioned_p (ctpr2, PATTERN (x))
		      || reg_set_p (ctpr2, x))
		    break;
		}
	  }
	if (rwd)
	  {
	    /* ldisp at the block's head, where it has the count's chain
	       to cover its 5 cycles to bap, if nothing before rwd uses
	       %ctpr2 or calls.  */
	    rtx ctpr2 = gen_rtx_REG (DImode, CTPR2_REGNUM);
	    bool head = l->napb > 0;
	    for (rtx_insn *x = BB_HEAD (pb); x != rwd; x = NEXT_INSN (x))
	      if (NONDEBUG_INSN_P (x)
		  && (CALL_P (x) || reg_mentioned_p (ctpr2, PATTERN (x))
		      || reg_set_p (ctpr2, x)))
		head = false;
	    if (head)
	      emit_insn_after (gen_e2k_ldisp_apb (GEN_INT (apbno)),
			       bb_note (pb));
	    /* After the copies e2k_ms_move_b put after rwd into registers
	       the setup reads (NPB SP: a %b[] invariant moved into the
	       register that had held the count).  */
	    rtx_insn *after = rwd;
	    for (rtx_insn *x = NEXT_INSN (rwd); x != NEXT_INSN (BB_END (pb));
		 x = NEXT_INSN (x))
	      if (NONDEBUG_INSN_P (x))
		for (int i = 0; i < l->n; i++)
		  if (aau_p (i)
		      && (reg_set_p (gen_rtx_REG (DImode, l->nodes[i].apb_iv), x)
			  || (l->nodes[i].apb_inv != INVALID_REGNUM
			      && reg_set_p (gen_rtx_REG (DImode,
							 l->nodes[i].apb_inv),
					    x))
			  || (l->nodes[i].apb_inv2 != INVALID_REGNUM
			      && reg_set_p (gen_rtx_REG (DImode,
							 l->nodes[i].apb_inv2),
					    x))))
		    {
		      after = x;
		      break;
		    }
	    /* rwd is a barrier too: set the temporary before it, unless
	       it is the register rwd reads (e2k_ms_apb_ok may take one
	       the loop's way in uses), or its value comes after.  */
	    bool before = (early && after == rwd
			   && !reg_overlap_mentioned_p (t, PATTERN (rwd)));
	    if (before)
	      emit_insn_before (apb_early (), rwd);
	    emit_insn_after (apb_seq (!head, !before), after);
	    continue;
	  }
	edge e, way = NULL;
	edge_iterator ei;
	FOR_EACH_EDGE (e, ei, pb->succs)
	  {
	    if (e->dest == l->bb)
	      way = e;
	    for (std::pair<basic_block, rtx_insn *> &b : pblocks)
	      if (e->dest == b.first)
		way = e;
	  }
	gcc_assert (way);
	apb_setup (way);
      }
  /* The prologue that falls into the kernel waits for its first cycle;
     the others jump there through the CTPR the loop end uses, which
     holds the kernel's address already (an ibranch costs 6 cycles).  */
  rtx lctpr = NULL_RTX;
  {
    subrtx_iterator::array_type array;
    FOR_EACH_SUBRTX (iter, array, PATTERN (l->jump), NONCONST)
      if (REG_P (*iter) && CTPR_REGNO_P (REGNO (*iter)))
	lctpr = const_cast<rtx> (*iter);
  }
  for (std::pair<basic_block, rtx_insn *> &pb : pblocks)
    {
      basic_block p = pb.first;
      rtx_insn *end = BB_END (p);
      if (!JUMP_P (end))
	{
	  int gap = (kstart - tmin + 2 - pdelta) - plast - 1;
	  if (gap > 0)
	    emit_insn_after (gen_e2k_nop_bundle (GEN_INT (MIN (gap, 8) - 1)),
			     pb.second);
	}
      else if (lctpr && simplejump_p (end))
	{
	  rtx label = JUMP_LABEL (end);
	  PATTERN (end)
	    = gen_rtx_PARALLEL (VOIDmode,
				gen_rtvec (2, gen_rtx_SET (pc_rtx,
							   gen_rtx_LABEL_REF
							   (Pmode, label)),
					   gen_rtx_USE (VOIDmode, lctpr)));
	  INSN_CODE (end) = -1;
	  if (recog_memoized (end) < 0)
	    gcc_unreachable ();
	  df_insn_rescan (end);
	}
    }

  /* Empty first cycles of the kernel are an empty wide instruction.  */
  int row0 = ii;
  for (int i = 0; i < l->n; i++)
    if (!l->nodes[i].kdead)
      row0 = MIN (row0, l->nodes[i].time % ii);
  /* The loop end may read its predicate in the wide instruction that
     sets it for the next iteration: tell dataflow it comes in.  */
  if (l->wl && l->npred)
    {
      /* The loop end reads the stay predicate of the iteration whose
	 last stage this is, under its name now; dataflow doesn't know
	 the ring rotates (uses of all of it at the loop end, below).  */
      rtx cond = e2k_ms_jump_cond (l->jump);
      XEXP (cond, 0) = gen_rtx_REG (BImode,
				    PRED0_REGNUM + e2k_ms_pname (l, l->stay,
								 0, 0));
      INSN_CODE (l->jump) = -1;
      if (recog_memoized (l->jump) < 0)
	gcc_unreachable ();
      df_insn_rescan (l->jump);
    }
  else if (l->wl)
    emit_insn_before (gen_rtx_USE (VOIDmode,
				   SET_DEST (PATTERN (l->nodes[l->stay].insn))),
		      l->jump);
  if (row0 > 0)
    emit_insn_before (gen_e2k_nop_bundle (GEN_INT (row0 - 1)), l->jump);
  rtx_code_label *rlabel = l->kchk >= 0 ? gen_label_rtx () : NULL;
  rtx_insn *kinsn = NULL;
  rtx_insn *kins[E2K_MS_MAX_NODES];
  for (int k : kseq)
    {
      int i = korder[k];
      rtx_insn *insn;
      if (i == l->kchk)
	{
	  /* The check, with its rbranch to the compensation code.  */
	  rtx br = gen_rtx_SET (pc_rtx,
				gen_rtx_IF_THEN_ELSE
				(VOIDmode,
				 gen_rtx_NE (VOIDmode,
					     gen_rtx_UNSPEC (VOIDmode,
							     gen_rtvec (1, const0_rtx),
							     UNSPEC_MLOCK),
					     const0_rtx),
				 gen_rtx_LABEL_REF (Pmode, rlabel), pc_rtx));
	  insn = emit_jump_insn_before (gen_rtx_PARALLEL
					(VOIDmode,
					 gen_rtvec (2, e2k_ms_set (kpats[k]), br)),
					l->jump);
	  JUMP_LABEL (insn) = rlabel;
	  LABEL_NUSES (rlabel)++;
	  kinsn = insn;
	}
      else
	insn = emit_insn_before (kpats[k], l->jump);
      INSN_LOCATION (insn) = INSN_LOCATION (l->nodes[i].insn);
      if (recog_memoized (insn) < 0)
	gcc_unreachable ();
      if (spec_p (i, true))
	e2k_ms_set_flag (insn, E2K_MS_SM);
      e2k_ms_clock c = { insn, l->nodes[i].time % ii + 1 };
      e2k_ms_clocks.safe_push (c);
      kins[i] = insn;
    }
  for (std::pair<rtx_insn *, int> &pi : pro_insns)
    {
      if (l->nodes[pi.second].kdead)
	continue;
      unsigned uid = INSN_UID (pi.first);
      if (uid >= e2k_ms_twin.length ())
	e2k_ms_twin.safe_grow_cleared (uid + 64);
      e2k_ms_twin[uid] = INSN_UID (kins[pi.second]);
    }
  /* Dataflow doesn't know that the old %b[N] is the new %b[N + 2]: to
     it, the values the next iteration reads under another name are
     dead (and the prologue's too).  Use every name at the loop end.  */
  for (int name = 0; name < 2 * l->pairs; name++)
    emit_insn_before (gen_rtx_USE (VOIDmode, e2k_ms_reg (DImode, name)),
		      l->jump);
  for (int name = 0; name < l->npred; name++)
    emit_insn_before (gen_rtx_USE (VOIDmode,
				   gen_rtx_REG (BImode, PRED0_REGNUM + name)),
		      l->jump);
  e2k_ms_clock c = { l->jump, ii };
  e2k_ms_clocks.safe_push (c);
  e2k_ms_set_flag (l->jump, E2K_MS_ABN | (l->npred ? E2K_MS_ABP : 0));
  for (rtx_insn *insn : l->insns)
    delete_insn (insn);
  if (l->edisp)
    delete_insn (l->edisp);
  rtx_insn *insn, *next;
  for (insn = BB_HEAD (l->bb); insn != NEXT_INSN (BB_END (l->bb));
       insn = next)
    {
      next = NEXT_INSN (insn);
      if (DEBUG_INSN_P (insn))
	delete_insn (insn);
    }
  l->bb->flags |= BB_DISABLE_SCHEDULE;
  if (!kinsn)
    {
      e2k_ms_kernels.safe_push (std::make_pair (l->bb->index, -1));
      e2k_ms_kernel_rings.safe_push (2 * l->pairs);
    }

  if (kinsn)
    {
      /* The check ends a block of the kernel; the compensation code,
	 at the end of the function, jumps back to the rest.  */
      basic_block k1 = l->bb;
      basic_block k2 = split_block (k1, kinsn)->dest;
      k2->flags |= BB_DISABLE_SCHEDULE;
      e2k_ms_kernels.safe_push (std::make_pair (k1->index, k2->index));
      e2k_ms_kernel_rings.safe_push (2 * l->pairs);
      rtx_code_label *k2label = block_label (k2);
      /* Empty rows between the check and the next instruction.  */
      int krow0 = l->nodes[l->kchk].time % ii, first = ii - 1;
      for (int i = 0; i < l->n; i++)
	if (l->nodes[i].time % ii > krow0)
	  first = MIN (first, l->nodes[i].time % ii);
      if (first > krow0 + 1)
	emit_insn_after (gen_e2k_nop_bundle (GEN_INT (first - krow0 - 2)),
			 NEXT_INSN (BB_HEAD (k2)));
      /* As at the kernel's start, the loop end's predicate comes in
	 (from the compensation code too).  */
      if (l->wl)
	emit_insn_after (gen_rtx_USE (VOIDmode,
				      SET_DEST (PATTERN (l->nodes[l->stay].insn))),
			 NEXT_INSN (BB_HEAD (k2)));
      rtx_insn *last = get_last_insn ();
      if (!BARRIER_P (last))
	last = emit_barrier_after (last);
      rtx_insn *head = emit_label_after (rlabel, last);
      rtx_insn *cur = head;
      for (unsigned q : rseq)
	{
	  int n = l->rec[q].first;
	  cur = emit_insn_after (rpats[q], cur);
	  INSN_LOCATION (cur) = INSN_LOCATION (l->nodes[n].insn);
	  if (recog_memoized (cur) < 0)
	    gcc_unreachable ();
	  if (spec_p (n))
	    e2k_ms_set_flag (cur, E2K_MS_SM);
	}
      rtx_insn *j = emit_jump_insn_after (gen_jump (k2label), cur);
      JUMP_LABEL (j) = k2label;
      LABEL_NUSES (k2label)++;
      /* Back by an ibranch, as lcc's compensation code goes: a prepared
	 transfer would need a CTPR, and writing %ctpr2 stops the loop's
	 array prefetch program (spec/isa/apb.md).  */
      if (e2k_dam_apb)
	e2k_ms_set_flag (j, E2K_MS_IBRANCH);
      emit_barrier_after (j);
      basic_block r
	= create_basic_block (head, j, EXIT_BLOCK_PTR_FOR_FN (cfun)->prev_bb);
      r->count = profile_count::zero ();
      make_edge (k1, r, 0)->probability = profile_probability::never ();
      make_edge (r, k2, 0);
    }

  /* After the loop: the last iteration's values, then the outgoing
     registers back.  The kernel ran n times, so a value defined in
     stage D of iteration n - 1 has rotated S - D times since.  A
     two-block while loop's values at the end of its second block may be
     diagnostic when its first block's exit was taken (copied with ,sm);
     its first block's exit compare runs again and its values there are
     copied over them under its condition.  */
  /* Every copy out is speculative: what it copies may be a diagnostic
     value nothing reads after this exit (a value copied in that the
     loop left unchanged, xz's index_tree_next).  */
  auto copy_out = [&] (e2k_ms_out &o)
    {
      machine_mode m = o.mode;
      rtx_insn *cp
	= emit_insn (gen_rtx_SET (gen_rtx_REG (m, o.regno),
				  e2k_ms_reg (m, e2k_ms_exit_name (l, o.value,
								   o.dist))));
      e2k_ms_set_flag (cp, E2K_MS_SM);
      return cp;
    };
  if (l->x1)
    {
      /* The exits go to different places: run the first block's exit
	 test again and branch, each way with its own copies.  */
      gcc_assert (!exit_edge->insns.r);
      basic_block x2 = exit_edge->dest;
      basic_block d = split_edge (exit_edge);
      rtx_insn *cmp = e2k_ms_emit_exit_test (l, BB_END (d));
      rtx label = block_label (l->x1);
      rtx cond = gen_rtx_fmt_ee (l->e1, VOIDmode, w->p1, const0_rtx);
      rtx_insn *j
	= emit_jump_insn_after (gen_rtx_SET (pc_rtx,
					     gen_rtx_IF_THEN_ELSE
					     (VOIDmode, cond,
					      gen_rtx_LABEL_REF (Pmode, label),
					      pc_rtx)), cmp);
      JUMP_LABEL (j) = label;
      LABEL_NUSES (label)++;
      if (recog_memoized (cmp) < 0 || recog_memoized (j) < 0)
	gcc_unreachable ();
      edge e2 = single_succ_edge (d);
      edge e1 = make_edge (d, l->x1, 0);
      e1->probability = profile_probability::even ();
      e2->probability = profile_probability::even ();
      for (int way = 1; way <= 2; way++)
	{
	  start_sequence ();
	  for (e2k_ms_out &o : l->outs)
	    if (o.hend == (way == 1))
	      copy_out (o);
	  emit_insn (gen_e2k_setbn_leave ());
	  rtx_insn *seq = end_sequence ();
	  for (rtx_insn *x = seq; x; x = NEXT_INSN (x))
	    if (recog_memoized (x) < 0)
	      gcc_unreachable ();
	  insert_insn_on_edge (seq, way == 1 ? e1 : find_edge (d, x2));
	}
      return true;
    }
  start_sequence ();
  /* The end of the array prefetch program, as lcc ends one.  */
  if (l->napb)
    {
      /* aaurw takes a register (gas); the setup's is dead here too.  */
      rtx t = gen_rtx_REG (DImode, l->apb_tmp);
      emit_move_insn (t, const0_rtx);
      emit_insn (gen_e2k_apb_stop ());
      emit_insn (gen_e2k_aabf (t));
    }
  for (e2k_ms_out &o : l->outs)
    if (!o.hend)
      copy_out (o);
  if (w)
    {
      bool any = false;
      for (e2k_ms_out &o : l->outs)
	any |= o.hend;
      if (any)
	{
	  e2k_ms_emit_exit_test (l, NULL);
	  for (e2k_ms_out &o : l->outs)
	    if (o.hend)
	      {
		machine_mode m = e2k_ms_copy_mode (o.mode);
		rtx cond = gen_rtx_fmt_ee (l->e1, VOIDmode, w->p1, const0_rtx);
		rtx set
		  = gen_rtx_SET (gen_rtx_REG (m, o.regno),
				 e2k_ms_reg (m, e2k_ms_exit_name (l, o.value,
								  o.dist)));
		e2k_ms_set_flag (emit_insn (gen_rtx_COND_EXEC (VOIDmode, cond,
							       set)),
				 E2K_MS_SM);
	      }
	}
    }
  emit_insn (gen_e2k_setbn_leave ());
  rtx_insn *after = end_sequence ();
  for (insn = after; insn; insn = NEXT_INSN (insn))
    if (recog_memoized (insn) < 0)
      gcc_unreachable ();
  /* Before what e2k_ms_move_b put on the edge.  */
  rtx_insn *old = exit_edge->insns.r;
  exit_edge->insns.r = NULL;
  insert_insn_on_edge (after, exit_edge);
  if (old)
    insert_insn_on_edge (old, exit_edge);
  return true;
}

/* Stores run in the last stage only (never in the prologue), long after
   the step of the register their address is in: that register's value
   then lives through every stage, a name of the ring for each cycle in
   II.  Let a store read instead the instance of the latest iteration
   whose step it may, with its offset that many steps lower, and that
   value lives a stage.  Linpack's unrolled daxpy (v5, II 2): eleven
   names fewer, II 3 -> 2.  Only when the ring is too big without it:
   in the generic v3 daxpy, whose ring fits anyway, the same addresses
   at the same times ran 28% slower on the 8C2 (4.8 -> 6.1 cycles an
   iteration, cause unknown).  UNDO puts the uses back for another II.
   Not with a lock load, whose check's plan follows uses
   (e2k_ms_dam_plan).  */
void
e2k_ms_rebase_stores (e2k_ms_loop *l, bool undo)
{
  for (int i = 0; i < l->n; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      if (undo)
	{
	  if (node->rebase_off)
	    node->uses[node->rebase_use].dist = node->rebase_dist0;
	  node->rebase_off = 0;
	  continue;
	}
      if (!node->store || l->kchk >= 0 || GET_CODE (PATTERN (node->insn)) != SET)
	continue;
      rtx set = PATTERN (node->insn), addr = XEXP (SET_DEST (set), 0);
      rtx base = GET_CODE (addr) == PLUS ? XEXP (addr, 0) : addr;
      if (!REG_P (base)
	  || (GET_CODE (addr) == PLUS && !CONST_INT_P (XEXP (addr, 1)))
	  || reg_mentioned_p (base, SET_SRC (set)))
	continue;
      int k = 0;
      while (k < node->nuses
	     && (node->uses[k].regno != REGNO (base) || node->uses[k].pred))
	k++;
      if (k == node->nuses || node->uses[k].value < 0)
	continue;
      int v = node->uses[k].value, dn = l->values[v].node;
      e2k_ms_node *def = &l->nodes[dn];
      rtx dset = single_set (def->insn);
      /* An induction step: r = r + C, reading nothing else of the loop.  */
      if (!dset || dset != PATTERN (def->insn) || !REG_P (SET_DEST (dset))
	  || REGNO (SET_DEST (dset)) != REGNO (base)
	  || GET_CODE (SET_SRC (dset)) != PLUS
	  || !rtx_equal_p (XEXP (SET_SRC (dset), 0), SET_DEST (dset))
	  || !CONST_INT_P (XEXP (SET_SRC (dset), 1)))
	continue;
      bool own = true;
      for (int u = 0; u < def->nuses; u++)
	if (def->uses[u].pred
	    || (def->uses[u].value >= 0 && def->uses[u].value != v))
	  own = false;
      if (!own)
	continue;
      int lat = 1;
      for (e2k_ms_dep &d : l->deps)
	if (d.from == dn && d.to == i)
	  lat = MAX (lat, d.lat);
      /* Iteration n's store at T + n II may read the instance of
	 iteration n + A, stepped at TD + (n + A) II + LAT.  */
      int a = (node->time - def->time - lat) / l->ii;
      int d0 = node->uses[k].dist, adv = d0 + a;
      if (node->time - def->time - lat < 0 || adv <= 0)
	continue;
      HOST_WIDE_INT off = adv * INTVAL (XEXP (SET_SRC (dset), 1));
      if (off == 0)
	continue;
      /* Not for a literal more.  */
      rtx nm = adjust_address_nv (SET_DEST (set), GET_MODE (SET_DEST (set)),
				  -off);
      rtx_insn *ni = make_insn_raw (gen_rtx_SET (nm, SET_SRC (set)));
      if (recog_memoized (ni) < 0
	  || e2k_insn_lits (ni) > e2k_insn_lits (node->insn))
	continue;
      node->rebase_use = k;
      node->rebase_dist0 = d0;
      node->rebase_off = off;
      node->uses[k].dist = -a;
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: store %d reads its address "
		 "%d iterations on, offset %d\n", INSN_UID (node->insn), adv,
		 (int) -off);
    }
}
