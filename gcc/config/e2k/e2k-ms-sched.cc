/* Software pipelining for the Elbrus (E2K) port (see e2k-ms.cc):
   the modulo schedule (the operations placed in a reservation table of
   II rows), the DAM plan, and the names of rotating registers.
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

/* Sort ORDER[0..N) stably by KEY[ORDER[i]].  */
void
e2k_ms_sort (int *order, int n, const int *key)
{
  for (int i = 1; i < n; i++)
    for (int k = i; k > 0 && key[order[k - 1]] > key[order[k]]; k--)
      std::swap (order[k - 1], order[k]);
}


int
e2k_ms_item_cmp (const void *a, const void *b, void *)
{
  return (((const e2k_ms_item *) a)->t - ((const e2k_ms_item *) b)->t);
}

/* Whether node I of L at time T would issue a divide a cycle before or
   after another one placed: a row's DFA state sees only its own cycle,
   and the divider stays busy the next (spec/isa/timing.md, "Divider":
   divides 1 cycle apart stall 4).  */
static bool
e2k_ms_div_clash (e2k_ms_loop *l, int ii, int i, int t)
{
  if (get_attr_type (l->nodes[i].insn) != TYPE_FDIV)
    return false;
  for (int j = 0; j < l->n; j++)
    if (j != i && l->nodes[j].time != INT_MIN
	&& get_attr_type (l->nodes[j].insn) == TYPE_FDIV)
      {
	int d = ((t - l->nodes[j].time) % ii + ii) % ii;
	if (d == 1 || d == ii - 1)
	  return true;
      }
  return false;
}

/* Try to put node I of L at time T in the reservation rows ROWS.  */
static bool
e2k_ms_place (e2k_ms_loop *l, int ii, char *rows, state_t tmp, int i, int t)
{
  char *row = rows + (((t % ii) + ii) % ii) * dfa_state_size;
  if (e2k_ms_div_clash (l, ii, i, t))
    return false;
  memcpy (tmp, row, dfa_state_size);
  if (state_transition (tmp, l->nodes[i].insn) >= 0)
    return false;
  memcpy (row, tmp, dfa_state_size);
  l->nodes[i].time = t;
  return true;
}

/* Place a while loop's exit test after its other nodes: the loop end
   is in the last row of the last stage, no node later, and it reads the
   predicate of node L->stay 3 cycles or more after it is set
   (spec/isa/timing.md).  Predicates don't rotate, so each one lives at
   most II cycles: the next iteration sets it II later, which a read in
   that same cycle doesn't see yet.  The exit test is a tree of nodes
   setting predicates: compares at the leaves, landps above them (a
   two-block loop's, and those of merged chains), each read 1 cycle or
   more after it is set.  Sets *TJUMP to the loop end's time.  */
static bool
e2k_ms_place_exit (e2k_ms_loop *l, int ii, char *rows, state_t tmp,
		   int *tjump)
{
  int n = l->n, s = l->stay, maxt = 0;
  int early[E2K_MS_MAX_NODES];
  for (int i = 0; i < n; i++)
    {
      early[i] = 0;
      if (!l->nodes[i].pred)
	maxt = MAX (maxt, l->nodes[i].time);
    }
  for (e2k_ms_dep &d : l->deps)
    if (l->nodes[d.to].pred && !l->nodes[d.from].pred)
      early[d.to] = MAX (early[d.to],
			 l->nodes[d.from].time + d.lat - ii * d.dist);
  /* Through the landps (a node's predicates come from nodes before it
     in the body).  */
  for (int i = 0; i < n; i++)
    for (e2k_ms_dep &d : l->deps)
      if (d.to == i && l->nodes[i].pred && l->nodes[d.from].pred)
	early[i] = MAX (early[i], early[d.from] + d.lat);
  int es = early[s];
  int tj = MAX (maxt, es + 3);
  tj += ((ii - 1 - tj % ii) % ii + ii) % ii;
  char *save = XALLOCAVEC (char, ii * dfa_state_size);
  memcpy (save, rows, ii * dfa_state_size);
  int pt[E2K_MS_MAX_NODES];
  /* With rotating predicates (e2k_ms_assign_pnames) one may live longer
     than II: then the stay node and the others go as late as they can,
     for short lives in the ring.  */
  bool rot = e2k_rotate_preds;
  for (int tries = 0; tries < 3; tries++, tj += ii)
    for (int ts = tj - 3; ts >= (rot ? es : MAX (tj - ii, es)); ts--)
      {
	memcpy (rows, save, ii * dfa_state_size);
	if (!e2k_ms_place (l, ii, rows, tmp, s, ts))
	  continue;
	for (int i = 0; i < n; i++)
	  pt[i] = INT_MIN;
	pt[s] = ts;
	/* The others from the top down: after their own predicates (as
	   early as that allows), before every reader, and at most II
	   before the last of them.  */
	bool ok = true;
	for (int c = n - 1; ok && c >= 0; c--)
	  {
	    if (c == s || !l->nodes[c].pred)
	      continue;
	    int hi = INT_MAX, last = INT_MIN;
	    for (e2k_ms_dep &d : l->deps)
	      if (d.from == c && l->nodes[d.to].pred && pt[d.to] != INT_MIN)
		{
		  hi = MIN (hi, pt[d.to] - d.lat);
		  last = MAX (last, pt[d.to]);
		}
	    if (last == INT_MIN)
	      continue;
	    int lo = rot ? early[c] : MAX (early[c], last - ii);
	    int t;
	    if (rot)
	      {
		for (t = hi; t >= lo; t--)
		  if (e2k_ms_place (l, ii, rows, tmp, c, t))
		    break;
		if (t < lo)
		  ok = false;
		else
		  pt[c] = t;
		continue;
	      }
	    for (t = lo; t <= hi; t++)
	      if (e2k_ms_place (l, ii, rows, tmp, c, t))
		break;
	    if (t > hi)
	      ok = false;
	    else
	      pt[c] = t;
	  }
	if (ok)
	  {
	    *tjump = tj;
	    return true;
	  }
      }
  memcpy (rows, save, ii * dfa_state_size);
  return false;
}

/* Schedule L as one stage of II cycles: a list schedule of one
   iteration, cycle by cycle.  Forward (BACK false), each cycle takes
   the ready nodes with the longest way to the end first, stores as soon
   as they are ready (only ALC2 and ALC5 take them, which the rest
   would fill every cycle); backward, from the last cycle, the nodes
   whose successors are placed, the longest way from the start first:
   the stores then spread two a cycle from the end and what feeds them
   before, where forward jacld's results all came late and its 115
   stores two a cycle after them (in the modulo scheduler's order no
   place below II 133 for 103 cycles).  The dependences on earlier
   iterations hold over II.  */
bool
e2k_ms_schedule_one (e2k_ms_loop *l, int ii, bool back)
{
  int n = l->n;
  state_t rows = XALLOCAVEC (char, ii * dfa_state_size);
  for (int r = 0; r < ii; r++)
    state_reset ((char *) rows + r * dfa_state_size);
  if (state_transition ((char *) rows + (ii - 1) * dfa_state_size,
			l->jump) >= 0)
    return false;
  state_t tmp = alloca (dfa_state_size);
  int pri[E2K_MS_MAX_NODES], nwait[E2K_MS_MAX_NODES], bound[E2K_MS_MAX_NODES];
  for (int i = 0; i < n; i++)
    {
      pri[i] = 0;
      nwait[i] = 0;
      bound[i] = back ? ii - 1 : 0;
      l->nodes[i].time = INT_MIN;
    }
  for (e2k_ms_dep &d : l->deps)
    if (d.dist == 0 && d.from != d.to)
      nwait[back ? d.from : d.to]++;
  /* Heights or depths: the dependences within an iteration go forward
     in the body.  */
  if (back)
    for (int i = 0; i < n; i++)
      for (e2k_ms_dep &d : l->deps)
	if (d.to == i && d.dist == 0 && d.from < i)
	  pri[i] = MAX (pri[i], d.lat + pri[d.from]);
  if (!back)
    {
      for (int i = n - 1; i >= 0; i--)
	for (e2k_ms_dep &d : l->deps)
	  if (d.from == i && d.dist == 0 && d.to > i)
	    pri[i] = MAX (pri[i], d.lat + pri[d.to]);
      for (int i = 0; i < n; i++)
	if (l->nodes[i].store)
	  pri[i] += 4 * ii;
    }
  int left = n;
  for (int k = 0; k < ii && left; k++)
    {
      int t = back ? ii - 1 - k : k;
      for (bool more = true; more; )
	{
	  more = false;
	  int best = -1;
	  for (int i = 0; i < n; i++)
	    if (l->nodes[i].time == INT_MIN && nwait[i] == 0
		&& (back ? bound[i] >= t : bound[i] <= t)
		&& (best < 0 || pri[i] > pri[best]))
	      {
		/* Whether row T takes it.  */
		if (!l->nodes[i].kdead)
		  {
		    memcpy (tmp, (char *) rows + t * dfa_state_size,
			    dfa_state_size);
		    if (state_transition (tmp, l->nodes[i].insn) >= 0
			|| e2k_ms_div_clash (l, ii, i, t))
		      continue;
		  }
		best = i;
	      }
	  if (best < 0)
	    break;
	  if (!l->nodes[best].kdead
	      && state_transition ((char *) rows + t * dfa_state_size,
				   l->nodes[best].insn) >= 0)
	    gcc_unreachable ();
	  l->nodes[best].time = t;
	  left--;
	  more = true;
	  for (e2k_ms_dep &d : l->deps)
	    if (d.dist == 0 && d.from != d.to)
	      {
		if (!back && d.from == best)
		  {
		    nwait[d.to]--;
		    bound[d.to] = MAX (bound[d.to], t + d.lat);
		  }
		else if (back && d.to == best)
		  {
		    nwait[d.from]--;
		    bound[d.from] = MIN (bound[d.from], t - d.lat);
		  }
	      }
	}
    }
  if (left)
    {
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: II %d: %d nodes left over "
		 "in one stage%s\n", ii, left, back ? ", backward" : "");
      return false;
    }
  for (e2k_ms_dep &d : l->deps)
    if (l->nodes[d.to].time + ii * d.dist < l->nodes[d.from].time + d.lat)
      {
	if (dump_file)
	  fprintf (dump_file, ";; e2k_modsched: II %d: one stage breaks "
		   "insn %d -> %d\n", ii, INSN_UID (l->nodes[d.from].insn),
		   INSN_UID (l->nodes[d.to].insn));
	return false;
      }
  l->ii = ii;
  l->stages = 1;
  return true;
}

/* Iterative modulo scheduling (B. R. Rau, "Iterative modulo
   scheduling", MICRO-27, 1994), for e2k_ms_schedule (IMS): the highest
   node not placed (the longest path from it to the end of an iteration,
   carried dependences counted at II) goes in the first cycle of its
   window whose row takes it; where none does, at its earliest start or
   a cycle after its last one, evicting from that row what is in the way
   and every placed node whose dependence on it no longer holds, all to
   be placed again.  Gives up after E2K_MS_IMS_BUDGET placements a node.
   The greedy orders place a node once: NPB LU's blts loop, a recurrence
   of 207 cycles through 329 operations, got II 274 because the loads
   that start an iteration took the rows its last nodes wrap into.  */
#define E2K_MS_IMS_BUDGET 6

static bool
e2k_ms_ims_place (e2k_ms_loop *l, int ii, char *rows, state_t tmp)
{
  int n = l->n;
  int nd = l->deps.length ();
  int *height = XALLOCAVEC (int, n);
  int *prev = XALLOCAVEC (int, n);
  int *seq = XALLOCAVEC (int, n);
  int *list = XALLOCAVEC (int, n);
  /* The least time a node may take: where a store moved to the last
     stage leaves room for it.  */
  int *mint = XALLOCAVEC (int, n);
  /* Each node's dependences, in and out: DEPS[OFF[i] .. OFF[i + 1]).  */
  int *off = XALLOCAVEC (int, n + 1);
  int *adj = XALLOCAVEC (int, 2 * nd);
  for (int i = 0; i <= n; i++)
    off[i] = 0;
  for (e2k_ms_dep &d : l->deps)
    {
      off[d.from + 1]++;
      off[d.to + 1]++;
    }
  for (int i = 0; i < n; i++)
    off[i + 1] += off[i];
  {
    int *fill = XALLOCAVEC (int, n);
    for (int i = 0; i < n; i++)
      fill[i] = off[i];
    for (int k = 0; k < nd; k++)
      {
	adj[fill[l->deps[k].from]++] = k;
	adj[fill[l->deps[k].to]++] = k;
      }
  }
  for (int i = 0; i < n; i++)
    {
      height[i] = 0;
      prev[i] = INT_MIN;
      seq[i] = 0;
      mint[i] = 0;
      l->nodes[i].time = INT_MIN;
    }
  bool changed = true;
  for (int round = 0; changed; round++)
    {
      if (round > n)
	return false;
      changed = false;
      for (e2k_ms_dep &d : l->deps)
	if (height[d.to] + d.lat - ii * d.dist > height[d.from])
	  {
	    height[d.from] = height[d.to] + d.lat - ii * d.dist;
	    changed = true;
	  }
    }
  auto rowof = [&] (int t) { return ((t % ii) + ii) % ii; };
  /* Row R's state again from the nodes it holds, in the order they went
     in; one that no longer fits (the DFA's choices can depend on the
     order) is taken out too.  */
  auto rebuild = [&] (int r)
    {
      char *row = rows + r * dfa_state_size;
      state_reset (row);
      if (r == ii - 1 && state_transition (row, l->jump) >= 0)
	gcc_unreachable ();
      int m = 0;
      for (int j = 0; j < n; j++)
	if (l->nodes[j].time != INT_MIN && !l->nodes[j].kdead
	    && rowof (l->nodes[j].time) == r)
	  list[m++] = j;
      for (int a = 1; a < m; a++)
	for (int b = a; b > 0 && seq[list[b - 1]] > seq[list[b]]; b--)
	  std::swap (list[b - 1], list[b]);
      for (int a = 0; a < m; a++)
	if (state_transition (row, l->nodes[list[a]].insn) >= 0)
	  l->nodes[list[a]].time = INT_MIN;
    };
  auto evict = [&] (int j)
    {
      int r = rowof (l->nodes[j].time);
      l->nodes[j].time = INT_MIN;
      if (!l->nodes[j].kdead)
	rebuild (r);
    };
  auto fits = [&] (int i, int t)
    {
      if (l->nodes[i].kdead)
	return true;
      if (e2k_ms_div_clash (l, ii, i, t))
	return false;
      memcpy (tmp, rows + rowof (t) * dfa_state_size, dfa_state_size);
      return state_transition (tmp, l->nodes[i].insn) < 0;
    };
  int counter = 0;
  for (int budget = E2K_MS_IMS_BUDGET * n; ; budget--)
    {
      int i = -1;
      for (int j = 0; j < n; j++)
	if (!l->nodes[j].pred && l->nodes[j].time == INT_MIN
	    && (i < 0 || height[j] > height[i]))
	  i = j;
      if (i < 0)
	{
	  /* Every store goes to the last stage, keeping its row
	     (e2k_ms_schedule): what reads after one then goes again, no
	     earlier than that allows.  */
	  int last = 0;
	  for (int j = 0; j < n; j++)
	    if (!l->nodes[j].pred)
	      last = MAX (last, l->nodes[j].time / ii);
	  bool again = false;
	  for (e2k_ms_dep &d : l->deps)
	    if (l->nodes[d.from].store && !l->nodes[d.to].store
		&& !l->nodes[d.to].pred && l->nodes[d.to].time != INT_MIN)
	      {
		int ts = last * ii + rowof (l->nodes[d.from].time);
		if (l->nodes[d.to].time + ii * d.dist < ts + d.lat)
		  {
		    mint[d.to] = MAX (mint[d.to], ts + d.lat - ii * d.dist);
		    evict (d.to);
		    again = true;
		  }
	      }
	  if (!again)
	    return true;
	  continue;
	}
      if (budget <= 0)
	{
	  if (dump_file)
	    {
	      int left = 0;
	      for (int j = 0; j < n; j++)
		left += !l->nodes[j].pred && l->nodes[j].time == INT_MIN;
	      fprintf (dump_file, ";; e2k_modsched: II %d: %d nodes not "
		       "placed iteratively\n", ii, left);
	    }
	  return false;
	}
      int early = mint[i];
      for (int a = off[i]; a < off[i + 1]; a++)
	{
	  e2k_ms_dep &d = l->deps[adj[a]];
	  if (d.to == i && d.from != i && l->nodes[d.from].time != INT_MIN)
	    early = MAX (early, l->nodes[d.from].time + d.lat - ii * d.dist);
	}
      int t = INT_MIN;
      for (int c = early; c < early + ii; c++)
	if (fits (i, c))
	  {
	    t = c;
	    break;
	  }
      if (t == INT_MIN)
	{
	  t = prev[i] == INT_MIN || early > prev[i] ? early : prev[i] + 1;
	  /* Make room: the divides a cycle away, then the row's nodes,
	     the last placed first.  */
	  for (int tries = 0; !fits (i, t); tries++)
	    {
	      if (tries > n)
		return false;
	      if (e2k_ms_div_clash (l, ii, i, t))
		{
		  for (int j = 0; j < n; j++)
		    if (j != i && l->nodes[j].time != INT_MIN
			&& get_attr_type (l->nodes[j].insn) == TYPE_FDIV)
		      {
			int dd = rowof (t - l->nodes[j].time);
			if (dd == 1 || dd == ii - 1)
			  evict (j);
		      }
		  continue;
		}
	      int last = -1;
	      for (int j = 0; j < n; j++)
		if (l->nodes[j].time != INT_MIN && !l->nodes[j].kdead
		    && rowof (l->nodes[j].time) == rowof (t)
		    && (last < 0 || seq[j] > seq[last]))
		  last = j;
	      /* Nothing to take out: the row can't hold it (the loop
		 end's).  */
	      if (last < 0)
		t++;
	      else
		evict (last);
	    }
	}
      if (!l->nodes[i].kdead
	  && state_transition (rows + rowof (t) * dfa_state_size,
			       l->nodes[i].insn) >= 0)
	gcc_unreachable ();
      l->nodes[i].time = t;
      seq[i] = ++counter;
      prev[i] = t;
      for (int a = off[i]; a < off[i + 1]; a++)
	{
	  e2k_ms_dep &d = l->deps[adj[a]];
	  if (d.from == i && d.to != i && l->nodes[d.to].time != INT_MIN
	      && l->nodes[d.to].time + ii * d.dist < t + d.lat)
	    evict (d.to);
	  else if (d.to == i && d.from != i
		   && l->nodes[d.from].time != INT_MIN
		   && t + ii * d.dist < l->nodes[d.from].time + d.lat)
	    evict (d.from);
	}
    }
}

/* Modulo schedule L with initiation interval II.  EST: order the nodes
   by their earliest start at II over every dependence, carried ones
   included (a longest path weighing a dependence LAT - II * DIST), and
   start none before it.  The body's order puts a node that only reads
   the last iteration's value of a recurrence (xz's crc64: the shift of
   the carried CRC) at the top, which leaves the recurrence's last node
   too little room at every II.  BAL: put each node in the cycle of its
   window whose row has the fewest ALU operations so far, not the first
   that fits: Linpack's unrolled daxpy (v5, fmul_add) had its four
   multiply-adds ready in one cycle, and the row that took them all kept
   room for one store of the two the II needed.  SLACK (EST): the
   earliest starts as at II - SLACK, which leaves each carried
   dependence SLACK cycles of room at II.  SHORT_BY: on failure, how many
   cycles the node that found no place lacked, if its successors bound
   it (0 if a whole II's rows were full).  CRIT (EST): the nodes with the
   least room between their earliest and latest starts first, then by
   earliest start: a recurrence's nodes before the loads that start the
   iteration, which otherwise fill the rows its last nodes wrap into
   (NPB LU's blts: its stores found no row among the loads).  IMS:
   place by e2k_ms_ims_place instead.  */
bool
e2k_ms_schedule (e2k_ms_loop *l, int ii, bool est, bool bal, int slack,
		 int *short_by, bool crit, bool ims)
{
  int n = l->n;
  state_t rows = XALLOCAVEC (char, ii * dfa_state_size);
  state_t tmp = alloca (dfa_state_size);
  for (int r = 0; r < ii; r++)
    state_reset ((char *) rows + r * dfa_state_size);
  /* The loop end takes the last cycle.  */
  if (state_transition ((char *) rows + (ii - 1) * dfa_state_size,
			l->jump) >= 0)
    return false;

  /* ALU operations placed in each row (BAL).  */
  int *nalu = XALLOCAVEC (int, ii);
  for (int r = 0; r < ii; r++)
    nalu[r] = 0;

  /* Order: earliest start within an iteration, then body order.  */
  int asap[E2K_MS_MAX_NODES], order[E2K_MS_MAX_NODES];
  for (int i = 0; i < n; i++)
    {
      asap[i] = 0;
      order[i] = i;
      l->nodes[i].time = INT_MIN;
    }
  for (int i = 0; i < n; i++)
    for (e2k_ms_dep &d : l->deps)
      if (d.to == i && d.dist == 0 && d.from < i)
	asap[i] = MAX (asap[i], asap[d.from] + d.lat);
  if (est)
    {
      /* Bellman-Ford; still changing after N rounds, a recurrence is
	 longer than II.  The exit test is placed apart.  */
      for (int i = 0; i < n; i++)
	asap[i] = 0;
      bool changed = true;
      for (int round = 0; changed; round++)
	{
	  if (round > n)
	    {
	      if (dump_file && (dump_flags & TDF_DETAILS))
		fprintf (dump_file, ";; e2k_modsched: II %d: earliest starts "
			 "don't settle\n", ii);
	      return false;
	    }
	  changed = false;
	  for (e2k_ms_dep &d : l->deps)
	    if (!l->nodes[d.from].pred && !l->nodes[d.to].pred
		&& asap[d.from] + d.lat - (ii - slack) * d.dist > asap[d.to])
	      {
		asap[d.to] = asap[d.from] + d.lat - (ii - slack) * d.dist;
		changed = true;
	      }
	}
    }
  if (est && crit)
    {
      /* Latest starts against the latest earliest start, by the same
	 dependences in reverse; the room is their difference.  */
      int top = 0, key[E2K_MS_MAX_NODES], alap[E2K_MS_MAX_NODES];
      for (int i = 0; i < n; i++)
	top = MAX (top, asap[i]);
      for (int i = 0; i < n; i++)
	alap[i] = top;
      bool changed = true;
      for (int round = 0; changed; round++)
	{
	  if (round > n)
	    return false;
	  changed = false;
	  for (e2k_ms_dep &d : l->deps)
	    if (!l->nodes[d.from].pred && !l->nodes[d.to].pred
		&& alap[d.to] - d.lat + (ii - slack) * d.dist < alap[d.from])
	      {
		alap[d.from] = alap[d.to] - d.lat + (ii - slack) * d.dist;
		changed = true;
	      }
	}
      for (int i = 0; i < n; i++)
	key[i] = (alap[i] - asap[i]) * (top + 1) + asap[i];
      e2k_ms_sort (order, n, key);
    }
  else
    e2k_ms_sort (order, n, asap);
  /* A check right after its lock load: it is the most constrained of
     what moves to the last stage.  */
  if (l->kchk >= 0)
    {
      int pk = 0, pl = 0;
      for (int k = 0; k < n; k++)
	{
	  if (order[k] == l->kchk)
	    pk = k;
	  if (order[k] == l->dam)
	    pl = k;
	}
      for (int k = pk; k > pl + 1; k--)
	order[k] = order[k - 1];
      if (pk > pl)
	order[pl + 1] = l->kchk;
      /* The stores before them after them: a store keeps the lock's and
	 the check's rows free of stores, and one in the only row the
	 loop end leaves the check (its rbranch takes SS) left NPB IS's
	 histogram at II 4 instead of lcc's 2.  A store can take any row
	 its window has: it moves to the last stage.  */
      if (e2k_dam_stores_late && pk > pl)
	{
	  int tmp[E2K_MS_MAX_NODES], m = 0, sk = pl + 1;
	  for (int k = 0; k <= sk; k++)
	    if (k < pl && l->nodes[order[k]].store)
	      tmp[m++] = order[k];
	  if (m)
	    {
	      int w = 0;
	      for (int k = 0; k <= sk; k++)
		if (!(k < pl && l->nodes[order[k]].store))
		  order[w++] = order[k];
	      for (int j = 0; j < m; j++)
		order[w++] = tmp[j];
	      gcc_assert (w == sk + 1);
	    }
	}
    }

  if (ims && !e2k_ms_ims_place (l, ii, (char *) rows, tmp))
    return false;
  for (int k = 0; k < n && !ims; k++)
    {
      int i = order[k];
      /* A while loop's exit test goes last (e2k_ms_place_exit).  */
      if (l->nodes[i].pred)
	continue;
      /* Stores and a check move to the last stage afterwards, keeping
	 their rows: between two of them only the rows count, and a
	 successor that moves later bounds nothing now.  */
      auto movable = [&] (int x) { return l->nodes[x].store || x == l->kchk; };
      auto rowof = [&] (int x) { return ((l->nodes[x].time % ii) + ii) % ii; };
      bool mov = movable (i);
      int early = INT_MIN, late = INT_MAX, rlo = INT_MIN, rhi = INT_MAX;
      for (e2k_ms_dep &d : l->deps)
	{
	  if (d.to == i && l->nodes[d.from].time != INT_MIN)
	    {
	      if (mov && movable (d.from))
		rlo = MAX (rlo, rowof (d.from) + d.lat - ii * d.dist);
	      else
		early = MAX (early,
			     l->nodes[d.from].time + d.lat - ii * d.dist);
	    }
	  if (d.from == i && l->nodes[d.to].time != INT_MIN)
	    {
	      if (mov && movable (d.to))
		rhi = MIN (rhi, rowof (d.to) - d.lat + ii * d.dist);
	      else if (!movable (d.to))
		late = MIN (late, l->nodes[d.to].time - d.lat + ii * d.dist);
	    }
	}
      /* Only successors placed: as late as they allow (an induction
	 step before the loads of the next iteration that use it).  */
      if (early == INT_MIN)
	early = late == INT_MAX ? 0 : late - (ii - 1);
      if (est)
	early = MAX (early, asap[i]);
      enum attr_type ty = get_attr_type (l->nodes[i].insn);
      bool alu = ty != TYPE_PLOG && ty != TYPE_MOVA;
      /* What only the prologue runs takes no channel.  */
      bool kdead = l->nodes[i].kdead;
      int t, best = INT_MIN;
      /* A check shares its lock load's row only where no other row
	 takes it: CoreMark's list reversal with both in one wide
	 instruction and the store in the next ran 2.9% slower on the
	 8C2 (relcc2 findings I45), and NPB IS's histogram needs the
	 sharing for II 2, as lcc has it.  */
      int avoid = (i == l->kchk && l->nodes[l->dam].time != INT_MIN
		   ? rowof (l->dam) : -1);
    again:
      for (t = early; t < early + ii && t <= late; t++)
	{
	  int r = ((t % ii) + ii) % ii;
	  if (kdead)
	    {
	      best = t;
	      break;
	    }
	  if (r < rlo || r > rhi || r == avoid
	      || e2k_ms_div_clash (l, ii, i, t))
	    continue;
	  char *row = (char *) rows + r * dfa_state_size;
	  memcpy (tmp, row, dfa_state_size);
	  if (state_transition (tmp, l->nodes[i].insn) < 0)
	    {
	      if (!bal || !alu)
		{
		  best = t;
		  break;
		}
	      if (best == INT_MIN
		  || nalu[r] < nalu[((best % ii) + ii) % ii])
		best = t;
	    }
	}
      if (best == INT_MIN && avoid >= 0)
	{
	  avoid = -1;
	  goto again;
	}
      if (best != INT_MIN)
	{
	  t = best;
	  int r = ((t % ii) + ii) % ii;
	  char *row = (char *) rows + r * dfa_state_size;
	  if (!kdead && state_transition (row, l->nodes[i].insn) >= 0)
	    gcc_unreachable ();
	  nalu[r] += alu && !kdead;
	}
      else
	{
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: II %d: no cycle for insn %d "
		     "in %d..%d (rows %d..%d)\n", ii,
		     INSN_UID (l->nodes[i].insn), early,
		     MIN (early + ii - 1, late), rlo, rhi);
	  if (short_by)
	    *short_by = late < early + ii - 1 ? MAX (1, early - late) : 0;
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    for (e2k_ms_dep &d : l->deps)
	      {
		if (d.to == i && l->nodes[d.from].time != INT_MIN
		    && l->nodes[d.from].time + d.lat - ii * d.dist >= early - 2)
		  fprintf (dump_file, ";;   after %d at %d (asap %d), lat %d "
			   "dist %d%s\n", INSN_UID (l->nodes[d.from].insn),
			   l->nodes[d.from].time, asap[d.from], d.lat, d.dist,
			   movable (d.from) && mov ? " (rows)" : "");
		if (d.from == i && l->nodes[d.to].time != INT_MIN
		    && !movable (d.to)
		    && l->nodes[d.to].time - d.lat + ii * d.dist <= late + 2)
		  fprintf (dump_file, ";;   before %d at %d (asap %d), lat %d "
			   "dist %d\n", INSN_UID (l->nodes[d.to].insn),
			   l->nodes[d.to].time, asap[d.to], d.lat, d.dist);
	      }
	  return false;
	}
      l->nodes[i].time = t;
    }

  /* Start at stage 0, keeping the rows (the loop end is in the last).  */
  int mint = INT_MAX;
  for (int i = 0; i < n; i++)
    if (!l->nodes[i].pred)
      mint = MIN (mint, l->nodes[i].time);
  int shift = (mint >= 0 ? mint / ii : -((-mint + ii - 1) / ii)) * ii;
  for (int i = 0; i < n; i++)
    if (!l->nodes[i].pred)
      l->nodes[i].time -= shift;

  /* Every store goes to the last stage, the same row.  */
  int maxt = 0;
  for (int i = 0; i < n; i++)
    maxt = MAX (maxt, l->nodes[i].time);
  if (l->wl)
    {
      if (!e2k_ms_place_exit (l, ii, (char *) rows, tmp, &maxt))
	{
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: II %d: no place for the "
		     "exit test\n", ii);
	  return false;
	}
    }
  int stages = maxt / ii + 1;

  /* A lock load per stage is in flight, and the DAM has 32 entries
     (spec/isa/speculation.md).  */
  if (l->kchk >= 0 && !e2k_dam_deep && stages > 16)
    return false;
  /* So does the check of a lock load, which the DFA keeps out of the
     loop end's row (its rbranch and the ct both take SS).  */
  for (int i = 0; i < n; i++)
    if (l->nodes[i].store || i == l->kchk)
      l->nodes[i].time += (stages - 1 - l->nodes[i].time / ii) * ii;
  /* Only the stages from the lock load's to its check's hold entries,
     one each: the stages before, which far loads add, hold none (NPB
     IS's histogram: 32 stages at II 2, nearly all of them before the
     lock; lcc's runs 28 iterations ahead, "? %pcnt28").  */
  if (l->kchk >= 0 && e2k_dam_deep
      && (l->nodes[l->kchk].time / ii - l->nodes[l->dam].time / ii + 1
	  > 32))
    return false;
  for (e2k_ms_dep &d : l->deps)
    if (l->nodes[d.to].time + ii * d.dist < l->nodes[d.from].time + d.lat)
      {
	if (dump_file)
	  fprintf (dump_file, ";; e2k_modsched: II %d: stores in the last "
		   "stage break insn %d -> %d\n", ii,
		   INSN_UID (l->nodes[d.from].insn),
		   INSN_UID (l->nodes[d.to].insn));
	return false;
      }
  l->ii = ii;
  l->stages = stages;
  return stages > 1;
}

/* Whether the dependences of L have a cycle longer than II (a positive
   one, each dependence weighing LAT - II * DIST); then PRED[i] is the
   dependence that last raised node I, and *LAST a node raised in the
   last round.  */
static bool
e2k_ms_long_cycle_p (e2k_ms_loop *l, int ii, int *pred, int *last)
{
  int n = l->n;
  auto_vec<int> start;
  start.safe_grow_cleared (n);
  for (int i = 0; i < n; i++)
    pred[i] = -1;
  for (int round = 0; round <= n; round++)
    {
      bool changed = false;
      for (unsigned k = 0; k < l->deps.length (); k++)
	{
	  e2k_ms_dep &d = l->deps[k];
	  if (start[d.from] + d.lat - ii * d.dist > start[d.to])
	    {
	      start[d.to] = start[d.from] + d.lat - ii * d.dist;
	      pred[d.to] = k;
	      *last = d.to;
	      changed = true;
	    }
	}
      if (!changed)
	return false;
    }
  return true;
}

/* The least II that no cycle of L's dependences is longer than (the
   recurrences' bound on it), or INT_MAX if there is none.  */
int
e2k_ms_rec_mii (e2k_ms_loop *l)
{
  int *pred = XALLOCAVEC (int, l->n);
  int last = -1;
  int lo = 0, hi = 1;
  while (hi <= 65536 && e2k_ms_long_cycle_p (l, hi, pred, &last))
    lo = hi, hi *= 2;
  if (hi > 65536)
    return INT_MAX;
  while (hi - lo > 1)
    {
      int mid = (lo + hi) / 2;
      if (e2k_ms_long_cycle_p (l, mid, pred, &last))
	lo = mid;
      else
	hi = mid;
    }
  return hi;
}

/* For -fdump-rtl-mach-details: the recurrence that bounds L's II, the
   cycle of dependences with the most latency per iteration it spans.  */
void
e2k_ms_dump_recurrence (e2k_ms_loop *l)
{
  int n = l->n;
  int *pred = XALLOCAVEC (int, n);
  int last = -1;
  int hi = e2k_ms_rec_mii (l), lo = hi - 1;
  if (hi == INT_MAX)
    return;
  fprintf (dump_file, ";; e2k_modsched: recurrences need II %d (II %d)\n",
	   hi, l->ii);
  if (lo == 0 || !e2k_ms_long_cycle_p (l, lo, pred, &last))
    return;
  /* N steps back from LAST is on the cycle.  */
  int x = last;
  for (int k = 0; k < n; k++)
    x = l->deps[pred[x]].from;
  auto_vec<int> cyc;
  int y = x;
  do
    {
      cyc.safe_push (pred[y]);
      y = l->deps[pred[y]].from;
    }
  while (y != x);
  int lat = 0, dist = 0;
  for (int k = cyc.length () - 1; k >= 0; k--)
    {
      e2k_ms_dep &d = l->deps[cyc[k]];
      rtx_insn *insn = l->nodes[d.from].insn;
      fprintf (dump_file, ";;   %5d %-26s -> %5d  lat %2d dist %d"
	       "  at %d -> %d\n", INSN_UID (insn),
	       recog_memoized (insn) >= 0 ? get_insn_name (INSN_CODE (insn))
	       : "?", INSN_UID (l->nodes[d.to].insn), d.lat, d.dist,
	       l->nodes[d.from].time, l->nodes[d.to].time);
      lat += d.lat;
      dist += d.dist;
    }
  fprintf (dump_file, ";;   the cycle: %d cycles over %d iterations\n",
	   lat, dist);
}

/* What a failed check redoes, in L->rec, and the lifetimes that takes,
   in L->ext.  The check of iteration I runs at its time TK; node N of
   iteration I + D ran at D * II + T_N.  Redo, in time order, what ran
   after the lock load and before the check and used its value, through
   values or predicates; and then every instance of the exit test in
   that span, since a predicate holds the last instance's value.  What
   those read and write must still be in its register then.  */
void
e2k_ms_dam_plan (e2k_ms_loop *l)
{
  l->rec.truncate (0);
  l->ext.truncate (0);
  if (l->kchk < 0)
    return;
  int ii = l->ii, s = l->stages;
  int tk = l->nodes[l->kchk].time, tl = l->nodes[l->dam].time;
  unsigned dep[E2K_MS_MAX_NODES];
  e2k_ms_dependents (l, l->dam, dep);
  bool preds = false;
  for (int n = 0; n < l->n; n++)
    for (int d = 0; d <= s; d++)
      if (l->nodes[n].pred && (dep[n] & (1u << d))
	  && d * ii + l->nodes[n].time > tl && d * ii + l->nodes[n].time <= tk)
	preds = true;
  for (int n = 0; n < l->n; n++)
    {
      if (n == l->kchk || l->nodes[n].store)
	continue;
      for (int d = -s; d <= s; d++)
	{
	  int t = d * ii + l->nodes[n].time;
	  if (t <= tl || t > tk)
	    continue;
	  if (l->nodes[n].pred ? preds : d >= 0 && (dep[n] & (1u << d)))
	    l->rec.safe_push (std::make_pair (n, d));
	}
    }
  /* In time order.  */
  for (unsigned a = 1; a < l->rec.length (); a++)
    for (unsigned b = a; b > 0; b--)
      {
	std::pair<int, int> &x = l->rec[b - 1], &y = l->rec[b];
	if (x.second * ii + l->nodes[x.first].time
	    <= y.second * ii + l->nodes[y.first].time)
	  break;
	std::swap (x, y);
      }
  for (std::pair<int, int> &r : l->rec)
    {
      e2k_ms_node *node = &l->nodes[r.first];
      int d = r.second;
      if (node->value >= 0)
	l->ext.safe_push (std::make_pair (node->value, tk - d * ii));
      for (int k = 0; k < node->nuses; k++)
	if (!node->uses[k].pred && node->uses[k].value >= 0)
	  l->ext.safe_push (std::make_pair (node->uses[k].value,
					    tk - (d - node->uses[k].dist) * ii));
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: a failed check redoes insn %d "
		 "of iteration +%d\n", INSN_UID (node->insn), d);
    }
}

/* Shorten the values' lifetimes, for a loop the ring can't hold.  In
   one at the machine's width the scheduler places the nodes in order of
   their earliest starts, each in the first cycle whose row has room:
   the loads and what else starts a chain take the first rows, and the
   delays add up along the chains (NPB LU's jacld, 618 operations at II
   111: an iteration over 2 stages and more, results computed early and
   read 250 cycles later, 130 names alive where the ring has 126).  So,
   the latest nodes first, each node moves to the cycle within its
   dependences, the stages there are and a row with room for it (a
   whole II on keeps its row: stage scheduling, Eichenberger and
   Davidson, 1995) that most shortens the lifetimes it starts and ends;
   a chain then follows its last node down.  Not stores (in the last
   stage), loads (placed early for misses: moved nearer their uses,
   NPB BT's ran 9% slower on the 2C3), predicates and what reads them,
   array prefetch, AAU stores, what only the prologue runs, nor what a
   store reads through e2k_ms_rebase_stores; not with a lock load (its
   plan follows the times) nor in a while loop (its exit test).  */
void
e2k_ms_compact (e2k_ms_loop *l)
{
  int ii = l->ii, s = l->stages, n = l->n, nv = l->values.length ();
  if (l->wl || l->kchk >= 0 || s < 2)
    return;
  auto_vec<vec<int> > users (nv);
  for (int v = 0; v < nv; v++)
    users.quick_push (vNULL);
  bool fixed[E2K_MS_MAX_NODES];
  for (int i = 0; i < n; i++)
    {
      e2k_ms_node *nd = &l->nodes[i];
      fixed[i] = (nd->store || nd->pred || nd->dpred || nd->apb || nd->staa
		  || nd->kdead || nd->lock || nd->chk >= 0
		  || (nd->mem && !nd->store));
      for (int k = 0; k < nd->nuses; k++)
	if (nd->uses[k].pred)
	  fixed[i] = true;
	else if (nd->uses[k].value >= 0)
	  users[nd->uses[k].value].safe_push (i);
    }
  for (int i = 0; i < n; i++)
    if (l->nodes[i].rebase_off)
      for (int k = 0; k < l->nodes[i].nuses; k++)
	if (!l->nodes[i].uses[k].pred && l->nodes[i].uses[k].value >= 0)
	  fixed[l->values[l->nodes[i].uses[k].value].node] = true;
  auto_vec<vec<int> > in (n), out (n), rowl (ii);
  for (int i = 0; i < n; i++)
    {
      in.quick_push (vNULL);
      out.quick_push (vNULL);
    }
  for (int r = 0; r < ii; r++)
    rowl.quick_push (vNULL);
  for (unsigned d = 0; d < l->deps.length (); d++)
    if (l->deps[d].from != l->deps[d].to)
      {
	in[l->deps[d].to].safe_push (d);
	out[l->deps[d].from].safe_push (d);
      }
  for (int i = 0; i < n; i++)
    if (!l->nodes[i].kdead)
      rowl[l->nodes[i].time % ii].safe_push (i);
  /* Whether row R takes its nodes but SKIP, and ADD.  */
  state_t st = alloca (dfa_state_size);
  auto row_ok = [&] (int r, int skip, int add)
    {
      state_reset (st);
      if (r == ii - 1 && state_transition (st, l->jump) >= 0)
	return false;
      for (int j : rowl[r])
	if (j != skip && state_transition (st, l->nodes[j].insn) >= 0)
	  return false;
      return add < 0 || state_transition (st, l->nodes[add].insn) < 0;
    };
  /* Value V's cycles alive, [*B, *E), with node I at time TI, as
     e2k_ms_assign_names counts them.  */
  auto span = [&] (int v, int i, int ti, int *b, int *e)
    {
      const e2k_ms_value &val = l->values[v];
      int dn = val.node;
      *b = dn == i ? ti : l->nodes[dn].time;
      *e = *b + MAX (insn_default_latency (l->nodes[dn].insn), 1);
      if (val.out_dist >= 0)
	*e = MAX (*e, (s + val.out_dist) * ii);
      for (int u : users[v])
	{
	  const e2k_ms_node *un = &l->nodes[u];
	  int tu = u == i ? ti : un->time;
	  for (int k = 0; k < un->nuses; k++)
	    if (!un->uses[k].pred && un->uses[k].value == v)
	      *e = MAX (*e, tu + un->uses[k].dist * ii);
	}
    };
  /* The instances alive in each cycle of II, and how many the ring and
     the registers the loop leaves free hold at once: the excess over
     that is what no packing can place.  */
  auto_vec<int> live;
  live.safe_grow_cleared (ii);
  int cap = 2 * (E2K_ROT_MAX / 2 - 1);
  for (unsigned r = 16; r < R0_REGNUM + 64; r++)
    cap += TEST_HARD_REG_BIT (l->fix_free, r) && r != l->apb_tmp;
  auto add = [&] (int b, int e, int d, int *dx)
    {
      for (int t = b; t < e; t++)
	{
	  int r = ((t % ii) + ii) % ii;
	  if (d > 0 && ++live[r] > cap)
	    (*dx)++;
	  else if (d < 0 && live[r]-- > cap)
	    (*dx)--;
	}
    };
  for (int v = 0; v < nv; v++)
    {
      int b, e, dx = 0;
      span (v, -1, 0, &b, &e);
      add (b, e, 1, &dx);
    }
  /* What moving node I to T changes: the excess (*DX) and the
     lifetimes (returned); LIVE as it was unless COMMIT.  */
  auto gain = [&] (int i, int t, int *dx, bool commit)
    {
      e2k_ms_node *nd = &l->nodes[i];
      int vals[E2K_MS_MAX_USES + 1], nvals = 0;
      if (nd->value >= 0)
	vals[nvals++] = nd->value;
      for (int k = 0; k < nd->nuses; k++)
	{
	  int v = nd->uses[k].value;
	  bool seen = false;
	  for (int k2 = 0; k2 < nvals; k2++)
	    seen |= vals[k2] == v;
	  if (v >= 0 && !nd->uses[k].pred && !seen)
	    vals[nvals++] = v;
	}
      int b0[E2K_MS_MAX_USES + 1], e0[E2K_MS_MAX_USES + 1];
      int b1[E2K_MS_MAX_USES + 1], e1[E2K_MS_MAX_USES + 1];
      int dl = 0, undo = 0;
      *dx = 0;
      for (int k = 0; k < nvals; k++)
	{
	  span (vals[k], i, nd->time, &b0[k], &e0[k]);
	  span (vals[k], i, t, &b1[k], &e1[k]);
	  dl += (e1[k] - b1[k]) - (e0[k] - b0[k]);
	  add (b0[k], e0[k], -1, dx);
	  add (b1[k], e1[k], 1, dx);
	}
      if (!commit)
	for (int k = 0; k < nvals; k++)
	  {
	    add (b1[k], e1[k], -1, &undo);
	    add (b0[k], e0[k], 1, &undo);
	  }
      return dl;
    };
  int order[E2K_MS_MAX_NODES], key[E2K_MS_MAX_NODES], moved = 0;
  for (int pass = 0; pass < 8; pass++)
    {
      for (int i = 0; i < n; i++)
	{
	  order[i] = i;
	  key[i] = -l->nodes[i].time;
	}
      e2k_ms_sort (order, n, key);
      bool any = false;
      for (int k = 0; k < n; k++)
	{
	  int i = order[k];
	  if (fixed[i])
	    continue;
	  e2k_ms_node *nd = &l->nodes[i];
	  int lo = 0, hi = s * ii - 1;
	  for (int d : in[i])
	    {
	      e2k_ms_dep &dp = l->deps[d];
	      lo = MAX (lo, l->nodes[dp.from].time + dp.lat - dp.dist * ii);
	    }
	  for (int d : out[i])
	    {
	      e2k_ms_dep &dp = l->deps[d];
	      hi = MIN (hi, l->nodes[dp.to].time - dp.lat + dp.dist * ii);
	    }
	  int cur = nd->time, r0 = cur % ii;
	  if (lo > cur || hi < cur || !row_ok (r0, i, -1))
	    continue;
	  /* The least excess, then the shortest lifetimes, then the
	     nearest.  */
	  int bestx = 0, bestl = 0, bestt = cur;
	  for (int t = lo; t <= hi; t++)
	    {
	      int r = t % ii;
	      if (t == cur || e2k_ms_div_clash (l, ii, i, t)
		  || (r != r0 && !row_ok (r, -1, i)))
		continue;
	      int dx, dl = gain (i, t, &dx, false);
	      if (dx > bestx || (dx == bestx && dl > bestl)
		  || (dx == bestx && dl == bestl
		      && abs (t - cur) >= abs (bestt - cur)))
		continue;
	      bestx = dx;
	      bestl = dl;
	      bestt = t;
	    }
	  if (bestt == cur || (bestx == 0 && bestl >= 0))
	    continue;
	  int dx;
	  gain (i, bestt, &dx, true);
	  int r = bestt % ii;
	  if (r != r0)
	    {
	      unsigned x = 0;
	      while (rowl[r0][x] != i)
		x++;
	      rowl[r0].unordered_remove (x);
	      rowl[r].safe_push (i);
	    }
	  nd->time = bestt;
	  any = true;
	  moved++;
	}
      if (!any)
	break;
    }
  for (int v = 0; v < nv; v++)
    users[v].release ();
  for (int i = 0; i < n; i++)
    {
      in[i].release ();
      out[i].release ();
    }
  for (int r = 0; r < ii; r++)
    rowl[r].release ();
  if (dump_file && moved)
    {
      int mx = 0;
      for (int r = 0; r < ii; r++)
	mx = MAX (mx, live[r]);
      fprintf (dump_file, ";; e2k_modsched: II %d: %d moves to shorten "
	       "lifetimes; %d alive at most, %d registers\n", ii, moved, mx,
	       cap);
    }
}

/* Give the values their names in the ring; false if it gets too big.

   Rotation makes the ring a cylinder: with P pairs per lane (even and
   odd names), the instance of value V from iteration I sits in physical
   pair (C_V - I) mod P from its definition to its last use, at times
   I * II + [START, END).  Values are packed first-fit: V and W of one
   lane clash when instances I and I + D, D = C_W - C_V (mod P), are
   alive at once.  */
bool
e2k_ms_assign_names (e2k_ms_loop *l, int gap)
{
  int ii = l->ii, s = l->stages, nv = l->values.length ();
  auto_vec<int> st (nv), en (nv), order (nv), lane (nv), slot (nv);
  for (int v = 0; v < nv; v++)
    {
      const e2k_ms_value &val = l->values[v];
      rtx_insn *def = l->nodes[val.node].insn;
      st.quick_push (l->nodes[val.node].time);
      /* Until the value lands, at least.  */
      en.quick_push (st[v] + MAX (insn_default_latency (def), 1));
      /* Until after the loop, for the iteration OUT_DIST before the
	 last.  */
      if (val.out_dist >= 0)
	en[v] = MAX (en[v], (s + val.out_dist) * ii);
      /* Until a failed check has redone what used it: the compensation
	 code runs after the check's wide instruction, whose results are
	 written by then, so through that instruction (a value it wrote
	 into the same pair was the operand the compensation read;
	 gcc.dg/vect/vect-alias-check-18.c).  */
      for (std::pair<int, int> &x : l->ext)
	if (x.first == v)
	  en[v] = MAX (en[v], x.second + 1);
      order.quick_push (v);
      lane.quick_push (-1);
      slot.quick_push (-1);
    }
  for (int i = 0; i < l->n; i++)
    for (int k = 0; k < l->nodes[i].nuses; k++)
      {
	e2k_ms_use *u = &l->nodes[i].uses[k];
	if (u->value >= 0 && !u->pred)
	  en[u->value] = MAX (en[u->value],
			      l->nodes[i].time + u->dist * ii);
      }
  for (int a = 1; a < nv; a++)
    for (int b = a; b > 0 && st[order[b - 1]] > st[order[b]]; b--)
      std::swap (order[b - 1], order[b]);

  /* A value whose last use issues no later than the next iteration's
     def needs no ring: it gets a register of its own outside it (NPB
     SP's 140-operation loops have 135 values, for what were the ring's
     62 names), one the loop leaves free (L->fix_free), shared by values
     whose lifetimes, modulo II, don't meet; registers the function uses
     already first, which don't widen the window.  Not a value carried
     or read after the loop, nor in a loop that reads an earlier
     iteration's instances after the kernel (a while loop's exits, a
     failed check's compensation).  */
  auto_vec<int> freg (nv);
  for (int v = 0; v < nv; v++)
    freg.quick_push (-1);
  if (e2k_ms_fixed && !l->wl && l->kchk < 0)
    {
      /* Each register's cycles modulo II, in words of 64.  */
      int nw = CEIL (ii, 64);
      auto_vec<uint64_t> occ, m;
      occ.safe_grow_cleared ((R0_REGNUM + 64) * nw);
      m.safe_grow_cleared (nw);
      for (int k = 0; k < nv; k++)
	{
	  int v = order[k];
	  const e2k_ms_value &val = l->values[v];
	  if (val.carried || val.carried2 || val.out_dist >= 0
	      || en[v] + gap - st[v] > ii)
	    continue;
	  for (int w = 0; w < nw; w++)
	    m[w] = 0;
	  for (int t = st[v]; t < en[v] + gap; t++)
	    {
	      int c = ((t % ii) + ii) % ii;
	      m[c / 64] |= HOST_WIDE_INT_1U << (c % 64);
	    }
	  for (int pass = 0; pass < 2 && freg[v] < 0; pass++)
	    for (unsigned r = 16; r < R0_REGNUM + 64; r++)
	      if (TEST_HARD_REG_BIT (l->fix_free, r) && r != l->apb_tmp
		  && (pass || df_regs_ever_live_p (r)))
		{
		  bool busy = false;
		  for (int w = 0; w < nw && !busy; w++)
		    busy = occ[r * nw + w] & m[w];
		  if (busy)
		    continue;
		  for (int w = 0; w < nw; w++)
		    occ[r * nw + w] |= m[w];
		  freg[v] = r;
		  break;
		}
	}
    }

  /* Whether V in pair C clashes with W in pair CW, both of one lane.  */
  auto clash = [&] (int v, int c, int w, int cw, int p)
    {
      int d0 = ((cw - c) % p + p) % p;
      for (int d = d0 - (s + 2) * p; d <= (s + 2) * p; d += p)
	{
	  if (v == w && d == 0)
	    continue;
	  if (!(st[w] + d * ii >= en[v] + gap
		|| en[w] + d * ii + gap <= st[v]))
	    return true;
	}
      return false;
    };

  /* A pair holds two lanes of II cycles each: no fewer pairs than the
     ring's values take cycles over 2 II, nor than half the most
     instances alive in one cycle of II (each lane has P registers at a
     time).  NPB LU's jacld at II 105 would need 98 of the 63, and
     packing each size up to there took minutes.  */
  int need = 0, maxlive = 0;
  {
    auto_vec<int> live;
    live.safe_grow_cleared (ii);
    for (int v = 0; v < nv; v++)
      if (freg[v] < 0)
	{
	  need += en[v] + gap - st[v];
	  for (int t = st[v]; t < en[v] + gap; t++)
	    live[((t % ii) + ii) % ii]++;
	}
    for (int r = 0; r < ii; r++)
      maxlive = MAX (maxlive, live[r]);
  }
  int pmax = E2K_ROT_MAX / 2 - 1;
  int p0 = MAX (1, MAX (CEIL (need, 2 * ii), CEIL (maxlive, 2)));
  for (int p = p0; p <= pmax; p++)
    {
      bool ok = true;
      for (int k = 0; k < nv && ok; k++)
	{
	  int v = order[k];
	  lane[v] = slot[v] = -1;
	  if (freg[v] >= 0)
	    continue;
	  for (int ln = 0; ln < 2 && slot[v] < 0; ln++)
	    for (int c = 0; c < p && slot[v] < 0; c++)
	      {
		bool bad = clash (v, c, v, c, p);
		for (int k2 = 0; k2 < k && !bad; k2++)
		  {
		    int w = order[k2];
		    bad = (freg[w] < 0 && lane[w] == ln
			   && clash (v, c, w, slot[w], p));
		  }
		if (!bad)
		  {
		    lane[v] = ln;
		    slot[v] = c;
		  }
	      }
	  ok = slot[v] >= 0;
	}
      if (!ok)
	continue;
      l->pairs = p;
      for (int v = 0; v < nv; v++)
	{
	  int sd = l->nodes[l->values[v].node].time / ii;
	  int n = ((slot[v] + sd - (s - 1)) % p + p) % p;
	  l->values[v].name = freg[v] >= 0 ? -1 - freg[v] : 2 * n + lane[v];
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: value %d (r%d, insn %d) "
		     "alive %d..%d, lane %d pair %d, name %d%s%s\n", v,
		     l->values[v].regno,
		     INSN_UID (l->nodes[l->values[v].node].insn),
		     st[v], en[v], lane[v], slot[v], l->values[v].name,
		     l->values[v].carried ? " carried" : "",
		     l->values[v].out_dist >= 0 ? " live-out" : "");
	}
      return true;
    }
  /* Up to 63 pairs (rsz, 6 bits); e2k_compute_window keeps rbs within
     its 6 bits.  */
  if (dump_file)
    {
      int sum = 0;
      for (int v = 0; v < nv; v++)
	if (freg[v] < 0)
	  {
	    sum += en[v] + gap - st[v];
	    fprintf (dump_file, ";; e2k_modsched: ring: value %d (insn %d) "
		     "%d..%d\n", v, INSN_UID (l->nodes[l->values[v].node].insn),
		     st[v], en[v]);
	  }
      fprintf (dump_file, ";; e2k_modsched: ring: %d cycles of values at "
	       "II %d, %d alive at most\n", sum, ii, maxlive);
    }
  return false;
}

/* The predicates of a while loop's exit test in a ring of their own
   (spec/isa/loops.md, "Rotation"): setbp psz = R - 1 makes %pred0 ..
   %pred(R - 1) rotate, and abp at the loop end makes the old %pred0 the
   new %pred1, so each iteration's predicates get fresh names as its
   %b[] values do, and may live longer than II (lcc leaves its while
   loops through "ct ? %pred1").  Packed like the values, one name per
   rotation.  No predicate below R may be live around the loop.  The
   predicates merges and predicated stores read (of a counted loop too)
   go in the same ring, and need it: a store is in the last stage.
   False if that can't be.  */
bool
e2k_ms_assign_pnames (e2k_ms_loop *l)
{
  l->npred = 0;
  bool data = false;
  for (int i = 0; i < l->n; i++)
    data |= l->nodes[i].dpred;
  if (!e2k_rotate_preds)
    return !data;
  if (!l->wl && !data)
    return true;
  int ii = l->ii, s = l->stages, n = l->n;
  int st[E2K_MS_MAX_NODES], en[E2K_MS_MAX_NODES], slot[E2K_MS_MAX_NODES];
  int order[E2K_MS_MAX_NODES], np = 0;
  for (int i = 0; i < n; i++)
    if (l->nodes[i].pred || l->nodes[i].dpred)
      {
	st[i] = l->nodes[i].time;
	en[i] = st[i] + 1;
	order[np++] = i;
      }
  if (!np)
    return true;
  for (int i = 0; i < n; i++)
    for (int k = 0; k < l->nodes[i].nuses; k++)
      if (l->nodes[i].uses[k].pred)
	{
	  int c = l->nodes[i].uses[k].value;
	  en[c] = MAX (en[c], l->nodes[i].time + l->nodes[i].uses[k].dist * ii);
	}
  /* The loop end reads the stay predicate in the last cycle, and no
     other predicate may take its name there: the jump comes after the
     cycle's other operations in the insn stream, so dataflow would see
     it read their value (and delete the prologue's).  */
  if (l->stay >= 0)
    en[l->stay] = MAX (en[l->stay], s * ii);
  for (int a = 1; a < np; a++)
    for (int b = a; b > 0 && st[order[b - 1]] > st[order[b]]; b--)
      std::swap (order[b - 1], order[b]);
  auto clash = [&] (int v, int c, int w, int cw, int p)
    {
      int d0 = ((cw - c) % p + p) % p;
      for (int d = d0 - (s + 2) * p; d <= (s + 2) * p; d += p)
	{
	  if (v == w && d == 0)
	    continue;
	  if (!(st[w] + d * ii >= en[v] || en[w] + d * ii <= st[v]))
	    return true;
	}
      return false;
    };
  bitmap lh = df_get_live_in (l->bb), lx = df_get_live_in (l->exit);
  bitmap l1 = l->x1 ? df_get_live_in (l->x1) : lx;
  for (int p = 1; p <= 32; p++)
    {
      if (fixed_regs[PRED0_REGNUM + p - 1]
	  || bitmap_bit_p (lh, PRED0_REGNUM + p - 1)
	  || bitmap_bit_p (lx, PRED0_REGNUM + p - 1)
	  || bitmap_bit_p (l1, PRED0_REGNUM + p - 1))
	return false;
      bool ok = true;
      for (int k = 0; k < np && ok; k++)
	{
	  int v = order[k];
	  slot[v] = -1;
	  for (int c = 0; c < p && slot[v] < 0; c++)
	    {
	      bool bad = clash (v, c, v, c, p);
	      for (int k2 = 0; k2 < k && !bad; k2++)
		bad = clash (v, c, order[k2], slot[order[k2]], p);
	      if (!bad)
		slot[v] = c;
	    }
	  ok = slot[v] >= 0;
	}
      if (!ok)
	continue;
      l->npred = p;
      for (int k = 0; k < np; k++)
	{
	  int v = order[k], sd = l->nodes[v].time / ii;
	  l->nodes[v].pname = ((slot[v] + sd - (s - 1)) % p + p) % p;
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: predicate of insn %d alive "
		     "%d..%d, name %d of %d\n", INSN_UID (l->nodes[v].insn),
		     st[v], en[v], l->nodes[v].pname, p);
	}
      return true;
    }
  return false;
}

/* The ring name, in the frame of kernel iteration FRAME, of predicate
   node I's instance from iteration J (as e2k_ms_name).  */
int
e2k_ms_pname (e2k_ms_loop *l, int i, int j, int frame)
{
  int kdef = j + l->nodes[i].time / l->ii - (l->stages - 1);
  int name = (l->nodes[i].pname + (frame - kdef)) % l->npred;
  return name < 0 ? name + l->npred : name;
}

/* The %b[] name, in the frame of kernel iteration FRAME, of value V's
   instance from iteration J (iteration 0 is the first stage of kernel
   iteration -(S - 1)).  */
int
e2k_ms_name (e2k_ms_loop *l, int v, int j, int frame)
{
  const e2k_ms_value &val = l->values[v];
  if (val.name < 0)
    return val.name;
  int kdef = j + l->nodes[val.node].time / l->ii - (l->stages - 1);
  int ring = 2 * l->pairs;
  int name = (val.name + 2 * (frame - kdef)) % ring;
  return name < 0 ? name + ring : name;
}

/* The register of NAME: a %b[] one, or (below 0) the fixed register of a
   value outside the ring (e2k_ms_assign_names).  */
rtx
e2k_ms_reg (machine_mode mode, int name)
{
  return gen_rtx_REG (mode, name < 0 ? -1 - name : E2K_ROT_REGNO (name));
}
