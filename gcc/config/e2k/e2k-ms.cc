/* Software pipelining (modulo scheduling) for the Elbrus (E2K)
   port, after register allocation (spec/isa/loops.md): the driver, which
   loops to pipeline and how (array prefetch, combined FP operations),
   and the output of setbn and loop ends.  e2k-ms-analyze.cc builds a
   loop's dependence graph, e2k-ms-sched.cc schedules it and
   e2k-ms-emit.cc writes the pipelined loop.
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

static bool e2k_ms_fail (basic_block, const char *);
static bool
e2k_ms_apb_big_p (void)
{
  machine_function *m = cfun->machine;
  if (m->apb_big < 0)
    {
      m->apb_big = 0;
      for (rtx_insn *insn = get_insns (); insn && !m->apb_big;
	   insn = NEXT_INSN (insn))
	if (NONDEBUG_INSN_P (insn))
	  {
	    subrtx_iterator::array_type array;
	    FOR_EACH_SUBRTX (iter, array, PATTERN (insn), ALL)
	      {
		tree d = NULL_TREE;
		if (GET_CODE (*iter) == SYMBOL_REF)
		  d = SYMBOL_REF_DECL (*iter);
		else if (MEM_P (*iter) && MEM_EXPR (*iter))
		  d = get_base_address (MEM_EXPR (*iter));
		if (d && VAR_P (d) && DECL_SIZE_UNIT (d)
		    && tree_fits_uhwi_p (DECL_SIZE_UNIT (d))
		    && tree_to_uhwi (DECL_SIZE_UNIT (d)) >= E2K_APB_BIG)
		  {
		    m->apb_big = 1;
		    break;
		  }
	      }
	  }
    }
  return m->apb_big;
}

/* Whether L is known to run at least E2K_MS_LONG iterations: by the
   profile, else by the count the doloop pass knew.  */
static bool
e2k_ms_long_p (e2k_ms_loop *l)
{
  basic_block bb = l->bb;
  profile_count entry = profile_count::zero ();
  edge e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, bb->preds)
    if (e->src != bb)
      entry += e->count ();
  if (bb->count.reliable_p () && entry.reliable_p () && entry.nonzero_p ())
    return (bb->count.to_gcov_type () / MAX (entry.to_gcov_type (), 1)
	    >= E2K_MS_LONG);
  return e2k_loop_exact_iters (l->jump) >= E2K_MS_LONG;
}

/* When set, e2k_ms_pipeline only finds the II, stores it here and emits
   nothing (e2k_ms_try).  */
static int *e2k_ms_probe_ii;

/* Schedule and emit the analyzed loop L (e2k_ms_emit has the other
   arguments).  */
static bool
e2k_ms_pipeline (e2k_ms_loop *l, const vec<rtx_insn *> &pre_ends,
		 const vec<edge> &entries, edge exit_edge, const e2k_ms_wl *w)
{
  basic_block bb = l->bb;
  /* The dependences given far loads' latency, and what they had.  */
  auto_vec<std::pair<unsigned, int> > far;
  /* In a recurrence the crossing would set II (adler32's 16 chained
     adds: 34 cycles instead of 16); e2k_assign_channels keeps such a
     chain in one cluster when it can (each operation goes where its
     operands cost no stall).  */
  {
    sbitmap *reach = sbitmap_vector_alloc (l->n, l->n);
    bitmap_vector_clear (reach, l->n);
    for (e2k_ms_dep &d : l->deps)
      bitmap_set_bit (reach[d.from], d.to);
    for (int k = 0; k < l->n; k++)
      for (int i = 0; i < l->n; i++)
	if (bitmap_bit_p (reach[i], k))
	  bitmap_ior (reach[i], reach[i], reach[k]);
    for (e2k_ms_dep &d : l->deps)
      if (d.cross && bitmap_bit_p (reach[d.to], d.from))
	{
	  d.lat -= d.cross;
	  d.cross = 0;
	}
    /* A load the array prefetch unit doesn't serve, and that no
       recurrence goes through, read E2K_MS_LOAD_FAR cycles on: so that
       the misses of several iterations are in flight at once, as lcc's
       kernels have them (its v3 mvt reads a column 22 iterations
       ahead; scheduled for L1, each miss stalls the whole kernel: 278
       cycles an element against lcc's 45 on the 4C).  Only in a loop
       known to run long, or bounded (the doloop pass's bound, from the
       loops around it or its arrays' types) somewhere between that and
       a million: the stages cost every way in, which short loops over
       data in L1 pay for nothing (CoreMark's matrix loops, bounded only
       by their counter's type, 50% slower; CoreMark 18%, xz -c 28%,
       with every pipelined loop's loads far), while PolyBench's
       triangular loops run up to N.  */
    HOST_WIDE_INT bound = e2k_loop_max_iters (l->jump);
    bool longish = (e2k_ms_long_p (l)
		    || (bound >= E2K_MS_LONG && bound <= (1 << 20)));
    if (e2k_ms_load_far > 0)
      for (e2k_ms_dep &d : l->deps)
	{
	  e2k_ms_node *ld = &l->nodes[d.from];
	  if (ld->store || !ld->mem || ld->apb || (ld->lock && !e2k_dam_far)
	      || ld->chk >= 0
	      || ld->value < 0 || bitmap_bit_p (reach[d.from], d.from)
	      || get_attr_type (ld->insn) != (ld->lock ? TYPE_LDLOCK
					      : TYPE_LOAD))
	    continue;
	  /* A gather (its address from another load of the loop, NPB CG's
	     p[colidx[k]]) misses L1 where a stream doesn't: in a counted
	     loop not known to run long, as far as an L2 hit (CG.W 4-5%
	     faster on the 8C2 and 2C3).  Not in a while loop, which may leave
	     early and pays the stages on every way in (CoreMark's list
	     searches: 1% slower).  */
	  if (!longish)
	    {
	      bool gather = false;
	      for (int k = 0; k < l->n && !gather && !l->wl
			      && e2k_ms_gather_far > 0; k++)
		if (k != d.from && l->nodes[k].mem && !l->nodes[k].store
		    && bitmap_bit_p (reach[k], d.from)
		    && !bitmap_bit_p (reach[d.from], k))
		  gather = true;
	      bool reads = false;
	      for (int k = 0; k < l->nodes[d.to].nuses; k++)
		if (!l->nodes[d.to].uses[k].pred
		    && l->nodes[d.to].uses[k].value == ld->value)
		  reads = true;
	      if (gather && reads && d.lat < (int) e2k_ms_gather_far)
		d.lat = e2k_ms_gather_far;
	      continue;
	    }
	  bool reads = false;
	  for (int k = 0; k < l->nodes[d.to].nuses; k++)
	    if (!l->nodes[d.to].uses[k].pred
		&& l->nodes[d.to].uses[k].value == ld->value)
	      reads = true;
	  if (reads && d.lat < (int) e2k_ms_load_far)
	    far.safe_push (std::make_pair ((unsigned) (&d - l->deps.address ()),
					   d.lat));
	}
    sbitmap_vector_free (reach);
  }
  int far_lat = e2k_ms_load_far;
  auto set_far = [&] (bool on)
    {
      for (auto &f : far)
	l->deps[f.first].lat = on ? MAX (far_lat, f.second) : f.second;
    };
  /* Half as far, or not at all below 8 cycles.  */
  auto nearer = [&] ()
    {
      far_lat /= 2;
      set_far (far_lat >= 8);
      if (far_lat < 8)
	far.truncate (0);
    };
  /* Lower bounds: operations per cycle, then the length of one
     iteration when not pipelined.  */
  int loads = 0, stores = 0, alu = 0, c03 = 0, c14 = 0, c0134 = 0, divs = 0;
  int kalu = 0;
  for (int i = 0; i < l->n; i++)
    {
      /* landp runs in the PLS, a mova in an AAS channel, not in an ALU
	 channel.  */
      enum attr_type t = get_attr_type (l->nodes[i].insn);
      /* Not in the kernel (e2k_ms_mark_kdead).  */
      if (l->nodes[i].kdead)
	{
	  kalu += t != TYPE_PLOG && t != TYPE_MOVA;
	  continue;
	}
      loads += !l->nodes[i].store && l->nodes[i].mem && !l->nodes[i].apb;
      stores += l->nodes[i].store;
      divs += t == TYPE_FDIV;
      alu += t != TYPE_PLOG && t != TYPE_MOVA;
      /* Packed operations, two or four channels.  */
      c03 += t == TYPE_PINT;
      c14 += t == TYPE_PINT14 || t == TYPE_PMUL || t == TYPE_ALU14;
      c0134 += e2k_packed_type_p (t) || t == TYPE_ALU14 || t == TYPE_ALU0134;
    }
  /* A store in ALC2 or ALC5 keeps a load out of ALC3 or ALC0 (gas,
     spec/isa/bundle.md), so an instruction holds 4 - 2 * stores loads.  */
  auto mii_of = [&] (int alu)
    {
      int m = MAX (CEIL (alu, 6), MAX (CEIL (loads + 2 * stores, 4),
				       CEIL (stores, 2)));
      m = MAX (m, MAX (CEIL (c03, 2), MAX (CEIL (c14, 2), CEIL (c0134, 4))));
      /* A divide every 2 cycles.  */
      return MAX (m, 2 * divs);
    };
  int mii = mii_of (alu);
  /* AAU stores pay for their setup (two AAU writes each, on every way
     in) only by the operations they take out of the kernel: where those
     wouldn't raise the bound, store as before (Linpack's daxpy, II 1
     either way: 1.2% slower on the 8C2 with them).  */
  if (l->nstaa && mii_of (alu + kalu) == mii)
    {
      l->staa_unwanted = true;
      return e2k_ms_why ("AAU stores would not pay");
    }
  if (l->napb)
    {
      /* Array prefetch costs about 20 cycles a run (the setup, and bap's
	 22 to the first mova, spec/isa/apb.md, "Timing") and takes the
	 memory latency out of the loop: a stream from memory without it
	 stalls on every cache line (PolyBench's jacobi-2d on the 8C2: 21.8
	 cycles an iteration for 2.0 modelled, 9 times slower).  lcc uses
	 it in every counted loop it can (apb.md, "How lcc uses APB"); so
	 here too, except where the movas don't shorten the kernel and the
	 profile, or else the count the doloop pass knew, says the loop runs
	 fewer than E2K_APB_MIN_TRIP times.  */
      int mii_apb = MAX (mii, CEIL (l->napb, 4));
      int mii_ld = MAX (mii, MAX (CEIL (alu + l->napb, 6),
				  CEIL (loads + l->napb + 2 * stores, 4)));
      gcov_type iters;
      profile_count entry = profile_count::zero ();
      edge e;
      edge_iterator ei;
      FOR_EACH_EDGE (e, ei, bb->preds)
	if (e->src != bb)
	  entry += e->count ();
      if (bb->count.reliable_p () && entry.reliable_p () && entry.nonzero_p ())
	iters = bb->count.to_gcov_type () / MAX (entry.to_gcov_type (), 1);
      else
	iters = e2k_loop_max_iters (l->jump);
      if (iters < 0 && !e2k_apb_unknown)
	iters = 0;
      if (mii_ld <= mii_apb && iters >= 0 && iters < E2K_APB_MIN_TRIP
	  && !e2k_apb_force && !e2k_ms_apb_big_p ())
	return e2k_ms_why ("array prefetch would not pay");
      mii = mii_apb;
    }
  /* A while loop's exit predicate lives 3 cycles at least, and without
     rotation (e2k_ms_assign_pnames) at most II.  */
  if (l->wl && !e2k_rotate_preds)
    mii = MAX (mii, 3);
  /* One iteration alone: its critical path (through dependences
     within the iteration) or its operations at 6 per cycle; with loads
     read at their latency.  */
  int asap[E2K_MS_MAX_NODES], len = CEIL (l->n, 6);
  for (int i = 0; i < l->n; i++)
    {
      asap[i] = 0;
      for (e2k_ms_dep &d : l->deps)
	if (d.to == i && d.dist == 0 && d.from < i)
	  asap[i] = MAX (asap[i], asap[d.from] + d.lat);
    }
  for (e2k_ms_dep &d : l->deps)
    if (d.dist == 0)
      len = MAX (len, asap[d.from] + d.lat + 1);
  for (int i = 0; i < l->n; i++)
    len = MAX (len, asap[i] + 1);
  if (l->wl)
    len = MAX (len, asap[l->stay] + 3 + 1);
  set_far (true);
  /* Where the body's order fails at an II, the earliest starts at that
     II (e2k_ms_schedule); not in a first attempt that a lock load may
     still improve (e2k_ms_try retries with the DAM), but once the II
     with one has been weighed (NPB LU's blts: no II with a lock load,
     II 274 by the body's order, 207 by the earliest starts).  */
  bool est_ok = e2k_ms_est && (!l->may_dam || l->want_dam || !e2k_dam
			       || l->dam_settled);
  int ii = MAX (mii, 1);
  /* Worth a prologue, a ring and two setbn only if the kernel is
     clearly shorter than one iteration; or shorter at all when the loop
     is known to run long (PolyBench's seidel-2d: II 38 for an iteration
     of 49 cycles, as lcc's, 1998 times).  */
  bool longrun = e2k_ms_long && e2k_ms_long_p (l);
  /* A loop that a recurrence holds to about one iteration still gains
     the array prefetch of its other streams when they likely come from
     memory (e2k_ms_apb_big_p): NPB SP's z_solve sweeps, 180 cycles an
     iteration on the 2C3 for 45 modelled, the divide's chain through
     the element the last iteration stored.  */
  bool apb_recur = (e2k_ms_apb_recur && l->napb > 0 && !l->wl
		    && e2k_ms_apb_big_p ());
  /* Unpipelined, an iteration also waits for what the last one fed it
     (the store of that element, then its load).  */
  int rec = len;
  for (e2k_ms_dep &d : l->deps)
    if (d.dist > 0)
      rec = MAX (rec, CEIL (asap[d.from] + d.lat - asap[d.to], d.dist));
  auto worth = [&] (int ii)
    {
      return ((ii + 2 <= len && (longrun || 4 * ii <= 3 * len))
	      || (l->n >= E2K_MS_BIG && 4 * ii <= e2k_ms_big_ii * len)
	      || (apb_recur && ii <= rec + 4))
	     && ii <= E2K_MS_MAX_II;
    };
  /* A big loop whose operations fill the channels about as long as one
     iteration takes gains little from overlap and pays for it in names
     (NPB LU's jacld: 618 operations, MII 105 for an iteration of 103
     cycles, its ring too big for every overlapped II below 139).  Once
     an overlapped schedule would take clearly longer than one iteration,
     one stage, as lcc runs these loops (P53 in the PoC's findings), is
     searched beside it: one iteration a pass of the kernel, which keeps
     the ring's renaming and array prefetch that the list schedule after
     register allocation lacks (161 instructions there, the loads'
     misses unhidden).  CAND[0] is the next II to try overlapped, CAND[1]
     in one stage, ALIVE while each may still fit; the lower goes first,
     so the first to fit, names and prologue too, is the shorter (jacld:
     one stage at II 124; jacu, in ssor: overlapped at 126 on the 2C3,
     one stage at 122 on the 8C2).  ONE: the stage tried now.  */
  bool one = false, dual = false;
  int cand[2] = { 0, 0 };
  bool alive[2] = { true, true };
  /* To the lower candidate; false if neither is left.  */
  auto pick = [&] ()
    {
      if (!alive[0] && !alive[1])
	return false;
      one = alive[1] && (!alive[0] || cand[1] < cand[0]);
      ii = cand[one];
      return true;
    };
  /* Overlapped next at NEXT (INT_MAX: no more): both from here?  */
  auto go_dual = [&] (int next)
    {
      if (dual || !e2k_ms_one_stage || l->n < E2K_MS_BIG || l->wl
	  || 10 * mii < 9 * len || next <= len + len / 8)
	return false;
      dual = true;
      cand[0] = next;
      cand[1] = MAX (mii, len);
      alive[0] = next != INT_MAX;
      alive[1] = true;
      return pick ();
    };
  for (;;)
    {
      bool ok = false, est = false;
      for (; worth (ii) && (!dual || !alive[!one] || ii <= cand[!one]); ii++)
	{
	  if (one ? (e2k_ms_schedule_one (l, ii, false)
		     || e2k_ms_schedule_one (l, ii, true))
	      : e2k_ms_schedule (l, ii, false))
	    ok = true;
	  else if (one)
	    ;
	  else if (est_ok && e2k_ms_schedule (l, ii, true))
	    ok = est = true;
	  else if (est_ok && e2k_ms_schedule (l, ii, true, true))
	    ok = est = true;
	  if (ok)
	    break;
	}
      if (ok && dump_file)
	fprintf (dump_file, ";; e2k_modsched: loop bb %d: %d insns, "
		 "II %d, %d stages, unpipelined %d%s%s\n", bb->index, l->n,
		 l->ii, l->stages, len, l->wl ? ", while loop" : "",
		 est ? ", by earliest start" : "");
      if (ok && dump_file && (dump_flags & TDF_DETAILS))
	e2k_ms_dump_recurrence (l);
      /* Past the other's candidate, or no more of these.  */
      if (!ok && dual)
	{
	  if (worth (ii))
	    cand[one] = ii;
	  else
	    alive[one] = false;
	  if (pick ())
	    continue;
	  dual = false;
	  one = false;
	}
      if (!ok && far.is_empty () && go_dual (INT_MAX))
	continue;
      /* Far loads cost stages and names, never II: nearer before a
	 longer II (PolyBench's deriche on v3: its II-1 loops need 56
	 stages with them, more names than the ring has).  */
      if (!ok && !far.is_empty ())
	{
	  nearer ();
	  ii = MAX (mii, 1);
	  continue;
	}
      if (!ok)
	{
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: loop bb %d: %d insns, MII "
		     "%d, one iteration %d cycles\n", bb->index, l->n, mii,
		     len);
	  return e2k_ms_fail (bb, "no schedule shorter than one iteration");
	}
      if (e2k_ms_probe_ii)
	{
	  *e2k_ms_probe_ii = l->ii;
	  return false;
	}
      e2k_ms_dam_plan (l);
      const char *why = NULL;
      if (!e2k_ms_assign_names (l, 0)
	  && (e2k_ms_rebase_stores (l, false), !e2k_ms_assign_names (l, 0))
	  && (!e2k_ms_shorten || (e2k_ms_compact (l),
				!e2k_ms_assign_names (l, 0))))
	why = "ring too big";
      else if (!e2k_ms_assign_pnames (l))
	why = "predicate ring";
      /* Lifetimes that touch let two instructions of one cycle each write
	 what the other reads, which the prologue can't do in sequence;
	 then keep a cycle between them.  (e2k_ms_emit fails before it
	 emits anything.)  */
      else if (!e2k_ms_emit (l, pre_ends, entries, exit_edge, w)
	       && (!e2k_ms_assign_names (l, 1)
		   || !e2k_ms_emit (l, pre_ends, entries, exit_edge, w)))
	why = "prologue order";
      if (!why)
	break;
      if (!far.is_empty ())
	{
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: II %d: %s; loads %d cycles "
		     "on\n", ii, why, far_lat / 2 >= 8 ? far_lat / 2 : 0);
	  e2k_ms_rebase_stores (l, true);
	  nearer ();
	  continue;
	}
      /* A longer II needs fewer names: try it while the kernel is still
	 clearly shorter than one iteration.  With array prefetch that
	 beats the same II without it (fdtd-2d's first loop: 25 stages at
	 II 1 needed 64 names; at II 2 it fits, and the movas keep the
	 memory latency out of the loop); and the body's order at a longer
	 II may fit where the earliest starts didn't.  */
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: II %d%s: %s\n", ii,
		 est ? " by earliest start" : "", why);
      e2k_ms_rebase_stores (l, true);
      /* A big loop fits its ring at a few percent longer, if at all:
	 fewer stages, not a cycle more, make the difference (jacld: 3
	 stages up to II 133, 2 at 134).  */
      int next = ii + (l->n >= E2K_MS_BIG ? MAX (1, ii / 16) : 1);
      if (go_dual (next))
	continue;
      bool more = (est || ((ii + 3 <= len || l->n >= E2K_MS_BIG)
			   && worth (next)));
      if (dual)
	{
	  cand[one] = next;
	  alive[one] = more;
	  if (pick ())
	    continue;
	  return e2k_ms_fail (bb, why);
	}
      if (!more)
	return e2k_ms_fail (bb, why);
      ii = next;
    }
  cfun->machine->rot_pairs = MAX (cfun->machine->rot_pairs, l->pairs);
  if (l->npred)
    cfun->machine->rot_preds = true;
  return true;
}

/* What e2k_ms_fuse_fma changed, to put back (e2k_ms_unfuse_fma): the
   add or subtract, its source before, and the multiply it took in.  */
struct e2k_fma_undo
{
  rtx_insn *use;
  rtx src;
  rtx mult;
  location_t loc;
};

static bool e2k_ms_fuse_fma (basic_block, bitmap, vec<e2k_fma_undo> * = NULL);
static void e2k_ms_unfuse_fma (vec<e2k_fma_undo> &);

/* Analyze and pipeline L (e2k_ms_emit has the other arguments); if
   that fails for loads that may read what the loop's stores write, try
   again with a lock load (DAM).  Deletes L.  */
static bool
e2k_ms_try (e2k_ms_loop *l, basic_block exit, const vec<rtx_insn *> &pre_ends,
	    const vec<edge> &entries, edge exit_edge, const e2k_ms_wl *w)
{
  basic_block bb = l->bb;
  int retries = 0;
  /* L's loop again, analyzed afresh with WANT_DAM, APB_OK and STAA_OK.  */
  auto again_with = [&] (bool want_dam, bool apb_ok, bool staa_ok)
    {
      e2k_ms_loop *l2 = new e2k_ms_loop;
      l2->bb = l->bb;
      l2->jump = l->jump;
      for (rtx_insn *insn : l->insns)
	l2->insns.safe_push (insn);
      l2->wl = l->wl;
      l2->stay = l2->c1 = -1;
      l2->nh = l2->nh0 = l->nh0;
      l2->p1 = l->p1;
      l2->pstay = l->pstay;
      l2->e1 = l->e1;
      l2->x1 = l->x1;
      l2->edisp = l->edisp;
      l2->want_dam = want_dam;
      l2->may_dam = false;
      l2->dam_settled = l->dam_settled;
      l2->dam = l2->kchk = -1;
      l2->apb_ok = apb_ok;
      l2->staa_ok = staa_ok;
      l2->apb_tmp = l->apb_tmp;
      l2->binv = l->binv;
      delete l;
      l = l2;
    };
  bool dam_first = false, probed = false, fma_probed = false;
  bool apb0 = l->apb_ok, staa0 = l->staa_ok;
  /* The loop's insns again from its block, after e2k_ms_fuse_fma or
     its undoing changed them.  */
  auto reread = [&] ()
    {
      l->insns.truncate (0);
      rtx_insn *insn;
      FOR_BB_INSNS (bb, insn)
	if (NONDEBUG_INSN_P (insn) && insn != l->jump)
	  l->insns.safe_push (insn);
    };
  for (int attempt = 0; ; attempt++)
    {
      bool ok = e2k_ms_analyze (l, exit);
      /* A loop not known to run long gets combined FP operations
	 (e2k_ms_fuse_fma) only where they shorten its II: NPB FT's
	 butterfly, 16 elements a run, fits II 2 with them (8 FP
	 operations and 4 AAU stores in the ALU channels, as lcc's
	 kernel), II 3 without; Linpack's daxpy, II 1 either way, only
	 gets a longer pipeline.  */
      if (ok && !fma_probed && !l->wl && e2k_ms_fma && e2k_ms_fma_ii
	  && !e2k_ms_long_p (l))
	{
	  int ii0 = INT_MAX, ii1 = INT_MAX;
	  fma_probed = true;
	  /* The II of L as analyzed; again without AAU stores where they
	     wouldn't pay (which ends the attempt before any II).  */
	  auto probe = [&] (int *ii)
	    {
	      e2k_ms_probe_ii = ii;
	      e2k_ms_pipeline (l, pre_ends, entries, exit_edge, w);
	      if (*ii == INT_MAX && l->staa_unwanted)
		{
		  again_with (l->want_dam, apb0, false);
		  if (e2k_ms_analyze (l, exit))
		    e2k_ms_pipeline (l, pre_ends, entries, exit_edge, w);
		}
	      e2k_ms_probe_ii = NULL;
	    };
	  probe (&ii0);
	  auto_vec<e2k_fma_undo> undo;
	  bool was = cfun->machine->ms_fma;
	  if (ii0 < INT_MAX
	      && e2k_ms_fuse_fma (bb, df_get_live_out (bb), &undo))
	    {
	      reread ();
	      again_with (l->want_dam, apb0, staa0);
	      if (e2k_ms_analyze (l, exit))
		probe (&ii1);
	      if (dump_file)
		fprintf (dump_file, ";; e2k_modsched: loop bb %d: II %d, "
			 "with combined FP operations %d\n", bb->index, ii0,
			 ii1 == INT_MAX ? -1 : ii1);
	      if (ii1 >= ii0)
		{
		  e2k_ms_unfuse_fma (undo);
		  cfun->machine->ms_fma = was;
		  reread ();
		}
	      again_with (l->want_dam, apb0, staa0);
	      ok = e2k_ms_analyze (l, exit);
	    }
	}
      /* A recurrence through memory can set the II where a lock load
	 would not (NPB IS's histogram, "prv_buff1[key_buff2[i]]++": II 5
	 a key, each load waiting for the last store; lcc takes about 1.3
	 cycles): find the II both ways, and take data speculation first
	 when it is clearly shorter.  */
      if (ok && !probed && !l->want_dam && l->may_dam && e2k_dam)
	{
	  int ii0 = INT_MAX, ii1 = INT_MAX;
	  probed = true;
	  e2k_ms_probe_ii = &ii0;
	  e2k_ms_pipeline (l, pre_ends, entries, exit_edge, w);
	  again_with (true, e2k_dam_apb && apb0, e2k_dam_apb && staa0);
	  if (e2k_ms_analyze (l, exit))
	    {
	      e2k_ms_probe_ii = &ii1;
	      e2k_ms_pipeline (l, pre_ends, entries, exit_edge, w);
	    }
	  e2k_ms_probe_ii = NULL;
	  dam_first = ii1 < INT_MAX && (ii0 == INT_MAX || 3 * ii1 <= 2 * ii0);
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: loop bb %d: II %d, with "
		     "DAM %d%s\n", bb->index, ii0 == INT_MAX ? -1 : ii0,
		     ii1 == INT_MAX ? -1 : ii1, dam_first ? ": DAM first" : "");
	  again_with (dam_first, dam_first && !e2k_dam_apb ? false : apb0,
		      dam_first && !e2k_dam_apb ? false : staa0);
	  l->dam_settled = true;
	  ok = e2k_ms_analyze (l, exit);
	}
      if (!ok)
	e2k_ms_fail (bb, "body");
      else
	ok = e2k_ms_pipeline (l, pre_ends, entries, exit_edge, w);
      /* Data speculation first failed: as before, without it.  */
      if (!ok && dam_first)
	{
	  dam_first = false;
	  again_with (false, apb0, staa0);
	  attempt--;
	  continue;
	}
      /* The same without AAU stores, if they wouldn't pay.  */
      if (!ok && l->staa_unwanted)
	{
	  again_with (l->want_dam, l->apb_ok, false);
	  attempt--;
	  continue;
	}
      /* Without array prefetch, if that failed with it; then without
	 AAU stores.  */
      bool apb_again = !ok && l->napb > 0;
      bool again = apb_again || (!ok && l->nstaa > 0);
      if (!again && (ok || attempt > retries || !l->may_dam || !e2k_dam))
	{
	  delete l;
	  return ok;
	}
      retries += again;
      /* Without array prefetch or AAU stores keeps a lock load (they go
	 together with -mdam-apb); the first attempt with one may have
	 both.  */
      if (again)
	again_with (e2k_dam_apb && l->want_dam, false,
		    apb_again && l->staa_ok);
      else
	again_with (true, e2k_dam_apb && apb0, e2k_dam_apb && staa0);
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: loop bb %d again with%s\n",
		 bb->index, apb_again ? "out array prefetch"
		 : again ? "out AAU stores" : " DAM");
    }
}

/* %b[0..7] can't hold a value a pipelined loop uses: setbn renames
   them.  Give each one the loop uses a register free around and in the
   loop, for the loop: copied there before it if live into it,
   back after it (after the setbn that gives the outgoing registers
   back) if live after it.  False if there's none free.  Under high
   register pressure (main of Linpack, everything inlined) allocation
   puts loop invariants there once the window is full; for an invariant
   with no register free, BINV (when not null) gets bit K instead (see
   e2k_ms_loop).  */
static bool
e2k_ms_move_b (const vec<basic_block> &bbs, const vec<rtx_insn *> &pre_ends,
	       const vec<edge> &entries, edge exit_edge, unsigned *binv)
{
  CLEAR_HARD_REG_SET (e2k_ms_live_out_extra);
  bool used[8] = { false };
  HARD_REG_SET body;
  CLEAR_HARD_REG_SET (body);
  rtx_insn *insn;
  for (basic_block bb : bbs)
    FOR_BB_INSNS (bb, insn)
      if (INSN_P (insn))
	{
	  subrtx_iterator::array_type array;
	  FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
	    if (REG_P (*iter) && REGNO (*iter) < FIRST_PSEUDO_REGISTER)
	      {
		if (B_REGNO_P (REGNO (*iter)))
		  {
		    if (REG_NREGS (*iter) != 1)
		      return false;
		    used[REGNO (*iter) - B0_REGNUM] = true;
		  }
		add_to_hard_reg_set (&body, GET_MODE (*iter), REGNO (*iter));
	      }
	}
  basic_block bb = bbs[0];
  bitmap lh = df_get_live_in (bb), lx = df_get_live_in (exit_edge->dest);
  /* An entry by a prepared conditional transfer can't be split (its
     disp would send it past the new block): the copies go before its
     jump, so their registers must be dead on its other way too.  */
  auto cond_entry = [] (edge e)
    {
      return (!(e->flags & EDGE_FALLTHRU) && !single_succ_p (e->src)
	      && JUMP_P (BB_END (e->src)));
    };
  auto_bitmap lo;
  for (edge e : entries)
    if (cond_entry (e))
      {
	edge o;
	edge_iterator ei;
	FOR_EACH_EDGE (o, ei, e->src->succs)
	  if (o != e)
	    bitmap_ior_into (lo, df_get_live_in (o->dest));
      }
  /* One the loop only sets and reads within an iteration needs nothing:
     the pipeliner renames its value (NPB SP's eta-direction fluxes, with
     every other register taken).  */
  for (int k = 0; k < 8; k++)
    if (used[k] && !bitmap_bit_p (lh, B0_REGNUM + k)
	&& !bitmap_bit_p (lx, B0_REGNUM + k))
      used[k] = false;
  unsigned map[8];
  int n = 0;
  for (int k = 0; k < 8; k++)
    if (used[k])
      {
	auto free_p = [&] (unsigned g)
	  {
	    for (int k2 = 0; k2 < k; k2++)
	      if (used[k2] && map[k2] == g)
		return false;
	    return (!fixed_regs[g] && !TEST_HARD_REG_BIT (body, g)
		    && !bitmap_bit_p (lh, g) && !bitmap_bit_p (lx, g)
		    && !bitmap_bit_p (lo, g));
	  };
	/* A global (%g16..%g31), else a window register the function
	   has, else one that grows the window (e2k_compute_window sizes
	   it from what the insns use).  */
	unsigned g = INVALID_REGNUM;
	for (unsigned r = 0; r < 32 && g == INVALID_REGNUM; r++)
	  if (free_p (r))
	    g = r;
	for (unsigned r = R0_REGNUM; r < R0_REGNUM + 64 && g == INVALID_REGNUM;
	     r++)
	  if (df_regs_ever_live_p (r) && free_p (r))
	    g = r;
	for (unsigned r = R0_REGNUM; r < R0_REGNUM + 64 && g == INVALID_REGNUM;
	     r++)
	  if (free_p (r))
	    g = r;
	if (g == INVALID_REGNUM)
	  {
	    /* An invariant the loop only reads: the pipeliner may give it a
	       register its renamed values leave free (BINV; NPB SP's
	       eta- and zeta-direction fluxes, every register taken).  */
	    bool set = false;
	    rtx reg = gen_rtx_REG (DImode, B0_REGNUM + k);
	    for (basic_block b : bbs)
	      FOR_BB_INSNS (b, insn)
		if (INSN_P (insn) && reg_set_p (reg, insn))
		  set = true;
	    if (!binv || set || !bitmap_bit_p (lh, B0_REGNUM + k))
	      return false;
	    *binv |= 1u << k;
	    used[k] = false;
	    continue;
	  }
	map[k] = g;
	n++;
      }
  if (!n)
    return true;
  if (dump_file)
    for (int k = 0; k < 8; k++)
      if (used[k])
	fprintf (dump_file, ";; e2k_modsched: loop bb %d: %%b[%d] -> %s%s%s\n",
		 bb->index, k, reg_names[map[k]],
		 bitmap_bit_p (lh, B0_REGNUM + k) ? ", copied in" : "",
		 bitmap_bit_p (lx, B0_REGNUM + k) ? ", copied out" : "");
  for (rtx_insn *pre_end : pre_ends)
    for (int k = 0; k < 8; k++)
      if (used[k] && bitmap_bit_p (lh, B0_REGNUM + k))
	{
	  rtx_insn *c = emit_insn_before
	    (gen_rtx_SET (gen_rtx_REG (DImode, map[k]),
			  gen_rtx_REG (DImode, B0_REGNUM + k)), pre_end);
	  recog_memoized (c);
	}
  for (edge e : entries)
    {
      start_sequence ();
      for (int k = 0; k < 8; k++)
	if (used[k] && bitmap_bit_p (lh, B0_REGNUM + k))
	  recog_memoized (emit_insn (gen_rtx_SET (gen_rtx_REG (DImode, map[k]),
						  gen_rtx_REG (DImode,
							       B0_REGNUM + k))));
      rtx_insn *seq = end_sequence ();
      if (seq && cond_entry (e))
	emit_insn_before (seq, BB_END (e->src));
      else if (seq)
	insert_insn_on_edge (seq, e);
    }
  for (basic_block bb2 : bbs)
    FOR_BB_INSNS (bb2, insn)
      if (INSN_P (insn))
	{
	  bool changed = false;
	  subrtx_ptr_iterator::array_type array;
	  FOR_EACH_SUBRTX_PTR (iter, array, &PATTERN (insn), NONCONST)
	    {
	      rtx *loc = *iter;
	      if (REG_P (*loc) && B_REGNO_P (REGNO (*loc))
		  && used[REGNO (*loc) - B0_REGNUM])
		{
		  *loc = gen_rtx_REG (GET_MODE (*loc),
				      map[REGNO (*loc) - B0_REGNUM]);
		  changed = true;
		}
	    }
	  if (REG_NOTES (insn))
	    FOR_EACH_SUBRTX_PTR (iter, array, &REG_NOTES (insn), NONCONST)
	      {
		rtx *loc = *iter;
		if (*loc && REG_P (*loc) && B_REGNO_P (REGNO (*loc))
		    && used[REGNO (*loc) - B0_REGNUM])
		  *loc = gen_rtx_REG (GET_MODE (*loc),
				      map[REGNO (*loc) - B0_REGNUM]);
	      }
	  if (changed)
	    {
	      INSN_CODE (insn) = -1;
	      df_insn_rescan (insn);
	    }
	}
  start_sequence ();
  for (int k = 0; k < 8; k++)
    if (used[k] && bitmap_bit_p (lx, B0_REGNUM + k))
      {
	emit_insn (gen_rtx_SET (gen_rtx_REG (DImode, B0_REGNUM + k),
				gen_rtx_REG (DImode, map[k])));
	SET_HARD_REG_BIT (e2k_ms_live_out_extra, map[k]);
      }
  rtx_insn *after = end_sequence ();
  if (after)
    insert_insn_on_edge (after, exit_edge);
  df_analyze ();
  return true;
}

static bool
e2k_ms_fail (basic_block bb, const char *why)
{
  if (dump_file)
    fprintf (dump_file, ";; e2k_modsched: loop bb %d not pipelined: %s\n",
	     bb->index, why);
  return false;
}

/* Whether L, a counted loop, may read through array prefetch (spec/isa/
   apb.md): a hardware loop end through %ctpr1 (not the strip-mined one,
   whose next chunk would restart the count the unit's positions follow
   after a trap), and %ctpr2, which holds the program, free on the way
   into the loop (the setup goes after what ends the blocks of
   PRE_ENDS, the waits after rwd %lsr), through it, and after it (EXIT).
   Also picks the register the setup computes the areas' addresses in:
   a window register dead on every way in.  Sets L->staa_ok if the loop
   may store through the AAU (e2k_ms_mark_staa), which needs that
   register but not %ctpr2.  */
static bool
e2k_ms_apb_ok (e2k_ms_loop *l, const vec<rtx_insn *> &pre_ends,
	       basic_block exit)
{
  l->staa_ok = false;
  if (!e2k_apb && !e2k_staa)
    return false;
  if (recog_memoized (l->jump) != CODE_FOR_e2k_hwloop_end)
    return e2k_ms_why ("no array prefetch: not a plain counted loop");
  HARD_REG_SET used, tail;
  CLEAR_HARD_REG_SET (used);
  CLEAR_HARD_REG_SET (tail);
  for (rtx_insn *insn : l->insns)
    e2k_note_regs (PATTERN (insn), &used);
  for (rtx_insn *pre_end : pre_ends)
    {
      basic_block pb = BLOCK_FOR_INSN (pre_end);
      for (rtx_insn *x = NEXT_INSN (pre_end); x && x != NEXT_INSN (BB_END (pb));
	   x = NEXT_INSN (x))
	if (INSN_P (x))
	  e2k_note_regs (PATTERN (x), &tail);
    }
  used |= tail;
  l->apb_tmp = INVALID_REGNUM;
  /* The setup runs where the loop starts and the end of the program
     where it has ended: a register dead at both will do.  First one the
     loop doesn't touch; failing that, one only the loop's own values use
     (Linpack's main has all 64 in use): the kernel and the prologue hold
     those in the ring, and the copies out write theirs after the end.  */
  for (int pass = 0; pass < 2 && l->apb_tmp == INVALID_REGNUM; pass++)
    for (unsigned r = R0_REGNUM; r < R0_REGNUM + 64; r++)
      {
	if (fixed_regs[r] || TEST_HARD_REG_BIT (pass ? tail : used, r))
	  continue;
	bool dead = !(pass && REGNO_REG_SET_P (df_get_live_in (exit), r));
	for (rtx_insn *pre_end : pre_ends)
	  if (REGNO_REG_SET_P (df_get_live_out (BLOCK_FOR_INSN (pre_end)), r))
	    dead = false;
	if (!dead)
	  continue;
	/* One the function uses already doesn't grow the window.  */
	if (l->apb_tmp == INVALID_REGNUM || df_regs_ever_live_p (r))
	  l->apb_tmp = r;
	if (df_regs_ever_live_p (r))
	  break;
      }
  if (l->apb_tmp == INVALID_REGNUM)
    return e2k_ms_why ("no array prefetch: no free register");
  /* AAU stores need no program in %ctpr2.  */
  l->staa_ok = e2k_staa;
  if (!e2k_apb)
    return false;
  rtx ctpr2 = gen_rtx_REG (DImode, CTPR2_REGNUM);
  if (reg_mentioned_p (ctpr2, PATTERN (l->jump)))
    return e2k_ms_why ("no array prefetch: %ctpr2 ends the loop");
  if (REGNO_REG_SET_P (df_get_live_in (l->bb), CTPR2_REGNUM)
      || REGNO_REG_SET_P (df_get_live_in (exit), CTPR2_REGNUM))
    return e2k_ms_why ("no array prefetch: %ctpr2 live around the loop");
  for (rtx_insn *insn : l->insns)
    if (reg_mentioned_p (ctpr2, PATTERN (insn)))
      return e2k_ms_why ("no array prefetch: %ctpr2 in the loop");
  return true;
}

/* The unroller's split induction variables in BB, a loop (-fsplit-ivs-
   in-unroller: gemm's two copies, "%g17 = %g16 + 8 ... %g16 = %g17 +
   8"): a chain of adds the pipeliner's II has to wait for, one cycle
   each.  R = R1 + C2 after R1 = R + C1, each set once in BB, becomes
   R = R + (C1 + C2), and R1 a register derived from R.  */
static void
e2k_ms_unsplit_ivs (basic_block bb)
{
  rtx_insn *insn;
  FOR_BB_INSNS (bb, insn)
    {
      rtx sb = NONDEBUG_INSN_P (insn) ? single_set (insn) : NULL_RTX;
      if (!sb || !REG_P (SET_DEST (sb)) || GET_MODE (SET_DEST (sb)) != DImode
	  || GET_CODE (SET_SRC (sb)) != PLUS || !REG_P (XEXP (SET_SRC (sb), 0))
	  || !CONST_INT_P (XEXP (SET_SRC (sb), 1)))
	continue;
      rtx r = SET_DEST (sb), r1 = XEXP (SET_SRC (sb), 0);
      if (REGNO (r1) == REGNO (r))
	continue;
      /* R1's one definition, before INSN: R + C1; R set only by INSN.  */
      rtx_insn *def = NULL;
      int nr = 0, nr1 = 0;
      bool before = false, seen = false;
      rtx_insn *x;
      FOR_BB_INSNS (bb, x)
	{
	  if (x == insn)
	    seen = true;
	  if (!NONDEBUG_INSN_P (x))
	    continue;
	  if (reg_set_p (r, x))
	    nr++;
	  if (reg_set_p (r1, x))
	    {
	      nr1++;
	      def = x;
	      before = !seen;
	    }
	}
      if (nr != 1 || nr1 != 1 || !def || !before)
	continue;
      rtx sa = single_set (def);
      if (!sa || GET_CODE (SET_SRC (sa)) != PLUS
	  || !REG_P (XEXP (SET_SRC (sa), 0))
	  || REGNO (XEXP (SET_SRC (sa), 0)) != REGNO (r)
	  || !CONST_INT_P (XEXP (SET_SRC (sa), 1)))
	continue;
      HOST_WIDE_INT c = (INTVAL (XEXP (SET_SRC (sa), 1))
			 + INTVAL (XEXP (SET_SRC (sb), 1)));
      if (c == 0)
	continue;
      if (validate_change (insn, &SET_SRC (sb),
			   gen_rtx_PLUS (DImode, r, GEN_INT (c)), 0)
	  && dump_file)
	fprintf (dump_file, ";; e2k_modsched: insn %d steps %s by %d\n",
		 INSN_UID (insn), reg_names[REGNO (r)], (int) c);
    }
}

/* In e2k_modsched: the DFA's reservations for a pipelined loop, where
   a lock load and its check may share a wide instruction
   (e2k-sched.md, "e2k_ldlock0").  */
bool e2k_dfa_ms;

/* Whether the combined FP operations' patterns match (-mfmul-add, or
   made by e2k_ms_fuse_fma in this function).  */
bool
e2k_fma_combined_p (void)
{
  return e2k_fmul_add || (cfun && cfun->machine && cfun->machine->ms_fma);
}

/* Combined FP operations for the multiplies of BB, a loop known to run
   long, whose product one add or subtract after them reads and nothing
   else: fmul_add, fmul_sub and fmul_rsub round the product before the
   add as the two operations would (spec/isa/semantics.md), in one ALU
   channel instead of two, which shortens a kernel bound by its channels
   (lcc's gemm kernel: nine copies of "C[i][j] += t * B[k][j]" with
   fmul_addd in five wide instructions).  Not where the addend comes from
   the last iteration (a reduction): the combined operation reads it at
   issue, 4 cycles before the add would, and the recurrence grows; not in
   short loops, whose longer pipelines would cost their ways in more
   (Linpack's daxpy, -mfmul-add).  True if it made one.  */
static bool
e2k_ms_fuse_fma (basic_block bb, bitmap live_out, vec<e2k_fma_undo> *undo)
{
  bool any = false;
  /* Values on a recurrence: computed in the iteration from a register
     carried around the loop (live into it and set in it), and feeding
     the next value of one (an unrolled reduction's partial sum,
     PolyBench's bicg: II 4 an element, 6 with its second copy's add
     combined).  FWD and BACK by insn: not what only leads from the
     induction registers through addresses (heat-3d's loads).  */
  auto_bitmap setb, carried, cur;
  rtx_insn *insn, *next;
  FOR_BB_INSNS (bb, insn)
    if (NONDEBUG_INSN_P (insn))
      {
	df_ref def;
	FOR_EACH_INSN_DEF (def, insn)
	  bitmap_set_bit (setb, DF_REF_REGNO (def));
      }
  bitmap_and (carried, df_get_live_in (bb), setb);
  auto_sbitmap fwd (get_max_uid ()), back (get_max_uid ());
  bitmap_clear (fwd);
  bitmap_clear (back);
  bitmap_copy (cur, carried);
  FOR_BB_INSNS (bb, insn)
    if (NONDEBUG_INSN_P (insn))
      {
	bool from = false;
	df_ref ref;
	FOR_EACH_INSN_USE (ref, insn)
	  from |= bitmap_bit_p (cur, DF_REF_REGNO (ref));
	rtx ss = single_set (insn);
	if (from && ss && REG_P (SET_DEST (ss)))
	  bitmap_set_bit (fwd, INSN_UID (insn));
	FOR_EACH_INSN_DEF (ref, insn)
	  if (from && ss && REG_P (SET_DEST (ss)))
	    bitmap_set_bit (cur, DF_REF_REGNO (ref));
	  else
	    bitmap_clear_bit (cur, DF_REF_REGNO (ref));
      }
  bitmap_copy (cur, carried);
  FOR_BB_INSNS_REVERSE (bb, insn)
    if (NONDEBUG_INSN_P (insn))
      {
	rtx ss = single_set (insn);
	if (!ss || !REG_P (SET_DEST (ss))
	    || !bitmap_bit_p (cur, REGNO (SET_DEST (ss))))
	  continue;
	bitmap_set_bit (back, INSN_UID (insn));
	bitmap_clear_bit (cur, REGNO (SET_DEST (ss)));
	df_ref use;
	FOR_EACH_INSN_USE (use, insn)
	  bitmap_set_bit (cur, DF_REF_REGNO (use));
      }
  FOR_BB_INSNS_SAFE (bb, insn, next)
    {
      rtx ms = NONDEBUG_INSN_P (insn) ? single_set (insn) : NULL_RTX;
      if (!ms || !REG_P (SET_DEST (ms)) || GET_CODE (SET_SRC (ms)) != MULT)
	continue;
      machine_mode mode = GET_MODE (SET_DEST (ms));
      if (mode != DFmode && mode != SFmode)
	continue;
      rtx t = SET_DEST (ms);
      rtx a = XEXP (SET_SRC (ms), 0), b = XEXP (SET_SRC (ms), 1);
      if (!REG_P (a) || !REG_P (b))
	continue;
      /* The first reader of T, with A, B and T unchanged before it.  */
      rtx_insn *use = NULL;
      for (rtx_insn *x = NEXT_INSN (insn);
	   x && x != NEXT_INSN (BB_END (bb)); x = NEXT_INSN (x))
	{
	  if (!NONDEBUG_INSN_P (x))
	    continue;
	  if (reg_overlap_mentioned_p (t, PATTERN (x)))
	    {
	      use = x;
	      break;
	    }
	  if (reg_set_p (a, x) || reg_set_p (b, x))
	    break;
	}
      rtx us = use && NONJUMP_INSN_P (use) ? single_set (use) : NULL_RTX;
      if (!us || !REG_P (SET_DEST (us)) || GET_MODE (SET_DEST (us)) != mode
	  || (GET_CODE (SET_SRC (us)) != PLUS
	      && GET_CODE (SET_SRC (us)) != MINUS))
	continue;
      rtx x0 = XEXP (SET_SRC (us), 0), x1 = XEXP (SET_SRC (us), 1);
      bool t0 = rtx_equal_p (x0, t), t1 = rtx_equal_p (x1, t);
      if (t0 == t1)
	continue;
      rtx c = t0 ? x1 : x0;
      if (!REG_P (c) || reg_overlap_mentioned_p (t, c))
	continue;
      /* T read nowhere else: set again after USE in BB (or by it) before
	 any read, or dead when BB ends.  */
      bool dead = reg_set_p (t, use), more = false;
      for (rtx_insn *x = NEXT_INSN (use);
	   !dead && x && x != NEXT_INSN (BB_END (bb)); x = NEXT_INSN (x))
	if (NONDEBUG_INSN_P (x))
	  {
	    if (reg_referenced_p (t, PATTERN (x)))
	      more = true;
	    if (reg_set_p (t, x))
	      dead = true;
	    if (more)
	      break;
	  }
      if (more || (!dead && bitmap_bit_p (live_out, REGNO (t))))
	continue;
      /* The addend set at or after USE in BB comes from the last
	 iteration there; one on a recurrence lengthens it too.  */
      bool rec = false;
      for (rtx_insn *x = use; x && x != NEXT_INSN (BB_END (bb));
	   x = NEXT_INSN (x))
	if (NONDEBUG_INSN_P (x) && reg_set_p (c, x))
	  rec = true;
      for (rtx_insn *x = PREV_INSN (use);
	   !rec && x && x != PREV_INSN (BB_HEAD (bb)); x = PREV_INSN (x))
	if (NONDEBUG_INSN_P (x) && reg_set_p (c, x))
	  {
	    rec = (bitmap_bit_p (fwd, INSN_UID (x))
		   && bitmap_bit_p (back, INSN_UID (x)));
	    break;
	  }
      if (rec)
	continue;
      rtx prod = gen_rtx_MULT (mode, a, b);
      rtx src = (GET_CODE (SET_SRC (us)) == PLUS
		 ? gen_rtx_PLUS (mode, prod, c)
		 : t0 ? gen_rtx_MINUS (mode, prod, c)
		 : gen_rtx_MINUS (mode, c, prod));
      bool was = cfun->machine->ms_fma;
      cfun->machine->ms_fma = true;
      rtx old_src = SET_SRC (us);
      if (!validate_change (use, &SET_SRC (us), src, 0))
	{
	  cfun->machine->ms_fma = was;
	  continue;
	}
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: insn %d and %d combined\n",
		 INSN_UID (insn), INSN_UID (use));
      if (undo)
	{
	  e2k_fma_undo u = { use, old_src, copy_rtx (PATTERN (insn)),
			     INSN_LOCATION (insn) };
	  undo->safe_push (u);
	}
      delete_insn (insn);
      any = true;
    }
  return any;
}

/* Put back what e2k_ms_fuse_fma combined, as UNDO recorded.  */
static void
e2k_ms_unfuse_fma (vec<e2k_fma_undo> &undo)
{
  for (unsigned i = undo.length (); i-- > 0; )
    {
      e2k_fma_undo &u = undo[i];
      rtx us = single_set (u.use);
      bool ok = validate_change (u.use, &SET_SRC (us), u.src, 0);
      gcc_assert (ok);
      rtx_insn *m = emit_insn_before (u.mult, u.use);
      INSN_LOCATION (m) = u.loc;
      if (recog_memoized (m) < 0)
	gcc_unreachable ();
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: insn %d and %d apart again\n",
		 INSN_UID (m), INSN_UID (u.use));
    }
  undo.truncate (0);
}

/* Pipeline the loop that BB is, ending in the hardware loop end JUMP.  */
static bool
e2k_ms_loop_1 (basic_block bb, rtx_insn *jump)
{
  if (EDGE_COUNT (bb->succs) != 2)
    return e2k_ms_fail (bb, "edges");
  edge exit_edge = NULL, e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, bb->succs)
    if (e->dest != bb)
      exit_edge = e;
  if (!exit_edge || (exit_edge->flags & EDGE_COMPLEX))
    return e2k_ms_fail (bb, "edges");
  /* Each way in ends with the wait after rwd %lsr (hw-doloop sets %lsr
     up on every incoming edge); the prologue goes in front of it.  */
  auto_vec<rtx_insn *> pre_ends;
  FOR_EACH_EDGE (e, ei, bb->preds)
    if (e->src != bb)
      {
	/* Past a jump to the loop and a disp that loop branch preparation
	   may have put on the same edge.  */
	rtx_insn *pre_end = BB_END (e->src);
	while (pre_end
	       && (!NONDEBUG_INSN_P (pre_end)
		   || (JUMP_P (pre_end) && JUMP_LABEL (pre_end) == BB_HEAD (bb)
		       && pre_end == BB_END (e->src))
		   || recog_memoized (pre_end) == CODE_FOR_e2k_disp_label))
	  pre_end = PREV_INSN (pre_end);
	if ((e->flags & EDGE_COMPLEX)
	    || !pre_end || recog_memoized (pre_end) != CODE_FOR_e2k_lsr_wait)
	  return e2k_ms_fail (bb, "preheader");
	pre_ends.safe_push (pre_end);
      }
  if (pre_ends.is_empty () || pre_ends.length () > 4)
    return e2k_ms_fail (bb, "preheader");

  auto_vec<basic_block> bbs;
  bbs.safe_push (bb);
  auto_vec<edge> no_entries;
  unsigned binv = 0;
  if (!e2k_ms_move_b (bbs, pre_ends, no_entries, exit_edge, &binv))
    return e2k_ms_fail (bb, "no free register for a %b[] value");

  e2k_ms_loop *l = new e2k_ms_loop;
  l->bb = bb;
  l->jump = jump;
  l->wl = false;
  l->stay = l->c1 = -1;
  l->p1 = l->pstay = NULL_RTX;
  l->x1 = NULL;
  l->edisp = NULL;
  l->nh = l->nh0 = 0;
  l->want_dam = l->may_dam = l->dam_settled = false;
  l->dam = l->kchk = -1;
  l->binv = binv;
  e2k_ms_unsplit_ivs (bb);
  if (e2k_ms_fma && e2k_ms_long_p (l))
    e2k_ms_fuse_fma (bb, df_get_live_out (bb));
  rtx_insn *insn;
  FOR_BB_INSNS (bb, insn)
    if (NONDEBUG_INSN_P (insn) && insn != jump)
      l->insns.safe_push (insn);
  l->apb_ok = e2k_ms_apb_ok (l, pre_ends, exit_edge->dest);
  return e2k_ms_try (l, exit_edge->dest, pre_ends, no_entries, exit_edge,
		     NULL);
}

/* Whether X reads memory e2k_short_chain marked as a hash chain's next
   node.  */
static bool
e2k_chain_ref_p (rtx x)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, x, NONCONST)
    if (MEM_P (*iter) && MEM_EXPR (*iter))
      {
	tree base = get_base_address (MEM_EXPR (*iter));
	if (base
	    && (TREE_CODE (base) == MEM_REF
		|| TREE_CODE (base) == TARGET_MEM_REF)
	    && MR_DEPENDENCE_CLIQUE (base) == cfun->machine->chain_clique)
	  return true;
      }
  return false;
}

/* While loops (spec/isa/loops.md, "Early exits and while loops"): a
   block H that ends "if (p) goto H" (or "if (!p)"), with p set in it,
   or two blocks, H ending "if (p1) goto X" and the one it falls through
   to, B, ending "if (p2) goto H" and falling through to X too, as
   "while (list && list->x != k) list = list->next" becomes.  Pipelined
   like a counted loop, but the kernel runs until the test says stop:
   every operation is speculative (the kernel runs the early stages of
   iterations past the end), the loop end "abn; ct %ctprN ? p" is in the
   last row of the last stage, and every other node is before it, so
   the iteration the loop ends with is complete (stores in the last
   stage too).  Two blocks become one: B's operations also run when H's
   exit is taken, speculatively (so B must not store), and "landp ~p1,
   p2" (lazy: p2's diagnostic tag doesn't count when p1 is set) is the
   loop end's test.  After the loop, H's exit compare runs again on the
   last iteration's values, and the registers live at X get H's values
   under it, B's otherwise.  The test needs no rotating predicates as
   long as II is 3 or more (e2k_ms_place_exit).  */
static bool
e2k_ms_wloop (basic_block h)
{
  rtx_insn *jump = BB_END (h);
  rtx cond = e2k_ms_jump_cond (jump);
  if (!cond || recog_memoized (jump) < 0 || get_attr_type (jump) != TYPE_CT)
    return false;
  basic_block b = NULL, last = h, x1 = NULL;
  bool diff_exits = false;
  rtx_insn *ljump = jump, *hdisp = NULL;
  e2k_ms_wl w;
  memset (&w, 0, sizeof w);
  if (JUMP_LABEL (jump) != BB_HEAD (h))
    {
      /* Two blocks: H exits, B loops.  */
      edge f = find_fallthru_edge (h->succs);
      if (!f || EDGE_COUNT (h->succs) != 2)
	return false;
      b = f->dest;
      if (b == h || !single_pred_p (b) || EDGE_COUNT (b->succs) != 2
	  || !JUMP_P (BB_END (b)))
	return false;
      ljump = BB_END (b);
      if (JUMP_LABEL (ljump) != BB_HEAD (h) || !e2k_ms_jump_cond (ljump)
	  || recog_memoized (ljump) < 0 || get_attr_type (ljump) != TYPE_CT)
	return false;
      edge fb = find_fallthru_edge (b->succs);
      x1 = BLOCK_FOR_INSN (JUMP_LABEL (jump));
      if (!fb || x1 == h || x1 == b)
	return false;
      if (fb->dest != x1)
	{
	  /* Copies out of the %b[0..7] e2k_ms_move_b renames go on the
	     second block's exit only.  */
	  rtx_insn *insn;
	  for (basic_block bb : { h, b })
	    FOR_BB_INSNS (bb, insn)
	      if (INSN_P (insn))
		{
		  subrtx_iterator::array_type array;
		  FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
		    if (REG_P (*iter) && B_REGNO_P (REGNO (*iter)))
		      return e2k_ms_fail (h, "%b[0..7] in a loop of two exits");
		}
	  diff_exits = true;
	}
      last = b;
      /* The disp of H's exit, if nothing else reads its CTPR.  */
      rtx ctpr = XEXP (XVECEXP (PATTERN (jump), 0, 1), 0);
      rtx_insn *insn;
      FOR_BB_INSNS (h, insn)
	if (NONDEBUG_INSN_P (insn) && insn != jump
	    && reg_mentioned_p (ctpr, PATTERN (insn)))
	  {
	    if (hdisp || recog_memoized (insn) != CODE_FOR_e2k_disp_label)
	      return e2k_ms_fail (h, "the exit's CTPR");
	    hdisp = insn;
	  }
      FOR_BB_INSNS (b, insn)
	if (NONDEBUG_INSN_P (insn) && insn != ljump
	    && reg_mentioned_p (ctpr, PATTERN (insn)))
	  return e2k_ms_fail (h, "the exit's CTPR");
      if (bitmap_bit_p (df_get_live_in (x1), REGNO (ctpr)))
	return e2k_ms_fail (h, "the exit's CTPR");
      if (!diff_exits)
	x1 = NULL;
    }
  else if (EDGE_COUNT (h->succs) != 2)
    return false;

  edge exit_edge = find_fallthru_edge (last->succs);
  if (!exit_edge || exit_edge->dest == h || (exit_edge->flags & EDGE_COMPLEX))
    return e2k_ms_fail (h, "edges");
  auto_vec<edge> entries;
  edge e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, h->preds)
    if (e->src != last)
      {
	if (e->flags & EDGE_COMPLEX)
	  return e2k_ms_fail (h, "entry edges");
	/* The prologue goes on the edge.  A prepared conditional
	   transfer along it goes where its CTPR says: only one whose disp
	   is in its own block can be pointed at the prologue
	   (e2k_ms_split_entry), not another latch of an outer loop.  */
	rtx_insn *j = BB_END (e->src);
	if (!(e->flags & EDGE_FALLTHRU) && JUMP_P (j) && recog_memoized (j) >= 0
	    && get_attr_type (j) == TYPE_CT && !single_succ_p (e->src)
	    && !e2k_ms_local_disp (j))
	  return e2k_ms_fail (h, "entered by a prepared conditional transfer");
	entries.safe_push (e);
      }
  if (entries.is_empty () || entries.length () > 4)
    return e2k_ms_fail (h, "entry edges");
  /* Not a hash chain's walk (e2k_short_chain): it leaves after a node or
     two, and the prologue and the loads past the end would cost more
     than the kernel saves.  */
  if (cfun->machine->chain_clique)
    for (basic_block bb : { h, b })
      if (bb)
	{
	  rtx_insn *i;
	  FOR_BB_INSNS (bb, i)
	    if (NONDEBUG_INSN_P (i) && e2k_chain_ref_p (PATTERN (i)))
	      return e2k_ms_fail (h, "the walk of a hash chain");
	}
  /* The loop end's CTPR is prepared before the loop and kept, or by a
     disp of the second block, which then goes to the prologues.  */
  rtx lctpr = XEXP (XVECEXP (PATTERN (ljump), 0, 1), 0);
  rtx_insn *insn, *bdisp = NULL;
  for (basic_block bb : { h, b })
    if (bb)
      FOR_BB_INSNS (bb, insn)
	if (NONDEBUG_INSN_P (insn) && insn != ljump
	    && reg_mentioned_p (lctpr, PATTERN (insn)))
	  {
	    if ((bb == b || (!b && bb == h)) && !bdisp
		&& recog_memoized (insn) == CODE_FOR_e2k_disp_label
		&& reg_set_p (lctpr, insn)
		&& (label_ref_label (XVECEXP (SET_SRC (PATTERN (insn)), 0, 0))
		    == JUMP_LABEL (ljump)))
	      {
		bdisp = insn;
		continue;
	      }
	    if (dump_file)
	      print_rtl_single (dump_file, insn);
	    return e2k_ms_fail (h, "the loop end's CTPR");
	  }
  /* Nothing that can't be pipelined, before e2k_ms_move_b changes the
     loop: a call reads and sets %b[0..7] (pcre2's name table scan lost
     its strcmp arguments).  */
  for (basic_block bb : { h, b })
    if (bb)
      FOR_BB_INSNS (bb, insn)
	if (NONDEBUG_INSN_P (insn)
	    && (CALL_P (insn) || e2k_asm_insn_p (insn)
		|| volatile_insn_p (PATTERN (insn))))
	  return e2k_ms_fail (h, "a call or asm");
  /* B runs speculatively: no stores.  */
  if (b)
    FOR_BB_INSNS (b, insn)
      if (NONDEBUG_INSN_P (insn) && insn != ljump)
	{
	  rtx set = single_set (insn);
	  if (!set || MEM_P (SET_DEST (set)))
	    return e2k_ms_fail (h, "the second block stores");
	}

  auto_vec<basic_block> bbs;
  bbs.safe_push (h);
  if (b)
    bbs.safe_push (b);
  auto_vec<rtx_insn *> no_pre_ends;
  if (!e2k_ms_move_b (bbs, no_pre_ends, entries, exit_edge, NULL))
    return e2k_ms_fail (h, "no free register for a %b[] value");

  e2k_ms_loop *l = new e2k_ms_loop;
  l->bb = h;
  l->jump = ljump;
  l->wl = true;
  l->stay = l->c1 = -1;
  l->p1 = l->pstay = NULL_RTX;
  l->x1 = x1;
  l->nh = 0;
  l->want_dam = l->may_dam = l->dam_settled = false;
  l->dam = l->kchk = -1;
  l->edisp = b ? NULL : bdisp;
  FOR_BB_INSNS (h, insn)
    if (NONDEBUG_INSN_P (insn) && insn != jump && insn != hdisp
	&& insn != bdisp)
      l->insns.safe_push (insn);
  l->nh = l->nh0 = l->insns.length ();
  rtx_insn *landp = NULL;
  if (b)
    {
      FOR_BB_INSNS (b, insn)
	if (NONDEBUG_INSN_P (insn) && insn != ljump && insn != bdisp)
	  l->insns.safe_push (insn);
      /* A free predicate for "landp ~p1, p2".  */
      HARD_REG_SET used;
      CLEAR_HARD_REG_SET (used);
      for (basic_block bb : bbs)
	FOR_BB_INSNS (bb, insn)
	  if (INSN_P (insn))
	    e2k_note_regs (PATTERN (insn), &used);
      bitmap lh = df_get_live_in (h), lx = df_get_live_in (exit_edge->dest);
      unsigned r;
      for (r = PRED0_REGNUM; PRED_REGNO_P (r); r++)
	if (!fixed_regs[r] && !TEST_HARD_REG_BIT (used, r)
	    && !bitmap_bit_p (lh, r) && !bitmap_bit_p (lx, r)
	    && !(x1 && bitmap_bit_p (df_get_live_in (x1), r)))
	  break;
      if (!PRED_REGNO_P (r))
	{
	  delete l;
	  return e2k_ms_fail (h, "no free predicate");
	}
      rtx c2 = e2k_ms_jump_cond (ljump);
      w.b = b;
      w.hjump = jump;
      w.hdisp = hdisp;
      w.bdisp = bdisp;
      w.p1 = XEXP (cond, 0);
      w.pstay = gen_rtx_REG (BImode, r);
      l->p1 = w.p1;
      l->pstay = w.pstay;
      l->e1 = GET_CODE (cond);
      rtx pat = gen_rtx_SET (w.pstay,
			     gen_rtx_AND (BImode,
					  gen_rtx_fmt_ee (reverse_condition
							  (l->e1), BImode,
							  w.p1, const0_rtx),
					  gen_rtx_fmt_ee (GET_CODE (c2), BImode,
							  XEXP (c2, 0),
							  const0_rtx)));
      landp = emit_insn_before (pat, ljump);
      if (recog_memoized (landp) < 0)
	gcc_unreachable ();
      l->insns.safe_push (landp);
    }
  bool ok = e2k_ms_try (l, exit_edge->dest, no_pre_ends, entries, exit_edge,
			b ? &w : NULL);
  if (!ok && landp)
    delete_insn (landp);
  return ok;
}

/* In a function without calls nothing needs %b[0..7], which register
   allocation may still have used: a pipelined loop can't keep a value
   in them across setbn.  Give each one a window register above all the
   used ones instead, in the whole function.  */
static void
e2k_ms_free_b (void)
{
  rtx_insn *insn;
  int maxr = -1;
  bool used[8] = { false };
  for (insn = get_insns (); insn; insn = NEXT_INSN (insn))
    {
      if (!INSN_P (insn))
	continue;
      if (CALL_P (insn))
	return;
      subrtx_iterator::array_type array;
      FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
	if (REG_P (*iter) && REGNO (*iter) < FIRST_PSEUDO_REGISTER)
	  for (unsigned r = REGNO (*iter); r < END_REGNO (*iter); r++)
	    {
	      if (W_REGNO_P (r))
		maxr = MAX (maxr, (int) (r - R0_REGNUM));
	      else if (B_REGNO_P (r))
		{
		  if (REG_NREGS (*iter) != 1)
		    return;
		  used[r - B0_REGNUM] = true;
		}
	    }
    }
  unsigned map[8];
  int next = maxr + 1, n = 0;
  for (int k = 0; k < 8; k++)
    if (used[k])
      {
	while (next <= 63 && fixed_regs[R0_REGNUM + next])
	  next++;
	if (next > 63)
	  return;
	map[k] = R0_REGNUM + next++;
	n++;
      }
  if (!n)
    return;
  for (insn = get_insns (); insn; insn = NEXT_INSN (insn))
    {
      if (!INSN_P (insn))
	continue;
      bool changed = false;
      subrtx_ptr_iterator::array_type array;
      FOR_EACH_SUBRTX_PTR (iter, array, &PATTERN (insn), NONCONST)
	{
	  rtx *loc = *iter;
	  if (REG_P (*loc) && B_REGNO_P (REGNO (*loc)))
	    {
	      *loc = gen_rtx_REG (GET_MODE (*loc),
				  map[REGNO (*loc) - B0_REGNUM]);
	      changed = true;
	    }
	}
      if (REG_NOTES (insn))
	FOR_EACH_SUBRTX_PTR (iter, array, &REG_NOTES (insn), NONCONST)
	  {
	    rtx *loc = *iter;
	    if (*loc && REG_P (*loc) && B_REGNO_P (REGNO (*loc)))
	      *loc = gen_rtx_REG (GET_MODE (*loc),
				  map[REGNO (*loc) - B0_REGNUM]);
	  }
      if (changed)
	{
	  INSN_CODE (insn) = -1;
	  remove_reg_equal_equiv_notes (insn);
	  df_insn_rescan (insn);
	}
    }
}

void
e2k_modsched (void)
{
  e2k_ms_free_b ();
  df_analyze ();
  /* The memory dependences ask may_alias_p, whose base terms of hard
     registers come from the last init_alias_analysis: some pass before
     this one, before the loop versions and copies made since
     (gcc.dg/vect/vect-alias-check-18.c: a store and the next vector
     iteration's load of the same bytes were "independent").  */
  init_alias_analysis ();
  dfa_start ();
  e2k_dfa_ms = true;
  /* Only haifa's sched_init sets it: in the first function of a file
     that sched2 skips (gcc.dg/vect/vect-div-bitmask-5.c's fun1, at
     -O1), the rows were empty and the states random.  */
  dfa_state_size = state_size ();
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *jump = BB_END (bb);
      if (!JUMP_P (jump) || recog_memoized (jump) < 0)
	continue;
      if ((recog_memoized (jump) == CODE_FOR_e2k_hwloop_end
	   || recog_memoized (jump) == CODE_FOR_e2k_hwloop_end_wide)
	  && JUMP_LABEL (jump) == BB_HEAD (bb))
	e2k_ms_loop_1 (bb, jump);
      else if (e2k_pipeline_while)
	e2k_ms_wloop (bb);
    }
  e2k_dfa_ms = false;
  dfa_finish ();
  end_alias_analysis ();
  /* Also when no loop was pipelined: e2k_ms_move_b puts its copies back
     on the exit edge before the schedule is tried (left there, they are
     lost, and the edge points at insns the garbage collector later
     reads as GIMPLE).  */
  commit_edge_insertions ();
}

const char *
e2k_output_setbn (int pairs, int npred)
{
  static char buf[160];
  machine_function *m = cfun->machine;
  e2k_compute_window ();
  int n = 0;
  /* The ring's own window: from the loop's setbn to the one after it,
     which the copies out of the ring precede (e2k_ms_emit).  The
     same wide instruction already uses the new window.  */
  if (m->ring_setwd)
    n = snprintf (buf, sizeof buf, "setwd\twsz = %d, nfx = 1, dbl = %d\n\t",
		  pairs ? m->ring_base + pairs : m->wsz,
		  e2k_dbl_p () ? 1 : 0);
  if (pairs == 0 && m->use_b)
    n += snprintf (buf + n, sizeof buf - n,
		   "setbn\trsz = 3, rbs = %d, rcur = 0", m->wbase);
  else
    n += snprintf (buf + n, sizeof buf - n,
		   "setbn\trsz = %d, rbs = %d, rcur = 0",
		   (pairs ? pairs : m->rot_pairs) - 1, m->ring_base);
  /* The predicate ring of a pipelined while loop, %pred0 .. NPRED - 1
     (e2k_ms_assign_pnames); size 1 again when the loop is left.  */
  if (npred > 0)
    snprintf (buf + n, sizeof buf - n, "\n\tsetbp\tpsz = %d", npred - 1);
  else if (pairs == 0 && m->rot_preds)
    snprintf (buf + n, sizeof buf - n, "\n\tsetbp\tpsz = 0");
  return buf;
}

/* A prepared conditional transfer; the loop end of a pipelined while
   loop also rotates the ring.  */
const char *
e2k_output_ct_pred (rtx_insn *insn)
{
  if (e2k_ms_flag (insn) & E2K_MS_ABP)
    return "abn\tabnf=1, abnt=1\n\tabp\tabpf=1, abpt=1\n\tct\t%3 ? %C0%1";
  if (e2k_ms_flag (insn) & E2K_MS_ABN)
    return "abn\tabnf=1, abnt=1\n\tct\t%3 ? %C0%1";
  return "ct\t%3 ? %C0%1";
}

const char *
e2k_output_hwloop_end (rtx_insn *insn)
{
  if (e2k_ms_flag (insn) & E2K_MS_ABP)
    return "alc\talcf=1, alct=1\n\tabn\tabnf=1, abnt=1\n\t"
	   "abp\tabpf=1, abpt=1\n\tct\t%0 ? %%NOT_LOOP_END";
  if (e2k_ms_flag (insn) & E2K_MS_ABN)
    return "alc\talcf=1, alct=1\n\tabn\tabnf=1, abnt=1\n\t"
	   "ct\t%0 ? %%NOT_LOOP_END";
  return "alc\talcf=1, alct=1\n\tct\t%0 ? %%NOT_LOOP_END";
}
