/* Wide instructions for the Elbrus (E2K) port: the scheduled
   insns grouped into bundles with the empty cycles between them, ALU
   channels assigned, and final's output: braces, nops, setwd, loop
   ends.
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

static void e2k_assign_channels (void);
static void e2k_fit_bundles (void);

void
e2k_gen_bundles (void)
{
  e2k_marks.truncate (0);
  e2k_marks.safe_grow_cleared (get_max_uid () + 1);

  basic_block bb;
  /* The last insn of the block before, its instruction still open.  */
  rtx_insn *last = NULL;
  int last_clock = -1;
  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *end = NEXT_INSN (BB_END (bb));
      rtx_insn *prev = NULL;
      int prev_clock = -1;
      /* What the scheduler put in a conditional jump's cycle from the
	 block it falls through to, in its extended block, shares the
	 jump's wide instruction: it runs when the jump is taken too,
	 which e2k_adjust_cost allows and e2k_spec_mark makes
	 speculative.  Otherwise each such cycle cost one more.  */
      bool carry = false;
      if (last && JUMP_P (last) && !CALL_P (last) && last_clock > 0
	  && recog_memoized (last) >= 0
	  && (get_attr_type (last) == TYPE_CT
	      || get_attr_type (last) == TYPE_BRANCH)
	  && recog_memoized (last) != CODE_FOR_e2k_hwloop_end
	  && recog_memoized (last) != CODE_FOR_e2k_hwloop_end_wide
	  && !(bb->flags & BB_DISABLE_SCHEDULE)
	  && !(BLOCK_FOR_INSN (last)->flags & BB_DISABLE_SCHEDULE)
	  && !LABEL_P (BB_HEAD (bb)) && bb->prev_bb == BLOCK_FOR_INSN (last)
	  && single_pred_p (bb)
	  && (single_pred_edge (bb)->flags & EDGE_FALLTHRU)
	  && !e2k_raw_insn_p (last) && !e2k_asm_insn_p (last)
	  && !e2k_alone_p (last))
	for (rtx_insn *insn = BB_HEAD (bb); insn != end;
	     insn = NEXT_INSN (insn))
	  if (e2k_prints_p (insn))
	    {
	      unsigned u = INSN_UID (insn), lu = INSN_UID (last);
	      carry = (u < e2k_insn_clock.length ()
		       && u < e2k_insn_ebb.length ()
		       && lu < e2k_insn_ebb.length ()
		       && e2k_insn_clock[u] == last_clock
		       && e2k_insn_ebb[u] != 0
		       && e2k_insn_ebb[u] == e2k_insn_ebb[lu]
		       && GET_MODE (insn) != TImode);
	      break;
	    }
      /* The open instruction has a transfer already: one at most; and a
	 setwd, setbn or setbp.  */
      bool xfer = false, setwd = false;
      rtx_insn *carry_jump = carry ? last : NULL;
      if (carry)
	{
	  prev = last;
	  prev_clock = last_clock;
	  xfer = true;
	}
      else if (last)
	e2k_marks[INSN_UID (last)].close = true;
      last = NULL;
      /* A new cycle may start at an insn that prints nothing (a
	 blockage); carry it to the next one that prints.  */
      bool new_cycle = false;
      for (rtx_insn *insn = BB_HEAD (bb); insn != end; insn = NEXT_INSN (insn))
	{
	  if (INSN_P (insn) && GET_MODE (insn) == TImode)
	    new_cycle = true;
	  if (!e2k_prints_p (insn))
	    continue;
	  unsigned uid = INSN_UID (insn);
	  int clock = uid < e2k_insn_clock.length () ? e2k_insn_clock[uid] : 0;
	  bool open = (prev == NULL
		       || new_cycle
		       || e2k_raw_insn_p (insn) || e2k_raw_insn_p (prev)
		       || (clock > 0 && prev_clock > 0 && clock != prev_clock)
		       || e2k_asm_insn_p (insn)
		       || e2k_asm_insn_p (prev)
		       || CALL_P (prev)
		       || (JUMP_P (prev) && !(carry && clock == prev_clock))
		       /* A prepare of the CTPR the jump reads: never in one
			  instruction (v1-v5 transfer to the old target, v6
			  falls through; gas refuses it only up to v5).  */
		       || (carry && clock == last_clock
			   && carry_jump && e2k_writes_jump_reg_p (insn, carry_jump))
		       || ((JUMP_P (insn) || CALL_P (insn)) && xfer)
		       || (e2k_setwd_type_p (insn)
			   && (setwd || (carry && clock == last_clock)))
		       || e2k_alone_p (insn) || e2k_alone_p (prev));
	  if (open)
	    {
	      if (prev)
		{
		  e2k_marks[INSN_UID (prev)].close = true;
		  if (e2k_nops && clock > 0 && prev_clock > 0
		      && clock > prev_clock + 1 && !JUMP_P (prev)
		      && !CALL_P (prev))
		    e2k_marks[INSN_UID (prev)].nops = clock - prev_clock - 1;
		}
	      e2k_marks[uid].open = true;
	      xfer = false;
	      setwd = false;
	      carry_jump = NULL;
	    }
	  xfer |= JUMP_P (insn) || CALL_P (insn);
	  setwd |= e2k_setwd_type_p (insn);
	  new_cycle = false;
	  prev = insn;
	  if (clock > 0)
	    prev_clock = clock;
	}
      last = prev;
      last_clock = prev_clock;
    }
  if (last)
    e2k_marks[INSN_UID (last)].close = true;
  /* Within an extended block the scheduler's clocks go on past each
     jump: keep the cycles it left between a block and the block it falls
     through to.  Interlocks would cover most, not all: an operation in a
     wide instruction with a ct reads a predicate written one cycle before
     as it was (spec/isa/timing.md).  */
  if (e2k_nops)
    FOR_EACH_BB_FN (bb, cfun)
      {
	basic_block b = bb->next_bb;
	edge e = find_fallthru_edge (bb->succs);
	if (!e || e->dest != b)
	  continue;
	rtx_insn *last = NULL, *first = NULL, *insn;
	FOR_BB_INSNS (bb, insn)
	  if (e2k_prints_p (insn))
	    last = insn;
	FOR_BB_INSNS (b, insn)
	  if (e2k_prints_p (insn))
	    {
	      first = insn;
	      break;
	    }
	if (!last || !first || CALL_P (last))
	  continue;
	unsigned lu = INSN_UID (last), fu = INSN_UID (first);
	if (lu >= e2k_insn_clock.length () || fu >= e2k_insn_clock.length ()
	    || lu >= e2k_insn_ebb.length () || fu >= e2k_insn_ebb.length ()
	    || e2k_insn_ebb[lu] == 0 || e2k_insn_ebb[lu] != e2k_insn_ebb[fu]
	    || e2k_insn_clock[lu] == 0 || e2k_insn_clock[fu] == 0)
	  continue;
	int gap = e2k_insn_clock[fu] - e2k_insn_clock[lu] - 1;
	if (gap <= 0)
	  continue;
	if (JUMP_P (last))
	  e2k_marks[lu].post_nops = gap;
	else
	  e2k_marks[lu].nops = MAX (e2k_marks[lu].nops, gap);
      }

  /* The jumps into a block are not scheduled with it: if its first wide
     instruction transfers control and also reads a predicate in another
     operation (a merge, a predicated operation), that read doesn't wait
     for a compare in the jump's wide instruction (spec/isa/timing.md).
     Put an empty one before it.  The 2C3 reads the new value
     (E2K_PRED1).  */
  FOR_EACH_BB_FN (bb, cfun)
    {
      edge e;
      edge_iterator ei;
      bool jumped = false;
      FOR_EACH_EDGE (e, ei, bb->preds)
	jumped |= !(e->flags & EDGE_FALLTHRU);
      /* Not in a pipelined loop's kernel: its compensation code jumps
	 back into it from far away.  */
      if (!jumped || (bb->flags & BB_DISABLE_SCHEDULE) || E2K_PRED1)
	continue;
      rtx_insn *first = NULL, *insn;
      bool ct = false, pred_read = false;
      for (insn = BB_HEAD (bb); insn != NEXT_INSN (BB_END (bb));
	   insn = NEXT_INSN (insn))
	{
	  if (!e2k_prints_p (insn))
	    continue;
	  if (!first)
	    first = insn;
	  if (JUMP_P (insn))
	    ct = true;
	  else
	    {
	      subrtx_iterator::array_type array;
	      FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
		if (REG_P (*iter) && PRED_REGNO_P (REGNO (*iter))
		    && !reg_set_p (*iter, insn))
		  pred_read = true;
	    }
	  if (e2k_marks[INSN_UID (insn)].close)
	    break;
	}
      if (first && ct && pred_read)
	e2k_marks[INSN_UID (first)].lead_nop = true;
    }

  /* Check the rule above over every wide instruction: gas no longer
     does for v6.  */
  if (flag_checking)
    {
      HARD_REG_SET sets, reads;
      CLEAR_HARD_REG_SET (sets);
      CLEAR_HARD_REG_SET (reads);
      for (rtx_insn *insn = get_insns (); insn; insn = NEXT_INSN (insn))
	{
	  unsigned uid = INSN_UID (insn);
	  if (!e2k_prints_p (insn) || uid >= e2k_marks.length ()
	      || e2k_raw_insn_p (insn))
	    continue;
	  if (e2k_marks[uid].open)
	    {
	      CLEAR_HARD_REG_SET (sets);
	      CLEAR_HARD_REG_SET (reads);
	    }
	  bool xfer = JUMP_P (insn) || CALL_P (insn);
	  for (unsigned r = CTPR1_REGNUM; r <= CTPR3_REGNUM; r++)
	    {
	      rtx reg = gen_rtx_REG (DImode, r);
	      if (!xfer && reg_set_p (reg, insn))
		SET_HARD_REG_BIT (sets, r);
	      if (xfer
		  && (reg_mentioned_p (reg, PATTERN (insn))
		      || (JUMP_P (insn) && JUMP_LABEL (insn)
			  && ANY_RETURN_P (JUMP_LABEL (insn))
			  && r == CTPR3_REGNUM)))
		SET_HARD_REG_BIT (reads, r);
	    }
	  gcc_assert (!hard_reg_set_intersect_p (sets, reads));
	}
    }

  if (e2k_channels)
    e2k_assign_channels ();
  e2k_fit_bundles ();
}

/* The size of a wide instruction in 32-bit words as gas lays it out
   (spec/isa/reservations.yaml, wide_instruction; bundle.md, "Overall
   layout"): HS, SS, an ALS per operation, CS0, the ALES2/ALES5 word
   (v4+), CS1, the ALES and AAS half-syllables rounded up to words, then
   LTS, PLS and CDS words, all rounded up to an even count.  gas takes at
   most 16 ("exceeds the maximal supported size").  Counted high where
   the port can't tell: a 16-bit literal as a word, no literal shared,
   an operation without a channel as one with an ALES half (and the
   ALES2/5 word on v4+) in a cluster of its own for the CDS.  */
struct e2k_wi_size
{
  int als, ales_half, mova_mask, lts, pls, ncds;
  bool ss, cs0, cs1, ales25;
  unsigned cds[16];
};

/* Note an RLP (KIND 0, a predicated operation's condition) or MRGC
   (KIND 1, a merge's predicate) entry: one per cluster, predicate and
   kind (spec/isa/predicates.md, "How much fits in one wide
   instruction").  */
static void
e2k_wi_cds (e2k_wi_size *s, rtx_insn *insn, int chan, unsigned regno,
	    unsigned kind)
{
  unsigned where = (chan < 0 ? 0x8000 | (INSN_UID (insn) & 0x7fff)
		    : chan < 3 ? 0 : 1);
  unsigned key = (kind << 31) | (regno << 16) | where;
  for (int i = 0; i < s->ncds; i++)
    if (s->cds[i] == key)
      return;
  if (s->ncds < 16)
    s->cds[s->ncds] = key;
  s->ncds++;
}

/* Whether INSN is a scalar FP add, subtract or multiply.  */

static bool
e2k_wi_fp_arith_p (rtx_insn *insn)
{
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) == COND_EXEC)
    pat = COND_EXEC_CODE (pat);
  if (GET_CODE (pat) != SET)
    return false;
  rtx src = SET_SRC (pat);
  return ((GET_CODE (src) == PLUS || GET_CODE (src) == MINUS
	   || GET_CODE (src) == MULT)
	  && (GET_MODE (src) == SFmode || GET_MODE (src) == DFmode));
}

static void
e2k_wi_add (e2k_wi_size *s, rtx_insn *insn)
{
  if (recog_memoized (insn) < 0)
    {
      s->als++;
      return;
    }
  switch (get_attr_type (insn))
    {
    case TYPE_GHOST:
    case TYPE_NOP:
      return;
    /* setwd takes all of LTS0 (and setbn shares its CS1).  */
    case TYPE_SETWD:
      s->cs1 = true;
      s->lts++;
      return;
    case TYPE_WAIT:
      s->cs1 = true;
      return;
    /* Prepares, with "ipd" in the SS.  */
    case TYPE_DISP:
    case TYPE_RET:
    case TYPE_BRANCH:
      s->cs0 = s->ss = true;
      return;
    /* ct, and alc, abn and abp at a loop's end.  */
    case TYPE_CT:
    case TYPE_BAP:
      s->ss = true;
      return;
    case TYPE_CALL:
      s->ss = s->cs1 = true;
      return;
    /* PLS0 holds @p0, @p1 and CLP0, PLS1 @p2, @p3 and CLP1, PLS2 CLP2:
       landp of two conditions takes PLS0, of three PLS0-1, of four
       PLS0-2.  */
    case TYPE_PLOG:
      s->pls += (INSN_CODE (insn) == CODE_FOR_e2k_landp4 ? 3
		 : INSN_CODE (insn) == CODE_FOR_e2k_landp3 ? 2 : 1);
      return;
    /* Operand 2 is the mova channel, 0-3.  */
    case TYPE_MOVA:
      {
	rtx pat = PATTERN (insn);
	if (GET_CODE (pat) == PARALLEL)
	  pat = XVECEXP (pat, 0, 0);
	int ch = INTVAL (XVECEXP (SET_SRC (pat), 0, 1));
	s->mova_mask |= 1 << (ch & 3);
	s->ss = true;
	return;
      }
    default:
      break;
    }
  int chan = e2k_marks[INSN_UID (insn)].chan1 - 1;
  s->als++;
  /* Lock and check loads carry a MAS (CS1), a check also its "rbranch
     .LDAMn" (CS0 and SS); so do aaurr and aaurw, always.  */
  enum attr_type t = get_attr_type (insn);
  if (get_attr_mas (insn) == MAS_YES || t == TYPE_LDLOCK || t == TYPE_LDCHK
      || t == TYPE_AAU)
    s->cs1 = true;
  if (t == TYPE_LDCHK)
    s->cs0 = s->ss = true;
  if (get_attr_ales (insn) == ALES_YES)
    {
      if (chan < 0 || chan == 0 || chan == 1 || chan == 3 || chan == 4)
	s->ales_half++;
      if (e2k_arch >= 4 && (chan < 0 || chan == 2 || chan == 5))
	s->ales25 = true;
    }
  /* v4 opened ALC2 and ALC5 to the scalar FP add, subtract and
     multiply, which take an ALES there (value), though none in the
     other channels (spec/isa/reservations.yaml).  */
  else if (e2k_arch >= 4 && (chan < 0 || chan == 2 || chan == 5)
	   && t == TYPE_FP && e2k_wi_fp_arith_p (insn))
    s->ales25 = true;
  s->lts += e2k_insn_lits (insn);
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) == COND_EXEC)
    {
      rtx c = XEXP (COND_EXEC_TEST (pat), 0);
      if (REG_P (c))
	e2k_wi_cds (s, insn, chan, REGNO (c), 0);
      pat = COND_EXEC_CODE (pat);
    }
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, pat, NONCONST)
    if (REG_P (*iter) && PRED_REGNO_P (REGNO (*iter))
	&& !reg_set_p (*iter, pat))
      e2k_wi_cds (s, insn, chan, REGNO (*iter), 1);
}

static int
e2k_wi_words (const e2k_wi_size *s)
{
  /* ALES0, 1, 3, 4, then AAS0 (the destinations of movas 0 and 1),
     AAS1 (2 and 3) and AAS2-AAS5, one per mova channel, by position: up
     to the highest channel used.  */
  int m = s->mova_mask;
  int halves = (s->ales_half + ((m & 3) != 0) + ((m & 12) != 0)
		+ (m & 8 ? 4 : m & 4 ? 3 : m & 2 ? 2 : m & 1 ? 1 : 0));
  int w = (1 + s->ss + s->als + s->cs0 + s->ales25 + s->cs1
	   + (halves + 1) / 2 + s->lts + s->pls + (s->ncds + 1) / 2);
  return (w + 1) & ~1;
}

/* End a wide instruction before the operation that would take it past
   16 words.  The scheduler's DFA keeps to the literals, CS0, CS1, SS and
   one PLS but not to the size, and prologue instructions reach 16
   (setwd's LTS0, getsp's literal, a 64-bit one, six operations; relcc2
   findings I52): one more predicated operation would be a gas error.
   Splitting keeps stream order, so every read of an old value in the
   instruction still comes before its writer, and costs a cycle.  */
static void
e2k_fit_bundles (void)
{
  e2k_wi_size s;
  memset (&s, 0, sizeof s);
  rtx_insn *prev = NULL;
  for (rtx_insn *insn = get_insns (); insn; insn = NEXT_INSN (insn))
    {
      if (!e2k_prints_p (insn))
	continue;
      unsigned uid = INSN_UID (insn);
      if (uid >= e2k_marks.length ())
	continue;
      if (e2k_raw_insn_p (insn) || e2k_asm_insn_p (insn)
	  || e2k_alone_p (insn))
	{
	  prev = NULL;
	  continue;
	}
      if (e2k_marks[uid].open)
	{
	  memset (&s, 0, sizeof s);
	  prev = NULL;
	}
      e2k_wi_size t = s;
      e2k_wi_add (&t, insn);
      if (prev && e2k_wi_words (&t) > 16 && e2k_fit_bundles_p)
	{
	  e2k_marks[INSN_UID (prev)].close = true;
	  e2k_marks[INSN_UID (prev)].words = e2k_wi_words (&s);
	  e2k_marks[uid].open = true;
	  memset (&t, 0, sizeof t);
	  e2k_wi_add (&t, insn);
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_fit_bundles: a wide instruction "
		     "ends before insn %d\n", uid);
	}
      s = t;
      prev = insn;
      if (e2k_marks[uid].close)
	{
	  e2k_marks[uid].words = e2k_wi_words (&s);
	  prev = NULL;
	}
    }
}

/* Channels.  The six ALU channels form two clusters, ALC0-2 and ALC3-5,
   and a result reaches the other cluster later: integer results and
   loads one cycle, FP-class results two, which an integer consumer pays
   anyway (spec/isa/timing.md, "Clusters").  gas gives each operation the
   first free channel it allows, so a consumer the scheduler placed right
   after its producer often lands in the other cluster and stalls a whole
   4-cycle step.  Choose the channels here instead, per wide instruction,
   keeping consumers in their producers' clusters where the channel sets
   allow.  */

/* The most insns of a wide instruction given channels: six ALU
   operations, four movas, the control transfer and more.  */
#define E2K_CHAN_OPS 16

/* What a result is: packed results reach integer operations, and
   anything in the other cluster, at 4; x86 flags (the flag operations',
   and fcmpud*f's) a cctop in their own channel at 2 (the flag
   operations'), anything else at their latency, in any channel
   (spec/isa/timing.md).  */
enum e2k_rkind { E2K_RK_NONE, E2K_RK_INT, E2K_RK_LOAD, E2K_RK_FP,
		 E2K_RK_PACKED, E2K_RK_FLAG };

/* The channels INSN may take (spec/isa/binutils-ops.yaml for v3, as in
   e2k-sched.md), 0 if it takes none, -1 if they are not known here.  A
   lock or check load prints its own channel: *FIXED is it and *BUSY the
   channels it keeps free of others.  */
static int
e2k_chan_set (rtx_insn *insn, int *fixed, int *busy, enum e2k_rkind *kind)
{
  *fixed = -1;
  *busy = 0;
  *kind = E2K_RK_INT;
  if (e2k_asm_insn_p (insn) || recog_memoized (insn) < 0)
    return -1;
  switch (get_attr_type (insn))
    {
    case TYPE_ALU:
      return 0x3f;
    case TYPE_ALU14:
      return 0x12;
    case TYPE_ALU0134:
      return 0x1b;
    case TYPE_CMP:
      return 0x1b;
    case TYPE_FLAG:
    case TYPE_FLAGMUL:
      *kind = E2K_RK_FLAG;
      return 0x09;
    case TYPE_CCTOP:
      return 0x09;
    case TYPE_FP:
    case TYPE_FMA:
    case TYPE_FFMA:
      /* v4 added ALC2 and ALC5 for FP add, subtract, multiply and the
	 combined operations (e2k-sched.md, "e2k_fp6").  */
      *kind = E2K_RK_FP;
      return e2k_arch >= 4 ? 0x3f : 0x1b;
    case TYPE_MUL:
    case TYPE_FCVT:
      *kind = E2K_RK_FP;
      return 0x1b;
    case TYPE_FCMP:
      *kind = E2K_RK_FLAG;
      return 0x1b;
    case TYPE_FSCALE:
      *kind = E2K_RK_FP;
      return 0x12;
    case TYPE_FDIV:
      *kind = E2K_RK_FP;
      return 0x20;
    case TYPE_DIV:
      return 0x20;
    case TYPE_PINT:
      *kind = E2K_RK_PACKED;
      return 0x09;
    case TYPE_PINT14:
    case TYPE_PMUL:
      *kind = E2K_RK_PACKED;
      return 0x12;
    case TYPE_PANY:
      *kind = E2K_RK_PACKED;
      return 0x1b;
    /* Array prefetch: movas in the AAS channels, at 5 cycles to any
       consumer; AAU register writes in ALC2/5.  */
    case TYPE_MOVA:
    case TYPE_BAP:
      *kind = E2K_RK_NONE;
      return 0;
    case TYPE_AAU:
      *kind = E2K_RK_NONE;
      return 0x24;
    case TYPE_LOAD:
      *kind = E2K_RK_LOAD;
      return 0x2d;
    case TYPE_STORE:
      *kind = E2K_RK_NONE;
      return 0x24;
    case TYPE_GETSP:
    case TYPE_MOVCTP:
      return 0x01;
    /* No store shares their wide instruction (e2k-sched.md,
       "e2k_ldlock0"), so they take only their own channels.  */
    case TYPE_LDLOCK:
      *kind = E2K_RK_LOAD;
      *fixed = 0;
      *busy = 0x01;
      return 0;
    case TYPE_LDCHK:
      *kind = E2K_RK_LOAD;
      *fixed = 5;
      *busy = 0x20;
      return 0;
    case TYPE_DISP:
    case TYPE_RET:
    case TYPE_BRANCH:
    case TYPE_CT:
    case TYPE_CALL:
    case TYPE_WAIT:
    case TYPE_GHOST:
    case TYPE_PLOG:
    case TYPE_SETWD:
      *kind = E2K_RK_NONE;
      return 0;
    default:
      return -1;
    }
}

/* The last write of each register: its wide instruction, latency,
   cluster (-1 if not known) and kind.  */
struct e2k_chan_prod
{
  int pos;
  int lat;
  int cl;
  enum e2k_rkind kind;
  /* A predicated producer's predicate (else -1), and whether it runs
     when the predicate is false.  */
  int pred;
  bool inv;
  /* An FP-side result a write-back conflict delays by a cycle.  */
  bool late;
  /* The channel of x86 flags a cctop there reads at 2, else -1.  */
  int ch;
};

struct e2k_chan_use_data
{
  int regs[16];
  /* A store's data: it reads an FP-side result as an FP operation does,
     2 cycles later only from the other cluster (relcc2 findings I44).  */
  bool fp[16];
  int n;
};

static void
e2k_chan_note_use (rtx *loc, void *data)
{
  e2k_chan_use_data *d = (e2k_chan_use_data *) data;
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, *loc, NONCONST)
    if (REG_P (*iter) && GPR_REGNO_P (REGNO (*iter)) && d->n < 16)
      d->regs[d->n++] = REGNO (*iter);
}

/* Whether INSN is a check load: it waits for nothing of its lock load,
   and a use of its register in the next instruction issues as if it
   were not there (tools/isa-probes on the 4C and 8C2, relcc2 findings
   I30): for the channels and stalls its register keeps the lock load's
   value.  */
static bool
e2k_chan_check_p (rtx_insn *insn)
{
  return recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_LDCHK;
}

/* The registers INSN reads, for e2k_chan_early.  */
static void
e2k_chan_uses (rtx_insn *insn, e2k_chan_use_data *d)
{
  d->n = 0;
  note_uses (&PATTERN (insn), e2k_chan_note_use, d);
  for (int j = 0; j < d->n; j++)
    d->fp[j] = false;
  if (recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_STORE)
    {
      rtx set = PATTERN (insn);
      if (GET_CODE (set) == COND_EXEC)
	set = COND_EXEC_CODE (set);
      if (GET_CODE (set) == PARALLEL)
	set = XVECEXP (set, 0, 0);
      rtx src = GET_CODE (set) == SET ? SET_SRC (set) : NULL_RTX;
      if (src && SUBREG_P (src))
	src = SUBREG_REG (src);
      if (src && REG_P (src))
	for (int j = 0; j < d->n; j++)
	  d->fp[j] = IN_RANGE (d->regs[j], (int) REGNO (src),
			       (int) END_REGNO (src) - 1);
    }
  if (!e2k_chan_check_p (insn))
    return;
  rtx set = PATTERN (insn);
  if (GET_CODE (set) == COND_EXEC)
    set = COND_EXEC_CODE (set);
  /* A pipelined loop's check and its jump (e2k_ldchk_jump).  */
  if (GET_CODE (set) == PARALLEL)
    set = XVECEXP (set, 0, 0);
  int k = 0;
  for (int j = 0; j < d->n; j++)
    if (d->regs[j] != (int) REGNO (SET_DEST (set)))
      d->regs[k++] = d->regs[j];
  d->n = k;
}

/* The table of e2k_assign_channels, and each register's producer before
   the last one: a consumer under the predicate opposite to the last
   one's reads that one's value (the two arms of an if-converted if-else
   that share a register).  */
static e2k_chan_prod e2k_chan_tab[FIRST_PSEUDO_REGISTER];
static e2k_chan_prod e2k_chan_prev[FIRST_PSEUDO_REGISTER];

/* Write-back conflicts (spec/isa/timing.md): an FP-side result (FP
   operation, integer multiply) bound for an integer operation, or for an
   FP one in the other cluster, comes a cycle late when an ALU operation
   or a load issues in its channel 2 cycles after it; so does a flag
   multiply's (smulx_fw, umulx_fw), to anything, but not when another
   flag multiply issues there.  The FP-side operations of each channel
   in the last four positions (by position modulo 4, so that one issued
   right after another doesn't hide it): position and result.  */
#define E2K_WB_DISTANCE 2
static int e2k_chan_fp_pos[6][4];
static int e2k_chan_fp_reg[6][4];

/* Whether an FP-side operation issued in channel C at POS - 2.  */
static bool
e2k_chan_wb_p (int c, int pos)
{
  int at = pos - E2K_WB_DISTANCE;
  return at >= 0 && e2k_chan_fp_pos[c][at & 3] == at;
}

/* Whether INSN's result is a predicate (a compare or cctop).  */
static bool
e2k_chan_pred_def_p (rtx_insn *insn)
{
  rtx set = single_set (insn);
  return (set && REG_P (SET_DEST (set))
	  && PRED_REGNO_P (REGNO (SET_DEST (set))));
}

/* The predicate INSN runs under in *PRED (-1: none) and *INV.  */
static void
e2k_chan_pred (rtx_insn *insn, int *pred, bool *inv)
{
  *pred = -1;
  *inv = false;
  if (GET_CODE (PATTERN (insn)) == COND_EXEC)
    {
      rtx c = COND_EXEC_TEST (PATTERN (insn));
      if (REG_P (XEXP (c, 0)))
	{
	  *pred = REGNO (XEXP (c, 0));
	  *inv = GET_CODE (c) == EQ;
	}
    }
}

/* Forget every register's producers.  */
static void
e2k_chan_clear (e2k_chan_prod *tab)
{
  for (int r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    {
      tab[r].kind = E2K_RK_NONE;
      e2k_chan_prev[r].kind = E2K_RK_NONE;
    }
  for (int c = 0; c < 6; c++)
    for (int k = 0; k < 4; k++)
      e2k_chan_fp_pos[c][k] = INT_MIN / 2;
}

/* Pipelined loops (e2k_modsched): for each prologue insn's UID, its
   node's insn in the kernel (whose channel it takes, so that a value
   an operation passes to its own next instance doesn't cross between
   the clusters on the way into the kernel); and the kernels' blocks
   (the second -1, or the block after a check that splits it).  */
vec<int> e2k_ms_twin;
vec<std::pair<int, int> > e2k_ms_kernels;
/* The number of rotating registers of each kernel's ring.  */
vec<int> e2k_ms_kernel_rings;

static void
e2k_chan_note_def (rtx x, const_rtx, void *data)
{
  if (SUBREG_P (x))
    x = SUBREG_REG (x);
  if (!REG_P (x) || !HARD_REGISTER_P (x))
    return;
  for (unsigned r = REGNO (x); r < END_REGNO (x); r++)
    {
      e2k_chan_prev[r] = e2k_chan_tab[r];
      e2k_chan_tab[r] = *(e2k_chan_prod *) data;
    }
}

/* The kinds of consumer, for the crossing costs: an integer operation,
   an FP-side one, a store's data (FP data as an FP operation takes it,
   integer data with no crossing cost: spec/isa/timing.md, "Clusters").  */
#define E2K_CONS_INT 0
#define E2K_CONS_FP 1
#define E2K_CONS_ST 2

/* Cycles a consumer of kind FP (E2K_CONS_*) in channel C at position POS
   (a cctop if CC) waits for the value of producer P, rounded up to the
   4-cycle stall steps (spec/isa/timing.md).  */
static int
e2k_chan_stall_1 (const e2k_chan_prod &p, int c, int pos, int fp, bool cc)
{
  if (p.kind == E2K_RK_NONE || p.cl < 0)
    return 0;
  bool other = c / 3 != p.cl;
  int lat = p.lat;
  if (p.kind == E2K_RK_FLAG)
    lat = cc && p.ch == c ? 2 : lat + p.late;
  else if (p.kind == E2K_RK_FP)
    lat += (other || fp == E2K_CONS_INT) ? 2 + p.late : 0;
  else if (p.kind == E2K_RK_PACKED)
    lat = (other || fp == E2K_CONS_INT) ? MAX (lat, 4) : lat;
  /* A v6 load costs its 5 cycles in either cluster; a store takes
     integer data from either cluster at no cost.  */
  else if (!(p.kind == E2K_RK_LOAD && E2K_LAT6) && fp != E2K_CONS_ST)
    lat += other;
  int e = lat - (pos - p.pos);
  return e > 0 ? 4 * ((e + 3) / 4) : 0;
}

/* The same for register R, from TAB, for a consumer under predicate PRED
   (INV as e2k_chan_pred).  */
static int
e2k_chan_stall (const e2k_chan_prod *tab, int r, int c, int pos, int fp,
		bool cc, int pred, bool inv)
{
  const e2k_chan_prod &p = tab[r];
  if (p.pred < 0 || p.kind == E2K_RK_NONE)
    return e2k_chan_stall_1 (p, c, pos, fp, cc);
  if (p.pred == pred && p.inv != inv)
    return e2k_chan_stall_1 (e2k_chan_prev[r], c, pos, fp, cc);
  if (p.pred == pred)
    return e2k_chan_stall_1 (p, c, pos, fp, cc);
  return MAX (e2k_chan_stall_1 (p, c, pos, fp, cc),
	      e2k_chan_stall_1 (e2k_chan_prev[r], c, pos, fp, cc));
}

/* How many cycles early register R, from TAB, is for channel C at POS
   (e2k_chan_stall's E).  */
static int
e2k_chan_early (const e2k_chan_prod *tab, int r, int c, int pos, int fp,
		bool cc, int pred, bool inv)
{
  int s = e2k_chan_stall (tab, r, c, pos, fp, cc, pred, inv);
  if (!s)
    return 0;
  for (int e = 1; e <= s; e++)
    if (e2k_chan_stall (tab, r, c, pos + e, fp, cc, pred, inv) == 0)
      return e;
  return s;
}

/* Give the operations of a wide instruction at POS their channels, the
   ones whose operands come soonest (TAB: what each register's producer
   was).  With PAD, returns how many empty cycles to put before it, the
   most an operand is still early by up to 3: an early operand stalls 4
   cycles (spec/isa/timing.md), the empty cycles cost what they are
   (a load result or a value crossing the clusters one cycle late: crc32's
   braid, 6 stalls in 46 cycles).  */
static int
e2k_chan_bundle (rtx_insn **ops, int n, int pos, e2k_chan_prod *tab,
		 bool pad)
{
  int set[E2K_CHAN_OPS], fixed[E2K_CHAN_OPS], cost[E2K_CHAN_OPS][6];
  int chan[E2K_CHAN_OPS], pred[E2K_CHAN_OPS];
  bool load[E2K_CHAN_OPS], store[E2K_CHAN_OPS], fpo[E2K_CHAN_OPS];
  bool inv[E2K_CHAN_OPS], cct[E2K_CHAN_OPS], fmul[E2K_CHAN_OPS];
  int busy = 0;
  bool ok = n <= E2K_CHAN_OPS;
  for (int i = 0; ok && i < n; i++)
    {
      int b;
      enum e2k_rkind kind;
      set[i] = e2k_chan_set (ops[i], &fixed[i], &b, &kind);
      if (set[i] < 0)
	{
	  ok = false;
	  break;
	}
      busy |= b;
      chan[i] = fixed[i];
      /* A channel chosen before stays: a kernel's (e2k_assign_channels
	 does those first), or its node's in the kernel for a prologue
	 instance.  */
      unsigned uid = INSN_UID (ops[i]);
      int pin = e2k_marks[uid].chan1 - 1;
      if (pin < 0 && uid < e2k_ms_twin.length () && e2k_ms_twin[uid])
	pin = e2k_marks[e2k_ms_twin[uid]].chan1 - 1;
      if (pin >= 0 && set[i] > 0 && (set[i] & (1 << pin)))
	set[i] = 1 << pin;
      enum attr_type t = get_attr_type (ops[i]);
      load[i] = t == TYPE_LOAD;
      /* An AAU register write is a staa with MAS 0x3f to gas.  */
      store[i] = t == TYPE_STORE || t == TYPE_AAU;
      bool fp = (t == TYPE_FP || t == TYPE_FMA || t == TYPE_FFMA
		 || t == TYPE_FCVT || t == TYPE_FSCALE
		 || t == TYPE_MUL || t == TYPE_FCMP || t == TYPE_FDIV
		 || e2k_packed_type_p (t));
      fpo[i] = fp;
      cct[i] = t == TYPE_CCTOP;
      fmul[i] = t == TYPE_FLAGMUL;
      e2k_chan_pred (ops[i], &pred[i], &inv[i]);
      e2k_chan_use_data d;
      e2k_chan_uses (ops[i], &d);
      for (int c = 0; c < 6; c++)
	{
	  cost[i][c] = 0;
	  if (set[i] & (1 << c))
	    for (int k = 0; k < d.n; k++)
	      cost[i][c] += e2k_chan_stall (tab, d.regs[k], c, pos,
					    d.fp[k] ? E2K_CONS_ST
					    : fp ? E2K_CONS_FP : E2K_CONS_INT,
					    cct[i], pred[i], inv[i]);
	  /* Half a stall step for delaying an FP-side result (its consumer
	     may have slack).  */
	  if ((set[i] & (1 << c)) && !fp && !fmul[i] && !store[i]
	      && !e2k_chan_pred_def_p (ops[i]) && e2k_chan_wb_p (c, pos))
	    cost[i][c] += 2;
	}
    }

  if (ok)
    {
      /* Search every assignment; the first best one (the lowest channels
	 in order, as gas picks) wins ties.  */
      int best = INT_MAX, cur[E2K_CHAN_OPS], bestc[E2K_CHAN_OPS];
      int i = 0, used = busy;
      for (int k = 0; k < n; k++)
	cur[k] = -1;
      auto search = [&] (auto &&self, int i, int used, int sum) -> void
	{
	  if (sum >= best)
	    return;
	  if (i == n)
	    {
	      /* gas: no store in ALC2 with a load in ALC3, nor in ALC5
		 with a load in ALC0 (spec/isa/bundle.md).  */
	      bool st2 = false, st5 = false, ld0 = false, ld3 = false;
	      for (int k = 0; k < n; k++)
		{
		  st2 |= store[k] && cur[k] == 2;
		  st5 |= store[k] && cur[k] == 5;
		  ld0 |= load[k] && cur[k] == 0;
		  ld3 |= load[k] && cur[k] == 3;
		}
	      if ((st2 && ld3) || (st5 && ld0))
		return;
	      best = sum;
	      memcpy (bestc, cur, sizeof cur);
	      return;
	    }
	  if (set[i] == 0)
	    {
	      self (self, i + 1, used, sum);
	      return;
	    }
	  for (int c = 0; c < 6; c++)
	    if ((set[i] & (1 << c)) && !(used & (1 << c)))
	      {
		cur[i] = c;
		self (self, i + 1, used | (1 << c), sum + cost[i][c]);
	      }
	  cur[i] = -1;
	};
      search (search, i, used, 0);
      if (best == INT_MAX)
	ok = false;
      else
	for (int k = 0; k < n; k++)
	  if (set[k] > 0)
	    {
	      chan[k] = bestc[k];
	      e2k_marks[INSN_UID (ops[k])].chan1 = bestc[k] + 1;
	    }
    }

  int delay = 0;
  if (ok && pad)
    for (int i = 0; i < n; i++)
      if (chan[i] >= 0 && chan[i] < 6)
	{
	  e2k_chan_use_data d;
	  e2k_chan_uses (ops[i], &d);
	  for (int k = 0; k < d.n; k++)
	    delay = MAX (delay,
			 e2k_chan_early (tab, d.regs[k], chan[i], pos,
					 d.fp[k] ? E2K_CONS_ST
					 : fpo[i] ? E2K_CONS_FP : E2K_CONS_INT,
					 cct[i], pred[i], inv[i]));
	}
  if (delay > 3)
    delay = 0;
  pos += delay;

  /* Record the results.  */
  for (int i = 0; i < n; i++)
    {
      rtx_insn *insn = ops[i];
      if (CALL_P (insn))
	{
	  e2k_chan_clear (tab);
	  continue;
	}
      int f, b;
      enum e2k_rkind kind;
      if (e2k_chan_set (insn, &f, &b, &kind) < 0)
	kind = E2K_RK_NONE;
      int cl = ok && chan[i] >= 0 ? chan[i] / 3 : -1;
      int lat = recog_memoized (insn) >= 0 ? insn_default_latency (insn) : 1;
      int ch = (cl >= 0 && kind == E2K_RK_FLAG
		&& get_attr_type (insn) == TYPE_FLAG ? chan[i] : -1);
      e2k_chan_prod p = { pos, lat, cl, kind, -1, false, false, ch };
      e2k_chan_pred (insn, &p.pred, &p.inv);
      if (!e2k_chan_check_p (insn))
	note_stores (insn, e2k_chan_note_def, &p);
    }
  /* Write-back conflicts this instruction makes (not a compare or
     cctop into a predicate, which writes no register: spec/isa/
     timing.md, "Write-back conflicts"), then its FP-side results.  */
  for (int i = 0; ok && i < n; i++)
    if (chan[i] >= 0 && chan[i] < 6 && !fpo[i] && !fmul[i] && !store[i]
	&& !CALL_P (ops[i]) && !e2k_chan_pred_def_p (ops[i])
	&& e2k_chan_wb_p (chan[i], pos))
      {
	int r = e2k_chan_fp_reg[chan[i]][(pos - E2K_WB_DISTANCE) & 3];
	if (r >= 0 && (tab[r].kind == E2K_RK_FP || tab[r].kind == E2K_RK_FLAG)
	    && tab[r].pos == pos - E2K_WB_DISTANCE && tab[r].cl == chan[i] / 3)
	  tab[r].late = true;
      }
  for (int i = 0; ok && i < n; i++)
    if (chan[i] >= 0 && chan[i] < 6 && (fpo[i] || fmul[i]) && !CALL_P (ops[i]))
      {
	rtx set = single_set (ops[i]);
	rtx d = set ? SET_DEST (set) : NULL_RTX;
	if (d && SUBREG_P (d))
	  d = SUBREG_REG (d);
	e2k_chan_fp_pos[chan[i]][pos & 3] = pos;
	e2k_chan_fp_reg[chan[i]][pos & 3]
	  = d && REG_P (d) && GPR_REGNO_P (REGNO (d)) ? (int) REGNO (d) : -1;
      }
  return delay;
}

/* Assign the channels of the wide instructions from FROM to before TO,
   the first at position *POS; with PAD, put empty cycles where they save
   a stall (e2k_chan_bundle) after a wide instruction that only falls
   through to the next.  */
static void
e2k_chan_range (rtx_insn *from, rtx_insn *to, int *pos, e2k_chan_prod *tab,
		bool pad)
{
  rtx_insn *ops[E2K_CHAN_OPS];
  int n = 0;
  bool over = false;
  rtx_insn *prev = NULL;
  for (rtx_insn *insn = from; insn != to; insn = NEXT_INSN (insn))
    {
      if (LABEL_P (insn))
	prev = NULL;
      if (!e2k_prints_p (insn))
	continue;
      e2k_mark &m = e2k_marks[INSN_UID (insn)];
      if (m.open)
	{
	  n = 0;
	  over = false;
	}
      if (n < E2K_CHAN_OPS)
	ops[n++] = insn;
      else
	over = true;
      if (m.close)
	{
	  bool can = (pad && prev && !JUMP_P (prev) && !CALL_P (prev)
		      && !e2k_marks[INSN_UID (prev)].post_nops
		      && !e2k_marks[INSN_UID (ops[0])].lead_nop);
	  int delay = over ? 0 : e2k_chan_bundle (ops, n, *pos, tab, can);
	  if (delay)
	    {
	      e2k_marks[INSN_UID (prev)].nops += delay;
	      *pos += delay;
	    }
	  *pos += 1 + m.nops;
	  n = 0;
	  prev = insn;
	}
    }
}

/* abn: what an iteration writes as %b[N] the next one reads as %b[N + 2],
   in a ring of RING registers (spec/isa/loops.md): move the producers of
   the table accordingly.  */
static void
e2k_chan_rotate (int ring)
{
  if (ring <= 0 || ring > E2K_ROT_MAX)
    return;
  e2k_chan_prod t[E2K_ROT_MAX], p[E2K_ROT_MAX];
  for (int n = 0; n < ring; n++)
    {
      t[(n + 2) % ring] = e2k_chan_tab[E2K_ROT_REGNO (n)];
      p[(n + 2) % ring] = e2k_chan_prev[E2K_ROT_REGNO (n)];
    }
  for (int n = 0; n < ring; n++)
    {
      e2k_chan_tab[E2K_ROT_REGNO (n)] = t[n];
      e2k_chan_prev[E2K_ROT_REGNO (n)] = p[n];
    }
}

/* Assign the channels of FROM .. TO, a loop body, in its steady state:
   twice round, the second time with what the first left in the table
   (rotated by abn's step for a kernel's ring of RING registers).  */
static void
e2k_chan_loop (rtx_insn *from, rtx_insn *to, int ring)
{
  e2k_chan_prod *tab = e2k_chan_tab;
  e2k_chan_clear (tab);
  int pos = 0;
  for (int round = 0; round < 2; round++)
    {
      if (round)
	{
	  e2k_chan_rotate (ring);
	  for (rtx_insn *insn = from; insn != to; insn = NEXT_INSN (insn))
	    e2k_marks[INSN_UID (insn)].chan1 = 0;
	}
      e2k_chan_range (from, to, &pos, tab, false);
    }
}

static void
e2k_assign_channels (void)
{
  e2k_chan_prod *tab = e2k_chan_tab;
  /* Kernels first, in their steady state.  */
  auto_bitmap kernel_bbs;
  for (unsigned i = 0; i < e2k_ms_kernels.length (); i++)
    {
      std::pair<int, int> &k = e2k_ms_kernels[i];
      basic_block b1 = BASIC_BLOCK_FOR_FN (cfun, k.first);
      basic_block b2 = k.second >= 0 ? BASIC_BLOCK_FOR_FN (cfun, k.second) : b1;
      if (!b1 || !b2)
	continue;
      bitmap_set_bit (kernel_bbs, b1->index);
      bitmap_set_bit (kernel_bbs, b2->index);
      e2k_chan_loop (BB_HEAD (b1), NEXT_INSN (BB_END (b2)),
		     i < e2k_ms_kernel_rings.length ()
		     ? e2k_ms_kernel_rings[i] : 0);
    }
  /* So are the other loops of one block: their first instruction reads
     what their last one wrote (xz's crc64 loop stalled 4 cycles an
     iteration on a value crossing the clusters back to the top).  */
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    if (!bitmap_bit_p (kernel_bbs, bb->index)
	&& find_edge (bb, bb) && !(bb->flags & BB_DISABLE_SCHEDULE))
      e2k_chan_loop (BB_HEAD (bb), NEXT_INSN (BB_END (bb)), 0);
  e2k_chan_clear (tab);
  int pos = 0;
  e2k_chan_range (get_insns (), NULL, &pos, tab, e2k_nops);
}

/* The channel chosen for the insn being printed, or -1.  */
int
e2k_cur_chan (void)
{
  if (!e2k_bundling || !current_output_insn)
    return -1;
  unsigned uid = INSN_UID (current_output_insn);
  return uid < e2k_marks.length () ? e2k_marks[uid].chan1 - 1 : -1;
}

/* Data speculation labels (see e2k_output_spec_load).  */
int e2k_dam_labelno;
vec<int> e2k_dam_pending;	/* labels to print after the bundle */
vec<int> e2k_dam_stubs;		/* stubs to print at the end */
int e2k_apb_labelno;
vec<char *> e2k_apb_progs;



/* Strip-mined loop ends (see e2k_output_hwloop_end_wide): the test for
   another chunk to print after the bundle, and the stubs.  */
struct e2k_hw_stub { int n; rtx ops[3]; };
static int e2k_hw_labelno;
static vec<e2k_hw_stub> e2k_hw_pending;
static vec<e2k_hw_stub> e2k_hw_stubs;

static void
e2k_dam_print_pending (FILE *f)
{
  for (int n : e2k_dam_pending)
    fprintf (f, ".LDAMB%d:\n", n);
  e2k_dam_pending.truncate (0);
  for (e2k_hw_stub &h : e2k_hw_pending)
    {
      output_asm_insn ("{\n\tcmpedb\t%1, 0, %2\n\t}", h.ops);
      fprintf (f, "\t{\n\tibranch\t.LHW%d ? ~", h.n);
      output_operand (h.ops[2], 0);
      fputs ("\n\t}\n", f);
    }
  e2k_hw_pending.truncate (0);
}

/* The wait before a hardware loop (e2k_lsr_wait, INSN): the loop may
   start 4 cycles after rwd %lsr (spec/isa/loops.md; v3-v5 run one
   iteration too many when it starts sooner, v6 only one).  Count the
   cycles of the wide instructions since rwd, printed before INSN, and
   wait out the rest.  Anything not counted exactly (a label, which
   another way in may reach, a multi-insn or raw sequence, asm) counts
   as no cycles, so the wait is never short.  */
const char *
e2k_output_lsr_wait (rtx_insn *insn)
{
  int cycles = 0;
  bool found = false;
  if (e2k_bundling)
    for (rtx_insn *x = PREV_INSN (insn); x; x = PREV_INSN (x))
      {
	if (LABEL_P (x) || BARRIER_P (x))
	  break;
	if (!NONDEBUG_INSN_P (x) || !e2k_prints_p (x))
	  continue;
	unsigned uid = INSN_UID (x);
	if (e2k_asm_insn_p (x) || e2k_raw_insn_p (x)
	    || uid >= e2k_marks.length ())
	  continue;
	/* The %lsr1 write is a multi-insn whose last instruction is it.  */
	bool rwd = e2k_rwd_lsr_p (x);
	if (!rwd && recog_memoized (x) >= 0
	    && get_attr_type (x) == TYPE_MULTI)
	  continue;
	if (e2k_marks[uid].close)
	  cycles += 1 + e2k_marks[uid].nops + e2k_marks[uid].post_nops;
	if (rwd)
	  {
	    found = true;
	    break;
	  }
	if (e2k_marks[uid].lead_nop)
	  cycles += 1;
      }
  int wait = found ? 4 - cycles : 4;
  if (wait <= 0)
    return "";
  static char buf[32];
  snprintf (buf, sizeof buf, "{\n\tnop\t%d\n\t}", wait - 1);
  return buf;
}

/* N empty cycles as wide instructions of their own, each one cycle and
   up to 7 nops (the HS field).  Cutting a longer wait short makes the
   consumer issue early, and an interlock stall costs about a whole
   latency more (spec/isa/timing.md): a divide's 11 cycles became 21.  */
static void
e2k_print_empty (FILE *f, int n)
{
  while (n > 0)
    {
      int k = MIN (n - 1, 7);
      fprintf (f, "\t{\n\tnop\t%d\n\t}\n", k);
      n -= k + 1;
    }
}

void
e2k_final_prescan_insn (rtx_insn *insn)
{
  if (!INSN_P (insn))
    return;
  /* gas pads user asm as lcc does (.accept strict_delay around it).  */
  if (e2k_asm_insn_p (insn))
    {
      fputs ("\t.accept\tstrict_delay\n", asm_out_file);
      return;
    }
  e2k_cur_sm = (e2k_ms_flag (insn) & 1) != 0;
  if (!e2k_bundling)
    return;
  unsigned uid = INSN_UID (insn);
  if (uid < e2k_marks.length () && e2k_marks[uid].open && !e2k_in_bundle
      && e2k_prints_p (insn) && !e2k_raw_insn_p (insn))
    {
      if (e2k_marks[uid].lead_nop)
	fputs ("\t{\n\tnop\t0\n\t}\n", asm_out_file);
      fputs ("\t{\n", asm_out_file);
      e2k_in_bundle = true;
    }
}

void
e2k_final_postscan_insn (FILE *f, rtx_insn *insn, rtx *, int)
{
  e2k_cur_sm = false;
  if (e2k_asm_insn_p (insn))
    {
      fputs ("\t.ignore\tstrict_delay\n", f);
      return;
    }
  if (!e2k_bundling)
    {
      e2k_dam_print_pending (f);
      return;
    }
  unsigned uid = INSN_UID (insn);
  if (e2k_in_bundle && uid < e2k_marks.length () && e2k_marks[uid].close)
    {
      int nops = e2k_marks[uid].nops;
      if (nops)
	fprintf (f, "\tnop\t%d\n", MIN (nops, 7));
      fputs ("\t}\n", f);
      /* A label where the instruction ends, its name the estimate.  */
      if (e2k_wi_size_check)
	{
	  static int n;
	  fprintf (f, ".Lwi%d_%d:\n", n++, e2k_marks[uid].words);
	}
      e2k_in_bundle = false;
      e2k_dam_print_pending (f);
      e2k_print_empty (f, nops - MIN (nops, 7));
      e2k_print_empty (f, e2k_marks[uid].post_nops);
    }
}

const char *
e2k_asm_output_opcode (FILE *f, const char *code)
{
  /* "addd,3" (e2k_assign_channels), "addd,sm" (a pipelined loop's
     operation), "addd,3,sm".  A mnemonic with an operand in it prints
     its channel with "%,".  */
  int chan = e2k_cur_chan ();
  if (!e2k_cur_sm && chan < 0)
    return code;
  const char *p = code;
  while (*p && *p != '\t' && *p != ' ' && *p != '\n' && *p != ','
	 && *p != '%')
    p++;
  if (*p == '%')
    return code;
  fwrite (code, 1, p - code, f);
  if (chan >= 0)
    fprintf (f, ",%d", chan);
  if (e2k_cur_sm)
    fputs (",sm", f);
  return p;
}

void
e2k_asm_function_prologue (FILE *)
{
  e2k_in_bundle = false;
}

void
e2k_asm_function_epilogue (FILE *f)
{
  if (e2k_in_bundle)
    fputs ("\t}\n", f);
  e2k_in_bundle = false;
  e2k_bundling = false;
  e2k_dam_print_pending (f);
  for (int n : e2k_dam_stubs)
    fprintf (f, ".LDAM%d:\n\t{\n\tibranch\t.LDAMB%d\n\t}\n", n, n);
  e2k_dam_stubs.truncate (0);
  for (char *p : e2k_apb_progs)
    {
      fputs (p, f);
      free (p);
    }
  e2k_apb_progs.truncate (0);
  for (e2k_hw_stub &h : e2k_hw_stubs)
    {
      char buf[128];
      snprintf (buf, sizeof buf,
		"{\n\tsubd\t%%1, %#" PRIx64 ", %%1\n\trwd\t%#" PRIx64
		", %%%%lsr\n\tnop\t3\n\t}\n\t{\n\tct\t%%0\n\t}",
		(uint64_t) E2K_LSR_CHUNK,
		(uint64_t) (E2K_LSR_CHUNK | E2K_LSR_VLC));
      fprintf (f, ".LHW%d:\n", h.n);
      output_asm_insn (buf, h.ops);
    }
  e2k_hw_stubs.truncate (0);
}

/* The end of a strip-mined loop (e2k_hwloop_end_wide; OPERANDS: CTPR,
   label, iterations left, predicate).  When the chunk is done and
   iterations are left, the stub takes the next chunk: %lsr = CHUNK |
   vlc, at least 4 cycles before the CTPR's transfer back to the loop.
   Strip-mined loops are rare enough that the test after the loop
   needn't share wide instructions with the code that follows.  */
const char *
e2k_output_hwloop_end_wide (rtx_insn *insn, rtx *operands)
{
  e2k_hw_stub h;
  h.n = ++e2k_hw_labelno;
  h.ops[0] = operands[0];
  h.ops[1] = operands[2];
  h.ops[2] = operands[3];
  e2k_hw_pending.safe_push (h);
  e2k_hw_stubs.safe_push (h);
  return e2k_output_hwloop_end (insn);
}
