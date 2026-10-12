/* Software pipelining for the Elbrus (E2K) port (see e2k-ms.cc):
   a loop's operations, their register and memory dependences, the loads
   array prefetch reads (spec/isa/apb.md), AAU stores and DAM checks.
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

unsigned
e2k_ms_flag (const rtx_insn *insn)
{
  unsigned uid = INSN_UID (insn);
  return uid < e2k_ms_flags.length () ? e2k_ms_flags[uid] : 0;
}

void
e2k_ms_set_flag (rtx_insn *insn, unsigned f)
{
  unsigned uid = INSN_UID (insn);
  if (uid >= e2k_ms_flags.length ())
    e2k_ms_flags.safe_grow_cleared (uid + 64);
  e2k_ms_flags[uid] |= f;
}








/* setbn_enter for L: it uses the %b[0..7] live after the loop, whose
   values pass through it, and nothing for the others, which would
   otherwise look live before every pipelined loop and so live out of an
   earlier one (NPB SP's zeta-direction fluxes, refused for a %b[1] only
   the next pipelined loop's setbn read).  */
rtx
e2k_ms_gen_setbn_enter (e2k_ms_loop *l)
{
  rtx u[8];
  bitmap a = df_get_live_in (l->exit);
  bitmap b = l->x1 ? df_get_live_in (l->x1) : a;
  for (int k = 0; k < 8; k++)
    u[k] = (bitmap_bit_p (a, B0_REGNUM + k) || bitmap_bit_p (b, B0_REGNUM + k)
	    ? gen_rtx_REG (DImode, B0_REGNUM + k) : const0_rtx);
  return gen_e2k_setbn_enter (GEN_INT (l->pairs), GEN_INT (l->npred), u[0],
			      u[1], u[2], u[3], u[4], u[5], u[6], u[7]);
}

/* Whether a loop body insn can be pipelined: one SET of a register or
   memory, of a kind that has a speculative form, or a store under a
   predicate (if-conversion's); compares into predicates that merges and
   such stores read, and in a while loop (WL) also the compares and
   landp of its exit test, which only read registers and each other.  */
static bool
e2k_ms_insn_ok (rtx_insn *insn, bool wl)
{
  if (!NONJUMP_INSN_P (insn) || recog_memoized (insn) < 0)
    return false;
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) == COND_EXEC)
    {
      rtx test = COND_EXEC_TEST (pat);
      if ((GET_CODE (test) != NE && GET_CODE (test) != EQ)
	  || !REG_P (XEXP (test, 0)) || !PRED_REGNO_P (REGNO (XEXP (test, 0)))
	  || XEXP (test, 1) != const0_rtx)
	return false;
      pat = COND_EXEC_CODE (pat);
      if (GET_CODE (pat) != SET || !MEM_P (SET_DEST (pat)))
	return false;
    }
  if (GET_CODE (pat) != SET || volatile_refs_p (pat)
      || side_effects_p (SET_SRC (pat)))
    return false;
  enum attr_type t = get_attr_type (insn);
  if (REG_P (SET_DEST (pat)) && PRED_REGNO_P (REGNO (SET_DEST (pat))))
    {
      /* FP compares too (LAME's quantize_lines_xrpow_01, "ix[0] =
	 (compareval0 > xr[0]) ? 0 : 1"): speculated as the loop's other
	 FP operations, so not under -mno-spec-fp (e2k_ms_analyze).  */
      if (t != TYPE_CMP && t != TYPE_FCMP && t != TYPE_CCTOP
	  && (t != TYPE_PLOG || !wl))
	return false;
      subrtx_iterator::array_type array;
      FOR_EACH_SUBRTX (iter, array, SET_SRC (pat), NONCONST)
	{
	  const_rtx x = *iter;
	  if (MEM_P (x))
	    return false;
	  if (REG_P (x)
	      && (REG_NREGS (x) != 1 || BX_REGNO_P (REGNO (x))
		  || (t == TYPE_PLOG
		      ? !PRED_REGNO_P (REGNO (x)) : !GPR_REGNO_P (REGNO (x)))))
	    return false;
	}
      return true;
    }
  switch (t)
    {
    case TYPE_ALU: case TYPE_ALU14: case TYPE_ALU0134: case TYPE_MUL:
    case TYPE_FP:
    case TYPE_FMA: case TYPE_FFMA: case TYPE_FCVT: case TYPE_LOAD:
    case TYPE_STORE:
    case TYPE_PINT: case TYPE_PINT14: case TYPE_PMUL: case TYPE_PANY:
    case TYPE_FLAG: case TYPE_FLAGMUL:
      break;
    /* FP divides (PolyBench's seidel-2d): the divider in ALC5 takes one
       every 2 cycles (e2k_ms_place); lcc speculates them in its
       pipelined loops too (spec/isa/speculation.md).  Not the square
       roots: fsqrts conflicts 5 cycles apart, fsqrttd reads two.  */
    case TYPE_FDIV:
      if (GET_CODE (SET_SRC (pat)) != DIV)
	return false;
      break;
    default:
      return false;
    }
  rtx dest = SET_DEST (pat);
  if (REG_P (dest))
    {
      unsigned r = REGNO (dest);
      if (REG_NREGS (dest) != 1 || !GPR_REGNO_P (r)
	  || BX_REGNO_P (r) || fixed_regs[r])
	return false;
    }
  else if (!MEM_P (dest))
    return false;
  int nmem = 0;
  /* A merge reads the predicate of its condition.  */
  rtx mcond = (GET_CODE (SET_SRC (pat)) == IF_THEN_ELSE
	       ? XEXP (XEXP (SET_SRC (pat), 0), 0) : NULL_RTX);
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, pat, NONCONST)
    {
      const_rtx x = *iter;
      if (MEM_P (x))
	{
	  nmem++;
	  if (MEM_VOLATILE_P (x) || GET_MODE (x) == BLKmode)
	    return false;
	}
      else if (REG_P (x) && x == mcond && PRED_REGNO_P (REGNO (x)))
	continue;
      else if (REG_P (x)
	       && (REG_NREGS (x) != 1
		   || BX_REGNO_P (REGNO (x)) || !GPR_REGNO_P (REGNO (x))))
	return false;
    }
  return nmem <= 1;
}

/* The registers X reads.  */
static bool
e2k_ms_note_uses (e2k_ms_node *node, rtx x)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, x, NONCONST)
    if (REG_P (*iter))
      {
	unsigned r = REGNO (*iter);
	int k;
	for (k = 0; k < node->nuses; k++)
	  if (node->uses[k].regno == r)
	    break;
	if (k < node->nuses)
	  continue;
	if (node->nuses == E2K_MS_MAX_USES)
	  return false;
	node->uses[node->nuses].regno = r;
	node->uses[node->nuses].value = -1;
	node->uses[node->nuses].dist = 0;
	node->nuses++;
      }
  return true;
}

/* An address as INV + IV + OFFSET: INV a loop-invariant register (or
   none), IV a register the loop steps by a constant (or none).  */
struct e2k_ms_addr
{
  unsigned inv, iv;		/* INVALID_REGNUM if absent */
  HOST_WIDE_INT offset;
  bool ok;
};

static void
e2k_ms_add_term (e2k_ms_addr *a, rtx x, const HOST_WIDE_INT *step)
{
  if (CONST_INT_P (x))
    a->offset += INTVAL (x);
  else if (REG_P (x) && step[REGNO (x)] != 0)
    {
      if (a->iv != INVALID_REGNUM)
	a->ok = false;
      a->iv = REGNO (x);
    }
  else if (REG_P (x) && step[REGNO (x)] == 0)
    {
      if (a->inv != INVALID_REGNUM)
	a->ok = false;
      a->inv = REGNO (x);
    }
  else
    a->ok = false;
}

/* Decompose MEM's address; STEP[r] is the per-iteration step of
   induction register r (0: invariant, HOST_WIDE_INT_MIN: varies).  */
static e2k_ms_addr
e2k_ms_decompose (rtx mem, const HOST_WIDE_INT *step)
{
  e2k_ms_addr a = { INVALID_REGNUM, INVALID_REGNUM, 0, true };
  rtx x = XEXP (mem, 0);
  if (GET_CODE (x) == PLUS)
    {
      e2k_ms_add_term (&a, XEXP (x, 0), step);
      e2k_ms_add_term (&a, XEXP (x, 1), step);
    }
  else
    e2k_ms_add_term (&a, x, step);
  if (a.inv != INVALID_REGNUM && step[a.inv] == HOST_WIDE_INT_MIN)
    a.ok = false;
  if (a.iv != INVALID_REGNUM && step[a.iv] == HOST_WIDE_INT_MIN)
    a.ok = false;
  return a;
}

static bool e2k_ms_inv_delta (unsigned, unsigned, basic_block,
			      HOST_WIDE_INT *, int = 0);

/* What INSN's SET_SRC, a register or a register plus a constant, is
   in terms of a register at the start of INSN's block: *C plus the
   register returned (through the block's own copies and constant adds
   before INSN: a latch that steps a pointer through a temporary,
   "t = r + 16000; ...; r = t"), or NULL.  */
static rtx
e2k_ms_block_start_value (rtx_insn *insn, HOST_WIDE_INT *c)
{
  basic_block bb = BLOCK_FOR_INSN (insn);
  *c = 0;
  for (int k = 0; k < 4; k++)
    {
      rtx set = PATTERN (insn);
      if (GET_CODE (set) != SET || !REG_P (SET_DEST (set))
	  || GET_MODE (SET_DEST (set)) != DImode)
	return NULL_RTX;
      rtx x = SET_SRC (set);
      if (GET_CODE (x) == PLUS && CONST_INT_P (XEXP (x, 1)))
	{
	  *c += INTVAL (XEXP (x, 1));
	  x = XEXP (x, 0);
	}
      if (!REG_P (x) || GET_MODE (x) != DImode)
	return NULL_RTX;
      rtx_insn *def = NULL;
      for (rtx_insn *i = PREV_INSN (insn);
	   i && i != PREV_INSN (BB_HEAD (bb)); i = PREV_INSN (i))
	if (INSN_P (i) && reg_set_p (x, i))
	  {
	    def = i;
	    break;
	  }
      if (!def)
	return x;
      insn = def;
    }
  return NULL_RTX;
}

/* For e2k_ms_inv_delta: what the pair of IA (setting RA) and IB
   (setting RB), the only insns of their block that set them, does to
   RA - RB: 1, it becomes *D; 2, it stays (both stepped by one
   constant); 0, anything else.  DEPTH: e2k_ms_inv_delta's.  */
static int
e2k_ms_pair_delta (rtx_insn *ia, rtx_insn *ib, unsigned ra, unsigned rb,
		   HOST_WIDE_INT *d, int depth)
{
  HOST_WIDE_INT ca, cb;
  rtx xa = e2k_ms_block_start_value (ia, &ca);
  rtx xb = e2k_ms_block_start_value (ib, &cb);
  if (!xa || !xb)
    return 0;
  if (REGNO (xa) == ra && REGNO (xb) == rb)
    return ca == cb ? 2 : 0;
  /* From one register: its value at the block's start.  */
  if (REGNO (xa) == REGNO (xb))
    {
      *d = ca - cb;
      return 1;
    }
  /* From two registers apart by a constant themselves at the block's
     start (seidel-2d's rows start as copies of their first values, set
     before the time loop).  */
  HOST_WIDE_INT dx;
  if (depth < 3
      && e2k_ms_inv_delta (REGNO (xa), REGNO (xb), BLOCK_FOR_INSN (ia), &dx,
			   depth + 1))
    {
      *d = dx + ca - cb;
      return 1;
    }
  return 0;
}

/* The one insn of BB that sets register R, or NULL; *N: how many do
   (a call that clobbers it counts).  */
static rtx_insn *
e2k_ms_block_def (basic_block bb, rtx r, int *n)
{
  rtx_insn *d = NULL, *insn;
  *n = 0;
  FOR_BB_INSNS (bb, insn)
    if (INSN_P (insn) && reg_set_p (r, insn))
      {
	d = insn;
	++*n;
      }
  return d;
}

/* Whether the registers RA and RB, which block AT doesn't set, differ
   by a constant at its start, *DELTA = RA - RB: on the way back from AT
   to where they were last set, every block that sets either sets both,
   once each, and either sets them from one register plus constants (or
   one from the other, or from two registers that differ by a constant
   there, to DEPTH 3), the same difference each time, or steps both by
   one constant and is itself reached that way.  The registers are hard
   ones, which other code of the function may use for other values: only
   the definitions that reach AT matter.  PolyBench's seidel-2d updates
   its array in place through rows i - 1, i and i + 1, pointers its outer
   loop steps by a row each: the store to row i and the load of the next
   element of row i are then a known distance apart, and the loads of
   the other rows (which the alias oracle has apart) can go through
   array prefetch.  */
static bool
e2k_ms_inv_delta (unsigned ra, unsigned rb, basic_block at,
		  HOST_WIDE_INT *delta, int depth)
{
  if (ra == rb)
    {
      *delta = 0;
      return true;
    }
  if (ra == INVALID_REGNUM || rb == INVALID_REGNUM
      || !GPR_REGNO_P (ra) || !GPR_REGNO_P (rb)
      || fixed_regs[ra] || fixed_regs[rb])
    return false;
  rtx xa = gen_rtx_REG (DImode, ra), xb = gen_rtx_REG (DImode, rb);
  bool ok = true, set = false;
  HOST_WIDE_INT d = 0;
  auto_bitmap seen;
  auto_vec<basic_block> work;
  work.safe_push (at);
  while (ok && !work.is_empty ())
    {
      basic_block b = work.pop ();
      edge e;
      edge_iterator ei;
      FOR_EACH_EDGE (e, ei, b->preds)
	{
	  basic_block p = e->src;
	  if (p == ENTRY_BLOCK_PTR_FOR_FN (cfun))
	    {
	      ok = false;
	      break;
	    }
	  if (!bitmap_set_bit (seen, p->index))
	    continue;
	  int na, nb;
	  rtx_insn *ia = e2k_ms_block_def (p, xa, &na);
	  rtx_insn *ib = e2k_ms_block_def (p, xb, &nb);
	  if (na == 0 && nb == 0)
	    {
	      work.safe_push (p);
	      continue;
	    }
	  HOST_WIDE_INT pd;
	  int kind = (na != 1 || nb != 1 || p == at ? 0
		      : e2k_ms_pair_delta (ia, ib, ra, rb, &pd, depth));
	  if (kind == 1 && (!set || pd == d))
	    {
	      set = true;
	      d = pd;
	    }
	  else if (kind == 2)
	    work.safe_push (p);
	  else
	    {
	      ok = false;
	      break;
	    }
	}
    }
  ok &= set;
  if (dump_file)
    fprintf (dump_file, ";; e2k_modsched: r%u - r%u at bb %d: %s "
	     HOST_WIDE_INT_PRINT_DEC "\n", ra, rb, at->index,
	     ok ? "apart by" : "unknown", ok ? d : (HOST_WIDE_INT) 0);
  if (ok)
    *delta = d;
  return ok;
}

static void
e2k_ms_add_dep (e2k_ms_loop *l, int from, int to, int lat, int dist,
		int cross = 0)
{
  for (e2k_ms_dep &d : l->deps)
    if (d.from == from && d.to == to && d.dist == dist)
      {
	int base = MAX (d.lat - d.cross, lat - cross);
	d.lat = MAX (d.lat, lat);
	d.cross = d.lat - base;
	return;
      }
  e2k_ms_dep d = { from, to, lat, dist, cross };
  l->deps.safe_push (d);
}

/* Whether A and B, through the same pointer, a parameter (one value in
   every iteration), are at byte ranges that don't overlap: the tree
   oracle does this only while the function is in SSA form (xz's price
   table and its trailing opts array, both in *coder).  */
static bool
e2k_ms_disjoint_p (rtx a, rtx b)
{
  tree ea = MEM_EXPR (a), eb = MEM_EXPR (b);
  if (!ea || !eb)
    return false;
  ao_ref ra, rb;
  ao_ref_init (&ra, ea);
  ao_ref_init (&rb, eb);
  tree ba = ao_ref_base (&ra), bb = ao_ref_base (&rb);
  if (!ba || !bb || TREE_CODE (ba) != MEM_REF || TREE_CODE (bb) != MEM_REF
      || TREE_CODE (TREE_OPERAND (ba, 0)) != SSA_NAME
      || TREE_OPERAND (ba, 0) != TREE_OPERAND (bb, 0)
      || !SSA_NAME_IS_DEFAULT_DEF (TREE_OPERAND (ba, 0)))
    return false;
  /* The access within what its expression may touch.  */
  for (rtx m : { a, b })
    {
      ao_ref &r = m == a ? ra : rb;
      if (!MEM_OFFSET_KNOWN_P (m) || !MEM_SIZE_KNOWN_P (m)
	  || maybe_lt (MEM_OFFSET (m), 0)
	  || (r.max_size_known_p ()
	      && maybe_gt ((MEM_OFFSET (m) + MEM_SIZE (m)) * BITS_PER_UNIT,
			   r.max_size)))
	return false;
    }
  poly_offset_int oa = ra.offset, ob = rb.offset;
  oa += mem_ref_offset (ba) << LOG2_BITS_PER_UNIT;
  ob += mem_ref_offset (bb) << LOG2_BITS_PER_UNIT;
  return !ranges_maybe_overlap_p (oa, ra.max_size, ob, rb.max_size);
}

/* Whether memory references A and B may conflict in any two iterations.
   may_alias_p ignores offsets, but believes dependence cliques, and
   those of an inlined function's restrict pointers only hold within one
   call (one iteration; gcc.dg/torture/pr90328.c): trust only clique 1
   (the function's own restrict pointers) and those of loops versioned
   for aliasing, and else ask again without the trees.  */
static bool
e2k_ms_may_alias (rtx a, rtx b)
{
  if (e2k_ms_disjoint_p (a, b))
    return false;
  if (may_alias_p (a, b))
    return true;
  tree ea = MEM_EXPR (a), eb = MEM_EXPR (b);
  if (!ea || !eb)
    return false;
  tree ba = get_base_address (ea), bb = get_base_address (eb);
  if (!ba || !bb
      || (TREE_CODE (ba) != MEM_REF && TREE_CODE (ba) != TARGET_MEM_REF)
      || (TREE_CODE (bb) != MEM_REF && TREE_CODE (bb) != TARGET_MEM_REF))
    return false;
  unsigned short c = MR_DEPENDENCE_CLIQUE (ba);
  machine_function *m = cfun->machine;
  if (c == 0 || c == 1 || c != MR_DEPENDENCE_CLIQUE (bb))
    return false;
  for (int k = 0; k < m->n_av_cliques; k++)
    if (c == m->av_cliques[k])
      return false;
  rtx a2 = copy_rtx (a), b2 = copy_rtx (b);
  set_mem_expr (a2, NULL_TREE);
  set_mem_expr (b2, NULL_TREE);
  return may_alias_p (a2, b2);
}

/* Whether a store to ST can't reach a later load from LD by the types
   they access (strict aliasing): a load may not read memory last stored
   through an incompatible type, while a later store may give it a new
   one, so only such true dependences may be left out, as GCC's
   true_dependence does (may_alias_p uses no types at all).  LAME's
   count_bits: int stores into ix against float loads of xr.  */
static bool
e2k_ms_tbaa_raw_p (rtx st, rtx ld)
{
  return (e2k_ms_tbaa && flag_strict_aliasing && MEM_ALIAS_SET (st)
	  && MEM_ALIAS_SET (ld)
	  && !alias_sets_conflict_p (MEM_ALIAS_SET (st), MEM_ALIAS_SET (ld)));
}

/* What a register derived from an induction register is
   (e2k_ms_analyze): X + INV + C, 64 bits, when OK.  */
struct e2k_ms_derived
{
  unsigned x[FIRST_PSEUDO_REGISTER], inv[FIRST_PSEUDO_REGISTER];
  HOST_WIDE_INT c[FIRST_PSEUDO_REGISTER];
  bool ok[FIRST_PSEUDO_REGISTER];
};

/* An address A through a derived register R = X + INV + C, as one
   through X: INV becomes A's invariant, or *INV2 when it has one, and
   *ADJ is R's value in the first iteration less X's on the way in (C,
   plus X's step when X steps before R is computed).  False, A
   unchanged, if A's register isn't such a one.  */
static bool
e2k_ms_underive (e2k_ms_addr *a, unsigned *inv2, HOST_WIDE_INT *adj,
		 const bool *derived, const e2k_ms_derived *dv,
		 const HOST_WIDE_INT *step, const int *ivdef)
{
  *inv2 = INVALID_REGNUM;
  *adj = 0;
  if (!a->ok || a->iv == INVALID_REGNUM || !derived[a->iv])
    return false;
  unsigned r = a->iv;
  if (!dv->ok[r] || derived[dv->x[r]])
    return false;
  *adj = dv->c[r] + (ivdef[dv->x[r]] < ivdef[r] ? step[dv->x[r]] : 0);
  if (a->inv == INVALID_REGNUM)
    a->inv = dv->inv[r];
  else
    *inv2 = dv->inv[r];
  a->iv = dv->x[r];
  return true;
}

/* Memory dependences.  POS[i] is node i's place in the body; IVDEF[r]
   the node that steps induction register r.  */
static void
e2k_ms_mem_deps (e2k_ms_loop *l, const HOST_WIDE_INT *step,
		 const int *ivdef, const bool *derived,
		 const e2k_ms_derived *dv)
{
  for (int a = 0; a < l->n; a++)
    for (int b = a + 1; b < l->n; b++)
      {
	e2k_ms_node *na = &l->nodes[a], *nb = &l->nodes[b];
	if (!na->mem || !nb->mem || (!na->store && !nb->store))
	  continue;
	/* A mova reads what the unit fetched ahead; e2k_ms_mark_apb made
	   sure no store of the loop writes that.  */
	if (na->apb || nb->apb)
	  continue;
	bool alias = e2k_ms_may_alias (na->mem, nb->mem);
	/* A store's data reaches a load in the next wide instruction late
	   (spec/isa/timing.md, "Store to load").  */
	int lab = na->store && !nb->store ? 2 : 1;
	int lba = nb->store && !na->store ? 2 : 1;
	e2k_ms_addr aa = e2k_ms_decompose (na->mem, step);
	e2k_ms_addr ab = e2k_ms_decompose (nb->mem, step);
	/* Through a register derived from an induction register, in
	   that register's terms (the copies of an unrolled body:
	   "A[i][j]" through ivtmp, "A[i + 1][j]" through ivtmp + 4800).  */
	unsigned ia2, ib2;
	HOST_WIDE_INT adja, adjb;
	bool va = e2k_ms_underive (&aa, &ia2, &adja, derived, dv, step, ivdef);
	bool vb = e2k_ms_underive (&ab, &ib2, &adjb, derived, dv, step, ivdef);
	if (dump_file)
	  fprintf (dump_file, ";; e2k_modsched: mem %d %d: %s, inv %d/%d "
		   "iv %d/%d ok %d/%d\n", INSN_UID (na->insn),
		   INSN_UID (nb->insn), alias ? "may alias" : "independent",
		   (int) aa.inv, (int) ab.inv, (int) aa.iv, (int) ab.iv,
		   aa.ok, ab.ok);
	if (!alias)
	  continue;
	/* A's invariant part from B's (e2k_ms_inv_delta).  */
	HOST_WIDE_INT dinv = 0;
	if (aa.ok && ab.ok && !va && !vb && aa.iv == ab.iv
	    && aa.iv != INVALID_REGNUM && aa.inv != ab.inv
	    && e2k_ms_inv_delta (aa.inv, ab.inv, l->bb, &dinv))
	  aa.inv = ab.inv;
	bool same_inv = ((!va && !vb && aa.inv == ab.inv)
			 || ((va || vb)
			     && ((aa.inv == ab.inv
				  && (va ? ia2 : INVALID_REGNUM)
				     == (vb ? ib2 : INVALID_REGNUM))
				 || (aa.inv == (vb ? ib2 : INVALID_REGNUM)
				     && (va ? ia2 : INVALID_REGNUM)
					== ab.inv))));
	if (aa.ok && ab.ok && same_inv && aa.iv == ab.iv
	    && aa.iv != INVALID_REGNUM)
	  {
	    /* Both step through one array: the access of B in iteration
	       I + D starts at (ob - oa) + D * C bytes from A's in I.  */
	    HOST_WIDE_INT c = step[aa.iv];
	    HOST_WIDE_INT oa = (va ? aa.offset + adja
				: aa.offset + dinv + (ivdef[aa.iv] < a ? c : 0));
	    HOST_WIDE_INT ob = (vb ? ab.offset + adjb
				: ab.offset + (ivdef[ab.iv] < b ? c : 0));
	    HOST_WIDE_INT sa = GET_MODE_SIZE (GET_MODE (na->mem));
	    HOST_WIDE_INT sb = GET_MODE_SIZE (GET_MODE (nb->mem));
	    for (int d = 0; d <= E2K_MS_MAX_II; d++)
	      {
		HOST_WIDE_INT diff = ob - oa + d * c;	/* B(I+D) - A(I) */
		if (diff > -sb && diff < sa)
		  e2k_ms_add_dep (l, a, b, lab, d);
		diff = oa - ob + d * c;			/* A(I+D) - B(I) */
		if (d > 0 && diff > -sa && diff < sb)
		  e2k_ms_add_dep (l, b, a, lba, d);
	      }
	  }
	else if (aa.ok && ab.ok && aa.inv == ab.inv && aa.iv == ab.iv)
	  {
	    /* The same invariant address every iteration.  */
	    e2k_ms_add_dep (l, a, b, lab, 0);
	    e2k_ms_add_dep (l, b, a, lba, 1);
	  }
	else if (na->store != nb->store
		 && e2k_ms_tbaa_raw_p (na->store ? na->mem : nb->mem,
				       na->store ? nb->mem : na->mem))
	  {
	    /* Only the load before a store after it.  */
	    int st = na->store ? a : b, ld = na->store ? b : a;
	    e2k_ms_add_dep (l, ld, st, 1, na->store ? 1 : 0);
	  }
	else if (na->store != nb->store && l->want_dam)
	  {
	    /* Left out for a lock load and its check (e2k_ms_add_dam);
	       the load stays before a store after it.  */
	    int st = na->store ? a : b, ld = na->store ? b : a;
	    e2k_ms_dep d = { st, ld, 2, na->store ? 0 : 1, 0 };
	    l->dam_deps.safe_push (d);
	    e2k_ms_add_dep (l, ld, st, 1, na->store ? 1 : 0);
	  }
	else
	  {
	    /* Only may alias: not likely the same doubleword.  */
	    e2k_ms_add_dep (l, a, b, 1, 0);
	    e2k_ms_add_dep (l, b, a, 1, 1);
	    l->may_dam |= na->store != nb->store;
	  }
      }
}

/* Whether MEM is aligned to BYTES by what its object or the computation
   of its address shows.  Not MEM_ALIGN, which takes a pointer's target
   type at its word: a cast such as *(uint32_t *) (buf + 1), common in
   decoders, belies it.  */
bool
e2k_known_aligned_p (rtx mem, unsigned bytes)
{
  if (!MEM_EXPR (mem) || !MEM_OFFSET_KNOWN_P (mem))
    return false;
  HOST_WIDE_INT off;
  if (!MEM_OFFSET (mem).is_constant (&off))
    return false;
  unsigned int align, bits = bytes * BITS_PER_UNIT;
  unsigned HOST_WIDE_INT bitpos;
  get_object_alignment_2 (MEM_EXPR (mem), &align, &bitpos, true);
  return (align >= bits
	  && (bitpos + (unsigned HOST_WIDE_INT) off * BITS_PER_UNIT) % bits == 0);
}

/* Array prefetch (spec/isa/apb.md) for the loads of L, a loop counted
   by %lsr: those that read aligned elements through an address the
   loop steps forward by a whole number of them (an increment
   register), and whose elements no store of the loop writes before
   they are read (the buffer doesn't see stores): a store may write the
   element the load read in the same iteration, after it, or behind
   it.  Each becomes a mova (latency 5, an AAS channel, no ALU channel)
   in the kernel; the prologue keeps the load.  Loads through one
   address share a descriptor; e2k_ms_apb_assign gives them areas.  At
   most 16 (4 AAS channels a cycle) through 8 descriptors with 7
   increments.  STEP and IVDEF as for e2k_ms_mem_deps; DERIVED the
   stepped registers the loop computes from another, DV what they are.  */
static void
e2k_ms_mark_apb (e2k_ms_loop *l, const HOST_WIDE_INT *step,
		 const int *ivdef, const bool *derived,
		 const e2k_ms_derived *dv)
{
  l->napb = 0;
  l->napb_d = 0;
  /* With a lock load too, as lcc's histogram loops (NPB IS): the
     compensation code goes back by an ibranch, which leaves %ctpr2.  */
  if (!l->apb_ok || (l->want_dam && !e2k_dam_apb))
    return;
  /* On the 4C a stream through array prefetch beside one read
     backwards with plain loads (which v3 can't prefetch, below) costs
     about 1.3 cycles an element from L2 and a little from memory, at
     the same schedule: PolyBench's durbin, "r[k-i-1] * y[i]" and
     "y[i] + alpha * y[k-i-1]", 3.94 -> 5.40 s with y prefetched; a
     probe, one forward and one backward stream at II 4: 5.37 ns an
     element from L2 with plain loads, 7.05 with the forward one
     prefetched.  Such loops keep plain loads on v3 and v4.  */
  if (e2k_arch < 5 && e2k_apb_beside_backward == 0)
    for (int i = 0; i < l->n; i++)
      {
	e2k_ms_node *node = &l->nodes[i];
	if (!node->mem || node->store || node->value < 0)
	  continue;
	e2k_ms_addr a = e2k_ms_decompose (node->mem, step);
	if (a.ok && a.iv != INVALID_REGNUM && !derived[a.iv]
	    && step[a.iv] < 0)
	  {
	    if (dump_file)
	      fprintf (dump_file, ";; e2k_modsched: no array prefetch: "
		       "insn %d reads backwards\n", INSN_UID (node->insn));
	    return;
	  }
      }
  HOST_WIDE_INT incrs[8];
  int nincr = 0;
  for (int i = 0; i < l->n && l->napb < 32; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      if (!node->mem || node->store || node->value < 0 || node->lock
	  || node->chk >= 0 || MEM_VOLATILE_P (node->mem))
	continue;
      rtx pat = PATTERN (node->insn);
      if (GET_CODE (pat) != SET || !REG_P (SET_DEST (pat)))
	continue;
      rtx src = SET_SRC (pat);
      if (GET_CODE (src) == ZERO_EXTEND)
	src = XEXP (src, 0);
      machine_mode dm = GET_MODE (SET_DEST (pat));
      HOST_WIDE_INT size = GET_MODE_SIZE (GET_MODE (src));
      if (!MEM_P (src) || (size != 1 && size != 2 && size != 4 && size != 8)
	  || MEM_ALIGN (src) < size * BITS_PER_UNIT
	  || (dm != QImode && dm != HImode && dm != SImode && dm != DImode
	      && dm != SFmode && dm != DFmode && GET_MODE_SIZE (dm) != 8)
	  || (GET_CODE (SET_SRC (pat)) == ZERO_EXTEND && dm != DImode))
	continue;
      e2k_ms_addr a = e2k_ms_decompose (src, step);
      if (!a.ok || a.iv == INVALID_REGNUM)
	continue;
      /* The setup reads the stepped register before the loop: one the
	 loop computes from another has no value there, but one that is
	 X + INV is the setup's X + INV, a second invariant of the base
	 (NPB SP's compute_rhs: "u[k][j][i] ... u[k + 1][j][i]" through
	 one register plus the planes' offsets).  DADJ: its value in the
	 first iteration less X's on the way in.  */
      unsigned inv2 = INVALID_REGNUM;
      HOST_WIDE_INT dadj = 0;
      bool via = false;
      if (derived[a.iv])
	{
	  if (!e2k_apb_derived
	      || !e2k_ms_underive (&a, &inv2, &dadj, derived, dv, step, ivdef))
	    continue;
	  via = true;
	}
      /* Backwards too (negative increments work, spec/isa/apb.md; lcc
	 reads PolyBench's durbin "r[k-i-1]" so), from v5 on: before, an
	 area's offset from its base is 32 bits, zero-extended, so it may
	 not go below the base, which lcc puts at the last element read
	 (its start in %aaind), and the PoC at the first (gcc.dg/vect's
	 vect-15-big-array, SIGILL on the 4C).  */
      HOST_WIDE_INT stp = step[a.iv];
      if (stp == 0 || stp % size != 0 || stp / size > 0x7fffffff
	  || stp / size < -0x7fffffff || (stp < 0 && e2k_arch < 5))
	continue;
      /* v3 and v4 give diagnostic values from an area not aligned to its
	 elements; v5 reads 2, 4 and 8 bytes anywhere (spec/isa/apb.md).
	 The type's alignment, which C requires of the pointer, will do
	 (-mapb-type-align), as on a strict-alignment target.  lcc
	 proves it instead (NPB SP's global arrays) and assumes it only
	 with -faligned; here SP's loads go through pointers ivopts
	 made, whose alignment GCC no longer knows (SP.W on the 4C 50.8
	 -> 37.3 s, lcc 32.3).  A misaligned cast such as
	 *(uint32_t *) (buf + 1), undefined in C, then traps at the use
	 of the diagnostic value instead of reading slowly.  */
      if (size > 1 && e2k_arch < 5
	  && !(e2k_apb_type_align || e2k_known_aligned_p (src, size)))
	continue;
      /* Steps other than one element take an increment register.  */
      int ki = 0;
      if (stp != size)
	{
	  while (ki < nincr && incrs[ki] != stp / size)
	    ki++;
	  if (ki == 7)
	    continue;
	}
      HOST_WIDE_INT oa = (via ? a.offset + dadj
			  : a.offset + (ivdef[a.iv] < i ? stp : 0));
      bool ok = true;
      for (int k = 0; k < l->n && ok; k++)
	{
	  e2k_ms_node *st = &l->nodes[k];
	  if (!st->store || !e2k_ms_may_alias (st->mem, src))
	    continue;
	  e2k_ms_addr b = e2k_ms_decompose (st->mem, step);
	  HOST_WIDE_INT sb = GET_MODE_SIZE (GET_MODE (st->mem));
	  /* A store through a derived register in the load's terms (an
	     in-place update, "rhs[k][j][i] = rhs[k][j][i] + ...").  */
	  unsigned binv2 = INVALID_REGNUM;
	  HOST_WIDE_INT bdadj = 0;
	  bool bvia = (b.ok && b.iv != INVALID_REGNUM && derived[b.iv]
		       && e2k_ms_underive (&b, &binv2, &bdadj, derived, dv,
					   step, ivdef));
	  if (b.ok && b.iv != INVALID_REGNUM && derived[b.iv] && !bvia)
	    b.ok = false;
	  /* The store's invariant part from the load's.  */
	  HOST_WIDE_INT dinv = 0;
	  if (b.ok && !via && !bvia && b.iv == a.iv && b.inv != a.inv
	      && e2k_ms_inv_delta (b.inv, a.inv, l->bb, &dinv))
	    b.inv = a.inv;
	  HOST_WIDE_INT ob = b.offset + dinv + (bvia ? bdadj
						: (b.iv != INVALID_REGNUM
						   && ivdef[b.iv] < k ? stp : 0));
	  bool same_inv = ((b.inv == a.inv && binv2 == inv2)
			   || (b.inv == inv2 && binv2 == a.inv));
	  /* (Backwards, none may write the array.)  */
	  ok = b.ok && same_inv && b.iv == a.iv && stp > 0;
	  /* The store of an iteration against the movas D iterations on:
	     none may read what it wrote, nor in its own iteration once it
	     comes first (an unrolled body's store at dy+16 and load at
	     dy+8 are fine).  */
	  for (HOST_WIDE_INT d = k < i ? 0 : 1; ok && oa + stp * d < ob + sb;
	       d++)
	    ok = d < 64 && oa + stp * d + size <= ob;
	}
      if (!ok)
	continue;
      int d = -1;
      for (int k = 0; k < i && d < 0; k++)
	if (l->nodes[k].apb && l->nodes[k].apb_iv == a.iv
	    && l->nodes[k].apb_inv == a.inv && l->nodes[k].apb_inv2 == inv2)
	  d = l->nodes[k].apb_d;
      if (d < 0 && l->napb_d == 32)
	continue;
      rtx mova = gen_e2k_mova (dm, SET_DEST (pat), const0_rtx, const0_rtx,
			       GEN_INT (size), const0_rtx, const1_rtx);
      rtx_insn *mi = make_insn_raw (mova);
      INSN_LOCATION (mi) = INSN_LOCATION (node->insn);
      if (recog_memoized (mi) < 0)
	continue;
      if (d < 0)
	d = l->napb_d++;
      if (stp != size && ki == nincr)
	incrs[nincr++] = stp / size;
      l->napb++;
      node->apb = true;
      node->orig = node->insn;
      node->insn = mi;
      node->apb_size = size;
      node->apb_d = d;
      node->apb_iv = a.iv;
      node->apb_inv = a.inv;
      node->apb_inv2 = inv2;
      node->apb_off = oa;
      node->apb_step = stp;
      /* Its value reaches any consumer 5 cycles on, in any cluster.  */
      for (e2k_ms_dep &d : l->deps)
	if (d.from == i)
	  {
	    d.lat = 5;
	    d.cross = 0;
	  }
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: insn %d through array "
		 "prefetch\n", INSN_UID (node->orig));
    }
}

/* AAU stores (spec/isa/apb.md, "AAU stores") for the stores of L, a
   loop counted by %lsr, as lcc's kernels store: through a descriptor
   whose base is where the store writes in iteration 0, and a store
   index of its own, 0 on the way in, that its incr steps.  No literal
   offsets, which lcc uses: gas can't place two AAU stores' literals in
   one wide instruction by itself ("literals cannot be packed"), only
   when written with their LTS (relcc2 findings I42).  The kernel runs the last stage of each iteration once
   and the stores are there, so the index needs no correction for the
   prologue.  The store then reads no address in the kernel, and what
   only computed the addresses of movas and such stores leaves it
   (e2k_ms_mark_kdead): PolyBench's jacobi-2d, five FP operations and a
   store, on v5 at II 1 as lcc's instead of 2.  A register's elements
   of their type's alignment, stepped forward by a whole number of them
   (unlike array prefetch, a misaligned AAU store just stores, also on
   the 4C: relcc2 findings I43, as lcc's v3 code assumes); at most 16
   (%aasti0-15), with the increment registers array prefetch leaves.  STEP, IVDEF and DERIVED
   as for e2k_ms_mark_apb.  */
static void
e2k_ms_mark_staa (e2k_ms_loop *l, const HOST_WIDE_INT *step,
		  const int *ivdef, const bool *derived)
{
  l->nstaa = 0;
  l->nstaa_d = 0;
  if (!l->staa_ok || l->want_dam)
    return;
  HOST_WIDE_INT incrs[7];
  int nincr = 0;
  /* Whether a step of E elements has an increment register, ADD it.  */
  auto incr_ok = [&] (HOST_WIDE_INT e, bool add)
    {
      if (e == 1)
	return true;
      for (int k = 0; k < nincr; k++)
	if (incrs[k] == e)
	  return true;
      if (nincr == 7)
	return false;
      if (add)
	incrs[nincr++] = e;
      return true;
    };
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].apb)
      incr_ok (l->nodes[i].apb_step / l->nodes[i].apb_size, true);
  for (int i = 0; i < l->n && l->nstaa < 16; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      if (!node->store || MEM_VOLATILE_P (node->mem))
	continue;
      rtx pat = PATTERN (node->insn);
      if (GET_CODE (pat) != SET || !REG_P (SET_SRC (pat)))
	continue;
      rtx mem = SET_DEST (pat), src = SET_SRC (pat);
      machine_mode m = GET_MODE (mem);
      HOST_WIDE_INT size = GET_MODE_SIZE (m);
      if ((size != 1 && size != 2 && size != 4 && size != 8)
	  || GET_MODE (src) != m || REG_NREGS (src) != 1
	  || MEM_ALIGN (mem) < size * BITS_PER_UNIT)
	continue;
      e2k_ms_addr a = e2k_ms_decompose (mem, step);
      if (!a.ok || a.iv == INVALID_REGNUM || derived[a.iv])
	continue;
      HOST_WIDE_INT stp = step[a.iv];
      if (stp <= 0 || stp % size != 0 || stp / size > 0x7fffffff
	  || !incr_ok (stp / size, false))
	continue;
      HOST_WIDE_INT oa = a.offset + (ivdef[a.iv] < i ? stp : 0);
      if (l->napb_d + l->nstaa_d == 32)
	continue;
      rtx_insn *si = make_insn_raw (gen_e2k_staa (m, src, const0_rtx,
						  const0_rtx, const0_rtx,
						  const0_rtx));
      INSN_LOCATION (si) = INSN_LOCATION (node->insn);
      if (recog_memoized (si) < 0)
	continue;
      incr_ok (stp / size, true);
      int d = l->napb_d + l->nstaa_d++;
      node->staa = true;
      node->orig = node->insn;
      node->insn = si;
      node->apb_size = size;
      node->apb_d = d;
      node->apb_iv = a.iv;
      node->apb_inv = a.inv;
      node->apb_inv2 = INVALID_REGNUM;
      node->apb_off = oa;
      node->apb_step = stp;
      node->staa_sti = l->nstaa++;
      /* It reads its data only: the address's registers and their
	 dependences go.  */
      int nu = 0;
      for (int k = 0; k < node->nuses; k++)
	if (node->uses[k].pred
	    || refers_to_regno_p (node->uses[k].regno, PATTERN (si)))
	  node->uses[nu++] = node->uses[k];
      node->nuses = nu;
      unsigned w = 0;
      for (unsigned k = 0; k < l->deps.length (); k++)
	{
	  e2k_ms_dep dp = l->deps[k];
	  int v = l->nodes[dp.from].value;
	  if (dp.to != i || v < 0
	      || refers_to_regno_p (l->values[v].regno, PATTERN (si)))
	    l->deps[w++] = dp;
	}
      l->deps.truncate (w);
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: insn %d through the AAU\n",
		 INSN_UID (node->orig));
    }
}

/* What the kernel doesn't need to run (e2k_ms_node::kdead): nodes whose
   results only movas (for their loads in the prologue), AAU stores' addresses
   (read by no node: e2k_ms_mark_staa) and other such nodes read, and
   nothing after the loop.  An induction step that only addressed
   arrays: an ALU channel each cycle of an II 1 kernel.  */
static void
e2k_ms_mark_kdead (e2k_ms_loop *l)
{
  if (!l->napb && !l->nstaa)
    return;
  for (bool more = true; more; )
    {
      more = false;
      for (int i = 0; i < l->n; i++)
	{
	  e2k_ms_node *nd = &l->nodes[i];
	  if (nd->kdead || nd->value < 0 || nd->store || nd->pred || nd->dpred
	      || nd->apb || nd->lock || nd->chk >= 0
	      || l->values[nd->value].out_dist >= 0)
	    continue;
	  bool used = false;
	  for (int j = 0; j < l->n && !used; j++)
	    if (j != i && !l->nodes[j].kdead && !l->nodes[j].apb)
	      for (int k = 0; k < l->nodes[j].nuses; k++)
		if (!l->nodes[j].uses[k].pred
		    && l->nodes[j].uses[k].value == nd->value)
		  used = true;
	  if (used)
	    continue;
	  nd->kdead = true;
	  more = true;
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: insn %d only in the "
		     "prologue\n", INSN_UID (nd->insn));
	}
    }
}

bool
e2k_ms_why (const char *why)
{
  if (dump_file)
    fprintf (dump_file, ";; e2k_modsched: %s\n", why);
  return false;
}

/* Whether node I of L loads a stack slot that register allocation
   spilled to (no address of it is taken), which one node of L stores, a
   register set earlier in the same iteration, and no other node writes:
   then the load is a copy of the stored value, of this iteration if the
   store comes first (a reload), else of the last one (a value the loop
   carries through the slot: NPB LU's jacld keeps predictive commoning's
   u[i][j-1][k][0] in one, and the dependence through memory held the
   loop's every stage to the store's, the last).  Sets *VS to that
   value and *DS to 0 or 1.  */
static bool
e2k_ms_slot_copy (e2k_ms_loop *l, int i, int *vs, int *ds)
{
  e2k_ms_node *ld = &l->nodes[i];
  rtx pat = PATTERN (ld->insn);
  if (!e2k_ms_carry_slots || ld->store || ld->value < 0 || ld->apb
      || ld->lock || ld->chk >= 0 || GET_CODE (pat) != SET
      || !REG_P (SET_DEST (pat)) || !MEM_P (SET_SRC (pat)))
    return false;
  rtx m = SET_SRC (pat);
  tree spill = get_spill_slot_decl (false);
  if (!spill || MEM_EXPR (m) != spill || MEM_VOLATILE_P (m)
      || !MEM_OFFSET_KNOWN_P (m) || !MEM_SIZE_KNOWN_P (m))
    return false;
  int st = -1;
  for (int j = 0; j < l->n; j++)
    {
      e2k_ms_node *nd = &l->nodes[j];
      if (j == i || nd->dead || !nd->mem || !nd->store
	  || MEM_EXPR (nd->mem) != spill)
	continue;
      rtx m2 = nd->mem;
      if (!MEM_OFFSET_KNOWN_P (m2) || !MEM_SIZE_KNOWN_P (m2))
	return false;
      if (!ranges_maybe_overlap_p (MEM_OFFSET (m), MEM_SIZE (m),
				   MEM_OFFSET (m2), MEM_SIZE (m2)))
	continue;
      rtx spat = PATTERN (nd->insn);
      if (st >= 0 || GET_CODE (spat) != SET || MEM_VOLATILE_P (m2)
	  || !REG_P (SET_SRC (spat)) || GET_MODE (m2) != GET_MODE (m)
	  || !rtx_equal_p (XEXP (m2, 0), XEXP (m, 0)))
	return false;
      st = j;
    }
  if (st < 0)
    return false;
  unsigned dr = REGNO (SET_SRC (PATTERN (l->nodes[st].insn)));
  for (int k = 0; k < l->nodes[st].nuses; k++)
    {
      e2k_ms_use *u = &l->nodes[st].uses[k];
      if (!u->pred && u->regno == dr)
	{
	  if (u->value < 0 || u->dist != 0)
	    return false;
	  *vs = u->value;
	  *ds = st > i;
	  return true;
	}
    }
  return false;
}

/* A copy between registers costs nothing in the ring, where its value
   would only get another name: fold each copy into its source, of this
   iteration or the last (DS 0 or 1): what read the copy D iterations
   later reads the source D + DS iterations later (at most 2).  The
   instances from before the loop that reads then reach move too: the
   copy's instance -K is the source's -(K + DS), held by the register
   the copy's was in; not if the source's is another one.  A reload of
   a spill slot is a copy too (e2k_ms_slot_copy): of what the loop
   stored there before, the source's instance -1 the slot's (INIT_MEM)
   if that was in the last iteration.  Then drop the copies from L's
   nodes, and mark the registers they set in FOLDED.  */
static void
e2k_ms_fold_copies (e2k_ms_loop *l, bool *folded)
{
  bool any = false;
  for (int i = 0; i < l->n; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      rtx pat = PATTERN (node->insn);
      int vc = node->value;
      if (vc < 0)
	continue;
      int vs, ds;
      rtx slot = NULL_RTX;
      if (e2k_ms_slot_copy (l, i, &vs, &ds))
	slot = SET_SRC (pat);
      else if (node->nuses != 1 || !REG_P (SET_SRC (pat))
	       || GET_MODE (SET_SRC (pat)) != GET_MODE (SET_DEST (pat)))
	continue;
      else
	{
	  vs = node->uses[0].value;
	  ds = node->uses[0].dist;
	  if (vs < 0 || node->uses[0].pred)
	    continue;
	}
      if (ds > 1 || vs == vc)
	continue;
      e2k_ms_value &src = l->values[vs], &cp = l->values[vc];
      if (ds == 1 && cp.carried2)
	continue;
      bool ok = true;
      for (int j = 0; j < l->n && ok; j++)
	for (int k = 0; k < l->nodes[j].nuses; k++)
	  if (!l->nodes[j].uses[k].pred && l->nodes[j].uses[k].value == vc
	      && l->nodes[j].uses[k].dist + ds > 2)
	    ok = false;
      for (e2k_ms_out &o : l->outs)
	if (o.value == vc && o.dist + ds > 2)
	  ok = false;
      /* The copy's instances -1 and -2 become the source's -1 - DS and
	 -2 - DS.  */
      for (int k = 0; k < 2 && ok; k++)
	if (k == 0 ? cp.carried : cp.carried2)
	  {
	    int t = k + ds;
	    bool need = t == 0 ? src.carried : src.carried2;
	    if (t > 1 || (need && src.init[t] != cp.init[k]))
	      ok = false;
	  }
      /* The source's instance -1 is the register it is in, which the
	 copy read in the first iteration; or the slot the load read.  */
      if (ds == 1 && !slot && (src.init[0] != src.regno || src.init_mem))
	ok = false;
      if (ds == 1 && slot)
	{
	  if (src.init_mem
	      ? !rtx_equal_p (src.init_mem, slot) : src.init[0] != src.regno)
	    ok = false;
	  /* Nothing reads the register's instance instead.  */
	  for (int j = 0; j < l->n && ok; j++)
	    for (int k = 0; k < l->nodes[j].nuses; k++)
	      if (!l->nodes[j].uses[k].pred && l->nodes[j].uses[k].value == vs
		  && l->nodes[j].uses[k].dist > 0)
		ok = false;
	  for (e2k_ms_out &o : l->outs)
	    if (o.value == vs && o.dist > 0)
	      ok = false;
	}
      if (!ok)
	continue;
      if (ds == 1 && slot)
	src.init_mem = slot;
      for (int j = 0; j < l->n; j++)
	for (int k = 0; k < l->nodes[j].nuses; k++)
	  if (!l->nodes[j].uses[k].pred && l->nodes[j].uses[k].value == vc)
	    {
	      l->nodes[j].uses[k].value = vs;
	      l->nodes[j].uses[k].dist += ds;
	    }
      for (e2k_ms_out &o : l->outs)
	if (o.value == vc)
	  {
	    o.value = vs;
	    o.dist += ds;
	  }
      for (int k = 0; k < 2; k++)
	if (k == 0 ? cp.carried : cp.carried2)
	  {
	    if (k + ds == 0)
	      src.carried = true;
	    else
	      src.carried2 = true;
	    src.init[k + ds] = cp.init[k];
	  }
      if (cp.out_dist >= 0)
	src.out_dist = MAX (src.out_dist, cp.out_dist + ds);
      node->dead = true;
      folded[REGNO (SET_DEST (pat))] = true;
      any = true;
      if (dump_file)
	fprintf (dump_file, ";; e2k_modsched: %s insn %d folded\n",
		 slot ? "slot load" : "copy", INSN_UID (node->insn));
    }
  if (!any)
    return;
  /* What reads the source a later iteration now.  */
  for (int i = 0; i < l->n; i++)
    if (!l->nodes[i].dead)
      for (int k = 0; k < l->nodes[i].nuses; k++)
	{
	  e2k_ms_use *u = &l->nodes[i].uses[k];
	  if (u->pred || u->value < 0)
	    continue;
	  if (u->dist == 1)
	    l->values[u->value].carried = true;
	  else if (u->dist == 2)
	    l->values[u->value].carried2 = true;
	}
  for (e2k_ms_out &o : l->outs)
    if (o.dist == 1)
      l->values[o.value].carried = true;
    else if (o.dist == 2)
      l->values[o.value].carried2 = true;

  /* Renumber the nodes and values left.  */
  int nmap[E2K_MS_MAX_NODES], n = 0;
  for (int i = 0; i < l->n; i++)
    nmap[i] = l->nodes[i].dead ? -1 : n++;
  int nv = l->values.length ();
  auto_vec<int> vmap (nv);
  auto_vec<e2k_ms_value> values (nv);
  for (int v = 0; v < nv; v++)
    if (l->nodes[l->values[v].node].dead)
      vmap.quick_push (-1);
    else
      {
	vmap.quick_push (values.length ());
	e2k_ms_value val = l->values[v];
	val.node = nmap[val.node];
	values.quick_push (val);
      }
  int nh = 0;
  for (int i = 0; i < l->n; i++)
    {
      if (nmap[i] < 0)
	continue;
      if (i < l->nh)
	nh++;
      e2k_ms_node node = l->nodes[i];
      if (node.value >= 0)
	node.value = vmap[node.value];
      for (int k = 0; k < node.nuses; k++)
	if (node.uses[k].pred)
	  node.uses[k].value = nmap[node.uses[k].value];
	else if (node.uses[k].value >= 0)
	  node.uses[k].value = vmap[node.uses[k].value];
      l->nodes[nmap[i]] = node;
    }
  for (e2k_ms_out &o : l->outs)
    o.value = vmap[o.value];
  if (l->stay >= 0)
    l->stay = nmap[l->stay];
  if (l->c1 >= 0)
    l->c1 = nmap[l->c1];
  for (int &c : l->c1s)
    c = nmap[c];
  l->nh = nh;
  l->n = n;
  l->values.truncate (0);
  for (e2k_ms_value &val : values)
    l->values.safe_push (val);
}

/* The condition of a loop end "if (P op 0) goto L", possibly with a
   (use CTPR): the (op P 0) rtx in the pattern, or NULL.  */
rtx
e2k_ms_jump_cond (rtx_insn *jump)
{
  rtx pat = PATTERN (jump);
  if (GET_CODE (pat) == PARALLEL)
    pat = XVECEXP (pat, 0, 0);
  if (GET_CODE (pat) != SET || SET_DEST (pat) != pc_rtx
      || GET_CODE (SET_SRC (pat)) != IF_THEN_ELSE
      || GET_CODE (XEXP (SET_SRC (pat), 1)) != LABEL_REF
      || XEXP (SET_SRC (pat), 2) != pc_rtx)
    return NULL_RTX;
  rtx cond = XEXP (SET_SRC (pat), 0);
  if ((GET_CODE (cond) != NE && GET_CODE (cond) != EQ)
      || !REG_P (XEXP (cond, 0)) || !PRED_REGNO_P (REGNO (XEXP (cond, 0)))
      || XEXP (cond, 1) != const0_rtx)
    return NULL_RTX;
  return cond;
}

/* The instances that use what node FROM of one iteration computes, in
   DEP: bit D of DEP[N] when node N of D iterations later does (D < 32),
   through values and predicates.  */
void
e2k_ms_dependents (e2k_ms_loop *l, int from, unsigned *dep)
{
  for (int i = 0; i < l->n; i++)
    dep[i] = 0;
  dep[from] = 1;
  for (bool changed = true; changed; )
    {
      changed = false;
      for (int i = 0; i < l->n; i++)
	for (int k = 0; k < l->nodes[i].nuses; k++)
	  {
	    const e2k_ms_use &u = l->nodes[i].uses[k];
	    int m = u.pred ? u.value : u.value >= 0 ? l->values[u.value].node : -1;
	    if (m < 0)
	      continue;
	    unsigned add = (dep[m] << u.dist) & ~dep[i];
	    if (add)
	      {
		dep[i] |= add;
		changed = true;
	      }
	  }
    }
}

/* Make the load L->dam_deps name a lock load that may move above the
   stores they name, with a check load of its own (spec/isa/
   speculation.md: the check reloads into the same register, and its
   rbranch is taken, if a store touched the bytes since).  */
static bool
e2k_ms_add_dam (e2k_ms_loop *l)
{
  if (l->dam_deps.is_empty ())
    return e2k_ms_why ("no load to speculate");
  /* The compensation code reruns what depends on the load, not the
     compares of the predicates it reads, which the ring may have given
     to another compare by then (GMP's in-place mpn_bdiv_dbm1c).  */
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].dpred)
      return e2k_ms_why ("predicates and a lock load");
  int ld = l->dam_deps[0].to;
  for (e2k_ms_dep &d : l->dam_deps)
    if (d.to != ld)
      return e2k_ms_why ("more than one load to speculate");
  if (e2k_ov_mem_p (l->nodes[ld].mem))
    return e2k_ms_why ("a load of a copy for overlapping arrays");
  /* Its check would reload unconditionally, from an address valid only
     under the predicate e2k_unpredicate_loads took away.  */
  if (e2k_unpred_cond_of (l->nodes[ld].insn))
    return e2k_ms_why ("a load run without its predicate");
  e2k_ms_node *ln = &l->nodes[ld];
  rtx dest, src;
  if (l->n == E2K_MS_MAX_NODES || ln->value < 0
      || ln->nuses == E2K_MS_MAX_USES
      || !e2k_spec_load_parts (ln->insn, &dest, &src))
    return e2k_ms_why ("a load without a lock form");
  rtx lpat = gen_rtx_PARALLEL (VOIDmode,
			       gen_rtvec (2, copy_rtx (PATTERN (ln->insn)),
					  gen_rtx_UNSPEC (VOIDmode,
							  gen_rtvec (1, const0_rtx),
							  UNSPEC_LDLOCK)));
  rtx_insn *lk = make_insn_raw (lpat);
  INSN_LOCATION (lk) = INSN_LOCATION (ln->insn);
  machine_mode mode = GET_MODE (dest);
  rtx test = gen_rtx_NE (VOIDmode,
			 gen_rtx_UNSPEC (VOIDmode, gen_rtvec (1, dest),
					 UNSPEC_LDCHK),
			 const0_rtx);
  rtx_insn *ck
    = make_insn_raw (gen_rtx_SET (dest,
				  gen_rtx_IF_THEN_ELSE (mode, test,
							copy_rtx (src), dest)));
  INSN_LOCATION (ck) = INSN_LOCATION (ln->insn);
  if (recog_memoized (lk) < 0 || recog_memoized (ck) < 0)
    return e2k_ms_why ("a load without a lock form");
  ln->insn = lk;
  ln->lock = true;
  int k = l->n++;
  e2k_ms_node *kn = &l->nodes[k];
  memset (kn, 0, sizeof *kn);
  kn->insn = ck;
  kn->value = -1;
  kn->chk = ld;
  kn->mem = ln->mem;
  /* The load's address operands, then its value (last, so that an
     address register of the same number gets the address's name).  */
  kn->nuses = ln->nuses;
  memcpy (kn->uses, ln->uses, sizeof ln->uses);
  e2k_ms_use u = { REGNO (dest), ln->value, 0, false };
  kn->uses[kn->nuses++] = u;
  l->dam = ld;
  l->kchk = k;
  e2k_ms_add_dep (l, ld, k, 3, 0);
  /* A check sees a store of the cycle before (lock, store and check a
     cycle apart: spec/isa/speculation.md, "Distances").  */
  for (e2k_ms_dep &d : l->dam_deps)
    e2k_ms_add_dep (l, d.from, k, 1, d.dist);
  /* The check reads the memory again, so it too goes before the stores
     the load goes before, and before the stores of what the load
     gave.  */
  unsigned nd = l->deps.length ();
  for (unsigned q = 0; q < nd; q++)
    {
      e2k_ms_dep d = l->deps[q];
      if (d.from == ld && l->nodes[d.to].store)
	e2k_ms_add_dep (l, k, d.to, 1, d.dist);
    }
  unsigned dep[E2K_MS_MAX_NODES];
  e2k_ms_dependents (l, ld, dep);
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].store)
      for (int d = 0; d < 32; d++)
	if (dep[i] & (1u << d))
	  e2k_ms_add_dep (l, k, i, 1, d);
  if (dump_file)
    fprintf (dump_file, ";; e2k_modsched: insn %d a lock load\n",
	     INSN_UID (ln->insn));
  return true;
}

/* Whether INSN is an FP operation, which may raise an FP exception.  */
bool
e2k_fp_class_p (rtx_insn *insn)
{
  if (recog_memoized (insn) < 0)
    return false;
  switch (get_attr_type (insn))
    {
    case TYPE_FP: case TYPE_FMA: case TYPE_FFMA: case TYPE_FCVT:
    case TYPE_FDIV: case TYPE_FCMP:
      return true;
    default:
      return false;
    }
}

/* Find the nodes, values and dependences of the loop whose body is
   L->insns; EXIT is where it goes when done.  */
bool
e2k_ms_analyze (e2k_ms_loop *l, basic_block exit)
{
  basic_block bb = l->bb;
  l->n = 0;
  l->exit = exit;
  l->npred = 0;
  /* A register set under a predicate, "if (p) r = x", keeps r when p
     is false, which a renamed instance can't: it becomes "t = x" and
     the merge "r = p ? t : r", t a register the loop doesn't use and
     that is dead around it (it only names the value, which gets a ring
     name).  */
  auto_vec<rtx_insn *> body;
  l->nh = l->nh0;
  {
    HARD_REG_SET used;
    CLEAR_HARD_REG_SET (used);
    for (rtx_insn *insn : l->insns)
      e2k_note_regs (PATTERN (insn), &used);
    e2k_note_regs (PATTERN (l->jump), &used);
    bitmap lh = df_get_live_in (bb), lx = df_get_live_in (exit);
    bitmap l1 = l->x1 ? df_get_live_in (l->x1) : lx;
    unsigned next_t = 0;
    for (unsigned k = 0; k < l->insns.length (); k++)
      {
	rtx_insn *insn = l->insns[k];
	rtx pat = PATTERN (insn);
	if (GET_CODE (pat) != COND_EXEC
	    || GET_CODE (COND_EXEC_CODE (pat)) != SET
	    || !REG_P (SET_DEST (COND_EXEC_CODE (pat))))
	  {
	    body.safe_push (insn);
	    continue;
	  }
	rtx set = COND_EXEC_CODE (pat), r = SET_DEST (set);
	machine_mode m = GET_MODE (r);
	unsigned t = INVALID_REGNUM;
	for (; next_t < FIRST_PSEUDO_REGISTER && t == INVALID_REGNUM; next_t++)
	  if (GPR_REGNO_P (next_t) && !BX_REGNO_P (next_t) && !B_REGNO_P (next_t)
	      && !fixed_regs[next_t] && !TEST_HARD_REG_BIT (used, next_t)
	      && !bitmap_bit_p (lh, next_t) && !bitmap_bit_p (lx, next_t)
	      && !bitmap_bit_p (l1, next_t)
	      && targetm.hard_regno_mode_ok (next_t, m))
	    t = next_t;
	if (t == INVALID_REGNUM || !REG_P (r) || REG_NREGS (r) != 1
	    || (m != SImode && m != DImode && m != SFmode && m != DFmode))
	  {
	    body.safe_push (insn);
	    continue;
	  }
	rtx tr = gen_rtx_REG (m, t);
	rtx_insn *a = make_insn_raw (gen_rtx_SET (tr, copy_rtx (SET_SRC (set))));
	rtx test = copy_rtx (COND_EXEC_TEST (pat));
	rtx_insn *b = make_insn_raw (gen_rtx_SET (r, gen_rtx_IF_THEN_ELSE
						 (m, test, tr, r)));
	INSN_LOCATION (a) = INSN_LOCATION (b) = INSN_LOCATION (insn);
	if (recog_memoized (a) < 0 || recog_memoized (b) < 0)
	  {
	    body.safe_push (insn);
	    continue;
	  }
	body.safe_push (a);
	body.safe_push (b);
	if ((int) k < l->nh0)
	  l->nh++;
      }
  }
  for (rtx_insn *insn : body)
    {
      /* A pipelined loop runs every operation but the stores for
	 iterations past the end too, speculatively; an FP one would then
	 give a diagnostic value where the flags are clear
	 (spec/isa/speculation.md, "What lcc speculates").  */
      if (!e2k_spec_fp && e2k_fp_class_p (insn))
	return e2k_ms_why ("an FP operation would run speculatively "
			   "(-mno-spec-fp)");
      if (l->n == E2K_MS_MAX_NODES)
	{
	  if (dump_file)
	    fprintf (dump_file, ";; e2k_modsched: more than %d operations\n",
		     E2K_MS_MAX_NODES);
	  return false;
	}
      if (!e2k_ms_insn_ok (insn, l->wl))
	{
	  if (dump_file)
	    {
	      fprintf (dump_file, ";; e2k_modsched: can't pipeline\n");
	      print_rtl_single (dump_file, insn);
	    }
	  return false;
	}
      e2k_ms_node *node = &l->nodes[l->n++];
      memset (node, 0, sizeof *node);
      node->insn = insn;
      node->value = -1;
      node->chk = -1;
      rtx pat = e2k_ms_set (PATTERN (insn));
      rtx dest = SET_DEST (pat);
      if (GET_CODE (PATTERN (insn)) == COND_EXEC
	  && !e2k_ms_note_uses (node, COND_EXEC_TEST (PATTERN (insn))))
	return e2k_ms_why ("too many registers");
      if (MEM_P (dest))
	{
	  node->store = true;
	  node->mem = dest;
	  if (!e2k_ms_note_uses (node, XEXP (dest, 0)))
	    return e2k_ms_why ("too many registers");
	}
      else
	node->pred = PRED_REGNO_P (REGNO (dest));
      if (!e2k_ms_note_uses (node, SET_SRC (pat)))
	return e2k_ms_why ("too many registers");
      subrtx_iterator::array_type array;
      FOR_EACH_SUBRTX (iter, array, SET_SRC (pat), NONCONST)
	if (MEM_P (*iter))
	  node->mem = const_cast<rtx> (*iter);
    }
  if (l->n < 2)
    return e2k_ms_why ("fewer than 2 insns");

  /* Values: one per definition of a register (predicates are not
     values: they stay in their registers).  CUR[r] is the value of r so
     far in this iteration, LAST[r] the body's last, LASTH[r] the last of
     a two-block loop's first block.  */
  int cur[FIRST_PSEUDO_REGISTER], last[FIRST_PSEUDO_REGISTER];
  int lasth[FIRST_PSEUDO_REGISTER], pcur[FIRST_PSEUDO_REGISTER];
  for (int r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    cur[r] = last[r] = lasth[r] = pcur[r] = -1;
  bitmap live_head = df_get_live_in (bb);
  bitmap live_exit = df_get_live_in (exit);
  bitmap live_x1 = l->x1 ? df_get_live_in (l->x1) : live_exit;
  for (int i = 0; i < l->n; i++)
    {
      rtx dest = SET_DEST (e2k_ms_set (PATTERN (l->nodes[i].insn)));
      if (!REG_P (dest))
	continue;
      unsigned r = REGNO (dest);
      if (l->nodes[i].pred)
	{
	  /* Set once, and not needed before or after the loop.  */
	  for (int j = 0; j < i; j++)
	    if (l->nodes[j].pred
		&& REGNO (SET_DEST (e2k_ms_set (PATTERN (l->nodes[j].insn))))
		   == r)
	      return e2k_ms_why ("a predicate set twice");
	  if (bitmap_bit_p (live_head, r) || bitmap_bit_p (live_exit, r)
	      || bitmap_bit_p (live_x1, r))
	    return e2k_ms_why ("a predicate live around the loop");
	  continue;
	}
      e2k_ms_value v;
      memset (&v, 0, sizeof v);
      v.node = i;
      v.regno = r;
      v.init[0] = r;
      v.init[1] = INVALID_REGNUM;
      v.mode = GET_MODE (dest);
      v.out_dist = -1;
      l->nodes[i].value = l->values.length ();
      last[r] = l->values.length ();
      if (i < l->nh)
	lasth[r] = l->values.length ();
      l->values.safe_push (v);
    }
  /* setbn renames %b[0..7] for the loop, but the ring lies below the
     registers they name outside it: a value there may pass through the
     loop, but the loop can't read one in or leave one behind.  */
  for (unsigned r = B0_REGNUM; r < B0_REGNUM + 8; r++)
    if (last[r] >= 0
	&& (bitmap_bit_p (live_head, r) || bitmap_bit_p (live_exit, r)
	    || bitmap_bit_p (live_x1, r)))
      {
	if (dump_file)
	  fprintf (dump_file, ";; e2k_modsched: %s live%s%s%s\n",
		   reg_names[r], bitmap_bit_p (live_head, r) ? " in" : "",
		   bitmap_bit_p (live_exit, r) ? " out" : "",
		   bitmap_bit_p (live_x1, r) ? " out of the first block" : "");
	return e2k_ms_why ("%b[0..7] live into or after the loop");
      }
  for (int i = 0; i < l->n; i++)
    {
      e2k_ms_node *node = &l->nodes[i];
      for (int k = 0; k < node->nuses; k++)
	{
	  e2k_ms_use *u = &node->uses[k];
	  if (PRED_REGNO_P (u->regno))
	    {
	      /* The exit test, merges and predicated stores read
		 predicates, set before them in the same iteration.  */
	      if (pcur[u->regno] < 0)
		{
		  if (dump_file)
		    print_rtl_single (dump_file, node->insn);
		  return e2k_ms_why ("a predicate from outside the iteration");
		}
	      u->pred = true;
	      u->value = pcur[u->regno];
	      continue;
	    }
	  if (cur[u->regno] >= 0)
	    u->value = cur[u->regno];
	  else if (last[u->regno] >= 0)
	    {
	      u->value = last[u->regno];
	      u->dist = 1;
	      l->values[u->value].carried = true;
	    }
	  /* setbn renames %b[0..7] for the loop: they can only hold
	     values local to an iteration (no copies in or out either:
	     live_head and live_exit above), or an invariant the kernel
	     reads from a register of its own (L->binv).  */
	  if (B_REGNO_P (u->regno) && u->value < 0
	      && !(l->binv & (1u << (u->regno - B0_REGNUM))))
	    return e2k_ms_why ("%b[0..7] invariant in the loop");
	}
      if (node->value >= 0)
	cur[l->values[node->value].regno] = node->value;
      if (node->pred)
	pcur[REGNO (SET_DEST (e2k_ms_set (PATTERN (node->insn))))] = i;
    }

  /* Compares that merges and predicated stores read are data: scheduled
     as any operation, their predicates named in the ring
     (e2k_ms_assign_pnames).  The exit test reads only its own.  */
  for (int i = 0; i < l->n; i++)
    {
      enum attr_type t = get_attr_type (l->nodes[i].insn);
      if (t == TYPE_CMP || t == TYPE_FCMP || t == TYPE_CCTOP
	  || t == TYPE_PLOG)
	continue;
      for (int k = 0; k < l->nodes[i].nuses; k++)
	if (l->nodes[i].uses[k].pred)
	  {
	    int c = l->nodes[i].uses[k].value;
	    enum attr_type tc = get_attr_type (l->nodes[c].insn);
	    if (tc != TYPE_CMP && tc != TYPE_FCMP && tc != TYPE_CCTOP)
	      return e2k_ms_why ("a merge or store on a landp");
	    l->nodes[c].dpred = true;
	  }
    }
  for (int i = 0; i < l->n; i++)
    {
      for (int k = 0; k < l->nodes[i].nuses; k++)
	if (l->nodes[i].uses[k].pred
	    && l->nodes[l->nodes[i].uses[k].value].dpred
	    && get_attr_type (l->nodes[i].insn) == TYPE_PLOG)
	  return e2k_ms_why ("a predicate both data and exit test");
      if (l->nodes[i].dpred)
	l->nodes[i].pred = false;
      else if (l->nodes[i].pred && !l->wl)
	return e2k_ms_why ("a predicate nothing reads");
    }

  /* A while loop's exit test.  */
  if (l->wl)
    {
      rtx pstay = l->pstay ? l->pstay : XEXP (e2k_ms_jump_cond (l->jump), 0);
      l->stay = pcur[REGNO (pstay)];
      if (l->stay < 0)
	return e2k_ms_why ("the loop end's predicate is not set in the loop");
      if (l->p1)
	{
	  l->c1 = pcur[REGNO (l->p1)];
	  l->c1s.truncate (0);
	  if (l->c1 < 0 || l->c1 >= l->nh)
	    return e2k_ms_why ("the first block's exit test");
	  /* The compares and the landps over them, in the first block.  */
	  bool in[E2K_MS_MAX_NODES] = { false };
	  auto_vec<int, 8> work;
	  work.safe_push (l->c1);
	  while (!work.is_empty ())
	    {
	      int i = work.pop ();
	      if (in[i])
		continue;
	      in[i] = true;
	      enum attr_type t = get_attr_type (l->nodes[i].insn);
	      if (i >= l->nh
		  || (t != TYPE_CMP && t != TYPE_FCMP && t != TYPE_CCTOP
		      && t != TYPE_PLOG))
		return e2k_ms_why ("the first block's exit test");
	      for (int k = 0; k < l->nodes[i].nuses; k++)
		if (l->nodes[i].uses[k].pred)
		  {
		    if (t != TYPE_PLOG)
		      return e2k_ms_why ("the first block's exit test");
		    work.safe_push (l->nodes[i].uses[k].value);
		  }
	    }
	  for (int i = 0; i < l->nh; i++)
	    if (in[i])
	      {
		if (l->nodes[i].dpred)
		  return e2k_ms_why ("a predicate both data and exit test");
		l->c1s.safe_push (i);
	      }
	}
      for (int i = 0; i < l->n; i++)
	for (int k = 0; k < l->nodes[i].nuses; k++)
	  if (l->nodes[i].uses[k].pred && l->nodes[i].uses[k].value == l->stay)
	    return e2k_ms_why ("the loop end's predicate read in the loop");
    }

  /* Registers read after the loop.  */
  auto add_out = [&] (unsigned r, int v, int dist, bool hend)
    {
      e2k_ms_out o = { r, l->values[v].mode, v, dist, hend };
      l->outs.safe_push (o);
      l->values[v].out_dist = MAX (l->values[v].out_dist, dist);
      if (dist > 0)
	l->values[v].carried = true;
    };
  for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    if (last[r] >= 0)
      {
	bool at2 = (bitmap_bit_p (live_exit, r)
		    || TEST_HARD_REG_BIT (e2k_ms_live_out_extra, r));
	/* With one exit, a register e2k_ms_move_b gave a %b[] value is
	   live there too (its copy back is still on the edge).  */
	bool at1 = (l->c1 >= 0
		    && (bitmap_bit_p (live_x1, r)
			|| (!l->x1
			    && TEST_HARD_REG_BIT (e2k_ms_live_out_extra, r))));
	if (at2)
	  add_out (r, last[r], 0, false);
	/* Left by the first block's exit, the register holds its value
	   at the end of that block: set there, or else from the last
	   iteration.  */
	if (at1 && (l->x1 || lasth[r] != last[r]))
	  add_out (r, lasth[r] >= 0 ? lasth[r] : last[r],
		   lasth[r] >= 0 ? 0 : 1, true);
      }
  /* That exit's test runs again after the loop.  */
  for (int c : l->c1s)
    for (int k = 0; k < l->nodes[c].nuses; k++)
      {
	e2k_ms_use *u = &l->nodes[c].uses[k];
	if (u->value >= 0 && !u->pred)
	  l->values[u->value].out_dist
	    = MAX (l->values[u->value].out_dist, u->dist);
      }

  /* How many times each register is set (before folding).  */
  int ndefs[FIRST_PSEUDO_REGISTER];
  bool folded[FIRST_PSEUDO_REGISTER];
  for (int r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    {
      ndefs[r] = 0;
      folded[r] = false;
    }
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].value >= 0)
      ndefs[l->values[l->nodes[i].value].regno]++;
  e2k_ms_fold_copies (l, folded);

  /* Register dependences.  */
  for (int i = 0; i < l->n; i++)
    for (int k = 0; k < l->nodes[i].nuses; k++)
      {
	e2k_ms_use *u = &l->nodes[i].uses[k];
	if (u->pred)
	  {
	    /* Compare -> landp 1 (spec/isa/timing.md); to a merge or a
	       predicated store as the scheduler has it.  */
	    rtx_insn *def = l->nodes[u->value].insn;
	    e2k_ms_add_dep (l, u->value, i,
			    get_attr_type (l->nodes[i].insn) == TYPE_PLOG
			    ? 1 : MAX (insn_latency (def, l->nodes[i].insn), 1),
			    0);
	    continue;
	  }
	if (u->value < 0)
	  continue;
	rtx_insn *def = l->nodes[l->values[u->value].node].insn;
	/* gas picks the channels, so a value may cross between ALC0-2 and
	   ALC3-5, which costs 1 cycle more (2 for an FP result;
	   spec/isa/timing.md).  In the kernel a late operand stalls every
	   iteration, while slack only adds stages.  */
	enum attr_type dt = get_attr_type (def);
	int cross = (dt == TYPE_FP || dt == TYPE_FMA || dt == TYPE_FFMA
		     || dt == TYPE_FCVT || dt == TYPE_FDIV
		     || dt == TYPE_MUL ? 2 : 1);
	/* A v6 load reaches either cluster at its 5.  */
	if (E2K_LAT6
	    && (dt == TYPE_LOAD || dt == TYPE_LDLOCK || dt == TYPE_LDCHK))
	  cross = 0;
	int lat = MAX (insn_latency (def, l->nodes[i].insn), 1);
	/* A packed result costs 4 in the other cluster, as it does to an
	   integer operation (which the bypass gives).  */
	if (e2k_packed_type_p (dt))
	  cross = MAX (4 - lat, 0);
	/* A flag result reaches a cctop in its own channel at 2, anything
	   else at 4 (the multiplies' at 6); the two can share a channel
	   only in different kernel rows, so count the 2 as a crossing,
	   which a recurrence drops.  */
	if (dt == TYPE_FLAG || dt == TYPE_FLAGMUL)
	  cross = MAX (insn_default_latency (def) - lat, 0);
	/* An operation that uses its own last result stays in its
	   channel.  */
	if (def == l->nodes[i].insn)
	  cross = 0;
	e2k_ms_add_dep (l, l->values[u->value].node, i, lat + cross,
			u->dist, cross);
      }

  /* Induction registers: defined once, as r = r + C, and carried.  A
     register a folded copy set varies.  */
  HOST_WIDE_INT step[FIRST_PSEUDO_REGISTER];
  int ivdef[FIRST_PSEUDO_REGISTER];
  for (unsigned r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    {
      step[r] = folded[r] ? HOST_WIDE_INT_MIN : 0;
      ivdef[r] = -1;
    }
  for (int i = 0; i < l->n; i++)
    if (l->nodes[i].value >= 0)
      {
	unsigned r = l->values[l->nodes[i].value].regno;
	rtx src = SET_SRC (PATTERN (l->nodes[i].insn));
	/* r = r + C in 32 bits, extended (an unsigned counter under dbl):
	   as for the registers derived below, a wrap is no nearer.  */
	if ((GET_CODE (src) == ZERO_EXTEND || GET_CODE (src) == SIGN_EXTEND)
	    && GET_CODE (XEXP (src, 0)) == PLUS)
	  src = XEXP (src, 0);
	if (step[r] == 0 && ivdef[r] < 0 && ndefs[r] == 1
	    && GET_CODE (src) == PLUS && REG_P (XEXP (src, 0))
	    && REGNO (XEXP (src, 0)) == r && CONST_INT_P (XEXP (src, 1))
	    && INTVAL (XEXP (src, 1)) != 0)
	  {
	    step[r] = INTVAL (XEXP (src, 1));
	    ivdef[r] = i;
	  }
	else
	  step[r] = HOST_WIDE_INT_MIN;
      }
  bool derived[FIRST_PSEUDO_REGISTER] = { false };
  e2k_ms_derived dv_s;
  memset (&dv_s, 0, sizeof dv_s);
  e2k_ms_derived *dv = &dv_s;
  /* Registers computed once from an induction register X: X + INV, the
     same in 32 bits zero-extended (dbl, or a zero extension of it), X * C
     and X << C step by a constant too.  A 32-bit sum that wraps puts the
     address about 2^32 elements away, never as near as another
     iteration's of the few in flight: for the dependences between
     iterations, the step holds (xz's opts[cur + len] in its trailing
     array, which ivopts can't make an induction variable).  After
     register allocation one register may hold several values of the
     body (NPB SP's compute_rhs: an address, then sums of doubles): the
     one computed so will do when every address through the register,
     and every register derived from it, reads it, from the node after
     its def to DEND[r], the register's next def (or the end).  */
  int dend[FIRST_PSEUDO_REGISTER];
  for (int r = 0; r < FIRST_PSEUDO_REGISTER; r++)
    dend[r] = l->n;
  for (bool more = true; more; )
    {
      more = false;
      for (int i = 0; i < l->n; i++)
	{
	  if (l->nodes[i].value < 0)
	    continue;
	  unsigned r = l->values[l->nodes[i].value].regno;
	  if (step[r] != HOST_WIDE_INT_MIN || folded[r] || ivdef[r] >= 0)
	    continue;
	  rtx src = SET_SRC (PATTERN (l->nodes[i].insn));
	  bool wide = GET_MODE (SET_DEST (PATTERN (l->nodes[i].insn))) == DImode;
	  if (GET_CODE (src) == ZERO_EXTEND || GET_CODE (src) == SIGN_EXTEND)
	    src = XEXP (src, 0);
	  else if (!wide && !e2k_dbl_p ())
	    continue;
	  rtx x = NULL_RTX;
	  HOST_WIDE_INT mul = 1;
	  if (GET_CODE (src) == PLUS && REG_P (XEXP (src, 0))
	      && (CONST_INT_P (XEXP (src, 1))
		  || (REG_P (XEXP (src, 1)) && step[REGNO (XEXP (src, 1))] == 0)))
	    x = XEXP (src, 0);
	  else if (GET_CODE (src) == PLUS && REG_P (XEXP (src, 1))
		   && REG_P (XEXP (src, 0)) && step[REGNO (XEXP (src, 0))] == 0)
	    x = XEXP (src, 1);
	  else if (GET_CODE (src) == MULT && REG_P (XEXP (src, 0))
		   && CONST_INT_P (XEXP (src, 1))
		   && IN_RANGE (INTVAL (XEXP (src, 1)), -4096, 4096))
	    x = XEXP (src, 0), mul = INTVAL (XEXP (src, 1));
	  else if (GET_CODE (src) == ASHIFT && REG_P (XEXP (src, 0))
		   && CONST_INT_P (XEXP (src, 1))
		   && IN_RANGE (INTVAL (XEXP (src, 1)), 0, 12))
	    x = XEXP (src, 0), mul = HOST_WIDE_INT_1 << INTVAL (XEXP (src, 1));
	  else if (REG_P (src))
	    x = src;
	  if (!x || REGNO (x) == r)
	    continue;
	  unsigned xr = REGNO (x);
	  if (ndefs[xr] > 1 && (i <= ivdef[xr] || i > dend[xr]))
	    continue;
	  int end = l->n;
	  bool before = false;
	  if (ndefs[r] != 1)
	    {
	      rtx rr = gen_rtx_REG (DImode, r);
	      for (int k = i + 1; k < l->n && end == l->n; k++)
		if (reg_set_p (rr, l->nodes[k].insn))
		  end = k;
	      for (int k = 0; k < l->n && !before; k++)
		if (l->nodes[k].mem
		    && reg_mentioned_p (rr, XEXP (l->nodes[k].mem, 0)))
		  before = k <= i || k > end;
	    }
	  else
	    /* Every use after the def: an earlier one would read the last
	       iteration's, in iteration 0 whatever came in.  */
	    for (int k = 0; k <= i && !before; k++)
	      for (int u = 0; u < l->nodes[k].nuses; u++)
		if (l->nodes[k].uses[u].regno == r && !l->nodes[k].uses[u].pred)
		  before = true;
	  if (before)
	    continue;
	  HOST_WIDE_INT sx = step[REGNO (x)];
	  if (sx == 0 || sx == HOST_WIDE_INT_MIN || mul == 0
	      || !IN_RANGE (sx, -65536, 65536))
	    continue;
	  step[r] = sx * mul;
	  ivdef[r] = i;
	  dend[r] = end;
	  derived[r] = true;
	  more = true;
	  /* X + INV + C in 64 bits, for array prefetch.  */
	  rtx full = SET_SRC (PATTERN (l->nodes[i].insn));
	  if (mul == 1 && wide && full == src)
	    {
	      dv->ok[r] = true;
	      dv->x[r] = REGNO (x);
	      dv->inv[r] = INVALID_REGNUM;
	      dv->c[r] = 0;
	      if (GET_CODE (src) == PLUS)
		{
		  rtx o = XEXP (src, 0) == x ? XEXP (src, 1) : XEXP (src, 0);
		  if (CONST_INT_P (o))
		    dv->c[r] = INTVAL (o);
		  else
		    dv->inv[r] = REGNO (o);
		}
	    }
	}
    }
  CLEAR_HARD_REG_SET (l->fix_free);
  for (unsigned r = 16; r < R0_REGNUM + 64; r++)
    if (!fixed_regs[r] && !bitmap_bit_p (live_head, r)
	&& !bitmap_bit_p (live_exit, r) && !bitmap_bit_p (live_x1, r))
      SET_HARD_REG_BIT (l->fix_free, r);
  for (int i = 0; i < l->n; i++)
    for (int k = 0; k < l->nodes[i].nuses; k++)
      if (!l->nodes[i].uses[k].pred && l->nodes[i].uses[k].value < 0)
	CLEAR_HARD_REG_BIT (l->fix_free, l->nodes[i].uses[k].regno);
  for (int k = 0; k < 8; k++)
    if (l->binv & (1u << k))
      {
	unsigned g = INVALID_REGNUM;
	for (int pass = 0; pass < 2 && g == INVALID_REGNUM; pass++)
	  for (unsigned r = 16; r < R0_REGNUM + 64 && g == INVALID_REGNUM; r++)
	    if (TEST_HARD_REG_BIT (l->fix_free, r) && r != l->apb_tmp
		&& (pass || df_regs_ever_live_p (r)))
	      g = r;
	if (g == INVALID_REGNUM)
	  return e2k_ms_why ("no free register for a %b[] invariant");
	CLEAR_HARD_REG_BIT (l->fix_free, g);
	l->bmap[k] = g;
	if (dump_file)
	  fprintf (dump_file, ";; e2k_modsched: loop bb %d: invariant %%b[%d] "
		   "read from %s\n", l->bb->index, k, reg_names[g]);
      }
  e2k_ms_mark_apb (l, step, ivdef, derived, dv);
  e2k_ms_mark_staa (l, step, ivdef, derived);
  e2k_ms_mem_deps (l, step, ivdef, derived, dv);
  if (l->want_dam && !e2k_ms_add_dam (l))
    return false;
  e2k_ms_mark_kdead (l);
  return true;
}
