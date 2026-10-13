/* Versioning for aliasing for the Elbrus (E2K) port (GIMPLE
   passes): a copy of a loop or block whose memory accesses may overlap,
   run when a test finds they don't, so that the pipeliner and the
   scheduler may reorder them.
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
#include "tree-vectorizer.h"

/* This file should be included last.  */
#include "e2k-internal.h"

/* ------------------------------------------------------------------ */
/* Loop versioning for aliasing                                        */
/* ------------------------------------------------------------------ */

/* lcc runs a loop whose arrays may overlap in two versions: a test of
   the address ranges picks a copy that may assume they don't (seen in
   its daxpy: the disjoint copy is a one-instruction pipelined loop).
   This GIMPLE pass, after the vectorizer (and again after complete
   unrolling, for the loops that it makes innermost), does the same for
   innermost counted loops without calls, with GCC's runtime alias
   checks (as loop distribution uses them).  In the disjoint copy, every memory
   reference gets a base in a new dependence clique, one per base
   address, as restrict would give: references with the same base keep
   the same base number and so claim nothing about each other, and a
   pair with different bases either was proved independent or is
   covered by the test.  Alias analysis in RTL, the scheduler (and its
   data speculation) and the modulo scheduler then see the copy's
   arrays as disjoint.  */

/* If NITERS is an unsigned X / K (converted to sizetype) and STEP a
   multiple of K, return STEP / K and set *X to X in sizetype; else 0.
   (STEP / K) * X exceeds STEP * (X / K) by (STEP / K) * (X % K), less
   than one step, so a segment built from it still covers every access,
   without the divide (zlib's inflate_fast: "len -= 3" loops, niters
   (len - 3) / 3, whose umulx chain made the check 20 cycles).  */
static HOST_WIDE_INT
e2k_av_undivided (tree niters, HOST_WIDE_INT step, tree *x)
{
  tree q = niters;
  if (CONVERT_EXPR_P (q))
    q = TREE_OPERAND (q, 0);
  if ((TREE_CODE (q) != TRUNC_DIV_EXPR && TREE_CODE (q) != EXACT_DIV_EXPR)
      || !INTEGRAL_TYPE_P (TREE_TYPE (q))
      || !TYPE_UNSIGNED (TREE_TYPE (q))
      || TYPE_PRECISION (TREE_TYPE (q)) > TYPE_PRECISION (sizetype)
      || !tree_fits_uhwi_p (TREE_OPERAND (q, 1)))
    return 0;
  unsigned HOST_WIDE_INT k = tree_to_uhwi (TREE_OPERAND (q, 1));
  if (k < 2 || k > (unsigned HOST_WIDE_INT) HOST_WIDE_INT_MAX
      || absu_hwi (step) % k != 0)
    return 0;
  HOST_WIDE_INT f = step / (HOST_WIDE_INT) k;
  /* F * X can wrap only for an X as wide as sizetype (and could for a
     32-bit X only with |F| >= 2^32, which no access step reaches).  */
  if (TYPE_PRECISION (TREE_TYPE (q)) == TYPE_PRECISION (sizetype)
      && f != 1 && f != -1)
    return 0;
  *x = fold_convert (sizetype, TREE_OPERAND (q, 0));
  return f;
}

/* Bytes from the first to the last access of DR over NITERS + 1
   iterations, as tree-loop-distribution.cc computes them; up to one
   step more when NITERS is a division (e2k_av_undivided).  */
static tree
e2k_av_segment (class loop *loop, data_reference *dr, tree niters)
{
  bool last = dominated_by_p (CDI_DOMINATORS, single_exit (loop)->src,
			      gimple_bb (DR_STMT (dr)));
  tree step = fold_convert (sizetype, DR_STEP (dr));
  tree x = NULL_TREE;
  HOST_WIDE_INT f = (tree_fits_shwi_p (DR_STEP (dr))
		     ? e2k_av_undivided (niters, tree_to_shwi (DR_STEP (dr)),
					 &x)
		     : 0);
  if (f)
    {
      tree seg = size_binop (MULT_EXPR, size_int (f), x);
      return last ? seg : size_binop (MINUS_EXPR, seg, step);
    }
  if (last)
    niters = size_binop (PLUS_EXPR, niters, size_one_node);
  niters = size_binop (MINUS_EXPR, niters, size_one_node);
  return size_binop (MULT_EXPR, step, niters);
}

/* The MEM_REF or TARGET_MEM_REF through a pointer that DR accesses, or
   NULL.  */
static tree
e2k_av_base_ref (data_reference *dr)
{
  tree base = get_base_address (DR_REF (dr));
  if (base
      && (TREE_CODE (base) == MEM_REF || TREE_CODE (base) == TARGET_MEM_REF)
      && TREE_CODE (TREE_OPERAND (base, 0)) == SSA_NAME)
    return base;
  return NULL_TREE;
}

/* The slot of DR's reference that holds its base, an array (or a
   structure) of static storage the function names directly, or NULL.
   Reached through MEM[&decl], which GCC doesn't fold back into the decl
   while it carries a dependence clique, such a reference can take one:
   NPB SP's lhs, rhs and u are global arrays it updates in place, plane
   i from planes i + 1 and i + 2.  A local array too once its address
   is taken anyway: no pointer reaches one that isn't, but the
   vectorizer's pointers to it make it addressable, and then every
   pointer of unknown target may alias it (NPB MG's resid, whose u1 and
   u2 the vector loop reads through pointers: the scalar fallback loop's
   store through r, of a pointer the vectorizer's runtime check made
   without points-to information, was tied to their loads).  */
static tree *
e2k_av_decl_slot (data_reference *dr)
{
  tree t = DR_REF (dr), *slot = NULL;
  while (handled_component_p (t))
    {
      slot = &TREE_OPERAND (t, 0);
      t = *slot;
    }
  /* Already MEM[&decl] (an earlier instance of the pass, or a loop
     versioned before its inner loops were unrolled).  */
  if (slot && TREE_CODE (t) == MEM_REF
      && TREE_CODE (TREE_OPERAND (t, 0)) == ADDR_EXPR
      && integer_zerop (TREE_OPERAND (t, 1)))
    t = TREE_OPERAND (TREE_OPERAND (t, 0), 0);
  if (!slot || !VAR_P (t) || (!is_global_var (t) && !TREE_ADDRESSABLE (t))
      || TREE_THIS_VOLATILE (t) || DECL_HARD_REGISTER (t)
      || DECL_THREAD_LOCAL_P (t))
    return NULL;
  return slot;
}

/* Whether array references A and B, through one object with the same
   array types, never touch the same element in LOOP: in some dimension
   both indices are invariant in it and differ by a constant (NPB SP's
   "rhs[m][i][j][k]" against "rhs[m][i1][j][k]", i1 = i + 1 set outside
   the loop, which the dependence test, reading the loop alone, takes for
   two unrelated values).  Other dimensions can't make up the difference
   when the indices stay in bounds, as the dependence test assumes.  */
static bool
e2k_av_apart_p (class loop *loop, tree a, tree b,
		hash_map<tree, name_expansion *> **cache)
{
  bool apart = false;
  while (TREE_CODE (a) == ARRAY_REF && TREE_CODE (b) == ARRAY_REF)
    {
      tree ia = TREE_OPERAND (a, 1), ib = TREE_OPERAND (b, 1);
      tree type = TREE_TYPE (ia);
      if (!types_compatible_p (TREE_TYPE (TREE_OPERAND (a, 0)),
			       TREE_TYPE (TREE_OPERAND (b, 0))))
	return false;
      if (!apart && INTEGRAL_TYPE_P (type)
	  && types_compatible_p (type, TREE_TYPE (ib))
	  && expr_invariant_in_loop_p (loop, ia)
	  && expr_invariant_in_loop_p (loop, ib))
	{
	  aff_tree fa, fb;
	  tree_to_aff_combination_expand (ia, type, &fa, cache);
	  tree_to_aff_combination_expand (ib, type, &fb, cache);
	  aff_combination_scale (&fb, -1);
	  aff_combination_add (&fa, &fb);
	  apart = fa.n == 0 && !fa.rest && maybe_ne (fa.offset, 0);
	}
      a = TREE_OPERAND (a, 0);
      b = TREE_OPERAND (b, 0);
    }
  /* MEM[&decl] as an earlier instance of the pass left it: its clique
     and base keep operand_equal_p from seeing the same object.  */
  auto obj = [] (tree t)
    {
      if (TREE_CODE (t) == MEM_REF
	  && TREE_CODE (TREE_OPERAND (t, 0)) == ADDR_EXPR
	  && integer_zerop (TREE_OPERAND (t, 1)))
	return TREE_OPERAND (TREE_OPERAND (t, 0), 0);
      return t;
    };
  return apart && operand_equal_p (obj (a), obj (b), 0);
}

/* Whether data references A and B, through one base address and offset
   with one constant step, a constant distance apart, cover byte ranges
   in LOOP that don't meet, at most its iteration bound plus one
   iterations each.  The vectorizer's references to a misaligned element
   carry its aligned part in their base object (NPB SP's back
   substitution, "rhs[m][i][j][k]" stored against "rhs[m][i1][j][k]" and
   "rhs[m][i2][j][k]", planes 33,800 bytes apart, read at offsets 8,
   33,808 and 67,608 from one pointer), so the dependence test gives up
   on them, and they lost the subgroups their scalar loop gets.  */
static bool
e2k_av_segments_apart_p (class loop *loop, data_reference *a,
			 data_reference *b)
{
  widest_int bound;
  if (!DR_BASE_ADDRESS (a) || !DR_BASE_ADDRESS (b)
      || !operand_equal_p (DR_BASE_ADDRESS (a), DR_BASE_ADDRESS (b), 0)
      || !operand_equal_p (DR_OFFSET (a), DR_OFFSET (b), 0)
      || TREE_CODE (DR_STEP (a)) != INTEGER_CST
      || !tree_int_cst_equal (DR_STEP (a), DR_STEP (b))
      || TREE_CODE (DR_INIT (a)) != INTEGER_CST
      || TREE_CODE (DR_INIT (b)) != INTEGER_CST
      || !tree_fits_uhwi_p (TYPE_SIZE_UNIT (TREE_TYPE (DR_REF (a))))
      || !tree_fits_uhwi_p (TYPE_SIZE_UNIT (TREE_TYPE (DR_REF (b))))
      || !max_loop_iterations (loop, &bound))
    return false;
  /* The bytes each covers, from its first iteration's to its last's.  */
  widest_int span = wi::abs (wi::to_widest (DR_STEP (a))) * bound;
  auto range = [&] (data_reference *d, widest_int *lo, widest_int *hi)
    {
      *lo = wi::to_widest (DR_INIT (d));
      if (tree_int_cst_sgn (DR_STEP (d)) < 0)
	*lo -= span;
      *hi = *lo + span
	    + tree_to_uhwi (TYPE_SIZE_UNIT (TREE_TYPE (DR_REF (d))));
    };
  widest_int la, ha, lb, hb;
  range (a, &la, &ha);
  range (b, &lb, &hb);
  return wi::les_p (ha, lb) || wi::les_p (hb, la);
}

/* From tree-ssa-loop-split.cc.  */
extern void patch_loop_exit (class loop *, tree_code, tree, tree, bool);
extern bool easy_exit_values (class loop *);
extern void connect_loop_phis (class loop *, class loop *, edge);
extern edge connect_loops (class loop *, class loop *);

/* e2k_av_forward's select ties each iteration to the last one's store
   (floyd-warshall at II 5, against lcc's 3 with speculative loads),
   although the store writes the element at most once: split LOOP after
   the iteration whose store address SA is the element's, LA.  The first
   part runs through that iteration with PHI, the element's register,
   left at its value before the loop; the second, from the first's exit
   values, which hold what that store wrote, keeps that value.  Neither
   part carries the element any more.  Like GCC's loop splitting
   (-fsplit-loops, tree-ssa-loop-split.cc), whose pieces this uses, the
   copy follows the loop and runs when the first part stops early; its
   iterations are counted by the IV of the exit test.  Returns the
   second part, or NULL.  */
static class loop *
e2k_av_split_why (class loop *loop, const char *why)
{
  if (dump_file)
    fprintf (dump_file, "e2k: loop %d not split: %s\n", loop->num, why);
  return NULL;
}

static class loop *
e2k_av_split (class loop *loop, gphi *phi, tree sa, tree la)
{
  edge exit = single_exit (loop);
  class tree_niter_desc niter;
  if (!exit || EDGE_COUNT (exit->src->succs) != 2
      || (loop->latch != loop->header && !empty_block_p (loop->latch))
      || !easy_exit_values (loop)
      || !number_of_iterations_exit (loop, exit, &niter, false, true)
      || niter.cmp == ERROR_MARK
      || !integer_onep (niter.assumptions)
      || !integer_zerop (niter.may_be_zero)
      || !niter.control.step || TREE_CODE (niter.control.step) != INTEGER_CST)
    return e2k_av_split_why (loop, "the exit or its count");
  /* The exit test's IV, after its step, and where it starts.  */
  gcond *ec = safe_dyn_cast <gcond *> (*gsi_last_bb (exit->src));
  if (!ec)
    return e2k_av_split_why (loop, "no exit test");
  tree cn = NULL_TREE;
  affine_iv civ, siv;
  tree ops[2] = { gimple_cond_lhs (ec), gimple_cond_rhs (ec) };
  for (tree op : ops)
    if (TREE_CODE (op) == SSA_NAME
	&& simple_iv (loop, loop, op, &civ, false)
	&& TREE_CODE (civ.step) == INTEGER_CST
	&& tree_int_cst_equal (civ.step, niter.control.step))
      {
	cn = op;
	break;
      }
  if (!cn
      || !simple_iv (loop, loop, sa, &siv, false)
      || TREE_CODE (siv.step) != INTEGER_CST || integer_zerop (siv.step)
      || !INTEGRAL_TYPE_P (TREE_TYPE (cn)))
    return e2k_av_split_why (loop, "the IVs");
  basic_block *bbs = get_loop_body (loop);
  bool copy = can_copy_bbs_p (bbs, loop->num_nodes);
  free (bbs);
  if (!copy)
    return e2k_av_split_why (loop, "can't copy");

  /* M, the iteration that stores the element, or the last one: the
     first part runs while the exit test's IV isn't its value then.  */
  gimple_seq stmts = NULL;
  tree st = ssizetype;
  /* force_gimple_operand starts its sequence afresh.  */
  auto operand = [&] (tree x)
    {
      gimple_seq seq = NULL;
      x = force_gimple_operand (unshare_expr (x), &seq, true, NULL_TREE);
      gimple_seq_add_seq (&stmts, seq);
      return x;
    };
  tree base = operand (siv.base);
  tree cbase = operand (civ.base);
  tree lastn = operand (fold_convert (st, niter.niter));
  tree d = gimple_build (&stmts, POINTER_DIFF_EXPR, st,
			 gimple_convert (&stmts, ptr_type_node, la),
			 gimple_convert (&stmts, ptr_type_node, base));
  tree step = fold_convert (st, siv.step);
  tree q = gimple_build (&stmts, TRUNC_DIV_EXPR, st, d, step);
  tree r = gimple_build (&stmts, TRUNC_MOD_EXPR, st, d, step);
  tree c1 = gimple_build (&stmts, EQ_EXPR, boolean_type_node, r,
			  build_zero_cst (st));
  tree c2 = gimple_build (&stmts, GE_EXPR, boolean_type_node, q,
			  build_zero_cst (st));
  tree c3 = gimple_build (&stmts, LE_EXPR, boolean_type_node, q, lastn);
  tree hit = gimple_build (&stmts, BIT_AND_EXPR, boolean_type_node, c1,
			   gimple_build (&stmts, BIT_AND_EXPR, boolean_type_node,
					 c2, c3));
  tree m = gimple_build (&stmts, COND_EXPR, st, hit, q, lastn);
  tree ct = TREE_TYPE (cn);
  tree newend = gimple_build (&stmts, PLUS_EXPR, ct,
			      gimple_convert (&stmts, ct, cbase),
			      gimple_build (&stmts, MULT_EXPR, ct,
					    gimple_convert (&stmts, ct, m),
					    fold_convert (ct, civ.step)));
  gsi_insert_seq_on_edge_immediate (loop_preheader_edge (loop), stmts);

  unsigned idx = 0;
  for (gphi_iterator pi = gsi_start_phis (loop->header);
       pi.phi () != phi; gsi_next (&pi))
    idx++;
  /* loop_version may move the PHIs (resizing them).  */
  tree res = gimple_phi_result (phi);
  initialize_original_copy_tables ();
  basic_block cond_bb;
  class loop *loop2 = loop_version (loop, boolean_true_node, &cond_bb,
				    profile_probability::always (),
				    profile_probability::always (),
				    profile_probability::always (),
				    profile_probability::very_likely (), true);
  if (!loop2)
    {
      free_original_copy_tables ();
      return e2k_av_split_why (loop, "loop_version failed");
    }
  edge new_e = connect_loops (loop, loop2);
  connect_loop_phis (loop, loop2, new_e);
  patch_loop_exit (loop, NE_EXPR, cn, newend, true);
  free_original_copy_tables ();

  /* The element's register no longer changes in either part.  */
  gphi *phi1 = as_a <gphi *> (SSA_NAME_DEF_STMT (res));
  SET_PHI_ARG_DEF (phi1, loop_latch_edge (loop)->dest_idx,
		   gimple_phi_result (phi1));
  gphi_iterator p2 = gsi_start_phis (loop2->header);
  for (unsigned k = 0; k < idx; k++)
    gsi_next (&p2);
  SET_PHI_ARG_DEF (p2.phi (), loop_latch_edge (loop2)->dest_idx,
		   gimple_phi_result (p2.phi ()));
  /* The test connect_loops copied after the loop reads its values
     directly: loop-closed SSA again, before e2k_av_loop versions
     either part.  */
  rewrite_into_loop_closed_ssa (NULL, TODO_update_ssa);
  scev_reset_htab ();
  if (dump_file)
    fprintf (dump_file, "e2k: loop %d: split after the store to the element, "
	     "the rest in loop %d\n", loop->num, loop2->num);
  return loop2;
}

/* In a one-block loop, a load from an address the loop doesn't step
   (DR_STEP 0) that one store of the loop may write, an element of the
   same type, can be a register instead: loaded before the loop, and
   after the store given the stored value when the store's address is
   its own (PolyBench's floyd-warshall, "path[i][j] = min (path[i][j],
   path[i][k] + path[k][j])": path[i][k] is written once, at j == k).
   The memory dependence that made every iteration wait for the last
   one's store becomes a compare and a select; the loop can then be
   versioned for the other pairs (e2k_av_loop) and pipelined.  lcc
   speculates such loads instead (lock loads checked each iteration).
   The loop is then split at that iteration (e2k_av_split), the second
   part *SPLIT.  LOOP is innermost; its body is its header, with an
   empty latch or as the latch.  True if it changed the loop.  */
static bool
e2k_av_forward (class loop *loop, class loop **split)
{
  *split = NULL;
  basic_block h = loop->header;
  if (loop->num_nodes > 2
      || (loop->num_nodes == 2 && !empty_block_p (loop->latch))
      || !single_succ_p (loop_preheader_edge (loop)->src))
    return false;
  auto_vec<loop_p, 3> nest;
  auto_vec<data_reference_p> drs;
  auto_vec<ddr_p> ddrs;
  if (!compute_data_dependences_for_loop (loop, false, &nest, &drs, &ddrs))
    {
      free_dependence_relations (ddrs);
      free_data_refs (drs);
      return false;
    }
  /* Statement order in the block.  */
  hash_map<gimple *, int> pos;
  int n = 0;
  for (gimple_stmt_iterator g = gsi_start_bb (h); !gsi_end_p (g); gsi_next (&g))
    pos.put (gsi_stmt (g), n++);
  gimple *ls = NULL, *ss = NULL;
  for (data_reference_p ld : drs)
    {
      gimple *s = DR_STMT (ld);
      if (!DR_IS_READ (ld) || !DR_STEP (ld) || !integer_zerop (DR_STEP (ld))
	  || gimple_bb (s) != h || !gimple_assign_single_p (s)
	  || TREE_CODE (gimple_assign_lhs (s)) != SSA_NAME
	  || gimple_has_volatile_ops (s))
	continue;
      tree lref = gimple_assign_rhs1 (s);
      tree type = TREE_TYPE (lref);
      unsigned HOST_WIDE_INT size;
      if (!expr_invariant_in_loop_p (loop, build_fold_addr_expr
				     (unshare_expr (lref)))
	  || !tree_fits_uhwi_p (TYPE_SIZE_UNIT (type))
	  || (size = tree_to_uhwi (TYPE_SIZE_UNIT (type))) == 0
	  || get_object_alignment (lref) < size * BITS_PER_UNIT)
	continue;
      /* The one store that may write it, after it in the block, of the
	 same type and alignment: it writes the whole element or none.  */
      gimple *st = NULL;
      bool ok = true;
      for (ddr_p ddr : ddrs)
	{
	  data_reference_p o = (DDR_A (ddr) == ld ? DDR_B (ddr)
				: DDR_B (ddr) == ld ? DDR_A (ddr) : NULL);
	  if (!o || !DR_IS_WRITE (o) || DDR_ARE_DEPENDENT (ddr) == chrec_known)
	    continue;
	  /* Only a store stepping through the element's own array (the same
	     base): a run-time check against it would always fail.  Others
	     are versioning's, whose disjoint copy then keeps the element in
	     a register with no recurrence (PolyBench's gemm, A[i][k]
	     against C[i][j]: 20 times slower this way), as is a store to
	     the element itself each iteration (a sum kept in memory, which
	     the copy's LIM keeps in a register).  */
	  if (st && st != DR_STMT (o))
	    ok = false;
	  if (!DR_STEP (o) || integer_zerop (DR_STEP (o))
	      || !DR_BASE_ADDRESS (o) || !DR_BASE_ADDRESS (ld)
	      || !operand_equal_p (DR_BASE_ADDRESS (o), DR_BASE_ADDRESS (ld), 0))
	    ok = false;
	  st = DR_STMT (o);
	}
      if (!ok || !st)
	continue;
      tree sref = gimple_assign_lhs (st);
      tree val = gimple_assign_rhs1 (st);
      if (gimple_bb (st) != h || !gimple_assign_single_p (st)
	  || gimple_has_volatile_ops (st)
	  || !types_compatible_p (TREE_TYPE (sref), type)
	  || get_object_alignment (sref) < size * BITS_PER_UNIT
	  || (TREE_CODE (val) != SSA_NAME && !is_gimple_min_invariant (val))
	  || *pos.get (st) <= *pos.get (s))
	continue;
      ls = s;
      ss = st;
      break;
    }
  free_dependence_relations (ddrs);
  free_data_refs (drs);
  if (!ls)
    return false;

  tree lref = gimple_assign_rhs1 (ls), type = TREE_TYPE (lref);
  tree sref = gimple_assign_lhs (ss), val = gimple_assign_rhs1 (ss);
  /* Before the loop: the element and its address.  */
  edge pe = loop_preheader_edge (loop);
  gimple_seq pre = NULL;
  tree la = force_gimple_operand (build_fold_addr_expr (unshare_expr (lref)),
				  &pre, true, NULL_TREE);
  tree r0 = make_ssa_name (type);
  gimple_seq_add_stmt (&pre, gimple_build_assign (r0, unshare_expr (lref)));
  gsi_insert_seq_on_edge_immediate (pe, pre);
  pe = loop_preheader_edge (loop);
  /* The register through the iterations.  */
  tree r = make_ssa_name (type);
  tree rn = make_ssa_name (type);
  gphi *phi = create_phi_node (r, h);
  add_phi_arg (phi, r0, pe, UNKNOWN_LOCATION);
  add_phi_arg (phi, rn, loop_latch_edge (loop), UNKNOWN_LOCATION);
  /* The load reads it.  */
  gimple_stmt_iterator gl = gsi_for_stmt (ls);
  gimple_assign_set_rhs_from_tree (&gl, r);
  update_stmt (gsi_stmt (gl));
  /* After the store: its value if it wrote the element.  */
  gimple_stmt_iterator gs = gsi_for_stmt (ss);
  gimple_seq post = NULL;
  tree sa = force_gimple_operand (build_fold_addr_expr (unshare_expr (sref)),
				  &post, true, NULL_TREE);
  tree c = make_ssa_name (boolean_type_node);
  gimple_seq_add_stmt (&post, gimple_build_assign (c, EQ_EXPR, sa, la));
  gimple_seq_add_stmt (&post, gimple_build_assign (rn, COND_EXPR, c, val, r));
  gsi_insert_seq_after (&gs, post, GSI_SAME_STMT);
  mark_virtual_operands_for_renaming (cfun);
  update_ssa (TODO_update_ssa_only_virtuals);
  scev_reset_htab ();

  if (dump_file)
    fprintf (dump_file, "e2k: loop %d: a load into a register its store "
	     "updates\n", loop->num);
  if (e2k_av_split_p)
    *split = e2k_av_split (loop, phi, sa, la);
  return true;
}

/* Whether integer T is computed from no pointer: constants, integers
   narrower than a pointer, and arithmetic on such values, through
   PHIs (DEPTH bounds the search).  */
static bool
e2k_pointer_free_p (tree t, hash_set<tree> &seen, int depth)
{
  if (TREE_CODE (t) == INTEGER_CST)
    return true;
  if (TREE_CODE (t) != SSA_NAME || !INTEGRAL_TYPE_P (TREE_TYPE (t))
      || depth > 12)
    return false;
  if (TYPE_PRECISION (TREE_TYPE (t)) < POINTER_SIZE)
    return true;
  if (seen.add (t))
    return true;
  gimple *d = SSA_NAME_DEF_STMT (t);
  if (gphi *phi = dyn_cast <gphi *> (d))
    {
      for (unsigned k = 0; k < gimple_phi_num_args (phi); k++)
	if (!e2k_pointer_free_p (gimple_phi_arg_def (phi, k), seen, depth + 1))
	  return false;
      return true;
    }
  if (!is_gimple_assign (d) || gimple_assign_load_p (d))
    return false;
  switch (gimple_assign_rhs_code (d))
    {
    case PLUS_EXPR: case MINUS_EXPR: case MULT_EXPR: case LSHIFT_EXPR:
    CASE_CONVERT:
      for (unsigned k = 1; k < gimple_num_ops (d); k++)
	if (!e2k_pointer_free_p (gimple_op (d, k), seen, depth + 1))
	  return false;
      return true;
    default:
      return false;
    }
}

/* LIM rewrites the pointer arithmetic it hoists into unsigned integer
   arithmetic (rewrite_to_defined_unconditional), and the pointers it
   then converts the sums to point anywhere: NPB FT's evolve, inlined
   with its arrays u0 and u1, reads "(dcomplex (*)[256][256])
   ((unsigned long) &u0 + k * 1048576)", to which PRE adds "nonlocal",
   so that the pipeliner took it to alias every store through u1 (ivopts
   passes the set on).  Give back what the pointer arithmetic had, the
   object alone, to a pointer converted from &DECL plus an integer
   computed from no pointer.  */
static void
e2k_restore_pt (function *fun)
{
  unsigned i;
  tree name;
  auto addr_decl = [] (tree t) -> tree
    {
      if (TREE_CODE (t) != SSA_NAME)
	return NULL_TREE;
      gimple *d = SSA_NAME_DEF_STMT (t);
      if (!is_gimple_assign (d)
	  || !CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (d)))
	return NULL_TREE;
      tree a = gimple_assign_rhs1 (d);
      if (TREE_CODE (a) != ADDR_EXPR)
	return NULL_TREE;
      tree v = TREE_OPERAND (a, 0);
      return VAR_P (v) && !DECL_EXTERNAL (v) ? v : NULL_TREE;
    };
  FOR_EACH_SSA_NAME (i, name, fun)
    {
      if (!POINTER_TYPE_P (TREE_TYPE (name)))
	continue;
      gimple *d = SSA_NAME_DEF_STMT (name);
      if (!is_gimple_assign (d)
	  || !CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (d))
	  || TREE_CODE (gimple_assign_rhs1 (d)) != SSA_NAME)
	continue;
      gimple *dx = SSA_NAME_DEF_STMT (gimple_assign_rhs1 (d));
      if (!is_gimple_assign (dx) || gimple_assign_rhs_code (dx) != PLUS_EXPR)
	continue;
      tree a = gimple_assign_rhs1 (dx), b = gimple_assign_rhs2 (dx);
      tree decl = addr_decl (a), off = b;
      if (!decl)
	{
	  decl = addr_decl (b);
	  off = a;
	}
      hash_set<tree> seen;
      if (!decl || !e2k_pointer_free_p (off, seen, 0))
	continue;
      /* PRE adds "nonlocal" to what LIM's pointer had (NPB FT); keep a
	 set that doesn't hold the object, which something else gave.  */
      struct ptr_info_def *pi = SSA_NAME_PTR_INFO (name);
      if (pi && !pi->pt.anything
	  && (!pi->pt.vars || !bitmap_bit_p (pi->pt.vars, DECL_PT_UID (decl))))
	continue;
      pi = get_ptr_info (name);
      pt_solution_set_var (&pi->pt, decl);
      if (dump_file)
	{
	  fprintf (dump_file, "e2k: ");
	  print_generic_expr (dump_file, name);
	  fprintf (dump_file, " points to ");
	  print_generic_expr (dump_file, decl);
	  fprintf (dump_file, "\n");
	}
    }
}

/* Whether REF reads an array element at an index the function computes:
   "tab[i]", or "*(tab + off)" with OFF not a constant.  */
static bool
e2k_indexed_ref_p (tree ref)
{
  for (tree r = ref; handled_component_p (r); r = TREE_OPERAND (r, 0))
    if (TREE_CODE (r) == ARRAY_REF && TREE_CODE (TREE_OPERAND (r, 1)) == SSA_NAME)
      return true;
  tree base = get_base_address (ref);
  if (!base || TREE_CODE (base) != MEM_REF
      || TREE_CODE (TREE_OPERAND (base, 0)) != SSA_NAME)
    return false;
  gimple *def = SSA_NAME_DEF_STMT (TREE_OPERAND (base, 0));
  return (is_gimple_assign (def)
	  && gimple_assign_rhs_code (def) == POINTER_PLUS_EXPR
	  && TREE_CODE (gimple_assign_rhs2 (def)) == SSA_NAME);
}

/* A loop walking a hash bucket's chain, "for (p = tab[h & m]; p; p =
   p->next)": GCC guesses that it runs as long as any while loop (94.5%
   to stay, 18 times), but hash tables keep their chains short (Lua's
   string table grows at one string a bucket), so a pipelined walk pays
   its prologue on nearly every entry and loads the nodes after the one
   it stops at, mostly cache misses: with Lua's internshrstr pipelined,
   k-nucleotide ran 3-6% slower on the 8C2.  lcc doesn't pipeline it.
   Tell the profile that the loop runs about twice, and mark the load of
   the next node with a dependence clique of its own (one base, so it
   tells alias analysis nothing), which e2k_ms_wloop looks for to leave
   the loop to the list scheduler.  A chain is a pointer the loop
   replaces by a field of what it points to, its first value loaded from
   an array element at a computed index.  True if it scaled LOOP's
   profile.  */
static bool
e2k_short_chain (class loop *loop)
{
  if (!loops_state_satisfies_p (LOOPS_HAVE_PREHEADERS) || !loop->latch)
    return false;
  edge pre = loop_preheader_edge (loop), latch = loop_latch_edge (loop);
  for (gphi_iterator gsi = gsi_start_phis (loop->header); !gsi_end_p (gsi);
       gsi_next (&gsi))
    {
      gphi *phi = gsi.phi ();
      tree p = gimple_phi_result (phi);
      if (virtual_operand_p (p) || !POINTER_TYPE_P (TREE_TYPE (p)))
	continue;
      tree init = PHI_ARG_DEF_FROM_EDGE (phi, pre);
      tree next = PHI_ARG_DEF_FROM_EDGE (phi, latch);
      if (TREE_CODE (init) != SSA_NAME || TREE_CODE (next) != SSA_NAME)
	continue;
      gimple *ns = SSA_NAME_DEF_STMT (next);
      bool offs = false;
      /* Or a node's offset to the next (Lua's tables, "n += gnext(n)"):
	 the pointer plus a value loaded through it, scaled.  */
      if (e2k_chain_offsets && is_gimple_assign (ns)
	  && gimple_assign_rhs_code (ns) == POINTER_PLUS_EXPR
	  && gimple_assign_rhs1 (ns) == p
	  && TREE_CODE (gimple_assign_rhs2 (ns)) == SSA_NAME)
	{
	  tree o = gimple_assign_rhs2 (ns);
	  gimple *os = SSA_NAME_DEF_STMT (o);
	  for (int k = 0; k < 4 && is_gimple_assign (os)
	       && !gimple_assign_load_p (os); k++)
	    {
	      enum tree_code c = gimple_assign_rhs_code (os);
	      if ((!CONVERT_EXPR_CODE_P (c) && c != MULT_EXPR
		   && c != LSHIFT_EXPR && c != NOP_EXPR)
		  || TREE_CODE (gimple_assign_rhs1 (os)) != SSA_NAME)
		break;
	      os = SSA_NAME_DEF_STMT (gimple_assign_rhs1 (os));
	    }
	  if (gimple_assign_load_p (os))
	    {
	      ns = os;
	      offs = true;
	    }
	}
      if (!gimple_assign_load_p (ns)
	  || !flow_bb_inside_loop_p (loop, gimple_bb (ns)))
	continue;
      tree nb = get_base_address (gimple_assign_rhs1 (ns));
      if (!nb || TREE_CODE (nb) != MEM_REF || TREE_OPERAND (nb, 0) != p)
	continue;
      gimple *is = SSA_NAME_DEF_STMT (init);
      /* The first node: loaded from an array element at a computed
	 index, or an element's address at one ("&t->node[h & m]").  */
      bool first = (gimple_assign_load_p (is)
		    && e2k_indexed_ref_p (gimple_assign_rhs1 (is)));
      /* Offsets link nothing but a table's chains: any node from before
	 the loop (luaH_getint's comes from two ways of hashing).  */
      if (!first && offs)
	first = true;
      if (!first || flow_bb_inside_loop_p (loop, gimple_bb (is)))
	continue;
      scale_loop_profile (loop, profile_probability::always (), 1);
      if (MR_DEPENDENCE_CLIQUE (nb) == 0)
	{
	  machine_function *m = cfun->machine;
	  if (!m->chain_clique)
	    m->chain_clique = get_new_clique (cfun);
	  MR_DEPENDENCE_CLIQUE (nb) = m->chain_clique;
	  MR_DEPENDENCE_BASE (nb) = 1;
	}
      if (dump_enabled_p ())
	dump_printf_loc (MSG_NOTE, ns, "a hash chain: runs about twice\n");
      return true;
    }
  return false;
}

/* In an innermost loop, a branch around loads from memory that the
   join then stores to on every path (lame's count_bits, "ix[k] = (xr[k]
   >= roundfac) ? ix[k] : 0": GIMPLE loads ix[k] only where the condition
   holds and stores the PHI of it and 0).  The loads can't fault, so they
   may run always: they move above the branch, the PHIs become selects
   and the loop one block, which RTL if-conversion doesn't make (it can't
   tell the loads are safe) and e2k_modsched can pipeline; branchy and
   unrolled, the loop took 13 cycles an element on the 8C2.  True if it
   changed LOOP; the caller cleans up the CFG.  */
static bool
e2k_cond_loads (class loop *loop)
{
  bool changed = false;
  basic_block *bbs = get_loop_body (loop);
  for (unsigned i = 0; i < loop->num_nodes; i++)
    {
      basic_block c = bbs[i];
      gcond *cs = safe_dyn_cast <gcond *> (*gsi_last_bb (c));
      if (!cs || EDGE_COUNT (c->succs) != 2)
	continue;
      /* A: the arm; J: the join.  */
      edge ea = NULL, ej = NULL;
      for (int k = 0; k < 2 && !ea; k++)
	{
	  edge e = EDGE_SUCC (c, k), o = EDGE_SUCC (c, 1 - k);
	  if (single_pred_p (e->dest) && single_succ_p (e->dest)
	      && single_succ (e->dest) == o->dest)
	    {
	      ea = e;
	      ej = o;
	    }
	}
      if (!ea)
	continue;
      basic_block a = ea->dest, j = ej->dest;
      if (!flow_bb_inside_loop_p (loop, a) || !flow_bb_inside_loop_p (loop, j)
	  || EDGE_COUNT (j->preds) != 2
	  || ((ea->flags | ej->flags | single_succ_edge (a)->flags)
	      & EDGE_COMPLEX))
	continue;
      bool ok = true;
      for (gphi_iterator gp = gsi_start_phis (j); !gsi_end_p (gp); gsi_next (&gp))
	if (virtual_operand_p (gimple_phi_result (gp.phi ())))
	  ok = false;
      /* A: only loads, each from memory J stores to before any call.  */
      int nl = 0;
      for (gimple_stmt_iterator g = gsi_start_bb (a); ok && !gsi_end_p (g);
	   gsi_next (&g))
	{
	  gimple *s = gsi_stmt (g);
	  if (is_gimple_debug (s))
	    continue;
	  if (!gimple_assign_load_p (s) || gimple_has_volatile_ops (s)
	      || gimple_vdef (s)
	      || TREE_CODE (gimple_assign_lhs (s)) != SSA_NAME)
	    {
	      ok = false;
	      break;
	    }
	  tree ref = gimple_assign_rhs1 (s);
	  bool stored = false;
	  for (gimple_stmt_iterator t = gsi_start_bb (j); !gsi_end_p (t);
	       gsi_next (&t))
	    {
	      gimple *u = gsi_stmt (t);
	      if (is_gimple_call (u) || gimple_has_volatile_ops (u))
		break;
	      if (gimple_store_p (u) && gimple_assign_single_p (u)
		  && operand_equal_p (gimple_assign_lhs (u), ref, 0))
		{
		  stored = true;
		  break;
		}
	    }
	  ok = stored;
	  nl++;
	}
      if (!ok || nl == 0)
	continue;

      /* The condition as a value, then the loads before the branch.  */
      tree cv = make_ssa_name (boolean_type_node);
      gimple_stmt_iterator gc = gsi_for_stmt (cs);
      gsi_insert_before (&gc, gimple_build_assign (cv, gimple_cond_code (cs),
						   gimple_cond_lhs (cs),
						   gimple_cond_rhs (cs)),
			 GSI_SAME_STMT);
      for (gimple_stmt_iterator g = gsi_start_bb (a); !gsi_end_p (g); )
	{
	  gimple *s = gsi_stmt (g);
	  if (is_gimple_debug (s))
	    {
	      gsi_remove (&g, true);
	      continue;
	    }
	  gsi_move_before (&g, &gc);
	}
      /* The PHIs: the arm's value where the branch went to it.  */
      bool to_a = (ea->flags & EDGE_TRUE_VALUE) != 0;
      edge fa = single_succ_edge (a);
      gimple_stmt_iterator gj = gsi_after_labels (j);
      for (gphi_iterator gp = gsi_start_phis (j); !gsi_end_p (gp); )
	{
	  gphi *phi = gp.phi ();
	  tree res = gimple_phi_result (phi);
	  tree va = PHI_ARG_DEF_FROM_EDGE (phi, fa);
	  tree vc = PHI_ARG_DEF_FROM_EDGE (phi, ej);
	  remove_phi_node (&gp, false);
	  gimple *sel = gimple_build_assign (res, COND_EXPR, cv,
					     to_a ? va : vc, to_a ? vc : va);
	  SSA_NAME_DEF_STMT (res) = sel;
	  gsi_insert_before (&gj, sel, GSI_SAME_STMT);
	}
      /* Always to J; the cleanup removes A.  */
      if (ej->flags & EDGE_TRUE_VALUE)
	gimple_cond_make_true (cs);
      else
	gimple_cond_make_false (cs);
      update_stmt (cs);
      changed = true;
      if (dump_enabled_p ())
	dump_printf_loc (MSG_OPTIMIZED_LOCATIONS, cs,
			 "loop %d: %d loads of bb %d run always\n",
			 loop->num, nl, a->index);
    }
  free (bbs);
  return changed;
}

/* Whether data references A and B, which the dependence test took for
   dependent, start a difference apart that isn't a constant (their
   DR_INITs are): then a check of their segments at run time can still
   tell them apart.  */
static bool
e2k_av_unknown_apart_p (data_reference *a, data_reference *b)
{
  hash_map<tree, name_expansion *> *cache = NULL;
  auto addr = [&] (data_reference *d, aff_tree *f)
    {
      aff_tree o;
      tree_to_aff_combination_expand (fold_convert (sizetype,
						    DR_BASE_ADDRESS (d)),
				      sizetype, f, &cache);
      tree_to_aff_combination_expand (fold_convert (sizetype, DR_OFFSET (d)),
				      sizetype, &o, &cache);
      aff_combination_add (f, &o);
    };
  aff_tree fa, fb;
  addr (a, &fa);
  addr (b, &fb);
  aff_combination_scale (&fb, -1);
  aff_combination_add (&fa, &fb);
  free_affine_expand_cache (&cache);
  return fa.n != 0 || fa.rest;
}

/* The loops (by number) e2k_av_loop made of one, which it leaves alone.
   Not dont_vectorize, which it sets on them too: the vectorizer sets it
   on its scalar fallback and epilogue loops, which then kept their
   aliasing and ran unpipelined wherever the vector loop's runtime
   profitability test sent short loops to them (NPB MG with -mvect128:
   2.2 times as long).  */
static bitmap e2k_av_made;

static bool
e2k_av_loop (function *fun, class loop *loop)
{
  if (loop->inner || !single_exit (loop) || !optimize_loop_for_speed_p (loop)
      || bitmap_bit_p (e2k_av_made, loop->num)
      || fun->machine->n_av_cliques == ARRAY_SIZE (fun->machine->av_cliques)
      || fun->machine->n_ov_cliques == ARRAY_SIZE (fun->machine->ov_cliques))
    return false;
  auto why = [&] (const char *w)
    {
      if (dump_file)
	fprintf (dump_file, "e2k: loop %d not versioned: %s\n", loop->num, w);
      return false;
    };
  tree niters = number_of_latch_executions (loop);
  if (!niters || niters == chrec_dont_know)
    return why ("count unknown");

  basic_block *bbs = get_loop_body (loop);
  bool call = false;
  for (unsigned i = 0; i < loop->num_nodes && !call; i++)
    for (gimple_stmt_iterator gsi = gsi_start_bb (bbs[i]); !gsi_end_p (gsi);
	 gsi_next (&gsi))
      if (is_gimple_call (gsi_stmt (gsi))
	  || gimple_has_volatile_ops (gsi_stmt (gsi)))
	{
	  call = true;
	  break;
	}
  free (bbs);
  if (call)
    return why ("a call");

  auto_vec<loop_p, 3> nest;
  auto_vec<data_reference_p> drs;
  auto_vec<ddr_p> ddrs;
  /* With read-read pairs too, for the subgroups below.  */
  bool ok = compute_data_dependences_for_loop (loop, true, &nest, &drs, &ddrs);
  /* Group the references by base address.  A declared array (MG's
     local u1[]) can't take a clique, but needs none if the dependence
     test has told it apart from every other array already (DECL).  */
  auto_vec<int> group;
  auto_vec<bool> decl, tag;
  bool write = false;
  for (unsigned i = 0; ok && i < drs.length (); i++)
    {
      data_reference *dr = drs[i];
      tree b = get_base_address (DR_REF (dr));
      decl.safe_push (b && DECL_P (b));
      tag.safe_push (!decl[i] || e2k_av_decl_slot (dr));
      /* A step of 0 too: an element the loop keeps adding to
	 (PolyBench's 2mm, "tmp[i][j] += alpha * A[i][k] * B[k][j]"),
	 which the copy's LIM then keeps in a register, stored after the
	 loop, as lcc's disjoint copy does.  */
      if (!DR_BASE_ADDRESS (dr) || !DR_STEP (dr)
	  || TREE_CODE (DR_STEP (dr)) != INTEGER_CST
	  || (!e2k_av_base_ref (dr) && !decl[i])
	  || !tree_fits_uhwi_p (TYPE_SIZE_UNIT (TREE_TYPE (DR_REF (dr)))))
	{
	  if (dump_file)
	    {
	      fprintf (dump_file, "e2k: loop %d: reference ", loop->num);
	      print_generic_expr (dump_file, DR_REF (dr));
	      fprintf (dump_file, "\n");
	    }
	  ok = false;
	  break;
	}
      write |= DR_IS_WRITE (dr);
      /* An element the loop doesn't step through is a group of its own
	 (PolyBench's cholesky, "A[i][j] -= A[i][k] * A[j][k]": A[i][j]
	 against the row it reads), checked against the rest of its
	 array like another array.  */
      bool z = integer_zerop (DR_STEP (dr));
      unsigned g = i;
      for (unsigned k = 0; k < i; k++)
	if (operand_equal_p (DR_BASE_ADDRESS (drs[k]), DR_BASE_ADDRESS (dr), 0)
	    && z == (bool) integer_zerop (DR_STEP (drs[k]))
	    && (!z
		|| (operand_equal_p (DR_OFFSET (drs[k]), DR_OFFSET (dr), 0)
		    && operand_equal_p (DR_INIT (drs[k]), DR_INIT (dr), 0))))
	  {
	    g = group[k];
	    break;
	  }
      group.safe_push (g);
    }
  ok &= write;

  hash_map<data_reference_p, unsigned> index;
  for (unsigned i = 0; ok && i < drs.length (); i++)
    index.put (drs[i], i);
  /* Within a group, the references the dependence test told apart over
     the whole loop get bases of their own: a subgroup is a set of
     references that may depend on each other (PolyBench's seidel-2d
     updates A in place, "A[i][j] = (A[i-1][j-1] + ... + A[i+1][j+1]) /
     9": the store to row i never writes rows i-1 and i+1, which lcc
     loads with no checks, while e2k_ms_dam checked them after every
     store).  SPLIT if one separates a store from another reference.  */
  auto_vec<unsigned> sub;
  for (unsigned i = 0; ok && i < drs.length (); i++)
    sub.safe_push (i);
  auto find = [&] (unsigned i)
    {
      while (sub[i] != i)
	i = sub[i] = sub[sub[i]];
      return i;
    };
  hash_map<tree, name_expansion *> *cache = NULL;
  for (unsigned i = 0; ok && i < ddrs.length (); i++)
    {
      unsigned ia = *index.get (DDR_A (ddrs[i]));
      unsigned ib = *index.get (DDR_B (ddrs[i]));
      if (DDR_ARE_DEPENDENT (ddrs[i]) != chrec_known
	  && group[ia] == group[ib]
	  && !e2k_av_apart_p (loop, DR_REF (drs[ia]), DR_REF (drs[ib]),
			      &cache)
	  && !e2k_av_segments_apart_p (loop, drs[ia], drs[ib]))
	{
	  unsigned ra = find (ia), rb = find (ib);
	  sub[MAX (ra, rb)] = MIN (ra, rb);
	}
    }
  free_affine_expand_cache (&cache);
  bool split = false;
  for (unsigned i = 0; ok && i < drs.length (); i++)
    for (unsigned k = 0; k < drs.length (); k++)
      if (DR_IS_WRITE (drs[i]) && tag[i] && tag[k]
	  && group[i] == group[k] && find (i) != find (k))
	split = true;

  /* Give reference I base FIND (I) + 1 in CLIQUE (a declared array's
     through MEM[&decl]).  */
  auto tag_ref = [&] (unsigned i, unsigned short clique)
    {
      tree base;
      if (decl[i])
	{
	  tree *slot = e2k_av_decl_slot (drs[i]);
	  if (!slot)
	    return;
	  tree d = *slot;
	  if (TREE_CODE (d) == MEM_REF)
	    base = d;
	  else
	    {
	      TREE_ADDRESSABLE (d) = 1;
	      base = build2 (MEM_REF, TREE_TYPE (d), build_fold_addr_expr (d),
			     build_int_cst (reference_alias_ptr_type (d), 0));
	      *slot = base;
	      update_stmt (DR_STMT (drs[i]));
	    }
	}
      else
	base = e2k_av_base_ref (drs[i]);
      MR_DEPENDENCE_CLIQUE (base) = clique;
      MR_DEPENDENCE_BASE (base) = find (i) + 1;
    };

  auto_vec<dr_with_seg_len_pair_t> pairs;
  tree n = fold_convert (sizetype, niters);
  for (unsigned i = 0; ok && i < ddrs.length (); i++)
    {
      ddr_p ddr = ddrs[i];
      data_reference *a = DDR_A (ddr), *b = DDR_B (ddr);
      if (DDR_ARE_DEPENDENT (ddr) == chrec_known)
	continue;
      unsigned ia = *index.get (a), ib = *index.get (b);
      if (group[ia] == group[ib])
	continue;
      if (!DR_IS_WRITE (a) && !DR_IS_WRITE (b))
	continue;
      if (decl[ia] || decl[ib])
	{
	  why ("a declared array that may overlap another");
	  ok = false;
	  break;
	}
      /* Different bases that are known to depend on each other; but
	 an element against the rest of its array may well not overlap
	 it (the dependence test can't tell "k < j" there).  */
      bool same = operand_equal_p (DR_BASE_ADDRESS (a), DR_BASE_ADDRESS (b), 0);
      if (DDR_ARE_DEPENDENT (ddr) != chrec_dont_know && !same
	  && e2k_av_rows && e2k_av_unknown_apart_p (a, b))
	{
	  /* Rows of one array a difference apart that the loop doesn't
	     know (NPB FT's fftz2, "y[i21+k][j]" and "y[i22+k][j]", i22 =
	     i21 + lk: the dependence test takes them for one row and
	     ties every store to the next, II 5 against lcc's 2): check
	     the segments as for two arrays.  */
	  if (dump_file)
	    {
	      fprintf (dump_file, "e2k: loop %d: ", loop->num);
	      print_generic_expr (dump_file, DR_REF (a));
	      fprintf (dump_file, " and ");
	      print_generic_expr (dump_file, DR_REF (b));
	      fprintf (dump_file, " an unknown distance apart\n");
	    }
	}
      else if (DDR_ARE_DEPENDENT (ddr) != chrec_dont_know && !same)
	{
	  if (dump_file)
	    {
	      fprintf (dump_file, "e2k: loop %d: ", loop->num);
	      print_generic_expr (dump_file, DR_REF (a));
	      fprintf (dump_file, " against ");
	      print_generic_expr (dump_file, DR_REF (b));
	      fprintf (dump_file, "\n");
	    }
	  why ("dependent references");
	  ok = false;
	  break;
	}
      unsigned HOST_WIDE_INT sa
	= tree_to_uhwi (TYPE_SIZE_UNIT (TREE_TYPE (DR_REF (a))));
      unsigned HOST_WIDE_INT sb
	= tree_to_uhwi (TYPE_SIZE_UNIT (TREE_TYPE (DR_REF (b))));
      pairs.safe_push (dr_with_seg_len_pair_t
		       (dr_with_seg_len (a, e2k_av_segment (loop, a, n), sa,
					 TYPE_ALIGN_UNIT (TREE_TYPE (DR_REF (a)))),
			dr_with_seg_len (b, e2k_av_segment (loop, b, n), sb,
					 TYPE_ALIGN_UNIT (TREE_TYPE (DR_REF (b)))),
			dr_with_seg_len_pair_t::REORDERED));
    }
  if (ok && !pairs.is_empty ())
    {
      /* One pass merges neighbours only: zlib's from[0..2] against
	 out[0..2] come out as three checks of out[k] against from[0..2];
	 a second pass makes them one.  */
      unsigned before;
      do
	{
	  before = pairs.length ();
	  prune_runtime_alias_test_list (&pairs, tree_fits_uhwi_p (niters)
					 ? tree_to_uhwi (niters) : 1);
	}
      while (pairs.length () < before);
      /* MG's resid: its rows against a[0], a[2] and a[3] (a step of 0,
	 each a group of its own) and two other rows, 5.  */
      ok = pairs.length () <= 8;
      if (!ok)
	why ("more than 8 checks");
    }
  else if (ok && split)
    {
      /* Nothing to check: the subgroups as bases of a clique of the loop
	 itself.  */
      unsigned short clique = get_new_clique (fun);
      loop->owned_clique = clique;
      machine_function *m = fun->machine;
      m->av_cliques[m->n_av_cliques++] = clique;
      for (unsigned i = 0; i < drs.length (); i++)
	tag_ref (i, clique);
      if (dump_file)
	fprintf (dump_file, "e2k: loop %d: references told apart\n",
		 loop->num);
      ok = false;
    }
  else
    {
      if (ok)
	why ("nothing to check");
      ok = false;
    }

  if (ok)
    {
      tree cond = NULL_TREE;
      gimple_seq stmts = NULL;
      create_runtime_alias_checks (loop, &pairs, &cond);
      cond = force_gimple_operand_1 (cond, &stmts, is_gimple_val, NULL_TREE);
      profile_probability prob
	= profile_probability::guessed_always ().apply_scale (9, 10);
      basic_block cond_bb;
      initialize_original_copy_tables ();
      class loop *nloop = loop_version (loop, cond, &cond_bb, prob,
					prob.invert (), prob, prob.invert (),
					true);
      free_original_copy_tables ();
      if (!nloop)
	ok = false;
      else
	{
	  nloop->dont_vectorize = true;
	  loop->dont_vectorize = true;
	  bitmap_set_bit (e2k_av_made, nloop->num);
	  bitmap_set_bit (e2k_av_made, loop->num);
	  if (stmts)
	    {
	      gimple_stmt_iterator gsi = gsi_last_bb (cond_bb);
	      gsi_insert_seq_before (&gsi, stmts, GSI_SAME_STMT);
	    }
	  update_ssa (TODO_update_ssa_no_phi);
	  /* LOOP is the copy the test chose for disjoint arrays.  */
	  unsigned short clique = get_new_clique (fun);
	  loop->owned_clique = clique;
	  machine_function *m = fun->machine;
	  m->av_cliques[m->n_av_cliques++] = clique;
	  for (unsigned i = 0; i < drs.length (); i++)
	    tag_ref (i, clique);
	  /* NLOOP runs when the arrays may overlap, as they then mostly
	     do (zlib's copies of distance 1 or 2): a clique of its own,
	     one base for all, which tells the alias oracle nothing.  */
	  unsigned short ov = get_new_clique (fun);
	  nloop->owned_clique = ov;
	  m->ov_cliques[m->n_ov_cliques++] = ov;
	  basic_block *bbs = get_loop_body (nloop);
	  for (unsigned b = 0; b < nloop->num_nodes; b++)
	    for (gimple_stmt_iterator gsi = gsi_start_bb (bbs[b]);
		 !gsi_end_p (gsi); gsi_next (&gsi))
	      if (is_gimple_assign (gsi_stmt (gsi)))
		for (unsigned k = 0; k < gimple_num_ops (gsi_stmt (gsi)); k++)
		  {
		    tree op = gimple_op (gsi_stmt (gsi), k);
		    tree base = op ? get_base_address (op) : NULL_TREE;
		    if (base && (TREE_CODE (base) == MEM_REF
				 || TREE_CODE (base) == TARGET_MEM_REF))
		      {
			MR_DEPENDENCE_CLIQUE (base) = ov;
			MR_DEPENDENCE_BASE (base) = 1;
		      }
		  }
	  free (bbs);
	  if (dump_file)
	    fprintf (dump_file, "e2k: versioned loop %d for aliasing "
		     "(%u checks), copy %d\n", loop->num, pairs.length (),
		     nloop->num);
	}
    }
  free_dependence_relations (ddrs);
  free_data_refs (drs);
  return ok;
}

namespace {

const pass_data pass_data_e2k_alias_version =
{
  GIMPLE_PASS,
  "e2k_alias_version",
  OPTGROUP_LOOP,
  TV_NONE,
  (PROP_cfg | PROP_ssa),
  0, 0, 0, 0
};

const pass_data pass_data_e2k_alias_version_late =
{
  GIMPLE_PASS,
  "e2k_alias_version_late",
  OPTGROUP_LOOP,
  TV_NONE,
  (PROP_cfg | PROP_ssa),
  0, 0, 0, 0
};

/* The innermost loops (by number) of function E2K_AV_FN at the end of
   the early instance, which the late one leaves alone.  */
static function *e2k_av_fn;
static bitmap e2k_av_seen;
static bitmap_obstack e2k_av_obstack;

/* The pass runs twice: after the vectorizer, before predictive commoning
   and complete unrolling (PolyBench's adi, jacobi-2d and heat-3d pipeline
   only so), and after SLP for the loops that became innermost since,
   once cunroll unrolled their small inner loops (NPB SP's sweeps over
   five planes: their "for (m = 0; m < 3; m++)" loops, innermost early,
   got a clique each, and the k loop around them none, so that its
   references told nothing about each other).  */
class pass_e2k_alias_version : public gimple_opt_pass
{
  bool late;
public:
  pass_e2k_alias_version (gcc::context *ctxt, bool late)
    : gimple_opt_pass (late ? pass_data_e2k_alias_version_late
		       : pass_data_e2k_alias_version, ctxt),
      late (late)
  {}

  bool gate (function *) final override
  {
    return e2k_alias_version && optimize >= 2 && flag_tree_loop_optimize;
  }

  unsigned int execute (function *fun) final override
  {
    if (!e2k_av_seen)
      {
	bitmap_obstack_initialize (&e2k_av_obstack);
	e2k_av_seen = BITMAP_ALLOC (&e2k_av_obstack);
	e2k_av_made = BITMAP_ALLOC (&e2k_av_obstack);
      }
    if (late && e2k_av_fn != fun)
      return 0;
    if (!late)
      {
	e2k_av_fn = fun;
	bitmap_clear (e2k_av_seen);
	bitmap_clear (e2k_av_made);
      }
    if (number_of_loops (fun) <= 1)
      return 0;
    bool changed = false;
    if (!late)
      {
	e2k_restore_pt (fun);
	for (auto loop : loops_list (fun, LI_ONLY_INNERMOST))
	  e2k_short_chain (loop);
	if (e2k_cond_loads_p)
	  {
	    bool cl = false;
	    for (auto loop : loops_list (fun, LI_ONLY_INNERMOST))
	      if (optimize_loop_for_speed_p (loop))
		cl |= e2k_cond_loads (loop);
	    if (cl)
	      {
		cleanup_tree_cfg ();
		scev_reset ();
		changed = true;
	      }
	  }
      }
    calculate_dominance_info (CDI_DOMINATORS);
    for (auto loop : loops_list (fun, LI_ONLY_INNERMOST))
      {
	if (late && bitmap_bit_p (e2k_av_seen, loop->num))
	  continue;
	class loop *split = NULL;
	if (optimize_loop_for_speed_p (loop))
	  changed |= e2k_av_forward (loop, &split);
	changed |= e2k_av_loop (fun, loop);
	if (split)
	  changed |= e2k_av_loop (fun, split);
      }
    /* What this instance saw or made (the copies), for the late one.  */
    if (!late)
      for (auto loop : loops_list (fun, LI_ONLY_INNERMOST))
	bitmap_set_bit (e2k_av_seen, loop->num);
    if (!changed)
      return 0;
    scev_reset ();
    rewrite_into_loop_closed_ssa (NULL, TODO_update_ssa);
    return TODO_cleanup_cfg;
  }
};

} // anon namespace

gimple_opt_pass *
make_pass_e2k_alias_version (gcc::context *ctxt, bool late)
{
  return new pass_e2k_alias_version (ctxt, late);
}

/* lcc versions straight-line code the same way: NPB BT's binvcrhs, a
   block of 5x5 matrix updates through three pointer arguments, tests
   whether the 200-byte ranges of lhs and c overlap and runs a copy that
   loads everything up front if they don't, the block as written (with
   data speculation) if they do.  Our scheduler could only lock-load each
   load above the stores before it and check it after them, one check a
   wide instruction (spec/isa/speculation.md): 973 instructions a call.
   This late GIMPLE pass versions a block outside loops whose loads
   follow stores through other pointers that may alias them.  The
   pointers are set before the block, the offsets constant; a test of
   the byte ranges the block touches through each picks a copy whose
   references get a base per pointer in a new dependence clique, as
   restrict would give.  Outside loops the block runs once for one set
   of pointer values, so the clique holds wherever later passes copy
   it.  */

/* Loads that must follow a store through another pointer before a
   block is worth two copies.  */
#define E2K_AVB_MIN_LOADS 8

/* A pointer through which a block accesses memory, and the bytes
   [LO, HI) from it that the block touches.  */
struct e2k_avb_group
{
  tree ptr;
  HOST_WIDE_INT lo, hi;
  bool store;
};

/* For a memory reference REF in BB: its MEM_REF, through a pointer no
   statement of BB sets, and the bytes [*LO, *LO + *SIZE) from the
   pointer it touches; else NULL.  */
static tree
e2k_avb_ref (tree ref, basic_block bb, HOST_WIDE_INT *lo, HOST_WIDE_INT *size)
{
  if (TREE_THIS_VOLATILE (ref)
      || (TREE_CODE (ref) == COMPONENT_REF
	  && DECL_BIT_FIELD (TREE_OPERAND (ref, 1)))
      || !tree_fits_uhwi_p (TYPE_SIZE_UNIT (TREE_TYPE (ref))))
    return NULL_TREE;
  poly_int64 off;
  tree base = get_addr_base_and_unit_offset (ref, &off);
  if (!base || TREE_CODE (base) != MEM_REF || !off.is_constant (lo))
    return NULL_TREE;
  tree p = TREE_OPERAND (base, 0);
  if (TREE_CODE (p) != SSA_NAME || !POINTER_TYPE_P (TREE_TYPE (p)))
    return NULL_TREE;
  gimple *d = SSA_NAME_DEF_STMT (p);
  if (!SSA_NAME_IS_DEFAULT_DEF (p) && gimple_code (d) != GIMPLE_PHI
      && gimple_bb (d) == bb)
    return NULL_TREE;
  poly_offset_int mo = mem_ref_offset (base);
  HOST_WIDE_INT m;
  if (!mo.is_constant () || !wi::fits_shwi_p (mo.to_constant ()))
    return NULL_TREE;
  m = mo.to_constant ().to_shwi ();
  *lo += m;
  *size = tree_to_uhwi (TYPE_SIZE_UNIT (TREE_TYPE (ref)));
  if (*size == 0 || *size > 64 || absu_hwi (*lo) > (1 << 20))
    return NULL_TREE;
  return base;
}

/* The memory reference of statement S, and whether it stores.  */
static tree
e2k_avb_stmt_ref (gimple *s, bool *store)
{
  if (!gimple_assign_single_p (s) || gimple_has_volatile_ops (s))
    return NULL_TREE;
  if (gimple_store_p (s))
    {
      *store = true;
      return gimple_assign_lhs (s);
    }
  if (gimple_assign_load_p (s))
    {
      *store = false;
      return gimple_assign_rhs1 (s);
    }
  return NULL_TREE;
}

/* Version block BB of FUN for aliasing; true if it did.  */
static bool
e2k_av_block (function *fun, basic_block bb)
{
  if (bb->loop_father != loops_for_fn (fun)->tree_root
      || !optimize_bb_for_speed_p (bb)
      || fun->machine->n_av_cliques == ARRAY_SIZE (fun->machine->av_cliques))
    return false;
  /* The references in order, each with its group (or -1).  */
  auto_vec<tree> refs;
  auto_vec<int> grp;
  auto_vec<bool> st;
  auto_vec<e2k_avb_group> groups;
  hash_map<tree, int> index;
  unsigned nstmts = 0;
  for (gimple_stmt_iterator g = gsi_start_bb (bb); !gsi_end_p (g); gsi_next (&g))
    {
      gimple *s = gsi_stmt (g);
      if (is_gimple_debug (s))
	continue;
      if (is_gimple_call (s) || gimple_code (s) == GIMPLE_ASM
	  || stmt_could_throw_p (fun, s) || ++nstmts > 4000)
	return false;
      bool store;
      tree ref = e2k_avb_stmt_ref (s, &store);
      if (!ref)
	{
	  if (gimple_vuse (s) && gimple_code (s) != GIMPLE_RETURN)
	    return false;
	  continue;
	}
      HOST_WIDE_INT lo, size;
      tree base = e2k_avb_ref (ref, bb, &lo, &size);
      int k = -1;
      if (base)
	{
	  tree p = TREE_OPERAND (base, 0);
	  bool existed;
	  int &slot = index.get_or_insert (p, &existed);
	  if (!existed)
	    {
	      slot = groups.length ();
	      groups.safe_push ({ p, lo, lo + size, store });
	    }
	  k = slot;
	  e2k_avb_group &gr = groups[k];
	  gr.lo = MIN (gr.lo, lo);
	  gr.hi = MAX (gr.hi, lo + (HOST_WIDE_INT) size);
	  gr.store |= store;
	}
      refs.safe_push (ref);
      grp.safe_push (k);
      st.safe_push (store);
    }
  if (groups.length () < 2 || refs.length () > 2048)
    return false;

  /* Pairs of groups the test must cover: a store through one may touch
     what the other accesses.  Loads that follow such a store are what
     the copy frees.  */
  unsigned ng = groups.length ();
  auto_sbitmap need (ng * ng);
  bitmap_clear (need);
  unsigned freed = 0;
  for (unsigned i = 0; i < refs.length (); i++)
    {
      if (grp[i] < 0)
	continue;
      bool counted = false;
      for (unsigned k = 0; k < refs.length (); k++)
	{
	  if (grp[k] < 0 || grp[k] == grp[i] || !(st[i] || st[k]))
	    continue;
	  unsigned a = MIN (grp[i], grp[k]), b = MAX (grp[i], grp[k]);
	  bool known = bitmap_bit_p (need, a * ng + b);
	  /* A load after a store.  */
	  bool frees = !st[i] && st[k] && k < i && !counted;
	  if (known && !frees)
	    continue;
	  if (!refs_may_alias_p (refs[i], refs[k], true))
	    continue;
	  bitmap_set_bit (need, a * ng + b);
	  if (frees)
	    {
	      freed++;
	      counted = true;
	    }
	}
    }
  unsigned checks = bitmap_count_bits (need);
  if (dump_file)
    fprintf (dump_file, "e2k: block %d: %u pointers, %u loads to free, "
	     "%u checks\n", bb->index, ng, freed, checks);
  if (freed < E2K_AVB_MIN_LOADS || checks == 0 || checks > 8)
    return false;

  /* The test: for each pair, one range ends before the other starts.  */
  auto addr = [&] (unsigned g, HOST_WIDE_INT k)
    {
      return fold_build2 (PLUS_EXPR, sizetype,
			  fold_convert (sizetype, groups[g].ptr), size_int (k));
    };
  tree cond = boolean_true_node;
  for (unsigned a = 0; a < ng; a++)
    for (unsigned b = a + 1; b < ng; b++)
      if (bitmap_bit_p (need, a * ng + b))
	{
	  tree t = fold_build2 (TRUTH_OR_EXPR, boolean_type_node,
				fold_build2 (LE_EXPR, boolean_type_node,
					     addr (a, groups[a].hi),
					     addr (b, groups[b].lo)),
				fold_build2 (LE_EXPR, boolean_type_node,
					     addr (b, groups[b].hi),
					     addr (a, groups[a].lo)));
	  cond = fold_build2 (TRUTH_AND_EXPR, boolean_type_node, cond, t);
	}

  /* BB keeps its labels and PHIs; BODY, the rest, is copied; COND_BB,
     between them, picks one.  */
  basic_block body = split_block_after_labels (bb)->dest;
  basic_block cond_bb = split_edge (single_pred_edge (body));
  basic_block copy;
  if (!gimple_duplicate_seme_region (single_succ_edge (cond_bb), NULL,
				     &body, 1, &copy, false))
    return false;
  edge te = single_succ_edge (cond_bb);
  te->flags = (te->flags & ~EDGE_FALLTHRU) | EDGE_TRUE_VALUE;
  edge fe = make_edge (cond_bb, body, EDGE_FALSE_VALUE);
  te->probability = profile_probability::guessed_always ().apply_scale (9, 10);
  fe->probability = te->probability.invert ();
  copy->count = te->count ();
  body->count = fe->count ();
  gimple_seq stmts = NULL;
  cond = force_gimple_operand (cond, &stmts, true, NULL_TREE);
  gimple_stmt_iterator gsi = gsi_last_bb (cond_bb);
  gsi_insert_seq_after (&gsi, stmts, GSI_CONTINUE_LINKING);
  gsi_insert_after (&gsi, gimple_build_cond (NE_EXPR, cond, boolean_false_node,
					    NULL_TREE, NULL_TREE),
		    GSI_CONTINUE_LINKING);
  free_dominance_info (CDI_DOMINATORS);
  update_ssa (TODO_update_ssa);

  /* The copy's references: a base per pointer.  */
  unsigned short clique = get_new_clique (fun);
  machine_function *m = fun->machine;
  m->av_cliques[m->n_av_cliques++] = clique;
  for (gimple_stmt_iterator g = gsi_start_bb (copy); !gsi_end_p (g);
       gsi_next (&g))
    {
      bool store;
      tree ref = e2k_avb_stmt_ref (gsi_stmt (g), &store);
      HOST_WIDE_INT lo, size;
      tree base = ref ? e2k_avb_ref (ref, copy, &lo, &size) : NULL_TREE;
      int *k = base ? index.get (TREE_OPERAND (base, 0)) : NULL;
      if (k)
	{
	  MR_DEPENDENCE_CLIQUE (base) = clique;
	  MR_DEPENDENCE_BASE (base) = *k + 1;
	}
    }
  if (dump_enabled_p ())
    dump_printf_loc (MSG_OPTIMIZED_LOCATIONS,
		     dump_user_location_t::from_location_t
		     (gimple_location (last_nondebug_stmt (copy))),
		     "versioned block %d for aliasing (%u checks, %u loads "
		     "freed), copy %d\n", body->index, checks, freed,
		     copy->index);
  return true;
}

namespace {

const pass_data pass_data_e2k_block_version =
{
  GIMPLE_PASS,
  "e2k_block_version",
  OPTGROUP_OTHER,
  TV_NONE,
  (PROP_cfg | PROP_ssa),
  0, 0, 0, 0
};

class pass_e2k_block_version : public gimple_opt_pass
{
public:
  pass_e2k_block_version (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_e2k_block_version, ctxt)
  {}

  bool gate (function *) final override
  {
    return e2k_alias_version_block && optimize >= 2;
  }

  unsigned int execute (function *fun) final override
  {
    if (!current_loops || !optimize_function_for_speed_p (fun))
      return 0;
    auto_vec<basic_block> bbs;
    basic_block bb;
    FOR_EACH_BB_FN (bb, fun)
      bbs.safe_push (bb);
    bool changed = false;
    for (basic_block b : bbs)
      changed |= e2k_av_block (fun, b);
    return changed ? TODO_cleanup_cfg : 0;
  }
};

} // anon namespace

gimple_opt_pass *
make_pass_e2k_block_version (gcc::context *ctxt)
{
  return new pass_e2k_block_version (ctxt);
}

/* ------------------------------------------------------------------ */
/* What vectorizing a loop costs (-mvect128 on v5+)                    */
/* ------------------------------------------------------------------ */

/* The pipeliner runs a loop's iteration every II cycles, at least one
   (it doesn't unroll), with II set by the busiest resource: six ALU
   channels, four array prefetch reads, two stores; integer qp
   operations in four channels (qpadd and qpcmp in two).  So a vector
   loop gains where the scalar one fits its iteration in a cycle or two
   (PolyBench's gemm: II 1 for one double or for two), and nothing where
   the vector one needs II 2 for two elements where the scalar one took
   II 1 for one (jacobi-2d: five reads, two of them misaligned, and a
   misaligned store, past four prefetch reads a cycle).  The body costs
   12 a cycle of II (an ALU operation 2, as in e2k_builtin_vectorization
   _cost, which the code around a loop keeps); loads of one stream,
   which the pipeliner reads once and passes on (x[i-1], x[i], x[i+1]),
   count once.  */
class e2k_vector_costs : public vector_costs
{
public:
  using vector_costs::vector_costs;

  unsigned int add_stmt_cost (int count, vect_cost_for_stmt kind,
			      stmt_vec_info stmt_info, slp_tree node,
			      tree vectype, int misalign,
			      vect_cost_model_location where) override;
  void finish_cost (const vector_costs *scalar_costs) override;

private:
  bool new_stream (stmt_vec_info stmt_info);
  static bool aligned_p (stmt_vec_info stmt_info, tree vectype);

  /* What one iteration of the loop takes of each resource.  */
  unsigned m_alu = 0, m_pint = 0, m_mova = 0, m_st = 0;
  /* The lanes of an in-order reduction (FOLD_LEFT_REDUCTION, an FP sum
     without -ffast-math): the vector loop adds them one after another,
     4 cycles each (durbin's "sum += r[k-i-1] * y[i]": II 8 for two
     doubles, the scalar loop's II 4 for one).  */
  unsigned m_fold_left = 0;
  /* The load streams so far: a data reference of each.  */
  auto_vec<data_reference *> m_streams;
};

/* Whether STMT_INFO's load reads a stream no earlier load does: not
   the same base, offset and step at a position up to four iterations
   away (a row of a multidimensional array further on is a stream of
   its own: heat-3d's A[i+1][j][k] against A[i][j][k]).  */
bool
e2k_vector_costs::new_stream (stmt_vec_info stmt_info)
{
  data_reference *dr = stmt_info ? STMT_VINFO_DATA_REF (stmt_info) : NULL;
  if (!dr || !DR_STEP (dr) || TREE_CODE (DR_STEP (dr)) != INTEGER_CST
      || !DR_INIT (dr) || TREE_CODE (DR_INIT (dr)) != INTEGER_CST)
    return true;
  unsigned HOST_WIDE_INT vf = 1;
  if (!costing_for_scalar ())
    if (loop_vec_info lv = dyn_cast<loop_vec_info> (m_vinfo))
      if (!LOOP_VINFO_VECT_FACTOR (lv).is_constant (&vf))
	return true;
  HOST_WIDE_INT step = tree_to_shwi (DR_STEP (dr)) * (HOST_WIDE_INT) vf;
  for (data_reference *o : m_streams)
    if (operand_equal_p (DR_BASE_ADDRESS (o), DR_BASE_ADDRESS (dr), 0)
	&& operand_equal_p (DR_OFFSET (o), DR_OFFSET (dr), 0)
	&& operand_equal_p (DR_STEP (o), DR_STEP (dr), 0)
	&& (step == 0
	    ? tree_int_cst_equal (DR_INIT (o), DR_INIT (dr))
	    : ((tree_to_shwi (DR_INIT (dr)) - tree_to_shwi (DR_INIT (o)))
	       % step == 0
	       && IN_RANGE ((tree_to_shwi (DR_INIT (dr))
			     - tree_to_shwi (DR_INIT (o))) / step, -4, 4))))
      return false;
  m_streams.safe_push (dr);
  return true;
}

/* Whether STMT_INFO's vector access, of VECTYPE, is known to be aligned
   to it: what the vectorizer then emits as an aligned access.  */
bool
e2k_vector_costs::aligned_p (stmt_vec_info stmt_info, tree vectype)
{
  if (!stmt_info || !vectype || !STMT_VINFO_DATA_REF (stmt_info))
    return false;
  dr_vec_info *dri = STMT_VINFO_DR_INFO (stmt_info);
  return (known_alignment_for_access_p (dri, vectype)
	  && dr_misalignment (dri, vectype) == 0);
}

unsigned int
e2k_vector_costs::add_stmt_cost (int count, vect_cost_for_stmt kind,
				 stmt_vec_info stmt_info, slp_tree node,
				 tree vectype, int misalign,
				 vect_cost_model_location where)
{
  if (where == vect_body && e2k_vect128 && e2k_arch >= 5)
    {
      unsigned n = 1;
      if (vectype)
	n = TYPE_VECTOR_SUBPARTS (vectype).to_constant ();
      if (!costing_for_scalar () && node && vectype
	  && vect_reduc_type (m_vinfo, node) == FOLD_LEFT_REDUCTION)
	m_fold_left = MAX (m_fold_left, n);
      bool fp = vectype && FLOAT_TYPE_P (TREE_TYPE (vectype));
      switch (kind)
	{
	case scalar_stmt:
	  m_alu += count;
	  break;
	case vector_stmt:
	  m_alu += count;
	  if (!fp)
	    m_pint += count;
	  break;
	case scalar_load:
	  if (new_stream (stmt_info))
	    m_mova += count;
	  break;
	case vector_load:
	case unaligned_load:
	  /* A movaqp where aligned, else two halves and a qppackdl (the
	     vectorizer takes an access of unknown alignment as aligned
	     here, and its code as not).  */
	  if (aligned_p (stmt_info, vectype))
	    {
	      if (new_stream (stmt_info))
		m_mova += count;
	    }
	  else
	    {
	      m_alu += count;
	      if (new_stream (stmt_info))
		m_mova += 2 * count;
	    }
	  break;
	case vector_gather_load:
	  m_alu += count * n;
	  m_mova += count * n;
	  break;
	case scalar_store:
	  m_st += count;
	  break;
	case vector_store:
	case unaligned_store:
	  /* A staaqp where aligned, else two halves (addd, qpswitchd) and
	     two stores.  */
	  if (aligned_p (stmt_info, vectype))
	    m_st += count;
	  else
	    {
	      m_alu += 2 * count;
	      m_st += 2 * count;
	    }
	  break;
	case vector_scatter_store:
	  m_alu += count * n;
	  m_st += count * n;
	  break;
	case vec_to_scalar:
	case scalar_to_vec:
	case vec_perm:
	  m_alu += count;
	  break;
	case vec_promote_demote:
	  m_alu += 2 * count;
	  break;
	case vec_construct:
	  m_alu += count * MAX (n / 2, 1u);
	  break;
	default:
	  break;
	}
    }
  return vector_costs::add_stmt_cost (count, kind, stmt_info, node, vectype,
				      misalign, where);
}

void
e2k_vector_costs::finish_cost (const vector_costs *scalar_costs)
{
  if (e2k_vect128 && e2k_arch >= 5 && is_a<loop_vec_info> (m_vinfo))
    {
      /* In twelfths of a cycle.  */
      unsigned b = MAX (MAX (m_alu * 2, m_pint * 3),
			MAX (m_mova * 3, m_st * 6));
      unsigned ii = MAX (MAX (1u, CEIL (b, 12)), 4 * m_fold_left);
      m_costs[vect_body] = ii * 12;
      /* The code around the loop, the scalar iterations peeled for
	 alignment and the epilogue's among it, runs unpipelined, bound
	 by latency rather than by channels: a tenth of the rate the costs
	 per operation assume (an unpipelined iteration takes 20 to 40
	 cycles: heat-3d's rows of 118 elements ran 59 vector iterations
	 at II 3 and two scalar ones slower than 118 at II 2; NPB SP's of
	 30 to 60, 1.8 times as long vectorized).  */
      m_costs[vect_prologue] *= 10;
      m_costs[vect_epilogue] *= 10;
      if (dump_file && (dump_flags & TDF_DETAILS))
	fprintf (dump_file, "e2k: %s iteration: %u ALU, %u integer qp, %u "
		 "loads, %u stores: II %u\n",
		 costing_for_scalar () ? "scalar" : "vector", m_alu, m_pint,
		 m_mova, m_st, ii);
    }
  vector_costs::finish_cost (scalar_costs);
}

vector_costs *
e2k_vectorize_create_costs (vec_info *vinfo, bool costing_for_scalar)
{
  return new e2k_vector_costs (vinfo, costing_for_scalar);
}
