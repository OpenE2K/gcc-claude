/* Builtins for the Elbrus (E2K) port: the types __float80 and
   __float128, the FP control and status register builtins that atomic
   compound assignment of floating types uses, and lcc's run-time CPU
   detection.
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
#include "cgraph.h"

/* This file should be included last.  */
#include "e2k-internal.h"

static void e2k_init_fp_state_builtins (void);
static void e2k_init_cpu_builtins (void);

void
e2k_init_builtins (void)
{
  /* lcc's __float80 is long double, one type (relcc2 spec/abi/
     calling-convention.md, "C++ ABI beyond calls"), as on x86 when long
     double is 80-bit.  */
  lang_hooks.types.register_builtin_type (long_double_type_node,
					  "__float80");
  /* As on x86: for C++, __float128 is a type distinct from _Float128 that
     mangles as "g".  */
  if (float128t_type_node == NULL_TREE)
    {
      float128t_type_node = make_node (REAL_TYPE);
      TYPE_PRECISION (float128t_type_node)
	= TYPE_PRECISION (float128_type_node);
      SET_TYPE_MODE (float128t_type_node, TYPE_MODE (float128_type_node));
      layout_type (float128t_type_node);
    }
  lang_hooks.types.register_builtin_type (float128t_type_node, "__float128");
  e2k_init_fp_state_builtins ();
  e2k_init_cpu_builtins ();
}

/* The FP control and status register builtins, for
   e2k_atomic_assign_expand_fenv (not documented for users), and lcc's
   run-time CPU detection.  */
enum e2k_builtin
{
  E2K_BUILTIN_RRS_PFPFR,
  E2K_BUILTIN_RRS_FPCR,
  E2K_BUILTIN_RRS_FPSR,
  E2K_BUILTIN_RWS_PFPFR,
  E2K_BUILTIN_RWS_FPCR,
  E2K_BUILTIN_RWS_FPSR,
  E2K_BUILTIN_CPU_INIT,
  E2K_BUILTIN_CPU_IS,
  E2K_BUILTIN_CPU_NAME,
  E2K_BUILTIN_CPU_ARCH,
  E2K_BUILTIN_GET_CPU_ISET,
  E2K_BUILTIN_MAX
};

static GTY(()) tree e2k_builtins[E2K_BUILTIN_MAX];

static void
e2k_init_fp_state_builtins (void)
{
  static const char *const names[E2K_BUILTIN_CPU_INIT] = {
    "__builtin_e2k_rrs_pfpfr", "__builtin_e2k_rrs_fpcr",
    "__builtin_e2k_rrs_fpsr", "__builtin_e2k_rws_pfpfr",
    "__builtin_e2k_rws_fpcr", "__builtin_e2k_rws_fpsr"
  };
  tree get = build_function_type_list (unsigned_type_node, NULL_TREE);
  tree set = build_function_type_list (void_type_node, unsigned_type_node,
				       NULL_TREE);
  for (int i = 0; i < E2K_BUILTIN_CPU_INIT; i++)
    e2k_builtins[i]
      = add_builtin_function (names[i], i < E2K_BUILTIN_RWS_PFPFR ? get : set,
			      i, BUILT_IN_MD, NULL, NULL_TREE);
}

/* lcc's run-time CPU detection (relcc2 spec/abi/source-compat.md, "CPU
   detection at run time"; lcc-builtins.md, "CPU detection").
   __builtin_cpu_is ("NAME") compares a word of the hidden 64-byte
   __cpu_info that libgcc's __cpu_init fills from %idr (cpuinfo.c): +0
   the ISA version for "elbrus-vN", +4 lcc's code for a CPU.
   __builtin_e2k_get_cpu_iset () is the +0 word.  __builtin_cpu_init,
   __builtin_cpu_name and __builtin_cpu_arch call libgcc's __cpu_init,
   __cpu_name and __cpu_arch, as lcc's call the functions of those names
   in its runtime.  The names are lcc 1.29.16's and 1.31.05's, which
   refuse any other.  */
static const struct
{
  const char *name;
  unsigned char word, value;
} e2k_cpu_is_names[] = {
  { "elbrus-v1", 0, 1 }, { "elbrus-v2", 0, 2 }, { "elbrus-v3", 0, 3 },
  { "elbrus-v4", 0, 4 }, { "elbrus-v5", 0, 5 }, { "elbrus-v6", 0, 6 },
  { "elbrus-v7", 0, 7 },
  { "elbrus-s", 1, 2 }, { "elbrus-2c+", 1, 3 }, { "elbrus-4c", 1, 4 },
  { "elbrus-2cm", 1, 5 }, { "elbrus-8c", 1, 6 }, { "elbrus-1c+", 1, 7 },
  { "elbrus-8c2", 1, 8 }, { "elbrus-12c", 1, 9 }, { "elbrus-16c", 1, 10 },
  { "elbrus-2c3", 1, 11 }, { "elbrus-48c", 1, 12 }, { "elbrus-8v7", 1, 13 }
};

static GTY(()) tree e2k_cpu_info_var;
static GTY(()) tree e2k_cpu_fns[3];

static void
e2k_init_cpu_builtins (void)
{
  tree cstr = build_pointer_type (build_qualified_type (char_type_node,
						       TYPE_QUAL_CONST));
  tree void_fn = build_function_type_list (void_type_node, NULL_TREE);
  tree str_fn = build_function_type_list (cstr, NULL_TREE);
  tree is_fn = build_function_type_list (integer_type_node, cstr,
					 NULL_TREE);
  tree iset_fn = build_function_type_list (unsigned_type_node, NULL_TREE);
  static const struct { const char *name; tree *type; } b[] = {
    { "__builtin_cpu_init", &void_fn }, { "__builtin_cpu_is", &is_fn },
    { "__builtin_cpu_name", &str_fn }, { "__builtin_cpu_arch", &str_fn },
    { "__builtin_e2k_get_cpu_iset", &iset_fn }
  };
  for (unsigned i = 0; i < ARRAY_SIZE (b); i++)
    e2k_builtins[E2K_BUILTIN_CPU_INIT + i]
      = add_builtin_function (b[i].name, *b[i].type,
			      E2K_BUILTIN_CPU_INIT + i, BUILT_IN_MD, NULL,
			      NULL_TREE);
}

/* Word WORD of __cpu_info.  */
static tree
e2k_cpu_info_word (int word)
{
  if (!e2k_cpu_info_var)
    {
      tree type = build_array_type_nelts (unsigned_type_node, 16);
      tree v = build_decl (BUILTINS_LOCATION, VAR_DECL,
			   get_identifier ("__cpu_info"), type);
      DECL_EXTERNAL (v) = 1;
      TREE_PUBLIC (v) = 1;
      DECL_ARTIFICIAL (v) = 1;
      DECL_VISIBILITY (v) = VISIBILITY_HIDDEN;
      DECL_VISIBILITY_SPECIFIED (v) = 1;
      varpool_node::get_create (v);
      e2k_cpu_info_var = v;
    }
  return build4 (ARRAY_REF, unsigned_type_node, e2k_cpu_info_var,
		 build_int_cst (integer_type_node, word), NULL_TREE,
		 NULL_TREE);
}

/* The entry of e2k_cpu_is_names for the argument ARG of
   __builtin_cpu_is, -1 if it is not a string literal, -2 if lcc doesn't
   know the name.  */
static int
e2k_cpu_is_index (tree arg, const char **name)
{
  while (arg && TREE_CODE (arg) != STRING_CST)
    {
      if (!EXPR_P (arg))
	return -1;
      arg = TREE_OPERAND (arg, 0);
    }
  if (!arg)
    return -1;
  *name = TREE_STRING_POINTER (arg);
  for (unsigned i = 0; i < ARRAY_SIZE (e2k_cpu_is_names); i++)
    if (strcmp (e2k_cpu_is_names[i].name, *name) == 0)
      return i;
  return -2;
}

/* Report a __builtin_cpu_is argument lcc refuses, at LOC.  */
static bool
e2k_check_cpu_is (location_t loc, tree arg)
{
  const char *name = NULL;
  switch (e2k_cpu_is_index (arg, &name))
    {
    case -1:
      error_at (loc, "the argument of %<__builtin_cpu_is%> must be a "
		"string literal");
      return false;
    case -2:
      error_at (loc, "unknown CPU %qs for %<__builtin_cpu_is%>", name);
      return false;
    default:
      return true;
    }
}

/* __builtin_cpu_is (ARG): the compare, or NULL_TREE for an argument
   e2k_check_builtin_call has reported.  */
static tree
e2k_fold_cpu_is (tree arg)
{
  const char *name;
  int i = e2k_cpu_is_index (arg, &name);
  if (i < 0)
    return NULL_TREE;
  return fold_build2 (EQ_EXPR, integer_type_node,
		      e2k_cpu_info_word (e2k_cpu_is_names[i].word),
		      build_int_cst (unsigned_type_node,
				     e2k_cpu_is_names[i].value));
}

bool
e2k_check_builtin_call (location_t loc, vec<location_t>, tree fndecl,
			tree, unsigned int nargs, tree *args, bool complain)
{
  if (fndecl_built_in_p (fndecl, BUILT_IN_MD)
      && DECL_MD_FUNCTION_CODE (fndecl) == E2K_BUILTIN_CPU_IS
      && nargs == 1)
    {
      const char *name;
      if (!complain)
	return e2k_cpu_is_index (args[0], &name) >= 0;
      return e2k_check_cpu_is (loc, args[0]);
    }
  return true;
}

tree
e2k_fold_builtin (tree fndecl, int n_args, tree *args, bool)
{
  switch (DECL_MD_FUNCTION_CODE (fndecl))
    {
    case E2K_BUILTIN_CPU_IS:
      if (n_args == 1)
	return e2k_fold_cpu_is (args[0]);
      return NULL_TREE;
    case E2K_BUILTIN_GET_CPU_ISET:
      return e2k_cpu_info_word (0);
    default:
      return NULL_TREE;
    }
}

tree
e2k_builtin_decl (unsigned code, bool)
{
  return code < E2K_BUILTIN_MAX ? e2k_builtins[code] : error_mark_node;
}

rtx
e2k_expand_builtin (tree exp, rtx target, rtx, machine_mode mode, int)
{
  tree fndecl = TREE_OPERAND (CALL_EXPR_FN (exp), 0);
  unsigned code = DECL_MD_FUNCTION_CODE (fndecl);
  switch (code)
    {
    case E2K_BUILTIN_CPU_IS:
      {
	tree arg = CALL_EXPR_ARG (exp, 0);
	if (!e2k_check_cpu_is (EXPR_LOCATION (exp), arg))
	  return const0_rtx;
	return expand_expr (e2k_fold_cpu_is (arg), target, mode,
			    EXPAND_NORMAL);
      }
    case E2K_BUILTIN_GET_CPU_ISET:
      return expand_expr (e2k_cpu_info_word (0), target, mode,
			  EXPAND_NORMAL);
    case E2K_BUILTIN_CPU_INIT:
    case E2K_BUILTIN_CPU_NAME:
    case E2K_BUILTIN_CPU_ARCH:
      {
	static const char *const fns[3]
	  = { "__cpu_init", "__cpu_name", "__cpu_arch" };
	unsigned i = (code == E2K_BUILTIN_CPU_INIT ? 0
		      : code == E2K_BUILTIN_CPU_NAME ? 1 : 2);
	if (!e2k_cpu_fns[i])
	  e2k_cpu_fns[i] = build_fn_decl (fns[i], TREE_TYPE (fndecl));
	return expand_expr (build_call_expr (e2k_cpu_fns[i], 0), target, mode,
			    EXPAND_NORMAL);
      }
    default:
      break;
    }
  if (code < E2K_BUILTIN_RWS_PFPFR)
    {
      if (!target || !register_operand (target, SImode))
	target = gen_reg_rtx (SImode);
      emit_insn (gen_e2k_rrs (target, GEN_INT (code)));
      return target;
    }
  rtx val = force_reg (SImode,
		       gen_lowpart (SImode,
				    expand_normal (CALL_EXPR_ARG (exp, 0))));
  emit_insn (gen_e2k_rws (GEN_INT (code - E2K_BUILTIN_RWS_PFPFR), val));
  return const0_rtx;
}

/* Atomic compound assignment of a floating type: like glibc's feholdexcept,
   feclearexcept and feupdateenv (sysdeps/e2k/fpu), which keep float and
   double flags in %pfpfr and 80-bit ones in %fpsr, with the same FE_*
   bits.  The masks in %pfpfr are the flag bits shifted left by 7; those
   in %fpcr are the flag bits.  */
void
e2k_atomic_assign_expand_fenv (tree *hold, tree *clear, tree *update)
{
  const unsigned HOST_WIDE_INT fe_all = 0x3d;
  tree uns = unsigned_type_node;
  tree get_pfpfr = e2k_builtins[E2K_BUILTIN_RRS_PFPFR];
  tree get_fpcr = e2k_builtins[E2K_BUILTIN_RRS_FPCR];
  tree get_fpsr = e2k_builtins[E2K_BUILTIN_RRS_FPSR];
  tree set_pfpfr = e2k_builtins[E2K_BUILTIN_RWS_PFPFR];
  tree set_fpcr = e2k_builtins[E2K_BUILTIN_RWS_FPCR];
  tree set_fpsr = e2k_builtins[E2K_BUILTIN_RWS_FPSR];

  tree pfpfr = create_tmp_var_raw (uns);
  tree fpcr = create_tmp_var_raw (uns);
  tree fpsr = create_tmp_var_raw (uns);
  tree held_pfpfr = create_tmp_var_raw (uns);
  tree held_fpsr = create_tmp_var_raw (uns);

  /* hold: save the three registers, then mask every exception and clear
     the flags.  */
  tree ld_pfpfr = build4 (TARGET_EXPR, uns, pfpfr,
			  build_call_expr (get_pfpfr, 0), NULL_TREE,
			  NULL_TREE);
  tree ld_fpcr = build4 (TARGET_EXPR, uns, fpcr,
			 build_call_expr (get_fpcr, 0), NULL_TREE, NULL_TREE);
  tree ld_fpsr = build4 (TARGET_EXPR, uns, fpsr,
			 build_call_expr (get_fpsr, 0), NULL_TREE, NULL_TREE);
  tree v_pfpfr
    = build2 (BIT_IOR_EXPR, uns,
	      build2 (BIT_AND_EXPR, uns, pfpfr,
		      build_int_cst (uns, ~fe_all)),
	      build_int_cst (uns, fe_all << 7));
  tree v_fpsr = build2 (BIT_AND_EXPR, uns, fpsr,
			build_int_cst (uns, ~fe_all));
  tree mk_held_pfpfr = build4 (TARGET_EXPR, uns, held_pfpfr, v_pfpfr,
			       NULL_TREE, NULL_TREE);
  tree mk_held_fpsr = build4 (TARGET_EXPR, uns, held_fpsr, v_fpsr,
			      NULL_TREE, NULL_TREE);
  tree v_fpcr = build2 (BIT_IOR_EXPR, uns, fpcr, build_int_cst (uns, fe_all));
  *hold = build2 (COMPOUND_EXPR, void_type_node,
		  build2 (COMPOUND_EXPR, void_type_node, ld_pfpfr, ld_fpcr),
		  ld_fpsr);
  *hold = build2 (COMPOUND_EXPR, void_type_node, *hold,
		  build2 (COMPOUND_EXPR, void_type_node, mk_held_pfpfr,
			  mk_held_fpsr));
  *hold = build2 (COMPOUND_EXPR, void_type_node, *hold,
		  build_call_expr (set_pfpfr, 1, held_pfpfr));
  *hold = build2 (COMPOUND_EXPR, void_type_node, *hold,
		  build_call_expr (set_fpcr, 1, v_fpcr));
  *hold = build2 (COMPOUND_EXPR, void_type_node, *hold,
		  build_call_expr (set_fpsr, 1, held_fpsr));

  /* clear: clear the flags again.  */
  *clear = build2 (COMPOUND_EXPR, void_type_node,
		   build_call_expr (set_pfpfr, 1, held_pfpfr),
		   build_call_expr (set_fpsr, 1, held_fpsr));

  /* update: collect the new flags, restore the environment and raise
     them.  */
  tree exc = create_tmp_var_raw (uns);
  tree v_exc = build2 (BIT_AND_EXPR, uns,
		       build2 (BIT_IOR_EXPR, uns,
			       build_call_expr (get_pfpfr, 0),
			       build_call_expr (get_fpsr, 0)),
		       build_int_cst (uns, fe_all));
  tree mk_exc = build4 (TARGET_EXPR, uns, exc, v_exc, NULL_TREE, NULL_TREE);
  tree raise = builtin_decl_implicit (BUILT_IN_ATOMIC_FERAISEEXCEPT);
  *update = build2 (COMPOUND_EXPR, void_type_node, mk_exc,
		    build_call_expr (set_pfpfr, 1, pfpfr));
  *update = build2 (COMPOUND_EXPR, void_type_node, *update,
		    build_call_expr (set_fpcr, 1, fpcr));
  *update = build2 (COMPOUND_EXPR, void_type_node, *update,
		    build_call_expr (set_fpsr, 1, fpsr));
  *update = build2 (COMPOUND_EXPR, void_type_node, *update,
		    build_call_expr (raise, 1, fold_convert (integer_type_node,
							     exc)));
}

#include "gt-e2k-builtins.h"
