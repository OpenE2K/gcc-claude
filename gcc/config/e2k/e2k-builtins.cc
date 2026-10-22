/* Builtins for the Elbrus (E2K) port: the types __float80 and
   __float128, the FP control and status register builtins that atomic
   compound assignment of floating types uses, lcc's run-time CPU
   detection, and lcc's operation builtins (e2k-builtins.def).
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
static void e2k_init_op_builtins (void);

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
  e2k_init_op_builtins ();
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

/* lcc's operation builtins (relcc2 spec/abi/lcc-builtins.md), from
   e2k-builtins.def, which gen-e2k-builtins.py writes from the
   specification: each is the operations lcc 1.31.05 compiles it to,
   written as lcc's code has them, "pextrh a0, a1, {k2&0xff!}, ret": the
   C arguments 0 and 1, argument 2 a constant masked to 8 bits in an
   8-bit ALES field ('!': no literal syllable), the result.  A KIND
   other than RULE is built by e2k_expand_bop.  Their function codes
   follow E2K_BUILTIN_MAX.  */
enum e2k_bkind
{
  E2K_BK_RULE, E2K_BK_PRED, E2K_BK_FX, E2K_BK_PACK, E2K_BK_SHUFH, E2K_BK_LD_SM, E2K_BK_LD_CLEARTAG, E2K_BK_ST, E2K_BK_PST
};

enum e2k_btype
{
  E2K_BT_NONE, E2K_BT_VOID, E2K_BT_U32, E2K_BT_U64, E2K_BT_I64,
  E2K_BT_V2DI, E2K_BT_XF, E2K_BT_PTR, E2K_BT_CPTR
};

struct e2k_bop
{
  const char *name;
  enum e2k_bkind kind;
  int iset;
  enum attr_type type;
  const char *trace;
  enum e2k_btype ret, args[4];
};

#define E2K_BUILTIN(NAME, KIND, ISET, TYPE, TRACE, R, A0, A1, A2, A3)	\
  { NAME, E2K_BK_##KIND, ISET, TYPE_##TYPE, TRACE, E2K_BT_##R,		\
    { E2K_BT_##A0, E2K_BT_##A1, E2K_BT_##A2, E2K_BT_##A3 } },
static const struct e2k_bop e2k_bops[] = {
#include "e2k-builtins.def"
};
#undef E2K_BUILTIN

#define E2K_NBOPS_MAX 512
STATIC_ASSERT (ARRAY_SIZE (e2k_bops) <= E2K_NBOPS_MAX);
static GTY(()) tree e2k_bop_decls[E2K_NBOPS_MAX];

/* A source operand of an operation builtin's insn.  */
enum e2k_bopnd_kind
{
  E2K_OPND_ARG,		/* argument ARG */
  E2K_OPND_CONST,	/* argument ARG, a constant, & MASK */
  E2K_OPND_SUFFIX,	/* the same, printed as the mnemonic's suffix */
  E2K_OPND_FIXED,	/* the literal VAL */
  E2K_OPND_VEC		/* the 16-byte constant VAL:VAL2 (low:high) */
};

struct e2k_bopnd
{
  enum e2k_bopnd_kind kind;
  int arg;
  bool lit8;
  unsigned HOST_WIDE_INT mask, val, val2;
};

/* An operation builtin's trace, parsed (e2k_bop_parse).  */
struct e2k_bop_parsed
{
  char mnem[32];	/* the mnemonic, up to its suffix ("plog_") */
  char tail[16];	/* the mnemonic after its suffix */
  int sfx;		/* the operand that is the suffix, or 0 */
  int n;		/* source operands, 1 to n */
  struct e2k_bopnd op[5];
};

static struct e2k_bop_parsed *e2k_bop_info;
static int e2k_bop_puttagd = -1, e2k_bop_puttagqp = -1;

/* Parse a trace placeholder "{k2&0xff!}", "{k0&0xff:02x}" or
   "{q0x...:0x...}" at P into O; return the text after it.  */
static const char *
e2k_bop_parse_brace (const char *p, struct e2k_bopnd *o)
{
  gcc_assert (*p == '{');
  p++;
  if (*p == 'q')
    {
      o->kind = E2K_OPND_VEC;
      o->val = strtoull (p + 1, (char **) &p, 0);
      gcc_assert (*p == ':');
      o->val2 = strtoull (p + 1, (char **) &p, 0);
    }
  else
    {
      gcc_assert (*p == 'k');
      o->kind = E2K_OPND_CONST;
      o->arg = strtol (p + 1, (char **) &p, 10);
      o->mask = HOST_WIDE_INT_M1U;
      if (*p == '&')
	o->mask = strtoull (p + 1, (char **) &p, 0);
      if (*p == '!')
	o->lit8 = true, p++;
      if (*p == ':')
	{
	  o->kind = E2K_OPND_SUFFIX;
	  while (*p != '}')
	    p++;
	}
    }
  gcc_assert (*p == '}');
  return p + 1;
}

static void
e2k_bop_parse (const struct e2k_bop *b, struct e2k_bop_parsed *r)
{
  memset (r, 0, sizeof *r);
  const char *t = b->trace;
  if (b->kind == E2K_BK_PACK || b->kind >= E2K_BK_LD_SM)
    return;
  /* The mnemonic and its suffix.  */
  const char *p = t;
  size_t i = 0;
  while (*p && *p != ' ' && *p != '{')
    r->mnem[i++] = *p++;
  r->mnem[i] = 0;
  if (*p == '{')
    {
      r->sfx = ++r->n;
      p = e2k_bop_parse_brace (p, &r->op[r->sfx]);
      i = 0;
      while (*p && *p != ' ')
	r->tail[i++] = *p++;
      r->tail[i] = 0;
    }
  /* The operands, up to "ret".  */
  while (*p)
    {
      while (*p == ' ' || *p == ',')
	p++;
      if (!*p || startswith (p, "ret"))
	break;
      struct e2k_bopnd *o = &r->op[++r->n];
      if (*p == 'a')
	{
	  o->kind = E2K_OPND_ARG;
	  o->arg = strtol (p + 1, (char **) &p, 10);
	}
      else if (*p == '{')
	p = e2k_bop_parse_brace (p, o);
      else
	{
	  o->kind = E2K_OPND_FIXED;
	  o->val = strtoull (p, (char **) &p, 0);
	}
    }
  gcc_assert (r->n >= 1 && r->n <= 4);
}

static tree
e2k_btype_tree (enum e2k_btype t)
{
  switch (t)
    {
    case E2K_BT_VOID:
      return void_type_node;
    case E2K_BT_U32:
      return unsigned_type_node;
    case E2K_BT_U64:
      return long_long_unsigned_type_node;
    case E2K_BT_I64:
      return long_integer_type_node;
    case E2K_BT_V2DI:
      /* long long __attribute__ ((vector_size (16))), lcc's v2di.  */
      return build_vector_type (long_long_integer_type_node, 2);
    case E2K_BT_XF:
      return long_double_type_node;
    case E2K_BT_PTR:
      return ptr_type_node;
    case E2K_BT_CPTR:
      return const_ptr_type_node;
    default:
      gcc_unreachable ();
    }
}

static void
e2k_init_op_builtins (void)
{
  unsigned n = ARRAY_SIZE (e2k_bops);
  e2k_bop_info = XCNEWVEC (struct e2k_bop_parsed, n);
  for (unsigned i = 0; i < n; i++)
    {
      const struct e2k_bop *b = &e2k_bops[i];
      e2k_bop_parse (b, &e2k_bop_info[i]);
      if (strcmp (b->name, "puttagd") == 0)
	e2k_bop_puttagd = i;
      else if (strcmp (b->name, "puttagqp") == 0)
	e2k_bop_puttagqp = i;
      tree args = void_list_node;
      for (int k = 3; k >= 0; k--)
	if (b->args[k] != E2K_BT_NONE)
	  args = tree_cons (NULL_TREE, e2k_btype_tree (b->args[k]), args);
      tree type = build_function_type (e2k_btype_tree (b->ret), args);
      char *name = ACONCAT (("__builtin_e2k_", b->name, NULL));
      e2k_bop_decls[i]
	= add_builtin_function (name, type, E2K_BUILTIN_MAX + i,
				BUILT_IN_MD, NULL, NULL_TREE);
    }
}

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
  { "elbrus", 1, 1 },
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
  if (code < E2K_BUILTIN_MAX)
    return e2k_builtins[code];
  if (code - E2K_BUILTIN_MAX < ARRAY_SIZE (e2k_bops))
    return e2k_bop_decls[code - E2K_BUILTIN_MAX];
  return error_mark_node;
}

/* The operation builtin insn INSN's index in e2k_bops.  */
static int
e2k_bop_index (rtx_insn *insn)
{
  rtx src = SET_SRC (PATTERN (insn));
  return INTVAL (XVECEXP (src, 0, XVECLEN (src, 0) - 1));
}

bool
e2k_bop_insn_p (rtx_insn *insn)
{
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) != SET || GET_CODE (SET_SRC (pat)) != UNSPEC)
    return false;
  int u = XINT (SET_SRC (pat), 1);
  return u == UNSPEC_E2K_BOP || u == UNSPEC_E2K_BOPP;
}

int
e2k_bop_attr_type (rtx_insn *insn)
{
  return e2k_bops[e2k_bop_index (insn)].type;
}

/* Literal syllables of an operation builtin insn, as e2k_insn_lits counts
   them: constants up to 15 and those in the mnemonic or an ALES field
   take none.  */
int
e2k_bop_lits (rtx_insn *insn)
{
  const struct e2k_bop_parsed *p = &e2k_bop_info[e2k_bop_index (insn)];
  rtx src = SET_SRC (PATTERN (insn));
  int n = 0;
  for (int k = 1; k <= p->n; k++)
    {
      rtx x = XVECEXP (src, 0, k - 1);
      if (!CONST_INT_P (x) || k == p->sfx || p->op[k].lit8)
	continue;
      HOST_WIDE_INT v = INTVAL (x);
      n += v >= 0 && v < 16 ? 0 : v == (int32_t) v ? 1 : 2;
    }
  return n;
}

/* Whether the third source of operation builtin INDEX (a const_int) is
   a literal in an ALES field (e2k_bop3l), not a register.  */
bool
e2k_bop_lit8_p (rtx index)
{
  const struct e2k_bop_parsed *p = &e2k_bop_info[INTVAL (index)];
  return p->n >= 3 && p->op[p->n].lit8;
}

/* The template of an operation builtin insn with NSRC sources.  */
const char *
e2k_bop_output (rtx *operands, int nsrc)
{
  static char buf[128];
  const struct e2k_bop_parsed *p
    = &e2k_bop_info[INTVAL (operands[nsrc + 1])];
  int len = snprintf (buf, sizeof buf, "%s", p->mnem);
  if (p->sfx)
    len += snprintf (buf + len, sizeof buf - len, "0x%02x%s",
		     (int) (INTVAL (operands[p->sfx]) & 0xff), p->tail);
  const char *sep = "\t";
  for (int k = 1; k <= p->n; k++)
    if (k != p->sfx)
      {
	len += snprintf (buf + len, sizeof buf - len, "%s%%%d", sep, k);
	sep = ", ";
      }
  snprintf (buf + len, sizeof buf - len, "%s%%0", sep);
  return buf;
}

/* TEMPLATE, a speculative operation's: ",sm" after the channel
   (e2k_asm_output_opcode).  */
const char *
e2k_output_sm (const char *tmpl)
{
  e2k_cur_sm = true;
  return tmpl;
}

/* Argument K of builtin call EXP of type T, in a register of the mode
   the operations read it in.  */
static rtx
e2k_bop_arg (tree exp, int k, enum e2k_btype t)
{
  tree a = CALL_EXPR_ARG (exp, k);
  rtx x = expand_normal (a);
  machine_mode m = TYPE_MODE (TREE_TYPE (a));
  switch (t)
    {
    case E2K_BT_V2DI:
      if (GET_MODE (x) != V2DImode)
	x = gen_lowpart (V2DImode, force_reg (m, x));
      return force_reg (V2DImode, x);
    case E2K_BT_XF:
      return force_reg (XFmode, x);
    default:
      return force_reg (DImode, convert_modes (DImode, m, x, 1));
    }
}

/* The constant argument K of builtin call EXP, or 0 after an error.  */
static unsigned HOST_WIDE_INT
e2k_bop_const (tree exp, int k, const struct e2k_bop *b)
{
  tree a = CALL_EXPR_ARG (exp, k);
  if (TREE_CODE (a) != INTEGER_CST)
    {
      error_at (EXPR_LOCATION (exp), "argument %d of %<__builtin_e2k_%s%> "
		"must be a constant", k + 1, b->name);
      return 0;
    }
  return TREE_INT_CST_LOW (a);
}

/* pshufh (a, imm) is pshufb 0, a, mask: halfword k of the result is
   halfword (imm >> 2k) & 3 of a (relcc2 lcc-builtins.md).  */
static unsigned HOST_WIDE_INT
e2k_pshufh_mask (unsigned HOST_WIDE_INT imm)
{
  unsigned HOST_WIDE_INT m = 0;
  for (int k = 0; k < 4; k++)
    {
      unsigned h = (imm >> (2 * k)) & 3;
      m |= (unsigned HOST_WIDE_INT) (2 * h) << (16 * k);
      m |= (unsigned HOST_WIDE_INT) (2 * h + 1) << (16 * k + 8);
    }
  return m;
}

/* Emit operation builtin I's insn into a new register of mode M on the
   sources OPS[1..N].  */
static rtx
e2k_emit_bop (unsigned i, machine_mode m, rtx *ops, int n)
{
  rtx d = gen_reg_rtx (m);
  rtx idx = GEN_INT (i);
  switch (n)
    {
    case 1:
      emit_insn (gen_e2k_bop1 (m, d, ops[1], idx));
      break;
    case 2:
      emit_insn (gen_e2k_bop2 (m, d, ops[1], ops[2], idx));
      break;
    case 3:
      if (CONST_INT_P (ops[3]))
	emit_insn (gen_e2k_bop3l (m, d, ops[1], ops[2], ops[3], idx));
      else
	emit_insn (gen_e2k_bop3 (m, d, ops[1], ops[2], ops[3], idx));
      break;
    case 4:
      if (CONST_INT_P (ops[4]))
	{
	  /* qplog_lt3 (v7).  */
	  sorry ("%<__builtin_e2k_%s%>", e2k_bops[i].name);
	  break;
	}
      emit_insn (gen_e2k_bop4 (m, d, ops[1], ops[2], ops[3], ops[4], idx));
      break;
    default:
      gcc_unreachable ();
    }
  return d;
}

/* An lcc load or store builtin's address: (char *) P + OFF.  */
static rtx
e2k_bop_addr (tree exp, bool off)
{
  rtx p = force_reg (Pmode, expand_normal (CALL_EXPR_ARG (exp, 0 + 0)));
  if (off)
    {
      rtx o = expand_normal (CALL_EXPR_ARG (exp, 1));
      p = force_reg (Pmode, gen_rtx_PLUS (Pmode, p,
					  convert_modes (Pmode, DImode, o, 0)));
    }
  return p;
}

static rtx
e2k_bop_mem (machine_mode m, rtx addr)
{
  rtx mem = gen_rtx_MEM (m, addr);
  set_mem_alias_set (mem, 0);
  return mem;
}

/* Expand call EXP of operation builtin I.  */
static rtx
e2k_expand_bop (unsigned i, tree exp)
{
  const struct e2k_bop *b = &e2k_bops[i];
  const struct e2k_bop_parsed *p = &e2k_bop_info[i];
  machine_mode rm = b->ret == E2K_BT_V2DI ? V2DImode : DImode;
  if (e2k_arch < b->iset)
    {
      error_at (EXPR_LOCATION (exp), "%<__builtin_e2k_%s%> needs "
		"%<-march=elbrus-v%d%> or later", b->name, b->iset);
      return b->ret == E2K_BT_VOID ? const0_rtx : CONST0_RTX (rm);
    }
  rtx ops[6], r;
  switch (b->kind)
    {
    case E2K_BK_PACK:
      r = gen_reg_rtx (V2DImode);
      emit_insn (gen_e2k_qppack (V2DImode, r,
				 e2k_bop_arg (exp, 0, E2K_BT_U64),
				 e2k_bop_arg (exp, 1, E2K_BT_U64)));
      return r;
    case E2K_BK_LD_SM:
    case E2K_BK_LD_CLEARTAG:
      {
	rtx a = e2k_bop_addr (exp, true);
	bool clear = b->kind == E2K_BK_LD_CLEARTAG;
	if (b->ret != E2K_BT_V2DI)
	  {
	    r = gen_reg_rtx (DImode);
	    emit_insn (gen_e2k_ldsmdi (r, e2k_bop_mem (DImode, a)));
	    if (!clear)
	      return r;
	    ops[1] = r;
	    ops[2] = const0_rtx;
	    return e2k_emit_bop (e2k_bop_puttagd, DImode, ops, 2);
	  }
	/* As lcc: two ldd,sm and a speculative qppackdl, since ldqp
	   wants 16-byte alignment (relcc2 lcc-builtins-check.yaml).  */
	rtx hi = gen_reg_rtx (DImode), lo = gen_reg_rtx (DImode);
	emit_insn (gen_e2k_ldsmdi (hi, e2k_bop_mem (DImode,
						    plus_constant (Pmode, a, 8))));
	emit_insn (gen_e2k_ldsmdi (lo, e2k_bop_mem (DImode, a)));
	r = gen_reg_rtx (V2DImode);
	emit_insn (gen_e2k_qppack_sm (r, hi, lo));
	if (!clear)
	  return r;
	ops[1] = r;
	ops[2] = const0_rtx;
	return e2k_emit_bop (e2k_bop_puttagqp, V2DImode, ops, 2);
      }
    case E2K_BK_ST:
      {
	machine_mode m = (b->args[0] == E2K_BT_V2DI ? V2DImode
			  : b->args[0] == E2K_BT_U32 ? SImode : DImode);
	rtx v = e2k_bop_arg (exp, 0, b->args[0]);
	if (m == SImode)
	  v = gen_lowpart (SImode, v);
	rtx mem = e2k_bop_mem (m, force_reg (Pmode,
					     expand_normal (CALL_EXPR_ARG (exp, 1))));
	/* Non-temporal: MAS 0x60 from v5, a plain store before
	   (relcc2 lcc-builtins.md, "Memory helpers").  */
	if (e2k_arch >= 5)
	  emit_insn (gen_e2k_stmas (m, mem, v, GEN_INT (0x60)));
	else
	  emit_move_insn (mem, v);
	return const0_rtx;
      }
    case E2K_BK_PST:
      {
	rtx v = e2k_bop_arg (exp, 0, E2K_BT_V2DI);
	rtx a = force_reg (Pmode, expand_normal (CALL_EXPR_ARG (exp, 1)));
	rtx m = e2k_bop_arg (exp, 2, E2K_BT_U32);
	emit_insn (gen_e2k_stmqp (a, v, m));
	return const0_rtx;
      }
    default:
      break;
    }

  for (int k = 1; k <= p->n; k++)
    {
      const struct e2k_bopnd *o = &p->op[k];
      switch (o->kind)
	{
	case E2K_OPND_ARG:
	  if (b->kind == E2K_BK_FX && b->args[o->arg] == E2K_BT_XF)
	    {
	      ops[k] = gen_reg_rtx (DImode);
	      emit_insn (gen_e2k_xf_pack (ops[k],
					  e2k_bop_arg (exp, o->arg,
						       E2K_BT_XF)));
	    }
	  else
	    ops[k] = e2k_bop_arg (exp, o->arg, b->args[o->arg]);
	  break;
	case E2K_OPND_CONST:
	case E2K_OPND_SUFFIX:
	  {
	    unsigned HOST_WIDE_INT v = e2k_bop_const (exp, o->arg, b);
	    if (b->kind == E2K_BK_SHUFH)
	      v = e2k_pshufh_mask (v);
	    ops[k] = gen_int_mode (v & o->mask, DImode);
	    break;
	  }
	case E2K_OPND_FIXED:
	  ops[k] = gen_int_mode (o->val, DImode);
	  break;
	case E2K_OPND_VEC:
	  {
	    rtvec v = gen_rtvec (2, gen_int_mode (o->val, DImode),
				 gen_int_mode (o->val2, DImode));
	    ops[k] = force_reg (V2DImode, gen_rtx_CONST_VECTOR (V2DImode, v));
	    break;
	  }
	}
    }

  /* What each place takes (e2k-builtins.md): src1 a register or a 5-bit
     literal, src3 a register, which lcc loads a constant into first
     (pshufb's mask).  */
  {
    int first = p->sfx ? 2 : 1, nsrc = p->n - (p->sfx != 0);
    if (nsrc >= 2 && CONST_INT_P (ops[first])
	&& !IN_RANGE (INTVAL (ops[first]), 0, 31))
      ops[first] = force_reg (DImode, ops[first]);
    if (nsrc == 3 && CONST_INT_P (ops[p->n]) && !p->op[p->n].lit8)
      ops[p->n] = force_reg (DImode, ops[p->n]);
  }

  if (b->kind == E2K_BK_PRED)
    {
      machine_mode am = b->args[0] == E2K_BT_V2DI ? V2DImode : DImode;
      r = gen_reg_rtx (DImode);
      emit_insn (gen_e2k_boppred (am, r, ops[1], ops[2], GEN_INT (i)));
      return gen_lowpart (SImode, r);
    }
  if (b->kind == E2K_BK_FX)
    {
      rtx t = e2k_emit_bop (i, DImode, ops, p->n);
      r = gen_reg_rtx (XFmode);
      emit_insn (gen_e2k_xf_unpack (r, t));
      return r;
    }
  r = e2k_emit_bop (i, rm, ops, p->n);
  if (b->ret == E2K_BT_U32)
    return gen_lowpart (SImode, r);
  return r;
}

rtx
e2k_expand_builtin (tree exp, rtx target, rtx, machine_mode mode, int)
{
  tree fndecl = TREE_OPERAND (CALL_EXPR_FN (exp), 0);
  unsigned code = DECL_MD_FUNCTION_CODE (fndecl);
  if (code >= E2K_BUILTIN_MAX)
    return e2k_expand_bop (code - E2K_BUILTIN_MAX, exp);
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
