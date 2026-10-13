/* List scheduler hooks for the Elbrus (E2K) port (haifa-sched,
   run by sched-ebb from e2k_reorg): dependence costs from
   spec/isa/timing.md, issue, control and data speculation (ld,sm, lock
   and check loads; spec/isa/speculation.md), if-conversion's
   predicates, and the output of AAU and speculative loads.
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

/* ------------------------------------------------------------------ */
/* Scheduling and bundling                                             */
/* ------------------------------------------------------------------ */

/* Packed integer operations (e2k-vect.md).  */
bool
e2k_packed_type_p (enum attr_type t)
{
  return t == TYPE_PINT || t == TYPE_PINT14 || t == TYPE_PMUL
	 || t == TYPE_PANY;
}

/* Which divider operation INSN (of type fdiv) is, for its timing: 1
   fdivs, 2 fsqrts, 3 fsqrtid, 4 fsqrttd, 0 the others (fdivd), also
   under a predicate.  */
int
e2k_fdiv_kind (rtx_insn *insn)
{
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) == COND_EXEC)
    pat = COND_EXEC_CODE (pat);
  if (GET_CODE (pat) == PARALLEL)
    pat = XVECEXP (pat, 0, 0);
  if (GET_CODE (pat) != SET)
    return 0;
  rtx src = SET_SRC (pat);
  if (GET_CODE (src) == UNSPEC && XINT (src, 1) == UNSPEC_FSQRTI)
    return 3;
  if (GET_CODE (src) == UNSPEC && XINT (src, 1) == UNSPEC_FSQRTT)
    return 4;
  if (GET_CODE (src) == SQRT)
    return GET_MODE (src) == SFmode ? 2 : 4;
  if (GET_CODE (src) == DIV && GET_MODE (src) == SFmode)
    return 1;
  return 0;
}

int
e2k_insn_lits (rtx_insn *insn)
{
  /* A pipelined loop's check load is a jump (its rbranch has a label)
     with a load's literals.  */
  if (!INSN_P (insn) || CALL_P (insn)
      || (JUMP_P (insn)
	  && !(recog_memoized (insn) >= 0
	       && get_attr_type (insn) == TYPE_LDCHK)))
    return 0;
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) == USE || GET_CODE (pat) == CLOBBER
      || GET_CODE (pat) == ASM_INPUT || asm_noperands (pat) >= 0)
    return 0;
  if (recog_memoized (insn) < 0)
    return 0;
  /* A predicated operation's literals are its operation's (a field
     insertion's descriptor, printed from its operands, too).  */
  bool pred = GET_CODE (pat) == COND_EXEC;
  if (pred)
    pat = COND_EXEC_CODE (pat);
  if (INSN_CODE (insn) == CODE_FOR_e2k_disp
      || INSN_CODE (insn) == CODE_FOR_e2k_disp_label
      || INSN_CODE (insn) == CODE_FOR_e2k_ldisp_apb)
    return 0;
  {
    enum attr_type t = get_attr_type (insn);
    if (t == TYPE_MOVA || t == TYPE_AAU || t == TYPE_BAP)
      return 0;
  }
  /* Not an AND under a predicate: *anddi3_lowmask isn't predicable, so
     that is the plain andd with its 64-bit mask (sqlite's randomFunc,
     "-(r & LARGEST_INT64)").  */
  if (e2k_field_insn_p (pat) && !(pred && GET_CODE (SET_SRC (pat)) == AND))
    return 1;
  /* An FP negation or absolute value: the sign bit is in the template,
     an xor or andn with 0x80000000, 0x8000000000000000 or (long double)
     0x8000.  */
  if (GET_CODE (pat) == SET
      && (GET_CODE (SET_SRC (pat)) == NEG || GET_CODE (SET_SRC (pat)) == ABS))
    {
      machine_mode m = GET_MODE (SET_SRC (pat));
      if (m == SFmode || m == XFmode)
	return 1;
      if (m == DFmode)
	return 2;
    }
  /* An AAU store's literal is its byte offset, if any.  */
  if (e2k_staa_p (pat))
    return XVECEXP (XEXP (SET_DEST (pat), 0), 0, 2) != const0_rtx;

  int n = 0;
  subrtx_var_iterator::array_type array;
  FOR_EACH_SUBRTX_VAR (iter, array, pat, ALL)
    {
      rtx x = *iter;
      switch (GET_CODE (x))
	{
	case CONST_INT:
	  {
	    HOST_WIDE_INT v = INTVAL (x);
	    if (v >= 0 && v < 16)
	      ;
	    else if (v == (int32_t) v)
	      n += 1;
	    else
	      n += 2;
	    break;
	  }
	case CONST_DOUBLE:
	  n += GET_MODE_SIZE (GET_MODE (x)) > 4 ? 2 : 1;
	  break;
	case CONST_VECTOR:
	  {
	    rtx d = simplify_subreg (DImode, x, GET_MODE (x), 0);
	    HOST_WIDE_INT v = d ? INTVAL (d) : -1;
	    n += v >= 0 && v < 16 ? 0 : v == (int32_t) v ? 1 : 2;
	    iter.skip_subrtxes ();
	    break;
	  }
	case UNSPEC:
	  if (e2k_reloc_unspec_p (x))
	    {
	      n += (XINT (x, 1) == UNSPEC_GOTOFF
		    || XINT (x, 1) == UNSPEC_TLS_LE) ? 2 : 1;
	      iter.skip_subrtxes ();
	    }
	  break;
	case NEG:
	case ABS:
	  /* negsf2/absdf2 etc. print the sign mask as a literal.  */
	  if (GET_MODE (x) == SFmode)
	    n += 1;
	  else if (GET_MODE (x) == DFmode)
	    n += 2;
	  break;
	case SYMBOL_REF:
	  n += 2;
	  break;
	/* A check load's rbranch target is CS0's.  */
	case LABEL_REF:
	  n += JUMP_P (insn) ? 0 : 2;
	  break;
	case CONST:
	  n += 2;
	  iter.skip_subrtxes ();
	  break;
	default:
	  break;
	}
    }
  return MIN (n, 2);
}

static void
e2k_note_mem_store (rtx x, const_rtx, void *data)
{
  if (MEM_P (x))
    *(bool *) data = true;
}

static bool
e2k_mem_access_p (rtx_insn *insn)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
    if (MEM_P (*iter))
      return true;
  return false;
}

/* The memory reference of a load or store, or NULL.  */
static rtx
e2k_insn_mem (rtx_insn *insn)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
    if (MEM_P (*iter))
      return const_cast<rtx> (*iter);
  return NULL_RTX;
}

/* Whether store PRO and load CON may touch one doubleword: the same
   address apart from a constant less than 8 bytes.  On v6 only a load
   of bytes the store wrote pays (spec/isa/timing.md, "Elbrus-2C3"), so
   there their bytes must overlap.  */
static bool
e2k_same_dword_p (rtx_insn *pro, rtx_insn *con)
{
  rtx a = e2k_insn_mem (pro), b = e2k_insn_mem (con);
  if (!a || !b)
    return false;
  poly_int64 pa, pb;
  HOST_WIDE_INT oa, ob;
  rtx ba = strip_offset (XEXP (a, 0), &pa);
  rtx bb = strip_offset (XEXP (b, 0), &pb);
  if (!pa.is_constant (&oa) || !pb.is_constant (&ob))
    return true;
  if (!rtx_equal_p (ba, bb))
    return false;
  HOST_WIDE_INT sa = GET_MODE_SIZE (GET_MODE (a));
  HOST_WIDE_INT sb = GET_MODE_SIZE (GET_MODE (b));
  if (E2K_LAT6 && sa > 0 && sb > 0)
    return oa < ob + sb && ob < oa + sa;
  return oa - ob < 8 && ob - oa < 8;
}

static bool e2k_ov_insn_p (rtx_insn *);


/* The condition a load had before e2k_unpredicate_loads ran it without
   one, by insn UID: the DAM may still move it above stores, with its
   check under the condition (a check under a false predicate does
   nothing, so its address need not be valid there; relcc2 findings
   I29).  */
vec<rtx> e2k_unpred_cond;

rtx
e2k_unpred_cond_of (const rtx_insn *insn)
{
  /* Only in machine reorg, which fills it and empties it at its end:
     sched1 of the next function reuses the UIDs.  */
  if (!reload_completed)
    return NULL_RTX;
  unsigned uid = INSN_UID (insn);
  return uid < e2k_unpred_cond.length () ? e2k_unpred_cond[uid] : NULL_RTX;
}

void
e2k_set_unpred_cond (rtx_insn *insn, rtx cond)
{
  unsigned uid = INSN_UID (insn);
  if (uid >= e2k_unpred_cond.length ())
    e2k_unpred_cond.safe_grow_cleared (uid + 64);
  e2k_unpred_cond[uid] = copy_rtx (cond);
}

/* Whether INSN reads or writes a CTPR.  */
static bool
e2k_mentions_ctpr_p (rtx_insn *insn)
{
  for (unsigned r = CTPR1_REGNUM; r <= CTPR3_REGNUM; r++)
    if (reg_mentioned_p (gen_rtx_REG (DImode, r), PATTERN (insn)))
      return true;
  return false;
}

/* Every operation in a wide instruction reads the registers as they were
   before it, and two operations can't write one register in the same
   wide instruction.  Memory is not as simple (4C, findings I9, I12): a
   load in the wide instruction of a store to its address reads the old
   value, except that a load in ALC5 sees a store in ALC2.  gas chooses
   the channels, so a load and a store that may touch the same memory
   never share a wide instruction, in either order.  GCC's scheduler
   assumes sequential order inside a cycle unless told otherwise, so
   output dependences and any dependence between a store and another
   memory access cost a cycle.  The dependence need not be a true one:
   once a block has many memory accesses, sched-deps flushes its lists
   and later loads get only an anti dependence on the flushing store.  */
int
e2k_adjust_cost (rtx_insn *con, int dep_type, rtx_insn *pro, int cost,
		 unsigned int)
{
  /* A taken transfer's whole wide instruction runs, and a call's too
     before the callee does.  So what depends on a call, and what depends
     on a jump because it has no speculative form or sets a register live
     where the jump goes, can't share their instruction.  Rewriting what
     the jump only reads (its predicate) can: the jump reads the old
     value.  e2k_spec_mark makes what does share it speculative, and
     only with control speculation (-mcontrol-spec): without it nothing
     shares (SQLite's createCollation, -mno-control-spec: a load of
     pColl->xCmp in the instruction of the jump that skips it when pColl
     is null, unmarked).  */
  if ((JUMP_P (pro) || CALL_P (pro)) && INSN_P (con) && cost < 1
      && (CALL_P (pro) || !e2k_control_spec || e2k_spec_kind (con) == 0
	  || e2k_spec_sets_live_p (con, pro)))
    return 1;
  /* A read of the FP state is volatile too, so everything after it
     depends on it at its 11 cycles (e2k_rrs); only a reader of its value
     needs that, and a write of the state, which waits for the read.
     Other reads issue one a cycle (timing.md, "State registers").  */
  if (INSN_P (pro) && recog_memoized (pro) == CODE_FOR_e2k_rrs
      && INSN_P (con) && !CALL_P (con) && !JUMP_P (con)
      && recog_memoized (con) != CODE_FOR_e2k_rws
      && !reg_overlap_mentioned_p (SET_DEST (PATTERN (pro)), PATTERN (con)))
    return MIN (cost, 1);
  /* The prologue's getsp is volatile, so everything after it depends on
     it at its latency; only what reads the new stack pointer needs that.
     lcc's prologues load arguments beside it.  The blockage after it
     resets the scheduler's register dependences, so a user of the stack
     pointer waits for getsp's 2 cycles from the blockage.  */
  if (e2k_prologue_prep_p && INSN_P (pro) && INSN_P (con)
      && !CALL_P (con) && !JUMP_P (con) && prologue_contains (pro))
    {
      int code = recog_memoized (pro);
      if (code == CODE_FOR_e2k_getsp
	  && !reg_mentioned_p (stack_pointer_rtx, PATTERN (con)))
	return 0;
      if (code == CODE_FOR_blockage && frame_pointer_needed == 0
	  && reg_mentioned_p (stack_pointer_rtx, PATTERN (con)))
	return MAX (cost, 2);
    }
  /* Operations in the wide instruction with setwd already use the new
     window (spec/abi/registers.md), as lcc's prologues do; %b[] in the
     one with setbn still uses the old rotating base.  setwd is volatile,
     so everything after it depends on it, and on the prologue's
     blockage after it, which only keeps the body below the frame's
     setup (registers carry the rest).  */
  if (INSN_P (pro) && (recog_memoized (pro) == CODE_FOR_e2k_setwd
			|| recog_memoized (pro) == CODE_FOR_blockage
			|| recog_memoized (pro) == CODE_FOR_e2k_setbn_enter
			|| recog_memoized (pro) == CODE_FOR_e2k_setbn_leave)
      && INSN_P (con) && !CALL_P (con) && !JUMP_P (con)
      && (!e2k_mentions_ctpr_p (con)
	  /* A disp or the return's prepare may share the prologue's
	     setwd, as in lcc's prologues: they start a cycle earlier
	     (one prepare a wide instruction).  */
	  || (e2k_prologue_prep_p
	      && (recog_memoized (pro) == CODE_FOR_e2k_setwd
		  || (recog_memoized (pro) == CODE_FOR_blockage
		      && prologue_contains (pro))))))
    {
      bool b = false;
      subrtx_iterator::array_type array;
      FOR_EACH_SUBRTX (iter, array, PATTERN (con), NONCONST)
	if (REG_P (*iter) && (B_REGNO_P (REGNO (*iter))
			      || BX_REGNO_P (REGNO (*iter))))
	  b = true;
      return b ? MAX (cost, 1) : 0;
    }
  /* rwd %lsr: only the loop's end reads %lsr, 4 cycles later
     (e2k_output_lsr_wait); what follows it may share its wide
     instruction, as lcc's AAU setup does.  But it is a barrier, which
     carries the dependences of what comes after it on what came before
     (sched-deps): a transfer, or a read of a CTPR, may depend on a
     prepare before it, and must not share that prepare's instruction.  */
  if (dep_type == REG_DEP_TRUE && INSN_P (pro)
      && e2k_rwd_lsr_p (pro))
    {
      bool ctpr = JUMP_P (con) || CALL_P (con) || e2k_mentions_ctpr_p (con);
      return ctpr ? MAX (MIN (cost, 2), 1) : 0;
    }
  if (INSN_P (pro) && INSN_P (con)
      && recog_memoized (pro) >= 0 && recog_memoized (con) >= 0)
    {
      enum attr_type pt = get_attr_type (pro), ct = get_attr_type (con);
      /* AAU writes are barriers to each other only to keep their order;
	 two fit a wide instruction (ALC2 and ALC5).  */
      if (pt == TYPE_AAU && ct == TYPE_AAU)
	return 0;
      /* Nor need what doesn't touch memory or the AAU wait for one: the
	 next base into the temporary goes in the AAU write's instruction,
	 which reads the old one (NPB FT's butterfly set its 8 descriptors
	 through one register in 16 wide instructions, against 8; its
	 setup ran every 16 elements).  */
      if (e2k_aau_setup_war && pt == TYPE_AAU
	  && (ct == TYPE_ALU || ct == TYPE_ALU14 || ct == TYPE_ALU0134
	      || ct == TYPE_DISP)
	  && !volatile_insn_p (PATTERN (con)))
	{
	  /* The program's ldisp too, which bap then waits 5 cycles for:
	     those go by during the writes.  */
	  rtx cs = single_set (con);
	  if (cs && REG_P (SET_DEST (cs)) && !MEM_P (SET_SRC (cs)))
	    return 0;
	}
      /* fmax and fmin: 2 cycles, 2 more to an integer operation
	 (spec/isa/timing.md).  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_FCVT)
	if (rtx ps = single_set (pro))
	  if (GET_CODE (SET_SRC (ps)) == UNSPEC
	      && (XINT (SET_SRC (ps), 1) == UNSPEC_FMAX
		  || XINT (SET_SRC (ps), 1) == UNSPEC_FMIN))
	    return cost == 4 ? 2 : cost - 2;
      /* A conversion's result read in another format than the one it
	 produces arrives later: a double or 64-bit integer read as a
	 single 5, a 64-bit integer as a double 5, a single as a double 6
	 (spec/isa/timing.md, "Formats").  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_FCVT && cost == 4)
	if (rtx ps = single_set (pro))
	  if (REG_P (SET_DEST (ps)))
	    {
	      machine_mode pm = GET_MODE (SET_DEST (ps));
	      rtx pd = SET_DEST (ps);
	      rtx cs = single_set (con);
	      int lat = cost;
	      subrtx_iterator::array_type array;
	      if (cs)
		FOR_EACH_SUBRTX (iter, array, SET_SRC (cs), NONCONST)
		  if (REG_P (*iter) && REGNO (*iter) == REGNO (pd))
		    {
		      machine_mode cm = GET_MODE (*iter);
		      if (cm == pm || GET_MODE_SIZE (cm) > 8)
			continue;
		      lat = MAX (lat, (cm == DFmode && GET_MODE_SIZE (pm) == 4)
				      ? 6 : 5);
		    }
	      return lat;
	    }
      /* A conditional ct waits for its disp only 2 cycles when not
	 taken; taken, 5 minus the distance, still less than an ibranch
	 (spec/isa/control-transfer.md, "Costs").  Don't stretch the
	 fall-through path for it (e2k_prepare_branches).  An
	 unconditional one is always taken: it waits the whole 5.  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_DISP && ct == TYPE_CT
	  && (!e2k_uncond_ct_cost || !JUMP_P (con) || any_condjump_p (con)))
	return MIN (cost, 2);
      /* A barrier after a disp (sched-deps makes it depend on every set
	 before it) that doesn't read its CTPR needn't wait for the
	 prepare: setbn_leave on a pipelined loop's way out, which
	 e2k_lift_prepares puts disps above, the AAU setup of a loop.  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_DISP
	  && volatile_insn_p (PATTERN (con)))
	if (rtx s = single_set (pro))
	  if (!reg_overlap_mentioned_p (SET_DEST (s), PATTERN (con)))
	    return 0;
      /* Nor anything after a disp that is a barrier itself (the end of
	 array prefetch, e2k_apb_stop) and reads no CTPR: the barrier
	 carries the dependences on prepares before it.  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_DISP
	  && volatile_insn_p (PATTERN (pro))
	  && !JUMP_P (con) && !CALL_P (con) && !e2k_mentions_ctpr_p (con))
	return 0;
      /* A check after a jump (e2k_unpred_cond_deps): not in its wide
	 instruction, which runs also when it is taken.  */
      if (JUMP_P (pro) && ct == TYPE_LDCHK)
	return MAX (cost, 1);
      /* The same dependences of the load itself are for its check; the
	 lock load drops them, but only when it issues, and resolving one
	 earlier must not hold it back.  */
      if (dep_type == REG_DEP_TRUE && (ct == TYPE_LOAD || ct == TYPE_LDLOCK))
	if (rtx cond = e2k_unpred_cond_of (con))
	  if (JUMP_P (pro) ? !e2k_spec_sets_live_p (con, pro)
	      : reg_set_p (XEXP (cond, 0), pro))
	    return 0;
      /* A check waits for nothing of its lock load (relcc2 findings
	 I30), and its users wait 1 cycle for it: 2 cycles after the
	 lock, they get the lock's value in time.  */
      if (pt == TYPE_LDLOCK && ct == TYPE_LDCHK && dep_type == REG_DEP_TRUE)
	{
	  rtx pd = SET_DEST (XVECEXP (PATTERN (pro), 0, 0));
	  rtx cs = PATTERN (con);
	  if (GET_CODE (cs) == COND_EXEC)
	    cs = COND_EXEC_CODE (cs);
	  if (REG_P (pd) && GET_CODE (cs) == SET && REG_P (SET_DEST (cs))
	      && REGNO (SET_DEST (cs)) == REGNO (pd)
	      && !reg_overlap_mentioned_p (pd, XEXP (SET_SRC (cs), 1)))
	    return MIN (cost, 2);
	}
      /* No version can prepare and transfer through one CTPR in one wide
	 instruction: v1-v5 transfer to the old target, v6 falls through
	 (spec/isa/timing.md, "Elbrus-2C3 (v6)").  */
      if (dep_type == REG_DEP_ANTI
	  && (ct == TYPE_DISP || ct == TYPE_MOVCTP || ct == TYPE_RET)
	  && cost < 1
	  && (pt == TYPE_CT || pt == TYPE_CALL || pt == TYPE_BRANCH))
	return 1;
      /* A load of a doubleword stored in the wide instruction just before
	 gets its value about 8 cycles late; one cycle between them is
	 enough (spec/isa/timing.md, "Store to load").  Only for the same
	 doubleword, or in a loop copy for overlapping arrays, where they
	 mostly are (zlib's copies of distance 1: 40 cycles for 3 bytes);
	 a store and a load that merely may alias keep 1.  */
      if (dep_type == REG_DEP_TRUE && pt == TYPE_STORE
	  && (ct == TYPE_LOAD || ct == TYPE_LDLOCK || ct == TYPE_LDCHK)
	  && (e2k_same_dword_p (pro, con) || e2k_ov_insn_p (con)))
	return MAX (cost, 2);
    }
  if (cost >= 1)
    return cost;
  if (dep_type == REG_DEP_OUTPUT)
    return 1;
  if (!INSN_P (pro) || !INSN_P (con))
    return cost;
  bool pro_stores = false, con_stores = false;
  note_stores (pro, e2k_note_mem_store, &pro_stores);
  note_stores (con, e2k_note_mem_store, &con_stores);
  if ((pro_stores && e2k_mem_access_p (con))
      || (con_stores && e2k_mem_access_p (pro)))
    return 1;
  return cost;
}

int
e2k_issue_rate (void)
{
  return 8;
}

int
e2k_multipass_lookahead (void)
{
  return 4;
}

/* Cycle of each scheduled insn, for nop padding.  */
static int e2k_sched_clock;
vec<int> e2k_insn_clock;
/* The extended block each insn was scheduled in (from 1; 0: not by
   sched-ebb), so that bundling knows whose clocks compare.  */
vec<int> e2k_insn_ebb;
static int e2k_ebb_id;

void
e2k_sched_init_global (FILE *, int, int)
{
  e2k_insn_clock.truncate (0);
  e2k_insn_clock.safe_grow_cleared (get_max_uid () + 1);
  e2k_insn_ebb.truncate (0);
}

int
e2k_sched_reorder (FILE *, int, rtx_insn **, int *, int clock)
{
  e2k_sched_clock = clock;
  return e2k_issue_rate ();
}

int
e2k_sched_reorder2 (FILE *, int, rtx_insn **, int *n_readyp, int clock)
{
  e2k_sched_clock = clock;
  return *n_readyp;
}

void
e2k_sched_init (FILE *, int, int)
{
  e2k_ebb_id++;
}

int
e2k_variable_issue (FILE *, int, rtx_insn *insn, int more)
{
  unsigned uid = INSN_UID (insn);
  /* Also the checks of lock loads, which the scheduler makes as it goes
     (without a clock the bundler counted their cycle as a nop).  */
  if (uid >= e2k_insn_clock.length ())
    e2k_insn_clock.safe_grow_cleared (uid + 64);
  e2k_insn_clock[uid] = e2k_sched_clock + 1;
  if (uid >= e2k_insn_ebb.length ())
    e2k_insn_ebb.safe_grow_cleared (uid + 64);
  e2k_insn_ebb[uid] = e2k_ebb_id;
  if (GET_CODE (PATTERN (insn)) == USE || GET_CODE (PATTERN (insn)) == CLOBBER)
    return more;
  return more - 1;
}

vec<e2k_mark> e2k_marks;

bool
e2k_prints_p (rtx_insn *insn)
{
  if (!NONDEBUG_INSN_P (insn))
    return false;
  rtx pat = PATTERN (insn);
  if (GET_CODE (pat) == USE || GET_CODE (pat) == CLOBBER)
    return false;
  if (recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_GHOST)
    return false;
  return true;
}

bool
e2k_asm_insn_p (rtx_insn *insn)
{
  rtx pat = PATTERN (insn);
  return GET_CODE (pat) == ASM_INPUT || asm_noperands (pat) >= 0;
}

/* Insns that print their own wide instructions and braces.  */
bool
e2k_raw_insn_p (rtx_insn *insn)
{
  return (recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_RAW);
}

/* Whether INSN takes a wide instruction of its own: a multi-insn
   sequence.  */
bool
e2k_alone_p (rtx_insn *insn)
{
  return recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_MULTI;
}

/* Whether INSN prints a setwd, setbn or setbp: gas takes one of each per
   wide instruction, and code the scheduler didn't clock, such as one
   pipelined loop's way out followed by the next one's way in, puts two
   side by side (7-Zip's 7zUpdate.cpp).  */
bool
e2k_setwd_type_p (rtx_insn *insn)
{
  return recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_SETWD;
}

/* Whether INSN sets a CTPR that JUMP reads.  */
bool
e2k_writes_jump_reg_p (rtx_insn *insn, rtx_insn *jump)
{
  for (unsigned r = CTPR1_REGNUM; r <= CTPR3_REGNUM; r++)
    {
      rtx reg = gen_rtx_REG (DImode, r);
      if (reg_set_p (reg, insn)
	  && (reg_mentioned_p (reg, PATTERN (jump))
	      || (JUMP_LABEL (jump) && ANY_RETURN_P (JUMP_LABEL (jump))
		  && r == CTPR3_REGNUM)))
	return true;
    }
  return false;
}

/* Data speculation (see "Data speculation" in e2k.md).  */

/* Check loads print "rbranch .LDAMn" in their wide instruction; ".LDAMBn"
   follows the instruction (e2k_final_postscan_insn) and the stub
   ".LDAMn: ibranch .LDAMBn" goes at the end of the function
   (e2k_asm_function_epilogue).  When the check reloaded, the rbranch
   leaves the wide instruction after it unexecuted until the reload has
   landed: a consumer in the next instruction read the early value once
   on the 4C (first call of a function, a struct field just spilled).
   lcc pairs every check with an rbranch too.  */

/* An array prefetch read (e2k_mova<mode>): OPERANDS[1] the area (its
   program instruction), [2] the channel, [3] the element size, [4] the
   byte offset in the step, [5] whether it advances the area.  */
const char *
e2k_output_mova (rtx *operands)
{
  static char buf[80];
  int size = INTVAL (operands[3]);
  snprintf (buf, sizeof buf, "mova%s,%d\tarea=%d, ind=%d, am=%d, be=0, %%0",
	    size == 1 ? "b" : size == 2 ? "h" : size == 4 ? "w"
	    : size == 8 ? "d" : "qp",
	    (int) INTVAL (operands[2]), (int) INTVAL (operands[1]),
	    (int) INTVAL (operands[4]), (int) INTVAL (operands[5]));
  return buf;
}

/* An AAU store (OPERANDS as e2k_staa<mode> has them) of SIZE bytes,
   with its incr.  */
const char *
e2k_output_staa (rtx *operands, int size)
{
  static char buf[96];
  HOST_WIDE_INT lit = INTVAL (operands[3]);
  char off[32] = "";
  if (lit)
    snprintf (off, sizeof off, " + %#" PRIx64, (uint64_t) (uint32_t) lit);
  snprintf (buf, sizeof buf, "staa%s\t%%0, %%%%aad%d[ %%%%aasti%d%s ]\n"
	    "\tincr\t%%%%aaincr%d",
	    size == 1 ? "b" : size == 2 ? "h" : size == 4 ? "w"
	    : size == 8 ? "d" : "qp",
	    (int) INTVAL (operands[1]), (int) INTVAL (operands[2]), off,
	    (int) INTVAL (operands[4]));
  return buf;
}

/* Whether PAT is an AAU store's (e2k_staa<mode>).  */
bool
e2k_staa_p (rtx pat)
{
  if (GET_CODE (pat) != SET || !MEM_P (SET_DEST (pat)))
    return false;
  rtx a = XEXP (SET_DEST (pat), 0);
  return GET_CODE (a) == UNSPEC && XINT (a, 1) == UNSPEC_STAA;
}

/* A prefetch: speculative, unless the insn prints ",sm" already
   (e2k_asm_output_opcode), as the scheduler marks what it moves.  */
const char *
e2k_output_prefetch (rtx *operands)
{
  static char buf[48];
  int mas = e2k_prefetch_mas (INTVAL (operands[2]));
  int n = snprintf (buf, sizeof buf, "ldb%s\t%%a0, %%%%empty",
		    e2k_cur_sm ? "" : ",sm");
  if (mas)
    snprintf (buf + n, sizeof buf - n, ", mas=0x%x", mas);
  return buf;
}

/* The MAS of a prefetch of LOCALITY, as lcc gives it (spec/isa/
   timing.md, "Software prefetch"): 0x60 (fetched, kept nowhere), 0x40
   (the 8C2's L3), 0x20 (L2) for 0 to 2; for 3, none (L1) in code tuned
   for a CPU that hasn't the PREFETCH_EMPTY erratum (the 12C, 16C and
   2C3 rev 0 drop a prefetch to %empty without an L1-bypass MAS;
   hwbugs.md) or for v7, else 0x20.  */
int
e2k_prefetch_mas (int locality)
{
  switch (locality)
    {
    case 0:
      return 0x60;
    case 1:
      return 0x40;
    case 2:
      return 0x20;
    default:
      return e2k_tune == 4 || e2k_tune == 8 || e2k_arch >= 7 ? 0 : 0x20;
    }
}

/* Print a lock load (LOCK) or a check load.  */
const char *
e2k_output_spec_load (rtx *operands, bool lock)
{
  static char buf[64];
  rtx mem = operands[1];
  if (GET_CODE (mem) == ZERO_EXTEND)
    mem = XEXP (mem, 0);
  operands[2] = mem;
  char sz;
  switch (GET_MODE_SIZE (GET_MODE (mem)))
    {
    case 1: sz = 'b'; break;
    case 2: sz = 'h'; break;
    case 4: sz = 'w'; break;
    case 8: sz = 'd'; break;
    default: gcc_unreachable ();
    }
  /* Its ",sm" is in the template, also for a load e2k_unpredicate_loads
     marked.  */
  e2k_cur_sm = false;
  if (lock)
    snprintf (buf, sizeof buf, "ld%c,0,sm\t%%2, %%0, mas=0x4", sz);
  else
    {
      int n = ++e2k_dam_labelno;
      e2k_dam_pending.safe_push (n);
      e2k_dam_stubs.safe_push (n);
      snprintf (buf, sizeof buf,
		"ld%c,5\t%%2, %%0, mas=0x3%%?\n\trbranch\t.LDAM%d", sz, n);
    }
  return buf;
}

/* IFCVT_MODIFY_INSN: a disp under a predicate still runs (e2k_disp
   prints none, as lcc prepares a predicated call's callee
   unconditionally), so it may go under one only where nothing on the
   other way writes %ctpr1 otherwise.  With calls in both arms ce3 left
   the two calls, identical through %ctpr1, as one after both disps,
   and the second disp chose the callee: "if (f == 2) lng (...); else
   dbl (...)" always called dbl.  */
void
e2k_ifcvt_modify_insn (struct ce_if_block *ce_info, rtx *pattern,
		       rtx_insn *insn)
{
  if (!*pattern || !ce_info || recog_memoized (insn) != CODE_FOR_e2k_disp)
    return;
  basic_block bb = BLOCK_FOR_INSN (insn);
  basic_block other = (bb == ce_info->then_bb ? ce_info->else_bb
		       : bb == ce_info->else_bb ? ce_info->then_bb : NULL);
  if (!other)
    return;
  rtx ctpr = gen_rtx_REG (DImode, CTPR1_REGNUM);
  rtx_insn *o;
  FOR_BB_INSNS (other, o)
    if (NONDEBUG_INSN_P (o) && reg_set_p (ctpr, o)
	&& !(recog_memoized (o) == CODE_FOR_e2k_disp
	     && rtx_equal_p (SET_SRC (single_set (o)),
			     SET_SRC (single_set (insn)))))
      {
	*pattern = NULL_RTX;
	return;
      }
}

/* IFCVT_MODIFY_TESTS: no operations under the predicate of an FP
   compare, which reaches them 4 cycles after it (spec/isa/timing.md),
   unless an arm is estimated to run at least -mifcvt-fp-prob=N percent
   of the time: around a rare update (a new maximum) the branch costs
   nothing, while the predicated update makes the next iteration's
   compare wait for it; around a frequent one ("x = x < a[i] ? b[i] :
   x") the chain waits for the branch every time.  */
void
e2k_ifcvt_modify_tests (struct ce_if_block *ce_info, rtx *true_expr,
			rtx *false_expr)
{
  rtx t = *true_expr;
  if (!t || !REG_P (XEXP (t, 0)))
    return;
  /* Stores under a predicate only in integer code: in an FP loop
     predicated memory made the kernel stall (relcc2 findings I19;
     Linpack 7% slower), in integer code they turn branchy loops with
     stores in both arms into straight code (xz's binary tree walk).
     Loads in FP code too with -mifcvt-fp-loads: e2k_unpred_load_copies
     runs them early, as ld,sm, with only a copy under the predicate.  */
  bool mem = false, store = false, fp = false;
  for (basic_block arm : { ce_info->then_bb, ce_info->else_bb })
    if (arm)
      {
	rtx_insn *insn;
	FOR_BB_INSNS (arm, insn)
	  if (NONDEBUG_INSN_P (insn) && recog_memoized (insn) >= 0)
	    {
	      enum attr_type ty = get_attr_type (insn);
	      rtx set = single_set (insn);
	      mem |= ty == TYPE_LOAD || ty == TYPE_STORE;
	      store |= ty == TYPE_STORE;
	      fp |= (ty == TYPE_FP || ty == TYPE_FMA || ty == TYPE_FFMA
		     || ty == TYPE_FCVT || ty == TYPE_FSCALE
		     || ty == TYPE_FDIV || ty == TYPE_FCMP
		     || (set && FLOAT_MODE_P (GET_MODE (SET_DEST (set)))));
	    }
      }
  if (mem && fp && (store || !e2k_ifcvt_fp_loads))
    {
      *true_expr = *false_expr = NULL_RTX;
      return;
    }
  /* The arms' estimated probability, for an FP compare's predicate.  */
  int prob = 0;
  for (basic_block arm : { ce_info->then_bb, ce_info->else_bb })
    if (arm)
      {
	edge e = find_edge (ce_info->test_bb, arm);
	int p = (e && e->probability.initialized_p ()
		 ? e->probability.to_reg_br_prob_base () * 100
		   / REG_BR_PROB_BASE : 50);
	prob = MAX (prob, p);
      }
  bool fp_pred_ok = e2k_ifcvt_fp_prob > 0 && prob >= e2k_ifcvt_fp_prob;
  basic_block bb = ce_info->test_bb;
  for (rtx_insn *insn = BB_END (bb); insn != PREV_INSN (BB_HEAD (bb));
       insn = PREV_INSN (insn))
    if (INSN_P (insn) && reg_set_p (XEXP (t, 0), insn))
      {
	if (recog_memoized (insn) >= 0 && get_attr_type (insn) == TYPE_FCMP
	    && !fp_pred_ok)
	  *true_expr = *false_expr = NULL_RTX;
	return;
      }
}

/* A pipelined loop's check load (e2k_ldchk_jump): its rbranch goes to
   the loop's compensation code.  */
const char *
e2k_output_ldchk_jump (rtx *operands)
{
  static char buf[64];
  rtx mem = operands[1];
  if (GET_CODE (mem) == ZERO_EXTEND)
    mem = XEXP (mem, 0);
  operands[3] = mem;
  const char *sz = "bhwd";
  int k = exact_log2 (GET_MODE_SIZE (GET_MODE (mem)));
  gcc_assert (k >= 0 && k <= 3);
  snprintf (buf, sizeof buf, "ld%c,5\t%%3, %%0, mas=0x3\n\trbranch\t%%l2",
	    sz[k]);
  return buf;
}

static bool
e2k_ldlock_p (const_rtx pat)
{
  return (GET_CODE (pat) == PARALLEL && XVECLEN (pat, 0) == 2
	  && GET_CODE (XVECEXP (pat, 0, 1)) == UNSPEC
	  && XINT (XVECEXP (pat, 0, 1), 1) == UNSPEC_LDLOCK);
}

/* Only after reload, in the EBB scheduler of machine reorg, and only
   data speculation: a semi-speculative load needs no check at all, and
   control speculation is a separate step.  */
void
e2k_set_sched_flags (spec_info_t spec_info)
{
  unsigned int *flags = &current_sched_info->flags;
  if (e2k_dam && optimize > 0 && reload_completed
      && (*flags & SCHED_EBB))
    {
      /* Control speculation is done without checks (e2k_spec_prepare).  */
      spec_info->mask = e2k_dam ? BEGIN_DATA : 0;
      *flags |= USE_DEPS_LIST | DO_SPECULATION;
      spec_info->flags = 0;
      spec_info->dump = sched_verbose >= 1 ? sched_dump : 0;
    }
  else
    spec_info->mask = 0;
}

/* The pieces of a load the DAM can speculate: (set (reg) SRC) with SRC
   a memory reference or a zero-extended one, or a lock load of one.  */
bool
e2k_spec_load_parts (rtx_insn *insn, rtx *dest, rtx *src)
{
  rtx pat = PATTERN (insn);
  if (e2k_ldlock_p (pat))
    pat = XVECEXP (pat, 0, 0);
  if (GET_CODE (pat) != SET)
    return false;
  *dest = SET_DEST (pat);
  *src = SET_SRC (pat);
  return (REG_P (*dest) && GPR_REGNO_P (REGNO (*dest))
	  && GET_MODE (*dest) == GET_MODE (*src)
	  && e2k_spec_load_operand (*src, GET_MODE (*src)));
}

/* Whether MEM is in a loop copy that runs when its arrays may overlap
   (e2k_av_loop): its loads mostly read what its stores just wrote, and a
   failed check costs its compensation code every time (zlib's
   inflate_fast, 46 cycles an iteration of 3 bytes instead of 10).  */
bool
e2k_ov_mem_p (rtx mem)
{
  if (GET_CODE (mem) == ZERO_EXTEND || GET_CODE (mem) == SIGN_EXTEND)
    mem = XEXP (mem, 0);
  if (!MEM_P (mem) || !MEM_EXPR (mem))
    return false;
  tree base = get_base_address (MEM_EXPR (mem));
  if (!base
      || (TREE_CODE (base) != MEM_REF && TREE_CODE (base) != TARGET_MEM_REF))
    return false;
  unsigned short c = MR_DEPENDENCE_CLIQUE (base);
  machine_function *m = cfun->machine;
  for (int k = 0; c && k < m->n_ov_cliques; k++)
    if (c == m->ov_cliques[k])
      return true;
  return false;
}

/* Whether INSN accesses memory in such a copy.  */
static bool
e2k_ov_insn_p (rtx_insn *insn)
{
  subrtx_iterator::array_type array;
  FOR_EACH_SUBRTX (iter, array, PATTERN (insn), NONCONST)
    if (MEM_P (*iter) && e2k_ov_mem_p (const_cast<rtx> (*iter)))
      return true;
  return false;
}

int
e2k_speculate_insn (rtx_insn *insn, ds_t ts, rtx *new_pat)
{
  rtx dest, src;
  if ((ts & ~BEGIN_DATA) != 0 || !e2k_spec_load_parts (insn, &dest, &src))
    return -1;
  if (e2k_ov_mem_p (src))
    return -1;
  if (e2k_ldlock_p (PATTERN (insn)))
    return 0;
  /* A pipelined loop's prologue is speculative already; a load
     e2k_unpredicate_loads ran without its condition is not.  */
  if (e2k_ms_flag (insn)
      && (e2k_ms_flag (insn) != E2K_MS_SM || !e2k_unpred_cond_of (insn)))
    return -1;
  /* Its check, a plain load, takes the load's dependences, and loads
     have none on branches (e2k_spec_prepare): not before every branch
     the load followed is scheduled, or the check could rise above one
     and fault on an address valid only past it.  */
  for (rtx_insn *p = PREV_INSN (insn);
       p && p != current_sched_info->prev_head && !e2k_unpred_cond_of (insn);
       p = PREV_INSN (p))
    if (JUMP_P (p)
	&& (INSN_UID (p) >= (int) e2k_insn_clock.length ()
	    || e2k_insn_clock[INSN_UID (p)] == 0))
      return -1;
  /* A failed check reloads from the address; it must still be there.  */
  if (reg_overlap_mentioned_p (dest, src))
    return -1;
  /* The lock load shares the SET with the original pattern: an address
     replacement (DEP_REPLACE, moving the load past an increment of its
     base) points into that SET and must change the lock load too.  The
     check copies the address current when it is made.  */
  *new_pat = gen_rtx_PARALLEL (VOIDmode,
			       gen_rtvec (2, PATTERN (insn),
					  gen_rtx_UNSPEC (VOIDmode,
							  gen_rtvec (1, const0_rtx),
							  UNSPEC_LDLOCK)));
  return 1;
}

/* Hold back a load about to be issued as a lock load while an increment
   of its base that may still be moved above it, by rewriting its
   address, is ready: issuing the load makes the check, which inherits
   the load's dependence on the increment as a hard one, and the
   increment was already in the ready list (an assertion in
   schedule_insn, gcc.c-torture/execute/920302-1.c).  Once the
   increment is issued, the rewritten address reaches the lock load
   (which shares the load's SET) and the check copies it.  */
int
e2k_lookahead_guard (rtx_insn *insn, int)
{
  if (!(TODO_SPEC (insn) & BEGIN_DATA))
    return 0;
  sd_iterator_def sd_it;
  dep_t dep;
  FOR_EACH_DEP (insn, SD_LIST_FORW, sd_it, dep)
    {
      /* haifa-sched.cc's QUEUE_INDEX: -1 ready, >= 0 queued.  */
      int q = HID (DEP_CON (dep))->queue_index;
      if (DEP_REPLACE (dep) != NULL && (q == -1 || q >= 0))
	return -1;
    }
  return 0;
}

bool
e2k_needs_block_p (ds_t)
{
  return false;
}

rtx
e2k_gen_spec_check (rtx_insn *insn, rtx_insn *label, ds_t)
{
  rtx dest, src;
  gcc_assert (label == NULL);
  bool ok = e2k_spec_load_parts (insn, &dest, &src);
  gcc_assert (ok);
  machine_mode mode = GET_MODE (dest);
  rtx test = gen_rtx_NE (VOIDmode,
			 gen_rtx_UNSPEC (VOIDmode,
					 gen_rtvec (1, copy_rtx (dest)),
					 UNSPEC_LDCHK),
			 const0_rtx);
  rtx set = gen_rtx_SET (copy_rtx (dest),
			 gen_rtx_IF_THEN_ELSE (mode, test, copy_rtx (src),
					       copy_rtx (dest)));
  if (rtx cond = e2k_unpred_cond_of (insn))
    return gen_rtx_COND_EXEC (VOIDmode, copy_rtx (cond), set);
  return set;
}

ds_t
e2k_get_insn_spec_ds (rtx_insn *insn)
{
  return e2k_ldlock_p (PATTERN (insn)) ? BEGIN_DATA : 0;
}

/* Counted loops on %lsr (see the "Counted loops" section of e2k.md).  */

/* Whether the loop the doloop pass is converting may run more than
   2^32 - 1 times (set by e2k_can_use_doloop_p for the doloop_end
   expander that follows).  */
bool e2k_doloop_wide;

/* The iterations the doloop pass knows that loop to run: its count if
   constant, else -2 - its bound, or -1: operand 2 of the doloop_end
   patterns, which e2k_hwloop_opt records for each hardware
   loop, by the UID of its loop end, for the modulo scheduler (array
   prefetch leaves loops known to be short alone).  RTL loops don't keep
   their bounds past the loop passes, nor loops their start labels.  */
HOST_WIDE_INT e2k_doloop_iters = -1;
hash_map<int_hash<int, 0, -1>, HOST_WIDE_INT> *e2k_loop_iters;
/* Likewise the loop ends of loops the vectorizer made (operand 3 of the
   doloop_end patterns, e2k_doloop_vect_p).  */
hash_set<int_hash<int, 0, -1> > *e2k_loop_vect;
