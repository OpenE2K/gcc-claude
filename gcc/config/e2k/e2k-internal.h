/* Subroutines for the Elbrus (E2K) port, 64-bit Linux.
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

#ifndef GCC_E2K_INTERNAL_H
#define GCC_E2K_INTERNAL_H

/* What the files of the back end share: types, macros, and the
   functions and variables one defines and others use.  */

/* Per-insn flags of e2k_modsched and e2k_unpredicate_loads (e2k_ms_flag),
   for final: print ",sm", print abn, abp; and a jump that stays an
   ibranch (e2k_prepare_branches).  */
enum { E2K_MS_SM = 1, E2K_MS_ABN = 2, E2K_MS_ABP = 4, E2K_MS_IBRANCH = 8 };

/* Bundle marks: for each insn UID, whether it opens a wide instruction,
   closes one, and how many empty cycles follow it.  */
struct e2k_mark
{
  bool open;
  bool close;
  int nops;
  /* After a conditional jump: empty cycles for the fall-through path
     only, as a wide instruction of its own before the next block.  */
  int post_nops;
  /* An empty wide instruction before this one (e2k_gen_bundles).  */
  bool lead_nop;
  /* The ALU channel chosen for the insn plus one (e2k_assign_channels),
     or 0 to let gas choose.  */
  unsigned char chan1;
  /* On the insn that closes a wide instruction: its estimated size in
     words (e2k_fit_bundles), for -mwi-size-check.  */
  unsigned char words;
};

/* Array prefetch programs (e2k_ms_apb_assign), printed after the
   function as lcc places them; loops that the profile or their count
   says run fewer than E2K_APB_MIN_TRIP times use it only when it
   shortens the kernel (e2k_ms_pipeline).  */
#define E2K_APB_MIN_TRIP 256

/* vlc: the count is valid (spec/isa/loops.md, %lsr bit 37).  */
#define E2K_LSR_VLC (HOST_WIDE_INT_1 << 37)

/* Strip-mined loops run chunks of this many iterations (a power of two
   below lcc's 0x3ffffe0), the first one shorter.  */
#define E2K_LSR_CHUNK (HOST_WIDE_INT_1 << 25)

/* Iterations from which a loop is worth pipelining for any gain over
   one iteration's length (e2k_ms_long_p, e2k_loop_rec_bound_p).  */
#define E2K_MS_LONG 64

/* Clocks of the kernel instructions, applied after schedule_ebbs.  */
struct e2k_ms_clock { rtx_insn *insn; int clock; };

#define E2K_MS_MAX_NODES 1024

/* Loops of this many operations are worth a modulo schedule even when
   it overlaps nothing (e2k_ms_pipeline).  */
#define E2K_MS_BIG 200

#define E2K_MS_MAX_USES 4

#define E2K_MS_MAX_II 512

struct e2k_ms_use
{
  unsigned regno;
  int value;			/* a predicate's: its defining node */
  int dist;			/* 0: this iteration's value; 1: the last */
  bool pred;
};

struct e2k_ms_node
{
  rtx_insn *insn;
  int value;			/* value defined, or -1 */
  int nuses;
  e2k_ms_use uses[E2K_MS_MAX_USES];
  rtx mem;			/* memory reference, if any */
  bool store;
  bool pred;			/* sets a predicate (a while loop's exit test) */
  bool dpred;			/* sets a predicate merges or stores read */
  bool dead;			/* a copy folded into its source */
  bool lock;			/* a lock load (DAM) */
  int chk;			/* a check load: its lock load's node, else -1 */
  /* A load read through array prefetch (e2k_ms_mark_apb): INSN is its
     mova, ORIG the load, which the prologue keeps.  It reads an
     APB_SIZE-byte element at APB_IV + APB_INV + APB_OFF in iteration 0
     (APB_INV INVALID_REGNUM if none), APB_STEP bytes further each
     iteration, through descriptor APB_D (APB_IV + APB_INV on the way
     in); channel, area, offset in the area's step and whether it
     advances the area once scheduled (e2k_ms_apb_assign).  */
  bool apb;
  rtx_insn *orig;
  int apb_size, apb_d, apb_chan, apb_area, apb_ind, apb_am;
  unsigned apb_iv, apb_inv;
  /* A second invariant of the base (a register derived from APB_IV
     plus an invariant, e2k_ms_mark_apb), or INVALID_REGNUM.  */
  unsigned apb_inv2;
  HOST_WIDE_INT apb_off, apb_step;
  /* An AAU store (e2k_ms_mark_staa): INSN is its staa, ORIG the store.
     Iteration 0 writes APB_IV + APB_INV + APB_OFF, APB_STEP bytes further
     each iteration, through descriptor APB_D, whose base adds
     L->apb_adj[APB_D], and store index STAA_STI (0 on the way in), which
     %aaincr STAA_INCR steps (e2k_ms_staa_assign).  */
  bool staa;
  int staa_sti, staa_incr;
  /* What the kernel doesn't run: a node whose result only the movas'
     loads in the prologue and the AAU stores' addresses read
     (e2k_ms_mark_kdead).  The prologue runs it.  */
  bool kdead;
  int time;
  int pname;			/* a predicate's ring name in its iteration */
  /* A store that reads its address register from a later iteration,
     with REBASE_OFF taken off its offset (e2k_ms_rebase_stores): its
     use REBASE_USE, whose distance was REBASE_DIST0.  */
  int rebase_use, rebase_dist0;
  HOST_WIDE_INT rebase_off;
};

struct e2k_ms_value
{
  int node;			/* defining node */
  unsigned regno;
  /* The registers holding the instances of the iterations before the
     loop, -1 and -2 (INVALID_REGNUM if not known).  */
  unsigned init[2];
  /* Or the stack slot holding instance -1 (e2k_ms_slot_copy).  */
  rtx init_mem;
  machine_mode mode;
  bool carried;			/* read by the next iteration */
  bool carried2;		/* read two iterations later */
  int out_dist;			/* the instance of the iteration this many
				   before the last is read after the loop;
				   -1 if none is */
  int span;			/* rotations from the def to the last use */
  int name;			/* %b[] name in the defining iteration */
};

/* A register live after the loop, copied from VALUE's instance of the
   iteration DIST before the last.  HEND: a two-block while loop's value
   at the end of its first block, copied over the other under the first
   block's exit condition.  */
struct e2k_ms_out
{
  unsigned regno;
  machine_mode mode;
  int value;
  int dist;
  bool hend;
};

struct e2k_ms_dep
{
  int from, to, lat, dist;
  /* The part of LAT for a result crossing clusters, dropped in
     recurrences (e2k_ms_pipeline).  */
  int cross;
};

struct e2k_ms_loop
{
  basic_block bb;
  rtx_insn *jump;
  /* A one-block while loop's disp of its loop end's CTPR, in the loop
     (the loop end prepared like any branch): it goes to the start of
     each prologue, as a second block's does (e2k_ms_wl).  */
  rtx_insn *edisp;
  auto_vec<rtx_insn *> insns;	/* the body in order, without the jump */
  int n;
  e2k_ms_node nodes[E2K_MS_MAX_NODES];
  auto_vec<e2k_ms_value> values;
  auto_vec<e2k_ms_dep> deps;
  auto_vec<e2k_ms_out> outs;
  int ii, stages, pairs;
  /* The predicate ring (setbp psz = NPRED - 1), or 0: predicates keep
     their registers.  EXIT is where the loop ends.  */
  int npred;
  basic_block exit;
  /* While loops: STAY is the node setting the predicate the loop end
     tests.  Of two blocks, the first block's insns are the first NH,
     and C1 is the node setting P1, its exit taken when (E1 P1 0): a
     compare, or a landp of compares (a chain of branches merged,
     e2k_merge_chains).  C1S are the nodes computing P1 in order, which
     run again after the loop to tell the exits apart.  */
  bool wl;
  int stay, nh, c1;
  int nh0;			/* the first block's insns in INSNS */
  auto_vec<int> c1s;
  rtx p1, pstay;
  enum rtx_code e1;
  /* Where the first block's exit goes, if not where the loop ends.  */
  basic_block x1;
  /* Data speculation (spec/isa/speculation.md, DAM): with WANT_DAM a
     load that may read what a store of the loop wrote moves above it as
     a lock load, node DAM, checked by node KCHK in the last stage.
     DAM_DEPS are the store -> load dependences left out for it; MAY_DAM
     says there were some to leave out.  REC lists the instances (node,
     iterations after the checked one) that ran with the early value
     before the check, which a failed check redoes, and EXT the
     lifetimes that redoing extends (value, cycle).  DAM_SETTLED: the
     II with a lock load has been weighed against the II without, so the
     earliest starts may be tried (e2k_ms_pipeline).  */
  bool want_dam, may_dam, dam_settled;
  int dam, kchk;
  auto_vec<e2k_ms_dep> dam_deps;
  auto_vec<std::pair<int, int> > rec, ext;
  /* Array prefetch (spec/isa/apb.md): APB_OK when this loop may use it,
     NAPB loads that do through NAPB_D descriptors, APB_TMP a register
     free on the ways in; %aaincr1 .. APB_NINCR hold APB_INCR[1 ..]
     (e2k_ms_apb_assign).  */
  bool apb_ok = false;
  int napb = 0, napb_d = 0, apb_nincr = 0;
  /* AAU stores (e2k_ms_mark_staa): STAA_OK when this loop may use them,
     NSTAA stores through descriptors NAPB_D .. NAPB_D + NSTAA_D - 1.  */
  bool staa_ok = false;
  int nstaa = 0, nstaa_d = 0;
  /* The AAU stores don't lower the bound on II (e2k_ms_pipeline): try
     again without them, keeping array prefetch.  */
  bool staa_unwanted = false;
  HOST_WIDE_INT apb_incr[8];
  /* What descriptor D's base adds to its induction variable (and
     invariant): 0 or less, so that no area's disp is negative
     (e2k_ms_apb_assign); an AAU store's offset (e2k_ms_staa_assign).  */
  HOST_WIDE_INT apb_adj[32];
  unsigned apb_tmp = INVALID_REGNUM;
  /* Window registers and %g16-%g31 (the kernel restores those after a
     signal handler, spec/abi/registers.md) that no value of the loop
     needs around it nor reads as an invariant, for values outside the
     ring (e2k_ms_assign_names).  */
  HARD_REG_SET fix_free;
  /* Invariants in %b[K] with no register free for them (e2k_ms_move_b):
     bit K of BINV; the loop reads BMAP[K] instead, copied in on each way
     in before setbn renames %b[].  */
  unsigned binv = 0;
  unsigned bmap[8];
  /* The mode each %b[K] is copied in (e2k_ms_move_b).  */
  machine_mode bmode[8];
};

/* An instruction of the prologue: node NODE of iteration J, or the copy
   of carried value VALUE into the ring (NODE -1), at time T.  */
struct e2k_ms_item { int t; int node; int j; int value; };

/* What a two-block while loop's blocks become one with: the second
   block B, the first one's exit jump HJUMP and its disp HDISP (or NULL),
   the predicate PSTAY of the landp the loop end now tests, and P1 the
   first block's exit predicate.  */
struct e2k_ms_wl
{
  basic_block b;
  rtx_insn *hjump, *hdisp;
  /* The loop end's disp, when the second block has it (the loop end
     prepared like any branch, its loop not innermost to GCC): it goes
     to the start of each prologue.  */
  rtx_insn *bdisp;
  rtx pstay, p1;
};

/* Whether the function refers to a declared object of at least
   E2K_APB_BIG bytes (the streams of its pipelined loops then likely come
   from memory, even those of short loops: NPB SP's 34-iteration loops
   over 2 MB arrays, 25.8 -> 24.4 s on the 8C2 with array prefetch, where
   short ones over data that stays in the caches pay its setup for
   nothing: Linpack's 320 KB matrix, 2.7% slower).  The loops' own
   addresses no longer name their arrays after ivopts.  */
#define E2K_APB_BIG (1 << 20)

/* e2k.cc.  */
extern bool e2k_tls_referenced_p (rtx x);
extern bool e2k_reloc_unspec_p (rtx x);
extern bool e2k_bundling;
extern bool e2k_in_bundle;
extern bool e2k_cur_sm;

/* e2k-abi.cc.  */
extern void e2k_init_pic_reg (void);
extern rtx e2k_legitimize_pic (rtx x);
extern rtx e2k_legitimize_tls (rtx x);
extern rtx e2k_legitimize_address (rtx x, rtx, machine_mode);
extern rtx e2k_function_arg (cumulative_args_t cum,
			     const function_arg_info &arg);
extern rtx e2k_function_incoming_arg (cumulative_args_t cum,
				      const function_arg_info &arg);
extern void e2k_function_arg_advance (cumulative_args_t cum_v,
				      const function_arg_info &arg);
extern unsigned int e2k_function_arg_boundary (machine_mode mode,
					       const_tree type);
extern bool e2k_strict_argument_naming (cumulative_args_t);
extern machine_mode e2k_promote_function_mode (const_tree type,
					       machine_mode mode,
					       int *punsignedp, const_tree,
					       int for_return);
extern bool e2k_return_in_memory (const_tree type, const_tree);
extern rtx e2k_function_value (const_tree type, const_tree fn, bool outgoing);
extern rtx e2k_libcall_value (machine_mode mode, const_rtx);
extern bool e2k_function_value_regno_p (const unsigned int regno);
extern void e2k_output_mi_thunk (FILE *f, tree thunk, HOST_WIDE_INT delta,
				 HOST_WIDE_INT vcall_offset, tree function);
extern rtx e2k_struct_value_rtx (tree fn, int incoming);
extern void e2k_compute_window (void);
extern bool e2k_frame_pointer_required (void);
extern bool e2k_can_eliminate (const int, const int to);
extern bool e2k_function_ok_for_sibcall (tree, tree);
extern enum unwind_info_type e2k_debug_unwind_info (void);
extern rtx_insn * e2k_md_asm_adjust (vec<rtx> &outputs, vec<rtx> &inputs,
				     vec<machine_mode> &input_modes,
				     vec<const char *> &constraints,
				     vec<rtx> &, vec<rtx> &, HARD_REG_SET &,
				     location_t loc);
extern void e2k_init_builtins (void);
extern tree e2k_builtin_decl (unsigned code, bool);
extern rtx e2k_expand_builtin (tree exp, rtx target, rtx, machine_mode, int);
extern void e2k_atomic_assign_expand_fenv (tree *hold, tree *clear,
					   tree *update);

/* e2k-expand.cc.  */
extern bool e2k_laying_out_parms;
extern bool e2k_vector_mode_supported_p (machine_mode mode);
extern machine_mode e2k_preferred_simd_mode (scalar_mode mode);
class vector_costs;
class vec_info;
extern vector_costs *e2k_vectorize_create_costs (vec_info *, bool);
extern int e2k_builtin_vectorization_cost (enum vect_cost_for_stmt, tree,
					   int);
extern bool e2k_vectorize_vec_perm_const (machine_mode vmode,
					  machine_mode op_mode, rtx target,
					  rtx op0, rtx op1,
					  const vec_perm_indices &sel);
extern bool e2k_field_insn_p (rtx pat);

/* e2k-sched.cc.  */
extern bool e2k_packed_type_p (enum attr_type t);
extern vec<rtx> e2k_unpred_cond;
extern rtx e2k_unpred_cond_of (const rtx_insn *insn);
extern void e2k_set_unpred_cond (rtx_insn *insn, rtx cond);
extern int e2k_adjust_cost (rtx_insn *con, int dep_type, rtx_insn *pro,
			    int cost, unsigned int);
extern int e2k_issue_rate (void);
extern int e2k_multipass_lookahead (void);
extern vec<int> e2k_insn_clock;
extern vec<int> e2k_insn_ebb;
extern void e2k_sched_init_global (FILE *, int, int);
extern int e2k_sched_reorder (FILE *, int, rtx_insn **, int *, int clock);
extern int e2k_sched_reorder2 (FILE *, int, rtx_insn **, int *n_readyp,
			       int clock);
extern void e2k_sched_init (FILE *, int, int);
extern int e2k_variable_issue (FILE *, int, rtx_insn *insn, int more);
extern vec<e2k_mark> e2k_marks;
extern bool e2k_prints_p (rtx_insn *insn);
extern bool e2k_asm_insn_p (rtx_insn *insn);
extern bool e2k_asm_call_p (rtx_insn *insn);
extern bool e2k_rwd_lsr_p (rtx_insn *insn);
extern bool e2k_raw_insn_p (rtx_insn *insn);
extern bool e2k_alone_p (rtx_insn *insn);
extern bool e2k_setwd_type_p (rtx_insn *insn);
extern bool e2k_writes_jump_reg_p (rtx_insn *insn, rtx_insn *jump);
extern void e2k_set_sched_flags (spec_info_t spec_info);
extern bool e2k_spec_load_parts (rtx_insn *insn, rtx *dest, rtx *src);
extern bool e2k_ov_mem_p (rtx mem);
extern int e2k_speculate_insn (rtx_insn *insn, ds_t ts, rtx *new_pat);
extern int e2k_lookahead_guard (rtx_insn *insn, int);
extern bool e2k_needs_block_p (ds_t);
extern rtx e2k_gen_spec_check (rtx_insn *insn, rtx_insn *label, ds_t);
extern ds_t e2k_get_insn_spec_ds (rtx_insn *insn);
extern hash_map<int_hash<int, 0, -1>, HOST_WIDE_INT> *e2k_loop_iters;
extern hash_set<int_hash<int, 0, -1> > *e2k_loop_vect;
extern bool e2k_loop_vect_made_p (rtx_insn *);

/* e2k-bundle.cc.  */
extern void e2k_gen_bundles (void);
extern void e2k_bundle_var_notes (void);
extern void e2k_bundle_stmt_notes (void);
extern void e2k_bundle_block_notes (void);
extern vec<int> e2k_ms_twin;
extern vec<std::pair<int, int> > e2k_ms_kernels;
extern vec<int> e2k_ms_kernel_rings;
extern int e2k_cur_chan (void);
extern int e2k_dam_labelno;
extern vec<int> e2k_dam_pending;
extern vec<int> e2k_dam_stubs;
extern int e2k_apb_labelno;
extern vec<char *> e2k_apb_progs;
extern void e2k_final_postscan_insn (FILE *f, rtx_insn *insn, rtx *, int);
extern void e2k_asm_function_prologue (FILE *);
extern void e2k_asm_function_epilogue (FILE *f);

/* e2k-branch.cc.  */
extern void e2k_prepare_loop_branches (void);
extern void e2k_prepare_branches (bool after_ms);
extern void e2k_share_ctprs (void);
extern void e2k_lift_prepares (void);
extern void e2k_hoist_prepares (void);

/* e2k-rename.cc.  */
extern bool e2k_rename_free_p (unsigned r, machine_mode mode, bitmap live,
			       const HARD_REG_SET &busy, unsigned wtop = 0);
extern unsigned e2k_window_top (void);
extern void e2k_note_depth (void);
extern void e2k_note_regs (rtx x, HARD_REG_SET *set);
extern basic_block e2k_chain_next (basic_block bb);
extern void e2k_spec_rename (void);

/* e2k-hwloop.cc.  */
extern bool e2k_can_use_doloop_p (const widest_int &iterations,
				  const widest_int &iterations_max,
				  unsigned int loop_depth,
				  bool entered_at_top);
extern HOST_WIDE_INT e2k_loop_max_iters (rtx_insn *jump);
extern HOST_WIDE_INT e2k_loop_exact_iters (rtx_insn *jump);
extern unsigned e2k_loop_unroll_adjust (unsigned nunroll, class loop *loop);
extern const char * e2k_invalid_within_doloop (const rtx_insn *insn);
extern void e2k_hwloop_unspill (void);
extern struct hw_doloop_hooks e2k_doloop_hooks;
extern vec<unsigned char> e2k_ms_flags;
extern HARD_REG_SET e2k_ms_live_out_extra;
extern vec<e2k_ms_clock> e2k_ms_clocks;

/* e2k-ms-analyze.cc.  */
extern unsigned e2k_ms_flag (const rtx_insn *insn);
extern void e2k_ms_set_flag (rtx_insn *insn, unsigned f);
extern rtx e2k_ms_gen_setbn_enter (e2k_ms_loop *l);
extern bool e2k_known_aligned_p (rtx mem, unsigned bytes);
extern bool e2k_ms_why (const char *why);
extern rtx e2k_ms_jump_cond (rtx_insn *jump);
extern void e2k_ms_dependents (e2k_ms_loop *l, int from, unsigned *dep);
extern bool e2k_fp_class_p (rtx_insn *insn);
extern bool e2k_ms_analyze (e2k_ms_loop *l, basic_block exit);

/* e2k-ms-sched.cc.  */
extern void e2k_ms_sort (int *order, int n, const int *key);
extern int e2k_ms_item_cmp (const void *a, const void *b, void *);
extern bool e2k_ms_schedule_one (e2k_ms_loop *l, int ii, bool back);
extern bool e2k_ms_schedule (e2k_ms_loop *l, int ii, bool est,
			     bool bal = false, int slack = 0,
			     int *short_by = NULL, bool crit = false,
			     bool ims = false);
extern int e2k_ms_rec_mii (e2k_ms_loop *l);
extern void e2k_ms_dump_recurrence (e2k_ms_loop *l);
extern void e2k_ms_dam_plan (e2k_ms_loop *l);
extern void e2k_ms_compact (e2k_ms_loop *l);
extern bool e2k_ms_assign_names (e2k_ms_loop *l, int gap);
extern bool e2k_ms_assign_pnames (e2k_ms_loop *l);
extern int e2k_ms_pname (e2k_ms_loop *l, int i, int j, int frame);
extern int e2k_ms_name (e2k_ms_loop *l, int v, int j, int frame);
extern rtx e2k_ms_reg (machine_mode mode, int name);

/* e2k-ms-emit.cc.  */
extern rtx e2k_ms_set (rtx pat);
extern rtx_insn * e2k_ms_local_disp (rtx_insn *jump);
extern bool e2k_ms_emit (e2k_ms_loop *l, const vec<rtx_insn *> &pre_ends,
			 const vec<edge> &entries, edge exit_edge,
			 const e2k_ms_wl *w);
extern void e2k_ms_rebase_stores (e2k_ms_loop *l, bool undo);

/* e2k-ms.cc.  */
extern void e2k_modsched (void);

/* e2k-av.cc.  */
extern gimple_opt_pass * make_pass_e2k_alias_version (gcc::context *ctxt,
						      bool late);
extern gimple_opt_pass * make_pass_e2k_block_version (gcc::context *ctxt);
extern gimple_opt_pass * make_pass_e2k_vect_mark (gcc::context *ctxt,
						  bool after);
extern bool e2k_vect_made_p (class loop *);

/* e2k-passes.cc.  */
extern rtl_opt_pass * make_pass_e2k_latch_copies (gcc::context *ctxt);
extern rtl_opt_pass * make_pass_e2k_dbl_zext (gcc::context *ctxt);
extern rtl_opt_pass * make_pass_e2k_narrow_ext (gcc::context *ctxt);
extern rtl_opt_pass * make_pass_e2k_dbl_widen (gcc::context *ctxt);
extern rtl_opt_pass * make_pass_e2k_addr_height (gcc::context *ctxt);
extern vec<int> e2k_spec_from;

/* e2k-spec.cc.  */
extern int e2k_spec_kind (rtx_insn *insn);
extern void e2k_spec_prepare (void);
extern bool e2k_spec_sets_live_p (rtx_insn *insn, rtx_insn *jump);
extern void e2k_spec_pin (rtx_insn *head, rtx_insn *tail);
extern void e2k_arm_reset_debug (rtx_insn *from, rtx_insn *to, rtx reg);
extern void e2k_unpredicate_loads (void);
extern void e2k_spec_mark (void);
extern void e2k_spec_prune (void);

/* e2k-reorg.cc.  */
extern void e2k_reorg (void);

#endif /* GCC_E2K_INTERNAL_H */
