# E2K back end proof of concept: state

Written by Claude (Anthropic) on the branch `claudes-e2k-compiler`, from
the relcc2 specification (`spec/isa`, `spec/abi`, `doc/gcc-port-plan.md`)
to find out what the spec is missing. Not for contribution to GCC (GCC
refuses AI-written code); the owner writes the real port by hand and may
reuse the design. Spec gaps go to relcc2 `docs/spec-poc-findings.md`.

This file is the source of truth for the work; update it with every
commit. Tags `v0.1` and `v0.2` mark the states described in the
sections of those names; "Since v0.2" lists what came after.

## Since v0.2

- C++ thunks are emitted as RTL and printed by `final` (new insn
  `e2k_thunk_jump` for the `disp`/`ct` pair), so they get line info
  (g++.dg/debug/dwarf2/non-virtual-thunk.C); same code as before.
- Counted loops on `%lsr` (`doloop_end`, `hw-doloop` in machine reorg,
  `e2k_hwloop_opt`): innermost loops without calls whose trip count is
  known to fit 32 bits end with `alc` + `ct %ctprN ? %NOT_LOOP_END`
  instead of increment/compare/branch. Before the loop: count | vlc,
  `rwd` to `%lsr`, `disp`, and a `nop 3` wide instruction for the
  4-cycle `rwd` latency (the preheader is another block to the
  scheduler). No `loop_mode`: probed on the 4C that `alc`/`%NOT_LOOP_END`
  count without it, and then stores are never suppressed. Loops the
  hook rejects keep `e2k_doloop_end` (decrement, compare, ibranch).
  Loops whose count may exceed 32 bits (most `long` index loops) don't
  use it yet: lcc strip-mines them into chunks of 0x3ffffe0 iterations
  (probed). C torture/ieee/dg-torture on the 4C: no new failures.
  CoreMark -O2 1,269 -> 1,277 it/s, Linpack (linpackc.c, 200) 93,815 ->
  107,133 KFLOPS (`toolchains/claude-e2k/perf`; lcc -O3: 2,305 it/s).
- Data speculation (`-mdam`, default): the EBB scheduler in machine
  reorg moves loads above stores that may write the same memory, as
  lock loads (`ld,sm … mas=0x4`, ALC0, reserving ALC2/ALC5 so no store
  shares the instruction), with a check load (`ld … mas=0x3`, ALC5) at
  the load's place: GCC's ia64-style simple checks
  (`TARGET_SCHED_SPECULATE_INSN`, `GEN_SPEC_CHECK`, ...). Every check
  carries `rbranch` to a stub that branches straight back (labels
  `.LDAMn`/`.LDAMBn` printed around the bundle): without it a consumer
  in the next instruction read the early value once (findings I11).
  Lock loads need `,sm` or they record nothing (findings I10). A check
  that keeps its entry costs its consumers nothing. Loads whose address
  the scheduler may rewrite past an increment are not speculated (GCC's
  dependence breaking doesn't cover the check), and two generic
  scheduler fixes were needed (`sched-deps.cc`: a shared DEP_REPLACE
  freed twice; same-base overlapping accesses were speculated). Torture
  on the 4C: no new failures. With `-funroll-loops`: CoreMark 1,335 it/s,
  Linpack 116,640 KFLOPS (v0.2: 1,269 / 93,815). Without unrolling it
  gains nothing yet: the check stays after the store and the uses after
  the check, so only load latency is hidden; overlapping whole
  iterations needs the consumers speculated too (recovery code).
- A load and a later store that may touch the same memory no longer
  share a wide instruction: a load in ALC5 sees a store in ALC2 of its
  own instruction (findings I12), and gas picks the channels.
  `e2k_adjust_cost` now gives every dependence between a store and
  another memory access, in either order, a cycle.
- A check load also reserves ALC2, so no store shares its instruction:
  a check that reloaded in ALC5 returned the value of a store in ALC2 of
  its own instruction (gcc.dg/torture/pr57425-1.c, findings I12).
- `-funroll-loops` is on at -O2 and above for speed (`e2k-common.cc`),
  at most 4 copies: unrolled iterations give the scheduler independent
  work, and the DAM lets their loads move above the previous stores.
  4C, with data speculation: CoreMark 1,277 -> 1,334 it/s, Linpack
  107,187 -> 110,645 KFLOPS; factors 2 and 8 were the same within
  noise. Torture on the 4C: no new failures.
- Rebuilding the runtime libraries with all of the above found a lock
  load moved above `__atomic_thread_fence` into the `wait` instruction
  (libgomp task.c, libstdc++ tzdb.cc; gas: "cannot encode MAS: CS1
  syllable is busy"). Two fixes: lock and check loads reserve CS1, which
  holds their MAS (so no `wait` or call shares their instruction), and
  `sched-deps.cc` no longer makes a dependence on a volatile store (a
  barrier's BLKmode scratch) speculative, so no load moves above a fence.
- Loops whose count may exceed 32 bits (or is unbounded) are strip-mined
  like lcc's and also count on `%lsr`: before the loop the count n goes
  to `((n - 1) & (2^25 - 1)) + 1 | vlc` for the first chunk and the
  iteration register keeps `(n - 1) & -2^25`; after the loop
  `{cmpedb}{ibranch .LHWn ? ~p}` goes to a stub at the end of the function
  that subtracts 2^25, writes `2^25 | vlc` to `%lsr`, waits and returns
  through the loop's CTPR (`e2k_doloop_end_wide`,
  `e2k_hwloop_end_wide`). The scratch registers come from the loop end's
  clobbers: RA keeps them out of the registers live into the loop. 4C:
  counts around 2^25 and 2^32 + 5 (`toolchains/claude-e2k/loops/strip.c`).
- Loads whose address the scheduler rewrites to move them past an
  increment of their base (DEP_REPLACE; unrolled loops) are speculated
  too, which they weren't since the 920302-1 crash. The lock load is now
  `(parallel [load's own SET, (unspec LDLOCK)])` sharing the SET with the
  original pattern, so the rewrite reaches it; a lookahead guard holds a
  lock load back while such an increment is ready, so the check (made
  when the load issues) copies the rewritten address; and haifa no
  longer gives the check a dependence the rewrite already broke
  (`process_insn_forw_deps_be_in_spec`). Linpack's daxpy now locks its
  `dx` loads above the `dy` stores: 110,587 -> 114,116 KFLOPS (CoreMark
  unchanged, 1,334 it/s). Torture on the 4C: no new failures. What
  remains in daxpy is store -> check -> fmul -> fadd -> store per
  element; lcc instead versions the loop on an overlap test (the
  disjoint version is a one-instruction loop_mode loop with `abn` and
  `staad`) and pipelines the overlapping one with lock loads and
  speculative `fmuld,sm`/`faddd,sm` consumers recomputed in an
  `rbranch` block.
- With counted loops, `-fmodulo-sched` (GCC's SMS) now pipelines some
  loops and marks them BB_DISABLE_SCHEDULE; the bundler then put the
  whole unscheduled loop into one wide instruction (gas: "An excessive
  ALF instruction", gcc.dg/sms-*.c). Machine reorg clears the flag, since
  its scheduler also forms the wide instructions. sms-*: 24 PASS on the 4C.
- Full C suite on the 4C after rebuilding the libraries (before the SMS
  fix): 166,705 PASS / 1,453 FAIL (v0.2: 166,718 / 1,439). New: the
  nine sms tests above (fixed); 28 guality location checks (loop-1,
  pr36728-1/2/3, pr54693-2, pr54796, pr68860-2: variables in loops
  counted on `%lsr` and after the reorg scheduler, see var-tracking in
  "Next"); vrp91's dump scan (unrolling at -O2). Compat suite on the
  4C: 0 unexpected.
- The scheduler's automaton is nondeterministic (`automata_option
  "ndfa"`, as ia64 and c6x): the channel exclusions between loads and
  stores (bundle.md) made the deterministic one reject wide instructions
  that fit, e.g. two loads and a store once the loads had taken ALC0 and
  ALC2, where loads in ALC0/ALC5 and the store in ALC2 fit (findings P8).
- Software pipelining (`-mpipeline`, default; `e2k_modsched` in machine
  reorg, after register allocation, before the EBB scheduler) of
  innermost counted loops of one block without calls, the way lcc builds
  them (spec/isa/loops.md):
  - iterative modulo scheduling over the DFA (one state per row of the
    kernel), from the operation counts up to an II at most 3/4 of one
    iteration's length and 2 cycles shorter (else not worth a prologue);
    latencies include the cluster crossing cost (+1, +2 for FP results)
    except an operation's use of its own last result: gas picks the
    channels, and a one-instruction kernel otherwise stalls in every
    iteration (findings I13);
  - every register the body defines is renamed into the rotating `%b[]`
    (`abn abnf=1, abnt=1` on the loop end, `setbn` before and after;
    `%b[8..63]` are new fixed hard registers): values are packed on the
    ring by lifetime, first fit in two lanes;
  - the kernel runs exactly n times: the first S-1 stages of iterations
    0..S-2 are peeled into a prologue, with the names they would have
    after the rotations they skip; every store goes in the last stage and
    everything else is `,sm`, so the early stages of iterations past the
    end, which the last kernel iterations run, are harmless; no
    `loop_mode`, `pcnt` or `ecnt` (findings I14); values live into the
    loop are copied into the ring in the prologue, values live after it
    copied out on the exit edge;
  - the ring sits between the window registers and the outgoing
    registers (calls use `wbs` = window + ring): a callee's `setwd` must
    cover all of the caller's window above `wbs`, so a ring above them
    made every later call trap (findings A17); a value in `%b[0..7]` may
    pass through the loop;
  - within one cycle, the kernel and the prologue are emitted reads
    before writes (what the wide instruction does), retrying the ring with
    a cycle between lifetimes when that has no order; the kernel ends
    with a `use` of every ring name: dataflow doesn't know about rotation
    and deleted values that the next iteration reads under another name;
  - memory dependences: exact distances for two accesses through one
    induction register, else `may_alias_p`, trusting only dependence
    cliques that hold across iterations (clique 1 and those of loops
    versioned for aliasing; an inlined function's `restrict` doesn't:
    gcc.dg/torture/pr90328.c, findings P9);
  - `TARGET_LOOP_UNROLL_ADJUST` doesn't unroll such loops when they
    don't store or their addresses use only induction and invariant
    registers (what the dependence test understands): an unrolled body
    pipelines worse;
  - dataflow doesn't know that `setbn` renames `%b[0..7]`: the entering
    `setbn` uses them and the leaving one sets them, else the ring's
    writes under the same names made a value there before the loop dead
    (a call argument set up before it; gcc.dg/torture/pr111048.c and
    gcc.c-torture/execute/va-arg-22.c at -Os); a value may so pass
    through the loop in them, as the ring lies elsewhere, but not be used
    or set in it;
  - in a function without calls, register allocation's values in
    `%b[0..7]` (it uses them before the window registers `%r4`.., findings
    P10) move to free window registers first, for the whole function;
  - a loop entered from several edges (hw-doloop sets `%lsr` up on each)
    gets the prologue on each.
  On the 8C2, daxpy with `restrict`: 3.4 -> 0.745 ns per element (II 1,
  18 stages; lcc 0.701). Checks on the 4C and the 8C2: sums, dot
  products, scaling, copies and daxpy for n = 1..1023 at -O1, -O2, -O3,
  -Os (`toolchains/claude-e2k/ms`). Alone it leaves CoreMark and Linpack
  as they were: their loops' arrays may overlap.
- Loop versioning for aliasing (`-malias-version`, default; a GIMPLE
  pass after the vectorizer, registered from option override): an
  innermost counted loop without calls whose stores may overlap other
  arrays gets GCC's runtime alias checks (as loop distribution builds
  them, at most 4 after pruning) and two copies; the references of the
  copy for disjoint arrays get a new dependence clique, one base per base
  address, which the loop owns. Alias analysis in RTL, the scheduler and
  the pipeliner then see its arrays as independent. lcc does the same
  (its daxpy). The cliques are kept as a set, not a range: copying a loop
  gives its references fresh cliques that a range would wrongly cover
  (pr90328 at -O3 failed so). At most 8 versioned loops per function.
  8C2, -O2, with the pipeliner: Linpack 221,755 -> 813,670 KFLOPS (lcc
  -O3 as v3 code 1,143,715), solution checksum 5050 as lcc's; CoreMark
  2,672 -> 2,761 it/s (lcc 4,469; CRC as before; the gain is the matrix
  loops the pipeliner now takes). Overlap tests (dy = dx +- 0..9,
  n = 1..100) agree with -O0.
- `fmul_add`, `fmul_sub` and `fmul_rsub` (two roundings, so the same
  results as the multiply and the add; the spec allows them only under
  -ffp-contract=fast) behind `-mfmul-add`, off: on the 8C2 a pipelined
  daxpy ran at the same speed with them (0.733 vs 0.739 ns per element)
  and Linpack as a whole about 10% slower (723,339 vs 812,886 KFLOPS, not
  understood yet). With gas's operands A, B, C, `fmul_subd` gives C - A*B
  and `fmul_rsubd` A*B - C (probed; findings I15); the first version had
  them swapped, which complex-sign-mul*, cbrt and the floatN-complex
  tests caught. The pipeliner takes them (type `fma`, latency 8).
- C torture/ieee/dg-torture on the 8C2 with all of the above
  (`-mfmul-add` off): 51,134 PASS / 192 FAIL; against the first 8C2 run
  (the pipeliner's first version) no new failures and pr90328 -O1/-Os
  fixed; against v0.2's list from the 4C the only new ones are
  `strub-run4*`, which fail on the 8C2 under DejaGnu only (they pass run
  by hand). Linpack's checksum is 5050 at -O1, -O2, -O3 and -Os.
- LRA (`find_hard_regno_for_1`) and register renaming (`check_new_reg_p`)
  charged an unused call-preserved register a prologue save, also for
  `LOCAL_REGNO` registers (the window), which IRA's `calculate_saved_nregs`
  already exempts; so they preferred globals and the outgoing `%b[0..7]`
  over a fresh `%r4`.. (findings P10: renaming after unrolling put a
  daxpy's values in `%b[]`). Both exempt them now.
- `%b[0..7]` and pipelined loops: register renaming no longer renames
  into them (`HARD_REGNO_RENAME_OK`), and a loop that still uses one
  (allocation under high pressure, e.g. Linpack's `main` with everything
  inlined, once the window is full) gets a global register free around
  and in the loop instead, copied from `%b[k]` before the first `setbn`
  and back after the second (the pipeliner counts the latter as a use
  after the loop although the copy still waits on the edge: Linpack's
  checksum caught that).
- Per-function `setwd dbl` as lcc chooses it (spec/abi/registers.md):
  at -O2 and above, a function that zero-extends 32-bit values to 64
  bits gets `dbl = 1`, decided once after expansion (`e2k_dbl_p`), and
  its 32-bit add, sub, logic, shift and multiply then also match a zero
  extension of their result (`*<code>si3_zext`). CoreMark's `ee_u32`
  index arithmetic loses most of its `sxt 6` (183 -> 37 in core_matrix),
  so its matrix loops pipeline at II 4. 8C2, -O2: CoreMark 2,761 ->
  3,012 it/s (lcc -O3 4,469), Linpack 823,196 KFLOPS (checksum 5050). C
  torture on the 8C2: unchanged (51,134 PASS / 192 FAIL).
- Inlining: at -O2 and above `max-inline-insns-auto` defaults to 100
  (GCC's 15), because a call costs a window switch and prepared
  transfers and bigger bodies give the scheduler more to pack; lcc also
  inlines CoreMark's state machine. 8C2, -O2: CoreMark 3,012 -> 3,309
  it/s; 200, or a larger `inline-unit-growth`, gained nothing more. C
  torture on the 8C2: 4 new FAILs that count code after inlining
  (`asm-inline.c` x3, `crc-17.c`'s dump scan), pr105537's ICE at -O3 -g
  gone (51,131 PASS / 194 FAIL).
- No 64-bit operation reads a value of 4 bytes or less
  (spec/abi/calling-convention.md, "Unused parts of a slot"). Combine
  made `(ashift:DI (subreg:DI (reg:SI)))` wherever the upper bits are
  masked off later (the table-driven CRC GCC makes of CoreMark's
  `crc16`), and under `dbl = 0` that reads whatever the upper half held
  before, tag included: once loads moved above branches, a dead `ld,sm`
  result that `core_bench_list` left in `%g1` made `crc16` trap
  (SIGILL, ILL_ILLOPN). Every operand predicate now rejects such a
  paradoxical subreg (`e2k_register_operand`), and a move of one
  zero-extends instead. C torture on the 8C2: unchanged.
- Control speculation in sched-ebb (generic GCC). `haifa_note_dep`
  built its dependence with `init_dep`, which drops the speculative
  weakness `note_dep` was given, and `sched_analyze_2` gave a load
  below a jump a speculative dependence on it only under sel-sched, so
  haifa never moved a possibly trapping load above a jump. Both now let
  sched-ebb do it. `process_insn_forw_deps_be_in_spec` also no longer
  gives a speculation check a broken (DEP_REPLACE) dependence on a
  consumer that is already ready when the check doesn't read what that
  consumer changes (else `schedule_insn` asserts: 283 torture ICEs).
- Control speculation (`-mcontrol-spec`, on): sched-ebb moves a load
  above a branch as a semi-speculative `ld,sm` (`*e2k_ldspec`), with an
  empty check at the load's place (`*e2k_chkctrl`) that keeps the uses
  after it; on the path the load came from, its address was valid. A
  load moved above a branch and a store becomes a lock load as before.
  8C2, -O2: CoreMark 3,367 -> 3,381 it/s. Most list-walking loads can't
  move: their register is live on the branch's other path, and sched2
  doesn't rename.
- ALU channels chosen by the compiler (`-mchannels`, on). gas gave each
  operation the first free channel it allows, so a consumer the
  scheduler placed right after its producer often sat in the other
  cluster and stalled a whole 4-cycle step (spec/isa/timing.md,
  "Clusters"). The bundler now prints every operation's channel
  (`addd,3`; compares through `%,`), choosing per wide instruction the
  assignment with the fewest stall cycles from v3's channel sets and
  gas's store/load exclusions. Interlock stalls in CoreMark on the 4C:
  6.0% -> 3.4% of cycles. 8C2, -O2: CoreMark 3,381 -> 3,476 it/s,
  Linpack 14.81 -> 14.65 s for 8,192 repetitions (its KFLOPS figure
  varies too much run to run to compare). C torture on the 8C2, with
  the three entries above: unchanged, 51,131 PASS / 194 FAIL.
- Fixed: a loop the pipeliner tried and gave up on lost the copies
  `e2k_ms_move_b` had put on its exit edge (values in `%b[0..7]` after
  the loop) when no other loop of the function was pipelined: edge
  insertions were committed only then. The edge also kept pointing at
  those insns, which the garbage collector later read as GIMPLE (an ICE
  in `ggc_set_mark` building zstd's `cover.c`).
- Predicates are local registers (`LOCAL_REGNO`) like the window
  registers: each call gets its own predicate file and the caller's is
  kept (registers.md), so they are not live at a function's end and
  allocation doesn't count them as callee-saved.
- sched-deps (generic): `deps_may_trap_p` honours `MEM_NOTRAP_P`; it
  looked only at the address, so a load the target knows can't trap
  still got a hard dependence on every earlier jump.
- Every branch is prepared (`-mprepare-branches`, on): an `ibranch`
  whose block has a CTPR dead after it becomes `disp %ctprK, target`
  just before it and `ct %ctprK [? pred]`, the CTPRs taken in turn so
  that the scheduler can move each `disp` above the transfers before
  it. A taken `ibranch` costs 6 cycles; a `ct` whose `disp` is D cycles
  before it costs max (0, 5 - D) taken and nothing not taken once D >= 2
  (spec/isa/control-transfer.md, "Costs"), so the `disp` -> `ct`
  dependence costs 2, not 5, to keep the fall-through path short, and a
  `disp` never shares a wide instruction with a transfer through the
  same CTPR (gas, before v6). CoreMark on the 4C: taken-`ibranch`
  cycles 171 M -> 4 M, fetch bubbles 16.3% -> 3.4% of cycles. 8C2, -O2:
  CoreMark +14.9% (3,456 -> 3,971 it/s, both measured with the C
  torture running there), Linpack 14.68 -> 13.99 s.
- Control speculation the lcc way, replacing the checked `ld,sm` of the
  entry above: before sched2 every load is marked non-trapping, so
  sched-ebb moves loads, and integer operations after them, above
  branches wherever the branch's other path doesn't need the register;
  afterwards whatever moved to an earlier block prints `,sm`
  (`e2k_spec_mark`; compares through `%,`). Only a non-speculative use
  of a diagnostic value traps, and on the path an operation came from
  its operands were valid. What has no speculative form (FP, stores,
  multi-operation patterns) is held below the branches before it
  (`e2k_spec_pin`, the dependence hook), and a load is made a lock load
  only once every branch it followed is scheduled: its check is a plain
  load with the load's dependences, which no longer include the
  branches, and above one it read a NULL-based diagnostic address
  (zstd, SIGILL). 8C2, -O2: CoreMark 4,103 -> 4,150 it/s; the renaming
  below is what lets it move most list loads.
- Renaming for speculation (`-mspec-rename`, on): in a block entered
  only by falling through from a conditional jump, a value computed in
  a register the jump or its other path still needs (the `list =
  list->next` that the loop returns) gets a free register of its own
  (a global, a window register the function has, or a predicate),
  copied back where its successors need it, so that sched-ebb can move
  the computation above the jump. Not across a call (its argument
  registers are read in the call's usage list), and not when a later
  use takes the register as part of a pair (`long double`). CoreMark's
  `find` loops: 18 -> 12 cycles per node. 8C2, -O2: CoreMark 4,150 ->
  4,488 it/s (lcc -O3 as v3 code: 4,469). C torture on the 8C2 with the
  five entries above: unchanged, 51,131 PASS / 194 FAIL.
- Loads now lose their dependences on earlier branches in the
  dependence hook (`e2k_spec_pin`), when the load's register is dead on
  the branch's other path, instead of being marked `MEM_NOTRAP_P`: GCC
  marks jump-table loads so itself, and with sched-deps honouring the
  flag (entry below) a table load rose above its range check as a plain
  `ldd` when `-mno-control-spec` was given (expat: SIGSEGV on an
  out-of-range index). CoreMark unchanged.
- sched-deps: the `deps_may_trap_p` change above is reverted (generic):
  `MEM_NOTRAP_P` there let a jump-table load move above its range
  check; the back end now frees its loads itself.
- Fixed (expat: 368 of 4,932 checks failed): the cycles the scheduler
  left between a block and the block it falls through to were not
  emitted (the bundler padded only within a block), and the hardware
  doesn't always wait: in a wide instruction whose `ct` is taken, a
  predicated operation or `merge` reads a predicate written by a
  compare in the previous instruction as it was (4C probe; registers
  are interlocked there). Within an extended block the gap is now
  emitted, after a conditional jump as an empty wide instruction of its
  own before the next block's label (so the taken path doesn't pay it).
  A block entered by a jump whose first wide instruction holds a
  transfer and also reads a predicate gets an empty one before it.
  CoreMark and Linpack unchanged. Real programs built with -O2 and run
  on the 4C: zlib, bzip2, xz, zstd, GMP, pcre2 and expat test suites
  pass. C torture on the 8C2 with the two entries above: unchanged.
- A load of the doubleword a store wrote in the wide instruction just
  before gets its value about 8 cycles late (relcc2 spec, timing.md
  "Store to load", measured by the spec work on the 4C and 8C2): the
  scheduler gives such a store -> load dependence 2 cycles when both
  addresses are one base plus offsets less than 8 bytes apart (spills
  and fills, stack arguments), and the modulo scheduler when the
  accesses are the same element. Dependences between accesses that
  only may alias keep 1 (giving them all 2 cost CoreMark 0.2%).
  CoreMark and Linpack unchanged. Tried and dropped: compare -> `ct`
  latency 3 in the DFA (timing.md; it was 2, the hardware waits the
  cycle): CoreMark -0.3%, Linpack +0.15%.
- While loops are modulo scheduled too (`-mpipeline-while`, on;
  `e2k_ms_wloop`), lcc's kind of loop that ends on a predicate
  (spec/isa/loops.md, "Early exits and while loops") but without
  `%lsr`: a block H ending "if (p) goto H", or two blocks, H ending
  "if (p1) goto X1" and B, which H falls into, ending "if (p2) goto H",
  as `while (list && list->x != k) list = list->next` becomes. Every
  operation is speculative (the kernel runs the early stages of
  iterations past the end), the loop end `abn; ct %ctprN ? p` is in the
  last row of the last stage with every other node before it, so the
  iteration the loop leaves on is complete (stores in the last stage
  too). The exit test is placed after the other nodes, as late as it
  may (`e2k_ms_place_exit`): compare -> `ct` 3 cycles, and predicates
  don't rotate, so each lives at most II cycles (II >= 3). Two blocks
  become one: B runs speculatively when H's exit is taken (so B must not
  store), and the loop end tests `landp ~p1, p2` (new pattern
  `e2k_landp`, PLS, one per wide instruction; lazy: p2's diagnostic tag
  doesn't count once p1 is set). After the loop H's exit compare runs
  again on the last iteration's values; registers live after the loop
  get H's values under it (new predicated copy `*e2k_cond_mov`) and
  B's otherwise (copied with `,sm`, as they may be diagnostic), or,
  when the two exits go to different blocks, an `ibranch` to the first
  exit's copies. Register copies inside pipelined loops (counted ones
  too) are folded into their sources, since the ring renames every
  value anyway: the renaming pass's `list = tmp` copy had made the
  pointer chase 6 cycles instead of 3. CoreMark's `find` loops run at
  3 cycles a node (II 3, 6 stages; 11-12 before, lcc's unpipelined
  if-converted loop about 9). 8C2, -O2: CoreMark 4,488 -> 5,127 it/s
  (+14%; lcc -O3 as v3 code 4,469), Linpack unchanged. C torture on the
  8C2 (all 1,639 execute tests, -O1/-O2/-O3/-Os): all pass, with 126
  while loops pipelined at -O2. Not when the loop is also entered by a
  prepared conditional `ct` (the latch of an enclosing loop with the
  same header, GCC's loop of two latches): its CTPR still points at the
  header, past the prologue put on the edge (GMP's `t-brootinv` hung).
  `core_list_reverse` isn't pipelined: its store to the node whose next
  field the next iterations load needs DAM in the kernel, as lcc does
  it.
- DAM in pipelined loops (counted and while): a loop that doesn't
  pipeline because a load may read what an earlier store of the loop
  wrote is tried again with that load as a lock load (`ld,sm ...,
  mas=0x4`, ALC0) and a check (`ld,5 ..., mas=0x3; rbranch`, new pattern
  `e2k_ldchk_jump`) in the last stage, after the stores it moved above
  and before the stores of what it loaded. The check moves to the last
  stage with the stores, keeping its row (between two such nodes only
  the rows count while placing; the DFA keeps it out of the loop end's
  row, both taking SS), and it is placed right after its lock load. A
  failed check (another iteration's store touched the bytes) branches
  to compensation code at the end of the function that redoes, in time
  order and under the current ring names, what ran between the lock
  load and the check and used its value (through values and
  predicates; every exit-test instance of that span, since a predicate
  keeps only the last), then jumps back after the check: the kernel is
  split there into two blocks. Those instances' operands and results
  are kept alive until the check (`e2k_ms_dam_plan`). Copies of the last
  iteration's values fold too now (instances -1 and -2 before the loop
  come from the copies' registers), which `reverse`'s `list = tmp`
  needed. One lock load per loop, so far. `core_list_reverse`: II 3, 3
  stages (8 cycles a node before). Checked on the 4C and 8C2 with lists
  that the reversal rewrites under itself (cycles, rho shapes; relcc2
  `toolchains/claude-e2k/dam/rev.c`): same results as without DAM, and
  with the `rbranch` removed it crashes, so the compensation runs and
  works. 8C2, -O2: CoreMark 5,127 -> 5,608 it/s. C torture on the 8C2
  (-O1/-O2/-O3/-Os): all 1,639 pass, 165 while loops pipelined at -O2,
  13 kernels with a check.
- A pipelined loop's prologue is a block of its own on each way in
  (`-mclock-prologue`, on), with the cycles of the modulo schedule
  (`e2k_ms_clocks`, like the kernel) instead of being scheduled by
  sched-ebb with the code before it. The modulo schedule counts the
  crossings between the clusters on every dependence, the list
  scheduler doesn't: CoreMark's matrix prologues stalled 4 cycles five
  times each (61 cycles for 23 of work). setbn gets a wide instruction
  of its own; copies in run at their own times, checked against the
  DFA (else the old way); empty wide instructions follow up to the
  kernel's first cycle when the prologue falls into the kernel, and a
  prologue that doesn't goes there with `ct` through the CTPR the loop
  end uses, which already holds the kernel's address (an `ibranch`
  would cost 6 cycles). A counted loop's 4-cycle wait after `rwd %lsr`
  goes when the prologue lasts that long. 8C2, -O2: CoreMark 5,608 ->
  5,695 it/s, Linpack 13.05 -> 11.32 s (+15%). C torture on the 8C2
  (-O1/-O2/-O3/-Os) and the real programs: all pass.
- Kernels get their ALU channels first, in their steady state (each
  kernel twice, the second time with what the first left as producers),
  and every prologue instance takes its node's channel in the kernel
  (`e2k_ms_twin`). The modulo schedule gives a node that reads its own
  last result no crossing cost, so that instance must stay in its
  channel all the way into the kernel; assigned on their own, prologue
  instances often went to the other cluster, a 4-cycle stall on the way
  in for each such node (CoreMark's matrix kernels measured 4.9 and 4.5
  cycles an iteration for a 4-cycle schedule, on the 4C). 8C2, -O2:
  CoreMark 5,695 -> 5,783 it/s, Linpack 11.32 -> 11.12 s; the matrix
  kernels now measure 4.0 and 3.9.

## v0.2 (2026-10-04)

v0.1 plus the runtime libraries (libatomic, libgomp, libquadmath), the
DejaGnu boards, GCC's own test suites run on the 4C, and the fixes they
led to.

### Results (Elbrus 4C, all through the `e2k-4c` board)

| Suite | PASS | FAIL | Results |
|---|---|---|---|
| GCC C (`check-c`) | 166,718 | 1,439 | `dejagnu/gcc-4c-2.{sum,log}` |
| g++ (`check-c++`) | 267,520 | 71 | `dejagnu/gxx-4c-2.*` |
| libstdc++ | 19,382 | 36 | `dejagnu/libstdcxx-4c-2.*` (42 rerun after a 4C outage: pass) |
| libgomp | all but pr52547 (trampoline) | | `dejagnu/libgomp-4c-*.sum` |
| libatomic | 54 | 0 | |
| ABI compat suite (C and C++, lcc<->gcc) | all | 0 unexpected | `compat-ringo/` |

(`dejagnu/` is relcc2 `toolchains/claude-e2k/dejagnu`, untracked.) The
C suite went from 3,325 to 1,439 failures with the fixes below. What
is left:

- guality at -O1 and above (1,165 + C++'s): var-tracking assignments
  are off because the port schedules in machine reorg; ia64 runs
  var-tracking in its reorg. -O0 guality passes.
- Not the compiler, same for lcc-built programs: the kernel starts
  processes with all FP exception flags set (~30 tests that assume clear
  flags: float*-nan, inf-compare-*, builtin-iseqsig-*,
  builtin-fp-int-inexact*, pr82692, c23-float-5); glibc's `fmin` keeps
  signaling NaNs (pr105414); libm's `cosh` raises SIGILL (pr68264);
  forced unwinding out of a signal handler (cleanup-8..11, C and C++);
  `long double` padding compared with memcmp (copysign1/2: the test only
  excludes x86/ia64).
- Gaps lcc shares: variable-sized return values (pr82564, pr8081,
  pr92088-2, nested-func-9/12/13/14/16/17, Wrestrict-17), frames over
  2 GiB (20031023-*, pr50092, pr105094, pr82389, pr108605).
- Port gaps: sibcalls (sibcall-3/4/9/10), trampolines (pr66633,
  libgomp pr52547), `__builtin_return_address (n > 0)`, complex `"r"`
  asm operands (pr55921, 20000804-1), patchable_function_entry, no
  speculation barrier.
- Target-dependent dumps (ctz, range tests, dse, thunk counts), gas's
  internal error on labels-3 -O3 -g (findings I8), the host objcopy
  for -gsplit-dwarf (pr83719, pr110885), a middle-end ICE with explicit
  -fvar-tracking-assignments (pr105537), analyzer complexity notes.
- C++: pr119916 assumes a 24-byte coroutine return object is returned
  in memory (E2K and lcc return it in registers); ext-floating11 (ICE
  in symtab verify) and constexpr-nsdmi5 fail in the full run but pass
  alone: to look at.
- libstdc++: 27_io file-io-diff (the harness diffs files left on the
  4C), 22_locale/messages (no catalogs on the target), names.cc (a
  glibc sigcontext.h member collides with the test's macros),
  30_threads 103382 (cancelling a condition_variable wait hangs at
  thread exit, also with the system libgcc_s; lcc's libstdc++ aborts).

Harness lessons: run check-c and check-c++ one after the other (they
share `gcc/`); `ssh-4c` spreads sessions over 6 ssh masters and
retries connections (sshd's MaxSessions/MaxStartups reset parallel
ones), and brings `.gcda` files back for gcov and -fprofile-use.

### Changes since v0.1

- Runtime libraries: libatomic and libgomp build unchanged; libquadmath
  needs the `__builtin_*q` builtins (now predefined as macros mapping to
  the `f128` ones, as rs6000 does). glibc's `<fenv.h>` breaks under C23
  (`femode_t`); the owner chose not to fix glibc in GCC, so the PoC's
  sysroot carries a patched `bits/fenv.h` (`mksysroot.sh`, see "Build and
  test"); with it no `-std=gnu17` workaround is needed. On the 4C: 4-thread 16-byte CAS mixing lcc
  and GCC code passes with ALT's libatomic and ours (shared, static);
  OpenMP (parallel for/reduction, atomic, critical, tasks) passes with 4
  and 16 threads, shared and static; libquadmath gives lcc's results (and
  a correctly rounded `sqrtq (0.5)` where lcc's GCC 11 copy is 1 ulp
  off), also when an lcc-built program loads it.
- libgcc defines lcc's `__cpu_info` (`libgcc/config/e2k/cpuinfo.c`,
  static libgcc only): MCST's static libc.a needs it for `dlopen`, NSS
  and iconv, so static links failed before. Filled from `%idr`; values
  match lcc's own on qemu v3/v5/v6 and the 4C (findings A10).
- Debug info works with MCST's gdb (findings A13): `DW_AT_frame_base`
  is a register expression from the CFI (`TARGET_DEBUG_UNWIND_INFO`
  returns UI_NONE; the prologue describes the CFA), because that gdb has
  no CFI unwinder and its `DW_OP_call_frame_cfa` is a procedure-stack
  offset. On the 4C gdb shows arguments, locals, structs and arrays in
  every frame at -O0/-O2; next/step/finish work
  (`toolchains/claude-e2k/gdb`).
- `-finstrument-functions` works (eeprof-1 passes at -O0..-O3; the
  earlier "abort" was the forced run missing the test's dg-options).
- DejaGnu boards (relcc2 `toolchains/claude-e2k/dejagnu`, untracked):
  `e2k-qemu` (sim config + `LD_LIBRARY_PATH` passed to the guest) and
  `e2k-4c` (ssh wrappers with the key; programs in
  `~/relcc2/claude-probe/dg/<pid>`, runtime libraries synced to
  `~/relcc2/claude-probe/dg/lib` by `sync-4c-libs`). Use
  `DEJAGNU=<dir>/site.exp make check-... RUNTESTFLAGS=--target_board=e2k-qemu`.
  libatomic's testsuite: 54/54 on both.
- libgcc_s exports `_Unwind_GetPCSP@GCC_3.0` (`libgcc/config/e2k/
  libgcc-e2k.ver`): MCST's glibc dlopens libgcc_s on thread exit and
  asserts it exists. Now every lcc libgcc_s export is present, same
  versions.
- libgomp uses the Linux configuration (`libgomp/configure.tgt`
  `e2k*-*-linux*`): futexes, pinned memory.
- libgomp's own testsuite on the 4C: all C, C++ and OpenACC-host tests
  pass except pr52547 (needs a trampoline). Runs: `libgomp-4c-2.sum`
  (C part; the C++ part was cut off when the 4C went down) and
  `libgomp-4c-3.sum` (C++/OpenACC: 3,129 pass; 4 output-order failures
  were the ssh harness, fixed and rerun: pass), in
  `toolchains/claude-e2k/dejagnu`.
- The 4C board multiplexes ssh (ControlMaster socket in
  `dejagnu/cm/`), merges stderr into stdout on the 4C (ssh loses their
  order), and is fine with `make -j8` for gcc and `-j4` for libgomp
  (owner: 16 threads on the 4C are fine; prefer the 4C to qemu, run
  tests in parallel). Both boards set `gcc,no_trampolines`; the qemu
  board wraps qemu in `timeout` (DejaGnu's limit didn't stop a hang).
- Inline asm: lcc's `x` constraint for long double, through
  `TARGET_MD_ASM_ADJUST` (pack with `movif` before the asm, `movx` +
  `movfi` after). glibc's mathinline.h asm sequences give lcc's bits at
  -O0..-O3, qemu and the 4C (findings A12).
- The quiet FP conditional move (`*movcc..._quiet`) clobbered a value
  operand: its DI scratch, written by `fcmpud*f` before the `merge`
  reads the values, was not earlyclobber, so the allocator could give
  it the register of the value to select (`islessgreater (x, y) ? a :
  b` returned garbage; GCC's fp-cmp-8, pr38016, pr109386).
- `-fstack-usage` reports the data-stack (USD) frame size; the window
  and return address live in the procedure and chain stacks and are
  not counted.
- Nonlocal goto and `__builtin_setjmp`/`__builtin_longjmp` work, through
  glibc (`e2k_expand_save_stack_nonlocal`): a frame can only be
  reentered by the kernel unwinding the chain stack. The receiving
  function keeps an 80-byte `jmp_buf` in its frame and calls `_setjmp`
  on it wherever GCC saves the nonlocal stack level (entry, after
  alloca, `__builtin_setjmp`); the save area holds its address. The
  goto writes the label into the `jmp_buf`'s return IP (offset 8, the
  saved `%cr0.hi`) and calls `longjmp`; `e2k_longjmp2` then returns into
  the frame at the label. No dispatch code, and `_setjmp` never returns
  twice at its call. Registers are those of the frame's latest call, as
  after any return. Caveat: the `jmp_buf` also restores `%br` from the
  `_setjmp` call, which will matter once loops rotate registers.
  Nested functions called directly work (no trampolines yet); lcc has
  neither.
- `TARGET_ATOMIC_ASSIGN_EXPAND_FENV`: atomic compound assignment of
  floating types saves and masks the FP environment, discards the
  exceptions of failed CAS iterations and raises those of the final one,
  like glibc's feholdexcept/feclearexcept/feupdateenv: float/double
  flags in `%pfpfr` (masks = flags << 7), 80-bit ones in `%fpsr` (masks
  in `%fpcr`). Uses undocumented builtins `__builtin_e2k_rrs_*` and
  `__builtin_e2k_rws_*` (`rrs`/`rws`). c11-atomic-exec-5 passes on the
  4C. It needs libatomic's `__atomic_feraiseexcept`, which was empty in
  builds configured before the sysroot's fenv.h fix (`HAVE_FENV_H`
  undefined): reconfigure libatomic.
- LTGT signals (fcmpod*f, as GCC has required since PR91323: `a < b ||
  a > b` folds to it), UNEQ and the UN* codes stay quiet (fcmpud*f).
  Because GCC's RTL reverses UNEQ to LTGT and back
  (`reversed_comparison_code_parts`), the FP cbranch/cstore/movcc
  expanders lower these codes at expand time
  (`e2k_lower_quiet_fp_cmp`): the flags go to an SImode pseudo and the
  condition becomes an integer test of them, so no FP UNEQ/LTGT is left
  in the RTL. Costs an `ands` before the `cmpesb` where `cmpandesb`
  would do (optimization item). pr91323 and fp-cmp-* pass.
- Scheduler: a dependence of any memory access on a store costs a cycle
  (`e2k_adjust_cost`). A load in the wide instruction of a store to its
  address reads the old value (4C, both st2+ld0 and st5+ld3; findings
  I9), but GCC only gave true memory dependences the store's latency:
  once a block has more than 32 pending memory references, sched-deps
  flushes its lists and later loads get just an anti dependence (cost
  0) on the flushing store, so a store and a dependent load could share
  a wide instruction. Miscompiled builtin-shufflevector-1 at -O2.
- `getsp` with a register amount takes a window register (new class
  `W_REGS`, constraint `w`). When `getsp` needs more stack, the kernel
  decodes the amount from the instruction (arch/e2k/kernel/getsp.c) and
  understands only literals, window registers and `%g16..%g31`; from
  `%g0..%g15` it falls back to 16 KiB, so VLAs or alloca over that
  faulted (loop-interchange-15; findings A16). lcc moves the amount to
  `%g24`.
- C++ thunks are written out by `e2k_output_mi_thunk`, as lcc does: no
  `setwd`, adjust `this` in `%r0` (`%r1` after a hidden result
  pointer), load a vcall offset through `%g0`, then `disp`/`ct` (not
  `call`) to the target, which runs in the caller's call. GCC's generic
  thunks can't forward `...`; variadic virtual functions in a secondary
  or virtual base now work (thunk3, pr81812; checked on the 4C at -O0,
  -O2, -fPIC).


## v0.1 (2026-10-03)

Base: GCC mainline `ea32419e8c4` (GCC 17 development). Target
`e2k-linux-gnu`, 64-bit mode only, code for elbrus-v3 (runs on v3 and
later). C and C++ with GCC's own libgcc (MCST's unwinder) and mainline
libstdc++.

### Results

Hardware is the reference (Elbrus 4C, v3), then MCST qemu
(`-cpu elbrus-v3`). lcc 1.29.16 is the ABI oracle.

| Test | MCST qemu | 4C |
|---|---|---|
| relcc2 compat suite, C units (1,683 tests per pair): lcc->gcc, gcc->lcc, gcc->gcc | 0 unexpected at -O0, -O1, -O2 | 0 unexpected at -O2 |
| compat suite, C++ `eh` unit (170 per pair, linked with `l++`) | 170/170 all pairs, -O0 and -O2 | 170/170 all pairs, -O2 |
| `eh` objects of every pair linked with this GCC's libstdc++/libgcc_s (shared and static) | 170/170 | 170/170 |
| gcc.c-torture/execute (1,646 applicable) | all pass at -O0, -O1, -O2, -O3 (but `20101011-1`: qemu can't raise SIGFPE) | all 1,639 built pass at -O0, -O2, -O3; -O2 -fPIC all but `20000603-1` (DR 236 aliasing, generic GCC) |
| C++ test `toolchains/claude-e2k/cxx/eh2.cc` (EH, rethrow, dtors in deep frames, virtual throw, std::function, map, iostreams, std::format) | pass -O0..-O3, static and shared | same |
| relcc2 `tools/abi/probes/dso` (PIE, non-PIE, static, mixed with lcc; lazy and BIND_NOW) | | pass |
| threaded atomics test mixed with lcc (`toolchains/claude-e2k/atomics`) | | pass (a negative control fails as it should) |
| long double arithmetic vs lcc (`toolchains/claude-e2k/ldbl`) | | bit-identical |
| quiet FP compares (`toolchains/claude-e2k/quietcmp`) | values right (qemu wrongly raises FE_INVALID) | pass, no FE_INVALID |

Of the 52 torture tests the runner skips, 42 pass when forced (computed
goto included); the other 10 are listed under "Not done" (plus DFP and
an x87 asm test).

Speed vs lcc -O2 on the 4C (`toolchains/claude-e2k/bench`): dot 2.0x,
isum 5.0x, saxpy 1.6x, mm128 1.3x slower; fib 0.9x, qsort 1.1x. The gap
is software pipelining, loop mode, APB and predication.

### Works

- C and C++ through GCC's front ends: exceptions, RTTI, mainline
  libstdc++ (including `<format>`; `<stacktrace>` builds).
- The lcc calling convention, including variadic, unprototyped, narrow
  integer extension, aggregates of any size, results over 64 bytes, C++
  hidden-pointer returns, `va_list` and `longjmp` across compilers.
- long double (x87 extended, as lcc), `__int128`, `__float128` (soft-fp
  in libgcc), `_Complex`.
- PIC, PIE, TLS (GD, IE, LE), jump tables, computed goto, alloca/VLAs.
- Atomics as lcc emits them (1/2/4/8 bytes); 16 bytes need libatomic,
  which isn't built yet.
- `__builtin_return_address (0)`, `__builtin_eh_return`, DWARF CFI
  (`.eh_frame`) for MCST's unwinder.
- Scheduling and bundling into wide instructions, with `nop N` padding;
  loop back edges through a prepared `ct`.
- lcc's source conventions: `__e2k__`, `__iset__`, `__ptr64__`,
  `__float80`, `__float128`, `q`/`w` constant suffixes; never `__LCC__`.

### Not done

| Item | State | What it needs |
|---|---|---|
| Nested-function trampolines | `sorry` (4 torture tests); lcc doesn't support nested functions either (A14) | A trampoline design: executable stack or not, loading `%g12` |
| Nonlocal goto, `__builtin_setjmp`/`longjmp` | compile, crash at run time (920428-2, built-in-setjmp); lcc has neither (A14) | Unwinding the chain stack, which glibc does only via the `e2k_longjmp2` syscall on an 80-byte buffer; GCC's builtin buffer is 5 words |
| `__builtin_apply` / untyped calls | hangs (pr47237); lcc doesn't have it | Probably leave unsupported |
| Per-function `setwd dbl` (relcc2 D7, owner's decision) | always `dbl = 0` (correct, as D7 says to start) | Choose `dbl = 1` after expand where 32-bit unsigned results need zero extension; an optimisation |
| `-pg` profiling | `sorry` | `mcount` convention (what does lcc do?); gcov untested |
| Inline asm | constraints `r` (even pair for 16-byte types, as lcc's new meaning), `x` (long double; since v0.1), `j` (pred), `b`, `t` (CTPR), `I`, `Z` | `x` for 16-byte vectors/`__int128` on v5+; more as real code needs them |
| `-march=elbrus-v4..v7` | accepted, but code is always v3 | ISA-dependent patterns (v5 `ldqp`/`stqp` 16-byte atomics, new ops), `e_flags`, v6 timings |
| Runtime libraries | libgcc, libstdc++; since v0.1 libatomic, libgomp, libquadmath | sanitizers, libitm, libssp, libvtv; a fixincludes rule for glibc's `<fenv.h>` (needs autogen) |
| Sibling calls | disabled | Tail calls through `ct` after the window is restored |
| Debug info in gdb | since v0.1: works in MCST's gdb on the 4C (A13) | gdb's own testsuite; C++ and optimized-code locations |
| Test suites | only c-torture/execute and the compat suite | DejaGnu boards for qemu and the 4C; gcc.dg, g++.dg, libstdc++ testsuite; a native bootstrap |
| Performance | see the speed line above | Conditional `ct`/early return via `%ctpr3`, earlier `disp`, predication, if-conversion, software pipelining, loop mode, APB, cluster-aware DFA |
| 32-bit and protected (`e2k128`) modes | not started | Out of scope (ALT Linux ships no runtimes for them) |
| DFP | not supported | As lcc |

## Design, with the pitfalls behind it

Each bullet is what the PoC does; **Pitfall** lines are the bugs that
shaped it, worth knowing for a rewrite.

### Registers (`e2k.h`)

- Hard registers: 0–31 `%g0..31`, 32–95 `%r0..63` (window), 96–103
  `%b[0..7]` (outgoing arguments and results), 104–135 `%pred0..31`,
  136–138 `%ctpr1..3`, 139 soft frame pointer, 140 soft arg pointer.
- `%r` registers are saved by the hardware window, so they are
  call-saved (`LOCAL_REGNO`); `%g` and `%b` are call-clobbered.
- Fixed: `%g13` (TP), `%g24..31` (rotating base), `%r8` (stack pointer
  copy), the CTPRs. `%r9` is the hard frame pointer when one is needed;
  `%g12` the static chain; `%g11` carries the caller's buffer address for
  results over 64 bytes (internal to the PoC, not ABI).
- 16-byte modes (TI, TF, XF) live in even-aligned register pairs and are
  split into DImode moves after reload, only for offsettable addresses.
  **Pitfall:** `change_address` on a reg+reg address made invalid RTL.
- DWARF numbers: `%r` 0–63, `%b` 64+, `%g` 128–159 (the spec gives none
  for `%g`). **Pitfall:** GCC's `debugger_reg_number` ICEs without one.

### Frame and window (`e2k.cc`: `e2k_expand_prologue`, `e2k_compute_window`)

- The prologue is `setwd` alone in the first wide instruction, then
  `getsp -size, %r8` when there is a frame or `%r8` is used.
  `FRAME_GROWS_DOWNWARD`; AP = FP = the entry USD.
- The window size is computed at final time from the hard registers
  used: W = pairs up to the highest `%r`; with calls or `%b` use,
  `setbn rbs=W, rsz=3`, `wsz=W+4` and `call ..., wbs=W`; else
  `wsz=max(W,4)` (4 is the hardware minimum, measured).
- **Pitfall:** the prologue is emitted in a nested sequence, so the scan
  for `%r8` uses must start from `get_topmost_sequence ()`.
- **Pitfall:** a blockage between `getsp` and a store carried the
  scheduler's new-cycle mark away; the bundler carries it to the next
  insn that prints.

### Arguments and results (`e2k_function_arg_1`, `e2k_slot_rtx`, `e2k_struct_value_rtx`, `e2k_expand_call`)

- 8-byte slots, values over 8 bytes start at even slots, slots 0–7 in
  registers; aggregates and complex values are a PARALLEL of DImode
  pieces (the last one SImode if it has 4 bytes or fewer). Variadic
  (last named and unnamed) and unprototyped arguments are a PARALLEL with
  a null first element, so they go in both registers and memory.
  `ACCUMULATE_OUTGOING_ARGS`, `REG_PARM_STACK_SPACE` 64 (or the result
  size if over 64), `STACK_PARMS_IN_REG_PARM_AREA`.
- Narrow integers: `PROMOTE_MODE` to DImode, the caller extends, the
  callee sees the narrow type and re-extends (`e2k_laying_out_parms`).
  **Pitfall:** PROMOTE_MODE must agree with `promote_function_mode`, or
  expand ICEs.
- Results up to 64 bytes in `%r0..7` (callee) / `%b[0..7]` (caller).
  `DEFAULT_PCC_STRUCT_RETURN 0`. **Pitfall:** with the default, all
  structs went to memory.
- Over 64 bytes (C rule: written at the caller's USD, no hidden
  pointer): the callee builds the value in a local buffer and the
  epilogue copies it to the entry USD (after all arguments are read,
  since the result overlaps them); the caller's call expander copies it
  from its USD into the buffer GCC addresses in `%g11`. **Pitfall:**
  dse1 deleted the stores into the buffer; its address is hidden behind
  an UNSPEC_OPAQUE copy. **Pitfall:** the call expander runs in a
  sequence of its own; finding the `%g11` load means walking the
  enclosing sequences.
- C++ types that aren't trivially copyable (TREE_ADDRESSABLE) return
  through a pointer in argument slot 0, as lcc does: `struct_value_rtx`
  returns NULL for them and they don't grow `REG_PARM_STACK_SPACE`.
  **Pitfall:** copying them like C structs broke `std::string` (SSO
  pointer into the callee's buffer).

### Calls and returns

- `disp %ctpr1, sym` (or `movtd %rN, %ctpr1`) as its own insn, then
  `call %ctpr1, wbs=W`; the return is `return %ctpr3` (a non-volatile
  unspec, so it can be hoisted) plus `ct %ctpr3`.
- `movtd` to a CTPR only in ALC0 (gas rule; the YAML lists 0, 1, 3, 4).
- Divisions clobber `%ctpr2` so that RTL PRE can't hoist a trapping
  division above a call (pr38819).
- Loop back edges (`e2k_prepare_loop_branches`, machine reorg before
  scheduling): `disp %ctprN, header` on every entry edge of an
  innermost call-free loop, the back edge becomes `ct %ctprN [? pred]`.
  A taken `ibranch` costs 6 cycles, a prepared `ct` none.
  **Pitfall:** `loop_optimizer_init` with LOOPS_NORMAL changes the CFG;
  use AVOID_CFG_MODIFICATIONS. Fixed CTPRs fail `register_operand`; use
  a dedicated predicate.

### Compares

- Fused compare-and-branch, cstore and movcc insns with a BImode
  scratch, split after reload into `cmp*b` + `ibranch ? [~]%pred` or
  `merge`. Integer `ne`/`gt`/`ge` invert the predicate; FP `gt`/`ge`
  swap operands. `merge` picks its first operand when the predicate is
  false.
- Quiet FP codes (UNLT, UNLE, UNGT, UNGE, UNEQ, LTGT) can't use
  `fcmpnlt`/`fcmpnle`, which signal on quiet NaNs: `fcmpud{s,d}f` or
  `fxcmpudxf` into a register (x86 flags: less 0x1, equal 0x40, greater
  0, unordered 0x45), then `cmpandesb`/`cmpesb`. Only those patterns get
  a DImode scratch.

### Integer and FP operations

- `sxt` codes: 0/1/2 sign-extend 8/16/32, 4/5/6 zero-extend (the guide
  says the opposite; checked on hardware). `setwd dbl=0`: 32-bit
  operations leave the upper half alone, so SImode values are kept
  extended explicitly where needed.
- `SHIFT_COUNT_TRUNCATED` 1 (counts are modulo the width; only SI and DI
  shifts exist).
- long double (XFmode) is a register pair (64-bit mantissa, 16-bit
  sign+exponent zero-extended); each operation is one insn doing
  `movif`, the `fx*` op, `movfi`, and re-extending the exponent with
  `sxt 5`. **Pitfall:** two-operand `neg`/`abs` in one wide instruction
  is "an excessive ALF instruction" for gas; they are type `multi`.
- `__float128` is a distinct type (not `long double`), so libstdc++'s
  `numeric_limits<_Float128>` doesn't clash; `q` and `w` suffixes.

### Scheduling and bundling (`e2k-sched.md`, `e2k_reorg`, `e2k_gen_bundles`)

- `TARGET_DELAY_SCHED2`; machine reorg runs `schedule_ebbs`, records the
  clock of every insn in the scheduler hooks, then `e2k_gen_bundles`
  marks wide-instruction boundaries and `nop N` gaps; braces are printed
  by `FINAL_PRESCAN_INSN` / `TARGET_ASM_FINAL_POSTSCAN_INSN`. Insns that
  print several wide instructions use `%#` (type `multi`), atomics print
  their own braces (type `raw`), and user asm is wrapped in
  `.accept`/`.ignore strict_delay`.
- DFA: ALC0–5 with load/store units and their exclusions, four literal
  syllables (`e2k_insn_lits` counts them per insn), CS0/CS1/SS;
  latencies from timing.md.
- `TARGET_SCHED_EXPOSED_PIPELINE` and output dependences cost at least 1:
  all operations in a wide instruction read the old registers.
  **Pitfall:** without that, the scheduler put a use and a redefinition
  of one register in the same cycle (loop-2e).
- **Pitfall:** templates that print a literal not present in the RTL
  (`neg`/`abs` sign masks) must be counted by `e2k_insn_lits`, or gas
  runs out of literal syllables.

### PIC and TLS

- No GOT register: a pseudo loaded by `rrd %ip` + `_GLOBAL_OFFSET_TABLE_`
  literal in one wide instruction; `@GOT`, `@GOTOFF`. PIC jump tables add
  the table address. TLS GD calls `__tls_get_addr (module, offset)`; IE
  and LE use `%g13`.

### Atomics

- RMW operations are lock-wait load (MAS 0x7, ALC0) + wait-unlock store
  (MAS 0x2, ALC2) loops with `rbranch`, as lcc; fences and seq_cst/
  release accesses use `wait ld_c, st_c`.

### Runtime (`libgcc/config/e2k/`, `libgcc/unwind.inc`)

- MCST's E2K libgcc files from lcc 1.29.16 (GPL, imported verbatim in
  `777ddd3000a`, then adapted): the unwinder walks the chain stack with
  the `access_hw_stacks`/`set_backtrace` syscalls; `.eh_frame` is used
  only to find FDEs and LSDAs.
- `__builtin_return_address (0)` is `rrd %cr0.hi` masked to 48 bits;
  `__builtin_eh_return` expands to nothing (the unwinder rewrites the
  chain with `set_backtrace` and returns normally).
- MCST's E2K hunks of `unwind.inc` are needed too (a chain-stack cache
  buffer for `uw_init_context`, reinitialised before phase 2).
- The procedure-stack layout (v1–v4 vs v5+) is chosen from `%idr`
  (model in bits 0–7) instead of lcc's `__builtin_cpu_is`.

## Build and test

Build environment: PATH must start with relcc2
`toolchains/claude-e2k/bin` (`e2k-linux-gnu-*` symlinks to lcc's
binutils). The sysroot `toolchains/claude-e2k/sysroot` is lcc's `fs/`
plus the empty `lib`/`usr/lib` GCC's search paths need and a copy of the
`usr/lib64/libc.so` linker script; recreate it with
`toolchains/claude-e2k/mksysroot.sh`.

```
L=/opt/mcst/lcc-1.29.16.e2k-v3.linux-6.1
cd toolchains/build-gcc-claude
../gcc-claude/configure --target=e2k-linux-gnu \
  --prefix=$PWD/../gcc-claude-install \
  --with-sysroot=<relcc2>/toolchains/claude-e2k/sysroot \
  --with-as=$L/binutils/bin/e2k-linux-as --with-ld=$L/binutils/bin/e2k-linux-ld \
  --enable-languages=c,c++ --disable-bootstrap --disable-multilib \
  --disable-libsanitizer --disable-libssp --disable-libitm --disable-nls \
  --enable-checking=yes,rtl --disable-werror
make -j10 all-gcc all-target-libgcc all-target-libstdc++-v3 \
  all-target-libatomic all-target-libgomp
make -j10 all-target-libquadmath CFLAGS_FOR_TARGET="-g -O2 -std=gnu17"
make install-gcc install-target-libgcc install-target-libstdc++-v3 \
  install-target-libatomic install-target-libgomp install-target-libquadmath
```

(v0.1 was configured with `--disable-libquadmath --disable-libgomp
--disable-libatomic` too; `config.status.v0.1` in the build directory.)

After a compiler change that affects code generation, rebuild the
libraries from scratch (`rm -rf e2k-linux-gnu/libgcc
e2k-linux-gnu/libstdc++-v3`): make doesn't rebuild them.

Compilers: `toolchains/gcc-claude-install/bin/e2k-linux-gnu-{gcc,g++}`,
or the uninstalled wrapper `toolchains/claude-e2k/scratch/gcc-e2k`.
Programs link with GCC's own driver, libgcc and libstdc++ against lcc's
glibc. Run under qemu with `qemu-e2k -cpu elbrus-v3 -L $L/fs` (add
`-E LD_LIBRARY_PATH=<install>/e2k-linux-gnu/lib64` for shared
libstdc++).

```
G=toolchains/claude-e2k/scratch/gcc-e2k
GXX=toolchains/gcc-claude-install/bin/e2k-linux-gnu-g++
python3 tools/abi/compat/run.py toolchains/compat/gen --target v3 \
  --cc gcc="$G -O2 -std=gnu17" --cxx gcc="$GXX -O2" \
  --pairs lcc:gcc,gcc:lcc,gcc:gcc -o toolchains/claude-e2k/compat-v3 -j8
#   add --remote claude@ringo.lan --ssh-key secrets/id_ed25519
#   --remote-dir relcc2/claude-compat --remote-jobs 4 for the 4C
toolchains/claude-e2k/torture/run.sh SRC OPT OUTDIR   # one test, qemu
toolchains/claude-e2k/torture/hw.sh NAME "OPTS"       # all tests, 4C
```

`-std=gnu17` for C: GCC 17 defaults to C23, where `f()` takes no
arguments (the `unproto` unit needs K&R calls), and lcc's glibc headers
break `<fenv.h>` under C23 (findings A8).

## Working notes (for agents)

- Commits: worktree-local identity "Claude (Opus 5.5)"; atomic commits;
  update this file with each one.
- On the 4C use only `~/relcc2/claude-probe` and `~/relcc2/claude-compat`;
  other agents work there (e.g. `~/relcc2/claude-loops`; don't touch).
  If ssh says "No route to host", the 4C is down: stop and tell the owner.
- The 8C2 (`claude@geofront.lan`, same key; Elbrus-8C2, v5, Elbrus
  Linux 9.5.5, glibc 2.35 like lcc's sysroot) is a second test machine:
  `~/relcc2/claude-probe` there, DejaGnu board `e2k-8c2` (`ssh-8c2`,
  `scp-8c2`, `sync-8c2-libs`), `make -j4`. Use plain `ssh`/`scp` with the
  key for it, not the 4C wrappers.
- Never look at `/opt/mcst/gcc-16.0.0-A.XXX.e2k-v7.5.10` on the host:
  unknown origin, relcc2 decision 4.

## Next (checkpoint 2026-10-05 evening, speculation and real programs)

State: since v0.2, counted loops on `%lsr`, DAM, unrolling, the port's
modulo scheduler with rotating `%b[]`, loop versioning for aliasing,
per-function `dbl`, more inlining, compiler-chosen ALU channels, every
branch prepared (`disp` + `ct`), check-free control speculation (`,sm`
on whatever moved above a branch) with renaming after register
allocation. 8C2 (v5 hardware running this v3 code), -O2: CoreMark
4,488 it/s (v0.2-era build 2,672; lcc -O3 as v3 code 4,469, tuned for
v5 4,530), Linpack 13.16 s for 8,192 repetitions at size 200 (its
KFLOPS figure varies too much to compare; lcc is still about 1.4x
faster). C torture/ieee/dg-torture on the 8C2: see the last entries
of "Since v0.2". The 4C is back (it was down 00:45-06:00).

Real programs, built with -O2 and run on the 4C (relcc2
`toolchains/claude-e2k/real`, `real-all.sh NAME CC CFLAGS`): zlib
(example, minigzip round trips), bzip2 (its reference samples), xz
(14 test programs and round trips), zstd (60 s fuzzer, 60 s stream
test, round trips), GMP (`make check`: 177 of 178, the other one skips
without assembly), pcre2 (RunTest), expat (runtests, 4,932 checks).
They found five back-end bugs the torture suites didn't: edge
insertions the pipeliner left uncommitted (GC crash, lost copies),
the renaming pass and `long double` register pairs, a DAM check above
a NULL test, the missing cycles across a fall-through into the next
block (a taken `ct`'s predicate read isn't interlocked), and jump-table
loads hoisted above their range check.

Measuring: `toolchains/claude-e2k/perf/build.sh NAME "CC" O2`, then
`run8.sh DIR...` on the 8C2 (`run.sh` for the 4C); check "Correct
operation validated" (CoreMark calibrates its iteration count, and
`crcfinal` depends on it). `tools/isa-score/profile.py` on the 4C for
where the cycles go. Pipelining tests: `toolchains/claude-e2k/ms`.

Plan, in order:
1. CoreMark's list loops (`core_list_find` 12 cycles a node against
   lcc's 9, `core_list_reverse` 8 against lcc's 2): while-loop modulo
   scheduling with an exit predicate (predicate rotation, `abp`) and DAM
   in the kernel for the store in `reverse`; if-conversion of
   two-exit loops into one predicated block.
2. `core_bench_state`: if-conversion to predicated operations
   (`define_cond_exec` or merges) of the state machine's short arms.
3. Pipelined loops whose arrays may overlap; the `-mfmul-add` slowdown;
   APB for pipelined loops.
4. Smaller: prologue cost of deep modulo schedules (short trip counts),
   return prepared at function entry in leaf functions, loop-exit
   `disp`s hoisted out of loops, var-tracking assignments.
5. More real programs (sqlite, Lua, jq) and the full C, g++, libstdc++
   and compat suites, last run at v0.2.
6. Port gaps: trampolines, sibcalls, `-march` v5+ (64-bit loop count in
   `%lsr1`).
