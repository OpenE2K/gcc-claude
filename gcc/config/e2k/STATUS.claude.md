# E2K back end proof of concept: state

Written by Claude (Anthropic) on the branch `claudes-e2k-compiler`, from
the relcc2 specification (`spec/isa`, `spec/abi`, `doc/gcc-port-plan.md`)
to find out what the spec is missing. Not for contribution to GCC (GCC
refuses AI-written code); the owner writes the real port by hand and may
reuse the design. Spec gaps go to relcc2 `docs/spec-poc-findings.md`.

This file is the source of truth for the work; update it with every
commit. Tags `v0.1`, `v0.2` and `v0.3` mark the states described in
the sections of those names; "Since v0.3" lists what came after.

## Since v0.3

- Renaming for speculation (`e2k_spec_rename`) counts a value its block
  computes and that can move up as it is (an address added up for a
  load) as available at the branch, as it did a renamed one: a load
  whose address its own block computed moved above no branch (bzip2's
  mainGtU, `block[i1 + k]` at every step).
- Zero extensions under `setwd dbl = 1` (relcc2 findings A18, P21):
  every 32-bit integer ALU operation zero-extends its result there
  (probed on the 4C and the 8C2: merges, rotates, divisions, lzcnts and
  popcnts too; FP-to-integer conversions and movts not), so those got
  extending patterns too; REE is on at -O2 (`-free`, which each target
  enables); and a pass after REE (`e2k_dbl_zext`) folds an extension
  whose operand an extending operation set earlier in the block: the
  operation sets the 64-bit register, and the extension becomes a copy
  (deleted in place) that cprop_hardreg forwards. REE alone takes a
  32-bit merge for a conditional copy and keeps the extension when it
  writes another register. zlib's deflate.c: 149 -> 74 zero extensions
  (REE alone 90; lcc 7, most of the rest are truncations of 64-bit
  values). Speed on the 8C2 the same within noise.
- Predicate logic of three and four conditions in one wide instruction
  (`e2k_landp3`, `e2k_landp4`): the four ELPs load `@p0-@p3`, and CLPs
  chain at most two deep (gas: "maximal supported cascading of 2",
  findings I20), so four conditions are a tree, `landp (landp (c1, c2),
  landp (c3, c4))`, still C's order: landp ignores a diagnostic second
  operand when its first is false. The DFA has landp -> landp 1 cycle
  and landp -> a predicated operation 2 (timing.md).
- Chains of branches to one place are merged (`-mmerge-chains`, on;
  `e2k_merge_chains` in machine reorg): blocks B1 ... Bk, each entered
  only from the one before and branching to T, become one block that
  computes every condition and branches once, on their landps (above).
  The operations of B2 ... Bk run before the branches that guarded them,
  speculatively (",sm"), and landp ignores the diagnostic predicate of
  a condition whose guard didn't hold (findings I18, probed on the 4C
  and the 8C2). The last block may branch elsewhere and fall through to
  T. Only blocks of operations with a speculative form, none setting a
  register live at T or a predicate an earlier condition reads; each
  chain's landps get predicates of their own in the function. A copy
  that renaming puts after a speculative operation is speculative too
  (gcc.c-torture 20180226-1 trapped). Alone it makes zlib slower (8C2,
  -9: 2.24 -> 2.36 s: the common early exit of longest_match's chain
  walk now waits for all four conditions); it is for the pipeliner
  (next).
- Pipelined while loops with a merged chain and a side way in (zlib's
  longest_match: the chain walk's four tests merged, its step `cur =
  prev[cur & mask]` with two exits merged, and the rare path after a
  match coming back to the step): before the branches are prepared, the
  loop's second block is copied for the other ways into it
  (`e2k_ms_tail_dup`), so that the loop is two blocks entered at the
  top; the first block's exit test may be a landp tree (all of it runs
  again after the loop to tell the exits apart, the compares
  speculative), placed as a tree (each predicate after its own, at most
  II before its last reader); an entry by a conditional ct whose disp is
  in its own block takes a prologue (the disp is pointed at it,
  `e2k_ms_split_entry`); and the loop end's own disp, there when GCC's
  loop wasn't innermost, goes to the start of each prologue. Copies
  `e2k_ms_move_b` puts on such an entry go before its jump instead (their
  registers dead on its other way), and a loop with a call or asm is
  turned down before anything changes (`e2k_ms_move_b` had renamed a
  call's `%b[]` arguments: pcre2's name table scan passed strcmp NULL).
  longest_match: II 8, 3 stages, against about 22 cycles a step before
  (the recurrence `and`, `shl`, `ldh` with the crossing cycle the
  scheduler assumes between any two operations). zlib -9: 8C2 2.24 ->
  1.26 s (lcc 1.18), 4C 4.40 -> 2.37 s (lcc 2.21).
- Control speculation fixes, found when longer superblocks (below) made
  zstd's fuzzer and GMP's t-fac_ui crash:
  - an operation sched-ebb moved to another block got ",sm" only if its
    block's place in the layout, recorded before scheduling, came after
    its new one; the scheduler can shift that numbering, and a load
    moved two blocks up in zstd's tree search ran non-speculatively.
    Now by block identity (`e2k_spec_mark`);
  - a taken transfer's whole wide instruction runs, but a dependence on
    a jump cost 0, so an operation the jump's target must not see (one
    without a speculative form, or setting a register live there) could
    share the jump's instruction; and one that shares it without a
    dependence runs on the taken path too. Now such a dependence costs
    a cycle (`e2k_adjust_cost`; also any dependence on a call, which
    reads its arguments in its instruction), and what shares a jump's
    instruction gets ",sm". CoreMark on the 8C2: 5,808 -> 5,764 it/s,
    the price of the placements that were wrong.
- sched-ebb extends its superblocks through fall-throughs down to 10%
  likely (`tracer-min-branch-probability`; GCC's default without a
  profile is 50): loads and ALU operations move above a branch at no
  cost here, and GCC guesses "if (a != b) return" taken, which ended an
  EBB at every step of bzip2's mainGtU. 8C2: zlib -9 2.24 -> 2.17 s,
  bzip2 -9 2.50 -> 2.35 s (without the merging and pipelining above).
- Scheduler model corrected from spec/isa/timing.md: `getsp` -> use 2
  (was 1), `fdtofs` 6 (7 to integer operations), `fdivs` 11 and `fsqrts`
  12 (all divides were 14), and the divider in ALC5, which all divides
  share (busy the next cycle; integer divides two more, `sdivd` wanting
  3 apart on v3). Found by rereading the spec against e2k-sched.md.
- The return is prepared at the entry of a function without calls
  (`return %ctpr3` after `setwd`, as lcc does): `return` -> `ct` costs 6
  cycles, which every epilogue paid in nops. Nothing else takes
  `%ctpr3` there (calls would empty it; e2k_prepare_branches takes only
  a CTPR dead at its branch).
- Byte-compare loops with two exits (xz's lzma_memcmplen, "while (len <
  limit && a[len] == b[len]) len++", 113 million iterations in xz -6)
  pipeline: the unroll hook no longer unrolls such a store-free loop of
  up to three blocks with more than one exit (unrolled, its copies exit
  to different places and nothing pipelines them; one exit and a branch
  inside stays unrolled, for the scheduler), and hw-doloop leaves a
  loop of two blocks whose first one exits early to the while-loop
  pipeliner (on %lsr it would need "ct ? ~p && %NOT_LOOP_END", not done
  yet), splitting the counted loop end it keeps into a decrement, a
  compare and a branch (`e2k_hwloop_fail`). The loop runs at II 3
  against about 7 cycles a byte (lcc: 1, with rotating predicates).
- Fixed (GMP: t-gcd, t-hgcd, t-hgcd_appr, t-perfpow and t-root
  aborted once hw-doloop left loops like MPN_NORMALIZE, "while (n > 0
  && p[n - 1] == 0) n--", to the while-loop pipeliner): in a two-block
  while loop, a register e2k_ms_move_b gave a value of %b[0..7] didn't
  get its first block's exit value back after the loop, since its copy
  to %b[] was still pending on the exit edge and dataflow didn't show
  it live there; an early exit then returned the count decremented.
- The return prepared at a leaf function's entry goes after the
  prologue's blockage, which waited for its 6 cycles (`nop 5` at the
  entry of every leaf function).
- Rotating predicates in pipelined while loops (`-mrotate-preds`, on;
  spec/isa/loops.md, "Rotation"): the exit test's compares and landps
  get names in a ring of their own, `setbp psz = R - 1` (with the
  prologue's setbn) and `abp` at the loop end making the old `%pred0`
  the new `%pred1`, as lcc leaves its while loops through "ct ?
  %pred1". A predicate may then live longer than II, which kept while
  loops at II 3 or more: strlen-like loops run at II 1, xz's
  lzma_memcmplen and pcre2's strcmp at II 2. Packed as the `%b[]`
  values (`e2k_ms_assign_pnames`); the exit test goes as late as it
  can; no predicate below the ring may be live around the loop, and
  the name the loop end reads is kept free in its cycle (the jump comes
  last in the insn stream, so dataflow would see it read a write of
  that cycle and delete the prologue's). `setbp psz = 0` leaves.
  4C: xz -6 20.96 -> 20.19 s, zlib and bzip2 about 1% faster.
- A pipelined loop's copies into its ring before the loop and out of
  it after are speculative (",sm"): a register the loop may leave
  unchanged is copied in and back out, and before the loop it may hold
  a diagnostic value from a speculative load that nothing reads on that
  way (xz's index_tree_next: a register `e2k_ms_move_b` counts live at
  the first exit; xz's test_index got SIGILL once more loops pipelined,
  below). Copies out were speculative only after a two-block while loop
  with one exit.
- A 32-bit induction step whose sum is also compared, before register
  allocation (`e2k_dbl_widen`, after combine, under `dbl = 1`):
  PROMOTE_MODE keeps `unsigned len` in a 64-bit pseudo, so `len + 1`
  compared with a limit and assigned back is an addition, a compare and
  a zero extension into the variable, which combine can't fold (two
  uses), and the extension sits on the recurrence. When the 32-bit
  pseudo's only definition has a zero-extending form and reads the
  variable, a 64-bit pseudo takes it in that form, the extension
  becomes a copy RA ties, and the compare reads its low part. Only
  recurrences: widening loop-count computations as well changed the
  allocation and cost Linpack 0.27% on the 4C; as it is, Linpack
  592.8 -> 594.5 K on the 4C (against no widening).
- The pipeliner's lower bound on II counts ALU operations, not the
  landps of an exit test, which run in the PLS: a while loop of six
  operations and a landp had II 2 at least.
- The doloop pass leaves alone a loop of two blocks whose first block
  exits too (`e2k_doloop_declined_p`, in the doloop_end expander; xz's
  lzma_memcmplen): hw-doloop doesn't put such a loop on `%lsr`, and
  `e2k_hwloop_fail` split its counter back into a decrement and a
  compare with zero next to the loop's own variable, still needed after
  the loop: an operation more per iteration than the compare it
  replaced. With the two entries above, lzma_memcmplen's kernel is six
  operations at II 1 (was seven at II 2), as lcc's: 1.1 cycles a byte
  on the 4C (was 2.0, 113 million bytes in xz -6).
- If-conversion puts loads and stores under a predicate in integer
  code (`ld*`, `st*` and the zero-extending loads are predicable): a
  branch around stores becomes straight code (xz's binary tree walk,
  a predicated store on each side; optimum_normal's price updates,
  four predicated stores and one block per iteration). Not in arms with
  FP operations, where they stalled the kernel (findings I19;
  `e2k_ifcvt_modify_tests`). A limit of 12 operations for both arms
  instead of 6 made no difference measurable on the 4C. With the four
  entries above, on the 4C: xz -6 20.68 -> 17.70 s (lcc 14.28; profile
  2,659 -> 2,441 million cycles, lzma_mf_bt4_skip 1,327 -> 1,161),
  xz -d 0.30 -> 0.27 s, bzip2 -d 1.37 -> 1.33 s, zlib and bzip2 -9
  the same, CoreMark 2,882 -> 2,889 it/s.
- A branch to the target of one before it in a chain of fall-throughs
  takes that one's CTPR, without a disp of its own (`e2k_share_ctprs`):
  a ct leaves its CTPR as it was (only calls and returns empty them), so
  the twelve early exits of bzip2's mainGtU share one disp (29 disps ->
  19) instead of taking the three CTPRs in turn. After the pipeliner,
  which rewrites the disps of the loops it pipelines: decided before
  it, a branch kept a CTPR whose disp had gone with the loop, and
  CoreMark crashed. CoreMark 2,889 -> 2,891 it/s, Linpack 594.6 ->
  596.5 K (4C).
- The pipeliner takes compares whose predicates merges and predicated
  stores read (if-conversion's), in counted loops too. Such a compare is
  scheduled as any operation, and its predicate gets a name in the
  rotating ring of the while loops' exit tests (`e2k_ms_assign_pnames`;
  `abp` now also at a counted loop's end), since a store runs in the
  last stage, long after its compare; merges and a predicated store's
  condition read it under that name. A compare read both by a merge or
  store and by the exit test is still turned down, and so is a lock
  load (DAM) in such a loop: its compensation code reruns what depends
  on the load, not the compares of the predicates it reads, which the
  ring may have given to another compare by then (GMP's in-place
  mpn_bdiv_dbm1c computed wrong limbs).
- The unroll hook counts a branch around a few integer operations
  (`e2k_ifcvt_arm_p`: at most MAX_CONDITIONAL_EXECUTE, nothing FP), and
  its join, as part of the branch's block: if-conversion after reload
  puts them under a predicate, stores included, so the loop is one block
  for the pipeliner instead of unrolled four times behind a remainder
  dispatch.
- A register written under a predicate, `if (p) r = x`, keeps r when p
  is false, which a renamed instance can't: the pipeliner's analysis
  makes it `t = x` and the merge `r = p ? t : r`, t a register the loop
  doesn't use and that is dead around it. With the two entries above,
  474 -> 526 loops pipelined in xz, zstd, bzip2, zlib and CoreMark, and
  on the 4C bzip2 -9 4.53 -> 4.40 s; CoreMark, Linpack, zlib and xz the
  same (CoreMark's 1% more, measured first, came from a lock load in a
  loop with data predicates, which the first entry turns down).
- A one-block while loop whose loop end was prepared like any branch,
  its disp in the loop, pipelines: the disp goes to the start of each
  prologue, as a second block's did (the pipeliner turned down 172
  loops in xz, zstd, bzip2, zlib and CoreMark on "the loop end's CTPR";
  now 63, most of the rest have calls, and one more loop pipelines).
- Renaming for speculation (`e2k_spec_rename`) also gives a value its own
  register when the block above reads that register: the same variable
  loaded in each step of a chain of exits (bzip2's mainGtU, once its
  exits are conditional returns, below) could not go above the previous
  step's compare.
- Conditional returns (`-mcond-returns`, on; `e2k_cond_returns`): in a
  function that prepares its return at its entry, a block computing the
  result and returning (or falling into the return block) is copied into
  each block that branches to it, before the branch, which becomes `ct
  %ctpr3 ? p` (`e2k_cond_return`), as lcc's early exits are; a block
  that falls into it and branches past it does the same on the reversed
  condition. The copies run unconditionally into free registers (each
  exit its own, or the exits would wait for each other), speculatively
  (",sm": they now run where the program returned earlier; gcc.c-torture
  20180226-1 trapped), and the result goes to its register under the
  condition; copies the branch made to the result block's registers go.
  After the chain merging and tail copying, and not in the innermost
  loops of up to three blocks the pipeliner may take (zlib's
  longest_match lost its pipelining, -9 twice as slow). GCC wants a
  conditional return as a plain SET, so %ctpr3 is kept live through
  EPILOGUE_USES, and the scheduling hook adds the dependence on the
  `return %ctpr3` prepare (sched-deps gives a jump's live registers
  latency 0, and gas rejects the prepare and the ct in one instruction),
  and drops the dependence of what follows a return on a register
  written under its condition (an argument still in %r0) unless the
  later operation also writes what that one reads or writes (xz's
  lzma_stream_flags_compare returned a clobbered code). bzip2's mainGtU:
  28 conditional returns in one superblock. 4C: bzip2 -9 4.39 -> 4.28 s,
  bzip2 -d 1.34 -> 1.31 s; zlib, xz, CoreMark and Linpack the same
  (findings P27).
- What a failed check's compensation code reads stays in its register
  through the check's wide instruction, not only until it: the code runs
  after that instruction, whose writes have landed by then. A pipelined,
  vectorized loop with a lock load redid an add with an operand the
  check's own instruction had overwritten with a later iteration's value
  (gcc.dg/vect/vect-alias-check-18.c on the 4C; findings P30).
- The pipeliner recomputes the alias analysis' base terms
  (`init_alias_analysis`) before asking `may_alias_p`: they come from
  the last pass that computed them, before the copies, edge splits and
  register renaming of machine reorg (findings P31).
- A hardware loop with more than two ways in gets one block they all go
  through, which sets up `%lsr` and holds a pipelined loop's prologue
  once: a vectorized loop after its peeled, fully unrolled alignment
  prologue has eight, more than the pipeliner copies its prologue onto.
- 64-bit vectors (`e2k-vect.md`; findings P32): V8QI, V4HI, V2SI and
  V2SF in the ordinary registers, which the vectorizer uses at -O3 (and
  for SLP). Moves and logic are the 64-bit integer operations (six
  channels, 1 cycle on); padd/psub (also saturating), min/max, compares
  to masks with pmerge selects, psign abs, shifts by a scalar, pmullh
  and the high-part multiplies, pmaddh dot products, psadbw sums of
  differences and byte sums, phadd reductions, punpck widening, pshufb
  permutes, broadcasts and narrowing (selection bits 0-3 only, the v3
  rule), pfadds/pfsubs/pfmuls, pistofs/pfstoistr. Types pint (ALC0/3),
  pint14, pmul (ALC1/4, 2 cycles) and pany (ALC0/1/3/4) in the DFA and
  the channel assignment, packed results reaching integer operations and
  the other cluster at 4 (spec/isa/timing.md); the pipeliner takes them
  (bounds for the two- and four-channel classes in its MII) and lock
  loads of vector modes. Packed shifts read the whole 64-bit count, but
  `SHIFT_COUNT_TRUNCATED` lets GCC hand over a wider register (a V2SI
  holding the count twice, gcc.dg/vect/pr88903-1.c), so the expanders
  mask the count to the lane and the shifts are unspecs (findings P29).
  Vectors are passed and returned as lcc does, one slot for 8 bytes
  (findings A19). 4C, 2,000 elements in L1, ns per element against
  this back end's scalar code and lcc -O3: byte add 0.21 (scalar 1.37,
  lcc 0.14), saturating add 0.21 (14.8, 0.14), int16 max 0.38 (12.1,
  0.21), int16 multiply 0.38 (1.37, 0.22), dot product 0.39 (5.39, lcc
  1.38), sum of absolute differences 0.22 (2.71, lcc 2.04), widening
  0.38 (2.40, lcc 0.72), narrowing 0.38 (1.71, lcc 1.04), int add 0.71
  (1.37, 0.38), float multiply-add 1.98 (3.38, 1.22). lcc's plain
  loops run two vectors a cycle through array prefetch; ldd/std allow
  one. gcc.dg/vect: all 952 runnable tests pass on the 8C2; CoreMark
  and Linpack the same (CoreMark's matrix indices are unsigned 32-bit
  and fail data reference analysis).
- In a recurrence of packed operations the pipeliner charges no
  crossing between clusters: the channel assignment keeps such a chain
  in one cluster when it can, and the 4-cycle crossing set II (an int16
  sum, two paddw a vector: II 8 -> 2).
- Array prefetch in pipelined counted loops (`-mapb`, on; findings
  I23, P33; spec/isa/apb.md): a load that steps one aligned element an
  iteration, and whose elements no store of the loop writes before
  they are read, is read through a mova in the kernel (latency 5, an
  AAS channel instead of an ALU and a load channel, no memory
  dependences), up to four; the peeled prologue keeps its loads, and
  each area starts where the kernel's first mova reads. Channels and
  areas per kernel row (left half from channels 0/1, right from 2/3);
  the setup (descriptors, `ldisp %ctpr2`, `bap`) on each way in after
  `rwd %lsr`, in a block of its own; `disp %ctpr2, disp=0x0` and
  `aaurw %r, %aabf0` after the loop; the program after the function.
  Not in strip-mined loops (a new chunk restarts the count the unit
  follows after a trap) or with DAM; tried again without it when the
  pipeliner fails. It costs about 20 cycles a run, so it is used where
  it shortens the kernel (the load channels bound it) or the profile
  says the loop runs 256 times or more (`-mapb-force`, for testing,
  everywhere it can). 4C: a vectorized float multiply-add (3 loads, a
  store) II 2 -> 1, 2.6 times faster in L1, 1.6 times faster than lcc;
  forced on 4M-element arrays the vectorized kernels run 5-12 times
  faster, as fast as lcc's on plain loops; a SIGALRM every 100 us
  (63,865 of them) changed no result. Linpack, CoreMark the same (no
  loop there qualifies).
- The prologue's `setwd` shares its wide instruction (spec/abi/
  registers.md: operations there already use the new window): it takes
  CS1 and LTS0 (its fields) instead of every unit, and what follows it
  and the prologue's blockage may issue with it, but for `%b[]`, which
  the `setbn` there doesn't rotate yet. A leaf function's `return
  %ctpr3` now goes with `setwd`, as lcc's does, 1 cycle earlier (a
  one-operation function: 3 wide instructions -> 2). CoreMark +0.1%,
  Linpack the same.
- The pipeliner's memory dependences know registers the loop computes
  from an induction register (`x + inv`, `x * C`, `x << C`, the same in
  32 bits zero-extended, or under `dbl`) as stepping by a constant, if
  nothing in the body reads them before their def; and accesses through
  one incoming pointer at byte ranges that can't overlap as independent
  (the tree oracle does that only in SSA form). xz's price loop in
  `lzma_lzma_optimum_normal` (four stores to `opts[len]`, `len * 44`
  from the counter): II 16 -> 3. Array prefetch keeps to true
  induction registers (its setup reads the register before the loop).
  xz -6 about 1% faster on the 4C (within noise).
- Every ALU class reserves the literal syllables its constant takes:
  FP, combined FP, FP compares, ALC1/4 and packed operations (the
  packed ones also 2 for a 64-bit constant) took none, so the scheduler
  could put more literals in a wide instruction than its four
  syllables hold, and gas refuses that ("literals cannot be packed into
  a wide command"); the field operations below hit it in xz's
  `list.c`. The latency bypasses name the new reservations, and take
  ALC1/4 operations as consumers too.
- Reassociation builds trees 4 wide (`TARGET_SCHED_REASSOCIATION_WIDTH`:
  six integer channels at 1 cycle, four FP ones at 4; lcc's sums are
  trees too) instead of chains. GCC reassociates only wrapping integer
  types and FP under `-fassociative-math`: an unsigned sum of eight
  terms, two of them products, 7 -> 6 wide instructions; eight
  unsigned `p[i] ^ (p[i] >> 3)` summed 11 -> 8; eight doubles summed
  under `-ffast-math` 9 -> 6.
- Division costs: an integer divide 16 instructions, a remainder 21 (no
  remainder operation: a divide, a multiply and a subtract), the high
  half of a product 4. expand_divmod divides by a constant with a
  high-part multiply only if that costs less than the divide, and
  allows a remainder the divide's cost less a multiply and an add: at
  11 every `x % 10` and `x / 7` divided. 4C, ns: `a[i] % 10` summed
  37.6 -> 2.75 per element (lcc 1.39), 64-bit `a[i] / 10` 37.5 ->
  1.40 (lcc 1.39), `x = x % 10 + c` 33.5 -> 17.4 per iteration (lcc
  13.4), the digits of a 64-bit number 651 -> 325 a call (lcc 224).
  The divides there also stalled for a nop limit, fixed below.
- Unsigned 64-bit integers convert to `float` and `double` in their own
  formats (`floatunsdi<F>2`): the signed conversion when the top bit is
  clear, else that of `x >> 1 | x & 1` doubled, which rounds the same
  and sets the same flags. GCC went through the x87 long double: 27
  operations and 21 cycles a conversion, now 13 and 14. Checked on the
  4C against lcc on boundary and random values.
- `bitrevs`/`bitrevd` for bit reversal, and trailing zeros as the
  leading zeros of the bits reversed, as lcc counts them: `ctz` takes
  2 operations in series instead of 4 (`-x & x`, `lzcnt`, 63 minus).
  Type `alu0134` (ALC0/1/3/4, 1 cycle) for them in the DFA, the channel
  assignment, the pipeliner's MII and speculation.
- Byte swaps: a load or store with MAS 0x8 swaps the bytes at no cost
  (spec/isa/semantics.md, "Byte-swapped accesses"; lcc does it only
  under `-ffast`), used where the access is known aligned from the
  object or the pointer's computation (globals, arrays, locals, malloc
  results), not from the pointer's type: a misaligned one is SIGBUS
  where a plain `ldw` works, and `*(uint32_t *) (buf + 1)` is common in
  decoders (on the 4C a first version trapped there, as lcc `-ffast`
  does; now right, also for packed fields). Elsewhere `pshufb` with a
  mask, as lcc does, kept whole until after reload so that combine can
  still fold it into an access. A load or store with a MAS takes CS1,
  which `setwd` also holds (gas: "cannot encode MAS: CS1 syllable is
  busy"): reservations by a `mas` attribute.
- `__builtin_prefetch` is a speculative byte load into `%empty` with
  MAS 0x20, as lcc prefetches (spec/isa/speculation.md); it emitted
  nothing before. It never traps, and a pipelined loop's copy keeps
  its `,sm`.
- Field operations (spec/isa/semantics.md): `getfd` for zero- and
  sign-extracts of up to 63 bits (`extzv`/`extv`, bit-fields, shift
  pairs, `x & (2^n - 1)` beyond 32 bits), `getfs` for a sign-extended
  32-bit field under `dbl = 1`; `insfs`/`insfd` for `(a << k) | (c &
  (2^k - 1))` and `(a << k) | zero-extended byte/half/word`, also from
  memory (split into a load and the insert, so that the load
  schedules). The descriptor is one 16-bit literal; BYTE names the
  field's top byte, which v1-v4 take the sign from (as lcc builds it),
  and `insfd` sets bit 15 as lcc does. Eighteen field idioms (shift
  pairs, masks, bit-fields, `buf << 8 | *p`): 1 operation each where
  they took 2-4 (lcc 1-3); the byte-accumulating loops 2 cycles
  shorter. Checked on the 4C against lcc on random values.
- Bit tests: `(x & m) == 0` and `!= 0`, and the single-bit or field
  tests (`zero_extract`) GCC makes of masks, are one `cmpand` into a
  predicate (spec/isa/operations-v3.md, "Integer compares") in
  branches, store-flags and conditional moves, as lcc tests bits; an
  `and` and a compare before. Eight bit-test functions: 1 operation
  fewer each (one 2 fewer), on par with lcc or fewer. Checked on the 4C
  against lcc.
- A wait longer than 8 cycles after a wide instruction is printed in
  full: `nop 7` there (the HS field's limit) and empty wide
  instructions for the rest; the rest was dropped, so the consumer
  issued early and stalled, which costs a multiple of 4 cycles
  (spec/isa/timing.md). A loop `x = x / d + k` (a divide's consumer 8
  cycles after it instead of 11): 21 -> 16 cycles an iteration on the
  4C. Divides are the usual case; also FP divides and square roots,
  and the gap between an extended block's blocks.
- Integer divides are scheduled at 15 cycles, not 11 (findings I24:
  13 plus one per 8 bits of quotient, 13-19, on the 4C and the 8C2).
  An early use stalls to the next multiple of 4, so 11 and 15 stall
  alike (`x = x / d + k`: 16 cycles for quotients below 2^24, 20
  above, either way); at 15 other work fills the wait.
- `-mtune=elbrus-4c` and `-mtune=elbrus-8c2`, as lcc takes them
  (spec/abi/source-compat.md): the CPU's ISA version (v3, v5), which
  overrides `-march` in either order, `__elbrus_4c__` /
  `__elbrus_8c2__`, and gas `-mcpu=<cpu>`, which marks objects
  `EF_E2K_INCOMPAT` (e_flags 0x03000010 / 0x05000010, as lcc's
  `e2k-v3.4c` and `e2k-v5.8c2`). Macros and flags match lcc 1.29.16's
  `-mtune` in every order. A stub so far: the tuning is the ISA's.
- Prepares (`disp`, `return`) carry `; ipd 2` for v3, as lcc's v3
  targets write it on every prepare; its v4+ targets write none, and
  neither do we there (findings I25). No measurable change: zlib,
  bzip2, xz within 1% on the 8C2.
- Temporaries only in `%g16`-`%g31`, as lcc's code: the kernel saves
  and restores only those around a signal handler and leaves
  `%g0`-`%g15` as the handler left them (arch/e2k/kernel/signal.c;
  findings A20), so a handler built here that used `%g0` broke the code
  it interrupted (4C, a SIGALRM every 100 us: SIGSEGV in the first
  thousands; now 400 runs right under 277,731 signals). `%g24`-`%g31`,
  left out before for rotation, which the port never uses, take their
  place: 16 scratch globals, as lcc has, instead of 22. A pipelined
  loop's `%b[]` values go to a window register when no global is free
  (Linpack's main). CoreMark -0.3%, Linpack -3% (595 K -> 575 K).
- No cluster crossing charged inside any recurrence of a pipelined
  loop, integer and FP ones too (packed ones before): the channel
  assignment keeps such a chain in one cluster. adler32's sixteen
  chained adds made a 34-cycle recurrence and the loop wasn't
  pipelined; now II 16-17. CoreMark +3.1% (2,920 -> 3,010), Linpack
  the same.
- Array prefetch reads several loads through one area, as lcc reads
  adler32's 16 bytes an iteration: loads whose address steps by a whole
  number of elements (an increment register `%aaincrN`), those through
  one address sharing a descriptor; after scheduling, an area per
  descriptor, element size, stage and buffer half, within a 32-byte
  window (`mrng`), each mova at its byte offset (`ind`), the area's
  last one advancing it (`am`), the start in the program's `disp`. Up
  to 16 movas (4 a cycle). On v3 and v4 an element wider than a byte
  needs its alignment known (an area that isn't aligned gives
  diagnostic values; `MEM_ALIGN` is only the type's), so fewer loops of
  wider elements use it there until a run-time check versions them.
  Programs of failed attempts are no longer printed. adler32 over 8 MB
  on the 4C: 51 -> 16.4 cycles per 16 bytes (lcc 16.5), the inflate
  benchmark 15% faster; 400 adler32 runs right under 277,731 SIGALRMs.
- Division and remainder by a constant are priced as what
  expand_divmod emits (shifts, or a high-part multiply and shifts; a
  multiply and a subtract more for a remainder), not as a divide: loop
  trip counts such as `(len - 3) / 3 + 1` were "too costly to compute"
  for a hardware loop. zlib's `inflate_fast` gets 10 hardware loops
  instead of 8, its 3-byte copy among them, which pipelines at II 2
  (lcc's 2) with its loads through array prefetch; the inflate
  benchmark's `inflate_fast` 4% faster on the 4C.
- Where an operand would still come 1-3 cycles early once the channels
  are known (a value crossing the clusters, a load result), the wide
  instruction before it gets that many empty cycles instead: an early
  operand stalls 4 cycles (spec/isa/timing.md), an empty cycle costs 1.
  The scheduler can't see clusters: with four loads in ALC0/2/3/5, two
  ALU results land in different clusters, and an operation reading both
  the next cycle stalls whatever its channel. Only after an instruction
  that falls through, with no label between. zlib's crc32 braid loop 46
  -> 26 cycles (crc32_z on the 4C 0.54 -> 0.32 G cycles for 11 MB,
  lcc 0.18), CoreMark +3.4% (3,002 -> 3,105), Linpack +1.2%.
- A symbol in an address costs what it takes, a 64-bit literal (two of
  a wide instruction's four literal syllables): a memory reference with
  one costs an instruction more, and `TARGET_ADDRESS_COST` 2. CSE and
  invariant motion then keep a loop's table base in a register, as lcc
  does, and late combine no longer puts it back into every load. zlib's
  crc32 braid (20 table loads an iteration, two a cycle with their
  literals): 31 -> 26 cycles; gunzip on the 4C 2% faster, crc32_z 13%.
- A loop block that exits by a conditional jump and falls into a block
  that only jumps back (with at most four register copies, dead at the
  exit) loops on itself instead: the jump inverted to its own head, the
  other block's copies moved before it, that block going to the exit.
  Block reordering leaves zlib's do-while copy that way, and its
  unsigned count could wrap, so it is no hardware loop; as a one-block
  while loop it pipelines (II 3 for 3 bytes, against 9-10 cycles).
  gunzip on the 4C 4% faster, inflate_fast 5%.
- No data speculation (DAM) for the loads of a loop copy that the
  aliasing versioning runs when the arrays may overlap: there they
  mostly do, and every failed check costs its compensation code. That
  copy's references get a dependence clique of their own (one base for
  all, which tells the alias oracle nothing), which the EBB scheduler's
  `TARGET_SCHED_SPECULATE_INSN` and the pipeliner's DAM test. zlib's
  inflate_fast copies of distance 1 or 2: 46 -> about 10 cycles per 3
  bytes; gunzip on the 4C 9% faster (2.53 -> 2.30 G cycles, lcc 1.78).
- In a loop copy for overlapping arrays, a load that may read what a
  store just wrote waits a cycle after it, as a load of the same
  doubleword already did: one issued in the very next wide instruction
  gets its value about 8 cycles late (spec/isa/timing.md, "Store to
  load"), and there they mostly alias. zlib's copies of distance 1:
  40 -> 24 cycles per 3 bytes; gunzip on the 4C 6% faster (2.30 ->
  2.17 G cycles, lcc 1.78).
- `setbn`/`setbp` take a wide instruction of their own also where the
  scheduler gave no clocks: one pipelined loop's way out followed by the
  next one's way in put two of each in one wide instruction, which gas
  rejects (7-Zip's `7zUpdate.cpp`).
- Up to 10 operations of a branch arm go under its predicate (was 6):
  an arm's stores often come with as many operations computing their
  values, as in 7-Zip's GetOptimum update of `opt[len]` (3 stores, 8
  operations). LZMA encode and decode 2.6% faster on the 4C, gunzip
  1.3%; CoreMark and Linpack the same.
- sched-deps again drops the output dependence between two writes of
  one register under opposite predicates (reverts the v0.3 change):
  lcc puts such pairs in one wide instruction all the time (662 in
  7-Zip's LZMA code alone, e.g. `addd,3 ... %dr0 ? ~%pred0` with
  `addd,4 ... %dr0 ? %pred0`), so the hardware takes them. Kept, the
  dependence cost a load's latency between the two arms of an if-else
  that register allocation gave one register, and the arms ran one
  after the other: GetOptimum's price block 32 -> 24 cycles (isa-score;
  lcc's measures 18), the LZMA benchmark on the 8C2 3.3% faster (12.52 -> 12.11 s, lcc 9.69);
  CoreMark and Linpack the same.
- The channel assignment's stall estimate (e2k_chan_bundle, which puts
  empty cycles before an operand that would come early) knows
  predicates: a consumer under the predicate opposite to its register's
  last producer reads the producer before that one, and an unpredicated
  consumer waits for both. With the arms of an if-else in one register
  (previous entry), arm B's load into it made arm A's read look early:
  3 empty cycles before GetOptimum's price loads once the next change
  had shortened their addresses (LZMA benchmark on the 8C2 12.06 ->
  11.93 s with that change). Alone: LZMA 12.10 -> 12.09 s, 7-Zip's
  benchmark decompression 1599 -> 1604 (compression 1640 the same).
  With the previous entry, 7-Zip's benchmark on the 8C2 went from 1627
  to 1640 compressing and 1575 to 1604 decompressing.
- New pass e2k_addr_height after combine: an address computed as a
  chain (expand builds p->a[x][y] as ((x << 7) + y + C) << 2 + p, each
  operation after the one before) is rebuilt from its terms, the ones
  ready first added first and the last one ready left for the access to
  add; the terms set nowhere in the loop are summed with the constant
  once, on the loop's entry edge (left in the loop, such a sum cost the
  modulo scheduler a rotating register over a whole iteration: bzip2's
  generateMTFValues stopped pipelining, bzip2 -9 3% slower). Ready times
  follow the definitions within the loop with rough latencies (loads 3,
  multiplications 4; a register set more than once, or outside the
  loop, is ready at the start). GetOptimum's price loads: 9 -> 5 cycles
  after the length clamp. Most rebuilt addresses also take an operation
  fewer in the loop. On the 8C2: LZMA benchmark 1.4% faster (12.09 ->
  11.92 s), 7-Zip's benchmark compression 1636 -> 1668 (decompression
  1604 -> 1607), xz -6 0.5%; zlib, bzip2, CoreMark and Linpack the
  same. -mno-addr-height turns it off.
- Field inserts (insfs, insfd) are predicable. A range decoder's refill,
  LZMA's `if (range < kTopValue) { range <<= 8; code = (code << 8) |
  *buf++; }`, was one operation short of going under its predicate, so
  every decoded bit took a branch (LzmaDec_DecodeReal: 228 -> 135
  blocks). On the 8C2: 7-Zip's benchmark decompression 8.2% faster
  (1607 -> 1738), xz -d 7% (0.150 -> 0.140 s), LZMA benchmark 1.6%
  (11.92 -> 11.73 s); compression, zlib, bzip2, CoreMark and Linpack
  the same.
- Channel assignment knows write-back conflicts (spec/isa/timing.md): an
  FP-side result (FP operation, integer multiply) bound for the integer
  side comes a cycle late, a whole stall step for a consumer placed at
  its latency, when an ALU operation or a load issues in its channel 2
  cycles after it. Such a channel costs half a stall step in the search,
  and a conflict it can't avoid makes the result a cycle late for the
  stall estimate (and the padding). LZMA's bit decoding put the refill's
  insfs in the channel of the muls computing the bound 2 cycles before,
  and the compare on the bound stalled 4 cycles. On the 8C2: 7-Zip's
  benchmark 1.8% faster both ways (compression 1656 -> 1686,
  decompression 1738 -> 1770), LZMA benchmark 0.9% (11.73 -> 11.62 s),
  xz -6 0.3%; CoreMark and Linpack the same.
- The branches e2k_modsched makes on the ways out of the loops it
  pipelines get prepared too (e2k_prepare_branches again after it, but
  not in its own clocked blocks): they were left as ibranches, 6 cycles
  each taken, and a pipelined while loop's exit is taken whenever the
  loop ends (LZMA's match finder Skip: 21 million taken ibranches in the
  benchmark, all of LzFind.c's 27 now cts). On the 8C2: LZMA benchmark
  0.35% faster (11.63 -> 11.59 s), zlib -9 0.6%, xz -6 0.4%.
- Loads that if-conversion put under a predicate run without it, as
  ld,sm, when in their block only operations under the same predicate
  read the result (up to a write of the register without a predicate or
  under the opposite one, or the block's end with it dead) and nothing
  changes the predicate meanwhile (e2k_unpredicate_loads, before the
  modulo scheduler): they no longer wait for the compare (LZMA's refill
  `code = (code << 8) | *buf++`, zlib's `hold += *in++ << bits`). When
  the load's register is used earlier in the block, it takes a free one
  (used in the function, dead after the load, untouched up to its last
  read), unless a write under the opposite predicate ends the range:
  regrename ran while the load was predicated, which counts as reading
  the old value, so the scheduler couldn't move it up. On the 8C2:
  7-Zip's benchmark decompression 1.9% faster (1770 -> 1804), LZMA
  benchmark 0.15%; the rest the same. -mno-unpredicate-loads turns it
  off, -munpred-limit=N stops after N loads (for bisecting).
- A compare is 3 cycles from a ct on its predicate, an FP compare 5
  (spec/isa/control-transfer.md, "Costs"); the DFA gave the compare's
  own 2 and 4, so a ct placed there waited a cycle the scheduler didn't
  see. On the 8C2: LZMA benchmark 0.8% faster (11.57 -> 11.48 s), bzip2
  -d 2.8%, bzip2 -9 1.1%, 7-Zip's benchmark compression 0.9%; gunzip
  the same.
- v4 and later run FP add, subtract, multiply and the combined
  operations in ALC2 and ALC5 too, six a cycle (timing.md,
  "Elbrus-8C2"): with -march or -mtune v4+ the DFA (`e2k_fp6`,
  `e2k_fma6`) and the channel assignment use all six channels for them;
  other FP operations stay in ALC0, 1, 3 and 4, and so do fcmpud*f and
  fcmpod*f, now typed as FP compares (they were FP operations). The
  v5-tuned suite passes on the 8C2 (torture -O2 and -O3, 1639 each;
  gcc.dg/vect -O3, 952; the real programs and their tests). No
  measurable gain: Linpack's daxpy put 5 FP operations in ALC2/5 and
  runs the same, and so does CoreMark.
- Channels for loops in their steady state: every pipelined kernel,
  and every other loop of one block, gets its channels in two rounds,
  the second with the producers the first left in the table (a
  kernel's ring rotated by abn's two registers), so that a value one
  iteration passes to the next lands in a channel of its consumer's
  cluster. The table was empty at the loop's top, and xz's crc64 loop
  stalled 4 cycles an iteration on a value crossing the clusters back
  to its first instruction. On the 8C2: xz -d 5% faster (0.137 ->
  0.130 s), 7-Zip's benchmark compression 0.9% (1692 -> 1708); zlib,
  bzip2, xz -6, the LZMA benchmark and gunzip the same.
- Insns the scheduler makes as it goes (the checks of lock loads) get
  their cycle recorded too: only UIDs below the count at the start of
  scheduling had one, and the bundler counted a check without a clock
  as an empty cycle, so every check but the first in a function had a
  nop after it.
- A check load waits for nothing of its lock load, and a use of its
  register right after it doesn't wait for it either (relcc2 findings
  I30, probed on the 4C and the 8C2): the scheduler puts a check 2
  cycles after its lock (its users 1 cycle after the check, so at the
  lock's latency), and the bundler no longer counts a check as reading
  its register or producing a new value (it padded a cycle after each
  check, a cluster crossing from the lock in ALC0 to the check in ALC5).
- A select of two loads stays two loads: GCC 17's phiopt turns
  `c ? *a : *b` into a load from a selected address
  (`factor_out_conditional_load`), which then waits for the compare;
  a new param, `phiopt-factor-loads`, turns that off, and the back end
  sets it to 0 (a speculative ld,sm never faults, so the factoring only
  lengthens the critical path). The two loads then come out predicated
  into one register; the next two entries run them early.
- If-conversion's choice between two loads, `r = p ? *a : *b` (7-Zip's
  and xz's binary-tree match finders: the next tree node), runs both
  loads unpredicated, as ld,sm, into free registers, and a merge after
  the second picks one (e2k_unpred_pairs, in e2k_unpredicate_loads):
  the operations under p between them read the first one's register,
  and r keeps its old value until the merge for what runs under not p.
  On its own this gains little: the loads still wait behind the stores
  under p and not p that the tree walk does before them (next entry).
- The DAM moves the loads of such a select above stores, with each
  check under the load's old predicate: a check under a false predicate
  does nothing, not even fault on an unreadable address, and with `,sm`
  it would be a plain speculative load, no check (relcc2 findings I29,
  probed on the 4C and the 8C2). e2k_unpredicate_loads records each
  load's condition (e2k_unpred_cond); e2k_speculate_insn accepts those
  loads; e2k_gen_spec_check puts the check under the condition (checks
  are predicable now); the dependence hook gives such a load speculative
  dependences on its predicate's setter and the jumps before it, which
  the check inherits and the lock load drops, and none on stores under
  the opposite predicate (when the predicate holds they don't run, and
  when it doesn't the value isn't used). The modulo scheduler's own DAM
  leaves these loads alone (its check would be unconditional).
  -munpred-dam=N: 0 none, 1 the select pairs (the default), 2 also the
  single loads e2k_unpredicate_loads runs early; 2 lifted LZMA's decoder
  refills above the probability stores and made 7-Zip's benchmark
  decompression 5.7% slower (1879 -> 1777): a lock load keeps stores out
  of its wide instruction. With the two entries before, on the 8C2
  against the channel entry above: xz -6 5.8% faster (7.91 -> 7.47 s),
  LZMA benchmark 1.5% (11.48 -> 11.31 s), 7-Zip's benchmark compression
  1.7% (1689 -> 1717) and decompression 4.0% (1806 -> 1879); zlib,
  bzip2 and gunzip the same. The tree walk's next node now comes 3
  cycles sooner a step (two lock loads with the compare, both checks
  after the stores, the merge 4 cycles after the second lock).
- Windows around pipelined loops as lcc's (-mring-setwd, on): in a
  function that calls, the window covers the registers and the 4
  outgoing pairs, and a loop's setbn grows it by the loop's ring, above
  the outgoing pairs (they can hold a value across the loop: zlib's
  inflate kept one there), and its exit shrinks it again. Before, the
  largest ring stayed below the outgoing pairs, so every call left it
  under the callee, and xz's encoder -> optimum parser -> match finder
  chain (48, 55, 28 and 55 pairs) overflowed the 112-pair register file:
  a spill and fill each call, 0.5% of xz -6's cycles in
  BUB_B_RF_SPILLFILL (60 M; lcc's chain of 20, 27, 17, 22 pairs never
  spills). Now none, but a window grow and shrink costs about 3 cycles
  (relcc2 findings I31), so the run time is the same; leaves keep the
  old layout. Stack spills (from sched1) were also looked at: they are
  cold (-fsched-pressure removes 70% of them and changes no time, and
  without sched1 zlib -9 is 35% slower), and a getsp in the setwd
  instruction costs nothing.
- The alias check of a loop versioned for overlapping arrays
  (e2k_av_loop) needs no divide: for a count X / K (zlib's
  inflate_fast copies, `len -= 3` loops: (len - 3) / 3) with K dividing
  the step, a segment of (STEP / K) * X covers every access and is at
  most a step too long (e2k_av_undivided); and the pruning of the checks
  is repeated until it merges nothing more, which makes zlib's three
  checks of out[k] against from[0..2] one. The direct copy's check went
  from a 20-cycle chain (umulx 0xaaaaaaab, shifts, three compares,
  merges, landp) to about 7 cycles; copies with 3 * (len / 3) <= dist <
  len now take the original loop (0.06% of gunzip's copies). From the
  v3 research report (item 6); a test of both loop shapes over lengths
  0-300 and distances in both directions matches a byte-by-byte copy in
  all 48,489 cases. On the 8C2: gunzip 5.0% faster (1.337 -> 1.270 s),
  zlib -d about 5%; the rest the same.
- Renaming for speculation (e2k_spec_rename) looks at the whole
  extended block, not only the block above: along a chain of blocks
  falling through into each other it keeps, for each register, the last
  block in its way (that mentions it, a call in it clobbers, or a jump
  needs it on the other path: e2k_chain_stamp), and a value of the next
  block conflicts if its register is in the way anywhere above. It takes
  the free register least recently used along the chain (globals first,
  not one a later block keeps across its end), window registers below
  the window's top included; a rename above the block before needs no
  copy back, and one with a copy back is done only for a value that
  block reads or needs after it. Debug binds of the renamed registers
  are reset. bzip2's mainGtU walked two blocks behind: each step's bytes
  went back into the registers of the step two up and waited for its
  compares. From the v3 research report (item 4). On the 8C2: bzip2 -9
  3.1% faster (1.973 -> 1.913 s); the rest the same.
- A branch's disp goes above the barriers before it in its block when
  nothing there touches its CTPR (e2k_lift_prepares, after
  e2k_share_ctprs): on a pipelined loop's way out, the copies out of the
  ring and setbn_leave came first, and the scheduler can't move the disp
  above setbn_leave, so the ct waited for its prepare (LZMA's match
  finder, 21 such exits in LzFind.c). A barrier's true dependence on a
  disp that it doesn't read costs nothing now (a loop's AAU setup waited
  5 cycles behind one too). Only a predicate test or an unconditional
  ct counts as a branch here, not a loop-mode back edge. From the v3
  research report (item 3, first step). On the 8C2: LZMA benchmark 0.5%
  faster (11.30 -> 11.24 s), 7-Zip's benchmark compression 0.6%, bzip2
  -9 0.7%; the rest the same.
- Where the modulo scheduler's order (by start within an iteration)
  finds no schedule at an II, it tries again at that II ordered by the
  earliest start at II over every dependence, carried ones included (a
  longest path weighing each LAT - II * DIST; none at all when a
  recurrence is longer than II), and starts no node before it
  (-mms-est, on). The body's order put a node that only reads the last
  iteration's value of a recurrence at the top, which left the
  recurrence's last node too little room at every II: xz's crc64 loop
  (the shift of the carried CRC) never pipelined, and now runs at II 9,
  its recurrence. Not in a first attempt a lock load may still improve
  (the DAM retry), and a schedule found this way whose ring or prologue
  doesn't fit goes on to the next II instead of giving up. From the v3
  research report (item 5; the simpler order its review proposed rather
  than the full swing modulo scheduling order). On the 8C2: zlib -9
  7.3% faster (1.033 -> 0.963 s), xz -d 5.7% (0.130 -> 0.123 s), 7-Zip's
  benchmark compression 1%; the rest the same.
- The integer operations of if-converted arms run before the compare
  when only operations under their predicate read the result
  (e2k_unpred_arms, in e2k_unpredicate_loads after the loads,
  -munpredicate-arms): each goes up to just before the setter of its
  predicate (not across a call, a barrier, a jump, or an insn that may
  run where it runs and changes an operand of it; the other arm's insns
  never ran there), as ",sm", into its own register when nothing where
  the predicate is false needs the old one, else into a free register
  (least recently used) that its uses then read, with a copy back under
  the predicate where something else may read the value. The last
  operations of each arm stay predicated and select the result. A write
  of the register under a third predicate ends the value. LZMA's bit
  decoding (range, code and the probability updated under opposite
  predicates): 177 operations in LzmaDec.c, 15.9 -> 15.1 cycles a bit
  statically, DAM checks 31 -> 14. An operation under a false predicate
  ignores a diagnostic operand (relcc2 findings I33, probed). From the v3
  research report (item 8). On the 8C2: xz -d 5.1% faster (0.123 ->
  0.117 s), zlib -9 3.5%, LZMA benchmark 1.8% (11.24 -> 11.03 s), 7-Zip's
  benchmark decompression 1.8% (1882 -> 1916), gunzip 1.3%; compression
  the same.
- -pthread defines _REENTRANT, as lcc's does and as GCC's other glibc
  targets do (linux.h CPP_SPEC). xz's configure rejected -pthread
  without it and built the PoC's xz with no thread flags, lcc's with
  -pthread (relcc2 findings P39).
- Array prefetch also for an array the loop stores to, wherever no
  later mova can read what a store wrote (the store of an iteration
  against the movas D iterations on, and in its own iteration a store
  that comes first), not only a store behind the load or at its
  element: Linpack's daxpy, unrolled by 4, loads dy at +8 and stores at
  +16. And for the setup and the end of the program a temporary the
  loop itself uses, when none is free: the setup runs where the loop
  starts and the end where it has ended, so a register dead at both
  will do (Linpack's main has all 64 window registers in use). On the
  8C2 with -mtune=elbrus-8c2: Linpack's main daxpy kernel II 4 -> 3 (dy
  through movas too), Linpack 4.2% faster (1,054-1,059 -> 1,100-1,102 K
  KFLOPS). Generic v3 code is unchanged (APB there needs known
  alignment).
- The modulo scheduler's third try at an II, after the body's order
  and the earliest starts: each node in the cycle of its window whose
  row has the fewest ALU operations so far, not the first that fits
  (Linpack's unrolled daxpy with fmul_add had its four multiply-adds
  ready in one cycle, and the row that took them all kept room for one
  store of the two the II needed). On the 8C2 CoreMark 2.5% faster
  (6,391 -> 6,553 it/s, generic v3 and v5 code alike); Linpack
  unchanged.
- Stores of a pipelined loop read their address register's instance
  from a later iteration, the latest whose step they may, with the
  offset that many steps lower, when the ring is too big otherwise: a
  store runs in the last stage, so the address register lived through
  every stage, a ring name for each cycle in II. Linpack's unrolled
  daxpy with -mfmul-add on v5: eleven names fewer, II 3 -> 2. Only
  where needed: in the generic v3 daxpy, whose ring fits anyway, the
  same addresses at the same times ran 28% slower on the 8C2 (4.8 ->
  6.1 cycles an iteration, cause unknown). No default build changes.
- A load into the addend of a combined FP operation (fmul_add,
  fmul_sub, fmul_rsub) gets 4 cycles more latency: a separate fmuld +
  faddd gives the addend's load the add's slack, which a load that
  misses L1 needs. -mfmul-add (still off by default), on the 8C2: a
  pipelined daxpy over L2-sized arrays 1.19 -> 1.11 cycles an element
  (1.06 without fmul_add); Linpack with -mtune=elbrus-8c2 1,066 ->
  1,103-1,106 K KFLOPS, now above the 1,098 K without fmul_add.
- The array prefetch setup right after rwd %lsr when the prologue of a
  pipelined loop goes in the same block (not clocked), as long as
  nothing after rwd uses %ctpr2: it went on the edge after the
  prologue, so bap came right before the kernel and the first movas
  waited out its 22 cycles; now the prologue covers them. On the 8C2
  with -mtune=elbrus-8c2 Linpack 7% faster (1,099-1,102 -> 1,174-1,180
  K KFLOPS), now ahead of the same build without array prefetch
  (1,159-1,161 K) and of generic v3 code (1,150-1,160 K); with
  -mfmul-add 1,105 -> 1,161-1,163 K. Generic v3 Linpack unchanged.
- What the scheduler put in a conditional jump's cycle from the block
  the jump falls through to, in its extended block, now shares the
  jump's wide instruction, as e2k_adjust_cost and e2k_spec_mark already
  assumed (it runs when the jump is taken too, so only what may run
  there goes in); the bundler used to start a new instruction after
  every jump, one cycle more each time. Not for pipelined kernels, nor
  a prepare of the CTPR the jump reads (gas refuses that before v6).
  bzlib.c 3,801 -> 3,750 wide instructions. On the 8C2 (generic v3,
  same session): bzip2 -9 3.0% faster (1.893 -> 1.837 s), zlib -9 1.1%,
  bzip2 -d 1.2% (2 ticks), CoreMark 0.9% (6,553 -> 6,611 it/s), 7-Zip
  decompression 0.5%; xz -6, the LZMA and gunzip benchmarks, 7-Zip
  compression and Linpack within 0.3%.
- -mno-spec-fp, lcc's -fno-spec-fp: no FP operation runs speculatively.
  By default (-mspec-fp, as lcc's default) a pipelined loop runs every
  operation but its stores for iterations past the end too, as ",sm",
  FP ones included, so a program that clears the FP flags
  (feclearexcept) and then runs such a loop gets SIGILL at the first
  non-speculative use of an inexact result, as with lcc
  (spec/isa/speculation.md, "What lcc speculates"). With -mno-spec-fp
  loops with FP operations aren't pipelined and FP operations aren't
  copied unpredicated into conditional returns. relcc2's specfp.c on
  the 4C with the PoC's kernels: SIGILL by default, the right result
  and FE_INEXACT set with -mno-spec-fp, as lcc's two builds.
- ",sm" only where it is needed (e2k_spec_prune, -mspec-prune): the
  passes that run an operation ahead of its guard flagged it whatever
  it read, but an integer operation traps only on a diagnostic operand.
  A forward pass over the CFG tracks which registers may hold a
  diagnostic value (made by a speculative load, FP operation or
  division, or by anything reading one) and drops the flag from integer
  operations that read none. Loads, FP operations, divisions, DAM
  operations, pipelined kernels and the rotating registers keep it.
  bzlib.c 1,541 -> 1,188 ",sm" operations; no change in speed (a ",sm"
  operation that succeeds costs nothing). Guarded loads through NULL
  and an unmapped page feeding integer chains run right on the 4C.
- An unconditional ct is scheduled the whole 5 cycles after its disp,
  as it always waits that long; only a conditional one keeps the
  2-cycle cap (-muncond-ct-cost). On the 8C2 (generic v3): LZMA
  benchmark 0.2% faster (11.040 -> 11.017 s), CoreMark 0.2% (6,608 ->
  6,621 it/s); zlib and bzip2 unchanged.
- Conditional latches (e2k_cond_latches, -mcond-latches; the v3
  hyperblock plan's step 2): a block B whose branch goes to a block J
  that only jumps to X, X dominating B, does J's operations before its
  branch and branches to X itself. Stores go under B's condition (and
  none storing what a copied load gave); a register dead on B's other
  way is written as it is (",sm"), one live there under the condition
  when it is J's last write and X needs it, else into a free register
  copied back under the condition. bzip2's unRLE: the eq_one block
  (store the byte, update the CRC, back to the loop's top) goes into
  the avail test, one block and one taken jump fewer each step. On the
  8C2 (generic v3): bzip2 -d 5.4% faster (0.583 -> 0.553 s), xz -6 1.0%
  (7.440 -> 7.363 s), LZMA benchmark 0.3%; the rest within noise.
- Loop invariants the middle end left in a loop, moved onto its ways
  in after register allocation (e2k_hoist_invariants, -mhoist-inv): a
  single set that can't trap and reads no memory, whose sources the loop
  doesn't write, whose register nothing else in the loop sets and
  neither the loop's top nor its exits read before. Into a hardware
  loop's preheader before its rwd %lsr, which the pipeliner looks for
  right before the loop (on the edge it kept 4 of CoreMark's matrix
  loops from being pipelined, CoreMark 22% slower). bzlib.c: 9
  invariants; unRLE's `bs * 100000`, the plan's target, stays, as its
  register is live into the loop's top. On the 8C2 (generic v3):
  Linpack 1.5% faster (1,147-1,161 -> 1,174-1,180 K); the rest within
  noise.
- A branch at the end of a short extended block whose disp could only
  go to the block's top, too close to its ct (taken: the ct waits for
  the disp's 5 cycles), is prepared instead in each predecessor of the
  extended block, after the predecessor's last use of the CTPR, when
  that CTPR (or another one dead after the branch) holds nothing else
  from there to the branch (e2k_hoist_prepares, -mhoist-prepares; the v3
  research report's P2, the design reviewed in the PoC's scratch/wf).
  Only for a ct taken at least a quarter of the time, at most 4 copies,
  none into a predecessor twice as hot, past a call that ends its block,
  or into %ctpr3 in leaf functions that keep it for their returns;
  df is recomputed after every move. LzFind.c's late cts 105 -> 84,
  LzmaEnc.c 191 -> 146. On the 8C2 (generic v3): 7-Zip's benchmark
  compression 1.9% faster (1,745 -> 1,779), bzip2 -9 1.5% (1.837 ->
  1.810 s), LZMA benchmark 0.5%, CoreMark 0.5% (6,620 -> 6,652 it/s),
  xz -6 0.2%; the rest unchanged.
- Fixed (xz -6 crashed once the tail duplication of joins, next, put
  a match finder's loop latch in the extended block before it): a
  predicated load that e2k_unpredicate_loads runs as a lock load (its
  check under the predicate) got a speculative dependence on every jump
  before it in its extended block (e2k_unpred_cond_deps), which
  replaced the one on a jump to where the load's register is live, and
  e2k_adjust_cost gave it cost 0. The lock load then issued in that
  jump's wide instruction and clobbered the register on the taken way
  (bt_find_func: `cur_match = pair[1]` in the register of `delta`,
  which the match path reads for `matches->dist`). Such a jump keeps
  its dependence now, with cost 1. Torture on the 4C passes; timings
  unchanged.
- Small joins copied for the jumps into them (e2k_tail_dup_joins,
  -mtail-dup-joins): a block J of at most 16 plain operations that a
  conditional branch falls into and 1-3 jumps also enter, ending in a
  branch, a jump or a fall-through, gets a copy for each jump at the end
  of the function, so its label goes and sched-ebb carries the branch's
  extended block on through J (the 3 cycles a ct waits for its compare
  get J's loads and compares; xz's tree-walk latch in bt_find_func).
  Only when the fall-through is the hotter way in; when a copy has to
  jump on to J's successor K, only when the fall-through is 4 times
  hotter than the ways that take that jump (bzip2's unRLE, a chain of
  such joins, ran 20% slower without the rule). The jump after a copy
  may get K copied too when K's label is one the copy made (CoreMark's
  state machine: the hot chain stays one extended block), not when K
  was a join already (xz's bt4_skip, whose walk goes either way: xz -6
  1.2% slower with those). At most 64 copied operations a function; not
  in innermost loops of up to three blocks. Tried and dropped: never
  copying for a copy's jump (CoreMark 0.5% slower than without the
  pass), and no copy that gives K a new label (CoreMark gains only 1%).
  On the 8C2 (generic v3): CoreMark 3.0% faster (6,653 -> 6,849 it/s;
  4C 3,316 -> 3,414), xz -6 2.6% (7.36 -> 7.17 s), LZMA benchmark 2.5%
  (10.95 -> 10.67 s); 7-Zip, bzip2, zlib and Linpack unchanged.
- Fixed (gcc.dg/vect/vect-div-bitmask-5.c failed to compile about half
  the time, "in e2k_ms_schedule"): the pipeliner sized its rows of DFA
  states by dfa_state_size, which only haifa's sched_init sets, so in
  the first function of a file that sched2 skips (that test's fun1,
  built with optimize ("O1")) the rows were empty and the states
  whatever the stack held. e2k_modsched sets it now. It had shown up
  only once another change moved what the stack held.
- A loop header's leading operations moved into the latches, before
  their jump, and onto the ways in (e2k_rotate_headers,
  -mrotate-headers). GCC's loop header copying leaves a loop's exit test
  at the bottom, so xz's tree walk (bt4_skip, 66% of xz -6) ran merge ->
  delta -> compare -> landp -> ct in each latch, and only after the
  transfer did the header compute the next pair's address from delta;
  lcc keeps the test at the top, beside that work. In a latch the moved
  operations run beside the test, speculatively (",sm"; their registers
  dead where the latch leaves the loop). Those that nothing before them
  in the header waits for: operations with a speculative form and
  predicated integer ones (lcc's "adds,sm ... ? %pred"), no FP operation
  under -mno-spec-fp, and no load, which in a latch also runs on the
  way out for a node the walk never visits (with the loads, 7-Zip's
  GetMatches took 5% more cycles and xz -6 was 1% slower). Only what
  fits (e2k_rotate_fit, a latency count of the latch): each issues no
  later than a cycle after the latch's jump would and has its result
  within 3 cycles of it, and only into latches whose jump waits until
  cycle 6 or later (bzip2's mainQSort3 swap arm, ready at 3: bzip2 -9
  2% slower). Not the pipeliner's loops: innermost of up to three
  blocks, and the two-block while loops e2k_ms_wloop may take (zlib -9
  was 52% slower without longest_match's II 5); nor a latch that heads
  an inner loop (zlib's detect_data_type lost its II 1 loop). The walk:
  22 -> 19 cycles a step. On the 8C2 (generic v3): xz -6 4.8% faster
  (7.18 -> 6.84 s; lcc 6.27), LZMA benchmark 2.3% (10.68 -> 10.44 s);
  7-Zip, zlib, bzip2, CoreMark and Linpack unchanged.
- Tried and shelved (patch in the PoC's scratch/stream-unroll.patch):
  Linpack's daxpy unrolled once for two elements a cycle on v5, as lcc
  does. It needed the pipeliner to follow an induction variable that
  register allocation split in two after unrolling ("r45 = g16 + 8 ...
  g16 = r45 + 8", a two-cycle recurrence; rewritten as g16 = g16 + 16,
  the other register a copy at an offset, for the dependence test and
  array prefetch), -mfmul-add (four multiplies and four adds leave no
  ALU channel), array prefetch for all four loads, and rebasing both
  stores through a register holding INV - OFF (their addresses are
  INV + X, so the offset can't go in the literal; without it the ring
  needs 78 names at II 1, 62 fit). The kernel then ran at II 1, 1.3
  cycles a measured pair on the 8C2, and the program's loop kernels
  took 10.0G cycles against 14.5G (lcc's 13.5G), but each of 81M daxpy
  calls (66 elements on average) paid about 107 cycles in its way in
  (array prefetch's setup and bap's wait, a 19-stage prologue): 22.7G
  cycles outside the kernels against 17.6G (lcc's 14.0G), and Linpack
  went from 1.20M to 1.14M KFLOPS (lcc 1.47M). Without -mfmul-add the
  unrolled loop stays at II 2, 1.16M. What would make it pay: cheaper
  ways into pipelined loops, which already cost more than lcc's, or
  a version for short trips.
- -mtune=elbrus-2c3, elbrus-16c and elbrus-12c (lcc's CPU codes 11, 10,
  9): ISA version 6, __elbrus_2c3__ (and the others), gas -mcpu (objects
  flagged 0x17000010 for the 2C3, as lcc's). And -mlatency=v3|v6, the
  timing generation (E2K_LAT6), apart from the ISA version: v1-v5 share
  v3's latencies, v6 changed them (spec/isa/timing.md, "Elbrus-2C3
  (v6)"), v7 takes v6's; the default follows the ISA version. The ISA
  version stays what decides encodings, channels and the APB and loop
  rules, which every CPU that runs the code must obey; the latencies
  only cost time when wrong. No timing change yet.
- v6 latencies, first: an L1 load takes 5 cycles in every channel, to
  every consumer in either cluster (spec/isa/timing.md, "Elbrus-2C3
  (v6)"). Copies of the load and lock-load reservations at 5 under
  E2K_LAT6 (e2k6_*, every bypass that names loads names them too; the
  load -> fmul_add addend bypass 9, 5 plus the add's slack), no
  crossing cost for a load's result in the channel model and the
  pipeliner, and 5 in e2k_ah_latency. On the 2C3 (-mtune=elbrus-2c3,
  core 0): CoreMark 6,112 -> 7,250 it/s (lcc's 2C3 build 5,264, its
  generic v3 4,415), Linpack 1.08M -> 1.50M KFLOPS (lcc 1.99M and
  1.44M), xz -6 7.50 -> 6.27 s. Torture at -O2 and -O3 and xz's
  levels pass there; generic v3 and 8C2 code unchanged.
- v6 latencies, second: on the 2C3 an integer compare or predicate logic
  reaches a predicated operation or a merge in 1 cycle (2 before; to a
  ct still 3), also in the wide instruction of a taken return, where v3
  and v5 read the old predicate one instruction after the writer (I17,
  which the latency of 2 kept away; relcc2 findings I38: landp has the
  same hazard there, and the 2C3 removed both). E2K_PRED1, only with
  -mtune=elbrus-2c3, since the 12C and 16C are not measured:
  -mlatency=v6 alone keeps 2. Copies of the compare reservations at 1
  (e2k6_cmp*, in every bypass that names compares), a predicate-logic
  bypass of 1 guarded by e2k_pred1_p, and no empty wide instruction
  before a jumped-to block that transfers and reads a predicate. On the
  2C3 (core 0, best of 3): zlib -9 0.834 -> 0.830 s, gunzip 0.054 ->
  0.053, bzip2 -9 1.701 -> 1.678, bunzip2 0.557 -> 0.554, xz -6 6.290 ->
  6.247, unxz 0.088 -> 0.086 (lcc's 2C3 build 0.838, 0.045, 1.696,
  0.542, 5.431, 0.069); CoreMark and Linpack unchanged (7,250 it/s,
  1.50M KFLOPS). Torture at -O2 and -O3 and the test suites of zlib,
  bzip2, xz, pcre2 and expat (where I17 first showed) pass there;
  generic v3 and 8C2 code unchanged.
- The nops inside the atomics (relcc2 findings A21): lcc's v3 counts
  after the lock-wait load (fetch-op nop 4, exchange nop 1,
  compare-exchange nop 2 and 1, against nop 2 in all three before),
  which a probe of each spacing (eight uncontended atomics a loop, each
  on its own line) found the cheapest on the 4C and the 8C2, 17.3
  cycles an atomic: nop 2 cost 19.3 in a fetch-add, 18.4 in an
  exchange. On the 2C3 every cheapest spacing is one cycle longer, 21.8
  cycles, so v6 timing (E2K_LAT6) adds one (lcc's own v6 build keeps
  v3's counts but for nop 7 and 0 in the compare-exchange, about 3
  cycles over the best on all three there). The threaded atomics test
  mixed with lcc's code passes on the 4C, the 8C2 and the 2C3 (8
  threads, each machine's tuning).
- The divider takes a divide every 2 cycles, except sdivd and udivd on
  v3 and v4, which want 3 (spec/isa/timing.md, "Divider"; the 8C2 and
  the 2C3 take sdivd every 2): every integer divide reserved it for 3
  before. Four independent divides now issue 2 apart (32-bit ones on
  v3 too); none of the benchmark sources changes.
- Store to load on v6: a load of other bytes of the doubleword stored
  in the wide instruction before no longer pays (spec/isa/timing.md,
  "Elbrus-2C3 (v6)"), so under E2K_LAT6 e2k_same_dword_p asks for
  overlapping bytes. One place in the benchmark sources moves (xz's
  match finder: a stw at -4 and the next ldw at 0 now share no gap);
  8C2 code unchanged.
- One CTPR is never prepared and transferred through in one wide
  instruction, on any version: v1-v5 transfer to the old target, v6
  falls through (spec/isa/timing.md), and gas refuses the pair only up
  to v5, so -mtune=elbrus-2c3 lost that check. The comments said v6
  allowed it; a checking assert in e2k_gen_bundles now holds every
  instruction to it, and the scheduler's anti-dependence rule covers
  movtd and return prepares too (a few lines move in four of the
  benchmark sources). The rwd %lsr wait's comment says what v6 does
  when a loop is entered too soon (one iteration). On the 2C3: torture
  with -mno-dam passes (with DAM it did already), and the ABI compat
  suite with the PoC tuned for the 2C3 against lcc's 2C3 build passes
  all 1,931 tests for lcc->gcc, gcc->lcc and gcc->gcc.
- Fused multiply-add on v6: fma, fms, fnma and fnms<mode>4 (fmas/fmad,
  fmss/fmsd, fnmas/fnmad, fnmss/fnmsd) for e2k_arch >= 6, type ffma, 5
  cycles through any operand on all six FP channels, 7 to an integer
  consumer. __builtin_fma and fma() become fmad. Contraction follows lcc
  (relcc2 findings P40): off on v6 unless -ffp-contract=fast or
  -ffast-math is given (GCC's GNU C default would fuse every a * b + c),
  and reductions stay unfused (--param avoid-fma-max-bits=64: an fma's
  5 cycles would lengthen the 4-cycle add recurrence). A test of exact
  once-rounded cases and of pipelined loops against the scalar builtin
  passes on the 2C3 at -O2, -O3 and -ffast-math (relcc2 findings I39:
  semantics.md's example has the wrong value), and torture with
  -ffp-contract=fast passes there. Default code is unchanged. Linpack on
  the 2C3 with -ffp-contract=fast: 1.50M -> 1.47M KFLOPS (lcc's own
  1.99M -> 2.05M); the kernels it fuses run at II 1 either way, so what
  costs is elsewhere (being looked at with the ways into pipelined
  loops).
- Cheaper ways into and out of pipelined loops, after a profile of
  Linpack's daxpy calls on the 2C3 against lcc's (relcc2's
  toolchains/claude-e2k/scratch/percall/report.md: the PoC spent about
  60 cycles a call outside the kernels of its unrolled daxpy, lcc
  about 30). The setup's instructions are barriers to the scheduler
  (rwd %lsr, the AAU writes), so what goes around them was placed
  better: the loop's CTPR is prepared before the count's chain, not
  after rwd; ldisp of the array prefetch program goes at the head of
  rwd's block, where the chain covers its 5 cycles to bap; a
  descriptor's base is written from its induction variable, not
  through a copy; the temporary's one value (an increment) is set
  before rwd, unless rwd reads it (e2k_ms_apb_ok may pick the count's
  register: a Linpack-shaped test found that); rwd lets what follows
  share its wide instruction, except a transfer or anything else
  reading a CTPR (as a barrier it carries their dependences on
  prepares before it); two AAU writes share an instruction (ALC2 and
  ALC5). The wait before the loop (e2k_lsr_wait) prints only what of
  rwd's 4 cycles the wide instructions since it haven't spent. On the
  way out, the end of array prefetch is 3 wide instructions instead of
  7 (the zero for %aabf0 set first; anything after the disp of %ctpr2
  that reads no CTPR needn't wait for it), and setbn, setbp and setwd
  may share a wide instruction with other operations (at most one of
  them in each; %b[] users still wait a cycle after setbn). The
  unrolled daxpy's way in: bap at cycle 7 instead of 10, the loop's
  CTPR at cycle 1 instead of 19. Linpack: 2C3 1.503M -> 1.605M KFLOPS
  (lcc's 2C3 build 1.994M), 8C2 1.204M -> 1.25-1.29M (total time
  10.50 -> 10.02-10.16 s; lcc 1.471M), 4C unchanged (lcc's 4C build
  584K, the PoC 617K); CoreMark +0.1%; zlib, bzip2 and xz unchanged on
  the 8C2 and the 2C3 (bzip2 -9 1.8% faster on the 2C3). A loop test
  (twelve kernels, n = 0..300 and 6 sizes to 2,999, against -O0, with a
  SIGALRM every 100 us; APB loops on the 8C2 and 2C3) and a Linpack
  solve (n = 200 and 1000, rolled and unrolled, same checksum as -O0)
  pass on the 4C, the 8C2 and the 2C3; torture at -O2 and -O3 on the 4C
  and at -O2 on the 2C3 too.
- -mfmul-add no longer asks for -ffp-contract=fast: fmul_add rounds
  twice, exactly what the RTL (plus (mult)) it matches says, and lcc
  uses it at -O3. Since contraction is off on v6 by default, the option
  did nothing there. Still off by default: on the 2C3 Linpack runs
  1.605M -> 1.568M KFLOPS with it (2.3% slower; 10% on the 8C2), and
  unrolling Linpack's rolled daxpy for two elements a cycle
  (claude-e2k/scratch/stream-unroll.patch, refreshed for the cheaper
  ways in) gives 1.559M: its kernel runs at II 2, the addend read at
  issue lengthens the pipelines, and Linpack's short calls pay for
  every stage. The loop test and the Linpack solve check are
  bit-exact with -O0 with it on the 8C2 and the 2C3.
- A hardware loop's count | vlc folded into the count's last add when
  the block before the loop computes it as X + C and nothing else reads
  it (the count is below 2^32): one operation less on each way in.
  CoreMark +0.25% on the 2C3 (7,251 -> 7,269 it/s), Linpack and the
  compressors unchanged on the 8C2 and the 2C3. Running GCC's loop
  invariant motion again after doloop, which computes the counts after
  loop2_invariant has run, moved Linpack's count chains out of dgefa's j
  loop as planned but made Linpack 1.5% slower on the 2C3 (0.7% on the
  4C): not kept.
- Fixed (SQLite's speedtest1: SIGSEGV on the 4C, the 8C2 and the 2C3,
  in "Reset the database"): e2k_ms_fold_latches, which turns a loop
  whose latch only jumps back into a one-block loop for the pipeliner,
  moved the latch's operations above the exit test, so they ran on the
  way out too, without ",sm": destroyTable's index scan loaded the next
  index's tnum from a null pIdx. It now moves only operations with a
  speculative form, and marks those that need it. speedtest1 --size 50
  then gives lcc's verification hash on all three machines, at 0.86
  (4C), 0.88 (8C2) and 0.88 (2C3) of lcc's speed.

## v0.3 (2026-10-05)

v0.2 plus the work on wide-instruction code: counted loops on `%lsr`,
data speculation (DAM), unrolling, ALU channels chosen by the compiler,
every branch prepared, check-free control speculation with renaming,
loop versioning for aliasing, per-function `setwd dbl`, a modulo
scheduler with rotating `%b[]` for counted and while loops (DAM in
kernels, two exits merged with `landp`, prologues with the schedule's
cycles), and predicated ALU operations. The entries below are in the
order they were made.

### Results

Speed, -O2 against lcc 1.29.16 -O3 (`e2k-v3`, generic v3 code; relcc2
`toolchains/claude-e2k/perf`, `speed`):

| | v0.2 | v0.3 | lcc |
|---|---|---|---|
| CoreMark, 4C | 1,269 it/s | 2,879 | 2,309 |
| Linpack (linpackc.c, size 200), 4C | 93,815 KFLOPS | 597,031 | 581,920 |
| CoreMark, 8C2 (v3 code) | | 5,788 it/s | 4,469 |
| zlib `minigzip -9`, 11 MB tar, 4C | | 4.39 s | 2.21 |
| bzip2 `-9`, 4C | | 5.0 s | 3.70 |
| xz `-6`, 4C | | 21.6 s | 14.28 |

Decompression is 1.3-1.6 times lcc's time. The benchmarks are loops
this work covers; the compressors are branchy loops lcc if-converts and
pipelines whole (see "Next").

Tests:

| Suite | Result |
|---|---|
| C torture, ieee, dg-torture at -O1, -O2, -O3, -Os (8C2) | 1,639 of 1,639 at each level |
| GCC C suite (`check-c`, 4C; before predication) | 166,713 PASS / 1,458 FAIL (v0.2: 166,718 / 1,439; the new failures are dump scans and guality) |
| ABI compat suite, lcc<->gcc (4C) | 1,931 x 3 pairs, 0 unexpected |
| Real programs' own tests (8C2 and 4C) | zlib, bzip2, xz, zstd, GMP (177 of 178: t-addaddmul skips), pcre2, expat: pass |
| g++, libstdc++ | not run since v0.2 |

### Changes

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
- Predicated execution: `define_cond_exec` on `%predN` (eq/ne), so
  GCC's if-conversion after reload (ce3) puts short branch arms under
  their predicate (`op ? %predN`, `? ~%predN`; up to 6 operations an
  arm, `MAX_CONDITIONAL_EXECUTE`). Predicable: integer moves, add/sub,
  logic, shifts, sign and zero extensions; not loads or stores (they
  are per alternative, through the `enabled` attribute and gensupport's
  `ce_enabled`). The condition prints at the end of the line with the
  new `%?` (gensupport puts a `define_cond_exec` template in front).
  Not under the predicate of an FP compare (`IFCVT_MODIFY_TESTS`): it
  reaches a predicated operation 4 cycles later, and in Linpack's
  idamax the branch around the update cost nothing while the
  predicated update made the next compare wait. sched-deps keeps the
  output dependence between two writes of one register under exclusive
  predicates (generic; both arms of an if-else incrementing one counter
  went into one wide instruction, whether E2K allows that isn't known).
  Real programs on the 4C: zlib -9 compression 4.57 -> 4.39 s, xz -6
  22.65 -> 21.62 s, xz decompression 0.31 -> 0.28 s, bzip2 unchanged;
  8C2: CoreMark unchanged (5,788 it/s), Linpack 11.13 -> 11.22 s.
  Predicated loads and stores too gave xz another 3% and CoreMark 0.7%,
  but Linpack lost 7%: its daxpy kernel (whose code predication doesn't
  touch, only the registers it got) ran at 6 cycles an iteration
  instead of 4.6, with write-back conflicts that the spec says don't
  delay FP consumers (relcc2 findings I19); left out until that is
  understood. lcc on the same programs is still well ahead (zlib 2.2 s,
  bzip2 3.7 s, xz 14.3 s): its loops are if-converted whole and
  pipelined, ours keep their branches.

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

## Next (after v0.3: real programs)

Real programs are slower than lcc's (4C, `toolchains/claude-e2k/
speed/speed.sh`): zlib -9 compression 4.4 s against 2.2, bzip2 5.0
against 3.7, xz -6 21.6 against 14.3, decompression 1.3-1.6x. Profiles
(`tools/isa-score/profile.py`): lcc if-converts whole loops with
branches inside (`landp` chains, predicated adds and loads, merges) and
pipelines or unrolls them with speculation (zlib's `longest_match`
chain walk at ILP 8.6 against our 1.25; bzip2's `mainGtU` compare
chains, `mainSort`'s scanning loops 4x faster). CoreMark and Linpack
don't show this.

Measuring (relcc2 `toolchains/claude-e2k`): `perf/build.sh NAME "CC"
O2` then `perf/run8.sh DIR...` on the 8C2 (check "Correct operation
validated": CoreMark calibrates its count); `real/real-all-h.sh NAME CC
CFLAGS [4c|8c2]` builds and tests the real programs, `speed/speed.sh
HOST BUILD...` times their compression; `torture/hw8.sh NAME "OPTS"`
(compiler in `$G`) runs every torture test on the 8C2. Long tests use a
copy of the compiler (`scratch/gcc-snap`, `$SNAP`) so that the build
can go on. Build only `cc1`, through ccache (`PATH=/usr/lib/ccache/bin:
$PATH make -j12 -C build-gcc-claude2/gcc cc1`).

Plan, in order:
1. Branchy loops: if-convert loops with short internal arms into one
   predicated block (predicated ALU ops, speculative loads, `landp`
   for combined exits) so the modulo scheduler takes them (it would
   need predicated nodes: a predicate lives at most II cycles); while
   loops whose first block leaves to a rare path that comes back
   (zlib's chain walk) as a kernel exit plus re-entry through the
   prologue.
2. The kernel stall behind relcc2 findings I19 (FP-side results and
   write-back conflicts), then predicated loads and stores.
3. Smaller: the `ibranch` after a pipelined loop's exit copies (6
   cycles an exit), prologue cost of deep schedules on short trips,
   return prepared at entry, loop-exit `disp`s hoisted.
4. Tests: g++ and libstdc++ suites (last at v0.2), more real programs
   (sqlite, Lua, jq).
5. Port gaps: trampolines, sibcalls, `-march` v5+ (64-bit `%lsr1`).
