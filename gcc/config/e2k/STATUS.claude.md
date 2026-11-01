# E2K back end proof of concept: state

Written by Claude (Anthropic) on the branch `claudes-e2k-compiler`, from
the relcc2 specification (`spec/isa`, `spec/abi`, `doc/gcc-port-plan.md`)
to find out what the spec is missing. Not for contribution to GCC (GCC
refuses AI-written code); the owner writes the real port by hand and may
reuse the design. Spec gaps go to relcc2 `docs/spec-poc-findings.md`.

This file is the source of truth for the work; update it with every
commit. Tags `v0.1` to `v0.6` mark the states described in the
sections of those names; "Since v0.6" lists what came after.

## Since v0.6

- The late pass checks the insns it builds as validate_change does
  (insn_invalid_p: constraints too), not with recog alone. A latch copy
  had put a DF store under a predicate, which recog takes as
  `*p *movdf_insn` although its store alternative isn't predicable, and
  final died: "insn does not satisfy its constraints" in vim 9.0's
  vim9execute.c, built by OS Elbrus's PDK (relcc2 findings P119). GCC's
  C torture at -O2, -O3 and -Os: assembly unchanged.
- A block left with nothing but its note is merged into the block it
  falls into before sched-ebb (e2k_merge_empty_blocks, now
  e2k_merge_jumpless_blocks; e2k_cond_returns
  after e2k_tail_dup_joins leaves some). sched-ebb put the next block's
  compare into the empty one and then had to move that block's jump
  after it, which it does only for a speculation check: ICU 67's
  collationiterator.cpp died in move_block_after_check (haifa-sched.cc),
  built by OS Elbrus's PDK (relcc2 findings P120). C torture: 17 of
  9,588 compiles change (the scheduler now works across the merged
  block, loop-15.c -O2 93 -> 85 wide instructions); the 7 changed v3
  execute tests pass on the 4C, pr113787 (changed for the 8C2 only)
  under MCST's qemu.
- A 16-byte vector built from constants takes the constant path only
  when every lane is a number: a lane that is an address is CONSTANT_P,
  but the CONST_VECTOR made from it has no constant half, and
  e2k_expand_move_v16 passed a null half on. Python 3.11's
  typeobject.c (`{&_Py_NoneStruct, NULL}`, SLP-vectorized for the 8C2
  and 2C3) segfaulted in expand (relcc2 findings P121). C torture:
  assembly unchanged.
- Fortran builds (gfortran, libgfortran: --enable-languages=c,c++,fortran,lto
  in relcc2's scripts). GCC's Fortran testsuite with the v3 cross on the 4C
  (static libgfortran, 0.6+4): 76,345 PASS, 131 FAIL, 62 UNRESOLVED. 125
  of the 193 come from internal procedures passed as arguments or taken
  as procedure pointers, which needed trampolines (the next entry).
  libgfortran is now built with
  -mno-spec-fp (configure.host's ieee_flags, as libquadmath's configure
  does): ieee/maxloc_nan_1, minloc_nan_1 and minloc_nan_2 had died of
  SIGILL after the program cleared the FP flags.
- Trampolines for nested functions whose address escapes (Fortran's
  internal procedures passed as arguments, too): MCST libffi's closure
  trampoline as doc/gcc-port-plan.md D1 gives it, two wide instructions
  that load the function into %ctpr1 and the chain into %g12 and jump.
  TARGET_TRAMPOLINE_INIT stores its five doublewords (the two literals
  rotated by 32 bits, high half first) and calls __clear_cache on them.
  The block has 64 bytes of slack, and the entry moves off page offsets
  0xdc0-0xdff (CODE_PLACEMENT, as gas moves labels; the same code in
  TARGET_TRAMPOLINE_ADJUST_ADDRESS). An object that builds one gets an
  "x" GNU-stack note and others none, as from lcc, so ld marks the
  program RWE. On the 4C: nested functions called through trampolines,
  recursively and from every 16-byte stack position (the 4 bad ones
  moved to 0xe00), static and dynamic; with -z noexecstack the call is
  SIGSEGV. GCC's 38 C tests that need trampolines: 444 PASS, 4 FAIL,
  all "returning a variable-sized value" (below, "Gaps lcc shares").
- A transfer never shares a wide instruction with a prepare of its CTPR,
  in either order (e2k_gen_bundles; only a jump carried into the next
  block's first instruction was kept from a later disp). A pipelined
  loop's prologue on a way in that doesn't fall into the kernel ends in
  a jump through the loop end's CTPR, which the prologue's second cycle
  prepares; with nothing else in its cycles after that the jump joined
  the disp, and the bundle check died ("in e2k_gen_bundles") in
  harfbuzz 8.0.1's hb-subset.cc (graph_t's constructor, -O2 for the
  8C2), built by OS Elbrus's PDK (relcc2 findings P122). The jump now
  takes a wide instruction of its own. C torture at -O2 for v3 and the
  8C2: assembly unchanged (3,166 compiles).
- ",sm" pruning (e2k_spec_prune) counts a register as possibly
  diagnostic until something sets it on every path from the entry, and
  every register a call clobbers after the call: a caller or callee can
  leave a diagnostic value there from its own speculative loads. It
  had started each function clean and stepped over calls, so a compare
  run ahead of its guard, reading a register nothing had set on that
  way in, lost its ",sm": gfortran's bind-c-contiguous-4 at -O2 died of
  SIGILL on the 4C in char_assumed_rank_f (cmpedb on an absent
  argument's extent in %g24, after libgfortran's runtime-warning call;
  relcc2 findings P124). C torture at -O2 for v3 and the 8C2: 67 of
  3,166 compiles gain ",sm" flags (976), nothing else changes.
- The machine-dependent pass drops DF_LIVE after reorg_loops, so its
  passes and sched-ebb see DF_LR's liveness: a register read on a jump's
  other way counts as live there even where no definition reaches it.
  DF_LIVE left such a read out, so a load the scheduler ran ahead of the
  test could set the register on that way, and its diagnostic value
  trapped at the read: gfortran's maxloc_with_mask_1 at -O2 (an absent
  mask's stride, multiplied in a block both ways share) died of SIGILL
  on the 4C (relcc2 findings P124). C torture at -O2 for v3 and the 8C2:
  55 of 3,166 compiles change (3,406 -> 3,413 wide instructions); the
  29 tests' 452 v3 execute results pass on the 4C.
- A reference through a VIEW_CONVERT_EXPR that makes the access larger
  than its operand gets alias set 0 (alias.cc,
  reference_alias_ptr_type_1), not the operand's. gfortran copies a
  polymorphic array's elements as VIEW_CONVERT_EXPR <struct t2> (*p),
  P a pointer to the declared type t1 that t2 extends; with t1's alias
  set the store of t2's real component didn't conflict with loads of
  it, and sched-ebb moved such a load above the store:
  gfortran.dg/class_assign_4.f90 at -O2 -ftracer and the -O3 set
  stopped with STOP 1 on the 4C (relcc2 findings P125). Any target that
  moves loads across stores by alias sets could do the same; only the
  E2K's speculation above jumps brought the two together here. C
  torture at -O2 for v3 and the 8C2: assembly unchanged.
- A load that drops its dependence on a jump keeps its order with the
  stores that jump stood for. Past param_max_pending_list_length (32)
  pending jumps, sched-deps makes the next jump a memory barrier
  (flush_pending_lists): it takes over the pending loads and stores,
  and later loads depend on it alone, with an anti dependence, the
  kind e2k_spec_pin drops to run a load above a jump. sched-deps now
  records its barriers (sched_deps_flush_insns), and e2k_spec_pin gives
  such a load a dependence on each store, call or asm before the
  barrier that may write what it reads, through earlier barriers.
  Shown with --param max-pending-list-length=4 on a store, 40 exits and
  loads that may alias it: three loads ran ahead of the store, and on
  the 4C the program gave the wrong result; now none. Not seen at the
  default limit in GCC's C torture or harfbuzz's hb-subset.cc (relcc2
  findings P126); C torture at -O2: assembly unchanged.
- C++: store_init_value folds a scalar's CONSTRUCTOR in a template
  again. GCC master's dad7275f7cc (PR c++/126811, 2026-09-07) stopped
  folding every CONSTRUCTOR there, and a scalar's, T{v}, then reached
  constexpr evaluation, which takes CONSTRUCTORs only for classes and
  arrays: "constexpr int i = int{5};" in a template died in
  verify_ctor_sanity (protobuf 3.21's map.h, built by OS Elbrus's PDK;
  relcc2 findings P127). Not the E2K's: pristine master at the base and
  at 5825d4a7a82 (2026-10-30) ICE the same for x86. x86 build of this
  tree: g++.dg's template, cpp0x, cpp2a and cpp23 tests and the
  constexpr, NSDMI and initlist ones pass (54,397 and 7,627 results, no
  FAIL), nsdmi-template27.C (PR 126811's test) among them.
- The modulo scheduler's time grows with a loop's dependences, not with
  their number times its nodes: e2k_ms_schedule visits each node's
  dependences through per-node lists (e2k_ms_adj); the least II at
  which its earliest starts settle is found once per set of
  dependences (e2k_ms_est_settle), where each try at a smaller II and
  slack had run N rounds over all of them; and e2k_ms_add_dep finds a
  duplicate through a hash index. gfortran.dg/sizeof_6.f90 at -O3,
  whose loops of 322 and 506 insns have some 250,000 memory
  dependences, compiled in 190 s and timed out in GCC's testsuite on the
  4C's run; now 31 s, with the same assembly. C torture at -O2 for v3
  and the 8C2: assembly unchanged.
- gfortran's REAL(16) comes from libquadmath, not libm's *f128
  functions: MCST's glibc for E2K has a placeholder sqrtf128 that
  returns its argument (OpenE2K glibc, sysdeps/e2k/fpu/e_sqrtf128.c,
  "this fake implementation"), and its generic float128 functions call
  it too. On the 4C sqrtf128 (2) is 2 and sqrtf128 (-42) -42, from the
  PoC's and lcc's C alike; gfortran.dg/ieee/large_1, quad_2 and
  dec_math failed on it (relcc2 findings A50). e2k.h defines
  TARGET_LIBC_FLOAT128_MATH_BROKEN, which trans-types.cc honours, and
  libgfortran's configure.ac and configure (edited alike: no autoconf
  2.69 here) set have_iec_60559_libc_support=no for e2k.
- libgfortran's spec keeps a -static link static under
  -static-libquadmath: its "-Bstatic -lquadmath -Bdynamic" turned ld
  back to shared libraries for -lm and libc, and the program, static
  crt1.o and crtbeginT.o with a shared libc and no interpreter, died
  at start (gfortran.dg/static_linking_1.f on the 4C, whose board
  links the runtime statically). The -B options now go only without
  -static, as gfortranspec.cc does for -lgfortran. acinclude.m4 and
  configure edited alike. Not the E2K's.
- gfortran's driver puts -lcaf_shmem (-fcoarray=shared, new on master)
  before libgfortran, which it calls: after it, a static libgfortran
  left _gfortran_random_seed_i4 and 8 more undefined
  (gfortran.dg/coarray_51.f90 on the 4C's static board). Not the
  E2K's.
- Before sched-ebb every block that ends in no jump is merged into the
  block it falls into (e2k_merge_jumpless_blocks, was
  e2k_merge_empty_blocks), not only an empty one: in mysql 8.0.27's
  xcom new_id, unrolled by e2k_cond_returns into a chain of exits, a
  block of two copies had one moved up and one down past the next
  block's jump, which then crossed into it and died in
  move_block_after_check (haifa-sched.cc) for v6 and the 8C2 (relcc2
  findings P128, after P120). C torture at -O2 for v3 and the 8C2: 109
  of 3,166 compiles change (5,329 -> 5,219 wide instructions); their
  54 tests' 824 v3 execute results pass on the 4C.
- Each register that some path reads before writing it is zeroed
  (e2k_zero_undefined; -mno-zero-undefined turns it off): after the
  prologue every one DF_LR finds live but the argument slots, and after
  a call every one it clobbers that is live after it, under the call's
  predicate (where a predicated call doesn't run, a value lives on in a
  register it clobbers). A forward walk drops what DF_LR overcounts: a
  read under the predicate of an earlier set in its block (an
  if-converted call and its arguments), and a pipelined loop's ring
  read under %b[0..7]'s names past its setbn_enter. A register some insn
  uses as a 16-byte vector is zeroed whole. GCC reads such registers
  for variables set on some paths only, or structs built by inserting
  fields: gfortran.dg/optional_absent_4.f90 at -Os stepped an absent
  mask's offset in %g24 in the loop both paths share, and on the 4C the
  addd was SIGILL on the diagnostic value (0x4afafafa4afafafa, tag 1)
  that a failed speculative load before the call had left there
  (relcc2 findings P129; spec/abi/calling-convention.md, "Unused parts
  of a slot"). It now passes at -O0 to -O3 and -Os. C torture at -O2
  for v3 and the 8C2: 375 of 3,166 compiles change (28,878 -> 28,901
  wide instructions); their 190 tests' 2,804 v3 execute results pass on
  the 4C. sqlite3.c for the 8C2: 230,116 -> 230,457 wide instructions,
  compile time +1.3%.
- A C++ thunk no longer takes the ",sm" marks of the function before
  it: e2k_output_mi_thunk sends its insns through final without
  e2k_reorg, whose per-UID flags (e2k_ms_flags) still held the last
  function's, and e2k_asm_output_opcode put ",sm" on every line of the
  thunk's jump, directives and braces too ("{,sm", ".accept,sm"), which
  gas rejects: lucene's SegmentInfos.cpp in Qt 4.8.7, built by OS
  Elbrus's PDK (relcc2 findings P130). The flags are cleared at each
  function's end. 114 C++ tests with virtual bases or covariant
  returns compile and assemble for the 8C2, none with a stray ",sm".
- libgfortran's close_units frees c_locale only once init_units has
  set it. A -fcoarray=lib image whose shared memory mmap didn't land at
  the supervisor's address exits (210, to be started again) from the
  program's coarray registration constructor, which may run before
  libgfortran's; the destructors then ran close_units, and
  freelocale (0) is SIGILL in MCST's glibc for E2K (a speculative load
  through the null pointer, a branch on the result). The supervisor
  took the image for failed: GCC's coarray execution tests failed (exit
  4, the image's signal) or hung in a barrier, a different 11 to 14 in
  each run on the 4C. this_image_1, atomic_1 and sync_images_failed_1,
  four at a time: 25 of 120 runs had failed and 4 hung, now 120 pass. Not
  the E2K's.
- A procedure that uses the IEEE modules runs no FP operation
  speculatively, as under -mno-spec-fp (owner, 2026-10-31): it may clear
  the flags or unmask exceptions, after which a speculative FP operation
  that raises a flag gives a diagnostic value. The mach pass finds such
  a procedure by its call of _gfortran_ieee_procedure_entry, which
  gfortran puts at the start of each (the REG_CALL_DECL note; the call
  itself goes through a CTPR), so a caller it is inlined into counts
  too. A loop of FP operations in one: 28 ",sm" FP operations, 52 wide
  instructions -> none, 21; the same loop elsewhere keeps them. The five
  IEEE tests that still die of SIGILL on the 4C (ieee_2, large_3,
  dec_math_1, minmax_3/4 at -O0) die inside the 4C's MCST libm (logbf,
  sqrtl, tanl, fmaxf: its speculative FP after the program cleared the
  flags), not in the PoC's code, so this doesn't change them.
- In a block the scheduler skips (a pipelined loop's prologue or
  kernel), an insn the pipeliner gave no clock, a transfer aside, takes
  a wide instruction of its own (e2k_gen_bundles). What was left on the
  edge the pipeliner split for its prologue lands there: the previous
  pipelined loop's exit (zero a register, stop the array prefetch with
  disp %ctpr2 and an aaurw of that register to %aabf0, setbn_leave) all
  went into one instruction, which gas rejects ("cannot encode MAS: CS1
  syllable is busy with set-instructions": aaurw's MAS and the setwd
  both need CS1), and whose aaurw read the register's old value. aom
  3.8.1's encodemv.c for the 8C2, built by OS Elbrus's PDK (relcc2
  findings P132). C torture at -O2 for v3 and the 8C2: 6 of 3,166
  compiles change (440 -> 452 wide instructions); their 3 tests' 48 v3
  execute results pass on the 4C.
- store_field (expr.cc, generic) stores a call's result returned in
  registers that no integer mode holds through a stack temporary. E2K
  returns aggregates of up to 64 bytes in registers, and the bit-field
  path for a C++ base whose tail padding the derived class reuses took
  smallest_int_mode_for_size (24 bytes) and failed (an ICE in require,
  at -O0 too). qtwebkit 5.212's NativeWebWheelEventQt.cpp for the 8C2,
  built by OS Elbrus's PDK (relcc2 findings P133). Paths that worked
  are unchanged by construction; the base's 20 bytes are copied, not
  its type's 24. g++.dg/torture/e2k-ret-base-tail-padding.C passes at
  -O0 to -O3 on the 4C.
- _LITTLE_ENDIAN is predefined (1), as lcc 1.29.16 defines it in every
  mode (C, C++, -ansi). virtualgl 2.6.5's copy of boost's endian.h
  knows E2K only through it ("needs to be set up for your CPU type"),
  built by OS Elbrus's PDK (relcc2 findings A51).
- An FP compare into a predicate right before a reader of it (a merge,
  a predicated operation) right before a taken return: on the 4C the
  reader takes the predicate as it was before the compare (relcc2
  findings I57; one empty cycle between compare and reader, or between
  reader and return, is enough; integer compares are fine). Scheduled
  code keeps the compare's latency of 4. Unbundled output (-O0,
  -fno-schedule-insns2) now prints nop 1 after such a compare, and a
  block jumped to, or fallen into right after a predicate write, whose
  first wide instruction reads a predicate and whose next returns gets
  an empty instruction first, as I17's rule gives one to a first wide
  instruction that reads a predicate and transfers.
  gcc.c-torture/execute/pr39501.c at -O0 (-ffast-math: min and max as
  merges) passes on the 4C. At -O2 the 1,583 execute tests compile as
  before; at -O0 -ffast-math two of them get the nop.
- An asm input of an integer type tied ("0") to a wider integer output
  is zero-extended into the output's mode (e2k_md_asm_adjust), as lcc
  does from -O2 (addd 0, 0 and adds into the register in one wide
  instruction; at -O0 it writes the low half only). The PoC wrote such
  a constant with adds under dbl = 0, which keeps the upper half, so
  g++.dg/opt/pr23478.C's loop bound was garbage there and it died
  later with SIGILL on the 4C (relcc2 findings A52). It passes now; of
  the 3,719 execute and compile torture tests at -O2 only
  compile/20020312-1.c (such an asm) changes, its two loads swapping
  channels.
- An untyped call (`__builtin_apply`) sets every result register, a
  PARALLEL as aarch64's untyped_call gives. As a plain call it only
  clobbered %b[0]-%b[7], so e2k_zero_undefined zeroed them before the
  result block saved them, and `__builtin_return` returned 0:
  builtin-return-1, builtin-return-2 and builtin-apply-4 (gcc.dg and
  torture/stackalign) aborted on the 4C at every level. They pass now
  at -O0 to -O3 and -Os, as do the other run tests that use
  `__builtin_apply` (builtin-apply2, builtin-apply3, stackalign's
  builtin-apply-2 and -3, pr47237).
- e2k_merge_jumpless_blocks goes by a block's last real insn: with -g,
  debug insns after a call that ended the block made it look jumpless,
  and it was merged into the next only then. gcc.dg/torture/pr59166.c
  (-O2, -Os), g++.dg/opt/pr100541-2.C and g++.dg/torture/pr116179-1.C
  (-Os) failed -fcompare-debug; they pass now. Without -g nothing
  changes: the 1,699 execute tortures at -O2 for the 8C2 compile as
  before.

## v0.6 (2026-10-29)

v0.5 plus a week of building MCST's Linux 6.1 and glibc 2.35 (OpenE2K)
with this compiler, so that a system needs nothing from lcc. The
kernel, glibc, binutils, gdb, this GCC and busybox, all built by the
PoC, boot on the 8C2. The changes came from what those sources ask of
a compiler (lcc's pragmas, inline-asm forms and builtins), from the
first boots, and from the testsuites of glibc and GCC run with the
native compiler on the machines. The tag is on `611906bb6b1`, the
commit every result below was measured with (`0.5+56`).

### Results

| Test | Result |
|---|---|
| Native bootstrap (C, C++, LTO; stage 1 at -O3, -j6) | passes on the 4C (v3, about 12 h) and the 8C2 (about 6 h) |
| glibc 2.35's testsuite, glibc built natively by the bootstrapped compiler | 8C2 (`-mtune=elbrus-8c2`): 3,379 PASS, 694 FAIL; 4C (v3): 3,349 PASS, 726 FAIL. lcc 1.29.16's native build: 2,842 / 1,140 and 2,817 / 1,166 (lcc compiles none of about 720 math tests) |
| glibc's cancellation tests with this libgcc_s | 84 of 92 pass on both; the 8 others lose a cancellation across a signal frame in MCST's unwinder |
| check-gcc on the 8C2 without the gdb tests (`GDB=/bin/false`, -j4) | gcc: 165,390 expected passes, 471 unexpected failures; g++: 267,644 and 77 |
| The gdb tests (guality, simulate-thread), one file at a time | gcc: 3,920 PASS, 280 FAIL; g++: 440 PASS |
| ABI compat suite, lcc and this compiler in both roles (1,931 tests a pair) | 0 unexpected under qemu (v3), on the 4C (v3) and on the 8C2 (v5), the booted system included |
| relcc2 `tools/distro` | 1,341 ELF files with 4,439 `.comment` strings, all this compiler's. Booted on the 8C2 over AoE (8 CPUs). On it, the native g++ and gdb worked, GNU make 4.4.1 rebuilt itself (its second and third builds are identical), and set 2 built natively passes all 26 checks |

Against the round before (`0.5+52`), glibc's results are the same test
for test. check-gcc changed only where P117, P118 and the sched-ebb ICE
were fixed (`pr107115.c`, `unroll-and-jam.c`, `pr80205.C`,
`pr100254.C`), and the gdb tests are the same. The 4C hasn't booted
the system yet (no serial console; 0.7).

### Changes

- `--with-arch=elbrus-vN` and `--with-tune=CPU` set the default ISA
  version and CPU (`OPTION_DEFAULT_SPECS`), as lcc's tree for a CPU has
  them: the cross compilers on lcc's `e2k-v5.8c2` and `e2k-v6.2c3`
  sysroots, whose system libraries already make every program run on
  that CPU alone, are configured `--with-tune=elbrus-8c2` and
  `--with-tune=elbrus-2c3`, and their libgcc and libstdc++ are built
  for that CPU. An `-march` on the command line drops the default CPU
  too, since `-mtune` overrides `-march`.
- `-mtune=elbrus-8c`, `elbrus-1c+` (v4), `elbrus-48c` and `elbrus-8v7`
  (v7), with lcc's `__elbrus_8c__`, `__elbrus_1cplus__`,
  `__elbrus_48c__` and `__elbrus_8v7__`, gas's `-mcpu` of the same name
  (an 8C object's `e_flags` are lcc 1.29.16 `e2k-v4.8c`'s, 0x13000010)
  and, like the 4C and 8C2, prefetches of locality 3 without a MAS, as
  the `e2k-v4.8c` and `v4.1c+` lcc trees emit them. `-mptr64` and its
  alias `-m64` are accepted (glibc's configure adds `-mptr64`);
  `-mptr32`/`-m32` and `-mptr128`/`-m128` stop with an error that names
  the mode, not as unknown options (relcc2 docs/poc-roadmap.md, B5).
- lcc's pragmas (`e2k-c.cc`; relcc2 spec/abi/source-compat.md,
  "Pragmas"), which glibc's and the kernel's E2K code use under `-Wall
  -Werror`: `ivdep`, `novector` and `unroll (N)` are GCC's `GCC ivdep`,
  `GCC novector` and `GCC unroll N`; the others (`loop count (N)`,
  `noprefetch`, `asm_inline`, `asm_length (N)`, `diag_suppress`, ...)
  are dropped by the preprocessor, as Darwin's `mark`, so they may sit
  between `unroll (N)` and the loop, where GCC's parser takes only its
  own loop pragmas (62 such runs in glibc and the kernel). `-E` keeps
  them. A bare `unroll` (lcc: unroll fully) is an error, as GCC's
  `unroll` needs a count; neither tree uses it. Before a `for` loop
  without a condition, where GCC's parsers refuse `GCC unroll` and `GCC
  ivdep` ("missing loop condition") and glibc and the kernel put lcc's
  (41 times), the hint is dropped (`LOOP_PRAGMA_WITHOUT_CONDITION_OK`, a
  macro in the C and C++ parsers).
- C++ types as l++ has them (relcc2 spec/abi/calling-convention.md, "C++
  ABI beyond calls"): `__float80` is `long double` itself, as on x86
  with an 80-bit long double, so `f (long double)` and `f (__float80)`
  are one function and C's `__builtin_types_compatible_p` says 1 (they
  were two types that both mangled `_Z1fe`); only `long double` mangles
  as `e`, and `_Float64x`, also XFmode, keeps the generic `DF64x`. Still
  open from the same list: a guard variable in its variable's COMDAT
  group as l++ puts it (a C++ front-end change; `-fno-gnu-unique` links
  either order meanwhile), and lcc's `alignof` of vectors of 32 bytes
  and more (their size; ours 16, since `min_align_of_type` caps at
  `BIGGEST_ALIGNMENT`, whose increase would also align every `alloca`
  to it).
- lcc's inline-asm forms that glibc and the kernel use (relcc2
  spec/abi/source-compat.md, "Inline assembly"; kernel-build.md):
  - `register T *fp asm ("FP")` (or `"%FP"`) reads the stack pointer at
    entry, as glibc's `_start` and ld.so's `_start2` need, and `"SP"`
    the current one. GCC refuses the argument pointer, which holds that
    value, for register variables, so `"FP"` is the hard frame pointer
    `%r9`, and a function whose insns read it gets a frame pointer,
    which the prologue sets to the entry stack pointer
    (`e2k_frame_pointer_required`; without a frame, `getsp 0` as in
    lcc). Checked under MCST's qemu against the caller's `"SP"`, `-O0`
    and `-O2`, v3 and v5, lcc giving the same.
  - `%L` prints the first register of a 16-byte value in a register
    pair, beside `%H`; on an asm operand that isn't one both are errors,
    as in lcc.
  - `J`: an integer 0-255.
  - A struct or union whose size is an integer mode's but which is
    aligned less than that mode (the kernel's 16-byte `e2k_qreg_t`, an
    8-byte struct of ints) is BLKmode on a strict-alignment target, and
    as an `"r"` operand it was an impossible constraint (outputs) or
    "probably does not match constraints" (inputs). `expand_asm_stmt`
    (a generic change in `cfgexpand.cc`; `copy_blkmode_from_reg` made
    extern) now moves such an operand through a register of that mode,
    for outputs, inputs and `"+r"`, as lcc gives it registers.
  - lcc's `"x"` from v5 takes any 16-byte value in one register (v3,
    v4: long double only, an error otherwise): a 16-byte vector as it
    is, anything else (`__int128`, `__float128`, a 16-byte struct)
    packed with `qppackdl` before the asm and taken apart with
    `qpswitchd` and a 64-bit read after it, as lcc does; and `"r"` on a
    16-byte vector from v5 is an even pair, as for every other 16-byte
    type (lcc's `-mno-old-asm-constraint-r` meaning, which MCST says
    will become the default; before, it was one register and `%H` an
    error).
    `e2k_md_asm_adjust`. `"x"` and `"+x"` on `__int128`, vectors and a
    struct, `"r"` on a vector with `%H`: lcc 1.29.16's results under
    MCST's qemu as v5, at `-O0` and `-O2`.
- lcc's run-time CPU detection (`e2k-builtins.cc`; relcc2
  spec/abi/source-compat.md, "CPU detection at run time"):
  `__builtin_cpu_is ("NAME")` folds to a load of the hidden
  `__cpu_info`'s word (+0 for `elbrus-vN`, +4 for a CPU) and a compare,
  as lcc compiles it, with lcc's names (`elbrus`, `elbrus-s` ...
  `elbrus-8v7`,
  `elbrus-v1` ... `elbrus-v7`); a non-literal or unknown name is an
  error at the call (`TARGET_CHECK_BUILTIN_CALL`), as in lcc.
  `__builtin_e2k_get_cpu_iset ()` is the +0 word; `__builtin_cpu_init`,
  `__builtin_cpu_name` and `__builtin_cpu_arch` call libgcc's
  `__cpu_init` and the new `__cpu_name` and `__cpu_arch` (`cpuinfo.c`,
  which also knows the 48C's model 0x0d, as lcc's runtime names the
  community qemu's v7). Under MCST's qemu (v3-v7) and the community
  qemu (v6, v7) the names, ISA versions, `__cpu_info` and
  `__builtin_cpu_is` results equal lcc 1.29.16's at `-O0` and `-O2`.
  Limit: `cpuinfo.o` is only in `libgcc.a`, which `g++ -shared` (with
  `-shared-libgcc`) doesn't link, so a C++ shared library that uses these
  builtins needs `-lgcc`; lcc's driver always links its runtime archive.
- Every asm statement is volatile (`-masm-volatile`, the default;
  `ASM_ALWAYS_VOLATILE_P`, a hook in `gimplify_asm_expr`), as lcc takes
  them: never deleted, merged or moved, also with unused outputs. MCST's
  kernel writes `barrier()`, per-CPU stores, the opening of user access
  and its state-register reads as non-volatile asms with dummy outputs
  (relcc2 spec/abi/kernel-build.md, "Inline assembly the kernel relies
  on"), which GCC's rules delete, merge or hoist (a `%sclkr` wait loop
  became endless). Owner's decision (2026-10-22): the compiler keeps
  them, the kernel isn't patched. `-mno-asm-volatile` gives GCC's rules.
- asm statements take up to 40 operands (MCST's kernel has one of 39,
  `TRAP_HANDLER_DONE`; lcc takes 50): a pattern that never matches makes
  `MAX_RECOG_OPERANDS` 40, the most genoutput takes per pattern.
- `-ffixed-ctpr1` to `-ffixed-ctpr3` keep the passes off that CTPR (lcc's
  `-fexclude-ctpr2`, which MCST's kernel builds its trap entry with):
  the CTPRs are fixed registers that the port's passes give out
  themselves, so `e2k_option_override` reads the options
  (`e2k_ctpr_reserved`); indirect jumps and jump tables go through
  `%ctpr1` instead of `%ctpr2`, the branch and loop passes choose among
  the others, and with `%ctpr2` reserved no loop is pipelined and there
  is no array prefetch or AAU store. A test with a jump table, loops,
  calls and a call through a pointer has no `%ctpr2` and gives the same
  results under MCST's qemu.
- lcc's `check_stack` attribute, which MCST's kernel writes
  `__interrupt__` for other compilers (about 90 functions: fast system
  calls, the global-register save, setjmp; relcc2
  spec/abi/kernel-build.md, "Functions without a data-stack frame"): no
  data-stack frame; calls with register arguments reserve no outgoing
  argument area (no `getsp`), and what would need the data stack is an
  error, as in lcc: spills and locals in memory, `alloca`, more than 8
  arguments in or out, a result over 64 bytes, a variadic call. At
  `-O0`, where GCC keeps every variable in memory, every such function
  is refused (the kernel builds at `-O3`).
- Functions with `check_stack` or `interrupt` may be inlined
  (`TARGET_FUNCTION_ATTRIBUTE_INLINABLE_P`; GCC's default inlines no
  function with a machine attribute), as lcc does: MCST's kernel has
  `__always_inline __interrupt` helpers (`native_read_UPSR_reg`), an
  "inlining failed" error in every file reading `%upsr` without it.
- `__attribute__ ((target ("no-control-spec,no-pipeline")))` turns those
  switches off for one function (also `[no-]pipeline-while`, `dam`,
  `apb`, `staa`): MCST's kernel turns semi-speculative loads off in its
  user-access functions (`__no_semispec`), which lcc 1.31.05 spells
  `optimize ("-fno-semi-spec-ld")`; GCC's optimize attribute takes only
  `-f` and `-O` options, and the PoC's `-O1` still speculates (`ld,sm`).
  The switches are `Save` options, put in place per function
  (`TARGET_SET_CURRENT_FUNCTION`); a function is inlined only into
  callers whose switches allow nothing it forbids
  (`TARGET_CAN_INLINE_P`; the kernel inlines an `always_inline` body
  without the attribute into the function with it). A test with
  pointer-chasing and counted loops: speculative loads only outside the
  marked functions; the compat suite has no unexpected failure.
- In a `check_stack` function nothing spills: values live across a call
  take window registers, which calls keep, not a global saved around the
  call on the stack (`flag_caller_saves` off there, set per function in
  `TARGET_SET_CURRENT_FUNCTION`), and every pseudo keeps a register
  class (`TARGET_IRA_CHANGE_PSEUDO_ALLOCNO_CLASS`: IRA gave none to a
  constant with a `REG_EQUIV`, and LRA spilled it). MCST's
  `fast_syscall_read_sclkr` and `dump_vprintk` were refused for those
  spills; with the TImode unions and the zero stores above, all nine
  `__interrupt` functions the PoC refused compile, as with lcc.
- `-mforce-inline` inlines every function declared `inline` wherever it
  can be, past the size limits (`DECL_DISREGARD_INLINE_LIMITS`, no error
  where it can't be), as lcc's `-fforce-inline`, part of its `-fkernel`:
  MCST's kernel has helpers that are correct only inlined (they rewrite
  the current frame's `%cr0`, `%usd`, `%wd`; relcc2 kernel-build.md,
  "Forced inlining"). An `inline` helper of 120 statements called 8
  times: 8 calls without it, none with it.
- `__builtin_trap`, and the traps GCC itself puts on paths it finds
  erroneous (`-fisolate-erroneous-paths-dereference`, on at `-O2`), is a
  store of 0 to address 0 (SIGSEGV), as lcc compiles it. Without a
  `trap` pattern GCC called `abort`: ld.so, linked from glibc's rtld
  objects, then pulled in `abort` and `raise` from libc, and its link
  failed on `raise`'s symbol versions. The 0 is written to the first
  global temporary not fixed, `%g16` unless `-ffixed-g16` (the
  kernel's), as lcc moves to `%g17`, and `%r0` when all sixteen are
  fixed (the kernel's trap entry), as lcc; the C++ thunks' temporary and the
  register handing a large result's buffer to the call expander
  (`SRET_REGNUM`, `%g31` down) honour `-ffixed-gN` the same way
  (`e2k_global_temp_regno`).
- 128-bit multiplies are inline, `muld` and `umulhd`/`smulhd` as lcc
  compiles them (`umulditi3`, `mulditi3`, which GCC's double-word
  multiply uses), at every level; they called `__multi3`, which MCST's
  kernel, linking no libgcc, doesn't have. Equal to lcc's results under
  MCST's qemu over 20,000 random and edge cases. 128-bit shifts by a
  variable count are inline too, at every level (`<shift_optab>ti3`,
  `e2k_expand_ti_shift`: 64-bit shifts and a mask from bit 6 of the
  count, no branch): GCC's generic expansion inlines them only where it
  optimizes for speed and called `__lshrti3` in the kernel's cold code
  (`kernel/sched/fair.c`, the last undefined symbol of vmlinux's link).
  Equal to lcc's results under MCST's qemu, v3 and v5, `-O0` to `-O3`
  and `-Os`, over 20,000 random values and counts.
- lcc's operation builtins, `__builtin_e2k_<op>` (relcc2
  spec/abi/lcc-builtins.md), 426 of lcc 1.31.05's 448, and
  `<e2kintrin.h>` with the short forms `_e2k_<op>`, the vector types, the
  alignment, byte-count and transpose helpers and the constants, written
  from the spec's description of lcc's header (whose text is not free).
  `gen-e2k-builtins.py` writes `e2k-builtins.def` and `e2kintrin-ops.h`
  from the spec's data: each builtin is the operations lcc compiles it to,
  in lcc's own trace ("pextrh a0, a1, {k2&0xff!}, ret"); its insn type
  is the port's type whose channels are the operation's on every ISA
  version it exists on and whose latency is nearest the measured one.
  One generic pattern per source count (`e2k-builtins.md`) takes the
  operation's index as its last operand, which gives the mnemonic and the
  type, so builtins schedule and bundle as the port's own operations do;
  the patterns say what each place takes (src1 a register or a 5-bit
  literal, src3 a register, ALES literals constants), which lcc's traces
  hide. Others: predicate results as 0 or 1 (`pcmp*ap`/`op`, v6), the
  80-bit `fxscalesx`, `qppackdl`, `pshufh`'s computed mask, the
  speculative and tag-clearing loads (`ldd,sm`, `qppackdl,sm`,
  `puttagd`/`puttagqp`, as lcc), `st_*_nt` (MAS 0x60 from v5), `pst_128`
  (`stmqp`). A builtin of a later ISA than the target is an error.
  Checked with relcc2 `tools/abi/builtins` `ops.c` against lcc 1.31.05
  under MCST's qemu (`toolchains/poc06/builtins-qemu.py` leaves out what
  qemu lacks, the four x86 flag operations): v3 169, v5 321, v6 376
  builtins, all equal, at `-O2` (v3 also `-O0`); `-g` changes no code.
- lcc's memory builtins with a MAS, `__builtin_loadmas_*`, `storemas_*`,
  `pstoremas_128v` with lcc's `__LCC_MAS_*` flags (speculative, volatile,
  tag clearing) and channels (checked as lcc does; a channel asked for is
  the one the insn gets, `e2k_mas_channel`), the `_be`, `_t1`, `_t2`,
  `_nta` loads and stores (two `ldd` and `qppackdl` for 16 bytes, as
  lcc), the four barriers (`wait` with the mask's six fields, as lcc
  writes it), `__builtin_e2k_get_cpu_mode ("core_mode.descr_v7")` and
  `__builtin_e2k_rrq`. relcc2's `models.c` under the community qemu
  gives lcc 1.31.05's results: 13,551 checks on v3, none failed; 18,051
  on v5 and v6, where lcc and the port fail the same 100 `pst_128_be`
  checks (the emulator's; hardware passes them). 443 of lcc's 448
  operation builtins exist now; not done: `clflush` and `prefetch` as
  builtins (the header's macros do them), and three v7 operations whose
  single ALU channel the port has no type for.
- The split-part block of v0.5 (PR 91663, below) broke MCST's kernel
  build with its `-ftrivial-auto-var-init=zero`: inlining gives an
  operand expression without a block the inlined body's outer block, a
  `.DEFERRED_INIT`'s name operand included; an inlined function's outer
  block is never pruned, the plain block of a split part inlined back is
  when unused, and `remove_unused_locals` neither marks nor clears a
  `.DEFERRED_INIT`'s operand blocks ("location references block not in
  block tree", `verify_gimple failed` in `fs/locks.c`). They are now
  cleared as a clobber's are (`clear_unused_block_pointer`, a generic
  change in `tree-ssa-live.cc`).
- A guard variable goes in its variable's COMDAT group, as l++ puts it
  (`CXX_GUARD_IN_VARIABLE_COMDAT`, a generic change in `cp/decl2.cc`,
  `get_guard`): both compilers make guards GNU_UNIQUE, and with GCC's
  own group for the guard, a link with l++'s object first defined it
  twice. relcc2's `memorycxx_abi_x.cc` links and runs in all four
  pairings and orders under MCST's qemu (0 failures); a template's
  static data member's guard is grouped the same way.
- A structure of 16 bytes aligned to 8 has TImode, not BLKmode
  (`STRUCT_MODE_WORD_ALIGN_OK`, a generic change in `stor-layout.cc`:
  under `STRICT_ALIGNMENT` a word-aligned aggregate keeps its multi-word
  integer mode and its own alignment, as on x86-64), so it can live in a
  register pair as lcc keeps it; `e2k_slow_unaligned_access` says such
  values move a word at a time (16-byte vectors from v5 still need 16).
  MCST's kernel has 16-byte unions of register halves (`e2k_pcsp_t`) in
  functions that must not touch the data stack (`check_stack`). Layouts
  are unchanged (the kernel's `struct page`/`folio` asserts hold); the
  compat suite, and `execute.exp` under MCST's qemu (17,916 passes and
  the same 62 failures without LTO; LTO the same on the 2000* tests),
  are unchanged.
- Zeros a compound literal leaves out (`MEM <char[2]> [&u + 6B] = {}`,
  from the gimplifier) are stored into a register-held object directly,
  not through a stack temporary (`store_field`, a generic change in
  `expr.cc`): the kernel's register-image unions needed the stack for it
  in `check_stack` functions.
- In an asm statement an address that is a literal alone prints after a
  space (" 0x0, sym"): MCST's kernel writes `"{std,5%[addr], ..."`, and
  lcc, which gives such an operand a register base, prints `std,5%r3,
  0x0`; the PoC's `std,50x0, prev_sclkr` was "invalid ALC50" to gas
  (`arch/e2k/kernel/sclkr.c`).
- `_Alignof`/`alignof` of a vector of N bytes, and of a structure
  holding one, say N as lcc's do (32 to 512 checked), not 16:
  `min_align_of_type` capped the answer at `BIGGEST_ALIGNMENT`, which
  stays 128 (it also sets every alloca's alignment and
  `__BIGGEST_ALIGNMENT__`); `MIN_ALIGN_OF_TYPE_LIMIT`, a generic macro in
  `stor-layout.cc`, is `MAX_OFILE_ALIGNMENT` here. Layouts were already
  lcc's, and locals get the alignment (the frame is realigned).
- PIC addresses in debug information: `e2k_delegitimize_address` turns
  the GOT register plus `sym@GOTOFF` into `sym` and a lone `sym@GOTOFF`
  into `sym` minus the GOT base, which stays `UNSPEC_GOTBASE` and prints
  as `_GLOBAL_OFFSET_TABLE_@ABS` (`TARGET_CONST_NOT_OK_FOR_DEBUG_P`,
  `TARGET_ASM_OUTPUT_ADDR_CONST_EXTRA`): MCST gas makes a bare
  `_GLOBAL_OFFSET_TABLE_` PC-relative even in data, where it fails
  ("symbol definition loop encountered at `L0'"). glibc's
  `locarchive.c` at `-O2 -g -fpie` lost 98 locations to "non-delegitimized
  UNSPEC" notes (a checking build prints them); now none, and locations
  such as `.LC58 - GOT + %r12` come out.
- The GOT address is loaded at entry only in functions that use it
  (`e2k_init_pic_reg` checks `crtl->uses_pic_offset_table`, which
  `e2k_got_reg` sets for PIC addresses and TLS GD/IE). Every function
  got the load before, PIC or not; `-O1` and up deleted it, `-O0` kept
  it, with an `R_E2K_64_PC_LIT` against `_GLOBAL_OFFSET_TABLE_`. MCST's
  kernel builds two modules at `-O0` (`jitterentropy_rng.ko`, and
  `smifb.ko` under `#pragma GCC optimize ("O0")`), and its module loader
  knows only `R_E2K_32_ABS`, `32_PC`, `64_ABS`, `64_ABS_LIT`,
  `64_CALL` and `DISP`, so they would not have loaded ("Unknown
  relocation"). `-O2` output is unchanged (21 files compared), and
  `-O0 -fPIC` keeps the load where `@GOTOFF` or `@GOT` needs it.
- Found by building GCC with itself and comparing (relcc2's
  `toolchains/poc06/dn.sh`: the native compiler, built by the cross,
  replays every compile of its own build on the machines and must give
  the cross's assembly):
  - v5's `getfz` of a scaled field counts its 16-bit descriptor as a
    literal (`e2k_field_insn_p`, `bf94db7bf47`). Counted from its
    operands, a shift and a mask both below 16 took none, and the
    scheduler put it beside two 64-bit symbol addresses, a fifth
    literal: gas "literals cannot be packed into a wide command", twice
    in libcpp's `lex.cc` built for the 8C2.
  - Insns are emitted in source order where two insn-emitting calls
    would be arguments of one call (`5c8611c427a`):
    `e2k_expand_ti_shift`'s `op (IOR, op (AND, ...), op (AND, ...))`,
    and five `force_reg` pairs. C++ leaves that order unspecified, and
    GCC built by the host's x86 compiler emitted the ANDs in the other
    order than GCC built by itself, so the two allocated registers
    differently for every variable 128-bit shift (libstdc++'s
    `floating_to_chars.cc`). The fixed cross gives exactly the native
    compiler's output. A bootstrap can't see this: all its stages are
    built by GCC. Also the 8-byte permutation's two operand loads
    (`884271b01d0`, gcc's `options-save.cc`).
  - No hard register changes from 32 bits or less to a wider mode
    (`e2k_can_change_mode_class`, `05f8cbc2657`). After allocation,
    late-combine made `(sign_extend:DI (and:SI %r0 3))` an `andd` of
    `(reg:DI %r0)`, a 64-bit read of an `adds` result under `dbl = 0`,
    whose upper half a dead speculative load had left diagnostic: the
    8C2 native cc1plus died with SIGILL `ILL_ILLOPN` in
    `cv_qualified_p` on most C++ files. The operand predicates refused
    only paradoxical subregs of pseudos. The v3 native has the same read
    and never met a diagnostic half. 0.22% more wide instructions over
    516 compiles, loads and stores unchanged.
- libquadmath, now built and shipped with the cross toolchains (relcc2
  docs/poc-roadmap.md, 0.5-9):
  - fixincludes' `glibc_e2k_femode` (`8d0c175b45b`). MCST glibc's E2K
    `bits/fenv.h` defines `femode_t` under `IEC_60559_BFP_EXT`, which
    C23 doesn't enable, while `fenv.h` declares `fegetmode` under
    `IEC_60559_BFP_EXT_C2X`, so `<fenv.h>` failed under GCC's default
    `-std=gnu23` without `_GNU_SOURCE` (libquadmath's `fmaq.c` among
    others). The rule rewrites the guard to the `_C2X` one, on E2K only
    and not where the header already names it: on lcc's `fs/usr/include`
    and on the PoC-built OpenE2K glibc it fixes that file alone. The
    cross sysroots' `sed` of the header is no longer needed, and on the
    machines a native compiler's `install-tools/mkheaders` can apply the
    rule to `/usr/include` (not tried yet). `fixincl.x`
    is edited by hand to what `fixincl.tpl` generates (no autogen here).
  - libquadmath is built with `-mno-spec-fp` (`47795336402`, its
    `configure.ac`), as glibc's libm. A program clears the flags before
    calling it to see what it raised, and a speculative FP operation
    that would raise a cleared flag traps (SIGILL `ILL_ILLOPN`) where
    its result is used: `sinq`, `cosq`, `tanq`, the Bessel functions
    and the complex functions on them died so (18 tests).
  - A zero 16-byte vector is stored from a register (`706679b3acb`):
    `e2k_expand_move_v16` let zero through to the generic move,
    `(set (mem:V2DI) (const_vector 0))`, which no pattern takes. Only
    PIC code met it (otherwise the constant goes to the pool first):
    libquadmath's `printf_fp.c` didn't build for the 8C2 or v6.
    `gcc.c-torture/compile/e2k-v16-zero-pic.c`. 516 compiles of GCC's
    own 8C2 build give the same assembly before and after.
  - Checked with relcc2's `tools/quadmath`, the `0.5+41` crosses' own
    libraries on the 4C (v3) and the 8C2 (8C2-tuned): every exported
    function and soft-fp's arithmetic, comparisons and conversions in
    the four rounding modes, 445,548 calls on each, against x86's
    libquadmath from the same source. Every value matches, apart from two
    conventions (`signbitq`'s nonzero value, libc's `FP_ILOGB0` and
    `FP_ILOGBNAN`); 8 `cacosq` calls with a signalling NaN raise no
    invalid where x86's do (x86 GCC classifies both parts before the
    test, the PoC skips the second). lcc's system libquadmath dies with
    SIGILL in 37 of the tests after `feclearexcept` and raises no
    inexact, overflow or underflow.
- A prepare stays out of a predicated arm where the way that skips the
  arm still reads its CTPR (`e2k_ifcvt_modify_insn`, `efd6f1c4975`): a
  `disp` runs whatever its predicate. jump2's head merging had put the
  two arms' prepares of `f` before the test in `if (bad) { f (...);
  abort (); } f (...)`, the arm's `disp` of `abort` ran on the good
  path too, and the `f` after the arm called `abort` (libffi's
  `test-callback.c`, 11 tests at `-O2`; every 0.5 build).
  `gcc.c-torture/execute/e2k-predcall-2.c`. Of 516 compiles of GCC's
  own build, 104 change for v3 (0.2% fewer wide instructions) and 104
  for the 8C2 (0.15% fewer, 0.06% more loads and stores). Keeping the
  allowed prepares unconditional in the RTL too would change 268; not
  done.
- libffi (MCST's 3.3, relcc2 `OpenE2K/libffi`) builds unchanged with
  `0.5+43`; its testsuite on the 4C passes 1,550 tests whether the test
  programs load the PoC's libffi or lcc's system one, and with lcc
  compiling the tests against the PoC's. Left: `va_struct2.c` and
  `va_struct3.c` fail "excess errors" only for GCC's newer unused
  parameter warning (x86 GCC gives it too), and lcc rejects
  `complex_int.c`'s `_Complex int`.
- An asm uses and clobbers every global register its template names,
  and uses every fixed global register among its clobbers
  (`e2k_asm_greg_clobbers` in `e2k_md_asm_adjust`, `89ef46924a9`): lcc
  reads templates, GCC only operands and clobbers, and the first boots
  of MCST's kernel built by the PoC broke on it three ways (relcc2
  findings A41): `ASM_RESTORE_GREG_V5` restores the user's `%g16`-`%g31`
  undeclared, and GCC computed addresses from `%g17` (`current`) after
  it, so the return to user trapped for ever; `barrier()`'s clobbers of
  `%g18`-`%g20` made a store just before it dead (`preempt |=
  NEED_RESCHED` deleted); `WRITE_UACCESS_REGS_CACHED` reads `%g20` and
  `%g21` and names them as clobbers, and `current_mmu_context = ctx` in
  `handle_sys_call` was deleted. The template reaches the hook through
  `md_asm_adjust_template` and `md_asm_adjust_basic_p` (target.h, set
  in cfgexpand.cc around the call). Reads of a global register
  variable after such an asm may still be merged with earlier ones
  (GIMPLE doesn't see the asm writing the variable); only an output
  operand stops that. `gcc.c-torture/execute/e2k-greg-asm-1.c` fails
  at `-O1`-`-Os` without it.
- combine's `subst` skips the uses an asm's `PARALLEL` may hold after
  its sets (`24e56a34219`): it took `SET_DEST` of each, which RTL
  checking rejects for a USE (seven kernel files ICEd after the change
  above; only aarch64's SME state added asm uses before).
- `-Wbitfield-arith` (C front end, off by default, `cef7fc29f8c`):
  warns where arithmetic on a bit-field of 33-63 bits declared with a
  64-bit type wraps at the field's width and the result is widened.
  GCC's C gives such a field a type of its width; lcc (EDG), clang and
  C++ compute in the declared type (relcc2 findings A42). MCST's
  `get_cr0_ip` (`cr0.Ip << 3`, 45 bits) lost the IP's top bits, so
  `is_from_C1_wait_trap` never matched and an idle CPU never left its
  wait. The warning lists such sites in MCST's code; the PoC keeps C's
  rule. `gcc.dg/Wbitfield-arith-1.c`.
- Operations that must share one wide instruction keep it when the
  bundler is off (`-fno-schedule-insns2`, `-mno-bundle`): the `landp`
  chains, whose `@p0`-`@p6` hold a value only within one, a hardware
  loop's `alc` (and `abn`, `abp`) with its `ct`, and a DAM check with its
  `rbranch` print `%<` ... `%>`, as the GOT pair did (relcc2 findings
  P117). Split, gas rejected `gcc.dg/torture/pr107115.c` ("undefined @p0
  used as an incoming parameter for CLP0"), and a `ct ? %NOT_LOOP_END`
  of its own read the count after `alc` had lowered it, so the loop ran
  one iteration short without a word (`gcc.dg/unroll-and-jam.c`'s `init`
  with `-mno-bundle`). Found by the native `check-gcc` of 0.5+52 on the
  8C2; bundled output is unchanged.
- No control speculation of an insn that may throw
  (`-fnon-call-exceptions`; `e2k_spec_kind`): it ends its block on an EH
  edge, and its exception belongs where the program has it.
  `g++.dg/opt/pr100254.C` and `g++.dg/ipa/pr80205.C` (`-std=gnu++98`)
  ICEd in `advance_target_bb` (sched-ebb.cc:699): a vtable load, the
  last insn of its block, rose above the jump that ended the block
  before.
- Dependence cliques of loops versioned for aliasing (`e2k-av.cc`; relcc2
  findings P118) hold across the iterations of one run of their loop,
  and nowhere else:
  - never clique 1 (`e2k_av_new_clique`): points-to analysis gives
    that one to the function's own `restrict` pointers, and
    tree-data-ref.cc and `e2k_ms_may_alias` believe it across the
    iterations of every loop. The hash-chain mark stays as it was: one
    base for all, so it claims nothing;
  - once the late instance is done (`e2k_av_check_cliques`): a clique
    one loop still owns stays as it is, on the iterations cunroll
    peeled off that loop too (NPB MG's `resid`). One that no loop owns
    any more (cunroll unrolled its loop into the one around it) leaves
    `av_cliques` and its references inside loops. Of several copies of
    its loop, each further one gets a clique of its own, and the
    references outside the copies lose theirs.
  `gcc.dg/unroll-and-jam.c`'s first loop, IPA-CP'd to constant bounds,
  had its jammed inner loop told apart (rows `i`, `i+1`, `i+2`) and
  then unrolled into the outer loop. There each iteration is another
  run, and the outer loop's pipeliner overlapped the row-`i+2` stores
  with the next iteration's row-`i` loads: a wrong checksum at `-O3` on
  the 4C and 8C2. The cost, v3 code at `-O3` on the 8C2: NPB LU class A
  83.0 s before, 86.2 s now (+3.8%, both verified). Its `ssor` loops 24
  and 47 were versioned, then unrolled into their outer loop and
  pipelined there on the stale clique, and the late instance can't
  version that loop ("reference (*_249)[j][k][m]"). MG (4.50 s, 4.49 s),
  CoreMark (6,950 iterations/s) and LAME (7.15 s, the same MP3) don't
  change.
- The pipeliner's II search (`e2k_ms_pipeline`) went round for ever
  once its search in one stage beside the overlapped one (P53, since
  v0.4) ended with neither fitting: the next line began that search
  again. LAME 3.100's `mpglib/layer3.c` at `-O3` hung cc1 in
  `hip_init_tables_layer3`: 542 insns, MII 165 for an iteration of 91
  cycles, so no II was worth trying in one stage. The search now starts
  at most once a loop, and that loop is left unpipelined. The
  assembly doesn't change anywhere else: 5,625 compiles
  (gcc.c-torture/execute at `-O2` and `-O3`, gcc.dg/vect, benchmark
  sets 1 and 2 at `-O2` and `-O3`).

## v0.5 (2026-10-22)

### Debug information

- No DWARF numbers but `%r0`-`%r63` (0-63) and `%b[0..63]` (64-127),
  the spec's and all MCST's gdb maps: a variable in a global or a
  predicate gets no location there (`IGNORED_DWARF_REGNUM`; dwarf2out's
  based_loc_descr and multiple_reg_loc_descriptor drop such a register
  too). The globals were 128-159, and gdb failed a whole command on one
  ("Unable to access DWARF register number 128": 126 of guality's
  3,035 checks on the 4C).
- The prologue's `getsp` carries `REG_FRAME_RELATED_EXPR` (`%r8 =
  %r8 - size`) instead of `REG_CFA_DEF_CFA`: var-tracking reads stack
  adjustments only from that note or the pattern, so it took `%r8` for
  the incoming stack pointer and put every stack slot the frame size
  too far from the frame base (guality's pr43077-1.c read 0 for `b` and
  `c` at every level from -O1). The CFI is the same.
- Variable location notes inside a wide instruction move to where it
  ends (`e2k_bundle_var_notes`, after var-tracking): inside the braces
  their labels took the instruction's start address, before any of its
  operations has run.
- 64-bit DWARF by default (`-gdwarf32` for GCC's), as lcc: its 1.28
  changelog deprecated `--dwarf2-64bit` as on by default. With 32-bit
  offsets (`R_E2K_32_ABS` in `.debug_info`, `.debug_line`,
  `.debug_aranges`) a linked program's debug sections can't pass 4 GiB.
- No `.debug_frame` (`-fno-dwarf2-cfi-asm` unless a `.eh_frame` is
  wanted): with `UI_NONE` GCC still had gas build one from `.cfi`
  directives, CFI no gdb of MCST's reads; lcc writes none.
- A pipelined loop's kernel keeps its statement markers (at its start)
  and turns its debug binds into resets: deleting them all let a
  variable the loop sets keep its value from before the loop beyond it
  under `-fvar-tracking-assignments` ("best = -1" after a search loop),
  and left the loop's lines without a breakable row.
- A lexical block whose end falls inside a wide instruction ends where
  the instruction ends (`e2k_bundle_block_notes`, from
  `TARGET_ASM_FUNCTION_PROLOGUE`, after final rebuilt the notes):
  otherwise it ended before its own last operation and gdb found none
  of its variables there.
- `-fvar-tracking-assignments` stays on (GCC's default; this port had
  turned it off since its first commit): guality on the 4C passes 2,159
  of 3,035 checks instead of 1,364 (`-O2` 246 instead of 132 of about
  370), with fewer wrong values (23 instead of 40); `-fcompare-debug`
  on sets 2 and 3's sources and 7-Zip finds no code difference.
- Call-site parameters name their register as the callee sees it
  (`DWARF_CALL_SITE_INCOMING_REGNO`, dwarf2out: `%b[i]` as `%r<i>`), the
  number the callee's `DW_OP_entry_value` uses and gdb matches.
- A statement that begins inside a wide instruction begins where it
  ends (`e2k_bundle_stmt_notes`; markers give the line table its
  `is_stmt` rows): a breakpoint on its line then sees what the earlier
  lines did. Guality with VTA: 2,511 of 3,035 checks instead of 2,159.
- Calls name their callee for the debug information: the call's MEM
  keeps its `MEM_EXPR` (`DW_AT_call_origin`), and
  `TARGET_DELEGITIMIZE_ADDRESS` turns a `disp` of a symbol back into it.
  With call-site parameters numbered as the callee sees them, gdb finds
  entry values ("n=n@entry=8" instead of `<optimized out>`).
- Debug insns stay in their blocks across `schedule_ebbs`
  (`e2k_record_debug_blocks`, `e2k_restore_debug_blocks`): one at a
  block's head depends on nothing before it and rose above the jump into
  the block before, so a line's breakpoint and a variable's binding took
  effect on the other path too (pr55665.C read a static as 0 before its
  initialization).
- An operation of an inlined call that runs under a statement outside
  that call takes the innermost scope both share
  (`e2k_bundle_scopes`): a hoisted invariant or a speculated load gave
  the inlined call the caller's wide instructions, and gdb showed that
  inlined frame at the caller's lines (25 ranges for a devirtualized
  `Circle::area` over its caller's loop). Lexical blocks keep their
  operations.
- Each further copy of a statement (unrolling, tail duplication, loop
  versions) gets a lexical block of its own (`e2k_bundle_dup_blocks`),
  holding an artificial label `copy` with an address, so that gdb, which
  keeps one breakpoint per line and block, stops in every copy, not
  only the one placed first. A C++ probe's loop unrolled by 4 now has 18
  locations for one line instead of 1; C++ guality 172 of 204 checks
  instead of 170 (pr55665.C at -O2 and -O3), C unchanged, and `-g`
  doesn't change the code (sets 1-3).
- A statement that begins before a jump, call or return in its wide
  instruction begins where the instruction starts, not past it:
  vla-1.c's "return a[0]", begun in its function's last instruction,
  took a breakpoint in the next function.
- A statement that would leave its lexical block past its wide
  instruction (the block's operations all in it) begins where the
  instruction starts, with the variable locations before it that hold
  there (`e2k_bundle_debug_notes`): pr43479.c's i was "No symbol" at
  its line.
- A variable addressed through a pointer register (aligned beyond the
  stack) is described by location notes through the register its
  accesses use, from the pointer's set to the register's next one
  (`e2k_pointer_decl_locations`): its DECL_RTL, which holds for the
  whole function, read a stale %r0 after regrename moved the pointer,
  and an unrelated value once the register was reused (pr36728.c's y).
- var-tracking sees every %b[N] clobbered after a setbn and where a
  pipelined kernel's jump goes (`e2k_setbn_clobbers`, removed after it):
  it took a register's value from before the loop for the one after it.
- A pipelined loop's exit gets the last bind of each variable its body
  sets, where it holds after the loop (`e2k_ms_exit_binds`): a sum
  returned after its loop was unknown at the return.
- No discriminators in the line table (`DWARF2_LINE_DISCRIMINATORS`), as
  lcc: gdb drops a statement's row after a row of its line with a
  non-zero discriminator, and pr43141.c's line 8 broke in main.
- Each function's first statement carries `DW_LNS_set_prologue_end`
  (`DWARF2_PROLOGUE_END_STMT`). gdb uses it for a breakpoint on a
  function only in units without location lists (`-O0`): in optimized
  ones it breaks at the entry, and `step` into a function always stops
  past every leading wide instruction with getsp, setwd or setbn
  (`e2k_skip_prologue`; relcc2 docs/mcst-coordination.md, M4).
- No modulo scheduling at `-Og` (`-mpipeline` turns it on): a kernel
  runs several iterations at once.
- At `-Og` a source line's operations never share a wide instruction
  with another line's and stay after the line before
  (`e2k_og_stmt_deps`, `e2k_adjust_cost`): a line's breakpoint sees the
  lines before it done and none of its own operations run. 21% more
  wide instructions at `-Og` on sets 1-3.
- A statement whose wide instruction changes nothing visible before its
  marker and something after it begins where the instruction starts.
- A pipelined loop's start shows the variables of one iteration as it
  starts, where their values from the iteration before are still in
  registers (`e2k_ms_kernel_binds`): inside the loop every variable was
  unknown.
- At `-O0` and `-Og` the window registers come before %g16-%g31 in
  the allocation order, and IRA keeps to it
  (`e2k_adjust_reg_alloc_order`, `HONOR_REG_ALLOC_ORDER`): it charged
  them for a save the window makes unnecessary and took the globals,
  which no DWARF number names (pr36728.c's pointer at `-O0`). Other
  levels unchanged.
- A pipelined loop's markers, all at the kernel's start, end with the
  body's first statement: gdb shows the kernel as that line, and
  `next` from the loop's header stops there once before leaving the
  loop.
- No renaming for speculation at `-Og` (`-mspec-rename` turns it on):
  it bought copies (1.8% more wide instructions on sets 1-3) and put
  values in %g16-%g31.
- A part ipa-split took out of a function and inlining put back gets a
  plain lexical block, not a second inlined instance of the function
  (`tree-inline.cc`, PR 91663): gdb stopped twice per call on the
  function or its first line (coreutils' `rm/r-root`).
- Debug binds decide no frame, window register, pipelining or
  predicate choice, and a function's `.LFB`/`.LFE` labels stay out of
  gas's code placement (native-build's fixes, cherry-picked as
  `ef0077c1085`, `fc770beedc3`, `fcba8257cc1`): GCC's 730 C++ sources
  and 3,314 C torture and libiberty files give the same stripped
  objects with `-g` and without (2026-10-16, at `17d629076f5`).

Guality (gcc.dg's checks of a variable at a breakpoint) on the 4C with
ALT's gdb 15.2, passing checks (the rows from 2026-10-16 counted by
debuginfo/gqcat.py after its fix for results that run into gdb's last
line: 3,042 checks and 15 wrong values where it read 3,041 and 14):

| | -O0 | -Og | -O1 | -O2 | -O3 -g | -Os | all | wrong values |
|---|---|---|---|---|---|---|---|---|
| before (`fbc2725b93a`) | 385/397 | 186/371 | 165/376 | 128/370 | 127/371 | 128/371 | 1,337/3,035 | 50 |
| 2026-10-16 (`31368195a91`) | 385/397 | 327/372 | 329/376 | 317/372 | 318/372 | 311/372 | 2,628/3,042 | 15 |
| now | 397/397 | 355/372 | 329/376 | 317/372 | 318/372 | 311/372 | 2,668/3,042 | 15 |
| lcc 1.29.16 | 364/397 | 340/372 | 32/374 | 32/364 | 32/368 | 32/369 | 896/3,021 | 98 |

c-c++-common's 47 checks: 46 pass, in C and in C++ (42 before the
statement fixes and the line table of 2026-10-16). Against x86-64 (GCC
16 and gdb 18 on the host, the same tests): 189 checks fail only here
(242 before 2026-10-16), none at -O0 and 4 at -Og. Most are values in
a global register, which no DWARF number names (relcc2
docs/mcst-coordination.md, M1): at -O0 and -Og the window registers
now come first, but at -O1 and above the globals stay, as they keep
the window small (with -ffixed-g16 ... -ffixed-g31 those checks
pass). Others follow from the machine:
a result returns in %r0, the first argument's register, so a dead
parameter lives on only as an entry value, which gdb resolves for an
indirect call only with DW_AT_call_target, which a call through a
%ctpr can't have (pr41353-1.c, 21 checks); a predicated call stops
gdb whatever its predicate (pr54519-1.c at -Os); an operation hoisted
above its statement's branch has run at the statement's breakpoint
(loop-1.c).

lcc ran the same tests through a wrapper (it lacks some diagnostic
options, warns about `noipa`, and rejects guality.h's `"X"` asm
constraints, which became `"g"`); it gives optimized code names and
types only, and one line row per function (relcc2 findings A30). A
60-line probe under gdb: lcc's `break` on a line in a loop lands in
the next function and prints every variable `<optimized out>`; this
compiler stops in the function, shows `p@entry=...`, `n=n@entry=8`.

C++ (g++.dg and c-c++-common guality as C++; this compiler with
build-gcc-claude's libstdc++, linked statically): 172 of 204 checks
pass, lcc 1.29.16's l++ 36 (10 of 28 at -O0: it can't compile
decomp1.C's structured bindings). The C++ checks left fail on x86 too
with GCC 16 and gdb 18 (pr55541.C: no is_stmt row for `}`; pr82630.C is
built without -g; pr86687.C's value is optimized out there). A C++
probe (classes, virtual calls, a template, a lambda, exceptions) shows
members, `*this`, the dynamic type with `set print object on`, `catch
throw`, `finish`'s returned double and `n@entry` values. MCST's gdb
15.2 (ALT's 15.2-alt1.1, OS Elbrus's 15.2-29.023 on the 8C2) aborts on
`p` of a lambda that captures by reference (an internal error in
`coerce_pieced_ref`, on GCC's valid `DW_OP_implicit_pointer` pieces):
gdb PR 30693, fixed upstream by 958d06262a7a (2026-05-07), which
applies to MCST's sources and removes it (checked on a core with a
cross-built 15.2-29.023). ALT rebuilt its gdb with it: 15.2-alt1.2,
on the 4C since 2026-10-15, prints the lambda.

Left open: at -O1 and above, a line whose first wide instruction also
changes what the line before set breaks after that instruction, past
some of its own operations (at -Og lines never share one); inside a
pipelined loop a variable shows only where its value from the
iteration before is still in a register at the kernel's start; a
predicated statement's breakpoint stops whatever its predicate (an
`op_index` numbering and gdb's help would be needed: relcc2
docs/mcst-coordination.md, M3); at -O1 and above values in globals
have no location (M1); `step` into a function stops past its first
wide instructions, sometimes mid-line, as MCST's gdb skips every
leading one with setwd or getsp whatever the line table says (M4).

## v0.4 (2026-10-14)

v0.3 plus nine days of work driven by broader benchmarks: set 2 (NPB,
PolyBench at program sizes, Lua, SQLite's speedtest1, LAME) and set 3
(all 30 PolyBench kernels), run on the 4C, the 8C2 and the 2C3 against
lcc 1.29.16 built for each CPU. In short:

- Branchy code: chains of branches merged, conditional returns and
  latches, small joins and computed-goto dispatch blocks copied into
  their predecessors, if-conversion of loads, stores, FP arms and calls,
  predicate logic of up to four conditions, renaming for speculation
  over whole superblocks.
- Pipelining: while loops with merged exits and rotating predicates,
  array prefetch and AAU stores in every counted loop they fit (as lcc),
  rings of up to 63 pairs, loops of up to 256 operations, iterative
  modulo scheduling, loads timed for L2 in loops that run long, lock
  loads beside array prefetch, cheaper ways into and out of pipelined
  loops.
- Aliasing: loops and straight-line blocks versioned on overlap tests
  (NPB BT's 5x5 routines as lcc does them), dependence cliques that
  survive vectorization.
- Vectors: 64-bit vectors on every version; 16-byte vectors on v5 and
  later, on by default, with a cost model of the pipeliner's II.
- Per-CPU code: `-mtune=elbrus-4c`, `-8c2`, `-2c3`, `-16c`, `-12c` with
  v6's latencies, and what v4-v6 add (fused multiply-add on v6, `%lsr1`,
  inline 16-byte atomics, `__int128` add and subtract, `fscale`).
- ABI and runtime, from the relcc2 spec audit: atomics' nops and
  release stores as lcc's, the stack protector's guard, `va_list`,
  `nfx` for long double, temporaries only in `%g16`-`%g31`, system
  calls in inline asm, `__clear_cache`, `crtfastmath.o`.
- e2k.cc split into 16 files; builds on GCC master of 2026-10-13.

The entries below are in the order they were made.

### Results

Speed against lcc 1.29.16 -O3, both built for the CPU (this back end
at -O2 with `-mtune=elbrus-4c`, `-8c2` or `-2c3`; lcc from its
`e2k-v3.4c`, `e2k-v5.8c2` and `e2k-v6.2c3` trees), as lcc's time over
ours (above 1: faster than lcc):

| | 4C (v3) | 8C2 (v5) | 2C3 (v6) |
|---|---|---|---|
| CoreMark | 1.51 (3,473 it/s; lcc 2,307) | not rerun | 1.40 (7,397; 5,267) |
| Linpack (linpackc.c, size 200) | 1.15 (671 MFLOPS; 585) | not rerun | 0.80 (1,599; 1,993) |
| zlib `-9`, `-d` | 1.28, 0.84 | | 1.01, 0.65 |
| bzip2 `-9`, `-d` | 1.07, 0.95 | | 1.07, 0.99 |
| xz `-6`, `-d` | 0.92, 0.95 | | 0.87, 0.78 |
| Set 2: NPB, PolyBench, Lua, SQLite, LAME | NPB 1.16, Lua 1.00, SQLite 0.90, LAME 0.96 | 1.03: 1.04, 1.06, 1.01, 0.91, 1.03 | 1.04: 1.04, 1.07, 1.02, 0.91, 0.97 |
| Set 3: PolyBench, 30 kernels (those over 0.05 s) | | 1.12 | 1.12 |

The compressors run on an 11 MB tar (relcc2's `speed/ctime.sh`, best
of three); decompression takes 0.04 to 0.3 s. The 4C's PolyBench
timings drift up to twice (huge pages that fall back), so it has no
PolyBench numbers here. A native GCC bootstrap occupied the 8C2 during
this round: its numbers are the quiet runs of 2026-10-13, with the
back end before the GCC merge, which compiles PolyBench to the same
code (set 2's NPB, Lua and LAME differ in the 19 files of the
predicated-call guard below). The largest gaps: NPB FT 0.79 (2C3) to
0.83 (8C2), LU 0.81 to 0.87, EP 0.92, SQLite's speedtest1 0.90 to
0.91, PolyBench's adi 0.83 (2C3) and 0.93 (8C2), Linpack on the 2C3.

Since v0.3 on the 4C (v0.3 ran generic v3 code, v0.4 code for the 4C;
lcc's times within 3%, xz's 9% shorter now): CoreMark 2,879 ->
3,473 it/s, Linpack 597 -> 671 MFLOPS, zlib `-9` 4.39 -> 1.75 s,
bzip2 `-9` 5.0 -> 3.51 s, xz `-6` 21.6 -> 13.9 s.

Tests:

| Suite | Result |
|---|---|
| C torture (execute), -O2: v3 code on the 4C, v5 on the 8C2, v6 on the 2C3 | 1,641 of 1,641 on each |
| gcc.dg/vect, -O3, v5 code (16-byte vectors) on the 8C2 | 954 of 954 runnable tests pass (77 more ask for x86 or Arm options) |
| ABI compat suite, lcc<->gcc, 1,931 tests x 3 pairs | 0 unexpected on the 4C (v3), and on the 8C2 (v5) with the compiler before the last four fixes |
| Real programs' own tests: zlib, bzip2, xz, zstd, GMP, pcre2, expat, 7-Zip | pass with v3 code on the 4C and v5 code on the 8C2 (GMP 177 of 178: t-addaddmul skips); pcre2's test 14 died once with SIGILL on the 8C2 in 20 runs (under a parallel bootstrap; see "Next") |
| GCC's C, C++ and libstdc++ suites | not run since v0.3 (2026-10-04/05) |

### Changes

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
- Fixed (SQLite's speedtest1 built with -mno-control-spec: SIGSEGV at
  0x18 in createCollation): the scheduler may put a fall-through
  block's first operations in its jump's cycle, and the bundler puts
  them in the jump's wide instruction, where they run when it is taken
  too; e2k_spec_mark gives them ",sm", but only with control
  speculation. Without it nothing now shares a jump's instruction
  (pColl->xCmp was loaded with the jump that skips it for a null pColl).
  Default code is unchanged.
- Clocked prologues of pipelined loops get a list schedule of their own
  (e2k_ms_list_prologue) instead of the modulo schedule's times, which
  keep its slack: a copy into the ring at its value's time in a
  virtual earlier iteration, the first load three cycles after it.
  Each item goes into the first cycle where its operands are there (at
  the pipeliner's latencies, never more than the modulo schedule gave)
  and the DFA takes it, a register's reads before a write of it and
  its writes in order; the kernel then starts as much sooner as every
  value it reads from the prologue allows, counting a cluster crossing
  on each of those edges (the kernel's channels keep recurrences in one
  cluster, the prologue's need not, and a cycle late costs a 4-cycle
  stall: without that count zlib -9 ran 1.1% slower on the 8C2).
  -mno-ms-list-prologue keeps the old times. Gains are a cycle or a few
  per way in: 1 in four of inflate_fast's loops, 4 in one of deflate's,
  5-6 in three of Linpack's, none in xz's match finder (its while loops'
  prologues are one serial iteration). Only with v6 timing: on the 2C3
  CoreMark 7,270 -> 7,310 it/s (+0.5%) and zlib -9 0.830 -> 0.825 s,
  the rest unchanged; on the 8C2 it made zlib -9 1.1% slower (and
  counting the crossing didn't help), so v3 and v5 code keep the
  modulo times. Torture passes on the 2C3, and with it on (before it
  was gated) on the 4C; the loop and Linpack checks pass on all
  three.
- A table jump's (and a computed goto's) movtd is an insn of its own,
  as a call's is, so that the scheduler sees its 9 cycles to the ct and
  can hoist it: they printed as movtd; ct back to back, the stall not
  modelled. CoreMark unchanged on the 8C2 and the 2C3. Lowering
  switches of fewer than 8 cases to compare ladders
  (TARGET_CASE_VALUES_THRESHOLD, for xz's 5-case rc_encode) made xz -6
  0.3-0.6% faster and CoreMark 6-7% slower on both: not kept.
- An array prefetch area's disp is never negative: the hardware adds it
  to the base zero-extended (relcc2 findings I41: disp=-64 reads 2^32 -
  64 bytes on, on the 4C, the 8C2 and the 2C3 alike), and an area whose
  stream starts below its induction register (a negative offset, or
  stages that start it earlier) read diagnostic values: gcc.dg/vect's
  vect-outer-3c died with SIGILL on the 4C once a longer II let it
  pipeline. A descriptor whose areas would start below its base now
  gets a base that much lower (an addd into the temporary before
  aaurwd), and every disp is 0 or more; lcc writes disp=0 and starts its
  areas through %aaind.
- Array prefetch also for loads that step backwards (PolyBench's
  durbin, "sum += r[k-i-1] * y[i]"), from v5 on, with no store of the
  loop writing the array, and the increment written by aaurwd there, as
  lcc does (%aaincr is 64 bits from v5). Backward areas read right on
  the 8C2 and the 2C3 (the loop tests under SIGALRM); on the 4C an
  area may not go below its base (findings I41: diagnostic values,
  SIGILL in gcc.dg/vect's vect-15-big-array, slp-47 and pr96783-2),
  which lcc avoids by putting the base at the last element read, so v3
  code doesn't. durbin on the 8C2: 3.6 -> 1.9 s (lcc 1.66).
- Loop versioning for aliasing also with references the loop doesn't
  step through, each such element a group of its own, checked against
  the rest of its array as well, where GCC's dependence test can't tell
  (it doesn't see "k < j"): PolyBench's 2mm "tmp[i][j] += alpha *
  A[i][k] * B[k][j]" and cholesky "A[i][j] -= A[i][k] * A[j][k]" get a
  copy for disjoint data in which LIM keeps the element in a register,
  stored after the loop, as lcc's disjoint copy does. The loop then
  pipelines at II 4 (the FP add) instead of storing every iteration
  for the next iteration's loads to wait on (2mm's 16-cycle recurrence
  through memory). 8C2, with array prefetch (below): 2mm 6.3 -> 1.2 s
  (lcc 1.19), cholesky 2.2 -> 0.48 s (lcc 0.47).
- A modulo schedule whose ring is too big (or whose prologue can't be
  ordered) at one II tries the next while the kernel stays clearly
  shorter than one iteration, rather than giving up, which with array
  prefetch meant trying again without it: fdtd-2d's first two loops, 25
  stages at II 1 needing 64 names, now run at II 2 with their loads
  through array prefetch, the third at II 3. With the next entry,
  fdtd-2d on the 8C2 47.7 -> 3.2 s (lcc 2.44).
- Array prefetch in every counted loop it fits, as lcc (spec/isa/
  apb.md, "How lcc uses APB"), unless the movas don't shorten the kernel
  and the loop is known to be short: the profile, or else the count the
  doloop pass knew (its constant count or bound: an operand of the
  doloop_end patterns, which e2k_hwloop_opt keeps by the loop end's UID;
  RTL loops lose their bounds after the loop passes, and loops their
  start labels), says fewer than 256 iterations. Before, a loop without
  a profile got it only where it shortened the kernel, and a stream from
  memory stalled on every cache line (jacobi-2d's loops: 21.8 cycles an
  iteration for 2.0 modelled). -mno-apb-unknown-count takes loops of
  unknown count to be short. 8C2: PolyBench jacobi-2d 24.8 -> 2.7 s
  (lcc 2.04), fdtd-2d (with the entry above) 47.7 -> 3.2 s (2.44),
  gramschmidt 5.5 -> 3.4 s (2.80), deriche 2.9 -> 2.3 s (1.20); set 2
  from 0.53 to 0.74 of lcc in all (NPB 0.54 -> 0.62, CG 0.45 -> 0.87;
  PolyBench 0.25 -> 0.68, with the entries above). The cost, where data
  stays in cache: Linpack 2.8% slower on the 8C2 (1,274 -> 1,238 K) and
  1.9% on the 2C3 (its loops run 1-200 times over a 320 KB matrix),
  CoreMark 0.35% and 0.07%, xz -d perhaps 2.5% on the 8C2, the rest of
  set 1 unchanged; with -mno-apb-unknown-count set 1 is as before and
  NPB 0.56, PolyBench 0.36.
- FP divides in pipelined loops, speculated as lcc does in its own: the
  divider in ALC5 takes one every 2 cycles (timing.md, "Divider": 1
  cycle apart stalls 4), so II is at least 2 per divide and no two
  divides go in adjacent rows (a row's DFA state sees only its own
  cycle; e2k_ms_div_clash). Square roots stay out (fsqrts conflicts 5
  cycles apart, fsqrttd reads two values). Loops such as gramschmidt's
  "Q[i][k] = A[i][k] / R[k][k]" and the initialization loops of
  seidel-2d and cholesky now pipeline (cholesky's at II 2); PolyBench's
  timed kernels keep their divides outside their inner loops, so their
  times don't change. Torture, gcc.dg/vect and the loop tests (a divide
  kernel among them) pass on all three machines.
- The modulo scheduler takes loops of up to 256 operations (was 64:
  a 64-bit reach mask, now an sbitmap per node) at an II up to 48, and
  says when a body is too big. NPB SP's flux loops have 140 (the
  xi-direction one, 181 cycles an iteration unpipelined on the 8C2);
  alone this changes nothing there, their values overflow the ring
  (next entry).
- Values of a pipelined loop that live no longer than its II, and are
  neither carried nor read after the loop, get registers of their own
  outside the rotating ring (-mms-fixed-regs, on): the next iteration's
  def issues no earlier than the last use, so no rotation is needed. A
  register is shared by values whose lifetimes, modulo II, don't meet;
  candidates are %g16-%g31 and the window registers the loop leaves
  free (not live around it, not an invariant it reads), those the
  function uses already first. Not in while loops or with DAM, whose
  exits and compensation read earlier iterations' instances. NPB SP's
  xi-direction flux loop, 135 values for the ring's 62 names at any II,
  now pipelines at II 26 (25 with the array prefetch entry below):
  181 -> 57 cycles an iteration on the 8C2, SP 26.9 -> 25.7 s.
- A %b[0..7] register a loop only sets and reads within an iteration
  needs no move before the pipeliner (e2k_ms_move_b): its value is
  renamed anyway. Under the register pressure of NPB's solvers there
  was often no free register to move it to, and the loop wasn't
  pipelined ("no free register for a %b[] value": 12 loops in SP, 13
  in LU, 18 in BT before; invariants live into the loop still need one).
- Array prefetch for up to 32 loads of a loop through up to 32
  descriptors (was 16 and 8; the hardware has 32 %aad, 32 areas a half,
  spec/isa/apb.md). Many areas share the buffer, each getting less of
  it, but at a large II even 64 bytes run far enough ahead. NPB SP's
  xi-direction fluxes (38 loads) II 26 -> 25, more of them prefetched.
  With the three entries above, NPB on the 8C2 0.62 -> 0.64 of lcc (LU
  16.5 -> 14.2 s, BT 12.5 -> 11.8, SP 26.9 -> 25.6), on the 2C3 0.56 ->
  0.58; set 1 and the rest of set 2 unchanged on both.
- The pipeliner's dump prints the insn reading a predicate from outside
  the iteration, and tells "%ctpr2 ends the loop" from "%ctpr2 live
  around the loop" when it refuses array prefetch. Most of the first in
  NPB are the empty paths of loop nests (the outer loop going around an
  inner one that runs no times); the second comes from a prepared
  branch of an outer loop that re-enters the inner loop's header
  (e2k_prepare_loop_branches sees one loop of two latches).
- The array prefetch setup after rwd %lsr goes after any copy
  e2k_ms_move_b put there into a register it reads: a %b[] value moved
  into the register that had held the count (dead after rwd) was read by
  the setup before the copy, as the count, and the areas started at a
  wrong address (NPB SP's eta-direction fluxes, once pipelined: SIGILL on
  a diagnostic value stored). Then the temporary isn't set before rwd
  either.
- Array prefetch also in loops known to be short when the function
  refers to a declared object of 1 MiB or more: their streams likely
  come from memory, while short loops over data that stays in the
  caches pay the setup for nothing (Linpack, 320 KB, stays as it was).
  The loops' addresses no longer name their arrays after ivopts, so the
  test is per function. NPB SP's 34-iteration loops over 2 MB arrays on
  the 8C2: SP 25.8 -> 24.4 s (24.3 with -mapb-force), NPB 0.64 -> 0.65
  of lcc (LU 14.2 -> 13.8 s); set 1 unchanged.
- An invariant a loop keeps in %b[0..7] with no register free to move
  it to no longer stops the pipeliner: e2k_ms_move_b leaves it (BINV),
  the analysis gives it a register the loop's renamed values leave free
  (L->bmap), the kernel's instances read that, and each way in copies
  it there before setbn. Nothing changes when the loop isn't pipelined.
  Counted loops only. NPB SP's eta-direction flux loop (149 operations)
  now pipelines at II 30: SP 24.4 -> 23.6 s on the 8C2. With the two
  entries above: NPB 0.64 -> 0.66 of lcc on the 8C2 (LU 14.2 -> 13.1 s),
  0.58 -> 0.61 on the 2C3 (LU 13.3 -> 10.7 s, SP 51.4 -> 47.0 s); set 1
  and the rest of set 2 unchanged.
- FP compares into predicates in pipelined loops, as integer ones were
  (merges and predicated stores read them, and while loops' exit tests):
  LAME's quantize_lines_xrpow_01, "ix[0] = (compareval0 > xr[0]) ? 0 :
  1". Speculated as the loop's other FP operations, so not under
  -mno-spec-fp.
- A pipelined loop leaves out the dependence from a store to a later
  load when their types can't alias under strict aliasing
  (-mms-tbaa, on): a load may not read memory last stored through an
  incompatible type, while a later store may give the memory a new type,
  so only these true dependences go, as in GCC's true_dependence
  (may_alias_p uses no types). LAME's count_bits stores ints into ix and
  loads floats from xr: its quantizer loops now pipeline (II 2 for two
  elements, II 7 for four), LAME 10.67 -> 10.12 s on the 8C2 (lcc 7.43)
  and 8.09 -> 7.53 s on the 2C3, output the same; with the entry above
  CoreMark +0.3% and bzip2 -9 1.3% faster on the 8C2, the rest of both
  sets unchanged.
- A one-block counted loop is unrolled after all when its register
  recurrence is too long for e2k_modsched (e2k_loop_rec_bound_p: an II
  of the recurrence must leave II + 2 <= one iteration and 4 II <= 3
  times it, the pipeliner's rule; copies count nothing). Such a loop
  runs better unrolled, where the scheduler overlaps what the
  iterations don't chain: PolyBench's seidel-2d (six adds and a divide,
  38 cycles of 49) once the next entry made its loop one block, 3.83 ->
  3.37 s on the 8C2, as before.
- e2k_latch_copies (after loop2_invariant, -mlatch-copies) moves the
  register copies out-of-SSA leaves in a loop's latch, after its exit
  test, in front of the exit jump, when each copied-to register is dead
  at the exit and the jump doesn't read it. doloop's entered_at_top is
  false while the latch holds anything, so such loops weren't counted
  and the unroller unrolled them as two blocks (relcc2 findings P43).
  PolyBench's deriche pipelines its four IIR loops at II 12: 2.31 ->
  1.18 s on the 8C2 (lcc 1.20), 2.07 -> 0.91 s on the 2C3 (lcc 0.92);
  NPB LU 13.10 -> 12.32 s and MG 1.14 -> 1.08 s on the 8C2.
- Pipelined counted loops store through the AAU, as lcc's kernels do
  (-mstaa): `staad v, %aadN[ %aastiK ]` with `incr %aaincrM`, a
  descriptor per store whose base is its element in iteration 0 and a
  store index from 0 (written on each way in with the array prefetch
  setup, or alone: no program needed). The kernel runs each iteration's
  last stage once and stores are there, so no correction for the
  prologue. Aligned 1-8 byte elements stepped forward by whole elements
  (v3/v4 alignment known, as for array prefetch), at most 16. The store
  reads no address register in the kernel, and what only addressed
  movas and AAU stores (an induction step) leaves the kernel
  (kernel-dead: scheduled for the prologue, which keeps the movas'
  loads, but without a channel). No literal offsets (gas, relcc2
  findings I42). Used only where the operations taken out of the kernel
  lower the bound on II; otherwise the loop is tried again without them
  (Linpack's daxpy: 1.2% slower with them at the same II 1).
  PolyBench's fdtd-2d II 2 -> 1 in two loops on v5.
- The ring holds up to 63 pairs (%b[0..127], rsz's 6 bits), not 31:
  lcc's kernels use %b[64] and up. A leaf whose outgoing pairs would
  follow too big a ring (rbs <= 63, gas) grows its window around the
  loop, as a function with calls does (at most 36 + 63 of the 112
  pairs). With AAU stores, PolyBench's jacobi-2d runs its main loops at
  II 1 (40 pairs): 2.64 -> 1.77 s on the 8C2 (lcc 2.04), 1.99 -> 1.36 s
  on the 2C3. With the three entries above, PolyBench 0.79 -> 0.98 of
  lcc on the 8C2 and 0.76 -> 0.94 on the 2C3 (fdtd-2d 1.14, jacobi-2d
  1.15, durbin 1.03, deriche 1.02).
- Loop versioning for aliasing also takes loops that touch a declared
  array the dependence test told apart from every other array (no
  clique for it: it needs none), and up to 8 checks instead of 4 (NPB
  MG's resid: rows against a[0], a[2], a[3] and two more rows). The
  dump says why a loop wasn't versioned. NPB MG 1.08 -> 0.67 s on the
  8C2 (lcc 0.67), 1.67 -> 1.02 s on the 2C3 (lcc 1.11). With the four
  entries above, set 2 0.78 -> 0.86 of lcc on the 8C2 (NPB 0.65 ->
  0.71) and 0.75 -> 0.82 on the 2C3 (NPB 0.61 -> 0.66); set 1: Linpack
  1.1% slower on the 8C2 and 1.5% on the 2C3, xz -c 1.0% and 1.6%,
  CoreMark +0.1%, the rest unchanged.
- e2k_loop_rec_bound_p counts a conditional move as a compare and a
  merge (1 + 1, or 4 + 1 with an FP compare), not as the DFA's "multi"
  latency: a loop with selects in its recurrence is pipelined instead
  of unrolled (floyd-warshall's, below: recurrence 6 of 9 cycles, not
  10 of 13). No other set-3 kernel moved beyond noise (correlation and
  covariance vary from 10 to 16 s with one binary on the 8C2).
- AAU stores on v3 and v4 no longer need known alignment, only their
  type's: a misaligned staad stores correctly on the 4C (relcc2
  findings I43), as lcc's v3 code assumes.
- e2k_av_forward: in a one-block loop, an element the loop doesn't step
  through, read before a store of the same type that steps through the
  same array, lives in a register: loaded before the loop, updated
  after the store by a compare of the addresses and a select. Its
  memory dependence (a check would always fail) becomes a register
  recurrence. PolyBench's floyd-warshall ("path[i][k]" against
  "path[i][j]"), now versioned for path[k][j] and pipelined at II 6
  (lcc 3, with lock loads): 402 -> 90 s on the 8C2 (lcc 47), 252 -> 57
  s on the 2C3 (lcc 36). Stores to other arrays, and to the element
  itself, stay versioning's (gemm was 20 times slower otherwise).
- A store's data register waits for an FP-side result as an FP
  operation does (relcc2 findings I44, probed on all three machines):
  the producer's latency in its cluster, 2 cycles more from the other.
  The bundler had charged every store the 2 cycles of an integer
  consumer (seidel-2d's add of each quotient waited for its store: 16
  cycles after the fdivd instead of 14). Divides count as FP-side
  results in the pipeliner's crossing costs.
- e2k_av_loop: within a group of references through one base address,
  those the dependence test can't tell apart (over the whole loop,
  read-read pairs included) form a subgroup with a base of its own in
  the loop's clique, also with nothing to version for when a subgroup
  separates a store from another reference (seidel-2d's rows i - 1 and
  i + 1 against the store to row i). The runtime checks stay the
  groups'.
- Loops known to run 64 times or more (profile, else the doloop
  pass's constant count) are pipelined for any II at least 2 cycles
  shorter than an iteration, not only for one under three quarters of
  it, and the unroller no longer unrolls them as recurrence-bound
  (-mms-long): an unrolled seidel-2d lost each unrolled iteration's
  start and had no array prefetch.
- Pipelined loops relate two base registers that differ by a constant
  (e2k_ms_inv_delta): back from the loop to where they were last set,
  each block sets both from one register plus constants (or from two
  that differ by a constant there) or steps both by one constant, with
  one difference throughout. Memory dependences and array prefetch's
  store test use it: seidel-2d's three row pointers, so the loop runs
  at II 38 with all three rows through array prefetch, as lcc's (79.7
  -> 50.9 s on the 8C2 with the three entries above; lcc 50.8).
- A function keeps up to 32 alias-versioning cliques (and 32 for the
  overlap copies), not 8: Linpack's main, with everything inlined, had
  run out, so its later daxpy_ur loops went unversioned and
  unpipelined.
- Far loads (-mms-load-far=48): in a pipelined loop, a load array
  prefetch doesn't serve and no recurrence goes through is read 48
  cycles before its use, so that several iterations' misses are in
  flight, as lcc's kernels read them about 22 iterations ahead (relcc2
  findings P44). More stages, never a longer II: with the ring too full
  or no schedule, loads half as far (24, 12, 0) first; the
  unpipelined length that decides profitability keeps real latencies.
  v3 PolyBench at LARGE: most kernels 1.2-4.5 times faster on the 4C;
  v5/v6 only doitgen (0.65 -> 0.95 of lcc on the 8C2).
- e2k_narrow_ext (-mnarrow-ext), after REE: an extension of a 32-bit
  register whose uses all read at most 32 bits becomes a copy (or
  goes); one whose only 64-bit uses follow its loop moves to the loop's
  exits, when only same-kind extensions reach them (reaching
  definitions). Promoted ints otherwise carry a sxt in every
  reduction's recurrence (ext-dce counts promoted subregs as 64-bit
  reads): nussinov's max at II 2 on the 2C3 as lcc's (was 3), an int
  sum at II 1 (was 2). relcc2 findings P45.
- The unroll hook counts a register set once in the loop to a stepped
  register plus an invariant or a constant as a simple address, so such
  loops stay the pipeliner's instead of being unrolled: adi's column
  sweep at II 22 as lcc's (was unrolled, 29 cycles an element), adi
  25.2 -> 22.9 s on the 8C2 (lcc 21.3).
- Far loads only in loops known to run long or bounded by the doloop
  pass between 64 iterations and a million: in every pipelined loop
  they made CoreMark 18% slower on the 8C2 (its short matrix loops),
  xz -c 28%, zlib -c 9%.
- ivopts (generic, tree-ssa-address.cc copy_ref_info) keeps the
  dependence clique of a MEM[&decl] reference, which get_base_address
  takes for the decl.
- e2k_av_loop: references to a global array take their dependence
  clique bases through MEM[&decl]; and two references whose indices in
  some dimension are loop invariants a constant apart (SSA definitions
  expanded: i and i1 = i + 1) are in different subgroups. NPB SP's
  in-place plane updates pipeline with array prefetch: SP.W 22.35 ->
  15.56 s on the 8C2 (lcc 11.34). Set 2: SP.W
  20.94 -> 15.65 s (8C2), 37.08 -> 28.65 s (2C3); geomeans 0.981, 0.990.
- e2k_block_version (new late GIMPLE pass, -malias-version-block): a
  block outside loops whose loads follow stores through other pointers
  is versioned on a test of the byte ranges it touches through each,
  the copy's references getting a dependence clique with a base per
  pointer, as lcc does in NPB BT's binvcrhs (973 -> 112 wide
  instructions there). BT.W 10.47 -> 6.18 s on the 8C2 (lcc 6.37),
  13.25 -> 9.57 s on the 2C3.
- setbn_enter uses only the %b registers live after the pipelined loop,
  not all eight: the blanket uses made %b look live out of any loop
  before a pipelined one, and refused it. NPB SP's zeta-direction flux
  loop pipelines (II 17): SP.W 15.65 -> 14.83 s on the 8C2.
- Conversions take 4 cycles to a consumer of the format they produce
  (the DFA had 5, fdtofs 6), more in another (timing.md, "Formats",
  in e2k_adjust_cost). EP's vranlc 85 -> 79 cycles an element.
- fmaxd/fmind for x > y ? x : y and x < y ? x : y (exactly their
  semantics, NaNs and signed zeros included; 2 cycles instead of a
  compare and a merge). EP.W 7.59 -> 7.29 s on the 8C2 (with the
  conversion latency).
- Histogram loops (one address read and written through a computed
  index) stay one copy for the pipeliner; e2k_ms_try takes data
  speculation first when its II is clearly shorter; a check sees a
  store of the cycle before (latency 1, was 2). IS.W 0.32 -> 0.28 s on
  the 2C3.
- e2k_cond_loads (-mcond-loads): loads a branch skips run always when
  the join stores to the same memory on every path, the PHIs becoming
  selects (lame's count_bits). lame 9.34 -> 7.58 s on the 8C2 (lcc
  7.44), 7.40 -> 5.87 s on the 2C3.
- e2k_restore_pt: a pointer LIM converted from (unsigned long) &DECL
  plus an integer computed from no pointer gets back DECL alone as its
  points-to set (PRE had added "nonlocal"); NPB FT's evolve pipelines.
- e2k_alias_version_late: a second instance after SLP versions/tags the
  loops that cunroll made innermost (NPB SP's sweeps); the first stays
  after the vectorizer (adi, jacobi-2d, heat-3d need that).
- In a function that calls, regrename keeps to the window registers
  register allocation used (-mrename-window, HARD_REGNO_RENAME_OK),
  unless the function's hottest block runs 16 times as often as its
  hottest call into more than a leaf's caller (-mrename-window-ratio=16,
  -mrename-window-shallow; e2k_note_depth records how deep each compiled
  function's calls go, GCC compiling callees first). regrename took the
  register used least recently, a never used one, so windows grew to
  their 64 registers and every call kept them below its callee: Lua's
  precallC 7 -> 32 pairs (lcc 9), and k-nucleotide spent 5% of its
  cycles on register-file spills on the 8C2 (BUB_B_RF_SPILLFILL 602M,
  now 10M; lcc 83M). Where calls are rare or go to leaves the renaming
  wins more (CoreMark's matrix_test ran 7% slower without it). Set 2:
  Lua n-body 6.16 -> 5.38 s on the 8C2 and 5.86 -> 5.48 s on the 2C3,
  k-nucleotide 7.52 -> 7.39 and 7.18 -> 6.94 s; geomeans 0.991, 0.986.
  CoreMark -0.2%, zlib -9 +1% (the static profile has deflate_slow call
  fill_window often).
- e2k_short_chain: a loop walking a hash bucket's chain (a pointer the
  loop replaces by a field of what it points to, first loaded from an
  array element at a computed index) gets a profile of about two
  iterations and a dependence clique of its own on the next node's
  load, by which e2k_ms_wloop leaves it to the list scheduler, as lcc
  does: GCC guesses 18 iterations, the chains hold a node or two, and
  the pipelined walk paid its prologue and the loads past the node it
  stopped at (cache misses) on every entry. Lua's string table
  (internshrstr, tablerehash, luaS_remove) and 7 of SQLite's hash
  lookups; nothing else in sets 1-3. k-nucleotide 7.39 -> 6.92 s on the
  8C2 (lcc 6.0), 6.94 -> 6.61 s on the 2C3.
- AAU register writes (aaurw, aaurwd) take a store's channel unit in the
  DFA and count as stores in the bundler's channel search: gas encodes
  them as staa with MAS 0x3f and keeps a load out of ALC3 (ALC0) beside
  one in ALC2 (ALC5), so a load scheduled beside an array prefetch
  setup made gas reject the wide instruction (NPB LU with
  -fprefetch-loop-arrays).
- Loops of 200 operations or more may pipeline at an II up to 5/4 of
  one iteration (E2K_MS_BIG), for array prefetch and a schedule without
  the false dependences of allocated registers; the pipeliner takes up
  to 1024 operations and an II up to 512 (256 and 48 before), and the
  registers of values living less than II (e2k_ms_fixed) track any II
  (they assumed 64 or less). NPB LU's ssor (blts's recurrence loop, II
  284, with array prefetch), BT's and IS's long loops: on the 8C2 LU.W
  11.93 -> 11.41 s, BT.W 5.63 -> 5.36 s, IS.W 0.34 -> 0.32 s; on the 2C3
  BT.W 8.45 -> 7.93 s. sqlite3.c compiles in 108 s (96). LU's two
  resource-bound loops (575 and 634 operations) still fail: about 260
  values live at once in the earliest-start schedule, more than the
  ring and the window hold.
- (long) (int) of a float or double is one fdtoidtr/fstoidtr (the 64-bit
  conversion agrees wherever the int one is defined): NPB EP's tally
  index lost its sxt.
- Array prefetch through registers the loop derives from an induction
  register, X + INV + C (-mapb-derived): the selection reads them as X
  with INV a second invariant of the area's base (apb_inv2, added by the
  setup) and the first iteration's offset adjusted; stores through such
  registers compare in the same terms, so in-place updates keep their
  loads. NPB SP's compute_rhs: 675 -> 771 loads through array prefetch;
  SP.W 25.40 -> 23.71 s on the 2C3 (no L3: the plain loads went to
  memory), 12.74 -> 12.42 s on the 8C2.
- A one-block loop with simple addresses whose load steps 64 bytes or
  more is unrolled by two (-mapb-wide-unroll), so each copy reads
  through an array prefetch area of its own: an area fetches a line
  every 2 cycles at most, which held such loops at II 1 to 2 cycles an
  element (lcc does the same). syrk 1.05 -> 0.66 s, set 3 geomean 0.983
  on the 8C2; set 2's cholesky 1.96 -> 1.38 s (init_array; lcc 1.49).
  Plain loads for such streams instead lost 6.4% of set 3.
- Conditional returns in functions that call too (-mcond-returns-calls):
  the return block's prepare comes along into the block that branches
  (where %ctpr3 is dead on the other way), as lcc prepares a return
  right after the last call, and a prepare that an earlier one already
  holds on every way in goes (e2k_share_return_preps; no call between).
  Lua 0.7-1.0%, speedtest1 1.4% fewer cycles on the 8C2.
- The pipeliner derives addresses through a register that also holds
  other values of the body (register allocation's reuse), when every
  address through it lies between the derived definition and the next:
  NPB SP's hottest compute_rhs loop reads 32 instead of 17 of its
  loads through array prefetch; SP.W 23.65 -> 21.10 s on the 2C3.
- A loop a recurrence holds to about one iteration pipelines anyway
  when some of its loads can read through array prefetch from arrays
  that likely come from memory (-mms-apb-recur; II up to the
  unpipelined loop's, its loop-carried bound included): NPB BT.W 4%
  and SP.W 3% faster on the 2C3, SP.W 2% slower on the 8C2.
- Memory dependences through a register derived from an induction
  register are exact: e2k_ms_mem_deps reads it in its base register's
  terms (e2k_ms_underive, shared with array prefetch), so an unrolled
  body's two copies no longer order each other's accesses.
- The unroller's split induction variables ("r1 = r0 + 8; ...;
  r0 = r1 + 8") become one stepped register and a derived one before
  pipelining (e2k_ms_unsplit_ivs): the chain of adds held every loop
  unrolled by two to II 2.
- In loops known to run long the pipeliner combines a multiply with the
  add or subtract that alone reads it (fmul_add, fmul_sub, fmul_rsub;
  -mms-fma), never where the addend is on a recurrence (an unrolled
  reduction's partial sum): PolyBench's heat-3d 17% faster on the 8C2
  and the 2C3.
- Array prefetch areas are spread over both halves of the buffer, as
  lcc does (-mms-apb-spread): two areas get 2 KiB each instead of
  1 KiB, twice the prefetch depth; gramschmidt 3.43 -> 2.9 s on the 8C2.
- A reload of a spill slot that the loop stores is a copy of the stored
  value for the pipeliner, of the last iteration when it comes first
  (-mms-carry-slots): NPB LU's jacld had a carried value in a slot.
- The ring's packing starts at a lower bound (lifetimes over 2 II,
  half the peak of live instances): no change in code, faster compiles
  of big loops.
- Big pipelined loops fit the ring more often: nodes move to cut the
  peak of live values and the lifetimes when it doesn't fit
  (-mms-shorten), and loops of 200 operations or more try II up to 1.5
  times one unpipelined iteration (-mms-big-ii).
- A big loop whose operations fill the machine about as long as one
  iteration takes, when its overlapped schedule would be clearly
  longer, is also tried one iteration a pass of the kernel, as lcc's
  NPB LU loops run, and the shorter that fits wins (-mms-one-stage):
  jacld II 124, jacu II 122-133 (8C2, 4C) or 126 overlapped (2C3).
- On v3 an array prefetch area reads at most 24 bytes plus one element
  a step (bytes 25, halves 26, words 28, doublewords 32); every mova of
  a wider area is a diagnostic value on the 4C, while the 8C2 and 2C3
  take 32 for any format. The area grouping now caps mrng there: LAME's
  FIR died of SIGILL once its words read through array prefetch on v3.
- On v3 and v4 array prefetch reads elements whose type is aligned
  without proving the pointer's alignment (-mapb-type-align), as a
  strict-alignment target relies on C's alignment (lcc proves it, or
  assumes it with -faligned). NPB SP.W 51.1 -> 36.5 s on the 4C (lcc
  32.3), MG.W 1.49 -> 1.07 s, PolyBench fdtd-2d 18.0 -> 5.5 s,
  jacobi-2d 15.7 -> 5.3 s.
- A loop that ends a hardware loop prepares its own back edge in a
  CTPR other than %ctpr2, which the inner loop's array prefetch program
  needs (-mloop-ctpr2-free): NPB FT's cffts2 and SP's x_solve kept 9
  loops from array prefetch. SP.W 20.74 -> 17.39 s on the 2C3 (lcc
  17.66), 12.01 -> 11.25 s on the 8C2 (lcc 11.34).
- On v3 and v4 a loop that reads one array backwards with plain loads
  gets no array prefetch (-mapb-beside-backward to prefetch anyway): on
  the 4C a prefetched stream beside it ran 1.3 cycles an element slower
  than plain loads. PolyBench's durbin 5.40 -> 3.96 s on the 4C (lcc
  6.34).
- A loop whose doloop counter register allocation spilled becomes a
  hardware loop anyway (-mhwloop-unspill): the count is loaded on the
  way in into a register free in the loop, or, when the loop uses them
  all, into one dead at its head while e2k_hwloop_opt converts the
  loop. NPB LU's jacld on v3 counted in memory and wasn't pipelined;
  LU.W on the 4C 23.7 -> 22.5 s (lcc 17.9).
- A loop that keeps an element in a register its store may update
  (e2k_av_forward) is split after the iteration whose store writes it
  (-mav-split), with loop_version and tree-ssa-loop-split.cc's
  connect_loops: neither part carries the element, and both copies of
  PolyBench's floyd-warshall loop pipeline at II 1. floyd-warshall
  74.7 -> 17.6 s on the 8C2 (lcc 47.2), 45.3 -> 13.3 s on the 2C3 (lcc
  35.6).
- A loop that hw-doloop found by its counter's liveness but that is
  entered elsewhere than at its head (the register reused around it)
  gets no hardware loop: e2k_hwloop_opt redirected every entry to the
  head and lost the loop's code (xz's main linked with an undefined
  label once predicated calls joined the blocks around such a loop).
- Calls run under a predicate: e2k_call, e2k_call_value, their disp
  (printed unconditionally; IFCVT_MODIFY_INSN keeps it out of an arm
  whose opposite prepares another callee) and the sqrt pair are
  predicable, so ce3 predicates a short arm with a call rather than
  branching around it, as lcc does for the errno call of NPB EP's sqrt
  ("fsqrttd ? ~p", "call sqrt ? p"). The clobbers of a predicated call
  neither read nor kill in GCC's dataflow (df-scan.cc,
  df-problems.cc): with them every call-clobbered register was live up
  to such a call, which cost NPB CG its array prefetch (2-3.4x slower),
  bzip2 10-13% and Lua 5-15%. NPB EP.W 3-4% faster on all three machines.
- CS1 as a MAS field per load/store channel (ALC0, 2, 3, 5), excluded by
  setwd, wait and calls; a lock load and its check keep stores out of
  their wide instruction by exclusion units, and in a pipelined kernel
  (e2k_dfa_ms) may share one, as lcc's NPB IS histogram has them, the
  check apart from its lock where a row has room (I45); stores before
  the DAM pair in the pipeliner's order go after it (-mdam-stores-late).
  IS's histogram II 4 -> 2.
- A pipelined loop with a lock load is bounded by the stages from the
  lock to its check (32 entries), not by all its stages (-mdam-deep), and
  the lock load is a far load like the others (-mdam-far): IS's lock 25
  iterations ahead of its check at II 2 (lcc's: 28).
- Array prefetch and AAU stores in pipelined loops with a lock load
  (-mdam-apb): the compensation code goes back by an ibranch, which
  leaves %ctpr2, as lcc's does. NPB IS class A, timed part, with the
  MAS and DAM depth changes: 1.68 -> 0.17 s on the 8C2 (lcc 0.18),
  1.20 -> 0.34 on the 2C3 (lcc 0.30), 3.05 -> 0.65 on the 4C (0.61).
- Alias versioning checks the segments of two references whose bases
  differ by an amount the loop doesn't know, which the dependence test
  takes for one element (-mav-rows): NPB FT's butterfly ("y[i21+k][j]",
  "y[i22+k][j]") II 5 -> 3.
- In a pipelined loop not known to run long, multiplies are combined
  with the adds after them where that shortens the II, found both ways
  (-mms-fma-ii; e2k_ms_unfuse_fma puts them back otherwise): FT's
  butterfly II 3 -> 2 with AAU stores, as lcc's kernel. FT.W 2-3% faster.
- An AAU register write shares its wide instruction with an ALU
  operation after it and with the APB program's ldisp, now emitted
  first (-maau-setup-war); bap keeps its 5 cycles after the ldisp
  (e2k_bap_deps). A descriptor a cycle instead of two: NPB FT.W 3-5%
  faster on all three machines.
- A pointer advanced by an offset loaded through it is a hash chain too
  (e2k_short_chain, -mchain-offsets): Lua's table lookups are no longer
  pipelined (luaH_getshortstr at II 10 for 1.7 expected nodes).
  k-nucleotide 1.6% faster on the 2C3.
- e2k_hoist_taken_loads (-mhoist-taken-loads): the loads that start a
  block reached by conditional branches, one at least taken to it, run
  above each of them speculatively where their register is dead on the
  other way; sched-ebb only speculates along fall-throughs. Lua's table
  lookups load a key's value beside its type, as lcc does: k-nucleotide
  2% faster on the 2C3.
- e2k_hoist_taken_loads also takes zero- and sign-extended loads and,
  with -mhoist-alu, the speculative-form operations that compute the
  next loads' addresses (an interpreter's opcode and table index),
  chains of them only along likely branches, always with a load; nothing moves along
  a branch taken less than a fifth of the time, and no block is left
  with nothing but its jump.
- e2k_dup_dispatch (-mdup-dispatch): a small block ending in a computed
  jump gets a copy on the taken way of each conditional branch to it,
  where e2k_hoist_taken_loads starts the next fetch and table load
  before the branch. Lua's VM: 2-7% fewer cycles on the 2C3, n-body and
  spectral-norm now at or under lcc's.
- A disp or the return's prepare may share the prologue's setwd, and
  operations that don't read the new stack pointer its getsp, as in
  lcc's prologues (-mprologue-prep): Lua 0.4-1.3% fewer cycles on the
  2C3.
- e2k_skip_jump_blocks (-mskip-jumps): a branch into a block of disps
  and a ct (a loop's way in split for its disp) goes through that ct's
  CTPR straight to its target, the disps moved before it.
- A predicated load whose arm ends by writing its register under the
  same predicate runs unpredicated (",sm") in a free register before
  the compare (-munpred-last), e.g. Lua's "o = &G(L)->nilvalue" in every
  API accessor.
- In a counted pipelined loop not known to run long, a gather (a load
  whose address another load of the loop gives) is read as far as an L2
  hit, 12 cycles, 16 with v6 latencies (-mms-gather-far): NPB CG.W 4-5%
  faster on the 8C2 and 2C3.
- e2k.cc is split into 16 files by subsystem, with e2k-internal.h for
  what they share and machine_function in e2k.h (the Design section's
  "Source files" lists them); the generated assembly is unchanged.
- -fdump-rtl-mach-details shows the recurrence that bounds each
  pipelined loop's II (e2k_ms_rec_mii, e2k_ms_dump_recurrence) and the
  neighbours that close a failed node's window.
- The earliest-start order is tried for loops the DAM might help once
  e2k_ms_try has weighed the II with a lock load (dam_settled).
- Two more earliest-start attempts: as at II - SLACK where a node
  lacked SLACK cycles (-mms-est-slack), and least room first
  (-mms-est-crit).
- Iterative modulo scheduling (Rau's, -mms-ims) where the other orders
  fail at an II, for counted loops without a lock load: NPB LU's blts
  at its recurrence's bound, II 207 (was 274; lcc about 253).
  With the two entries before: LU.W 4.4% faster on the 8C2, 7.8% on
  the 4C (2C3: ssor's cycles 18% fewer, wall time noisy), SP 2-2.6%,
  adi 3-6%.
- Channel assignment covers wide instructions of up to 16 insns (was
  8, which left full kernel instructions to gas). Validated with the next four (ms13): sets within noise.
- Write-back conflicts are tracked over the last four cycles per
  channel, so back-to-back FP-side operations no longer hide one.
  smulx_fw back to back: 1.5 -> 1 cycle an element.
- floor, ceil, btrunc, roundeven, rint, nearbyint (SF, DF, V2SF) are
  fdtoifd/fstoifs/pfstoifs with roundsd's immediate; floor, ceil and
  trunc raise no inexact (lcc's do). floor loop 16.9 -> 0.70 ns on the 8C2.
- Overflow checks with the x86 flag operations (-mflag-ops, off for
  qemu runs): addv (adds_fw/addd_fd + a branch on OF, cctopo), subv
  (cmpo<s,d>b), mulv and umulv on SI (smulx_fw/umulx_fw); constants and
  64-bit multiplies stay GCC's. A flag result reaches its own channel's
  cctop in 2, anything else in 4 (multiplies 6). Same results as lcc over
  60.9M cases; 0.25-0.72 of lcc's time on all three machines.
- ldexp is fscaled/fscales on v4+ where it needn't set errno
  (-fno-math-errno). ldexp loop 34 -> 0.90 ns on the 8C2.
- Loops with the quiet FP compares (fcmpud*f) pipeline; their flags
  reach integer operations in 4 in either cluster. isless counts 8.70 -> 0.676
  ns on the 8C2.
- Fields of 32-bit values are extracted with getfs, not getfd (a 32-bit
  result read as 64 bits costs 3 more cycles under dbl = 0, and may
  trap on a diagnostic upper half).
- sqrt with errno: fsqrtid/fsqrttd on every path, the libm call only for
  errno (CDCE_UNCONDITIONAL_IFN); no SIGILL from MCST libm's diagnostic
  NaN after feclearexcept (FE_INVALID). EP class A 1% faster.
- A predicated load that ends its arm runs early as ld,sm into a free
  register, only a copy under the predicate (-munpred-copy).
- Loads of FP arms may go under a predicate (-mifcvt-fp-loads; SF/DF
  loads predicable): isless select chains 20-30% faster.
- FP compares' predicates are used where an arm is estimated to run at
  least 30% of the time (-mifcvt-fp-prob=30): `<` select chains 28-31%
  faster, Linpack 3% on the 8C2.
- sqrt's errno call waits for the inline root (it reads the root,
  copied to %b[1]): before, the scheduler could put the call first, and
  MCST's libm still trapped after feclearexcept (FE_INVALID) when the
  root fed an FP operation (relcc2 findings A23).
- A variadic call whose C++ result takes the hidden pointer stores the
  last declared argument in memory, not the one before it (relcc2
  findings A24): lcc callees read it there.
- System calls in inline asm as glibc and the uapi headers write them
  (relcc2 findings A25, P87): `%#` prints the window base in an asm;
  `"call"` is a clobber name; an asm with `"call"` or `"b[N]"` clobbers
  what a call does and memory (also for the GIMPLE optimizers,
  `ASM_CLOBBER_MEMORY_P`), and its function gets the outgoing pairs
  with `wbs` >= 4 (SIGSEGV below); a leaf's early return prepare isn't
  kept across an asm that clobbers `%ctpr3` or calls.
- `setwd nfx = 0` in functions with long double operations, as lcc: with
  `nfx = 1` a signal between `movif` and `movfi` lost the 16-bit part
  (relcc2 findings A26: 104 and 143 wrong results in 8.2 million on the
  4C and 8C2 under a 50 us timer, 0 now).
- `va_list` is `char *`, as lcc: C++ functions taking one mangle `Pc`
  and link with lcc's code (they were `Pv`).
- The stack protector reads glibc's guard at TP - 8 (`%g13 - 8`):
  `-fstack-protector*` programs linked against `__stack_chk_guard`,
  which MCST's glibc lacks.
- Control speculation leaves volatile loads alone (they ran with `,sm`
  in the wide instruction of the jump that skips them).
- `__builtin___clear_cache` calls `__clear_cache`, which calls
  `__e2k_clear_cache` (`CLEAR_INSN_CACHE`, as MCST's runtime): both
  were empty.
- `-ffast-math`, `-Ofast` and `-funsafe-math-optimizations` link MCST's
  `crtfastmath.o` (flush to zero, denormals are zero), as lcc, also
  into shared objects.
- No temporaries in `%g0`-`%g15` (a signal handler's writes to them
  reach the interrupted code): the thunk temporary is `%g16`,
  `SRET_REGNUM` `%g31`.
- Under `-fPIC` an asm's `"i"`/`"ri"` operand takes no symbol as a
  literal (`LEGITIMATE_PIC_OPERAND_P`): `"ri"` uses a register, `"i"`
  is an error, as lcc; it was a text relocation.
- 16-byte atomics inline on `-march=elbrus-v5` and up (`ldqp`/`stqp`
  lock-wait loops in lcc's v5 and v6 forms, `nfx = 0`);
  `-mno-quad-memory-atomic` calls libatomic as before (relcc2 findings
  A29). Fetch-add is 54 cycles against lcc's 45 (GCC's loop around the
  compare-exchange), compare-exchange 42 against 46.
- Wide instructions are kept within the 16 words gas takes
  (`e2k_fit_bundles`, relcc2 findings I52): each is counted as gas lays
  it out after channel assignment and ended early before an operation
  that would pass 16; prologues already reached 16. `-mwi-size-check`
  labels each instruction with its estimate for checking against gas.
  `e2k_insn_lits` now counts a predicated field insertion's literal and
  a pipelined check load's.
- v5+: a loop whose count may pass 32 bits writes it to `%lsr1` (after
  `%lsr` with `vlc`) instead of being strip-mined, so `size_t` loops
  pipeline with array prefetch there (axpy over 1M doubles 7.6 -> 0.86
  ns an element on the 8C2).
- The channel assigner charges a store's integer data no cluster
  crossing (spec/isa/timing.md, "Clusters": only FP data pays, +2):
  it took a store as an FP consumer, which cost an integer producer in
  the other cluster a cycle.
- Compares and cctops into a predicate no longer count as write-back
  conflict makers in the channel assigner (timing.md, "Write-back
  conflicts").
- Divider timing by operation (timing.md, "The divider"): fsqrtid 11,
  fsqrttd 14 holding the divider 4 cycles before v6 (2 on v6), also
  for predicated operations (`e2k_fdiv_kind`).
- Loops with double square roots are pipelined under -fno-math-errno,
  as lcc does: fsqrttd is an unspec of its two operands, which the
  pipeliner takes, one every 4 cycles before v6 (2 on v6). A sqrt
  loop takes 4 cycles an element on the 4C, 8C2 and 2C3, as lcc's.
- The wide-instruction size count also takes the ALES2/ALES5 word of an
  FP add, subtract or multiply in ALC2 or ALC5 on v4 and later, a
  predicated low-mask AND's 64-bit literal and an FP negation's sign
  bit: none of 1.4 million instructions (-O2, -O3, v5, v6) is over its
  estimate now (v5 had 1,647).
- The array prefetch setup reads a loop's %b[] invariants from the
  registers they were copied to before setbn: on v6 the listed prologue
  takes the setup in after setbn, where NPB LU's ssor built a
  descriptor from a fresh ring register (SIGILL on the 2C3).
- `__builtin_prefetch` takes lcc's MAS for its locality: 0x60, 0x40,
  0x20 for 0-2, and for 3 none (an L1 fill) when tuned for the 4C or
  8C2 or for v7, else 0x20 (timing.md, "Software prefetch").
- rrs of the FP state has its 11-cycle latency (timing.md, "State
  registers"), only for readers of its value; independent reads go one
  a cycle (`e2k_adjust_cost`, `e2k_rrs_deps`).
- Release and seq_cst stores are lcc's: the wait and the store in one
  wide instruction, and on v5 the wait with sal and sas after an empty
  instruction (the E8C2's soft-wait erratum): 6.4 cycles a store on the
  8C2 against 13.8 (atomics.md).
- Code for the machine's ISA gains nothing yet: sets 2 and 3 with
  `-march=elbrus-v5 -mtune=elbrus-8c2` run as fast as with the `-mtune`
  alone (v3 code): geomean 1.000 and 0.999 on the 8C2, and with
  `-march=elbrus-v6` 1.002 and 0.998 on the 2C3; fdtd-2d is 3% slower
  as v5 code, adi 7% as v6 code. The PoC doesn't use what v5 and v6
  add for loops (128-bit packed operations) yet.
- `e2k_narrow_ext` defers its rescans until it is done: a deleted
  extension's refs, freed at once, left other DU chains dangling (ICE
  on PolyBench's durbin with 128-bit vectors).
- `e2k_ms_move_b` and the BINV copies move a %b[] value in the widest
  mode the loop uses it in: a 16-byte vector lost its high half in a
  DImode copy (gcc.dg/vect's vect-nest-cycle-3).
- From v5, 16-byte vector modes (V16QI, V8HI, V4SI, V2DI, V4SF, V2DF)
  take one register: qpor copies, loads are two ldd and qppackdl on v5
  (its ldqp is served by L2) and ldqp on v6, stores stqp where 16-byte
  aligned, else two std; arguments keep their two 64-bit slots; nfx = 0
  in a function holding one. GNU vector code gets qp arithmetic and
  logic; the pipeliner leaves such loops out.
- `-mvect128` (off by default) lets the vectorizer use the 16-byte
  modes on v5+: qp arithmetic, multiplies, min/max, shifts, integer
  and FP compares into masks, qpmerge, same-width conversions, qppermb
  permutes, lane sums; misaligned moves as two ldd or std on v5.
- 16-byte vector loops are pipelined: the ring copies keep the
  vector's mode. With -mvect128 on the 8C2, saxpy runs at II 2 for four
  floats and daxpy at II 1 for two doubles; PolyBench with the dynamic
  cost model: gemm 1.58x, stencils down to 0.50x, geomean 0.954.
- v5: array prefetch takes 2-, 4- and 8-byte loads at any alignment
  (the halves of a misaligned 16-byte vector).
- AAU stores at any alignment (they need none on any version): the
  halves of a misaligned v5 vector store.
- Unsigned compares of 64-bit vector lanes flip the sign bits and use
  qpcmpgtd (no unsigned max there); an ICE in 960209-1 with -mvect128.
- A 16-byte vector MEM_REF gets its type's alignment at expand: ivopts'
  pointers keep only the array's 8 bytes, so peeled aligned loads
  expanded as misaligned (heat-3d).
- e2k_ms_inv_delta also follows a block that sets one invariant alone
  from the other plus a constant (a vector's +8 half, hoisted).
- Pipelined loops read an aligned v5 16-byte vector with one movaqp
  (fmt 5 area; the ldd+ldd+qppackdl run only in the prologue, as one
  ldqp) and store one with staaqp: saxpy II 1 for four floats, gemm's
  vector loop II 1 for two doubles; PolyBench with -mvect128 and the
  dynamic cost model from 0.954 to 0.995 of the scalar code.
- Pipelined loops combine a 16-byte FP multiply and its add into
  qpfmul_add and kin as they do scalar ones: PolyBench's syr2k 1.39x
  with -mvect128.
- v5: a field scaled by 2 to 128, (x >> k) & m or (x << k) & m, is one
  getfz (an integer operation, 1 cycle), as lcc's v5 code has it: Lua
  1.6-5.6% faster on the 8C2.
- v5: `__int128` add and subtract are addd/subd, addcd_c/subcd_c and
  addcd/subcd (3 operations, 2 cycles) instead of five with a compare
  and a merge.
- v5 `-mvect128`: a vectorizer cost model of the pipeliner's II
  (channels, array prefetch reads, stores; in-order reductions; code
  outside the loop ten times): PolyBench 1.012 against scalar on the
  8C2 (gemm 1.59, heat-3d 0.69); still off by default.
- Alias versioning tells apart rows of one array that a vector loop
  reads at misaligned offsets (by the bytes each covers): NPB SP's
  vector loops pipeline again.
- Alias versioning also takes the vectorizer's scalar fallback and
  epilogue loops (it skipped every dont_vectorize loop).
- Alias versioning gives cliques to addressable local arrays (MG's
  u1 and u2 once vectorized), so their loops stay pipelined.
- v5 `-mvect128`: no basic-block SLP inside loops (NPB LU lost ten
  pipelined loops to it).
- v5 `-mvect128` costs: multiplies fused into adds (both loops),
  stores in the ALU channels, lane packing and extraction in four
  channels, a stream packing each vector once: heat-3d and
  gramschmidt's column loop stay scalar.
- v5: vector rotates are psrcw, qpsrcw and qpsrcd (lcc uses psrcw).
- v5 vector costs: 40 cycles for each scalar loop vectorizing adds
  around a vector one (peeled iterations, epilogue): NPB SP's short
  loops stay scalar.
- v6: misaligned 16-byte loads through array prefetch (movaqp) and
  stores through the AAU (staaqp), as the 2C3 takes them.
- v6 vector costs: misaligned 16-byte accesses as aligned ones (no
  peeling for alignment).
- 16-byte vectors: no basic-block SLP with them (NPB BT's 5x5 block
  routines on the 2C3); narrower groups as without -mvect128.
- Loops the vectorizer made (epilogues, peeled and fallback copies)
  keep near loads: their bound is the runtime threshold, not a sign of
  a long loop (LAME's band loops).
- v5 vector costs: no loop without a whole-vector load or store (Lua's
  type-tag stores, one byte each).
- 16-byte vectors on by default for v5 and later (-mno-vect128), with
  the dynamic vectorizer cost model at -O2.
- Builds on GCC master of 2026-10-13 (merged, ca33fb40100):
  `CLZ_DEFINED_VALUE_AT_ZERO` gives the element's bit size, as the
  vectorizer now asks with vector modes.
- `e2k_narrow_ext` drops the DU chains before its deferred rescans: the
  rescans unlinked refs freed already (an ICE on zstd's divsufsort.c
  with 16-byte vectors on v6).
- `e2k_short_chain` takes a chain's first node from a parameter (no
  block) as from before the loop (an ICE on 7-Zip's ExtHandler.cpp).
- `e2k_ms_fold_latches` sets the inverted jump's REG_BR_PROB from its
  edge (verify_flow_info failed on 7-Zip's GzHandler.cpp).
- A disp stays out of a predicated arm when its CTPR is live after the
  arm, unless the other arm prepares the same callee: a call shared in
  the join took the arm's callee on both ways (GMP's mpz_lucas_mod
  called mpz_addmul_ui for mpz_submul_ui).

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
- Renaming for speculation (`-mspec-rename`, on but at `-Og`): in a block entered
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
  libgomp pr52547; done since v0.6), `__builtin_return_address (n > 0)`, complex `"r"`
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

### Source files

The order of the back end's last steps is `e2k_reorg`'s (e2k-reorg.cc).

| File | What it holds |
|---|---|
| `e2k.h`, `linux.h` | target macros; `struct machine_function` (per-function state) |
| `e2k-protos.h` | what `e2k.md` and the middle end call |
| `e2k-internal.h` | what the `.cc` files share: types, macros, declarations by file |
| `e2k.opt`, `e2k-opts.h` | options |
| `e2k.md`, `e2k-vect.md`, `predicates.md`, `constraints.md` | instruction patterns |
| `e2k-sched.md` | the DFA: channels, units, latencies (spec/isa/timing.md) |
| `e2k.cc` | target hooks (`targetm`), options, register modes, addresses and constants, costs, operand printing, types |
| `e2k-abi.cc` | PIC and TLS, arguments and results, frame, prologue and epilogue, calls, inline asm, nonlocal gotos |
| `e2k-builtins.cc` | builtins and the `__float80`/`__float128` types |
| `e2k-c.cc` | the C and C++ front ends' part: lcc's pragmas |
| `e2k-expand.cc` | expanders and splitters: moves, compares, conditional moves, vectors, `getf`/`insf`, byte swaps |
| `e2k-av.cc` | GIMPLE passes: loops and blocks versioned for aliasing |
| `e2k-passes.cc` | small RTL passes: latch copies, `dbl` zero extensions, narrow extensions, address height |
| `e2k-hwloop.cc` | counted loops on `%lsr`: doloop, unrolling, count setup, spilled counts |
| `e2k-reorg.cc` | machine reorg (`e2k_reorg`) and the control flow reshaping it starts with |
| `e2k-ms.cc` | software pipelining: driver, loop choice, FMA fusing, `setbn` and loop-end output |
| `e2k-ms-analyze.cc` | pipelining: dependence graph, alias rules, APB loads, AAU stores, DAM |
| `e2k-ms-sched.cc` | pipelining: the modulo schedule, the DAM plan, rotating register names |
| `e2k-ms-emit.cc` | pipelining: prologue, kernel, exits, copies out, APB program |
| `e2k-branch.cc` | prepared transfers: disps placed, shared and moved up |
| `e2k-spec.cc` | speculation around scheduling: what may move up, extra dependences, unpredicated loads, `,sm`, diagnostic values |
| `e2k-rename.cc` | register renaming within the window; renaming for speculation |
| `e2k-sched.cc` | list scheduler hooks: costs, issue, speculation, AAU and speculative load output |
| `e2k-bundle.cc` | wide instructions: bundles, nops, ALU channels, final's output |

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

### Frame and window (`e2k-abi.cc`: `e2k_expand_prologue`, `e2k_compute_window`)

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
  Results the other way round: the callee extends, and the caller sees
  `%b[0]` in the narrow mode (`e2k_function_value` with `!outgoing`) and
  re-extends, as lcc's callers do. MCST's `clone.S`, `clone2.S` and
  `longjmp.S` return `int` in the low half only (glibc's
  `tst-getcwd-smallbuff` printed `/proc/<junk>/uid_map`).
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
  `.accept`/`.ignore strict_delay`. Operations that must share one wide
  instruction (`landp` chains, a loop end's `alc` and `ct`, a DAM check
  and its `rbranch`, `rrd %ip` with its GOT literal) sit between `%<`
  and `%>`, braces when the bundler is off.
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
- `DWARF_FRAME_REGISTERS` 48, as in MCST's libgcc build: the unwinder
  reads no register rules, and with all 261 hard registers each
  `_Unwind_FrameState` was 2.4 KB (`uw_init_context` 2,528 bytes of
  stack, lcc's 160). A cancellation from a signal handler on glibc's
  `tst-cancel21` alternate stack (2 * SIGSTKSZ) ran out of it.
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

Compilers:
- To compile only (`-c`, `-S`): the build tree's driver at the latest
  build, `toolchains/build-gcc-claude3/gcc/xgcc
  -Btoolchains/build-gcc-claude3/gcc/` (absolute paths), as
  `toolchains/claude-e2k/torture/run.sh`, `build.sh` and `build2.sh`
  use it. Its target libraries (2026-10-12) are older than its
  compiler: don't link with them.
- For whole programs: an installed generic-v3 cross on lcc's sysroot
  from `toolchains/poc-cross/cross-cpu.sh`,
  `toolchains/poc-cross/cross-VERSION-v3/gcc-e2k-VERSION-v3/bin/e2k-linux-gnu-{gcc,g++}`;
  the newest is 0.5+43 (before `89ef46924a9`, global registers in asm).
- `toolchains/gcc-claude-install` holds the compiler of 2026-10-05, and
  the old wrapper `toolchains/claude-e2k/scratch/gcc-e2k` was deleted on
  2026-10-25.

Programs link with GCC's own driver, libgcc and libstdc++ against lcc's
glibc. Run under qemu with `qemu-e2k -cpu elbrus-v3 -L $L/fs` (add
`-E LD_LIBRARY_PATH=<install>/e2k-linux-gnu/lib64` for shared
libstdc++).

```
X=toolchains/poc-cross/cross-0.5+43-v3/gcc-e2k-0.5+43-v3/bin
G=$X/e2k-linux-gnu-gcc GXX=$X/e2k-linux-gnu-g++
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
  `scp-8c2`, `sync-8c2-libs`), `make -j4`. Connect with relcc2's
  `tools/setup/e2k-ssh` and `e2k-scp` only (its key, nothing else).
- Never look at `/opt/mcst/gcc-16.0.0-A.XXX.e2k-v7.5.10` on the host:
  unknown origin, relcc2 decision 4.

## Next (after v0.4)

Where v0.4 stands is in its results above: ahead of lcc on PolyBench
and CoreMark, even with it on set 2, behind on NPB FT and LU, SQLite,
NPB EP, PolyBench's adi, xz, and Linpack on the 2C3. Plan, in order:

1. The set-2 gaps (FT, LU, SQLite, EP): profile each against lcc's code
   with relcc2's `tools/isa-score/profile.py` (cycles per block on the
   4C, the 8C2 and the 2C3).
2. Linpack on the 2C3: 1.15 times lcc's speed on the 4C, 0.80 on the
   2C3 (v6's 5-cycle L1 loads in daxpy's kernel?).
3. v6: a column loop vectorized beside a stream from memory (PolyBench
   cholesky's init_array 1.37 times as long with 16-byte vectors;
   relcc2 findings P93, point 9).
4. Calls under a predicate where the two ways prepare different
   callees for a call they share in the join are branches again (the
   predicated-call guard); a call per arm, as lcc has, would keep them
   straight code.
5. pcre2's test 14 died once with SIGILL on the 8C2 (one run in 20,
   during a GCC bootstrap there); not reproduced in 19 more runs.
6. Tests: GCC's C and C++ suites and libstdc++ on the 4C (last at v0.3).
7. Port gaps: sibling calls; heap trampolines (`-ftrampoline-impl=heap`
   needs libgcc's heap-trampoline.c for E2K, plan D1).

Measuring (relcc2 `toolchains/claude-e2k` unless said): `perf/build.sh
NAME "CC" O2`, then `perf/run4.sh`, `run8.sh` or `run6.sh DIR...` on
the 4C, 8C2 or 2C3 (CoreMark and Linpack; check "Correct operation
validated": CoreMark calibrates its count); `real/real-all-h.sh NAME CC
CFLAGS [4c|8c2] [CXX]` builds the real programs and runs their tests,
`speed/ctime.sh HOST ROUNDS BUILD...` times their compression (lcc's
builds: `real/lcc4c`, `lcc8c2`, `lcc2c3`); relcc2 `toolchains/bench2`
(set 2, `build.sh`) and `toolchains/bench3` (set 3, `build.sh` and
`remote.sh`) per CPU target, lcc's results in `res-*-lcc.txt`;
`torture/hw4.sh`, `hw8.sh` and `hw6c0.sh NAME "OPTS"` (compiler in `$G`)
run every torture test on the 4C, the 8C2 and the 2C3 (core 0),
`torture/hwv.sh` the gcc.dg/vect tests. Long tests use a snapshot of
the compiler (`mksnap.sh NAME`, then `scratch/gcc-snap` with `$SNAP`)
so that the build can go on. Build cc1 in build-gcc-claude3 (`make -j10
-C build-gcc-claude3/gcc cc1`); its gcc/ was configured without shared
libgcc, so after `make all-gcc` or `make specs` there put the libgcc
spec with `-lgcc_eh` for static links back into its `specs` file.
