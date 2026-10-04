# E2K back end proof of concept: state

Written by Claude (Anthropic) on the branch `claudes-e2k-compiler`, from
the relcc2 specification (`spec/isa`, `spec/abi`, `doc/gcc-port-plan.md`)
to find out what the spec is missing. Not for contribution to GCC (GCC
refuses AI-written code); the owner writes the real port by hand and may
reuse the design. Spec gaps go to relcc2 `docs/spec-poc-findings.md`.

This file is the source of truth for the work; update it with every
commit. Tag `v0.1` marks the state described in "v0.1" below; "Since
v0.1" lists what came after.

## Since v0.1

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

## In progress (checkpoint before context compaction, 2026-10-04)

- GCC's C testsuite on the 4C, running in the background:
  `cd toolchains/build-gcc-claude; DEJAGNU=../claude-e2k/dejagnu/site.exp
  make -j8 -C gcc check-c RUNTESTFLAGS=--target_board=e2k-4c`
  (log `check-gcc-c-4c.log`; results `gcc/testsuite/gcc*/gcc.log`, then
  copied to `toolchains/claude-e2k/dejagnu/gcc-4c.{sum,log}`). Midway:
  30.7k PASS, 166 FAIL, triaged:
  - ~120: `gcc.c-torture/execute/builtins/*-chk.c` (all levels) and
    `built-in-setjmp`: `__builtin_setjmp`/`__builtin_longjmp` are not
    implemented. Plan: GCC's 5-word buffer holds FP, receiver label and
    stack save (words 0-2); put the address of a real 80-byte glibc
    `jmp_buf` in the setjmp caller's frame into word 3. The
    `builtin_setjmp_setup` pattern calls `_setjmp` on it and jumps to
    the receiver label (word 1) when it returns nonzero; the
    `builtin_longjmp` pattern calls glibc `longjmp (*(word 3), 1)`,
    which unwinds the chain stack through the kernel (`e2k_longjmp2`).
    Don't rebuild cc1 while the testsuite runs.
  - frames over 2 GiB (20031023-*; lcc rejects them too), pr82564
    (nested function returning a VLA struct; lcc rejects), labels-3
    `-O3 -g` (gas internal error, findings I8), pr55921 and 20000804-1
    (`"r"` asm operand of `_Complex` type: complex modes are not allowed
    in registers; known gap, left).
- Then: g++ testsuite (`check-c++`), libstdc++ testsuite, libatomic on
  the 4C done (54/54); then tag v0.2 (owner agreed: v0.2 = DejaGnu boards
  + runtime testsuites + fixes + regression rerun).

## Working notes (for agents)

- Commits: worktree-local identity "Claude (Opus 5.5)"; atomic commits;
  update this file with each one.
- On the 4C use only `~/relcc2/claude-probe` and `~/relcc2/claude-compat`;
  other agents work there (e.g. `~/relcc2/claude-loops`; don't touch).
  If ssh says "No route to host", the 4C is down: stop and tell the owner.
- Never look at `/opt/mcst/gcc-16.0.0-A.XXX.e2k-v7.5.10` on the host:
  unknown origin, relcc2 decision 4.

## Next

1. The rest of "Not done": trampolines and nonlocal goto (each needs a
   spec answer first), gdb, DejaGnu boards and test suites,
   `-march` variants.
2. Performance last.
