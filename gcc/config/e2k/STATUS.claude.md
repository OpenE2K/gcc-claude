# E2K back end proof of concept: state

Written by Claude (Anthropic) on the branch `claudes-e2k-compiler`, from
the relcc2 specification (`spec/isa`, `spec/abi`, `doc/gcc-port-plan.md`)
to find out what the spec is missing. Not for contribution to GCC (GCC
refuses AI-written code); the owner writes the real port by hand and may
reuse the design. Spec gaps go to relcc2 `docs/spec-poc-findings.md`.

This file is the source of truth for the work; update it with every
commit. Tag `v0.1` marks the state described in "v0.1" below.

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
| Nested-function trampolines | `sorry` (4 torture tests) | A trampoline design: executable stack or not, loading `%g12`; does lcc support GNU nested functions? |
| Nonlocal goto, `__builtin_setjmp`/`longjmp` | compile, crash at run time (920428-2, built-in-setjmp) | Unwinding the chain stack as glibc's `longjmp` does |
| `__builtin_apply` / untyped calls | hangs (pr47237) | Rarely used; probably leave unsupported |
| `-finstrument-functions` | aborts (eeprof-1) | Investigate |
| `-pg` profiling | `sorry` | `mcount` convention (what does lcc do?); gcov untested |
| Inline asm | constraints `r`, `j` (pred), `b`, `t` (CTPR), `I`, `Z` only | lcc's `x` (extended register), `r` = even pair for 16-byte values, more as real code needs them |
| `-march=elbrus-v4..v7` | accepted, but code is always v3 | ISA-dependent patterns (v5 `ldqp`/`stqp` 16-byte atomics, new ops), `e_flags`, v6 timings |
| Runtime libraries | libgcc and libstdc++ only | libatomic, libgomp, libquadmath, sanitizers, libitm (MCST publishes E2K ports of some) |
| Sibling calls | disabled | Tail calls through `ct` after the window is restored |
| Debug info in gdb | `-g` emitted, never tried in gdb | Check backtraces, locals, the made-up return column (DWARF 0) |
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
  --disable-libsanitizer --disable-libquadmath --disable-libgomp \
  --disable-libatomic --disable-libssp --disable-libitm --disable-nls \
  --enable-checking=yes,rtl --disable-werror
make -j10 all-gcc all-target-libgcc all-target-libstdc++-v3
make install-gcc install-target-libgcc install-target-libstdc++-v3
```

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
  other agents work there (keep `-j` about 4).
- Never look at `/opt/mcst/gcc-16.0.0-A.XXX.e2k-v7.5.10` on the host:
  unknown origin, relcc2 decision 4.

## Next

1. Runtime libraries, starting with libatomic (MCST publishes E2K ports;
   use them as reference, minding that they target lcc/EDG).
2. Inline asm: the `x` constraint and even pairs for `r`.
3. Then the rest of "Not done", performance last.
