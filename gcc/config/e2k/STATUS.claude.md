# Status of the experimental E2K back end (written by Claude)

Source of truth for this work; update it with every commit.

## Purpose

The owner asked Claude to write a barebones GCC back end from the relcc2
specification, to learn what the spec is missing. Not for contribution to
GCC (GCC refuses AI-written code); the owner may reuse the design. Spec
gaps go to relcc2 `docs/spec-poc-findings.md` (another agent folds them
into `spec/`). Spec commit used: relcc2 `c556801`.

Scope chosen by the owner: GCC, everything including bundling.

## Layout

| Path | What |
|---|---|
| relcc2 `toolchains/gcc-claude` | this worktree, branch `claudes-e2k-compiler` (git identity "Claude (Opus 5.5)", worktree-local config) |
| relcc2 `toolchains/build-gcc-claude` | build directory (`make -j10 all-gcc`) |
| relcc2 `toolchains/claude-e2k/scratch/gcc-e2k` | wrapper: `xgcc -B<build>/gcc/` |
| relcc2 `toolchains/claude-e2k/compat-v3` | last compat-suite run |
| relcc2 `docs/spec-poc-findings.md` | spec findings (not committed by Claude) |

Do not look at `/opt/mcst/gcc-16.0.0-A.XXX.e2k-v7.5.10` on the host: its
origin is unknown, and relcc2 decision 4 rules out unpublished MCST
material.

## Build and test

```
cd toolchains/build-gcc-claude && make -j10 all-gcc
G=toolchains/claude-e2k/scratch/gcc-e2k
L=/opt/mcst/lcc-1.29.16.e2k-v3.linux-6.1
$G -O2 -c t.c && $L/bin/lcc t.o -o t && qemu-e2k -cpu elbrus-v3 -L $L/fs ./t
python3 tools/abi/compat/run.py toolchains/compat/gen --target v3 \
  --cc gcc="$G -O2 -std=gnu17" --pairs lcc:gcc,gcc:lcc,gcc:gcc \
  -o toolchains/claude-e2k/compat-v3 -j8
```

`-std=gnu17`: GCC 17 defaults to C23, where `f()` has no parameters, and
the `unproto` unit needs K&R calls. Linking is done by lcc (libgcc, crt,
glibc from its sysroot); no libgcc is built here.

## Design summary

- Hard registers: 0–31 `%g`, 32–95 `%r0..63` (window, call-saved by
  hardware, `LOCAL_REGNO`), 96–103 `%b[0..7]` (outgoing args/results),
  104–135 `%pred`, 136–138 `%ctpr1..3`, 139 soft FP, 140 soft AP.
  `%r8` = stack pointer copy (written by the prologue's `getsp`), `%r9` =
  hard frame pointer when needed, `%g13` TP (fixed), `%g24..31` fixed
  (rotating), `%g12` static chain, `%g11` caller-side buffer address for
  results over 64 bytes.
- Window: computed at final time by scanning hard registers
  (`e2k_compute_window`): W = pairs up to the highest `%r` used; if any
  `%b` or call, `setbn rbs=W, rsz=3` and `wsz=W+4`, calls use `wbs=W`;
  else `wsz=max(W,4)`. `setwd ..., nfx=1, dbl=0` alone in the first wide
  instruction.
- Frame: `getsp -(locals+outgoing)` into `%r8` when there is a frame or
  `%r8` is used; FRAME_GROWS_DOWNWARD; AP = FP = entry USD.
  `ACCUMULATE_OUTGOING_ARGS`, `REG_PARM_STACK_SPACE` = 64 (or the result
  size if > 64), `STACK_PARMS_IN_REG_PARM_AREA`.
- Arguments: 8-byte slots, >8 bytes at even slots, slots 0–7 in regs;
  aggregates/complex as PARALLEL of DI pieces (last piece SI if ≤ 4
  bytes). Variadic (last named + unnamed) and unprototyped args returned
  as PARALLEL with a null first element (register and memory).
  Narrow integers: caller promotes to DI; callee sees the natural mode and
  re-extends (flag `e2k_laying_out_parms`). PROMOTE_MODE → DImode.
- Results ≤ 64 bytes in `%r0..7`/`%b[0..7]`; > 64 bytes: callee builds in
  a local buffer (`struct_value_rtx` incoming) and the epilogue copies it
  to the entry USD; the caller's call expander copies from its USD to the
  buffer whose address GCC put in `%g11`.
- Calls: `disp %ctpr1` (or `movtd`) as a separate insn, then `call
  %ctpr1, wbs=W`. Return: `return %ctpr3` (hoistable) + `ct %ctpr3`.
- Compares: fused compare+branch / cstore / movcc insns with a BImode
  scratch, split after reload into `cmp*b` + `ibranch ? [~]%pred` /
  `merge`. Integer ne/gt/ge invert; FP gt/ge swap.
- long double (XFmode): register pair (mantissa, 16-bit sign+exponent);
  arithmetic is one insn that does `movif`, the `fx*` op, `movfi`.
  `__float128` (TFmode): libgcc calls. `__int128`: register pair.
- PIC: pseudo GOT register, `rrd %ip` + `_GLOBAL_OFFSET_TABLE_` literal in
  one wide instruction; `@GOT` / `@GOTOFF`. TLS: GD (`__tls_get_addr(mod,
  off)`), IE, LE.
- Scheduling and bundling: `TARGET_DELAY_SCHED2`; `e2k_reorg` runs
  `schedule_ebbs`, then `e2k_gen_bundles` marks wide instructions (new
  cycle, or after a call/jump/multi insn/asm) and `nop N` gaps; braces
  are printed by `FINAL_PRESCAN_INSN` / `TARGET_ASM_FINAL_POSTSCAN_INSN`.
  `%#` in a template starts a new wide instruction; `%<`/`%>` brace ops
  that must share one when not bundling. DFA in `e2k-sched.md` (channels
  from binutils-ops.yaml, latencies from timing.md, literal syllables
  via `e2k_insn_lits`). `-mno-bundle` prints one op per line.

## State (update with each commit)

- Builds (`all-gcc`). Hello world with qsort, recursion and varargs
  printf (double, long double) runs under qemu-e2k v3.
- Compat suite (C units, 1,683 tests per pair, lcc 1.29.16 v3, MCST
  qemu `-cpu elbrus-v3`): **0 unexpected failures** for lcc->gcc,
  gcc->lcc and gcc->gcc at -O0, -O1 and -O2. The C++ `eh` unit is not
  run (no C++ front end built).
- Compat suite on the Elbrus 4C (`--remote claude@ringo.lan`, -O2): 0
  unexpected failures in all three pairs.
- gcc.c-torture/execute under qemu v3 (runner:
  relcc2 `toolchains/claude-e2k/torture/run.sh`, links with lcc): all
  1,646 applicable tests pass at -O0, -O1, -O2, -O3; 52 unsupported
  (trampolines, label values, DFP, return address, x86-only).
  `20101011-1` (SIGFPE on divide by zero) only runs on hardware: MCST
  qemu can't deliver the exception; passes on the 4C.
- On the 4C (hardware is the reference; MCST qemu next, community qemu
  last): torture at -O0/-O2/-O3 all 1,639 built tests pass; -O2 -fPIC all
  but 20000603-1 (DR 236 type aliasing, GCC generic). Runner:
  `toolchains/claude-e2k/torture/hw.sh NAME "OPTS"`.
- PIC/TLS: relcc2 `tools/abi/probes/dso` sources built by this GCC (PIE,
  non-PIE, static, mixed with lcc) pass on the 4C, lazy and BIND_NOW.
- Divides clobber `%ctpr2` so RTL PRE can't hoist a trapping division
  above a call (pr38819). PIC tablejump adds the table address.
- Atomics: CAS, exchange, fetch_{add,sub,and,or,xor} for 1/2/4/8 bytes
  as lcc's lock-wait/wait-unlock loops (type "raw" insns that print their
  own braces); loads/stores/fences with `wait` per atomics.md; 16 bytes
  through libatomic. Threaded test mixed with lcc passes on the 4C
  (`toolchains/claude-e2k/atomics`).
- Scheduler: `TARGET_SCHED_EXPOSED_PIPELINE` and output deps cost >= 1,
  because operations in one wide instruction all read the old registers.
- Bugs found on the way (fixed): `sxt` bit 2 means zero extension (the
  guide says the opposite), DEFAULT_PCC_STRUCT_RETURN must be 0, the
  >64-byte result buffer needed an opaque address (dse1 deleted stores
  into it), callee re-extension of narrow args, `getsp` missing when only
  incoming stack args use `%r8`, PROMOTE_MODE must agree with
  promote_function_mode.

## Next

1. Inline asm constraints; gcc.dg execute tests; performance vs lcc on the 4C.
2. Atomics (lock-wait load / wait-unlock store), C++/EH, sibcalls,
   predication (cond_exec), clusters in the DFA.
3. Keep `docs/spec-poc-findings.md` current.
