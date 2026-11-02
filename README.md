# GCC for Elbrus (E2K): an AI-written proof of concept

This branch (`claudes-e2k-compiler`) is GCC's development tree of
2026-10-13 plus a backend for MCST's Elbrus (E2K) VLIW architecture.
The backend was written by Claude, Anthropic's AI model, at the request
of the [relcc2](https://github.com/OpenE2K/relcc2) project. relcc2
writes down the E2K ISA and ABI; this backend was built from that
specification to find out what it gets wrong or leaves out.

**It is research material, not a contribution.** It is heavily
AI-written, and GCC does not accept AI-generated code, so nothing here
is meant for upstream GCC. In the relcc2 owner's words: "you can bite
me if I send anything from it to upstream."

GCC's own README is `README`.

## What is whose

- **Claude:**
  - everything under `gcc/config/e2k/` and `gcc/common/config/e2k/`;
  - the e2k parts of `gcc/config.gcc`, `gcc/configure.ac`,
    `gcc/configure` and `libgcc/config.host`;
  - the changes to `libgcc/config/e2k/` after its import.
- **MCST:**
  - `libgcc/config/e2k/` as first committed: imported verbatim, in a
    commit of its own, from the GPL runtime sources MCST publishes with
    lcc 1.29.16 (`internal-lcc-libs-open-source`). The unwinder walks
    the chain stack instead of interpreting CFI.
  - The e2k parts of `libgcc/unwind.inc` come from the same sources,
    ported to the mainline tree.

`gcc/config/e2k/README.claude` says the same in GCC's style.

## What it does

- 64-bit unprotected mode (`e2k64`) only.
- `-march=elbrus-v3` (the default, forward compatible) to `elbrus-v7`.
- CPU names: `elbrus-4c`, `-8c`, `-8c2`, `-1c+`, `-2c3`, `-12c`,
  `-16c`, `-48c`, `-8v7`.
- C, C++, Fortran and LTO.
- It follows lcc's ABI, which relcc2 checks code from both compilers
  against.

It schedules into wide instructions itself. It uses loop mode, array
prefetch, predication, speculation and 16-byte vectors on v5 and later.
It also has lcc-compatible `__builtin_e2k_*` builtins and
`<e2kintrin.h>`, plus DWARF that MCST's gdb reads.

Results at v0.6 (2026-10-29), on an Elbrus-4C (v3) and an Elbrus-8C2
(v5):

| Test | Result |
|---|---|
| ABI compatibility with lcc (relcc2's suite, 1,931 tests per pair, both directions) | no unexpected failures on the 4C and the 8C2 (and on the 2C3 when last run there, 2026-10-13) |
| Native bootstrap (C, C++, LTO) | passes on the 4C and the 8C2 |
| GCC's testsuite on the 8C2, without the gdb tests | gcc: 165,390 expected passes, 471 unexpected failures; g++: 267,644 and 77 |
| glibc 2.35's testsuite, glibc built by this compiler | 8C2: 3,379 PASS, 694 FAIL (lcc's build: 2,842 / 1,140) |
| A system built by it alone (MCST's Linux and glibc, binutils, gdb, this GCC, busybox) | boots on the 8C2 |

Since v0.6 it has built 2,563 of the 2,640 source packages of OS
Elbrus 9.5.5 from MCST's package kit, fixing the bugs that turned up.

`gcc/config/e2k/STATUS.claude.md` is the full record: the results of
each version, every change and the bug behind it, the design and its
pitfalls, and how to build and test.

## Building

You need MCST's binutils
([OpenE2K/binutils-gdb](https://github.com/OpenE2K/binutils-gdb)) and a
sysroot with MCST's glibc: an lcc cross compiler's, or
[OpenE2K/glibc](https://github.com/OpenE2K/glibc) built by this
compiler. Then configure with `--target=e2k-linux-gnu`.

- The configure line is in `STATUS.claude.md` under "Build and test".
- relcc2's `tools/gcc-native/cross.sh` builds and packs a complete
  x86_64-hosted cross toolchain.

## Licence

As GCC: GPL version 3 or later, with the GCC Runtime Library Exception
for the runtime libraries. MCST's files keep their copyright notices.
