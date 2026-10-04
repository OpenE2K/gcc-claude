;; Pipeline description for E2K v1-v5 (measured on an Elbrus 4C, v3).
;; Written by Claude (Anthropic) as an experiment; see README.claude.
;;
;; Channels per operation come from spec/isa/binutils-ops.yaml,
;; latencies from spec/isa/timing.md, the store/load exclusions from
;; spec/isa/bundle.md "Bundling restrictions".  One cycle is one wide
;; instruction.
;;
;; This file is part of GCC.
;;
;; GCC is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

(define_automaton "e2k_alu,e2k_lit,e2k_ctl")

(define_cpu_unit "alc0,alc1,alc2,alc3,alc4,alc5" "e2k_alu")
;; A load in ALC3 can't share a wide instruction with a store in ALC2,
;; nor a load in ALC0 with a store in ALC5.
(define_cpu_unit "ld0,ld3,st2,st5" "e2k_alu")
(exclusion_set "st2" "ld3")
(exclusion_set "st5" "ld0")

;; Four 32-bit literal syllables; a 64-bit literal takes two adjacent ones.
(define_cpu_unit "lts0,lts1,lts2,lts3" "e2k_lit")

;; CS0 (disp, return, ibranch), CS1 (setwd, call, wait) and SS (ct,
;; ibranch, call).
(define_cpu_unit "cs0,cs1,ss" "e2k_ctl")

(define_reservation "e2k_any6" "alc0|alc1|alc2|alc3|alc4|alc5")
(define_reservation "e2k_c0134" "alc0|alc1|alc3|alc4")
(define_reservation "e2k_c14" "alc1|alc4")
(define_reservation "e2k_c5" "alc5")
(define_reservation "e2k_cld" "(alc0+ld0)|alc2|(alc3+ld3)|alc5")
(define_reservation "e2k_cst" "(alc2+st2)|(alc5+st5)")
(define_reservation "e2k_lit1" "lts0|lts1|lts2|lts3")
(define_reservation "e2k_lit2" "(lts0+lts1)|(lts1+lts2)|(lts2+lts3)")
(define_reservation "e2k_all"
  "alc0+alc1+alc2+alc3+alc4+alc5+lts0+lts1+lts2+lts3+cs0+cs1+ss")

;; ALU classes, each with 0, 1 or 2 literal syllables.

(define_insn_reservation "e2k_alu0" 1
  (and (eq_attr "type" "alu") (match_test "e2k_insn_lits (insn) == 0")) "e2k_any6")
(define_insn_reservation "e2k_alu1" 1
  (and (eq_attr "type" "alu") (match_test "e2k_insn_lits (insn) == 1")) "e2k_any6+e2k_lit1")
(define_insn_reservation "e2k_alu2" 1
  (and (eq_attr "type" "alu") (match_test "e2k_insn_lits (insn) == 2")) "e2k_any6+e2k_lit2")

(define_insn_reservation "e2k_alu14" 1
  (eq_attr "type" "alu14") "e2k_c14")

(define_insn_reservation "e2k_mul0" 4
  (and (eq_attr "type" "mul") (match_test "e2k_insn_lits (insn) == 0")) "e2k_c0134")
(define_insn_reservation "e2k_mul1" 4
  (and (eq_attr "type" "mul") (match_test "e2k_insn_lits (insn) == 1")) "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_mul2" 4
  (and (eq_attr "type" "mul") (match_test "e2k_insn_lits (insn) == 2")) "e2k_c0134+e2k_lit2")

(define_insn_reservation "e2k_div" 11
  (eq_attr "type" "div") "e2k_c5")

(define_insn_reservation "e2k_fp" 4
  (eq_attr "type" "fp") "e2k_c0134")

(define_insn_reservation "e2k_fcvt" 5
  (eq_attr "type" "fcvt") "e2k_c0134")

(define_insn_reservation "e2k_fdiv" 14
  (eq_attr "type" "fdiv") "e2k_c5")

(define_insn_reservation "e2k_cmp0" 2
  (and (eq_attr "type" "cmp") (match_test "e2k_insn_lits (insn) == 0")) "e2k_c0134")
(define_insn_reservation "e2k_cmp1" 2
  (and (eq_attr "type" "cmp") (match_test "e2k_insn_lits (insn) == 1")) "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_cmp2" 2
  (and (eq_attr "type" "cmp") (match_test "e2k_insn_lits (insn) == 2")) "e2k_c0134+e2k_lit2")

(define_insn_reservation "e2k_fcmp" 4
  (eq_attr "type" "fcmp") "e2k_c0134")

(define_insn_reservation "e2k_load0" 3
  (and (eq_attr "type" "load") (match_test "e2k_insn_lits (insn) == 0")) "e2k_cld")
(define_insn_reservation "e2k_load1" 3
  (and (eq_attr "type" "load") (match_test "e2k_insn_lits (insn) == 1")) "e2k_cld+e2k_lit1")
(define_insn_reservation "e2k_load2" 3
  (and (eq_attr "type" "load") (match_test "e2k_insn_lits (insn) == 2")) "e2k_cld+e2k_lit2")

;; A lock load must be in ALC0 (or ALC3; the port prints ALC0).  It also
;; takes ALC2 and ALC5, the store channels, so that no store shares its
;; wide instruction: whether such a store would remove the new entry is
;; not known.  A check load must be in ALC5 (or ALC2) and costs its
;; consumers nothing beyond the lock's latency (measured on the 4C); its
;; rbranch takes CS0 and SS like an ibranch.  It takes ALC2 too, so no
;; store shares its instruction either: a check that reloaded returned
;; the value of a store later in its own wide instruction
;; (gcc.dg/torture/pr57425-1.c).
(define_insn_reservation "e2k_ldlock0" 3
  (and (eq_attr "type" "ldlock") (match_test "e2k_insn_lits (insn) == 0"))
  "alc0+ld0+alc2+alc5")
(define_insn_reservation "e2k_ldlock1" 3
  (and (eq_attr "type" "ldlock") (match_test "e2k_insn_lits (insn) == 1"))
  "alc0+ld0+alc2+alc5+e2k_lit1")
(define_insn_reservation "e2k_ldlock2" 3
  (and (eq_attr "type" "ldlock") (match_test "e2k_insn_lits (insn) == 2"))
  "alc0+ld0+alc2+alc5+e2k_lit2")
(define_insn_reservation "e2k_ldchk0" 1
  (and (eq_attr "type" "ldchk") (match_test "e2k_insn_lits (insn) == 0"))
  "alc2+alc5+cs0+ss")
(define_insn_reservation "e2k_ldchk1" 1
  (and (eq_attr "type" "ldchk") (match_test "e2k_insn_lits (insn) == 1"))
  "alc2+alc5+cs0+ss+e2k_lit1")
(define_insn_reservation "e2k_ldchk2" 1
  (and (eq_attr "type" "ldchk") (match_test "e2k_insn_lits (insn) == 2"))
  "alc2+alc5+cs0+ss+e2k_lit2")

(define_insn_reservation "e2k_store0" 1
  (and (eq_attr "type" "store") (match_test "e2k_insn_lits (insn) == 0")) "e2k_cst")
(define_insn_reservation "e2k_store1" 1
  (and (eq_attr "type" "store") (match_test "e2k_insn_lits (insn) == 1")) "e2k_cst+e2k_lit1")
(define_insn_reservation "e2k_store2" 1
  (and (eq_attr "type" "store") (match_test "e2k_insn_lits (insn) == 2")) "e2k_cst+e2k_lit2")

(define_insn_reservation "e2k_getsp" 1
  (eq_attr "type" "getsp") "alc0+e2k_lit1")

;; binutils-ops.yaml lists ALC0,1,3,4 for movtd, but gas accepts movtd to
;; %ctpr1-3 only in ALC0 (tc-e2k.c).
(define_insn_reservation "e2k_movctp" 9
  (eq_attr "type" "movctp") "alc0")

;; Control.
(define_insn_reservation "e2k_disp" 5
  (eq_attr "type" "disp") "cs0")
(define_insn_reservation "e2k_ret" 6
  (eq_attr "type" "ret") "cs0")
(define_insn_reservation "e2k_branch" 1
  (eq_attr "type" "branch") "cs0+ss")
(define_insn_reservation "e2k_ct" 1
  (eq_attr "type" "ct") "ss")
(define_insn_reservation "e2k_call" 1
  (eq_attr "type" "call") "cs1+ss")
(define_insn_reservation "e2k_wait" 1
  (eq_attr "type" "wait") "cs1")
(define_insn_reservation "e2k_setwd" 1
  (eq_attr "type" "setwd") "e2k_all")
(define_insn_reservation "e2k_multi" 4
  (eq_attr "type" "multi") "e2k_all")
(define_insn_reservation "e2k_raw" 6
  (eq_attr "type" "raw") "e2k_all")
(define_insn_reservation "e2k_nop" 1
  (eq_attr "type" "nop") "e2k_all")
(define_insn_reservation "e2k_ghost" 0
  (eq_attr "type" "ghost") "nothing")

;; FP-class results reach integer operations two cycles later.
(define_bypass 6 "e2k_fp,e2k_mul0,e2k_mul1,e2k_mul2"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_cmp0,e2k_cmp1,e2k_cmp2,e2k_load0,e2k_load1,e2k_load2")
(define_bypass 6 "e2k_fcvt"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_cmp0,e2k_cmp1,e2k_cmp2,e2k_load0,e2k_load1,e2k_load2")
;; Compare -> ibranch on its predicate.
(define_bypass 3 "e2k_cmp0,e2k_cmp1,e2k_cmp2" "e2k_branch")
(define_bypass 5 "e2k_fcmp" "e2k_branch")
