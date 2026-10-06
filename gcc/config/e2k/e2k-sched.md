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

;; Nondeterministic: a wide instruction takes an operation if some
;; choice of channels fits all of them (the first free channel of a load
;; can leave no room for a store that the exclusions below then forbid).
(automata_option "ndfa")
(define_automaton "e2k_alu,e2k_lit,e2k_ctl,e2k_aau")

(define_cpu_unit "alc0,alc1,alc2,alc3,alc4,alc5" "e2k_alu")
;; The divider in ALC5, shared by fdivs, fdivd, sdivs, sdivd, fsqrts: two
;; divides 1 cycle apart stall, sdivd wants 3 on v3 (spec/isa/timing.md,
;; "Divider").
(define_cpu_unit "divu" "e2k_alu")
;; A load in ALC3 can't share a wide instruction with a store in ALC2,
;; nor a load in ALC0 with a store in ALC5.
(define_cpu_unit "ld0,ld3,st2,st5" "e2k_alu")
(exclusion_set "st2" "ld3")
(exclusion_set "st5" "ld0")

;; The four AAS channels of the array prefetch reads (movas).
(define_cpu_unit "aas0,aas1,aas2,aas3" "e2k_aau")

;; Four 32-bit literal syllables; a 64-bit literal takes two adjacent ones.
(define_cpu_unit "lts0,lts1,lts2,lts3" "e2k_lit")

;; CS0 (disp, return, ibranch), CS1 (setwd, call, wait) and SS (ct,
;; ibranch, call); PLS, predicate logic (one landp, for its fixed @p
;; names).
(define_cpu_unit "cs0,cs1,ss,pls" "e2k_ctl")

(define_reservation "e2k_any6" "alc0|alc1|alc2|alc3|alc4|alc5")
(define_reservation "e2k_c0134" "alc0|alc1|alc3|alc4")
(define_reservation "e2k_c14" "alc1|alc4")
(define_reservation "e2k_cld" "(alc0+ld0)|alc2|(alc3+ld3)|alc5")
(define_reservation "e2k_cst" "(alc2+st2)|(alc5+st5)")
(define_reservation "e2k_lit1" "lts0|lts1|lts2|lts3")
(define_reservation "e2k_lit2" "(lts0+lts1)|(lts1+lts2)|(lts2+lts3)")
(define_reservation "e2k_all"
  "alc0+alc1+alc2+alc3+alc4+alc5+lts0+lts1+lts2+lts3+cs0+cs1+ss+pls")

;; ALU classes, each with 0, 1 or 2 literal syllables.

(define_insn_reservation "e2k_alu0" 1
  (and (eq_attr "type" "alu") (match_test "e2k_insn_lits (insn) == 0")) "e2k_any6")
(define_insn_reservation "e2k_alu1" 1
  (and (eq_attr "type" "alu") (match_test "e2k_insn_lits (insn) == 1")) "e2k_any6+e2k_lit1")
(define_insn_reservation "e2k_alu2" 1
  (and (eq_attr "type" "alu") (match_test "e2k_insn_lits (insn) == 2")) "e2k_any6+e2k_lit2")

(define_insn_reservation "e2k_alu14" 1
  (and (eq_attr "type" "alu14") (match_test "e2k_insn_lits (insn) == 0"))
  "e2k_c14")
(define_insn_reservation "e2k_alu14_1" 1
  (and (eq_attr "type" "alu14") (match_test "e2k_insn_lits (insn) == 1"))
  "e2k_c14+e2k_lit1")
(define_insn_reservation "e2k_alu14_2" 1
  (and (eq_attr "type" "alu14") (match_test "e2k_insn_lits (insn) == 2"))
  "e2k_c14+e2k_lit2")


(define_insn_reservation "e2k_mul0" 4
  (and (eq_attr "type" "mul") (match_test "e2k_insn_lits (insn) == 0")) "e2k_c0134")
(define_insn_reservation "e2k_mul1" 4
  (and (eq_attr "type" "mul") (match_test "e2k_insn_lits (insn) == 1")) "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_mul2" 4
  (and (eq_attr "type" "mul") (match_test "e2k_insn_lits (insn) == 2")) "e2k_c0134+e2k_lit2")

(define_insn_reservation "e2k_div" 11
  (eq_attr "type" "div") "alc5+divu,divu,divu")

(define_insn_reservation "e2k_fp" 4
  (and (eq_attr "type" "fp") (match_test "e2k_insn_lits (insn) == 0"))
  "e2k_c0134")
(define_insn_reservation "e2k_fp_1" 4
  (and (eq_attr "type" "fp") (match_test "e2k_insn_lits (insn) == 1"))
  "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_fp_2" 4
  (and (eq_attr "type" "fp") (match_test "e2k_insn_lits (insn) == 2"))
  "e2k_c0134+e2k_lit2")

;; Combined FP operations (fmul_add): ALC0, 1, 3, 4 on v3, latency 8
;; (spec/isa/timing.md).
(define_insn_reservation "e2k_fma" 8
  (and (eq_attr "type" "fma") (match_test "e2k_insn_lits (insn) == 0"))
  "e2k_c0134")
(define_insn_reservation "e2k_fma_1" 8
  (and (eq_attr "type" "fma") (match_test "e2k_insn_lits (insn) == 1"))
  "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_fma_2" 8
  (and (eq_attr "type" "fma") (match_test "e2k_insn_lits (insn) == 2"))
  "e2k_c0134+e2k_lit2")

(define_insn_reservation "e2k_fcvt" 5
  (and (eq_attr "type" "fcvt")
       (match_test "recog_memoized (insn) != CODE_FOR_truncdfsf2"))
  "e2k_c0134")
;; fdtofs takes 6 (timing.md).
(define_insn_reservation "e2k_fcvt6" 6
  (and (eq_attr "type" "fcvt")
       (match_test "recog_memoized (insn) == CODE_FOR_truncdfsf2"))
  "e2k_c0134")

;; fdivs 11, fsqrts 12, fdivd 14 (timing.md).
(define_insn_reservation "e2k_fdivs" 11
  (and (eq_attr "type" "fdiv")
       (match_test "recog_memoized (insn) == CODE_FOR_divsf3"))
  "alc5+divu,divu")
(define_insn_reservation "e2k_fsqrts" 12
  (and (eq_attr "type" "fdiv")
       (match_test "recog_memoized (insn) == CODE_FOR_sqrtsf2"))
  "alc5+divu,divu")
(define_insn_reservation "e2k_fdiv" 14
  (and (eq_attr "type" "fdiv")
       (match_test "recog_memoized (insn) != CODE_FOR_divsf3
		    && recog_memoized (insn) != CODE_FOR_sqrtsf2"))
  "alc5+divu,divu")

(define_insn_reservation "e2k_cmp0" 2
  (and (eq_attr "type" "cmp") (match_test "e2k_insn_lits (insn) == 0")) "e2k_c0134")
(define_insn_reservation "e2k_cmp1" 2
  (and (eq_attr "type" "cmp") (match_test "e2k_insn_lits (insn) == 1")) "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_cmp2" 2
  (and (eq_attr "type" "cmp") (match_test "e2k_insn_lits (insn) == 2")) "e2k_c0134+e2k_lit2")

(define_insn_reservation "e2k_fcmp" 4
  (and (eq_attr "type" "fcmp") (match_test "e2k_insn_lits (insn) == 0"))
  "e2k_c0134")
(define_insn_reservation "e2k_fcmp_1" 4
  (and (eq_attr "type" "fcmp") (match_test "e2k_insn_lits (insn) == 1"))
  "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_fcmp_2" 4
  (and (eq_attr "type" "fcmp") (match_test "e2k_insn_lits (insn) == 2"))
  "e2k_c0134+e2k_lit2")

;; Packed integer operations (e2k-vect.md): 1 cycle to packed and FP
;; operations, 2 for the multiplies and psadbw (spec/isa/timing.md).
(define_insn_reservation "e2k_pint" 1
  (and (eq_attr "type" "pint") (match_test "e2k_insn_lits (insn) == 0"))
  "alc0|alc3")
(define_insn_reservation "e2k_pint_1" 1
  (and (eq_attr "type" "pint") (match_test "e2k_insn_lits (insn) == 1"))
  "(alc0|alc3)+e2k_lit1")
(define_insn_reservation "e2k_pint_2" 1
  (and (eq_attr "type" "pint") (match_test "e2k_insn_lits (insn) == 2"))
  "(alc0|alc3)+e2k_lit2")
(define_insn_reservation "e2k_pint14" 1
  (and (eq_attr "type" "pint14") (match_test "e2k_insn_lits (insn) == 0"))
  "e2k_c14")
(define_insn_reservation "e2k_pint14_1" 1
  (and (eq_attr "type" "pint14") (match_test "e2k_insn_lits (insn) == 1"))
  "e2k_c14+e2k_lit1")
(define_insn_reservation "e2k_pint14_2" 1
  (and (eq_attr "type" "pint14") (match_test "e2k_insn_lits (insn) == 2"))
  "e2k_c14+e2k_lit2")
(define_insn_reservation "e2k_pmul" 2
  (and (eq_attr "type" "pmul") (match_test "e2k_insn_lits (insn) == 0"))
  "e2k_c14")
(define_insn_reservation "e2k_pmul_1" 2
  (and (eq_attr "type" "pmul") (match_test "e2k_insn_lits (insn) == 1"))
  "e2k_c14+e2k_lit1")
(define_insn_reservation "e2k_pmul_2" 2
  (and (eq_attr "type" "pmul") (match_test "e2k_insn_lits (insn) == 2"))
  "e2k_c14+e2k_lit2")
(define_insn_reservation "e2k_pany0" 1
  (and (eq_attr "type" "pany") (match_test "e2k_insn_lits (insn) == 0")) "e2k_c0134")
(define_insn_reservation "e2k_pany1" 1
  (and (eq_attr "type" "pany") (match_test "e2k_insn_lits (insn) == 1")) "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_pany2" 1
  (and (eq_attr "type" "pany") (match_test "e2k_insn_lits (insn) == 2")) "e2k_c0134+e2k_lit2")

;; Array prefetch: a mova's result reaches any consumer at 5, in any
;; channel or cluster; the AAU register writes go in ALC2/5, bap in SS
;; (spec/isa/apb.md).
(define_insn_reservation "e2k_mova" 5
  (eq_attr "type" "mova") "aas0|aas1|aas2|aas3")
(define_insn_reservation "e2k_aau" 1
  (eq_attr "type" "aau") "alc2|alc5")
(define_insn_reservation "e2k_bap" 1
  (eq_attr "type" "bap") "ss")

;; Predicate logic: 3 to a ct, 2 to a predicated operation.
(define_insn_reservation "e2k_plog" 3
  (eq_attr "type" "plog") "pls")

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
;; (gcc.dg/torture/pr57425-1.c).  Both take CS1, which holds their MAS
;; (gas: "cannot encode MAS: CS1 syllable is busy" next to a wait or a
;; call).
(define_insn_reservation "e2k_ldlock0" 3
  (and (eq_attr "type" "ldlock") (match_test "e2k_insn_lits (insn) == 0"))
  "alc0+ld0+alc2+alc5+cs1")
(define_insn_reservation "e2k_ldlock1" 3
  (and (eq_attr "type" "ldlock") (match_test "e2k_insn_lits (insn) == 1"))
  "alc0+ld0+alc2+alc5+cs1+e2k_lit1")
(define_insn_reservation "e2k_ldlock2" 3
  (and (eq_attr "type" "ldlock") (match_test "e2k_insn_lits (insn) == 2"))
  "alc0+ld0+alc2+alc5+cs1+e2k_lit2")
(define_insn_reservation "e2k_ldchk0" 1
  (and (eq_attr "type" "ldchk") (match_test "e2k_insn_lits (insn) == 0"))
  "alc2+alc5+cs0+cs1+ss")
(define_insn_reservation "e2k_ldchk1" 1
  (and (eq_attr "type" "ldchk") (match_test "e2k_insn_lits (insn) == 1"))
  "alc2+alc5+cs0+cs1+ss+e2k_lit1")
(define_insn_reservation "e2k_ldchk2" 1
  (and (eq_attr "type" "ldchk") (match_test "e2k_insn_lits (insn) == 2"))
  "alc2+alc5+cs0+cs1+ss+e2k_lit2")

(define_insn_reservation "e2k_store0" 1
  (and (eq_attr "type" "store") (match_test "e2k_insn_lits (insn) == 0")) "e2k_cst")
(define_insn_reservation "e2k_store1" 1
  (and (eq_attr "type" "store") (match_test "e2k_insn_lits (insn) == 1")) "e2k_cst+e2k_lit1")
(define_insn_reservation "e2k_store2" 1
  (and (eq_attr "type" "store") (match_test "e2k_insn_lits (insn) == 2")) "e2k_cst+e2k_lit2")

(define_insn_reservation "e2k_getsp" 2
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
  (and (eq_attr "type" "setwd")
       (match_test "recog_memoized (insn) != CODE_FOR_e2k_setwd"))
  "e2k_all")
;; The prologue's setwd (with setbn) takes CS1 and LTS0, which holds its
;; wsz, nfx and dbl (spec/isa/bundle.md, "CS1"); the rest of its wide
;; instruction is free (e2k_adjust_cost).
(define_insn_reservation "e2k_setwd_entry" 1
  (and (eq_attr "type" "setwd")
       (match_test "recog_memoized (insn) == CODE_FOR_e2k_setwd"))
  "cs1+lts0")
(define_insn_reservation "e2k_multi" 4
  (eq_attr "type" "multi") "e2k_all")
(define_insn_reservation "e2k_raw" 6
  (eq_attr "type" "raw") "e2k_all")
(define_insn_reservation "e2k_nop" 1
  (eq_attr "type" "nop") "e2k_all")
(define_insn_reservation "e2k_ghost" 0
  (eq_attr "type" "ghost") "nothing")

;; FP-class results reach integer operations two cycles later.
(define_bypass 6 "e2k_fp,e2k_fp_1,e2k_fp_2,e2k_mul0,e2k_mul1,e2k_mul2"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_alu14,e2k_alu14_1,e2k_alu14_2,
   e2k_cmp0,e2k_cmp1,e2k_cmp2,
   e2k_load0,e2k_load1,e2k_load2")
(define_bypass 6 "e2k_fcvt"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_alu14,e2k_alu14_1,e2k_alu14_2,
   e2k_cmp0,e2k_cmp1,e2k_cmp2,
   e2k_load0,e2k_load1,e2k_load2")
(define_bypass 7 "e2k_fcvt6"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_alu14,e2k_alu14_1,e2k_alu14_2,
   e2k_cmp0,e2k_cmp1,e2k_cmp2,
   e2k_load0,e2k_load1,e2k_load2")
;; Packed results reach integer operations at 4.
(define_bypass 4 "e2k_pint,e2k_pint_1,e2k_pint_2,e2k_pint14,e2k_pint14_1,e2k_pint14_2,
		  e2k_pmul,e2k_pmul_1,e2k_pmul_2,e2k_pany0,e2k_pany1,e2k_pany2"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_alu14,e2k_alu14_1,e2k_alu14_2,
   e2k_cmp0,e2k_cmp1,e2k_cmp2,
   e2k_load0,e2k_load1,e2k_load2")
;; Compare -> predicate logic, and predicate logic chained through a
;; %pred: 1; predicate logic -> an operation under its predicate: 2
;; (spec/isa/timing.md).
(define_bypass 1 "e2k_cmp0,e2k_cmp1,e2k_cmp2" "e2k_plog")
(define_bypass 1 "e2k_plog" "e2k_plog")
(define_bypass 2 "e2k_plog"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_alu14,e2k_alu14_1,e2k_alu14_2,
   e2k_load0,e2k_load1,e2k_load2")
;; Compare -> ibranch on its predicate.
(define_bypass 3 "e2k_cmp0,e2k_cmp1,e2k_cmp2" "e2k_branch")
(define_bypass 5 "e2k_fcmp,e2k_fcmp_1,e2k_fcmp_2" "e2k_branch")
