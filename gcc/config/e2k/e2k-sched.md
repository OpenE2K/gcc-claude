;; Pipeline description for E2K v1-v5 (measured on an Elbrus 4C, v3),
;; with v6's latencies under E2K_LAT6 (measured on an Elbrus-2C3).
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
;; divides 1 cycle apart stall, sdivd wants 3 on v3 and v4, 2 from v5 on
;; (spec/isa/timing.md, "Divider").
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
;; CS1 holds the MASes of the loads and stores in ALC0, 2, 3 and 5 at
;; once, and then nothing else (spec/isa/bundle.md, "Bundling
;; restrictions"): an operation with a MAS takes its channel's field.
(define_cpu_unit "mas0,mas2,mas3,mas5" "e2k_ctl")
(exclusion_set "cs1" "mas0,mas2,mas3,mas5")
;; A lock load and a check load keep stores out of their wide
;; instruction (e2k_ldlock0).
(define_cpu_unit "nost0,nost5" "e2k_alu")
(exclusion_set "st2,st5" "nost0,nost5")

(define_reservation "e2k_any6" "alc0|alc1|alc2|alc3|alc4|alc5")
(define_reservation "e2k_c0134" "alc0|alc1|alc3|alc4")
(define_reservation "e2k_c14" "alc1|alc4")
(define_reservation "e2k_cld" "(alc0+ld0)|alc2|(alc3+ld3)|alc5")
(define_reservation "e2k_cst" "(alc2+st2)|(alc5+st5)")
(define_reservation "e2k_cld_mas"
  "(alc0+ld0+mas0)|(alc2+mas2)|(alc3+ld3+mas3)|(alc5+mas5)")
(define_reservation "e2k_cst_mas" "(alc2+st2+mas2)|(alc5+st5+mas5)")
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

;; puttagd (lcc's builtin) in ALC2 or ALC5.
(define_insn_reservation "e2k_alu25" 1
  (eq_attr "type" "alu25") "alc2|alc5")

(define_insn_reservation "e2k_alu0134" 1
  (and (eq_attr "type" "alu0134") (match_test "e2k_insn_lits (insn) == 0"))
  "e2k_c0134")
(define_insn_reservation "e2k_alu0134_1" 1
  (and (eq_attr "type" "alu0134") (match_test "e2k_insn_lits (insn) == 1"))
  "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_alu0134_2" 1
  (and (eq_attr "type" "alu0134") (match_test "e2k_insn_lits (insn) == 2"))
  "e2k_c0134+e2k_lit2")

(define_insn_reservation "e2k_mul0" 4
  (and (eq_attr "type" "mul") (match_test "e2k_insn_lits (insn) == 0")) "e2k_c0134")
(define_insn_reservation "e2k_mul1" 4
  (and (eq_attr "type" "mul") (match_test "e2k_insn_lits (insn) == 1")) "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_mul2" 4
  (and (eq_attr "type" "mul") (match_test "e2k_insn_lits (insn) == 2")) "e2k_c0134+e2k_lit2")

;; Integer divides take 13 cycles plus one per 8 bits of quotient (13
;; below 256, 19 at 55 bits; 4C and 8C2, findings I24); 15 covers
;; quotients below 2^24 without the 4-cycle stall of an early consumer.
(define_insn_reservation "e2k_div" 15
  (and (eq_attr "type" "div")
       (match_test "e2k_arch < 5 && e2k_div64_p (insn)"))
  "alc5+divu,divu,divu")
(define_insn_reservation "e2k_div2" 15
  (and (eq_attr "type" "div")
       (match_test "e2k_arch >= 5 || !e2k_div64_p (insn)"))
  "alc5+divu,divu")

(define_insn_reservation "e2k_fp" 4
  (and (eq_attr "type" "fp")
       (match_test "e2k_arch < 4 && e2k_insn_lits (insn) == 0"))
  "e2k_c0134")
(define_insn_reservation "e2k_fp_1" 4
  (and (eq_attr "type" "fp")
       (match_test "e2k_arch < 4 && e2k_insn_lits (insn) == 1"))
  "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_fp_2" 4
  (and (eq_attr "type" "fp")
       (match_test "e2k_arch < 4 && e2k_insn_lits (insn) == 2"))
  "e2k_c0134+e2k_lit2")
;; v4 added FP add, subtract and multiply (scalar and packed) and the
;; combined FP operations in ALC2 and ALC5: six a cycle, with the same
;; latencies (spec/isa/timing.md, "Elbrus-8C2").
(define_insn_reservation "e2k_fp6" 4
  (and (eq_attr "type" "fp")
       (match_test "e2k_arch >= 4 && e2k_insn_lits (insn) == 0"))
  "e2k_any6")
(define_insn_reservation "e2k_fp6_1" 4
  (and (eq_attr "type" "fp")
       (match_test "e2k_arch >= 4 && e2k_insn_lits (insn) == 1"))
  "e2k_any6+e2k_lit1")
(define_insn_reservation "e2k_fp6_2" 4
  (and (eq_attr "type" "fp")
       (match_test "e2k_arch >= 4 && e2k_insn_lits (insn) == 2"))
  "e2k_any6+e2k_lit2")

;; Combined FP operations (fmul_add): ALC0, 1, 3, 4 on v3, latency 8
;; (spec/isa/timing.md).
(define_insn_reservation "e2k_fma" 8
  (and (eq_attr "type" "fma")
       (match_test "e2k_arch < 4 && e2k_insn_lits (insn) == 0"))
  "e2k_c0134")
(define_insn_reservation "e2k_fma_1" 8
  (and (eq_attr "type" "fma")
       (match_test "e2k_arch < 4 && e2k_insn_lits (insn) == 1"))
  "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_fma_2" 8
  (and (eq_attr "type" "fma")
       (match_test "e2k_arch < 4 && e2k_insn_lits (insn) == 2"))
  "e2k_c0134+e2k_lit2")
(define_insn_reservation "e2k_fma6" 8
  (and (eq_attr "type" "fma")
       (match_test "e2k_arch >= 4 && e2k_insn_lits (insn) == 0"))
  "e2k_any6")
(define_insn_reservation "e2k_fma6_1" 8
  (and (eq_attr "type" "fma")
       (match_test "e2k_arch >= 4 && e2k_insn_lits (insn) == 1"))
  "e2k_any6+e2k_lit1")
(define_insn_reservation "e2k_fma6_2" 8
  (and (eq_attr "type" "fma")
       (match_test "e2k_arch >= 4 && e2k_insn_lits (insn) == 2"))
  "e2k_any6+e2k_lit2")

;; Fused multiply-add (v6): 5 cycles through any operand, six a cycle
;; (spec/isa/timing.md, "Elbrus-2C3 (v6)").
(define_insn_reservation "e2k_ffma" 5
  (eq_attr "type" "ffma") "e2k_any6")

;; Conversions take 4 to a consumer that reads their result in the
;; format they produce (fdtoistr -> istofd, istofd -> fmuld), more in
;; another (e2k_adjust_cost), 6 to integer operations (timing.md,
;; "Formats": the 5, and fdtofs's 6, measured earlier chained a
;; conversion into itself).
(define_insn_reservation "e2k_fcvt" 4
  (eq_attr "type" "fcvt")
  "e2k_c0134")
;; fscaled, fscales (v4+): ALC1 or ALC4.
(define_insn_reservation "e2k_fscale" 4
  (eq_attr "type" "fscale")
  "e2k_c14")

;; fdivs 11, fsqrts 12, fdivd 14; a double root's fsqrtid 11 and
;; fsqrttd 14, fsqrttd keeping the divider from another operation 1-3
;; cycles after it before v6 (timing.md, "The divider": back to back 5
;; a cycle, 4 and 5 at 2 and 3 apart; v6 2 and 3).  By e2k_fdiv_kind,
;; which sees through a predicate.
(define_insn_reservation "e2k_fdivs" 11
  (and (eq_attr "type" "fdiv")
       (match_test "e2k_fdiv_kind (insn) == 1"))
  "alc5+divu,divu")
(define_insn_reservation "e2k_fsqrts" 12
  (and (eq_attr "type" "fdiv")
       (match_test "e2k_fdiv_kind (insn) == 2"))
  "alc5+divu,divu")
(define_insn_reservation "e2k_fsqrtid" 11
  (and (eq_attr "type" "fdiv")
       (match_test "e2k_fdiv_kind (insn) == 3"))
  "alc5+divu,divu")
(define_insn_reservation "e2k_fsqrttd" 14
  (and (eq_attr "type" "fdiv")
       (match_test "!E2K_LAT6 && e2k_fdiv_kind (insn) == 4"))
  "alc5+divu,divu,divu,divu")
(define_insn_reservation "e2k_fsqrttd6" 14
  (and (eq_attr "type" "fdiv")
       (match_test "E2K_LAT6 && e2k_fdiv_kind (insn) == 4"))
  "alc5+divu,divu")
(define_insn_reservation "e2k_fdiv" 14
  (and (eq_attr "type" "fdiv")
       (match_test "e2k_fdiv_kind (insn) == 0"))
  "alc5+divu,divu")

(define_insn_reservation "e2k_cmp0" 2
  (and (eq_attr "type" "cmp")
       (match_test "!E2K_PRED1 && e2k_insn_lits (insn) == 0")) "e2k_c0134")
(define_insn_reservation "e2k_cmp1" 2
  (and (eq_attr "type" "cmp")
       (match_test "!E2K_PRED1 && e2k_insn_lits (insn) == 1")) "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_cmp2" 2
  (and (eq_attr "type" "cmp")
       (match_test "!E2K_PRED1 && e2k_insn_lits (insn) == 2")) "e2k_c0134+e2k_lit2")

(define_insn_reservation "e2k6_cmp0" 1
  (and (eq_attr "type" "cmp")
       (match_test "E2K_PRED1 && e2k_insn_lits (insn) == 0")) "e2k_c0134")
(define_insn_reservation "e2k6_cmp1" 1
  (and (eq_attr "type" "cmp")
       (match_test "E2K_PRED1 && e2k_insn_lits (insn) == 1")) "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k6_cmp2" 1
  (and (eq_attr "type" "cmp")
       (match_test "E2K_PRED1 && e2k_insn_lits (insn) == 2")) "e2k_c0134+e2k_lit2")

(define_insn_reservation "e2k_fcmp" 4
  (and (eq_attr "type" "fcmp") (match_test "e2k_insn_lits (insn) == 0"))
  "e2k_c0134")
(define_insn_reservation "e2k_fcmp_1" 4
  (and (eq_attr "type" "fcmp") (match_test "e2k_insn_lits (insn) == 1"))
  "e2k_c0134+e2k_lit1")
(define_insn_reservation "e2k_fcmp_2" 4
  (and (eq_attr "type" "fcmp") (match_test "e2k_insn_lits (insn) == 2"))
  "e2k_c0134+e2k_lit2")

;; The x86 flag operations: ALC0 or ALC3; a result reaches a cctop in
;; its own channel in 2 cycles, anything else in 4, and the multiplies'
;; everything in 6 (e2k_chan_bundle keeps a cctop in its flags'
;; channel); cctop as a compare, 2 to an operation under its predicate
;; (1 on the 2C3), 3 to a ct (spec/isa/timing.md).
(define_insn_reservation "e2k_flag" 4
  (and (eq_attr "type" "flag") (match_test "e2k_insn_lits (insn) == 0"))
  "alc0|alc3")
(define_insn_reservation "e2k_flag_1" 4
  (and (eq_attr "type" "flag") (match_test "e2k_insn_lits (insn) == 1"))
  "(alc0|alc3)+e2k_lit1")
(define_insn_reservation "e2k_flag_2" 4
  (and (eq_attr "type" "flag") (match_test "e2k_insn_lits (insn) == 2"))
  "(alc0|alc3)+e2k_lit2")
(define_insn_reservation "e2k_flagmul" 6
  (and (eq_attr "type" "flagmul") (match_test "e2k_insn_lits (insn) == 0"))
  "alc0|alc3")
(define_insn_reservation "e2k_flagmul_1" 6
  (and (eq_attr "type" "flagmul") (match_test "e2k_insn_lits (insn) == 1"))
  "(alc0|alc3)+e2k_lit1")
(define_insn_reservation "e2k_cctop" 2
  (and (eq_attr "type" "cctop") (match_test "!E2K_PRED1")) "alc0|alc3")
(define_insn_reservation "e2k6_cctop" 1
  (and (eq_attr "type" "cctop") (match_test "E2K_PRED1")) "alc0|alc3")
(define_bypass 2 "e2k_flag,e2k_flag_1,e2k_flag_2" "e2k_cctop,e2k6_cctop")
(define_bypass 3 "e2k_cctop,e2k6_cctop" "e2k_branch,e2k_ct")
(define_bypass 1 "e2k_cctop,e2k6_cctop" "e2k_plog")

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
;; (spec/isa/apb.md).  An AAU write is a staa with MAS 0x3f, so gas keeps
;; a load out of ALC3 or ALC0 beside it as beside a store.
(define_insn_reservation "e2k_mova" 5
  (eq_attr "type" "mova") "aas0|aas1|aas2|aas3")
(define_insn_reservation "e2k_aau" 1
  (eq_attr "type" "aau") "e2k_cst_mas")
(define_insn_reservation "e2k_bap" 1
  (eq_attr "type" "bap") "ss")

;; Predicate logic: 3 to a ct, 2 to a predicated operation.
(define_insn_reservation "e2k_plog" 3
  (eq_attr "type" "plog") "pls")

(define_insn_reservation "e2k_load0" 3
  (and (eq_attr "type" "load") (eq_attr "mas" "no")
       (match_test "!E2K_LAT6 && e2k_insn_lits (insn) == 0")) "e2k_cld")
(define_insn_reservation "e2k_load1" 3
  (and (eq_attr "type" "load") (eq_attr "mas" "no")
       (match_test "!E2K_LAT6 && e2k_insn_lits (insn) == 1")) "e2k_cld+e2k_lit1")
(define_insn_reservation "e2k_load2" 3
  (and (eq_attr "type" "load") (eq_attr "mas" "no")
       (match_test "!E2K_LAT6 && e2k_insn_lits (insn) == 2")) "e2k_cld+e2k_lit2")

;; A lock load must be in ALC0 (or ALC3; the port prints ALC0).  No
;; store shares its wide instruction: whether such a store would remove
;; the new entry is not known.  A check load must be in ALC5 (or ALC2)
;; and costs its consumers nothing beyond the lock's latency (measured
;; on the 4C); its rbranch takes CS0 and SS like an ibranch.  No store
;; shares its instruction either: a check that reloaded returned the
;; value of a store later in its own wide instruction
;; (gcc.dg/torture/pr57425-1.c).  In a pipelined loop's kernel
;; (e2k_dfa_ms) a lock load and a check may share one, as lcc's
;; histogram loops have them (NPB IS: lock in ALC3, check in ALC5, the
;; stores in the other instruction at II 2).  Elsewhere each takes ALC2
;; and ALC5 whole: a list schedule that packed lock loads with other
;; loads made xz -c 1.7% slower on the 8C2.
(define_insn_reservation "e2k_ldlock0" 3
  (and (eq_attr "type" "ldlock")
       (match_test "!e2k_dfa_ms && !E2K_LAT6 && e2k_insn_lits (insn) == 0"))
  "alc0+ld0+alc2+alc5+nost0+mas0")
(define_insn_reservation "e2k_ldlock0_ms" 3
  (and (eq_attr "type" "ldlock")
       (match_test "e2k_dfa_ms && !E2K_LAT6 && e2k_insn_lits (insn) == 0"))
  "alc0+ld0+nost0+mas0")
(define_insn_reservation "e2k_ldlock1" 3
  (and (eq_attr "type" "ldlock")
       (match_test "!e2k_dfa_ms && !E2K_LAT6 && e2k_insn_lits (insn) == 1"))
  "alc0+ld0+alc2+alc5+nost0+mas0+e2k_lit1")
(define_insn_reservation "e2k_ldlock1_ms" 3
  (and (eq_attr "type" "ldlock")
       (match_test "e2k_dfa_ms && !E2K_LAT6 && e2k_insn_lits (insn) == 1"))
  "alc0+ld0+nost0+mas0+e2k_lit1")
(define_insn_reservation "e2k_ldlock2" 3
  (and (eq_attr "type" "ldlock")
       (match_test "!e2k_dfa_ms && !E2K_LAT6 && e2k_insn_lits (insn) == 2"))
  "alc0+ld0+alc2+alc5+nost0+mas0+e2k_lit2")
(define_insn_reservation "e2k_ldlock2_ms" 3
  (and (eq_attr "type" "ldlock")
       (match_test "e2k_dfa_ms && !E2K_LAT6 && e2k_insn_lits (insn) == 2"))
  "alc0+ld0+nost0+mas0+e2k_lit2")
(define_insn_reservation "e2k_ldchk0" 1
  (and (eq_attr "type" "ldchk") (match_test "!e2k_dfa_ms && e2k_insn_lits (insn) == 0"))
  "alc2+alc5+mas5+nost5+cs0+ss")
(define_insn_reservation "e2k_ldchk0_ms" 1
  (and (eq_attr "type" "ldchk") (match_test "e2k_dfa_ms && e2k_insn_lits (insn) == 0"))
  "alc5+mas5+nost5+cs0+ss")
(define_insn_reservation "e2k_ldchk1" 1
  (and (eq_attr "type" "ldchk") (match_test "!e2k_dfa_ms && e2k_insn_lits (insn) == 1"))
  "alc2+alc5+mas5+nost5+cs0+ss+e2k_lit1")
(define_insn_reservation "e2k_ldchk1_ms" 1
  (and (eq_attr "type" "ldchk") (match_test "e2k_dfa_ms && e2k_insn_lits (insn) == 1"))
  "alc5+mas5+nost5+cs0+ss+e2k_lit1")
(define_insn_reservation "e2k_ldchk2" 1
  (and (eq_attr "type" "ldchk") (match_test "!e2k_dfa_ms && e2k_insn_lits (insn) == 2"))
  "alc2+alc5+mas5+nost5+cs0+ss+e2k_lit2")
(define_insn_reservation "e2k_ldchk2_ms" 1
  (and (eq_attr "type" "ldchk") (match_test "e2k_dfa_ms && e2k_insn_lits (insn) == 2"))
  "alc5+mas5+nost5+cs0+ss+e2k_lit2")

(define_insn_reservation "e2k_store0" 1
  (and (eq_attr "type" "store") (eq_attr "mas" "no")
       (match_test "e2k_insn_lits (insn) == 0")) "e2k_cst")
(define_insn_reservation "e2k_store1" 1
  (and (eq_attr "type" "store") (eq_attr "mas" "no")
       (match_test "e2k_insn_lits (insn) == 1")) "e2k_cst+e2k_lit1")
(define_insn_reservation "e2k_store2" 1
  (and (eq_attr "type" "store") (eq_attr "mas" "no")
       (match_test "e2k_insn_lits (insn) == 2")) "e2k_cst+e2k_lit2")

;; With a MAS, also its field of CS1.
(define_insn_reservation "e2k_load_mas0" 3
  (and (eq_attr "type" "load") (eq_attr "mas" "yes")
       (match_test "!E2K_LAT6 && e2k_insn_lits (insn) == 0"))
  "e2k_cld_mas")
(define_insn_reservation "e2k_load_mas1" 3
  (and (eq_attr "type" "load") (eq_attr "mas" "yes")
       (match_test "!E2K_LAT6 && e2k_insn_lits (insn) != 0"))
  "e2k_cld_mas+e2k_lit2")
(define_insn_reservation "e2k_store_mas0" 1
  (and (eq_attr "type" "store") (eq_attr "mas" "yes")
       (match_test "e2k_insn_lits (insn) == 0"))
  "e2k_cst_mas")
(define_insn_reservation "e2k_store_mas1" 1
  (and (eq_attr "type" "store") (eq_attr "mas" "yes")
       (match_test "e2k_insn_lits (insn) != 0"))
  "e2k_cst_mas+e2k_lit2")

;; v6 (the 2C3): an L1 load takes 5 cycles in every channel, to every
;; consumer in either cluster (spec/isa/timing.md, "Elbrus-2C3 (v6)").
;; The same channels; -mlatency=v6 or a v6 CPU (E2K_LAT6).
(define_insn_reservation "e2k6_load0" 5
  (and (eq_attr "type" "load") (eq_attr "mas" "no")
       (match_test "E2K_LAT6 && e2k_insn_lits (insn) == 0")) "e2k_cld")
(define_insn_reservation "e2k6_load1" 5
  (and (eq_attr "type" "load") (eq_attr "mas" "no")
       (match_test "E2K_LAT6 && e2k_insn_lits (insn) == 1")) "e2k_cld+e2k_lit1")
(define_insn_reservation "e2k6_load2" 5
  (and (eq_attr "type" "load") (eq_attr "mas" "no")
       (match_test "E2K_LAT6 && e2k_insn_lits (insn) == 2")) "e2k_cld+e2k_lit2")
(define_insn_reservation "e2k6_ldlock0" 5
  (and (eq_attr "type" "ldlock")
       (match_test "!e2k_dfa_ms && E2K_LAT6 && e2k_insn_lits (insn) == 0"))
  "alc0+ld0+alc2+alc5+nost0+mas0")
(define_insn_reservation "e2k6_ldlock0_ms" 5
  (and (eq_attr "type" "ldlock")
       (match_test "e2k_dfa_ms && E2K_LAT6 && e2k_insn_lits (insn) == 0"))
  "alc0+ld0+nost0+mas0")
(define_insn_reservation "e2k6_ldlock1" 5
  (and (eq_attr "type" "ldlock")
       (match_test "!e2k_dfa_ms && E2K_LAT6 && e2k_insn_lits (insn) == 1"))
  "alc0+ld0+alc2+alc5+nost0+mas0+e2k_lit1")
(define_insn_reservation "e2k6_ldlock1_ms" 5
  (and (eq_attr "type" "ldlock")
       (match_test "e2k_dfa_ms && E2K_LAT6 && e2k_insn_lits (insn) == 1"))
  "alc0+ld0+nost0+mas0+e2k_lit1")
(define_insn_reservation "e2k6_ldlock2" 5
  (and (eq_attr "type" "ldlock")
       (match_test "!e2k_dfa_ms && E2K_LAT6 && e2k_insn_lits (insn) == 2"))
  "alc0+ld0+alc2+alc5+nost0+mas0+e2k_lit2")
(define_insn_reservation "e2k6_ldlock2_ms" 5
  (and (eq_attr "type" "ldlock")
       (match_test "e2k_dfa_ms && E2K_LAT6 && e2k_insn_lits (insn) == 2"))
  "alc0+ld0+nost0+mas0+e2k_lit2")
(define_insn_reservation "e2k6_load_mas0" 5
  (and (eq_attr "type" "load") (eq_attr "mas" "yes")
       (match_test "E2K_LAT6 && e2k_insn_lits (insn) == 0"))
  "e2k_cld_mas")
(define_insn_reservation "e2k6_load_mas1" 5
  (and (eq_attr "type" "load") (eq_attr "mas" "yes")
       (match_test "E2K_LAT6 && e2k_insn_lits (insn) != 0"))
  "e2k_cld_mas+e2k_lit2")

(define_insn_reservation "e2k_getsp" 2
  (and (eq_attr "type" "getsp")
       (match_test "recog_memoized (insn) != CODE_FOR_e2k_rrs
		    && recog_memoized (insn) != CODE_FOR_e2k_rwd_lsr_vlc"))
  "alc0+e2k_lit1")
;; Its 64-bit literal, vlc.
(define_insn_reservation "e2k_rwd_lsr_vlc" 2
  (and (eq_attr "type" "getsp")
       (match_test "recog_memoized (insn) == CODE_FOR_e2k_rwd_lsr_vlc"))
  "alc0+e2k_lit2")

;; A read of the FP state (%pfpfr, %fpcr, %fpsr: the port's only rrs)
;; delivers its value 11 cycles later (timing.md, "State registers").
(define_insn_reservation "e2k_rrs" 11
  (and (eq_attr "type" "getsp")
       (match_test "recog_memoized (insn) == CODE_FOR_e2k_rrs"))
  "alc0")

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
(define_bypass 6 "e2k_fp,e2k_fp_1,e2k_fp_2,e2k_fp6,e2k_fp6_1,e2k_fp6_2,
		  e2k_mul0,e2k_mul1,e2k_mul2"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_alu14,e2k_alu14_1,e2k_alu14_2,
   e2k_alu0134,e2k_alu0134_1,e2k_alu0134_2,e2k_cmp0,e2k_cmp1,e2k_cmp2,
   e2k6_cmp0,e2k6_cmp1,e2k6_cmp2,
   e2k_load0,e2k_load1,e2k_load2,e2k_load_mas0,e2k_load_mas1,
   e2k6_load0,e2k6_load1,e2k6_load2,e2k6_load_mas0,e2k6_load_mas1")
;; 7 to an integer consumer.
(define_bypass 7 "e2k_ffma"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_alu14,e2k_alu14_1,e2k_alu14_2,
   e2k_alu0134,e2k_alu0134_1,e2k_alu0134_2,e2k_cmp0,e2k_cmp1,e2k_cmp2,
   e2k6_cmp0,e2k6_cmp1,e2k6_cmp2,
   e2k_load0,e2k_load1,e2k_load2,e2k_load_mas0,e2k_load_mas1,
   e2k6_load0,e2k6_load1,e2k6_load2,e2k6_load_mas0,e2k6_load_mas1")
(define_bypass 6 "e2k_fcvt,e2k_fscale"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_alu14,e2k_alu14_1,e2k_alu14_2,
   e2k_alu0134,e2k_alu0134_1,e2k_alu0134_2,e2k_cmp0,e2k_cmp1,e2k_cmp2,
   e2k6_cmp0,e2k6_cmp1,e2k6_cmp2,
   e2k_load0,e2k_load1,e2k_load2,e2k_load_mas0,e2k_load_mas1,
   e2k6_load0,e2k6_load1,e2k6_load2,e2k6_load_mas0,e2k6_load_mas1")
;; A load into the addend of a combined FP operation: 4 more, the add's
;; slack in a separate fmuld + faddd, which a load that misses L1 needs
;; (the 8C2: a pipelined daxpy over L2-sized arrays 1.06 -> 1.20 cycles
;; an element with fmul_add without it).
(define_bypass 7 "e2k_load0,e2k_load1,e2k_load2,e2k_load_mas0,e2k_load_mas1"
  "e2k_fma,e2k_fma_1,e2k_fma_2,e2k_fma6,e2k_fma6_1,e2k_fma6_2"
  "e2k_fma_addend_p")
(define_bypass 9 "e2k6_load0,e2k6_load1,e2k6_load2,e2k6_load_mas0,e2k6_load_mas1"
  "e2k_fma,e2k_fma_1,e2k_fma_2,e2k_fma6,e2k_fma6_1,e2k_fma6_2"
  "e2k_fma_addend_p")
;; Packed results reach integer operations at 4.
(define_bypass 4 "e2k_pint,e2k_pint_1,e2k_pint_2,e2k_pint14,e2k_pint14_1,e2k_pint14_2,
		  e2k_pmul,e2k_pmul_1,e2k_pmul_2,e2k_pany0,e2k_pany1,e2k_pany2"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_alu14,e2k_alu14_1,e2k_alu14_2,
   e2k_alu0134,e2k_alu0134_1,e2k_alu0134_2,e2k_cmp0,e2k_cmp1,e2k_cmp2,
   e2k6_cmp0,e2k6_cmp1,e2k6_cmp2,
   e2k_load0,e2k_load1,e2k_load2,e2k_load_mas0,e2k_load_mas1,
   e2k6_load0,e2k6_load1,e2k6_load2,e2k6_load_mas0,e2k6_load_mas1")
;; Compare -> predicate logic, and predicate logic chained through a
;; %pred: 1; predicate logic -> an operation under its predicate: 2
;; (spec/isa/timing.md).
(define_bypass 1 "e2k_cmp0,e2k_cmp1,e2k_cmp2,e2k6_cmp0,e2k6_cmp1,e2k6_cmp2"
  "e2k_plog")
(define_bypass 1 "e2k_plog" "e2k_plog")
(define_bypass 2 "e2k_plog"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_alu14,e2k_alu14_1,e2k_alu14_2,
   e2k_alu0134,e2k_alu0134_1,e2k_alu0134_2,e2k_load0,e2k_load1,e2k_load2,
   e2k_load_mas0,e2k_load_mas1,e2k6_load0,e2k6_load1,e2k6_load2,
   e2k6_load_mas0,e2k6_load_mas1")
;; 1 on the 2C3 (E2K_PRED1).
(define_bypass 1 "e2k_plog"
  "e2k_alu0,e2k_alu1,e2k_alu2,e2k_alu14,e2k_alu14_1,e2k_alu14_2,
   e2k_alu0134,e2k_alu0134_1,e2k_alu0134_2,e2k_load0,e2k_load1,e2k_load2,
   e2k_load_mas0,e2k_load_mas1,e2k6_load0,e2k6_load1,e2k6_load2,
   e2k6_load_mas0,e2k6_load_mas1"
  "e2k_pred1_p")
;; Compare -> ibranch or ct on its predicate (spec/isa/control-transfer.md,
;; "Costs"; a ct placed earlier waits for it, which the scheduler then
;; doesn't see; andp -> ct is plog's own 3).
(define_bypass 3 "e2k_cmp0,e2k_cmp1,e2k_cmp2,e2k6_cmp0,e2k6_cmp1,e2k6_cmp2"
  "e2k_branch,e2k_ct")
(define_bypass 5 "e2k_fcmp,e2k_fcmp_1,e2k_fcmp_2" "e2k_branch,e2k_ct")
