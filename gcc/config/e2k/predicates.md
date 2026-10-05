;; Predicates for the Elbrus (E2K) port.
;; Written by Claude (Anthropic) as an experiment; see README.claude.
;;
;; This file is part of GCC.
;;
;; GCC is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; A register, but not a 64-bit view of a value of 4 bytes or less
;; (e2k_partial_subreg_p).
(define_predicate "e2k_register_operand"
  (and (match_operand 0 "register_operand")
       (not (match_test "e2k_partial_subreg_p (op)"))))

;; Any register or literal that can go in src2: literals of up to 64 bits
;; are placed in the wide instruction's literal syllables.
(define_predicate "e2k_src2_operand"
  (ior (match_operand 0 "e2k_register_operand")
       (and (match_code "const_int,const_double,const_wide_int,symbol_ref,label_ref,const")
	    (match_test "e2k_legitimate_constant_p (mode, op)"))))

;; src1 only takes a register or a 5-bit literal.
(define_predicate "e2k_src1_operand"
  (ior (match_operand 0 "e2k_register_operand")
       (and (match_code "const_int")
	    (match_test "IN_RANGE (INTVAL (op), 0, 31)"))))

(define_predicate "e2k_reg_or_zero_operand"
  (ior (match_operand 0 "e2k_register_operand")
       (match_test "op == CONST0_RTX (mode)")))

(define_predicate "e2k_call_operand"
  (ior (match_code "symbol_ref")
       (match_operand 0 "e2k_register_operand")))

(define_predicate "e2k_int_cmp_operator"
  (match_code "eq,ne,lt,le,gt,ge,ltu,leu,gtu,geu"))

;; Comparisons a compare operation computes directly.
(define_predicate "e2k_direct_int_cmp_operator"
  (match_code "eq,lt,le,ltu,leu"))

;; Floating-point comparisons with a predicate compare operation,
;; possibly with swapped operands.
(define_predicate "e2k_fp_cmp_operator"
  (match_code "eq,ne,lt,le,gt,ge,unordered,ordered"))

(define_predicate "e2k_direct_fp_cmp_operator"
  (match_code "eq,ne,lt,le,unordered,ordered"))

;; Comparisons that must not signal on quiet NaNs but have no quiet
;; predicate compare (fcmpnlt/nle signal): fcmpud*f and an integer test.
(define_predicate "e2k_quiet_fp_cmp_operator"
  (match_code "unlt,unle,ungt,unge,uneq,ltgt"))

(define_predicate "e2k_any_fp_cmp_operator"
  (ior (match_operand 0 "e2k_fp_cmp_operator")
       (match_operand 0 "e2k_quiet_fp_cmp_operator")))

(define_predicate "e2k_pred_test_operator"
  (match_code "eq,ne"))

(define_predicate "e2k_symbolic_operand"
  (match_code "symbol_ref,label_ref,const"))

(define_predicate "e2k_move_operand"
  (ior (match_operand 0 "memory_operand")
       (match_operand 0 "e2k_src2_operand")))

;; The CTPRs are fixed registers, which register_operand rejects.
(define_predicate "e2k_ctpr_operand"
  (and (match_code "reg")
       (match_test "CTPR_REGNO_P (REGNO (op))")))

;; The source of a load the scheduler may turn into a lock load: a
;; non-volatile memory reference or a zero-extending load of one.
(define_predicate "e2k_spec_load_operand"
  (match_code "mem,zero_extend")
{
  rtx mem = GET_CODE (op) == ZERO_EXTEND ? XEXP (op, 0) : op;
  return (MEM_P (mem) && !MEM_VOLATILE_P (mem)
	  && GET_MODE_SIZE (GET_MODE (mem)) <= 8
	  && memory_address_p (GET_MODE (mem), XEXP (mem, 0)));
})
