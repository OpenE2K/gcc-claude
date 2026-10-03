;; Constraints for the Elbrus (E2K) port.
;; Written by Claude (Anthropic) as an experiment; see README.claude.
;;
;; This file is part of GCC.
;;
;; GCC is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

(define_register_constraint "j" "PRED_REGS"
  "A predicate register %pred0..%pred31.")

(define_register_constraint "b" "B_REGS"
  "An outgoing argument register %b[0]..%b[7].")

;; src1 of an ALU operation takes a 5-bit literal in the syllable.
(define_constraint "I"
  "An integer from 0 to 31."
  (and (match_code "const_int")
       (match_test "IN_RANGE (ival, 0, 31)")))

(define_constraint "Z"
  "Zero of any mode."
  (match_test "op == CONST0_RTX (mode)"))
