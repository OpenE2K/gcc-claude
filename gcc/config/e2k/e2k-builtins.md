;; lcc's operation builtins for the Elbrus (E2K) port (e2k-builtins.cc,
;; e2k-builtins.def; relcc2 spec/abi/lcc-builtins.md).
;; Written by Claude (Anthropic) as an experiment; see README.claude.
;;
;; This file is part of GCC.
;;
;; GCC is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 3, or (at your option) any later
;; version.

;; One operation: operand 0 its result, 1 to N its sources in the order
;; lcc's code has them (the builtin's arguments, constants, fixed
;; literals), the last the builtin's index in e2k-builtins.def, which
;; gives the mnemonic and the type (e2k_bop_attr_type).  The sources take
;; any mode: the operation decides the width it reads.  What each place
;; takes is the encoding's (spec/isa/bundle.md): src1 a register or a
;; 5-bit literal, src2 a register or any literal, src3 a register (ALES
;; names it), an 8-bit ALES literal (ALOPF11_LIT8, "bop3l") a constant,
;; the mnemonic's suffix (plog's table, "bop4") a constant.
(define_mode_iterator BOP [DI V2DI])

(define_insn "@e2k_bop1<mode>"
  [(set (match_operand:BOP 0 "register_operand" "=r")
	(unspec:BOP [(match_operand 1 "e2k_bop_operand" "ri")
		     (match_operand 2 "const_int_operand" "n")]
		    UNSPEC_E2K_BOP))]
  ""
  { return e2k_bop_output (operands, 1); }
  [(set (attr "type") (symbol_ref "(enum attr_type) e2k_bop_attr_type (insn)"))])

(define_insn "@e2k_bop2<mode>"
  [(set (match_operand:BOP 0 "register_operand" "=r")
	(unspec:BOP [(match_operand 1 "e2k_bop_src1_operand" "rI")
		     (match_operand 2 "e2k_bop_operand" "ri")
		     (match_operand 3 "const_int_operand" "n")]
		    UNSPEC_E2K_BOP))]
  ""
  { return e2k_bop_output (operands, 2); }
  [(set (attr "type") (symbol_ref "(enum attr_type) e2k_bop_attr_type (insn)"))])

(define_insn "@e2k_bop3<mode>"
  [(set (match_operand:BOP 0 "register_operand" "=r")
	(unspec:BOP [(match_operand 1 "e2k_bop_src1_operand" "rI")
		     (match_operand 2 "e2k_bop_operand" "ri")
		     (match_operand 3 "register_operand" "r")
		     (match_operand 4 "const_int_operand" "n")]
		    UNSPEC_E2K_BOP))]
  ""
  { return e2k_bop_output (operands, 3); }
  [(set (attr "type") (symbol_ref "(enum attr_type) e2k_bop_attr_type (insn)"))])

(define_insn "@e2k_bop3l<mode>"
  [(set (match_operand:BOP 0 "register_operand" "=r")
	(unspec:BOP [(match_operand 1 "e2k_bop_src1_operand" "rI")
		     (match_operand 2 "e2k_bop_operand" "ri")
		     (match_operand 3 "const_int_operand" "n")
		     (match_operand 4 "const_int_operand" "n")]
		    UNSPEC_E2K_BOP))]
  "e2k_bop_lit8_p (operands[4])"
  { return e2k_bop_output (operands, 3); }
  [(set (attr "type") (symbol_ref "(enum attr_type) e2k_bop_attr_type (insn)"))])

(define_insn "@e2k_bop4<mode>"
  [(set (match_operand:BOP 0 "register_operand" "=r")
	(unspec:BOP [(match_operand 1 "const_int_operand" "n")
		     (match_operand 2 "e2k_bop_src1_operand" "rI")
		     (match_operand 3 "e2k_bop_operand" "ri")
		     (match_operand 4 "register_operand" "r")
		     (match_operand 5 "const_int_operand" "n")]
		    UNSPEC_E2K_BOP))]
  ""
  { return e2k_bop_output (operands, 4); }
  [(set (attr "type") (symbol_ref "(enum attr_type) e2k_bop_attr_type (insn)"))])

;; A compare into a predicate that the builtin returns as 0 or 1
;; (pcmp*ap, pcmp*op, v6): lcc's "merged 0, 1, ret, pred" after it.
;; Split after reload, as the port's cstore patterns are, so that the
;; predicate is a scratch.
(define_insn_and_split "@e2k_boppred<mode>"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(unspec:DI [(match_operand:BOP 1 "register_operand" "r")
		    (match_operand:BOP 2 "register_operand" "r")
		    (match_operand 3 "const_int_operand" "n")]
		   UNSPEC_E2K_BOPPRED))
   (clobber (match_scratch:BI 4 "=j"))]
  ""
  "#"
  "&& reload_completed"
  [(set (match_dup 4)
	(unspec:BI [(match_dup 1) (match_dup 2) (match_dup 3)]
		   UNSPEC_E2K_BOPP))
   (set (match_dup 0)
	(if_then_else:DI (ne (match_dup 4) (const_int 0))
			 (const_int 1) (const_int 0)))]
  ""
  [(set_attr "type" "multi")])

(define_insn "*e2k_bopp<mode>"
  [(set (match_operand:BI 0 "register_operand" "=j")
	(unspec:BI [(match_operand:BOP 1 "register_operand" "r")
		    (match_operand:BOP 2 "register_operand" "r")
		    (match_operand 3 "const_int_operand" "n")]
		   UNSPEC_E2K_BOPP))]
  ""
  { return e2k_bop_output (operands, 2); }
  [(set (attr "type") (symbol_ref "(enum attr_type) e2k_bop_attr_type (insn)"))])

;; lcc's speculative loads (ld_64s_sm, ld_128_sm, the _cleartag ones):
;; ldd,sm never faults, a bad address giving a diagnostic value
;; (spec/isa/speculation.md).  e2k_output_sm prints the ",sm".
(define_insn "e2k_ldsmdi"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(unspec:DI [(match_operand:DI 1 "memory_operand" "m")]
		   UNSPEC_E2K_LDSM))]
  ""
  { return e2k_output_sm ("ldd\t%1, %0"); }
  [(set_attr "type" "load")])

;; qppackdl,sm for the 16-byte speculative loads: its halves may be
;; diagnostic, which a non-speculative operation would trap on.
(define_insn "e2k_qppack_sm"
  [(set (match_operand:V2DI 0 "register_operand" "=r")
	(unspec:V2DI [(match_operand:DI 1 "register_operand" "r")
		      (match_operand:DI 2 "register_operand" "r")]
		     UNSPEC_E2K_PACKSM))]
  "e2k_arch >= 5"
  { return e2k_output_sm ("qppackdl\t%1, %2, %0"); }
  [(set_attr "type" "pany")])

;; A store with a MAS (st_128_nt: stqp, mas=0x60; st_64s_nt and
;; st_32u_nt from v5).
(define_mode_iterator STMAS [SI DI V2DI])
(define_mode_attr stmas_sz [(SI "w") (DI "d") (V2DI "qp")])

(define_insn "@e2k_stmas<mode>"
  [(set (match_operand:STMAS 0 "memory_operand" "=m")
	(unspec:STMAS [(match_operand:STMAS 1 "register_operand" "r")
		       (match_operand 2 "const_int_operand" "n")]
		      UNSPEC_E2K_STMAS))]
  ""
  "st<stmas_sz>\t%0, %1, mas = %2"
  [(set_attr "type" "store")
   (set_attr "mas" "yes")])

;; pst_128 (v5): stmqp writes byte i of operand 1 where bit i of operand 2
;; is set; its address is operand 0 alone (no offset).
(define_insn "e2k_stmqp"
  [(set (mem:V2DI (match_operand:DI 0 "register_operand" "r"))
	(unspec:V2DI [(match_operand:V2DI 1 "register_operand" "r")
		      (match_operand:DI 2 "register_operand" "r")
		      (mem:V2DI (match_dup 0))]
		     UNSPEC_E2K_STMQP))]
  "e2k_arch >= 5"
  "stmqp\t%0, %2, %1"
  [(set_attr "type" "store")])
