;; Machine description for the Elbrus (E2K) port, 64-bit mode.
;; Written by Claude (Anthropic) as an experiment, from the relcc2
;; specification; see README.claude.  Not for contribution to GCC.
;;
;; This file is part of GCC.
;;
;; GCC is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.
;;
;; GCC is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
;; or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
;; License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GCC; see the file COPYING3.  If not see
;; <http://www.gnu.org/licenses/>.

;; Output conventions:
;;  - Operations are printed one per line; the bundler (e2k.cc) wraps
;;    each scheduled cycle in { }.  "%#" inside a template starts a new
;;    wide instruction (for insns that print dependent operations), and
;;    "%<" ... "%>" force braces around operations that must share one
;;    wide instruction when the bundler is off.
;;  - Stores use the ".ignore ld_st_style" order: address, offset, data.

(define_constants
  [(R0_REGNUM 32)
   (SP_REGNUM 40)
   (B0_REGNUM 96)
   (PRED0_REGNUM 104)
   (CTPR1_REGNUM 136)
   (CTPR2_REGNUM 137)
   (CTPR3_REGNUM 138)
   (TP_REGNUM 13)])

(define_c_enum "unspec"
  [UNSPEC_GOT
   UNSPEC_GOTOFF
   UNSPEC_GOTBASE
   UNSPEC_TLS_LE
   UNSPEC_TLS_IE
   UNSPEC_TLS_GDMOD
   UNSPEC_TLS_GDREL
   UNSPEC_DISP
   UNSPEC_MOVTD
   UNSPEC_FSQRTI
   UNSPEC_WAIT
   UNSPEC_RETURN
   UNSPEC_OPAQUE])

(define_c_enum "unspecv"
  [UNSPECV_SETWD
   UNSPECV_GETSP
   UNSPECV_RETURN
   UNSPECV_BLOCKAGE
   UNSPECV_WAIT
   UNSPECV_CAS
   UNSPECV_ATOMIC])

;; Instruction classes, used by the pipeline description (e2k-sched.md).
;;  alu      integer add/logic/shift/sxt/merge: any of ALC0-5
;;  alu14    lzcnt, popcnt: ALC1, ALC4
;;  mul      integer multiply: ALC0,1,3,4
;;  div      integer divide: ALC5
;;  fp       FP add/multiply: ALC0,1,3,4
;;  fcvt     FP conversions: ALC0,1,3,4
;;  fdiv     FP divide/sqrt: ALC5
;;  cmp      integer compare into a predicate: ALC0,1,3,4
;;  fcmp     FP compare into a predicate: ALC0,1,3,4
;;  load     ALC0,2,3,5
;;  store    ALC2,5
;;  getsp    ALC0
;;  movctp   movtd into a CTPR: ALC0,1,3,4
;;  disp     disp/return: CS0
;;  branch   ibranch: CS0 + SS
;;  ct       ct %ctprN: SS
;;  call     call: CS1 + SS
;;  setwd    setwd/setbn: CS1, alone
;;  multi    prints several wide instructions
;;  ghost    prints nothing
(define_attr "type"
  "alu,alu14,mul,div,fp,fcvt,fdiv,cmp,fcmp,load,store,getsp,movctp,disp,ret,branch,ct,call,setwd,wait,multi,raw,ghost,nop"
  (const_string "alu"))

(include "predicates.md")
(include "constraints.md")
(include "e2k-sched.md")

(define_mode_iterator I48 [SI DI])
(define_mode_iterator F [SF DF])
(define_mode_iterator GPRM [SI DI SF DF])
(define_mode_iterator DBL [TI TF XF])

(define_mode_attr sd [(SI "s") (DI "d") (SF "s") (DF "d")])
(define_mode_attr SIGNBIT [(SF "0x80000000") (DF "0x8000000000000000")])

;; ---------------------------------------------------------------------
;; Moves
;; ---------------------------------------------------------------------

(define_expand "mov<mode>"
  [(set (match_operand:GPRM 0 "nonimmediate_operand")
	(match_operand:GPRM 1 "general_operand"))]
  ""
{
  if (e2k_expand_move (<MODE>mode, operands))
    DONE;
})

(define_expand "movqi"
  [(set (match_operand:QI 0 "nonimmediate_operand")
	(match_operand:QI 1 "general_operand"))]
  ""
{
  if (e2k_expand_move (QImode, operands))
    DONE;
})

(define_expand "movhi"
  [(set (match_operand:HI 0 "nonimmediate_operand")
	(match_operand:HI 1 "general_operand"))]
  ""
{
  if (e2k_expand_move (HImode, operands))
    DONE;
})

(define_insn "*movqi_insn"
  [(set (match_operand:QI 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:QI 1 "e2k_move_operand"      "r,i,m,r"))]
  "register_operand (operands[0], QImode)
   || register_operand (operands[1], QImode)"
  "@
   adds\t%1, 0x0, %0
   adds\t0x0, %1, %0
   ldb\t%1, %0
   stb\t%0, %1"
  [(set_attr "type" "alu,alu,load,store")])

(define_insn "*movhi_insn"
  [(set (match_operand:HI 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:HI 1 "e2k_move_operand"      "r,i,m,r"))]
  "register_operand (operands[0], HImode)
   || register_operand (operands[1], HImode)"
  "@
   adds\t%1, 0x0, %0
   adds\t0x0, %1, %0
   ldh\t%1, %0
   sth\t%0, %1"
  [(set_attr "type" "alu,alu,load,store")])

(define_insn "*movsi_insn"
  [(set (match_operand:SI 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:SI 1 "e2k_move_operand"      "r,i,m,r"))]
  "register_operand (operands[0], SImode)
   || register_operand (operands[1], SImode)"
  "@
   adds\t%1, 0x0, %0
   adds\t0x0, %1, %0
   ldw\t%1, %0
   stw\t%0, %1"
  [(set_attr "type" "alu,alu,load,store")])

(define_insn "*movsf_insn"
  [(set (match_operand:SF 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:SF 1 "e2k_move_operand"      "r,F,m,r"))]
  "register_operand (operands[0], SFmode)
   || register_operand (operands[1], SFmode)"
  "@
   adds\t%1, 0x0, %0
   adds\t0x0, %1, %0
   ldw\t%1, %0
   stw\t%0, %1"
  [(set_attr "type" "alu,alu,load,store")])

(define_insn "*movdi_insn"
  [(set (match_operand:DI 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:DI 1 "e2k_move_operand"      "r,i,m,r"))]
  "register_operand (operands[0], DImode)
   || register_operand (operands[1], DImode)"
  "@
   addd\t%1, 0x0, %0
   addd\t0x0, %1, %0
   ldd\t%1, %0
   std\t%0, %1"
  [(set_attr "type" "alu,alu,load,store")])

(define_insn "*movdf_insn"
  [(set (match_operand:DF 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:DF 1 "e2k_move_operand"      "r,F,m,r"))]
  "register_operand (operands[0], DFmode)
   || register_operand (operands[1], DFmode)"
  "@
   addd\t%1, 0x0, %0
   addd\t0x0, %1, %0
   ldd\t%1, %0
   std\t%0, %1"
  [(set_attr "type" "alu,alu,load,store")])

;; 16-byte values in a register pair: __int128, __float128 and long double.
(define_expand "mov<mode>"
  [(set (match_operand:DBL 0 "nonimmediate_operand")
	(match_operand:DBL 1 "general_operand"))]
  ""
{
  if (e2k_expand_move (<MODE>mode, operands))
    DONE;
})

(define_insn_and_split "*mov<mode>_insn"
  [(set (match_operand:DBL 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:DBL 1 "e2k_move_operand"      "r,iF,m,r"))]
  "register_operand (operands[0], <MODE>mode)
   || register_operand (operands[1], <MODE>mode)"
  "#"
  "reload_completed"
  [(const_int 0)]
{
  e2k_split_double_move (operands[0], operands[1]);
  DONE;
}
  [(set_attr "type" "multi")])

;; ---------------------------------------------------------------------
;; Extensions
;; ---------------------------------------------------------------------

;; sxt: src1 bits 0-1 select 8/16/32 bits; bit 2 set means zero extension.
;; The guide (10.3.8) says the opposite; lcc and qemu agree with this.
(define_insn "extendsidi2"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(sign_extend:DI (match_operand:SI 1 "register_operand" "r")))]
  ""
  "sxt\t2, %1, %0")

(define_insn "extendhidi2"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(sign_extend:DI (match_operand:HI 1 "register_operand" "r")))]
  ""
  "sxt\t1, %1, %0")

(define_insn "extendqidi2"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(sign_extend:DI (match_operand:QI 1 "register_operand" "r")))]
  ""
  "sxt\t0, %1, %0")

(define_insn "extendhisi2"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(sign_extend:SI (match_operand:HI 1 "register_operand" "r")))]
  ""
  "sxt\t1, %1, %0")

(define_insn "extendqisi2"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(sign_extend:SI (match_operand:QI 1 "register_operand" "r")))]
  ""
  "sxt\t0, %1, %0")

(define_insn "extendqihi2"
  [(set (match_operand:HI 0 "register_operand" "=r")
	(sign_extend:HI (match_operand:QI 1 "register_operand" "r")))]
  ""
  "sxt\t0, %1, %0")

;; Loads always write the whole register, zero-extended (spec
;; registers.md, "dbl").
(define_insn "zero_extendsidi2"
  [(set (match_operand:DI 0 "register_operand" "=r,r")
	(zero_extend:DI (match_operand:SI 1 "nonimmediate_operand" "r,m")))]
  ""
  "@
   sxt\t6, %1, %0
   ldw\t%1, %0"
  [(set_attr "type" "alu,load")])

(define_insn "zero_extendhidi2"
  [(set (match_operand:DI 0 "register_operand" "=r,r")
	(zero_extend:DI (match_operand:HI 1 "nonimmediate_operand" "r,m")))]
  ""
  "@
   sxt\t5, %1, %0
   ldh\t%1, %0"
  [(set_attr "type" "alu,load")])

(define_insn "zero_extendqidi2"
  [(set (match_operand:DI 0 "register_operand" "=r,r")
	(zero_extend:DI (match_operand:QI 1 "nonimmediate_operand" "r,m")))]
  ""
  "@
   sxt\t4, %1, %0
   ldb\t%1, %0"
  [(set_attr "type" "alu,load")])

(define_insn "zero_extendhisi2"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(zero_extend:SI (match_operand:HI 1 "nonimmediate_operand" "r,m")))]
  ""
  "@
   sxt\t5, %1, %0
   ldh\t%1, %0"
  [(set_attr "type" "alu,load")])

(define_insn "zero_extendqisi2"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(zero_extend:SI (match_operand:QI 1 "nonimmediate_operand" "r,m")))]
  ""
  "@
   sxt\t4, %1, %0
   ldb\t%1, %0"
  [(set_attr "type" "alu,load")])

(define_insn "zero_extendqihi2"
  [(set (match_operand:HI 0 "register_operand" "=r,r")
	(zero_extend:HI (match_operand:QI 1 "nonimmediate_operand" "r,m")))]
  ""
  "@
   sxt\t4, %1, %0
   ldb\t%1, %0"
  [(set_attr "type" "alu,load")])

;; ---------------------------------------------------------------------
;; Integer arithmetic
;; ---------------------------------------------------------------------

(define_insn "add<mode>3"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(plus:I48 (match_operand:I48 1 "register_operand" "%r")
		  (match_operand:I48 2 "e2k_src2_operand" "ri")))]
  ""
  "add<sd>\t%1, %2, %0")

(define_insn "sub<mode>3"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(minus:I48 (match_operand:I48 1 "e2k_src1_operand" "rI")
		   (match_operand:I48 2 "e2k_src2_operand" "ri")))]
  ""
  "sub<sd>\t%1, %2, %0")

(define_insn "neg<mode>2"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(neg:I48 (match_operand:I48 1 "register_operand" "r")))]
  ""
  "sub<sd>\t0x0, %1, %0")

(define_insn "mul<mode>3"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(mult:I48 (match_operand:I48 1 "register_operand" "%r")
		  (match_operand:I48 2 "e2k_src2_operand" "ri")))]
  ""
  "mul<sd>\t%1, %2, %0"
  [(set_attr "type" "mul")])

;; Integer division by zero raises SIGFPE (FPE_INTDIV, seen on the 4C).
;; RTL PRE assumes calls return and will hoist a plain trapping SET out
;; of a loop above a call that exits (gcc.c-torture pr38819).  Only a
;; clobber of a hard register stops it (can_assign_to_reg_without_clobbers_p),
;; as x86's flags clobber does; %ctpr2 is otherwise used only inside the
;; indirect-jump insns.
(define_code_iterator DIVOP [div udiv])
(define_code_attr divop [(div "sdiv") (udiv "udiv")])

(define_expand "<code><mode>3"
  [(parallel [(set (match_operand:I48 0 "register_operand")
		   (DIVOP:I48 (match_operand:I48 1 "register_operand")
			      (match_operand:I48 2 "register_operand")))
	      (clobber (reg:DI CTPR2_REGNUM))])]
  "")

(define_insn "*<code><mode>3"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(DIVOP:I48 (match_operand:I48 1 "register_operand" "r")
		   (match_operand:I48 2 "register_operand" "r")))
   (clobber (reg:DI CTPR2_REGNUM))]
  ""
  "<divop><sd>\t%1, %2, %0"
  [(set_attr "type" "div")])

(define_insn "umulsidi3"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(mult:DI (zero_extend:DI (match_operand:SI 1 "register_operand" "%r"))
		 (zero_extend:DI (match_operand:SI 2 "register_operand" "r"))))]
  ""
  "umulx\t%1, %2, %0"
  [(set_attr "type" "mul")])

(define_insn "mulsidi3"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(mult:DI (sign_extend:DI (match_operand:SI 1 "register_operand" "%r"))
		 (sign_extend:DI (match_operand:SI 2 "register_operand" "r"))))]
  ""
  "smulx\t%1, %2, %0"
  [(set_attr "type" "mul")])

(define_insn "umuldi3_highpart"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(truncate:DI
	  (lshiftrt:TI
	    (mult:TI (zero_extend:TI (match_operand:DI 1 "register_operand" "%r"))
		     (zero_extend:TI (match_operand:DI 2 "register_operand" "r")))
	    (const_int 64))))]
  ""
  "umulhd\t%1, %2, %0"
  [(set_attr "type" "mul")])

(define_insn "smuldi3_highpart"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(truncate:DI
	  (lshiftrt:TI
	    (mult:TI (sign_extend:TI (match_operand:DI 1 "register_operand" "%r"))
		     (sign_extend:TI (match_operand:DI 2 "register_operand" "r")))
	    (const_int 64))))]
  ""
  "smulhd\t%1, %2, %0"
  [(set_attr "type" "mul")])

(define_code_iterator LOGIC [and ior xor])
(define_code_attr logic [(and "and") (ior "or") (xor "xor")])
(define_code_attr logic_optab [(and "and") (ior "ior") (xor "xor")])

(define_insn "<logic_optab><mode>3"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(LOGIC:I48 (match_operand:I48 1 "register_operand" "%r")
		   (match_operand:I48 2 "e2k_src2_operand" "ri")))]
  ""
  "<logic><sd>\t%1, %2, %0")

;; andn, orn: the second operand is inverted (guide 10.3.5).
(define_insn "*andn<mode>3"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(and:I48 (not:I48 (match_operand:I48 1 "e2k_src2_operand" "ri"))
		 (match_operand:I48 2 "register_operand" "r")))]
  ""
  "andn<sd>\t%2, %1, %0")

(define_insn "*orn<mode>3"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(ior:I48 (not:I48 (match_operand:I48 1 "e2k_src2_operand" "ri"))
		 (match_operand:I48 2 "register_operand" "r")))]
  ""
  "orn<sd>\t%2, %1, %0")

(define_insn "*xorn<mode>3"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(not:I48 (xor:I48 (match_operand:I48 1 "register_operand" "%r")
			  (match_operand:I48 2 "e2k_src2_operand" "ri"))))]
  ""
  "xorn<sd>\t%1, %2, %0")

(define_insn "one_cmpl<mode>2"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(not:I48 (match_operand:I48 1 "register_operand" "r")))]
  ""
  "xorn<sd>\t%1, 0x0, %0")

(define_code_iterator SHIFT [ashift lshiftrt ashiftrt rotate rotatert])
(define_code_attr shift [(ashift "shl") (lshiftrt "shr") (ashiftrt "sar")
			 (rotate "scl") (rotatert "scr")])
(define_code_attr shift_optab [(ashift "ashl") (lshiftrt "lshr")
			       (ashiftrt "ashr") (rotate "rotl")
			       (rotatert "rotr")])

;; The count has the width of the operation: the spec doesn't say whether
;; shld reads only the low bits of its count.
(define_insn "<shift_optab><mode>3"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(SHIFT:I48 (match_operand:I48 1 "register_operand" "r")
		   (match_operand:I48 2 "e2k_src2_operand" "ri")))]
  ""
  "<shift><sd>\t%1, %2, %0")

(define_insn "clz<mode>2"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(clz:I48 (match_operand:I48 1 "register_operand" "r")))]
  ""
  "lzcnt<sd>\t%1, %0"
  [(set_attr "type" "alu14")])

(define_insn "popcount<mode>2"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(popcount:I48 (match_operand:I48 1 "register_operand" "r")))]
  ""
  "popcnt<sd>\t%1, %0"
  [(set_attr "type" "alu14")])

;; ---------------------------------------------------------------------
;; Floating point (single and double in the integer registers)
;; ---------------------------------------------------------------------

(define_code_iterator FARITH [plus minus mult])
(define_code_attr farith [(plus "fadd") (minus "fsub") (mult "fmul")])
(define_code_attr farith_optab [(plus "add") (minus "sub") (mult "mul")])

(define_insn "<farith_optab><mode>3"
  [(set (match_operand:F 0 "register_operand" "=r")
	(FARITH:F (match_operand:F 1 "register_operand" "r")
		  (match_operand:F 2 "register_operand" "r")))]
  ""
  "<farith><sd>\t%1, %2, %0"
  [(set_attr "type" "fp")])

(define_insn "div<mode>3"
  [(set (match_operand:F 0 "register_operand" "=r")
	(div:F (match_operand:F 1 "register_operand" "r")
	       (match_operand:F 2 "register_operand" "r")))]
  ""
  "fdiv<sd>\t%1, %2, %0"
  [(set_attr "type" "fdiv")])

(define_insn "sqrtsf2"
  [(set (match_operand:SF 0 "register_operand" "=r")
	(sqrt:SF (match_operand:SF 1 "register_operand" "r")))]
  ""
  "fsqrts\t%1, %0"
  [(set_attr "type" "fdiv")])

;; fsqrtid gives a first approximation, fsqrttd the IEEE result (guide 10.4.2).
(define_expand "sqrtdf2"
  [(set (match_operand:DF 0 "register_operand")
	(sqrt:DF (match_operand:DF 1 "register_operand")))]
  ""
{
  rtx t = gen_reg_rtx (DFmode);
  emit_insn (gen_e2k_fsqrtid (t, operands[1]));
  emit_insn (gen_e2k_fsqrttd (operands[0], operands[1], t));
  DONE;
})

(define_insn "e2k_fsqrtid"
  [(set (match_operand:DF 0 "register_operand" "=r")
	(unspec:DF [(match_operand:DF 1 "register_operand" "r")] UNSPEC_FSQRTI))]
  ""
  "fsqrtid\t%1, %0"
  [(set_attr "type" "fdiv")])

(define_insn "e2k_fsqrttd"
  [(set (match_operand:DF 0 "register_operand" "=r")
	(sqrt:DF (match_operand:DF 1 "register_operand" "r")))
   (use (match_operand:DF 2 "register_operand" "r"))]
  ""
  "fsqrttd\t%1, %2, %0"
  [(set_attr "type" "fdiv")])

(define_insn "neg<mode>2"
  [(set (match_operand:F 0 "register_operand" "=r")
	(neg:F (match_operand:F 1 "register_operand" "r")))]
  ""
  "xor<sd>\t%1, <SIGNBIT>, %0")

(define_insn "abs<mode>2"
  [(set (match_operand:F 0 "register_operand" "=r")
	(abs:F (match_operand:F 1 "register_operand" "r")))]
  ""
  "andn<sd>\t%1, <SIGNBIT>, %0")

(define_insn "extendsfdf2"
  [(set (match_operand:DF 0 "register_operand" "=r")
	(float_extend:DF (match_operand:SF 1 "register_operand" "r")))]
  ""
  "fstofd\t%1, %0"
  [(set_attr "type" "fcvt")])

(define_insn "truncdfsf2"
  [(set (match_operand:SF 0 "register_operand" "=r")
	(float_truncate:SF (match_operand:DF 1 "register_operand" "r")))]
  ""
  "fdtofs\t%1, %0"
  [(set_attr "type" "fcvt")])

(define_mode_attr ifl [(SI "s") (DI "d")])

(define_insn "float<I48:mode><F:mode>2"
  [(set (match_operand:F 0 "register_operand" "=r")
	(float:F (match_operand:I48 1 "register_operand" "r")))]
  ""
  "i<I48:sd>tof<F:sd>\t%1, %0"
  [(set_attr "type" "fcvt")])

(define_insn "fix_trunc<F:mode><I48:mode>2"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(fix:I48 (match_operand:F 1 "register_operand" "r")))]
  ""
  "f<F:sd>toi<I48:sd>tr\t%1, %0"
  [(set_attr "type" "fcvt")])

;; ---------------------------------------------------------------------
;; long double (XFmode) in a register pair: mantissa, then the 16-bit
;; sign and exponent.  Each operation assembles the extended register with
;; movif, operates and splits the result with movfi, so no extended
;; value ever lives across a call or a spill.
;; ---------------------------------------------------------------------

(define_code_iterator XARITH [plus minus mult div])
(define_code_attr xarith [(plus "fxaddxx") (minus "fxsubxx")
			  (mult "fxmulxx") (div "fxdivxx")])
(define_code_attr xarith_optab [(plus "add") (minus "sub")
				(mult "mul") (div "div")])

(define_insn "<xarith_optab>xf3"
  [(set (match_operand:XF 0 "register_operand" "=&r")
	(XARITH:XF (match_operand:XF 1 "register_operand" "r")
		   (match_operand:XF 2 "register_operand" "r")))
   (clobber (match_scratch:DI 3 "=&r"))
   (clobber (match_scratch:DI 4 "=&r"))]
  ""
  "movif\t%1, %H1, %3\n\tmovif\t%2, %H2, %4%#<xarith>\t%3, %4, %3%#movfi\t%3, %H0\n\taddd\t%3, 0x0, %0"
  [(set_attr "type" "multi")])

(define_insn "negxf2"
  [(set (match_operand:XF 0 "register_operand" "=&r")
	(neg:XF (match_operand:XF 1 "register_operand" "r")))]
  ""
  "addd\t%1, 0x0, %0\n\txors\t%H1, 0x8000, %H0")

(define_insn "absxf2"
  [(set (match_operand:XF 0 "register_operand" "=&r")
	(abs:XF (match_operand:XF 1 "register_operand" "r")))]
  ""
  "addd\t%1, 0x0, %0\n\tandns\t%H1, 0x8000, %H0")

(define_insn "extend<mode>xf2"
  [(set (match_operand:XF 0 "register_operand" "=&r")
	(float_extend:XF (match_operand:F 1 "register_operand" "r")))
   (clobber (match_scratch:DI 2 "=&r"))]
  ""
  "f<sd>tofx\t%1, %2%#movfi\t%2, %H0\n\taddd\t%2, 0x0, %0"
  [(set_attr "type" "multi")])

(define_insn "truncxf<mode>2"
  [(set (match_operand:F 0 "register_operand" "=r")
	(float_truncate:F (match_operand:XF 1 "register_operand" "r")))
   (clobber (match_scratch:DI 2 "=&r"))]
  ""
  "movif\t%1, %H1, %2%#fxtof<sd>\t%2, %0"
  [(set_attr "type" "multi")])

(define_insn "float<mode>xf2"
  [(set (match_operand:XF 0 "register_operand" "=&r")
	(float:XF (match_operand:I48 1 "register_operand" "r")))
   (clobber (match_scratch:DI 2 "=&r"))]
  ""
  "i<sd>tofx\t%1, %2%#movfi\t%2, %H0\n\taddd\t%2, 0x0, %0"
  [(set_attr "type" "multi")])

(define_insn "fix_truncxf<mode>2"
  [(set (match_operand:I48 0 "register_operand" "=r")
	(fix:I48 (match_operand:XF 1 "register_operand" "r")))
   (clobber (match_scratch:DI 2 "=&r"))]
  ""
  "movif\t%1, %H1, %2%#fxtoi<sd>tr\t%2, %0"
  [(set_attr "type" "multi")])

;; ---------------------------------------------------------------------
;; Compares, branches, conditional moves
;;
;; Compares write a predicate register.  Before register allocation a
;; compare and its user are one insn with a predicate scratch; after it
;; they are split so the scheduler can separate them.
;; ---------------------------------------------------------------------

(define_insn "*cmp<mode>_pred"
  [(set (match_operand:BI 0 "register_operand" "=j")
	(match_operator:BI 1 "e2k_direct_int_cmp_operator"
	  [(match_operand:I48 2 "e2k_src1_operand" "rI")
	   (match_operand:I48 3 "e2k_src2_operand" "ri")]))]
  ""
  "cmp%K1<sd>b\t%2, %3, %0"
  [(set_attr "type" "cmp")])

(define_insn "*fcmp<mode>_pred"
  [(set (match_operand:BI 0 "register_operand" "=j")
	(match_operator:BI 1 "e2k_direct_fp_cmp_operator"
	  [(match_operand:F 2 "register_operand" "r")
	   (match_operand:F 3 "register_operand" "r")]))]
  ""
  "fcmp%K1<sd>b\t%2, %3, %0"
  [(set_attr "type" "fcmp")])

(define_insn "*fcmpxf_pred"
  [(set (match_operand:BI 0 "register_operand" "=j")
	(match_operator:BI 1 "e2k_direct_fp_cmp_operator"
	  [(match_operand:XF 2 "register_operand" "r")
	   (match_operand:XF 3 "register_operand" "r")]))
   (clobber (match_operand:DI 4 "register_operand" "=&r"))
   (clobber (match_operand:DI 5 "register_operand" "=&r"))]
  ""
  "movif\t%2, %H2, %4\n\tmovif\t%3, %H3, %5%#fxcmp%K1xb\t%4, %5, %0"
  [(set_attr "type" "multi")])

(define_insn "*branch_pred"
  [(set (pc)
	(if_then_else (match_operator 0 "e2k_pred_test_operator"
			[(match_operand:BI 1 "register_operand" "j")
			 (const_int 0)])
		      (label_ref (match_operand 2))
		      (pc)))]
  ""
  "ibranch\t%l2 ? %C0%1"
  [(set_attr "type" "branch")])

(define_expand "cbranch<mode>4"
  [(parallel
     [(set (pc)
	   (if_then_else (match_operator 0 "e2k_int_cmp_operator"
			   [(match_operand:I48 1 "register_operand")
			    (match_operand:I48 2 "e2k_src2_operand")])
			 (label_ref (match_operand 3))
			 (pc)))
      (clobber (scratch:BI))])]
  "")

(define_insn_and_split "*cbranch<mode>4"
  [(set (pc)
	(if_then_else (match_operator 0 "e2k_int_cmp_operator"
			[(match_operand:I48 1 "register_operand" "r")
			 (match_operand:I48 2 "e2k_src2_operand" "ri")])
		      (label_ref (match_operand 3))
		      (pc)))
   (clobber (match_scratch:BI 4 "=j"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  e2k_split_compare_branch (operands, <MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_expand "cbranch<mode>4"
  [(parallel
     [(set (pc)
	   (if_then_else (match_operator 0 "e2k_fp_cmp_operator"
			   [(match_operand:F 1 "register_operand")
			    (match_operand:F 2 "register_operand")])
			 (label_ref (match_operand 3))
			 (pc)))
      (clobber (scratch:BI))])]
  "")

(define_insn_and_split "*cbranch<mode>4"
  [(set (pc)
	(if_then_else (match_operator 0 "e2k_fp_cmp_operator"
			[(match_operand:F 1 "register_operand" "r")
			 (match_operand:F 2 "register_operand" "r")])
		      (label_ref (match_operand 3))
		      (pc)))
   (clobber (match_scratch:BI 4 "=j"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  e2k_split_compare_branch (operands, <MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_expand "cbranchxf4"
  [(parallel
     [(set (pc)
	   (if_then_else (match_operator 0 "e2k_fp_cmp_operator"
			   [(match_operand:XF 1 "register_operand")
			    (match_operand:XF 2 "register_operand")])
			 (label_ref (match_operand 3))
			 (pc)))
      (clobber (scratch:BI))
      (clobber (scratch:DI))
      (clobber (scratch:DI))])]
  "")

(define_insn_and_split "*cbranchxf4"
  [(set (pc)
	(if_then_else (match_operator 0 "e2k_fp_cmp_operator"
			[(match_operand:XF 1 "register_operand" "r")
			 (match_operand:XF 2 "register_operand" "r")])
		      (label_ref (match_operand 3))
		      (pc)))
   (clobber (match_scratch:BI 4 "=j"))
   (clobber (match_scratch:DI 5 "=&r"))
   (clobber (match_scratch:DI 6 "=&r"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  e2k_split_compare_branch (operands, XFmode);
  DONE;
}
  [(set_attr "type" "multi")])

;; merge: src1 when the predicate is false, src2 when true (guide 10.3.9).
(define_insn "*merge<mode>"
  [(set (match_operand:GPRM 0 "register_operand" "=r")
	(if_then_else:GPRM
	  (match_operator 1 "e2k_pred_test_operator"
	    [(match_operand:BI 2 "register_operand" "j")
	     (const_int 0)])
	  (match_operand:GPRM 3 "e2k_src2_operand" "ri")
	  (match_operand:GPRM 4 "e2k_src1_operand" "rI")))]
  ""
  "merge<sd>\t%4, %3, %0, %C1%2")

(define_expand "cstore<mode>4"
  [(parallel
     [(set (match_operand:DI 0 "register_operand")
	   (match_operator:DI 1 "e2k_int_cmp_operator"
	     [(match_operand:I48 2 "register_operand")
	      (match_operand:I48 3 "e2k_src2_operand")]))
      (clobber (scratch:BI))])]
  "")

(define_insn_and_split "*cstore<mode>4"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(match_operator:DI 1 "e2k_int_cmp_operator"
	  [(match_operand:I48 2 "register_operand" "r")
	   (match_operand:I48 3 "e2k_src2_operand" "ri")]))
   (clobber (match_scratch:BI 4 "=j"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  e2k_split_cstore (operands, <MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_expand "cstore<mode>4"
  [(parallel
     [(set (match_operand:DI 0 "register_operand")
	   (match_operator:DI 1 "e2k_fp_cmp_operator"
	     [(match_operand:F 2 "register_operand")
	      (match_operand:F 3 "register_operand")]))
      (clobber (scratch:BI))])]
  "")

(define_insn_and_split "*cstore<mode>4"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(match_operator:DI 1 "e2k_fp_cmp_operator"
	  [(match_operand:F 2 "register_operand" "r")
	   (match_operand:F 3 "register_operand" "r")]))
   (clobber (match_scratch:BI 4 "=j"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  e2k_split_cstore (operands, <MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_expand "mov<GPRM:mode>cc"
  [(parallel
     [(set (match_operand:GPRM 0 "register_operand")
	   (if_then_else:GPRM (match_operand 1 "comparison_operator")
			      (match_operand:GPRM 2 "e2k_src2_operand")
			      (match_operand:GPRM 3 "e2k_src1_operand")))
      (clobber (scratch:BI))])]
  ""
{
  if (e2k_expand_movcc (operands))
    DONE;
  FAIL;
})

(define_insn_and_split "*movcc<GPRM:mode><I48:mode>"
  [(set (match_operand:GPRM 0 "register_operand" "=r")
	(if_then_else:GPRM
	  (match_operator 1 "e2k_int_cmp_operator"
	    [(match_operand:I48 2 "register_operand" "r")
	     (match_operand:I48 3 "e2k_src2_operand" "ri")])
	  (match_operand:GPRM 4 "e2k_src2_operand" "ri")
	  (match_operand:GPRM 5 "e2k_src1_operand" "rI")))
   (clobber (match_scratch:BI 6 "=j"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  e2k_split_movcc (operands, <I48:MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_insn_and_split "*movcc<GPRM:mode><F:mode>"
  [(set (match_operand:GPRM 0 "register_operand" "=r")
	(if_then_else:GPRM
	  (match_operator 1 "e2k_fp_cmp_operator"
	    [(match_operand:F 2 "register_operand" "r")
	     (match_operand:F 3 "register_operand" "r")])
	  (match_operand:GPRM 4 "e2k_src2_operand" "ri")
	  (match_operand:GPRM 5 "e2k_src1_operand" "rI")))
   (clobber (match_scratch:BI 6 "=j"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  e2k_split_movcc (operands, <F:MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

;; ---------------------------------------------------------------------
;; Jumps
;; ---------------------------------------------------------------------

(define_insn "jump"
  [(set (pc) (label_ref (match_operand 0)))]
  ""
  "ibranch\t%l0"
  [(set_attr "type" "branch")])

;; An indirect jump goes through a CTPR: movtd, then ct (9 cycles apart
;; to avoid a stall, spec/isa/timing.md).
(define_insn "indirect_jump"
  [(set (pc) (match_operand:DI 0 "register_operand" "r"))
   (clobber (reg:DI CTPR2_REGNUM))]
  ""
  "movtd\t%0, %%ctpr2%#ct\t%%ctpr2"
  [(set_attr "type" "multi")])

(define_expand "tablejump"
  [(parallel [(set (pc) (match_operand:DI 0 "register_operand"))
	      (use (label_ref (match_operand 1)))
	      (clobber (reg:DI CTPR2_REGNUM))])]
  ""
{
  /* PIC jump tables hold offsets from the table (ADDR_DIFF_VEC).  */
  if (flag_pic)
    {
      rtx base = force_reg (Pmode, gen_rtx_LABEL_REF (Pmode, operands[1]));
      operands[0] = expand_simple_binop (Pmode, PLUS, operands[0], base,
					 NULL_RTX, 0, OPTAB_DIRECT);
      operands[0] = force_reg (Pmode, operands[0]);
    }
})

(define_insn "*tablejump"
  [(set (pc) (match_operand:DI 0 "register_operand" "r"))
   (use (label_ref (match_operand 1)))
   (clobber (reg:DI CTPR2_REGNUM))]
  ""
  "movtd\t%0, %%ctpr2%#ct\t%%ctpr2"
  [(set_attr "type" "multi")])

;; Loop back edges become prepared transfers: a taken ibranch costs 6
;; cycles on the 4C, a ct whose CTPR was prepared outside the loop none
;; (see e2k_prepare_loop_branches).
(define_insn "e2k_disp_label"
  [(set (match_operand:DI 0 "e2k_ctpr_operand" "=t")
	(unspec:DI [(label_ref (match_operand 1))] UNSPEC_DISP))]
  ""
  "disp\t%0, %l1"
  [(set_attr "type" "disp")])

(define_insn "*ct_pred"
  [(set (pc)
	(if_then_else (match_operator 0 "e2k_pred_test_operator"
			[(match_operand:BI 1 "register_operand" "j")
			 (const_int 0)])
		      (label_ref (match_operand 2))
		      (pc)))
   (use (match_operand:DI 3 "e2k_ctpr_operand" "t"))]
  ""
  "ct\t%3 ? %C0%1"
  [(set_attr "type" "ct")])

(define_insn "*ct_jump"
  [(set (pc) (label_ref (match_operand 0)))
   (use (match_operand:DI 1 "e2k_ctpr_operand" "t"))]
  ""
  "ct\t%1"
  [(set_attr "type" "ct")])

;; ---------------------------------------------------------------------
;; Calls
;;
;; disp/movtd prepares %ctpr1 as a separate insn so that the scheduler
;; can hoist it (disp -> call 5 cycles, movtd -> call 9).
;; ---------------------------------------------------------------------

(define_expand "call"
  [(parallel [(call (match_operand 0)
		    (match_operand 1))
	      (use (match_operand 2))
	      (use (match_operand 3))])]
  ""
{
  e2k_expand_call (NULL_RTX, operands[0], operands[1], operands[3]);
  DONE;
})

(define_expand "call_value"
  [(parallel [(set (match_operand 0)
		   (call (match_operand 1)
			 (match_operand 2)))
	      (use (match_operand 3))])]
  ""
{
  e2k_expand_call (operands[0], operands[1], operands[2], NULL_RTX);
  DONE;
})

(define_insn "e2k_disp"
  [(set (reg:DI CTPR1_REGNUM)
	(unspec:DI [(match_operand:DI 0 "e2k_symbolic_operand")] UNSPEC_DISP))]
  ""
  "disp\t%%ctpr1, %0"
  [(set_attr "type" "disp")])

(define_insn "e2k_movtd_ctpr1"
  [(set (reg:DI CTPR1_REGNUM)
	(unspec:DI [(match_operand:DI 0 "register_operand" "r")] UNSPEC_MOVTD))]
  ""
  "movtd\t%0, %%ctpr1"
  [(set_attr "type" "movctp")])

(define_insn "e2k_call"
  [(call (mem:DI (reg:DI CTPR1_REGNUM))
	 (match_operand 0))]
  ""
  { return e2k_output_call (); }
  [(set_attr "type" "call")])

(define_insn "e2k_call_value"
  [(set (match_operand 0)
	(call (mem:DI (reg:DI CTPR1_REGNUM))
	      (match_operand 1)))]
  ""
  { return e2k_output_call (); }
  [(set_attr "type" "call")])

;; __builtin_apply and untyped calls.
(define_expand "untyped_call"
  [(parallel [(call (match_operand 0 "")
		    (const_int 0))
	      (match_operand 1 "")
	      (match_operand 2 "")])]
  ""
{
  int i;
  e2k_expand_call (NULL_RTX, operands[0], const0_rtx, NULL_RTX);
  for (i = 0; i < XVECLEN (operands[2], 0); i++)
    {
      rtx set = XVECEXP (operands[2], 0, i);
      emit_move_insn (SET_DEST (set), SET_SRC (set));
    }
  emit_insn (gen_blockage ());
  DONE;
})

;; ---------------------------------------------------------------------
;; Prologue, epilogue, stack
;; ---------------------------------------------------------------------

(define_expand "prologue"
  [(const_int 0)]
  ""
{
  e2k_expand_prologue ();
  DONE;
})

(define_expand "epilogue"
  [(const_int 0)]
  ""
{
  e2k_expand_epilogue ();
  DONE;
})

;; setwd and setbn share CS1; the window size is only known once every
;; register has been assigned, so it is printed by e2k.cc at final time.
(define_insn "e2k_setwd"
  [(unspec_volatile [(const_int 0)] UNSPECV_SETWD)]
  ""
  { return e2k_output_setwd (); }
  [(set_attr "type" "setwd")])

(define_insn "e2k_getsp"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(unspec_volatile:DI [(match_operand:DI 1 "e2k_src2_operand" "ri")]
			    UNSPECV_GETSP))]
  ""
  "getsp\t%1, %0"
  [(set_attr "type" "getsp")])

(define_insn "e2k_return_prep"
  [(set (reg:DI CTPR3_REGNUM)
	(unspec:DI [(const_int 0)] UNSPEC_RETURN))]
  ""
  "return\t%%ctpr3"
  [(set_attr "type" "ret")])

(define_insn "e2k_return"
  [(return)
   (use (reg:DI CTPR3_REGNUM))]
  "reload_completed"
  "ct\t%%ctpr3"
  [(set_attr "type" "ct")])

(define_expand "allocate_stack"
  [(match_operand:DI 0 "register_operand")
   (match_operand:DI 1 "general_operand")]
  ""
{
  rtx neg = expand_unop (DImode, neg_optab, operands[1], NULL_RTX, 0);
  emit_insn (gen_e2k_getsp (stack_pointer_rtx, force_reg (DImode, neg)));
  emit_move_insn (operands[0], virtual_stack_dynamic_rtx);
  DONE;
})

;; USD is not a register: restoring the stack pointer means giving the
;; difference back with getsp.
(define_expand "restore_stack_block"
  [(match_operand:DI 0 "register_operand")
   (match_operand:DI 1 "register_operand")]
  ""
{
  rtx delta = expand_binop (DImode, sub_optab, operands[1],
			    stack_pointer_rtx, NULL_RTX, 0, OPTAB_LIB_WIDEN);
  emit_insn (gen_e2k_getsp (stack_pointer_rtx, force_reg (DImode, delta)));
  DONE;
})

(define_expand "restore_stack_nonlocal"
  [(match_operand:DI 0 "register_operand")
   (match_operand:DI 1 "memory_operand")]
  ""
{
  rtx old = force_reg (DImode, operands[1]);
  rtx delta = expand_binop (DImode, sub_optab, old,
			    stack_pointer_rtx, NULL_RTX, 0, OPTAB_LIB_WIDEN);
  emit_insn (gen_e2k_getsp (stack_pointer_rtx, force_reg (DImode, delta)));
  DONE;
})

(define_insn "blockage"
  [(unspec_volatile [(const_int 0)] UNSPECV_BLOCKAGE)]
  ""
  ""
  [(set_attr "type" "ghost")])

(define_insn "nop"
  [(const_int 0)]
  ""
  "nop"
  [(set_attr "type" "nop")])

;; ---------------------------------------------------------------------
;; PIC and TLS
;; ---------------------------------------------------------------------

;; GOT address: rrd %ip and the PC-relative _GLOBAL_OFFSET_TABLE_ literal
;; must be in the same wide instruction (spec/abi/elf.md).
(define_insn "e2k_gotbase"
  [(set (match_operand:DI 0 "register_operand" "=&r")
	(unspec:DI [(const_int 0)] UNSPEC_GOTBASE))
   (clobber (match_scratch:DI 1 "=&r"))]
  ""
  "%<rrd\t%%ip, %0\n\taddd\t0x0, _GLOBAL_OFFSET_TABLE_, %1%>%#addd\t%0, %1, %0"
  [(set_attr "type" "multi")])

(define_insn "*tls_le"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(plus:DI (reg:DI TP_REGNUM)
		 (unspec:DI [(match_operand:DI 1 "e2k_symbolic_operand")]
			    UNSPEC_TLS_LE)))]
  ""
  "addd\t%%g13, %1@TLS_LE, %0")

(define_insn "*gotoff"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(plus:DI (match_operand:DI 1 "register_operand" "r")
		 (unspec:DI [(match_operand:DI 2 "e2k_symbolic_operand")]
			    UNSPEC_GOTOFF)))]
  ""
  "addd\t%1, %2@GOTOFF, %0")

;; A copy GCC can't see through: the address of the buffer for results
;; over 64 bytes, so that stores into it aren't deleted as dead before
;; the epilogue (which copies it out) exists.
(define_insn "e2k_opaque_copy"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(unspec:DI [(match_operand:DI 1 "register_operand" "r")] UNSPEC_OPAQUE))]
  ""
  "addd\t%1, 0x0, %0")

;; ---------------------------------------------------------------------
;; Memory ordering
;; ---------------------------------------------------------------------

(define_expand "mem_thread_fence"
  [(match_operand:SI 0 "const_int_operand")]
  ""
{
  if (!is_mm_relaxed (memmodel_from_int (INTVAL (operands[0]))))
    emit_insn (gen_e2k_wait_ldst (e2k_barrier_mem ()));
  DONE;
})

;; wait ld_c, st_c: earlier loads and stores complete (spec/abi/atomics.md).
(define_insn "e2k_wait_ldst"
  [(set (match_operand:BLK 0 "")
	(unspec:BLK [(match_dup 0)] UNSPEC_WAIT))]
  ""
  "wait\tld_c = 1, st_c = 1"
  [(set_attr "type" "wait")])

;; ---------------------------------------------------------------------
;; Atomics (spec/abi/atomics.md): every read-modify-write is a lock-wait
;; load (MAS 0x7, ALC0) and a wait-unlock store (MAS 0x2, ALC2) whose wide
;; instruction also holds "rbranch" (= ibranch ? %MLOCK) back to the load,
;; the same sequence lcc emits, whatever the memory order.  These insns
;; carry a local label, so they print their own braces (type "raw") and
;; let gas pad them (.accept strict_delay), as lcc does.
;; ---------------------------------------------------------------------

(define_mode_iterator ATM [QI HI SI DI])
(define_mode_attr ldsz [(QI "b") (HI "h") (SI "w") (DI "d")])
;; Width of the ALU operation on the loaded value.
(define_mode_attr opsz [(QI "s") (HI "s") (SI "s") (DI "d")])

(define_expand "atomic_compare_and_swap<mode>"
  [(match_operand:SI 0 "register_operand")	;; bool success
   (match_operand:ATM 1 "register_operand")	;; old value
   (match_operand:ATM 2 "memory_operand")	;; memory
   (match_operand:ATM 3 "register_operand")	;; expected
   (match_operand:ATM 4 "register_operand")	;; desired
   (match_operand:SI 5 "const_int_operand")	;; is_weak
   (match_operand:SI 6 "const_int_operand")	;; success model
   (match_operand:SI 7 "const_int_operand")]	;; failure model
  ""
{
  rtx mem = e2k_atomic_mem (operands[2]);
  rtx exp = convert_to_mode (DImode, operands[3], 1);
  rtx des = convert_to_mode (DImode, operands[4], 1);
  rtx old = gen_reg_rtx (DImode);
  rtx ok = gen_reg_rtx (DImode);
  emit_insn (gen_e2k_cas<mode> (old, ok, mem, force_reg (DImode, exp),
				force_reg (DImode, des)));
  emit_move_insn (operands[1], gen_lowpart (<MODE>mode, old));
  emit_move_insn (operands[0], gen_lowpart (SImode, ok));
  DONE;
})

(define_insn "e2k_cas<mode>"
  [(set (match_operand:DI 0 "register_operand" "=&r")
	(unspec_volatile:DI [(match_operand:ATM 2 "memory_operand" "+m")
			     (match_operand:DI 3 "register_operand" "r")
			     (match_operand:DI 4 "register_operand" "r")]
			    UNSPECV_CAS))
   (set (match_dup 2) (unspec_volatile:ATM [(const_int 0)] UNSPECV_CAS))
   (set (match_operand:DI 1 "register_operand" "=&r")
	(unspec_volatile:DI [(const_int 0)] UNSPECV_CAS))
   (clobber (match_scratch:BI 5 "=&j"))
   (clobber (match_scratch:DI 6 "=&r"))]
  ""
  ".accept\tstrict_delay\n1:\n\tnop\t1\n\t{\n\tld<ldsz>,0\t%2, %0, mas = 0x7\n\tnop\t2\n\t}\n\t{\n\tcmpe<opsz>b,0\t%0, %3, %5\n\tnop\t1\n\t}\n\t{\n\tmerge<opsz>,0\t%0, %4, %6, %5\n\tmerged,1\t0x0, 0x1, %1, %5\n\t}\n\t{\n\tst<ldsz>,2\t%2, %6, mas = 0x2\n\trbranch\t1b\n\t}\n\t.ignore\tstrict_delay"
  [(set_attr "type" "raw")])

(define_code_iterator ATOP [plus minus and ior xor])
(define_code_attr atop [(plus "add") (minus "sub") (and "and") (ior "or")
			(xor "xor")])
(define_code_attr atop_name [(plus "add") (minus "sub") (and "and")
			     (ior "or") (xor "xor")])

(define_expand "atomic_fetch_<atop_name><mode>"
  [(match_operand:ATM 0 "register_operand")
   (match_operand:ATM 1 "memory_operand")
   (ATOP:ATM (match_dup 1) (match_operand:ATM 2 "register_operand"))
   (match_operand:SI 3 "const_int_operand")]
  ""
{
  rtx mem = e2k_atomic_mem (operands[1]);
  emit_insn (gen_e2k_fetch_<atop_name><mode> (operands[0], mem,
					       force_reg (<MODE>mode,
							  operands[2])));
  DONE;
})

(define_insn "e2k_fetch_<atop_name><mode>"
  [(set (match_operand:ATM 0 "register_operand" "=&r")
	(match_operand:ATM 1 "memory_operand" "+m"))
   (set (match_dup 1)
	(unspec_volatile:ATM [(ATOP:ATM (match_dup 1)
					(match_operand:ATM 2 "register_operand" "r"))]
			     UNSPECV_ATOMIC))
   (clobber (match_scratch:DI 3 "=&r"))]
  ""
  ".accept\tstrict_delay\n1:\n\tnop\t1\n\t{\n\tld<ldsz>,0\t%1, %0, mas = 0x7\n\tnop\t2\n\t}\n\t{\n\t<atop><opsz>,0\t%0, %2, %3\n\t}\n\t{\n\tst<ldsz>,2\t%1, %3, mas = 0x2\n\trbranch\t1b\n\t}\n\t.ignore\tstrict_delay"
  [(set_attr "type" "raw")])

(define_expand "atomic_exchange<mode>"
  [(match_operand:ATM 0 "register_operand")
   (match_operand:ATM 1 "memory_operand")
   (match_operand:ATM 2 "register_operand")
   (match_operand:SI 3 "const_int_operand")]
  ""
{
  rtx mem = e2k_atomic_mem (operands[1]);
  emit_insn (gen_e2k_exchange<mode> (operands[0], mem,
				     force_reg (<MODE>mode, operands[2])));
  DONE;
})

(define_insn "e2k_exchange<mode>"
  [(set (match_operand:ATM 0 "register_operand" "=&r")
	(match_operand:ATM 1 "memory_operand" "+m"))
   (set (match_dup 1)
	(unspec_volatile:ATM [(match_operand:ATM 2 "register_operand" "r")]
			     UNSPECV_ATOMIC))]
  ""
  ".accept\tstrict_delay\n1:\n\tnop\t1\n\t{\n\tld<ldsz>,0\t%1, %0, mas = 0x7\n\tnop\t2\n\t}\n\t{\n\tst<ldsz>,2\t%1, %2, mas = 0x2\n\trbranch\t1b\n\t}\n\t.ignore\tstrict_delay"
  [(set_attr "type" "raw")])

;; Loads: acquire adds a dummy use that waits for the value; seq_cst also
;; waits for earlier loads and stores first.  Stores: release waits
;; first; seq_cst also waits for the store to complete.
(define_expand "atomic_load<mode>"
  [(match_operand:ATM 0 "register_operand")
   (match_operand:ATM 1 "memory_operand")
   (match_operand:SI 2 "const_int_operand")]
  ""
{
  enum memmodel model = memmodel_from_int (INTVAL (operands[2]));
  if (is_mm_seq_cst (model))
    emit_insn (gen_e2k_wait_ldst (e2k_barrier_mem ()));
  emit_move_insn (operands[0], operands[1]);
  if (!is_mm_relaxed (model))
    emit_insn (gen_e2k_dummy_use (e2k_barrier_mem (),
				  gen_lowpart (SImode, operands[0])));
  DONE;
})

(define_expand "atomic_store<mode>"
  [(match_operand:ATM 0 "memory_operand")
   (match_operand:ATM 1 "register_operand")
   (match_operand:SI 2 "const_int_operand")]
  ""
{
  enum memmodel model = memmodel_from_int (INTVAL (operands[2]));
  if (!is_mm_relaxed (model))
    emit_insn (gen_e2k_wait_ldst (e2k_barrier_mem ()));
  emit_move_insn (operands[0], force_reg (<MODE>mode, operands[1]));
  if (is_mm_seq_cst (model))
    emit_insn (gen_e2k_wait_st (e2k_barrier_mem ()));
  DONE;
})

(define_insn "e2k_dummy_use"
  [(set (match_operand:BLK 0 "")
	(unspec:BLK [(match_dup 0)
		     (match_operand:SI 1 "register_operand" "r")] UNSPEC_WAIT))]
  ""
  "adds,sm\t%1, 0x0, %%empty"
  [(set_attr "type" "alu")])

(define_insn "e2k_wait_st"
  [(set (match_operand:BLK 0 "")
	(unspec:BLK [(match_dup 0) (const_int 1)] UNSPEC_WAIT))]
  ""
  "wait\tst_c = 1"
  [(set_attr "type" "wait")])
