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
   UNSPEC_FSQRTT
   UNSPEC_FMAX
   UNSPEC_FMIN
   UNSPEC_FRINT_FLOOR
   UNSPEC_FRINT_CEIL
   UNSPEC_FRINT_TRUNC
   UNSPEC_FRINT_EVEN
   UNSPEC_FRINT_RINT
   UNSPEC_FRINT_NEARBY
   UNSPEC_ADD_FLAGS
   UNSPEC_SMULX_FLAGS
   UNSPEC_UMULX_FLAGS
   UNSPEC_CCTOPO
   UNSPEC_CMPO
   UNSPEC_FSCALE
   UNSPEC_WAIT
   UNSPEC_RETURN
   UNSPEC_OPAQUE
   UNSPEC_FCMPU
   UNSPEC_FCMPO
   UNSPEC_XUNPACK
   UNSPEC_DOLOOP
   UNSPEC_LOOP_END
   UNSPEC_SETBN_B
   UNSPEC_LDLOCK
   UNSPEC_LDCHK
   UNSPEC_MLOCK
   UNSPEC_PMERGE
   UNSPEC_PSHUFB
   UNSPEC_QPLO
   UNSPEC_QPPERMB
   UNSPEC_QPMERGE
   UNSPEC_QPFCMP
   UNSPEC_QPHI
   UNSPEC_QPPACK
   UNSPEC_PSADBW
   UNSPEC_ADDCD
   UNSPEC_ADDCDC
   UNSPEC_SUBCD
   UNSPEC_SUBCDC
   UNSPEC_PHADD
   UNSPEC_PMADDH
   UNSPEC_PUNPCKL
   UNSPEC_PUNPCKH
   UNSPEC_PSLL
   UNSPEC_PSRL
   UNSPEC_PSRA
   UNSPEC_MOVA
   UNSPEC_STAA
   UNSPEC_LDISP])

(define_c_enum "unspecv"
  [UNSPECV_SETWD
   UNSPECV_GETSP
   UNSPECV_RETURN
   UNSPECV_BLOCKAGE
   UNSPECV_WAIT
   UNSPECV_CAS
   UNSPECV_ATOMIC
   UNSPECV_RRD_CR0HI
   UNSPECV_XPACK
   UNSPECV_RRS
   UNSPECV_RWS
   UNSPECV_THUNK_JUMP
   UNSPECV_RWD_LSR
   UNSPECV_RWD_LSR1
   UNSPECV_LSR_WAIT
   UNSPECV_SETBN
   UNSPECV_NOP_BUNDLE
   UNSPECV_AAURWD
   UNSPECV_AAURW_INCR
   UNSPECV_AAURW_STI
   UNSPECV_BAP
   UNSPECV_AABF
   UNSPECV_APB_STOP])

;; Instruction classes, used by the pipeline description (e2k-sched.md).
;;  alu      integer add/logic/shift/sxt/merge: any of ALC0-5
;;  alu14    lzcnt, popcnt: ALC1, ALC4
;;  alu0134  bitrev: ALC0,1,3,4, 1 cycle
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
  "alu,alu14,alu0134,mul,div,fp,fma,ffma,fcvt,fdiv,cmp,fcmp,plog,load,ldlock,ldchk,store,getsp,movctp,disp,ret,branch,ct,call,setwd,wait,multi,raw,ghost,nop,pint,pint14,pmul,pany,mova,aau,bap,flag,flagmul,cctop,fscale"
  (const_string "alu"))

;; Loads and stores with a MAS, which CS1 holds (spec/isa/bundle.md,
;; "CS1": gas, "cannot encode MAS: CS1 syllable is busy").
(define_attr "mas" "no,yes" (const_string "no"))

;; Operations with an ALES (spec/isa/reservations.yaml, "ales" other than
;; none): a half-syllable in ALC0, 1, 3 or 4, and on v4+ the ALES2/ALES5
;; word in ALC2 or 5.  e2k_fit_bundles counts them in a wide
;; instruction's size.  By type, as the operations the port emits have
;; them (the multiplies, FP divides and roots, packed operations, the
;; flag operations, insfs/insfd, rrd/rrs/rws, getsp, the AAU registers,
;; conversions with rounding modes), erring towards "yes"; fcmpud*f too.
(define_attr "ales" "no,yes"
  (if_then_else
    (eq_attr "type" "mul,fdiv,fma,ffma,fcvt,pint,pint14,pmul,pany,flag,flagmul,getsp,aau,fscale,alu0134")
    (const_string "yes")
    (const_string "no")))

;; Operations that may run under a predicate ("op ? %predN"; the
;; condition prints with "%?" at the end of the line).  GCC's if-conversion
;; after reload makes them (define_cond_exec below).
(define_attr "predicable" "no,yes" (const_string "no"))
;; Alternatives the predicated version leaves out (gensupport.cc makes
;; this take "predicable" per alternative into account).
(define_attr "enabled" "no,yes" (const_string "yes"))

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
   adds\t%1, 0x0, %0%?
   adds\t0x0, %1, %0%?
   ldb\t%1, %0%?
   stb\t%0, %1%?"
  [(set_attr "type" "alu,alu,load,store")
   (set_attr "predicable" "yes,yes,yes,yes")])

(define_insn "*movhi_insn"
  [(set (match_operand:HI 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:HI 1 "e2k_move_operand"      "r,i,m,r"))]
  "register_operand (operands[0], HImode)
   || register_operand (operands[1], HImode)"
  "@
   adds\t%1, 0x0, %0%?
   adds\t0x0, %1, %0%?
   ldh\t%1, %0%?
   sth\t%0, %1%?"
  [(set_attr "type" "alu,alu,load,store")
   (set_attr "predicable" "yes,yes,yes,yes")])

(define_insn "*movsi_insn"
  [(set (match_operand:SI 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:SI 1 "e2k_move_operand"      "r,i,m,r"))]
  "register_operand (operands[0], SImode)
   || register_operand (operands[1], SImode)"
  "@
   adds\t%1, 0x0, %0%?
   adds\t0x0, %1, %0%?
   ldw\t%1, %0%?
   stw\t%0, %1%?"
  [(set_attr "type" "alu,alu,load,store")
   (set_attr "predicable" "yes,yes,yes,yes")])

(define_insn "*movsf_insn"
  [(set (match_operand:SF 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:SF 1 "e2k_move_operand"      "r,F,m,r"))]
  "register_operand (operands[0], SFmode)
   || register_operand (operands[1], SFmode)"
  "@
   adds\t%1, 0x0, %0%?
   adds\t0x0, %1, %0%?
   ldw\t%1, %0%?
   stw\t%0, %1%?"
  [(set_attr "type" "alu,alu,load,store")
   (set_attr "predicable" "yes,yes,yes,no")])

(define_insn "*movdi_insn"
  [(set (match_operand:DI 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:DI 1 "e2k_move_operand"      "r,i,m,r"))]
  "register_operand (operands[0], DImode)
   || register_operand (operands[1], DImode)"
  "@
   addd\t%1, 0x0, %0%?
   addd\t0x0, %1, %0%?
   ldd\t%1, %0%?
   std\t%0, %1%?"
  [(set_attr "type" "alu,alu,load,store")
   (set_attr "predicable" "yes,yes,yes,yes")])

(define_insn "*movdf_insn"
  [(set (match_operand:DF 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:DF 1 "e2k_move_operand"      "r,F,m,r"))]
  "register_operand (operands[0], DFmode)
   || register_operand (operands[1], DFmode)"
  "@
   addd\t%1, 0x0, %0%?
   addd\t0x0, %1, %0%?
   ldd\t%1, %0%?
   std\t%0, %1%?"
  [(set_attr "type" "alu,alu,load,store")
   (set_attr "predicable" "yes,yes,yes,no")])

;; Data speculation (DAM, spec/isa/speculation.md), made by the scheduler
;; in machine reorg (e2k_speculate_insn, e2k_gen_spec_check): a load
;; moved above stores that may write its memory becomes a lock load
;; (ld,sm mas=0x4 in ALC0), and a check load (mas=0x3 in ALC5, into the
;; same register) stays where the load was.  The check keeps the early
;; value if no store touched the bytes, else reloads; everything that
;; uses the value comes after the check.  The check's rbranch is still
;; needed (e2k_output_spec_load).
(define_mode_iterator SPECM [QI HI SI DI SF DF V8QI V4HI V2SI V2SF])

;; A lock load keeps the load's own SET (shared with its original
;; pattern; e2k_speculate_insn), so that an address the scheduler
;; rewrites to move the load past an increment of its base reaches it.
(define_insn "*e2k_ldlock<mode>"
  [(set (match_operand:SPECM 0 "e2k_register_operand" "=r")
	(match_operand:SPECM 1 "e2k_spec_load_operand" ""))
   (unspec [(const_int 0)] UNSPEC_LDLOCK)]
  ""
  { return e2k_output_spec_load (operands, true); }
  [(set_attr "type" "ldlock")])

(define_insn "*e2k_ldchk<mode>"
  [(set (match_operand:SPECM 0 "e2k_register_operand" "+r")
	(if_then_else:SPECM (ne (unspec [(match_dup 0)] UNSPEC_LDCHK)
				(const_int 0))
			    (match_operand:SPECM 1 "e2k_spec_load_operand" "")
			    (match_dup 0)))]
  ""
  { return e2k_output_spec_load (operands, false); }
  [(set_attr "type" "ldchk")
   ;; Under the condition of a load e2k_unpredicate_loads ran without it
   ;; (e2k_gen_spec_check).
   (set_attr "predicable" "yes")])

;; The check of a lock load in a pipelined loop's kernel (e2k_modsched):
;; when the entry was lost, its rbranch goes to code that redoes what
;; already used the early value, and back.
(define_insn "e2k_ldchk_jump<mode>"
  [(set (match_operand:SPECM 0 "e2k_register_operand" "+r")
	(if_then_else:SPECM (ne (unspec [(match_dup 0)] UNSPEC_LDCHK)
				(const_int 0))
			    (match_operand:SPECM 1 "e2k_spec_load_operand" "")
			    (match_dup 0)))
   (set (pc) (if_then_else (ne (unspec [(const_int 0)] UNSPEC_MLOCK)
			       (const_int 0))
			   (label_ref (match_operand 2))
			   (pc)))]
  ""
  { return e2k_output_ldchk_jump (operands); }
  [(set_attr "type" "ldchk")])

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
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(sign_extend:DI (match_operand:SI 1 "e2k_register_operand" "r")))]
  ""
  "sxt\t2, %1, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "extendhidi2"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(sign_extend:DI (match_operand:HI 1 "e2k_register_operand" "r")))]
  ""
  "sxt\t1, %1, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "extendqidi2"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(sign_extend:DI (match_operand:QI 1 "e2k_register_operand" "r")))]
  ""
  "sxt\t0, %1, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "extendhisi2"
  [(set (match_operand:SI 0 "e2k_register_operand" "=r")
	(sign_extend:SI (match_operand:HI 1 "e2k_register_operand" "r")))]
  ""
  "sxt\t1, %1, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "extendqisi2"
  [(set (match_operand:SI 0 "e2k_register_operand" "=r")
	(sign_extend:SI (match_operand:QI 1 "e2k_register_operand" "r")))]
  ""
  "sxt\t0, %1, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "extendqihi2"
  [(set (match_operand:HI 0 "e2k_register_operand" "=r")
	(sign_extend:HI (match_operand:QI 1 "e2k_register_operand" "r")))]
  ""
  "sxt\t0, %1, %0%?"
  [(set_attr "predicable" "yes")])

;; Loads always write the whole register, zero-extended (spec
;; registers.md, "dbl").
(define_insn "zero_extendsidi2"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r,r")
	(zero_extend:DI (match_operand:SI 1 "nonimmediate_operand" "r,m")))]
  ""
  "@
   sxt\t6, %1, %0%?
   ldw\t%1, %0%?"
  [(set_attr "type" "alu,load")
   (set_attr "predicable" "yes,yes")])

(define_insn "zero_extendhidi2"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r,r")
	(zero_extend:DI (match_operand:HI 1 "nonimmediate_operand" "r,m")))]
  ""
  "@
   sxt\t5, %1, %0%?
   ldh\t%1, %0%?"
  [(set_attr "type" "alu,load")
   (set_attr "predicable" "yes,yes")])

(define_insn "zero_extendqidi2"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r,r")
	(zero_extend:DI (match_operand:QI 1 "nonimmediate_operand" "r,m")))]
  ""
  "@
   sxt\t4, %1, %0%?
   ldb\t%1, %0%?"
  [(set_attr "type" "alu,load")
   (set_attr "predicable" "yes,yes")])

(define_insn "zero_extendhisi2"
  [(set (match_operand:SI 0 "e2k_register_operand" "=r,r")
	(zero_extend:SI (match_operand:HI 1 "nonimmediate_operand" "r,m")))]
  ""
  "@
   sxt\t5, %1, %0%?
   ldh\t%1, %0%?"
  [(set_attr "type" "alu,load")
   (set_attr "predicable" "yes,yes")])

(define_insn "zero_extendqisi2"
  [(set (match_operand:SI 0 "e2k_register_operand" "=r,r")
	(zero_extend:SI (match_operand:QI 1 "nonimmediate_operand" "r,m")))]
  ""
  "@
   sxt\t4, %1, %0%?
   ldb\t%1, %0%?"
  [(set_attr "type" "alu,load")
   (set_attr "predicable" "yes,yes")])

(define_insn "zero_extendqihi2"
  [(set (match_operand:HI 0 "e2k_register_operand" "=r,r")
	(zero_extend:HI (match_operand:QI 1 "nonimmediate_operand" "r,m")))]
  ""
  "@
   sxt\t4, %1, %0%?
   ldb\t%1, %0%?"
  [(set_attr "type" "alu,load")
   (set_attr "predicable" "yes,yes")])

;; ---------------------------------------------------------------------
;; Integer arithmetic
;; ---------------------------------------------------------------------

(define_insn "add<mode>3"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(plus:I48 (match_operand:I48 1 "e2k_register_operand" "%r")
		  (match_operand:I48 2 "e2k_src2_operand" "ri")))]
  ""
  "add<sd>\t%1, %2, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "sub<mode>3"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(minus:I48 (match_operand:I48 1 "e2k_src1_operand" "rI")
		   (match_operand:I48 2 "e2k_src2_operand" "ri")))]
  ""
  "sub<sd>\t%1, %2, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "neg<mode>2"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(neg:I48 (match_operand:I48 1 "e2k_register_operand" "r")))]
  ""
  "sub<sd>\t0x0, %1, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "mul<mode>3"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(mult:I48 (match_operand:I48 1 "e2k_register_operand" "%r")
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
  [(parallel [(set (match_operand:I48 0 "e2k_register_operand")
		   (DIVOP:I48 (match_operand:I48 1 "e2k_register_operand")
			      (match_operand:I48 2 "e2k_register_operand")))
	      (clobber (reg:DI CTPR2_REGNUM))])]
  "")

(define_insn "*<code><mode>3"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(DIVOP:I48 (match_operand:I48 1 "e2k_register_operand" "r")
		   (match_operand:I48 2 "e2k_register_operand" "r")))
   (clobber (reg:DI CTPR2_REGNUM))]
  ""
  "<divop><sd>\t%1, %2, %0"
  [(set_attr "type" "div")])

(define_insn "umulsidi3"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(mult:DI (zero_extend:DI (match_operand:SI 1 "e2k_register_operand" "%r"))
		 (zero_extend:DI (match_operand:SI 2 "e2k_register_operand" "r"))))]
  ""
  "umulx\t%1, %2, %0"
  [(set_attr "type" "mul")])

(define_insn "mulsidi3"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(mult:DI (sign_extend:DI (match_operand:SI 1 "e2k_register_operand" "%r"))
		 (sign_extend:DI (match_operand:SI 2 "e2k_register_operand" "r"))))]
  ""
  "smulx\t%1, %2, %0"
  [(set_attr "type" "mul")])

(define_insn "umuldi3_highpart"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(truncate:DI
	  (lshiftrt:TI
	    (mult:TI (zero_extend:TI (match_operand:DI 1 "e2k_register_operand" "%r"))
		     (zero_extend:TI (match_operand:DI 2 "e2k_register_operand" "r")))
	    (const_int 64))))]
  ""
  "umulhd\t%1, %2, %0"
  [(set_attr "type" "mul")])

(define_insn "smuldi3_highpart"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(truncate:DI
	  (lshiftrt:TI
	    (mult:TI (sign_extend:TI (match_operand:DI 1 "e2k_register_operand" "%r"))
		     (sign_extend:TI (match_operand:DI 2 "e2k_register_operand" "r")))
	    (const_int 64))))]
  ""
  "smulhd\t%1, %2, %0"
  [(set_attr "type" "mul")])

(define_code_iterator LOGIC [and ior xor])
(define_code_attr logic [(and "and") (ior "or") (xor "xor")])
(define_code_attr logic_optab [(and "and") (ior "ior") (xor "xor")])

;; Field extract (spec/isa/semantics.md, "Field extract"): getfd x, desc
;; is x rotated right by POS with LEN bits kept, zero- or sign-extended
;; from the field's top; v1-v4 take the sign from the byte the
;; descriptor's BYTE names, set here to the field's top byte, which is
;; right on every version (as lcc builds it).  SImode fields lie in the
;; register's low half, so getfd serves them too.  One 16-bit literal.
(define_code_iterator ANY_EXTRACT [zero_extract sign_extract])

(define_insn "*<code><mode>"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(ANY_EXTRACT:I48 (match_operand:I48 1 "e2k_register_operand" "r")
			 (match_operand 2 "const_int_operand")
			 (match_operand 3 "const_int_operand")))]
  "e2k_getf_field_p (<MODE>mode, operands[2], operands[3])"
  { return e2k_output_getf (operands, <CODE> == SIGN_EXTRACT); })

(define_expand "extzv<mode>"
  [(set (match_operand:I48 0 "e2k_register_operand")
	(zero_extract:I48 (match_operand:I48 1 "e2k_register_operand")
			  (match_operand 2 "const_int_operand")
			  (match_operand 3 "const_int_operand")))]
  ""
{
  if (!e2k_getf_field_p (<MODE>mode, operands[2], operands[3]))
    FAIL;
})

(define_expand "extv<mode>"
  [(set (match_operand:I48 0 "e2k_register_operand")
	(sign_extract:I48 (match_operand:I48 1 "e2k_register_operand")
			  (match_operand 2 "const_int_operand")
			  (match_operand 3 "const_int_operand")))]
  ""
{
  if (!e2k_getf_field_p (<MODE>mode, operands[2], operands[3]))
    FAIL;
})

;; v5's add and subtract with carry (spec/isa/operations-v5.md, "Scalar
;; operations"; ALC1/4, 1 cycle to anything integer as addd): addcd a,
;; b, c is a + b + (c & 1), addcd_c its carry out (0 or 1); subcd a - b -
;; (c & 1), subcd_c its borrow out as 0 or -1, which the next subcd
;; takes by bit 0.  __int128 addition and subtraction (addti3, subti3)
;; in three operations and 2 cycles, where v3 takes five and 4.
(define_int_iterator CARRYOP [UNSPEC_ADDCD UNSPEC_ADDCDC UNSPEC_SUBCD
			      UNSPEC_SUBCDC])
(define_int_attr carryop [(UNSPEC_ADDCD "addcd") (UNSPEC_ADDCDC "addcd_c")
			  (UNSPEC_SUBCD "subcd") (UNSPEC_SUBCDC "subcd_c")])

(define_insn "e2k_<carryop>"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(unspec:DI [(match_operand:DI 1 "e2k_register_operand" "r")
		    (match_operand:DI 2 "e2k_register_operand" "r")
		    (match_operand:DI 3 "e2k_register_operand" "r")]
		   CARRYOP))]
  "e2k_arch >= 5"
  "<carryop>\t%1, %2, %3, %0"
  [(set_attr "type" "alu14")
   (set_attr "ales" "yes")])

(define_code_iterator ADDSUB [plus minus])
(define_code_attr addsub [(plus "add") (minus "sub")])

(define_expand "<addsub>ti3"
  [(set (match_operand:TI 0 "e2k_register_operand")
	(ADDSUB:TI (match_operand:TI 1 "e2k_register_operand")
		   (match_operand:TI 2 "e2k_register_operand")))]
  "e2k_arch >= 5"
{
  e2k_expand_addsub_ti (operands, <CODE> == PLUS);
  DONE;
})

;; v5: a field scaled by 2 to 128, (x >> k) & m or (x << k) & m for m
;; a run of ones whose low end is bit 1 to 7, in one getfz
;; (e2k_getfz_desc) instead of a shift and an AND: an index into an array
;; of 2- to 128-byte elements, lcc's Lua "base + GETARG_A (i)" (16-byte
;; TValues), a CRC table's "tab[(crc ^ c) & 0xff]".
(define_insn "*getfz<mode>_lshr"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(and:I48 (lshiftrt:I48 (match_operand:I48 1 "e2k_register_operand" "r")
			       (match_operand 2 "const_int_operand"))
		 (match_operand 3 "const_int_operand")))]
  "e2k_getfz_desc (<MODE>mode, true, operands[2], operands[3]) >= 0"
  { return e2k_output_getfz (operands, true); })

(define_insn "*getfz<mode>_ashl"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(and:I48 (ashift:I48 (match_operand:I48 1 "e2k_register_operand" "r")
			     (match_operand 2 "const_int_operand"))
		 (match_operand 3 "const_int_operand")))]
  "e2k_getfz_desc (<MODE>mode, false, operands[2], operands[3]) >= 0"
  { return e2k_output_getfz (operands, false); })

;; x & (2^n - 1) for n from 33 to 63, whose mask needs a 64-bit literal:
;; getfd x, n << 6 (a 16-bit one).
(define_insn "*anddi3_lowmask"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(and:DI (match_operand:DI 1 "e2k_register_operand" "r")
		(match_operand:DI 2 "const_int_operand")))]
  "e2k_lowmask_bits (operands[2]) > 32"
  { return e2k_output_lowmask (operands); })

;; Field insert: insf a, desc, c rotates a right by desc's offset and
;; puts c's low LEN bits in its low LEN bits (spec/isa/semantics.md,
;; "Other scalar operations"), so (a << K) | (c & (2^K - 1)) is one
;; operation with offset WIDTH - K, LEN K, as lcc refills its bit
;; buffers.  ALC0, 1, 3, 4.
(define_insn "*insf<mode>"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(ior:I48 (and:I48 (match_operand:I48 3 "e2k_register_operand" "r")
			  (match_operand 4 "const_int_operand"))
		 (ashift:I48 (match_operand:I48 1 "e2k_register_operand" "r")
			     (match_operand 2 "const_int_operand"))))]
  "e2k_insf_mask_p (<MODE>mode, operands[2], operands[4])"
  { return e2k_output_insf (operands, <MODE>mode); }
  [(set_attr "type" "alu0134")
   (set_attr "predicable" "yes")])

(define_mode_iterator INSFN [QI HI SI])
(define_insn "*insf<I48:mode>_<INSFN:mode>"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(ior:I48 (ashift:I48 (match_operand:I48 1 "e2k_register_operand" "r")
			     (match_operand 2 "const_int_operand"))
		 (zero_extend:I48
		   (match_operand:INSFN 3 "e2k_register_operand" "r"))))]
  "GET_MODE_BITSIZE (<INSFN:MODE>mode) < GET_MODE_BITSIZE (<I48:MODE>mode)
   && INTVAL (operands[2]) == GET_MODE_BITSIZE (<INSFN:MODE>mode)"
  { return e2k_output_insf (operands, <I48:MODE>mode); }
  [(set_attr "type" "alu0134")
   (set_attr "predicable" "yes")])

;; The same zero-extended: getfd extends a zero_extract field anyway,
;; and under dbl = 1 getfs and insfs zero-extend their 32-bit results
;; (e2k_dbl_zext folds extensions into these).
(define_insn "*zero_extractsi_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (zero_extract:SI (match_operand:SI 1 "e2k_register_operand" "r")
			   (match_operand 2 "const_int_operand")
			   (match_operand 3 "const_int_operand"))))]
  "e2k_getf_field_p (SImode, operands[2], operands[3])"
  { return e2k_output_getf (operands, false); })

(define_insn "*sign_extractsi_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (sign_extract:SI (match_operand:SI 1 "e2k_register_operand" "r")
			   (match_operand 2 "const_int_operand")
			   (match_operand 3 "const_int_operand"))))]
  "e2k_dbl_p () && e2k_getf_field_p (SImode, operands[2], operands[3])"
  { return e2k_output_getfs (operands); })

(define_insn "*insfsi_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (ior:SI (and:SI (match_operand:SI 3 "e2k_register_operand" "r")
			  (match_operand 4 "const_int_operand"))
		  (ashift:SI (match_operand:SI 1 "e2k_register_operand" "r")
			     (match_operand 2 "const_int_operand")))))]
  "e2k_dbl_p () && e2k_insf_mask_p (SImode, operands[2], operands[4])"
  { return e2k_output_insf (operands, SImode); }
  [(set_attr "type" "alu0134")
   (set_attr "predicable" "yes")])

(define_mode_iterator INSFN2 [QI HI])
(define_insn "*insfsi_<INSFN2:mode>_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (ior:SI (ashift:SI (match_operand:SI 1 "e2k_register_operand" "r")
			     (match_operand 2 "const_int_operand"))
		  (zero_extend:SI
		    (match_operand:INSFN2 3 "e2k_register_operand" "r")))))]
  "e2k_dbl_p ()
   && INTVAL (operands[2]) == GET_MODE_BITSIZE (<INSFN2:MODE>mode)"
  { return e2k_output_insf (operands, SImode); }
  [(set_attr "type" "alu0134")
   (set_attr "predicable" "yes")])

;; The byte (halfword) a refill loads: the load first, into a scratch
;; (combine adds the clobber; a late pass may form this after split1, so
;; it splits after reload too).
(define_insn_and_split "*insf<I48:mode>_<INSFN:mode>_mem"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(ior:I48 (ashift:I48 (match_operand:I48 1 "e2k_register_operand" "r")
			     (match_operand 2 "const_int_operand"))
		 (zero_extend:I48
		   (match_operand:INSFN 3 "memory_operand" "m"))))
   (clobber (match_scratch:INSFN 4 "=&r"))]
  "GET_MODE_BITSIZE (<INSFN:MODE>mode) < GET_MODE_BITSIZE (<I48:MODE>mode)
   && INTVAL (operands[2]) == GET_MODE_BITSIZE (<INSFN:MODE>mode)"
  "#"
  "&& (can_create_pseudo_p () || REG_P (operands[4]))"
  [(set (match_dup 4) (match_dup 3))
   (set (match_dup 0)
	(ior:I48 (ashift:I48 (match_dup 1) (match_dup 2))
		 (zero_extend:I48 (match_dup 4))))]
{
  if (!REG_P (operands[4]))
    operands[4] = gen_reg_rtx (<INSFN:MODE>mode);
}
  [(set_attr "type" "multi")])

(define_insn "<logic_optab><mode>3"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(LOGIC:I48 (match_operand:I48 1 "e2k_register_operand" "%r")
		   (match_operand:I48 2 "e2k_src2_operand" "ri")))]
  ""
  "<logic><sd>\t%1, %2, %0%?"
  [(set_attr "predicable" "yes")])

;; With setwd dbl = 1 a 32-bit operation zero-extends its result
;; (spec/abi/registers.md, "dbl"): one operation for an unsigned 32-bit
;; result used as 64 bits.  lcc sets dbl = 1 at -O2 in functions that
;; need that, e2k_dbl_p decides the same way.
(define_code_iterator ZEXTOP [plus minus and ior xor ashift lshiftrt ashiftrt
			      mult])
(define_code_attr zextop [(plus "add") (minus "sub") (and "and") (ior "or")
			  (xor "xor") (ashift "shl") (lshiftrt "shr")
			  (ashiftrt "sar") (mult "mul")])
(define_code_attr zexttype [(plus "alu") (minus "alu") (and "alu") (ior "alu")
			    (xor "alu") (ashift "alu") (lshiftrt "alu")
			    (ashiftrt "alu") (mult "mul")])

(define_insn "*<code>si3_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (ZEXTOP:SI (match_operand:SI 1 "e2k_register_operand" "r")
		     (match_operand:SI 2 "e2k_src2_operand" "ri"))))]
  "e2k_dbl_p ()"
  "<zextop>s\t%1, %2, %0%?"
  [(set_attr "type" "<zexttype>")
   (set_attr "predicable" "yes")])

;; dbl = 1 zero-extends every 32-bit integer ALU result (probed on the 4C
;; and the 8C2: merges, rotates, divisions, lzcnts, popcnts too; FP to
;; integer conversions and movts not).  With REE (-free, on at -O2) these
;; also drop the sxt after a value that is used both ways.
(define_code_iterator ZEXTROT [rotate rotatert])
(define_code_attr zextrot [(rotate "scl") (rotatert "scr")])

(define_insn "*<code>si3_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (ZEXTROT:SI (match_operand:SI 1 "e2k_register_operand" "r")
		      (match_operand:SI 2 "e2k_src2_operand" "ri"))))]
  "e2k_dbl_p ()"
  "<zextrot>s\t%1, %2, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "*<code>si3_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (DIVOP:SI (match_operand:SI 1 "e2k_register_operand" "r")
		    (match_operand:SI 2 "e2k_register_operand" "r"))))
   (clobber (reg:DI CTPR2_REGNUM))]
  "e2k_dbl_p ()"
  "<divop>s\t%1, %2, %0"
  [(set_attr "type" "div")])

(define_insn "*negsi2_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (neg:SI (match_operand:SI 1 "e2k_register_operand" "r"))))]
  "e2k_dbl_p ()"
  "subs\t0x0, %1, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "*one_cmplsi2_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (not:SI (match_operand:SI 1 "e2k_register_operand" "r"))))]
  "e2k_dbl_p ()"
  "xorns\t%1, 0x0, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "*andnsi3_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (and:SI (not:SI (match_operand:SI 1 "e2k_src2_operand" "ri"))
		  (match_operand:SI 2 "e2k_register_operand" "r"))))]
  "e2k_dbl_p ()"
  "andns\t%2, %1, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "*ornsi3_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (ior:SI (not:SI (match_operand:SI 1 "e2k_src2_operand" "ri"))
		  (match_operand:SI 2 "e2k_register_operand" "r"))))]
  "e2k_dbl_p ()"
  "orns\t%2, %1, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "*xornsi3_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (not:SI (xor:SI (match_operand:SI 1 "e2k_register_operand" "%r")
			  (match_operand:SI 2 "e2k_src2_operand" "ri")))))]
  "e2k_dbl_p ()"
  "xorns\t%1, %2, %0%?"
  [(set_attr "predicable" "yes")])

(define_code_iterator ZEXTCNT [clz popcount])
(define_code_attr zextcnt [(clz "lzcnt") (popcount "popcnt")])

(define_insn "*<code>si2_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (ZEXTCNT:SI (match_operand:SI 1 "e2k_register_operand" "r"))))]
  "e2k_dbl_p ()"
  "<zextcnt>s\t%1, %0"
  [(set_attr "type" "alu14")])

(define_insn "*mergesi_zext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(zero_extend:DI
	  (if_then_else:SI
	    (match_operator 1 "e2k_pred_test_operator"
	      [(match_operand:BI 2 "e2k_register_operand" "j")
	       (const_int 0)])
	    (match_operand:SI 3 "e2k_src2_operand" "ri")
	    (match_operand:SI 4 "e2k_src1_operand" "rI"))))]
  "e2k_dbl_p ()"
  "merges\t%4, %3, %0, %C1%2")

;; andn, orn: the second operand is inverted (guide 10.3.5).
(define_insn "*andn<mode>3"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(and:I48 (not:I48 (match_operand:I48 1 "e2k_src2_operand" "ri"))
		 (match_operand:I48 2 "e2k_register_operand" "r")))]
  ""
  "andn<sd>\t%2, %1, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "*orn<mode>3"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(ior:I48 (not:I48 (match_operand:I48 1 "e2k_src2_operand" "ri"))
		 (match_operand:I48 2 "e2k_register_operand" "r")))]
  ""
  "orn<sd>\t%2, %1, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "*xorn<mode>3"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(not:I48 (xor:I48 (match_operand:I48 1 "e2k_register_operand" "%r")
			  (match_operand:I48 2 "e2k_src2_operand" "ri"))))]
  ""
  "xorn<sd>\t%1, %2, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "one_cmpl<mode>2"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(not:I48 (match_operand:I48 1 "e2k_register_operand" "r")))]
  ""
  "xorn<sd>\t%1, 0x0, %0%?"
  [(set_attr "predicable" "yes")])

(define_code_iterator SHIFT [ashift lshiftrt ashiftrt rotate rotatert])
(define_code_attr shift [(ashift "shl") (lshiftrt "shr") (ashiftrt "sar")
			 (rotate "scl") (rotatert "scr")])
(define_code_attr shift_optab [(ashift "ashl") (lshiftrt "lshr")
			       (ashiftrt "ashr") (rotate "rotl")
			       (rotatert "rotr")])

;; The count is taken modulo the width (SHIFT_COUNT_TRUNCATED).
(define_insn "<shift_optab><mode>3"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(SHIFT:I48 (match_operand:I48 1 "e2k_register_operand" "r")
		   (match_operand:I48 2 "e2k_src2_operand" "ri")))]
  ""
  "<shift><sd>\t%1, %2, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "clz<mode>2"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(clz:I48 (match_operand:I48 1 "e2k_register_operand" "r")))]
  ""
  "lzcnt<sd>\t%1, %0"
  [(set_attr "type" "alu14")])

(define_insn "bitreverse<mode>2"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(bitreverse:I48 (match_operand:I48 1 "e2k_register_operand" "r")))]
  ""
  "bitrev<sd>\t%1, %0"
  [(set_attr "type" "alu0134")])

;; Trailing zeros: the leading zeros of the bits reversed, as lcc counts
;; them (spec/isa/operations-v3.md); the width for 0.
(define_expand "ctz<mode>2"
  [(set (match_dup 2)
	(bitreverse:I48 (match_operand:I48 1 "e2k_register_operand")))
   (set (match_operand:I48 0 "e2k_register_operand")
	(clz:I48 (match_dup 2)))]
  ""
{
  operands[2] = gen_reg_rtx (<MODE>mode);
})

;; Byte swaps: a load or store with MAS bit 3 swaps the bytes of an
;; aligned access at no cost (a misaligned one is SIGBUS;
;; spec/isa/semantics.md, "Byte-swapped accesses"), used where the
;; alignment is known and not only the type's (e2k_bswap_mem_p);
;; elsewhere pshufb with a mask, as lcc does.
(define_mode_attr bswsz [(SI "w") (DI "d")])

(define_insn "*bswap<mode>_load"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(bswap:I48 (match_operand:I48 1 "memory_operand" "m")))
   (clobber (match_scratch:DI 2 "=X"))]
  "e2k_bswap_mem_p (operands[1])"
  "ld<bswsz>\t%1, %0, mas=0x8"
  [(set_attr "type" "load")
   (set_attr "mas" "yes")])

(define_insn "*bswap<mode>_store"
  [(set (match_operand:I48 0 "memory_operand" "=m")
	(bswap:I48 (match_operand:I48 1 "e2k_register_operand" "r")))
   (clobber (match_scratch:DI 2 "=X"))]
  "e2k_bswap_mem_p (operands[0])"
  "st<bswsz>\t%0, %1, mas=0x8"
  [(set_attr "type" "store")
   (set_attr "mas" "yes")])

;; In registers until after reload, so that combine can fold it into an
;; aligned load or store first.
(define_insn_and_split "bswap<mode>2"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(bswap:I48 (match_operand:I48 1 "e2k_register_operand" "r")))
   (clobber (match_scratch:DI 2 "=&r"))]
  ""
  "#"
  "&& reload_completed"
  [(const_int 0)]
{
  e2k_split_bswap (operands[0], operands[1], operands[2]);
  DONE;
}
  [(set_attr "type" "multi")])

(define_insn "popcount<mode>2"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(popcount:I48 (match_operand:I48 1 "e2k_register_operand" "r")))]
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
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(FARITH:F (match_operand:F 1 "e2k_register_operand" "r")
		  (match_operand:F 2 "e2k_register_operand" "r")))]
  ""
  "<farith><sd>\t%1, %2, %0"
  [(set_attr "type" "fp")])


;; x86-style maximum and minimum: fmaxd a, b is a > b ? a : b and fmind
;; a, b is a < b ? a : b, b when either is a NaN or both are zeros
;; (spec/isa/semantics.md, "FP min, max and combined operations"), so
;; they are those conditional moves exactly, not smax/smin.  2 cycles
;; (e2k_adjust_cost) in ALC0, 1, 3 and 4, the channels of a conversion.
(define_int_iterator FMINMAX [UNSPEC_FMAX UNSPEC_FMIN])
(define_int_attr fminmax [(UNSPEC_FMAX "fmax") (UNSPEC_FMIN "fmin")])

(define_insn "e2k_<fminmax><mode>"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(unspec:F [(match_operand:F 1 "e2k_register_operand" "r")
		   (match_operand:F 2 "e2k_register_operand" "r")] FMINMAX))]
  ""
  "<fminmax><sd>\t%1, %2, %0"
  [(set_attr "type" "fcvt")])

;; Round to an integral value: fdtoifd a, b and fstoifs a, b round b with
;; a as x86 roundsd's immediate (spec/isa/semantics.md): bits 0-1 the
;; mode (0 to nearest even, 1 down, 2 up, 3 toward zero), bit 2 %pfpfr's
;; mode instead, bit 3 no inexact.  floor, ceil, trunc and roundeven
;; raise no inexact, as glibc's and C23's don't (lcc's 0x1-0x3 do), rint
;; does (0x4), nearbyint doesn't (0xc); as i386 with SSE4.1.  4 cycles in
;; ALC0, 1, 3 and 4.  round's halves away from zero are no mode.
(define_int_iterator FRINT [UNSPEC_FRINT_FLOOR UNSPEC_FRINT_CEIL
			    UNSPEC_FRINT_TRUNC UNSPEC_FRINT_EVEN
			    UNSPEC_FRINT_RINT UNSPEC_FRINT_NEARBY])
(define_int_attr frint [(UNSPEC_FRINT_FLOOR "floor") (UNSPEC_FRINT_CEIL "ceil")
			(UNSPEC_FRINT_TRUNC "btrunc")
			(UNSPEC_FRINT_EVEN "roundeven")
			(UNSPEC_FRINT_RINT "rint")
			(UNSPEC_FRINT_NEARBY "nearbyint")])
(define_int_attr frint_imm [(UNSPEC_FRINT_FLOOR "0x9") (UNSPEC_FRINT_CEIL "0xa")
			    (UNSPEC_FRINT_TRUNC "0xb") (UNSPEC_FRINT_EVEN "0x8")
			    (UNSPEC_FRINT_RINT "0x4")
			    (UNSPEC_FRINT_NEARBY "0xc")])

(define_insn "<frint><mode>2"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(unspec:F [(match_operand:F 1 "e2k_register_operand" "r")] FRINT))]
  ""
  "f<sd>toif<sd>\t<frint_imm>, %1, %0"
  [(set_attr "type" "fcvt")])

;; ldexp and scalbn (v4+): fscaled a, b is a * 2^b, b a signed 32-bit
;; integer, rounded once with IEEE flags (spec/isa/semantics.md); ALC1
;; and ALC4, 4 cycles.  GCC uses it only where the call needn't set errno
;; (-fno-math-errno), as lcc uses fscales only under -ffast; ldexp stays
;; a call otherwise, in both.
(define_insn "ldexp<mode>3"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(unspec:F [(match_operand:F 1 "e2k_register_operand" "r")
		   (match_operand:SI 2 "e2k_register_operand" "r")]
		  UNSPEC_FSCALE))]
  "e2k_arch >= 4"
  "fscale<sd>\t%1, %2, %0"
  [(set_attr "type" "fscale")])

;; ---------------------------------------------------------------------
;; Overflow checks (__builtin_*_overflow, -ftrapv) with the x86 flag
;; operations (spec/isa/semantics.md, "x86 flag operations"; spec/isa/
;; x86-support.md): adds_fw a, b (addd_fd, v3+, for 64 bits) gives the
;; EFLAGS of a + b in a register, smulx_fw/umulx_fw those of the 32 x 32
;; product (OF set with CF), and cctopo f OF (0x800) as a predicate;
;; cmpo<s,d>b a, b is the overflow of a - b itself.  The RTL tests OF as
;; the bit test it is, (f & 0x800) != 0, so that if-conversion turns the
;; flag of a value (sqlite3AddInt64's) into a store-flag, and the test
;; splits into cctopo (e2k_emit_cmp).  The flag operations and cctop run
;; only in ALC0 and ALC3; a flag result reaches a cctop in its channel
;; in 2 cycles, anything else in 4 (the multiplies' in 6); cctop reaches
;; a predicated operation in 2 (1 on v6) and a ct in 3, as a compare.
;; lcc's __builtin_add_overflow on int is ten operations (an add, three
;; compares, four predicated moves, two extensions).
;; Neither qemu runs the flag operations or cctop: -mno-flag-ops leaves
;; addv and mulv to GCC's generic code for qemu runs.  Nothing here
;; touches %upsr.
;; ---------------------------------------------------------------------

(define_mode_attr flagop [(SI "s_fw") (DI "d_fd")])
(define_int_iterator MULXF [UNSPEC_SMULX_FLAGS UNSPEC_UMULX_FLAGS])
(define_int_attr mulxf [(UNSPEC_SMULX_FLAGS "smulx") (UNSPEC_UMULX_FLAGS "umulx")])

(define_insn "e2k_add<mode>_flags"
  [(set (match_operand:SI 0 "e2k_register_operand" "=r")
	(unspec:SI [(match_operand:I48 1 "e2k_register_operand" "r")
		    (match_operand:I48 2 "e2k_src2_operand" "ri")]
		   UNSPEC_ADD_FLAGS))]
  "e2k_flag_ops"
  "add<flagop>\t%1, %2, %0"
  [(set_attr "type" "flag")])

(define_insn "e2k_<mulxf>_flags"
  [(set (match_operand:SI 0 "e2k_register_operand" "=r")
	(unspec:SI [(match_operand:SI 1 "e2k_register_operand" "r")
		    (match_operand:SI 2 "e2k_src2_operand" "ri")]
		   MULXF))]
  "e2k_flag_ops"
  "<mulxf>_fw\t%1, %2, %0"
  [(set_attr "type" "flagmul")])

(define_insn "e2k_cctopo"
  [(set (match_operand:BI 0 "e2k_register_operand" "=j")
	(unspec:BI [(match_operand:SI 1 "e2k_register_operand" "r")]
		   UNSPEC_CCTOPO))]
  "e2k_flag_ops"
  "cctopo\t%1, %0"
  [(set_attr "type" "cctop")])

(define_insn "e2k_cmpo<mode>"
  [(set (match_operand:BI 0 "e2k_register_operand" "=j")
	(unspec:BI [(match_operand:I48 1 "e2k_src1_operand" "rI")
		    (match_operand:I48 2 "e2k_src2_operand" "ri")]
		   UNSPEC_CMPO))]
  ""
  "cmpo<sd>b\t%1, %2, %0"
  [(set_attr "type" "cmp")])

;; Before register allocation the test and its branch are one insn with
;; a predicate scratch, as the compares' (below).
(define_insn_and_split "e2k_cmpo<mode>_branch"
  [(set (pc)
	(if_then_else
	  (ne (unspec:BI [(match_operand:I48 0 "e2k_src1_operand" "rI")
			  (match_operand:I48 1 "e2k_src2_operand" "ri")]
			 UNSPEC_CMPO)
	      (const_int 0))
	  (label_ref (match_operand 2))
	  (pc)))
   (clobber (match_scratch:BI 3 "=j"))]
  ""
  "#"
  "reload_completed"
  [(set (match_dup 3) (unspec:BI [(match_dup 0) (match_dup 1)] UNSPEC_CMPO))
   (set (pc) (if_then_else (ne (match_dup 3) (const_int 0))
			   (label_ref (match_dup 2))
			   (pc)))]
  ""
  [(set_attr "type" "multi")])

;; The flags before the add, which may overwrite an operand; the add, so
;; the result is there on both ways; then the branch.  Two operations
;; and the branch.  With a constant operand GCC's own test is one
;; compare: leave it that.
(define_expand "addv<mode>4"
  [(match_operand:I48 0 "e2k_register_operand")
   (match_operand:I48 1 "e2k_register_operand")
   (match_operand:I48 2 "e2k_src2_operand")
   (match_operand 3 "")]
  "e2k_flag_ops"
{
  if (CONST_INT_P (operands[2]))
    FAIL;
  rtx f = gen_reg_rtx (SImode);
  emit_insn (gen_e2k_add<mode>_flags (f, operands[1], operands[2]));
  emit_insn (gen_add<mode>3 (operands[0], operands[1], operands[2]));
  e2k_emit_of_branch (f, operands[3]);
  DONE;
})

;; cmpo<s,d>b reads the operands at the branch, after the subtract: copy
;; one the result overwrites.
(define_expand "subv<mode>4"
  [(match_operand:I48 0 "e2k_register_operand")
   (match_operand:I48 1 "e2k_register_operand")
   (match_operand:I48 2 "e2k_src2_operand")
   (match_operand 3 "")]
  ""
{
  rtx a = operands[1], b = operands[2];
  if (reg_overlap_mentioned_p (operands[0], a))
    a = copy_to_mode_reg (<MODE>mode, a);
  if (reg_overlap_mentioned_p (operands[0], b))
    b = copy_to_mode_reg (<MODE>mode, b);
  emit_insn (gen_sub<mode>3 (operands[0], a, b));
  emit_jump_insn (gen_e2k_cmpo<mode>_branch (a, b, operands[3]));
  DONE;
})

;; 32 x 32: smulx_fw sets OF (and CF) when the product doesn't fit 32
;; bits signed, umulx_fw when it doesn't fit unsigned; a constant
;; operand as addv.  64 x 64 is GCC's: smulhd/umulhd and a compare.
(define_expand "mulvsi4"
  [(match_operand:SI 0 "e2k_register_operand")
   (match_operand:SI 1 "e2k_register_operand")
   (match_operand:SI 2 "e2k_src2_operand")
   (match_operand 3 "")]
  "e2k_flag_ops"
{
  if (CONST_INT_P (operands[2]))
    FAIL;
  rtx f = gen_reg_rtx (SImode);
  emit_insn (gen_e2k_smulx_flags (f, operands[1], operands[2]));
  emit_insn (gen_mulsi3 (operands[0], operands[1], operands[2]));
  e2k_emit_of_branch (f, operands[3]);
  DONE;
})

(define_expand "umulvsi4"
  [(match_operand:SI 0 "e2k_register_operand")
   (match_operand:SI 1 "e2k_register_operand")
   (match_operand:SI 2 "e2k_src2_operand")
   (match_operand 3 "")]
  "e2k_flag_ops"
{
  if (CONST_INT_P (operands[2]))
    FAIL;
  rtx f = gen_reg_rtx (SImode);
  emit_insn (gen_e2k_umulx_flags (f, operands[1], operands[2]));
  emit_insn (gen_mulsi3 (operands[0], operands[1], operands[2]));
  e2k_emit_of_branch (f, operands[3]);
  DONE;
})

;; Combined operations: the multiply rounds before the add or subtract
;; (two roundings, spec/isa/semantics.md), so they compute what the two
;; operations would, in one channel: exactly the RTL's (plus (mult)), not
;; a contraction (lcc uses them at -O3).  With gas's operands A, B, C,
;; fmul_sub gives C - A * B and fmul_rsub A * B - C (probed on the 8C2).
;; Off by default (-mfmul-add): pipelined daxpy loops ran no faster with
;; them on the 8C2, and Linpack as a whole about 10% slower there, 2.3%
;; on the 2C3 (the addend is read at issue, 9 cycles after a v6 load,
;; and the longer pipelines cost Linpack's short calls more).
(define_insn "*fmul_add<mode>4"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(plus:F (mult:F (match_operand:F 1 "e2k_register_operand" "r")
			(match_operand:F 2 "e2k_register_operand" "r"))
		(match_operand:F 3 "e2k_register_operand" "r")))]
  "e2k_fma_combined_p ()"
  "fmul_add<sd>\t%1, %2, %3, %0"
  [(set_attr "type" "fma")])

(define_insn "*mulsub<mode>4"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(minus:F (mult:F (match_operand:F 1 "e2k_register_operand" "r")
			 (match_operand:F 2 "e2k_register_operand" "r"))
		 (match_operand:F 3 "e2k_register_operand" "r")))]
  "e2k_fma_combined_p ()"
  "fmul_rsub<sd>\t%1, %2, %3, %0"
  [(set_attr "type" "fma")])

(define_insn "*submul<mode>4"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(minus:F (match_operand:F 3 "e2k_register_operand" "r")
		 (mult:F (match_operand:F 1 "e2k_register_operand" "r")
			 (match_operand:F 2 "e2k_register_operand" "r"))))]
  "e2k_fma_combined_p ()"
  "fmul_sub<sd>\t%1, %2, %3, %0"
  [(set_attr "type" "fma")])

;; Fused multiply-add (v6): rounded once, as C fma (spec/isa/semantics.md,
;; "v6 operations").  With gas's operands A, B, C: fma A * B + C, fms
;; A * B - C, fnma -(A * B) + C, fnms -(A * B) - C.
(define_insn "fma<mode>4"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(fma:F (match_operand:F 1 "e2k_register_operand" "r")
	       (match_operand:F 2 "e2k_register_operand" "r")
	       (match_operand:F 3 "e2k_register_operand" "r")))]
  "e2k_arch >= 6"
  "fma<sd>\t%1, %2, %3, %0"
  [(set_attr "type" "ffma")])

(define_insn "fms<mode>4"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(fma:F (match_operand:F 1 "e2k_register_operand" "r")
	       (match_operand:F 2 "e2k_register_operand" "r")
	       (neg:F (match_operand:F 3 "e2k_register_operand" "r"))))]
  "e2k_arch >= 6"
  "fms<sd>\t%1, %2, %3, %0"
  [(set_attr "type" "ffma")])

(define_insn "fnma<mode>4"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(fma:F (neg:F (match_operand:F 1 "e2k_register_operand" "r"))
	       (match_operand:F 2 "e2k_register_operand" "r")
	       (match_operand:F 3 "e2k_register_operand" "r")))]
  "e2k_arch >= 6"
  "fnma<sd>\t%1, %2, %3, %0"
  [(set_attr "type" "ffma")])

(define_insn "fnms<mode>4"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(fma:F (neg:F (match_operand:F 1 "e2k_register_operand" "r"))
	       (match_operand:F 2 "e2k_register_operand" "r")
	       (neg:F (match_operand:F 3 "e2k_register_operand" "r"))))]
  "e2k_arch >= 6"
  "fnms<sd>\t%1, %2, %3, %0"
  [(set_attr "type" "ffma")])

(define_insn "div<mode>3"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(div:F (match_operand:F 1 "e2k_register_operand" "r")
	       (match_operand:F 2 "e2k_register_operand" "r")))]
  ""
  "fdiv<sd>\t%1, %2, %0"
  [(set_attr "type" "fdiv")])

(define_insn "sqrtsf2"
  [(set (match_operand:SF 0 "e2k_register_operand" "=r")
	(sqrt:SF (match_operand:SF 1 "e2k_register_operand" "r")))]
  ""
  "fsqrts\t%1, %0"
  [(set_attr "type" "fdiv")])

;; fsqrtid gives a first approximation, fsqrttd the IEEE result (guide
;; 10.4.2), from the operand and the approximation: an unspec with both,
;; a plain SET the modulo scheduler takes.
(define_expand "sqrtdf2"
  [(set (match_operand:DF 0 "e2k_register_operand")
	(sqrt:DF (match_operand:DF 1 "e2k_register_operand")))]
  ""
{
  rtx t = gen_reg_rtx (DFmode);
  emit_insn (gen_e2k_fsqrtid (t, operands[1]));
  emit_insn (gen_e2k_fsqrttd (operands[0], operands[1], t));
  DONE;
})

(define_insn "e2k_fsqrtid"
  [(set (match_operand:DF 0 "e2k_register_operand" "=r")
	(unspec:DF [(match_operand:DF 1 "e2k_register_operand" "r")] UNSPEC_FSQRTI))]
  ""
  "fsqrtid\t%1, %0%?"
  [(set_attr "type" "fdiv")
   (set_attr "predicable" "yes")])

(define_insn "e2k_fsqrttd"
  [(set (match_operand:DF 0 "e2k_register_operand" "=r")
	(unspec:DF [(match_operand:DF 1 "e2k_register_operand" "r")
		    (match_operand:DF 2 "e2k_register_operand" "r")]
		   UNSPEC_FSQRTT))]
  ""
  "fsqrttd\t%1, %2, %0%?"
  [(set_attr "type" "fdiv")
   (set_attr "predicable" "yes")])

(define_insn "neg<mode>2"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(neg:F (match_operand:F 1 "e2k_register_operand" "r")))]
  ""
  "xor<sd>\t%1, <SIGNBIT>, %0")

(define_insn "abs<mode>2"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(abs:F (match_operand:F 1 "e2k_register_operand" "r")))]
  ""
  "andn<sd>\t%1, <SIGNBIT>, %0")

(define_insn "extendsfdf2"
  [(set (match_operand:DF 0 "e2k_register_operand" "=r")
	(float_extend:DF (match_operand:SF 1 "e2k_register_operand" "r")))]
  ""
  "fstofd\t%1, %0"
  [(set_attr "type" "fcvt")])

(define_insn "truncdfsf2"
  [(set (match_operand:SF 0 "e2k_register_operand" "=r")
	(float_truncate:SF (match_operand:DF 1 "e2k_register_operand" "r")))]
  ""
  "fdtofs\t%1, %0"
  [(set_attr "type" "fcvt")])

(define_mode_attr ifl [(SI "s") (DI "d")])

(define_insn "float<I48:mode><F:mode>2"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(float:F (match_operand:I48 1 "e2k_register_operand" "r")))]
  ""
  "i<I48:sd>tof<F:sd>\t%1, %0"
  [(set_attr "type" "fcvt")])

;; Unsigned 64 bits to FP in the FP registers' own formats (without this
;; GCC goes through the x87 long double): x itself when its top bit is
;; clear, else (x >> 1 | x & 1) converted and doubled, which rounds the
;; same.
(define_expand "floatunsdi<F:mode>2"
  [(match_operand:F 0 "e2k_register_operand")
   (match_operand:DI 1 "e2k_register_operand")]
  ""
{
  e2k_expand_floatunsdi (operands[0], operands[1]);
  DONE;
})

(define_insn "fix_trunc<F:mode><I48:mode>2"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(fix:I48 (match_operand:F 1 "e2k_register_operand" "r")))]
  ""
  "f<F:sd>toi<I48:sd>tr\t%1, %0"
  [(set_attr "type" "fcvt")])

;; (long) (int) x in one conversion: where the two differ, x is outside
;; int and the C conversion undefined (NPB EP's "qq[l]", l = max (fabs
;; (t3), fabs (t4)): fdtoistr and sxt 2, a cycle more on its chain).
(define_insn "*fix_trunc<F:mode>si_sext"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(sign_extend:DI
	  (fix:SI (match_operand:F 1 "e2k_register_operand" "r"))))]
  ""
  "f<F:sd>toidtr\t%1, %0"
  [(set_attr "type" "fcvt")])

;; ---------------------------------------------------------------------
;; long double (XFmode) in a register pair: mantissa, then the 16-bit
;; sign and exponent, kept zero-extended to 64 bits (movfi writes only the
;; low half, so its result is extended with sxt 5, as lcc returns it) so
;; that no 64-bit copy ever reads a stale, possibly tagged, upper half.  Each operation assembles the extended register with
;; movif, operates and splits the result with movfi, so no extended
;; value ever lives across a call or a spill.
;; ---------------------------------------------------------------------

(define_code_iterator XARITH [plus minus mult div])
(define_code_attr xarith [(plus "fxaddxx") (minus "fxsubxx")
			  (mult "fxmulxx") (div "fxdivxx")])
(define_code_attr xarith_optab [(plus "add") (minus "sub")
				(mult "mul") (div "div")])

(define_insn "<xarith_optab>xf3"
  [(set (match_operand:XF 0 "e2k_register_operand" "=&r")
	(XARITH:XF (match_operand:XF 1 "e2k_register_operand" "r")
		   (match_operand:XF 2 "e2k_register_operand" "r")))
   (clobber (match_scratch:DI 3 "=&r"))
   (clobber (match_scratch:DI 4 "=&r"))]
  ""
  "movif\t%1, %H1, %3\n\tmovif\t%2, %H2, %4%#<xarith>\t%3, %4, %3%#movfi\t%3, %H0\n\taddd\t%3, 0x0, %0%#sxt\t5, %H0, %H0"
  [(set_attr "type" "multi")])

(define_insn "negxf2"
  [(set (match_operand:XF 0 "e2k_register_operand" "=&r")
	(neg:XF (match_operand:XF 1 "e2k_register_operand" "r")))]
  ""
  "addd\t%1, 0x0, %0\n\txord\t%H1, 0x8000, %H0"
  [(set_attr "type" "multi")])

(define_insn "absxf2"
  [(set (match_operand:XF 0 "e2k_register_operand" "=&r")
	(abs:XF (match_operand:XF 1 "e2k_register_operand" "r")))]
  ""
  "addd\t%1, 0x0, %0\n\tandnd\t%H1, 0x8000, %H0"
  [(set_attr "type" "multi")])

;; An "x" asm operand: the long double in one extended register.  The
;; DImode register then carries an 80-bit value that a 64-bit copy would
;; truncate, so the pack is volatile (never shared or moved away from its
;; asm), and the unpack first normalizes the asm's result with movx, as
;; lcc does after every "x" output.
(define_insn "e2k_xf_pack"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(unspec_volatile:DI [(match_operand:XF 1 "e2k_register_operand" "r")]
			    UNSPECV_XPACK))]
  ""
  "movif\t%1, %H1, %0"
  [(set_attr "type" "fcvt")])

;; No earlyclobber: the output may overlap the input (movx reads it
;; first), so the allocator needn't copy the 80-bit value with addd.
(define_insn "e2k_xf_unpack"
  [(set (match_operand:XF 0 "e2k_register_operand" "=r")
	(unspec:XF [(match_operand:DI 1 "e2k_register_operand" "r")]
		   UNSPEC_XUNPACK))]
  ""
  "movx\t%1, %0%#movfi\t%0, %H0%#sxt\t5, %H0, %H0"
  [(set_attr "type" "multi")])

(define_insn "extend<mode>xf2"
  [(set (match_operand:XF 0 "e2k_register_operand" "=&r")
	(float_extend:XF (match_operand:F 1 "e2k_register_operand" "r")))
   (clobber (match_scratch:DI 2 "=&r"))]
  ""
  "f<sd>tofx\t%1, %2%#movfi\t%2, %H0\n\taddd\t%2, 0x0, %0%#sxt\t5, %H0, %H0"
  [(set_attr "type" "multi")])

(define_insn "truncxf<mode>2"
  [(set (match_operand:F 0 "e2k_register_operand" "=r")
	(float_truncate:F (match_operand:XF 1 "e2k_register_operand" "r")))
   (clobber (match_scratch:DI 2 "=&r"))]
  ""
  "movif\t%1, %H1, %2%#fxtof<sd>\t%2, %0"
  [(set_attr "type" "multi")])

(define_insn "float<mode>xf2"
  [(set (match_operand:XF 0 "e2k_register_operand" "=&r")
	(float:XF (match_operand:I48 1 "e2k_register_operand" "r")))
   (clobber (match_scratch:DI 2 "=&r"))]
  ""
  "i<sd>tofx\t%1, %2%#movfi\t%2, %H0\n\taddd\t%2, 0x0, %0%#sxt\t5, %H0, %H0"
  [(set_attr "type" "multi")])

(define_insn "fix_truncxf<mode>2"
  [(set (match_operand:I48 0 "e2k_register_operand" "=r")
	(fix:I48 (match_operand:XF 1 "e2k_register_operand" "r")))
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
  [(set (match_operand:BI 0 "e2k_register_operand" "=j")
	(match_operator:BI 1 "e2k_direct_int_cmp_operator"
	  [(match_operand:I48 2 "e2k_src1_operand" "rI")
	   (match_operand:I48 3 "e2k_src2_operand" "ri")]))]
  ""
  "cmp%K1<sd>b%,\t%2, %3, %0"
  [(set_attr "type" "cmp")])

(define_insn "*fcmp<mode>_pred"
  [(set (match_operand:BI 0 "e2k_register_operand" "=j")
	(match_operator:BI 1 "e2k_direct_fp_cmp_operator"
	  [(match_operand:F 2 "e2k_register_operand" "r")
	   (match_operand:F 3 "e2k_register_operand" "r")]))]
  ""
  "fcmp%K1<sd>b%,\t%2, %3, %0"
  [(set_attr "type" "fcmp")])

(define_insn "*fcmpxf_pred"
  [(set (match_operand:BI 0 "e2k_register_operand" "=j")
	(match_operator:BI 1 "e2k_direct_fp_cmp_operator"
	  [(match_operand:XF 2 "e2k_register_operand" "r")
	   (match_operand:XF 3 "e2k_register_operand" "r")]))
   (clobber (match_operand:DI 4 "e2k_register_operand" "=&r"))
   (clobber (match_operand:DI 5 "e2k_register_operand" "=&r"))]
  ""
  "movif\t%2, %H2, %4\n\tmovif\t%3, %H3, %5%#fxcmp%K1xb\t%4, %5, %0"
  [(set_attr "type" "multi")])

(define_insn "*cmpand<mode>_pred"
  [(set (match_operand:BI 0 "e2k_register_operand" "=j")
	(eq:BI (and:I48 (match_operand:I48 1 "e2k_register_operand" "r")
			(match_operand:I48 2 "e2k_src2_operand" "ri"))
	       (const_int 0)))]
  ""
  "cmpande<sd>b\t%1, %2, %0"
  [(set_attr "type" "cmp")])

;; Quiet compare into a register: x86-style flags, less 0x1, equal 0x40,
;; greater 0, unordered 0x45 (checked on the 4C; MCST qemu wrongly raises
;; invalid on quiet NaNs).  The result is 32 bits.
(define_insn "e2k_fcmpu<mode>"
  [(set (match_operand:SI 0 "e2k_register_operand" "=r")
	(unspec:SI [(match_operand:F 1 "e2k_register_operand" "r")
		    (match_operand:F 2 "e2k_register_operand" "r")]
		   UNSPEC_FCMPU))]
  ""
  "fcmpud<sd>f\t%1, %2, %0"
  [(set_attr "type" "fcmp")
   (set_attr "ales" "yes")])

(define_insn "e2k_fcmpuxf"
  [(set (match_operand:SI 0 "e2k_register_operand" "=&r")
	(unspec:SI [(match_operand:XF 1 "e2k_register_operand" "r")
		    (match_operand:XF 2 "e2k_register_operand" "r")]
		   UNSPEC_FCMPU))
   (clobber (match_operand:DI 3 "e2k_register_operand" "=&r"))]
  ""
  "movif\t%1, %H1, %0\n\tmovif\t%2, %H2, %3%#fxcmpudxf\t%0, %3, %0"
  [(set_attr "type" "multi")])

;; The same flags from the signaling compare (invalid on any NaN), for
;; LTGT: GCC folds a < b || a > b to it and expects it to signal.
(define_insn "e2k_fcmpo<mode>"
  [(set (match_operand:SI 0 "e2k_register_operand" "=r")
	(unspec:SI [(match_operand:F 1 "e2k_register_operand" "r")
		    (match_operand:F 2 "e2k_register_operand" "r")]
		   UNSPEC_FCMPO))]
  ""
  "fcmpod<sd>f\t%1, %2, %0"
  [(set_attr "type" "fcmp")])

(define_insn "e2k_fcmpoxf"
  [(set (match_operand:SI 0 "e2k_register_operand" "=&r")
	(unspec:SI [(match_operand:XF 1 "e2k_register_operand" "r")
		    (match_operand:XF 2 "e2k_register_operand" "r")]
		   UNSPEC_FCMPO))
   (clobber (match_operand:DI 3 "e2k_register_operand" "=&r"))]
  ""
  "movif\t%1, %H1, %0\n\tmovif\t%2, %H2, %3%#fxcmpodxf\t%0, %3, %0"
  [(set_attr "type" "multi")])

;; Predicated execution: GCC's if-conversion after reload (ce3) puts the
;; operations of a short branch arm under its predicate; they print it
;; with "%?" (e2k_print_operand).  A predicated operation reads its
;; predicate 2 cycles after a compare (spec/isa/timing.md), the DFA's
;; latency; the bundler keeps that across blocks.  On the 2C3 it is 1
;; (E2K_PRED1), also in a taken return's wide instruction.
(define_cond_exec
  [(match_operator 0 "e2k_pred_test_operator"
     [(match_operand:BI 1 "e2k_register_operand" "j")
      (const_int 0)])]
  ""
  "")

(define_insn "*branch_pred"
  [(set (pc)
	(if_then_else (match_operator 0 "e2k_pred_test_operator"
			[(match_operand:BI 1 "e2k_register_operand" "j")
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
			   [(match_operand:I48 1 "e2k_register_operand")
			    (match_operand:I48 2 "e2k_src2_operand")])
			 (label_ref (match_operand 3))
			 (pc)))
      (clobber (scratch:BI))])]
  "")

;; Bit tests: (x & m) == 0 or != 0 is one cmpande (spec/isa/
;; operations-v3.md, "Integer compares"), where an and and a compare
;; took two; combine forms the and, or the field test (zero_extract)
;; GCC makes of a mask, inside the branch, the store-flag and the
;; conditional move, as lcc tests bits.
(define_insn_and_split "*cbranch<mode>4_and"
  [(set (pc)
	(if_then_else
	  (match_operator 0 "e2k_pred_test_operator"
	    [(and:I48 (match_operand:I48 1 "e2k_register_operand" "r")
		      (match_operand:I48 2 "e2k_src2_operand" "ri"))
	     (const_int 0)])
	  (label_ref (match_operand 3))
	  (pc)))
   (clobber (match_scratch:BI 4 "=j"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  rtx ops[5] = { operands[0],
		 e2k_bit_test (<MODE>mode, operands[1], operands[2], NULL_RTX),
		 const0_rtx, operands[3], operands[4] };
  e2k_split_compare_branch (ops, <MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_insn_and_split "*cbranch<mode>4_extract"
  [(set (pc)
	(if_then_else
	  (match_operator 0 "e2k_pred_test_operator"
	    [(zero_extract:I48 (match_operand:I48 1 "e2k_register_operand" "r")
			       (match_operand 2 "const_int_operand")
			       (match_operand 5 "const_int_operand"))
	     (const_int 0)])
	  (label_ref (match_operand 3))
	  (pc)))
   (clobber (match_scratch:BI 4 "=j"))]
  "e2k_getf_field_p (<MODE>mode, operands[2], operands[5])"
  "#"
  "reload_completed"
  [(const_int 0)]
{
  rtx ops[5] = { operands[0],
		 e2k_bit_test (<MODE>mode, operands[1], operands[2],
			       operands[5]),
		 const0_rtx, operands[3], operands[4] };
  e2k_split_compare_branch (ops, <MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_insn_and_split "*cbranch<mode>4"
  [(set (pc)
	(if_then_else (match_operator 0 "e2k_int_cmp_operator"
			[(match_operand:I48 1 "e2k_register_operand" "r")
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
	   (if_then_else (match_operator 0 "e2k_any_fp_cmp_operator"
			   [(match_operand:F 1 "e2k_register_operand")
			    (match_operand:F 2 "e2k_register_operand")])
			 (label_ref (match_operand 3))
			 (pc)))
      (clobber (scratch:BI))
      (clobber (scratch:DI))])]
  ""
{
  if (e2k_lower_quiet_fp_cmp (&operands[0], &operands[1], &operands[2],
			      <MODE>mode))
    {
      emit_jump_insn (gen_cbranchsi4 (operands[0], operands[1], operands[2],
				      operands[3]));
      DONE;
    }
})

(define_insn_and_split "*cbranch<mode>4"
  [(set (pc)
	(if_then_else (match_operator 0 "e2k_fp_cmp_operator"
			[(match_operand:F 1 "e2k_register_operand" "r")
			 (match_operand:F 2 "e2k_register_operand" "r")])
		      (label_ref (match_operand 3))
		      (pc)))
   (clobber (match_scratch:BI 4 "=j"))
   (clobber (match_scratch:DI 5 "=X"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  e2k_split_compare_branch (operands, <MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_insn_and_split "*cbranch<mode>4_quiet"
  [(set (pc)
	(if_then_else (match_operator 0 "e2k_quiet_fp_cmp_operator"
			[(match_operand:F 1 "e2k_register_operand" "r")
			 (match_operand:F 2 "e2k_register_operand" "r")])
		      (label_ref (match_operand 3))
		      (pc)))
   (clobber (match_scratch:BI 4 "=j"))
   (clobber (match_scratch:DI 5 "=r"))]
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
	   (if_then_else (match_operator 0 "e2k_any_fp_cmp_operator"
			   [(match_operand:XF 1 "e2k_register_operand")
			    (match_operand:XF 2 "e2k_register_operand")])
			 (label_ref (match_operand 3))
			 (pc)))
      (clobber (scratch:BI))
      (clobber (scratch:DI))
      (clobber (scratch:DI))])]
  ""
{
  if (e2k_lower_quiet_fp_cmp (&operands[0], &operands[1], &operands[2],
			      XFmode))
    {
      emit_jump_insn (gen_cbranchsi4 (operands[0], operands[1], operands[2],
				      operands[3]));
      DONE;
    }
})

(define_insn_and_split "*cbranchxf4"
  [(set (pc)
	(if_then_else (match_operator 0 "e2k_any_fp_cmp_operator"
			[(match_operand:XF 1 "e2k_register_operand" "r")
			 (match_operand:XF 2 "e2k_register_operand" "r")])
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
  [(set (match_operand:GPRM 0 "e2k_register_operand" "=r")
	(if_then_else:GPRM
	  (match_operator 1 "e2k_pred_test_operator"
	    [(match_operand:BI 2 "e2k_register_operand" "j")
	     (const_int 0)])
	  (match_operand:GPRM 3 "e2k_src2_operand" "ri")
	  (match_operand:GPRM 4 "e2k_src1_operand" "rI")))]
  ""
  "merge<sd>\t%4, %3, %0, %C1%2")

(define_expand "cstore<mode>4"
  [(parallel
     [(set (match_operand:DI 0 "e2k_register_operand")
	   (match_operator:DI 1 "e2k_int_cmp_operator"
	     [(match_operand:I48 2 "e2k_register_operand")
	      (match_operand:I48 3 "e2k_src2_operand")]))
      (clobber (scratch:BI))])]
  "")

(define_insn_and_split "*cstore<mode>4_and"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(match_operator:DI 1 "e2k_pred_test_operator"
	  [(and:I48 (match_operand:I48 2 "e2k_register_operand" "r")
		    (match_operand:I48 3 "e2k_src2_operand" "ri"))
	   (const_int 0)]))
   (clobber (match_scratch:BI 4 "=j"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  rtx ops[5] = { operands[0], operands[1],
		 e2k_bit_test (<MODE>mode, operands[2], operands[3], NULL_RTX),
		 const0_rtx, operands[4] };
  e2k_split_cstore (ops, <MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_insn_and_split "*cstore<mode>4_extract"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(match_operator:DI 1 "e2k_pred_test_operator"
	  [(zero_extract:I48 (match_operand:I48 2 "e2k_register_operand" "r")
			     (match_operand 3 "const_int_operand")
			     (match_operand 5 "const_int_operand"))
	   (const_int 0)]))
   (clobber (match_scratch:BI 4 "=j"))]
  "e2k_getf_field_p (<MODE>mode, operands[3], operands[5])"
  "#"
  "reload_completed"
  [(const_int 0)]
{
  rtx ops[5] = { operands[0], operands[1],
		 e2k_bit_test (<MODE>mode, operands[2], operands[3],
			       operands[5]),
		 const0_rtx, operands[4] };
  e2k_split_cstore (ops, <MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_insn_and_split "*cstore<mode>4"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(match_operator:DI 1 "e2k_int_cmp_operator"
	  [(match_operand:I48 2 "e2k_register_operand" "r")
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
     [(set (match_operand:DI 0 "e2k_register_operand")
	   (match_operator:DI 1 "e2k_any_fp_cmp_operator"
	     [(match_operand:F 2 "e2k_register_operand")
	      (match_operand:F 3 "e2k_register_operand")]))
      (clobber (scratch:BI))
      (clobber (scratch:DI))])]
  ""
{
  if (e2k_lower_quiet_fp_cmp (&operands[1], &operands[2], &operands[3],
			      <MODE>mode))
    {
      emit_insn (gen_cstoresi4 (operands[0], operands[1], operands[2],
				operands[3]));
      DONE;
    }
})

(define_insn_and_split "*cstore<mode>4"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(match_operator:DI 1 "e2k_fp_cmp_operator"
	  [(match_operand:F 2 "e2k_register_operand" "r")
	   (match_operand:F 3 "e2k_register_operand" "r")]))
   (clobber (match_scratch:BI 4 "=j"))
   (clobber (match_scratch:DI 5 "=X"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  e2k_split_cstore (operands, <MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_insn_and_split "*cstore<mode>4_quiet"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(match_operator:DI 1 "e2k_quiet_fp_cmp_operator"
	  [(match_operand:F 2 "e2k_register_operand" "r")
	   (match_operand:F 3 "e2k_register_operand" "r")]))
   (clobber (match_scratch:BI 4 "=j"))
   (clobber (match_scratch:DI 5 "=r"))]
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
     [(set (match_operand:GPRM 0 "e2k_register_operand")
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

(define_insn_and_split "*movcc<GPRM:mode><I48:mode>_and"
  [(set (match_operand:GPRM 0 "e2k_register_operand" "=r")
	(if_then_else:GPRM
	  (match_operator 1 "e2k_pred_test_operator"
	    [(and:I48 (match_operand:I48 2 "e2k_register_operand" "r")
		      (match_operand:I48 3 "e2k_src2_operand" "ri"))
	     (const_int 0)])
	  (match_operand:GPRM 4 "e2k_src2_operand" "ri")
	  (match_operand:GPRM 5 "e2k_src1_operand" "rI")))
   (clobber (match_scratch:BI 6 "=j"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  rtx ops[7] = { operands[0], operands[1],
		 e2k_bit_test (<I48:MODE>mode, operands[2], operands[3],
			       NULL_RTX),
		 const0_rtx, operands[4], operands[5], operands[6] };
  e2k_split_movcc (ops, <I48:MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_insn_and_split "*movcc<GPRM:mode><I48:mode>_extract"
  [(set (match_operand:GPRM 0 "e2k_register_operand" "=r")
	(if_then_else:GPRM
	  (match_operator 1 "e2k_pred_test_operator"
	    [(zero_extract:I48 (match_operand:I48 2 "e2k_register_operand" "r")
			       (match_operand 3 "const_int_operand")
			       (match_operand 7 "const_int_operand"))
	     (const_int 0)])
	  (match_operand:GPRM 4 "e2k_src2_operand" "ri")
	  (match_operand:GPRM 5 "e2k_src1_operand" "rI")))
   (clobber (match_scratch:BI 6 "=j"))]
  "e2k_getf_field_p (<I48:MODE>mode, operands[3], operands[7])"
  "#"
  "reload_completed"
  [(const_int 0)]
{
  rtx ops[7] = { operands[0], operands[1],
		 e2k_bit_test (<I48:MODE>mode, operands[2], operands[3],
			       operands[7]),
		 const0_rtx, operands[4], operands[5], operands[6] };
  e2k_split_movcc (ops, <I48:MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_insn_and_split "*movcc<GPRM:mode><I48:mode>"
  [(set (match_operand:GPRM 0 "e2k_register_operand" "=r")
	(if_then_else:GPRM
	  (match_operator 1 "e2k_int_cmp_operator"
	    [(match_operand:I48 2 "e2k_register_operand" "r")
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
  [(set (match_operand:GPRM 0 "e2k_register_operand" "=r")
	(if_then_else:GPRM
	  (match_operator 1 "e2k_fp_cmp_operator"
	    [(match_operand:F 2 "e2k_register_operand" "r")
	     (match_operand:F 3 "e2k_register_operand" "r")])
	  (match_operand:GPRM 4 "e2k_src2_operand" "ri")
	  (match_operand:GPRM 5 "e2k_src1_operand" "rI")))
   (clobber (match_scratch:BI 6 "=j"))
   (clobber (match_scratch:DI 7 "=X"))]
  ""
  "#"
  "reload_completed"
  [(const_int 0)]
{
  e2k_split_movcc (operands, <F:MODE>mode);
  DONE;
}
  [(set_attr "type" "multi")])

(define_insn_and_split "*movcc<GPRM:mode><F:mode>_quiet"
  [(set (match_operand:GPRM 0 "e2k_register_operand" "=r")
	(if_then_else:GPRM
	  (match_operator 1 "e2k_quiet_fp_cmp_operator"
	    [(match_operand:F 2 "e2k_register_operand" "r")
	     (match_operand:F 3 "e2k_register_operand" "r")])
	  (match_operand:GPRM 4 "e2k_src2_operand" "ri")
	  (match_operand:GPRM 5 "e2k_src1_operand" "rI")))
   (clobber (match_scratch:BI 6 "=j"))
   (clobber (match_scratch:DI 7 "=&r"))]
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

;; An indirect jump goes through a CTPR: movtd, then ct, 9 cycles apart
;; to avoid a stall (spec/isa/timing.md).  The movtd is an insn of its
;; own, as a call's is, so that the scheduler can hoist it.
(define_expand "indirect_jump"
  [(set (pc) (match_operand:DI 0 "e2k_register_operand"))]
  ""
{
  emit_insn (gen_e2k_movtd_ctpr2 (operands[0]));
  emit_jump_insn (gen_e2k_indirect_ct ());
  DONE;
})

(define_insn "e2k_movtd_ctpr2"
  [(set (reg:DI CTPR2_REGNUM)
	(unspec:DI [(match_operand:DI 0 "e2k_register_operand" "r")]
		   UNSPEC_MOVTD))]
  ""
  "movtd\t%0, %%ctpr2"
  [(set_attr "type" "movctp")])

(define_insn "e2k_indirect_ct"
  [(set (pc) (unspec:DI [(reg:DI CTPR2_REGNUM)] UNSPEC_MOVTD))]
  ""
  "ct\t%%ctpr2"
  [(set_attr "type" "ct")])

(define_expand "tablejump"
  [(parallel [(set (pc) (match_operand:DI 0 "e2k_register_operand"))
	      (use (label_ref (match_operand 1)))])]
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
  emit_insn (gen_e2k_movtd_ctpr2 (operands[0]));
  emit_jump_insn (gen_e2k_tablejump_ct (operands[1]));
  DONE;
})

(define_insn "e2k_tablejump_ct"
  [(set (pc) (unspec:DI [(reg:DI CTPR2_REGNUM)] UNSPEC_MOVTD))
   (use (label_ref (match_operand 0)))]
  ""
  "ct\t%%ctpr2"
  [(set_attr "type" "ct")])

;; Prepares carry "ipd 2" (prefetch the target and the next line) for
;; v3, as lcc writes it there; lcc's v4+ targets write none, and neither
;; changes zlib's speed measurably on the 8C2 (findings I25).

;; Loop back edges become prepared transfers: a taken ibranch costs 6
;; cycles on the 4C, a ct whose CTPR was prepared outside the loop none
;; (see e2k_prepare_loop_branches).
(define_insn "e2k_disp_label"
  [(set (match_operand:DI 0 "e2k_ctpr_operand" "=t")
	(unspec:DI [(label_ref (match_operand 1))] UNSPEC_DISP))]
  ""
  { return e2k_arch <= 3 ? "disp\t%0, %l1; ipd 2" : "disp\t%0, %l1"; }
  [(set_attr "type" "disp")])

(define_insn "*ct_pred"
  [(set (pc)
	(if_then_else (match_operator 0 "e2k_pred_test_operator"
			[(match_operand:BI 1 "e2k_register_operand" "j")
			 (const_int 0)])
		      (label_ref (match_operand 2))
		      (pc)))
   (use (match_operand:DI 3 "e2k_ctpr_operand" "t"))]
  ""
  "* return e2k_output_ct_pred (insn);"
  [(set_attr "type" "ct")])

;; Predicate logic (PLS): operand 0 = condition 1 && condition 2, each a
;; predicate or its negation, through the primary predicates @p0 and @p1
;; and the result @p4 (spec/isa/bundle.md, "PLS").  landp ("lazy and")
;; ignores the second condition's diagnostic tag when the first is false
;; (MCST qemu, translate-pls.c), so a condition computed speculatively may
;; follow one that already decides.  One per wide instruction, for the
;; @p names; latency 1 from a compare, 3 to a ct (spec/isa/timing.md).
;; For the while loops e2k_modsched pipelines.
(define_insn "e2k_landp"
  [(set (match_operand:BI 0 "e2k_register_operand" "=j")
	(and:BI (match_operator:BI 1 "e2k_pred_test_operator"
		  [(match_operand:BI 2 "e2k_register_operand" "j")
		   (const_int 0)])
		(match_operator:BI 3 "e2k_pred_test_operator"
		  [(match_operand:BI 4 "e2k_register_operand" "j")
		   (const_int 0)])))]
  ""
  "pass\t%2, @p0\n\tpass\t%4, @p1\n\tlandp\t%C1@p0, %C3@p1, @p4\n\tpass\t@p4, %0"
  [(set_attr "type" "plog")])

;; Three and four conditions in one wide instruction: the four ELPs load
;; @p0-@p3 and the three CLPs compute @p4-@p6; a CLP may read another's
;; result, two deep at most (gas: "maximal supported cascading of 2",
;; from MCST's iset description), so four conditions are a tree.  The
;; first operand of each landp is the conditions before its second, so
;; this is C's c1 && c2 && c3 && c4 with each condition computed
;; speculatively under the ones before it: landp ignores its second
;; operand's diagnostic tag when the first is false.
(define_insn "e2k_landp3"
  [(set (match_operand:BI 0 "e2k_register_operand" "=j")
	(and:BI
	  (and:BI (match_operator:BI 1 "e2k_pred_test_operator"
		    [(match_operand:BI 2 "e2k_register_operand" "j")
		     (const_int 0)])
		  (match_operator:BI 3 "e2k_pred_test_operator"
		    [(match_operand:BI 4 "e2k_register_operand" "j")
		     (const_int 0)]))
	  (match_operator:BI 5 "e2k_pred_test_operator"
	    [(match_operand:BI 6 "e2k_register_operand" "j")
	     (const_int 0)])))]
  ""
  "pass\t%2, @p0\n\tpass\t%4, @p1\n\tpass\t%6, @p2\n\t\
landp\t%C1@p0, %C3@p1, @p4\n\tlandp\t@p4, %C5@p2, @p5\n\tpass\t@p5, %0"
  [(set_attr "type" "plog")])

(define_insn "e2k_landp4"
  [(set (match_operand:BI 0 "e2k_register_operand" "=j")
	(and:BI
	  (and:BI (match_operator:BI 1 "e2k_pred_test_operator"
		    [(match_operand:BI 2 "e2k_register_operand" "j")
		     (const_int 0)])
		  (match_operator:BI 3 "e2k_pred_test_operator"
		    [(match_operand:BI 4 "e2k_register_operand" "j")
		     (const_int 0)]))
	  (and:BI (match_operator:BI 5 "e2k_pred_test_operator"
		    [(match_operand:BI 6 "e2k_register_operand" "j")
		     (const_int 0)])
		  (match_operator:BI 7 "e2k_pred_test_operator"
		    [(match_operand:BI 8 "e2k_register_operand" "j")
		     (const_int 0)]))))]
  ""
  "pass\t%2, @p0\n\tpass\t%4, @p1\n\tpass\t%6, @p2\n\tpass\t%8, @p3\n\t\
landp\t%C1@p0, %C3@p1, @p4\n\tlandp\t%C5@p2, %C7@p3, @p5\n\t\
landp\t@p4, @p5, @p6\n\tpass\t@p6, %0"
  [(set_attr "type" "plog")])

(define_insn "*ct_jump"
  [(set (pc) (label_ref (match_operand 0)))
   (use (match_operand:DI 1 "e2k_ctpr_operand" "t"))]
  ""
  "ct\t%1"
  [(set_attr "type" "ct")])

;; ---------------------------------------------------------------------
;; Counted loops
;;
;; The doloop pass ends a counted loop with e2k_doloop_end on a counter
;; holding the iteration count.  In machine reorg e2k_hwloop_opt turns
;; an innermost loop without calls into a hardware loop: the count goes
;; to %lsr (with vlc) before the loop and the end becomes alc + ct
;; through a prepared CTPR on %NOT_LOOP_END (spec/isa/loops.md).  A loop
;; it can't convert keeps e2k_doloop_end, which decrements, compares and
;; branches (the second alternative for a counter spilled to memory).
;;
;; %lsr counts 32 bits.  A loop whose count may not fit gets it in %lsr1
;; on v5+ (e2k_rwd_lsr_wide); before, it is strip-mined as lcc does: e2k_doloop_end_wide also asks for a DI scratch, and since
;; RA keeps both scratches out of the loop's live registers, the
;; preheader computes the first chunk in them and the exit path tests
;; for more chunks with the predicate (e2k_hwloop_end_wide).
;; ---------------------------------------------------------------------

(define_expand "doloop_end"
  [(use (match_operand 0 "nonimmediate_operand"))
   (use (label_ref (match_operand 1)))]
  "optimize"
{
  if (GET_MODE (operands[0]) != DImode
      || e2k_doloop_declined_p (operands[1]))
    FAIL;
  rtx n = GEN_INT (e2k_doloop_iters);
  if (e2k_doloop_wide)
    emit_jump_insn (gen_e2k_doloop_end_wide (operands[0], operands[1], n));
  else
    emit_jump_insn (gen_e2k_doloop_end (operands[0], operands[1], n));
  DONE;
})

(define_insn "e2k_doloop_end"
  [(set (pc)
	(if_then_else (ne (match_operand:DI 0 "nonimmediate_operand" "+r,*m")
			  (const_int 1))
		      (label_ref (match_operand 1))
		      (pc)))
   (set (match_dup 0) (plus:DI (match_dup 0) (const_int -1)))
   (unspec [(const_int 0) (match_operand 2 "const_int_operand")] UNSPEC_DOLOOP)
   (clobber (match_scratch:BI 3 "=j,j"))
   (clobber (match_scratch:DI 4 "=X,&r"))]
  ""
  "@
   subd\t%0, 1, %0%#cmpedb\t%0, 0, %3%#ibranch\t%l1 ? ~%3
   ldd\t%0, %4%#subd\t%4, 1, %4%#std\t%0, %4%#cmpedb\t%4, 0, %3%#ibranch\t%l1 ? ~%3"
  [(set_attr "type" "multi")])

(define_insn "e2k_doloop_end_wide"
  [(set (pc)
	(if_then_else (ne (match_operand:DI 0 "nonimmediate_operand" "+r,*m")
			  (const_int 1))
		      (label_ref (match_operand 1))
		      (pc)))
   (set (match_dup 0) (plus:DI (match_dup 0) (const_int -1)))
   (unspec [(const_int 1) (match_operand 2 "const_int_operand")] UNSPEC_DOLOOP)
   (clobber (match_scratch:BI 3 "=j,j"))
   (clobber (match_scratch:DI 4 "=&r,&r"))]
  ""
  "@
   subd\t%0, 1, %0%#cmpedb\t%0, 0, %3%#ibranch\t%l1 ? ~%3
   ldd\t%0, %4%#subd\t%4, 1, %4%#std\t%0, %4%#cmpedb\t%4, 0, %3%#ibranch\t%l1 ? ~%3"
  [(set_attr "type" "multi")])

;; The end of a hardware loop: count down %lsr and go back to the start
;; through the prepared CTPR (operand 0) until the count runs out.
(define_insn "e2k_hwloop_end"
  [(set (pc)
	(if_then_else (ne (unspec:DI [(const_int 0)] UNSPEC_LOOP_END)
			  (const_int 0))
		      (label_ref (match_operand 1))
		      (pc)))
   (use (match_operand:DI 0 "e2k_ctpr_operand" "t"))]
  ""
  "* return e2k_output_hwloop_end (insn);"
  [(set_attr "type" "ct")])

;; The end of a strip-mined loop: operand 2 holds the iterations left
;; after this chunk, a multiple of the chunk size; operand 3 is free
;; after the loop.  The test for another chunk follows the wide
;; instruction and branches to a stub that reloads %lsr and goes back
;; to the loop (e2k_output_hwloop_end_wide).
(define_insn "e2k_hwloop_end_wide"
  [(set (pc)
	(if_then_else (ne (unspec:DI [(const_int 0)] UNSPEC_LOOP_END)
			  (const_int 0))
		      (label_ref (match_operand 1))
		      (pc)))
   (use (match_operand:DI 0 "e2k_ctpr_operand" "t"))
   (set (match_operand:DI 2 "e2k_register_operand" "+r")
	(unspec:DI [(match_dup 2)] UNSPEC_LOOP_END))
   (clobber (match_operand:BI 3 "e2k_register_operand" "=j"))]
  ""
  "* return e2k_output_hwloop_end_wide (insn, operands);"
  [(set_attr "type" "ct")])

(define_insn "e2k_rwd_lsr"
  [(unspec_volatile [(match_operand:DI 0 "e2k_register_operand" "r")]
		    UNSPECV_RWD_LSR)]
  ""
  "rwd\t%0, %%lsr"
  [(set_attr "type" "getsp")])

;; v5+: a count that may not fit %lsr's 32 bits goes to %lsr1, the 64-bit
;; counter, written after %lsr (vlc only), which would otherwise reset it
;; (spec/isa/loops.md, "%lsr1"; lcc: rwd %lsr, then rwd n, %lsr1).
(define_insn "e2k_rwd_lsr_wide"
  [(unspec_volatile [(match_operand:DI 0 "e2k_register_operand" "r")]
		    UNSPECV_RWD_LSR1)]
  "e2k_arch >= 5"
  "rwd\t0x2000000000, %%lsr%#rwd\t%0, %%lsr1"
  [(set_attr "type" "multi")])

;; The rotating area of %b[] for a pipelined loop (e2k_modsched), its
;; size in register pairs in operand 0, and giving the outgoing registers
;; back after the loop.  Printed at final time, when the window is known.
;; Dataflow doesn't know that setbn renames %b[0..7]: a value there
;; before the loop that is live after it is used by the first (else the
;; ring's writes under the same names would make it dead) and set again
;; by the second, as the ring lies elsewhere in the window.  Operands 2-9
;; are those %b[] (const0_rtx for the others, which would otherwise look
;; live before every pipelined loop; e2k_ms_gen_setbn_enter).
(define_insn "e2k_setbn_enter"
  [(unspec_volatile [(match_operand 0 "const_int_operand")
		     (match_operand 1 "const_int_operand")] UNSPECV_SETBN)
   (use (match_operand 2 "e2k_setbn_use_operand"))
   (use (match_operand 3 "e2k_setbn_use_operand"))
   (use (match_operand 4 "e2k_setbn_use_operand"))
   (use (match_operand 5 "e2k_setbn_use_operand"))
   (use (match_operand 6 "e2k_setbn_use_operand"))
   (use (match_operand 7 "e2k_setbn_use_operand"))
   (use (match_operand 8 "e2k_setbn_use_operand"))
   (use (match_operand 9 "e2k_setbn_use_operand"))]
  ""
  { return e2k_output_setbn (INTVAL (operands[0]), INTVAL (operands[1])); }
  [(set_attr "type" "setwd")])

(define_insn "e2k_setbn_leave"
  [(unspec_volatile [(const_int 0)] UNSPECV_SETBN)
   (set (reg:DI 96) (unspec:DI [(const_int 0)] UNSPEC_SETBN_B))
   (set (reg:DI 97) (unspec:DI [(const_int 0)] UNSPEC_SETBN_B))
   (set (reg:DI 98) (unspec:DI [(const_int 0)] UNSPEC_SETBN_B))
   (set (reg:DI 99) (unspec:DI [(const_int 0)] UNSPEC_SETBN_B))
   (set (reg:DI 100) (unspec:DI [(const_int 0)] UNSPEC_SETBN_B))
   (set (reg:DI 101) (unspec:DI [(const_int 0)] UNSPEC_SETBN_B))
   (set (reg:DI 102) (unspec:DI [(const_int 0)] UNSPEC_SETBN_B))
   (set (reg:DI 103) (unspec:DI [(const_int 0)] UNSPEC_SETBN_B))]
  ""
  { return e2k_output_setbn (0, 0); }
  [(set_attr "type" "setwd")])

;; N + 1 empty cycles as a wide instruction of their own (a pipelined
;; loop's kernel that starts with them).
(define_insn "e2k_nop_bundle"
  [(unspec_volatile [(match_operand 0 "const_int_operand")]
		    UNSPECV_NOP_BUNDLE)]
  ""
  "{\n\tnop\t%0\n\t}"
  [(set_attr "type" "raw")])

;; rwd %lsr takes 4 cycles; a loop entered sooner runs once too often on
;; v3-v5 and stops after one iteration on v6 (spec/isa/loops.md).
;; The preheader and the loop are different blocks to the scheduler, so
;; spend the cycles explicitly: what of the 4 the wide instructions since
;; rwd haven't (e2k_output_lsr_wait).
(define_insn "e2k_lsr_wait"
  [(unspec_volatile [(const_int 0)] UNSPECV_LSR_WAIT)]
  ""
  { return e2k_output_lsr_wait (insn); }
  [(set_attr "type" "raw")])

;; Array prefetch (spec/isa/apb.md), for the loads of a pipelined loop
;; (e2k_modsched, e2k_ms_apb): a mova reads an element of its area's
;; current step (operand 1 the area, i.e. the program instruction; 2 the
;; channel, which picks the half; 3 the element size; 4 the byte offset
;; in the step, ind) and with operand 5 (am) 1 advances the area.  It
;; needs the program in %ctpr2 until the loop ends.
(define_mode_iterator MOVAM [QI HI SI DI SF DF V8QI V4HI V2SI V2SF
			     V16QI V8HI V4SI V2DI V4SF V2DF])

(define_insn "@e2k_mova<mode>"
  [(set (match_operand:MOVAM 0 "e2k_register_operand" "=r")
	(unspec:MOVAM [(match_operand 1 "const_int_operand")
		       (match_operand 2 "const_int_operand")
		       (match_operand 3 "const_int_operand")
		       (match_operand 4 "const_int_operand")
		       (match_operand 5 "const_int_operand")]
		      UNSPEC_MOVA))
   (use (reg:DI CTPR2_REGNUM))]
  ""
  { return e2k_output_mova (operands); }
  [(set_attr "type" "mova")])

;; A descriptor's base (v3: the array address in the descriptor, the
;; start index the one the hardware fixes, %aaind0 = 0).  ALC2 or ALC5.
(define_insn "e2k_aaurwd"
  [(unspec_volatile [(match_operand:DI 0 "e2k_register_operand" "r")
		     (match_operand 1 "const_int_operand")]
		    UNSPECV_AAURWD)]
  ""
  "aaurwd\t%0, %%aad%1"
  [(set_attr "type" "aau")])

;; An increment register (operand 1, 1-7; %aaincr0 is always 1): the
;; step of the areas that name it, in elements.  It takes a register
;; (gas).
(define_insn "e2k_aaurw_incr"
  [(unspec_volatile [(match_operand:DI 0 "e2k_register_operand" "r")
		     (match_operand 1 "const_int_operand")]
		    UNSPECV_AAURW_INCR)]
  ""
  ;; %aaincr is 32 bits, sign-extended, before v5 and 64 bits from v5 on
  ;; (spec/isa/apb.md), where a 32-bit write of a negative step would
  ;; not do; lcc writes aaurwd there.
  {
    return (e2k_arch >= 5 ? "aaurwd\t%0, %%aaincr%1"
	    : "aaurw\t%0, %%aaincr%1");
  }
  [(set_attr "type" "aau")])

;; A store index (operand 1, 0-15), for AAU stores.
(define_insn "e2k_aaurw_sti"
  [(unspec_volatile [(match_operand:DI 0 "e2k_register_operand" "r")
		     (match_operand 1 "const_int_operand")]
		    UNSPECV_AAURW_STI)]
  ""
  ;; %aasti is 32 bits before v5 and 64 from v5 on, as %aaind.
  {
    return (e2k_arch >= 5 ? "aaurwd\t%0, %%aasti%1"
	    : "aaurw\t%0, %%aasti%1");
  }
  [(set_attr "type" "aau")])

;; An AAU store (spec/isa/apb.md, "AAU stores") in a pipelined loop's
;; kernel (e2k_ms_mark_staa): operand 0 to AAD[1].base + AASTI[2] +
;; operand 3 (bytes), then AASTI[2] steps AAINCR[4] elements.  ALC2 or
;; ALC5; it needs no array prefetch program.  The address is the unspec
;; alone: the kernel's insns are final, and the alias oracle takes it
;; for any address.
(define_insn "@e2k_staa<mode>"
  [(set (mem:MOVAM (unspec:DI [(match_operand 1 "const_int_operand")
			       (match_operand 2 "const_int_operand")
			       (match_operand 3 "const_int_operand")
			       (match_operand 4 "const_int_operand")]
			      UNSPEC_STAA))
	(match_operand:MOVAM 0 "e2k_register_operand" "r"))]
  ""
  { return e2k_output_staa (operands, GET_MODE_SIZE (<MODE>mode)); }
  [(set_attr "type" "store")])

;; The program at .LAPB<operand 0> into %ctpr2, and its start.
(define_insn "e2k_ldisp_apb"
  [(set (reg:DI CTPR2_REGNUM)
	(unspec:DI [(match_operand 0 "const_int_operand")] UNSPEC_LDISP))]
  ""
  "ldisp\t%%ctpr2, .LAPB%0"
  [(set_attr "type" "disp")])

(define_insn "e2k_bap"
  [(unspec_volatile [(reg:DI CTPR2_REGNUM)] UNSPECV_BAP)]
  ""
  "bap"
  [(set_attr "type" "bap")])

;; After the loop, as lcc ends one: overwriting %ctpr2 ends the program,
;; and a write to %aabf0 keeps the kernel from restarting it after a
;; trap (spec/isa/apb.md, "Starting, pausing and stopping").
(define_insn "e2k_apb_stop"
  [(set (reg:DI CTPR2_REGNUM)
	(unspec_volatile:DI [(const_int 0)] UNSPECV_APB_STOP))]
  ""
  "disp\t%%ctpr2, disp=0x0"
  [(set_attr "type" "disp")])

(define_insn "e2k_aabf"
  [(unspec_volatile [(match_operand:DI 0 "e2k_register_operand" "r")]
		    UNSPECV_AABF)]
  ""
  "aaurw\t%0, %%aabf0"
  [(set_attr "type" "aau")])

;; __builtin_prefetch, as lcc prefetches: a byte load into %empty,
;; speculative (it never traps), with the MAS of its locality
;; (e2k_prefetch_mas).
(define_insn "prefetch"
  [(prefetch (match_operand:DI 0 "address_operand" "p")
	     (match_operand 1 "const_int_operand")
	     (match_operand 2 "const_int_operand"))]
  ""
  { return e2k_output_prefetch (operands); }
  [(set_attr "type" "load")
   (set (attr "mas")
	(if_then_else (match_test "e2k_prefetch_mas (INTVAL (operands[2]))")
		      (const_string "yes") (const_string "no")))])

;; ---------------------------------------------------------------------
;; Calls
;;
;; disp/movtd prepares %ctpr1 as a separate insn so that the scheduler
;; can hoist it (disp -> call 5 cycles, movtd -> call 9).
;;
;; A call may run under a predicate ("call %ctpr1, wbs = N ? %predK"), as
;; lcc calls sqrt for its errno only when fsqrttd's operand is negative
;; and log only for the points it keeps (NPB EP): if-conversion then
;; predicates a rarely taken arm with a call instead of branching around
;; it.  Its disp stays unconditional: it only writes %ctpr1, which the
;; call reads, and calls clobber the CTPRs anyway, so no other value
;; lives there across the arm; dataflow keeps the conditional write in
;; order with the other prepares.
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
  { return e2k_arch <= 3 ? "disp\t%%ctpr1, %0; ipd 2" : "disp\t%%ctpr1, %0"; }
  [(set_attr "type" "disp")
   (set_attr "predicable" "yes")])

(define_insn "e2k_movtd_ctpr1"
  [(set (reg:DI CTPR1_REGNUM)
	(unspec:DI [(match_operand:DI 0 "e2k_register_operand" "r")] UNSPEC_MOVTD))]
  ""
  "movtd\t%0, %%ctpr1"
  [(set_attr "type" "movctp")])

(define_insn "e2k_call"
  [(call (mem:DI (reg:DI CTPR1_REGNUM))
	 (match_operand 0))]
  ""
  { return e2k_output_call (); }
  [(set_attr "type" "call")
   (set_attr "predicable" "yes")])

(define_insn "e2k_call_value"
  [(set (match_operand 0)
	(call (mem:DI (reg:DI CTPR1_REGNUM))
	      (match_operand 1)))]
  ""
  { return e2k_output_call (); }
  [(set_attr "type" "call")
   (set_attr "predicable" "yes")])

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

;; A register amount must be in a window register (constraint "w"):
;; when getsp needs more stack the kernel decodes the operand, and from a
;; global below %g16 it can't, so it grows the stack by 16 KiB only and
;; the program faults (an 800 KB VLA did).  lcc moves the amount to %g24.
(define_insn "e2k_getsp"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(unspec_volatile:DI [(match_operand:DI 1 "e2k_src2_operand" "wi")]
			    UNSPECV_GETSP))]
  ""
  "getsp\t%1, %0"
  [(set_attr "type" "getsp")])

(define_insn "e2k_return_prep"
  [(set (reg:DI CTPR3_REGNUM)
	(unspec:DI [(const_int 0)] UNSPEC_RETURN))]
  ""
  { return e2k_arch <= 3 ? "return\t%%ctpr3; ipd 2" : "return\t%%ctpr3"; }
  [(set_attr "type" "ret")])

(define_insn "e2k_return"
  [(return)
   (use (reg:DI CTPR3_REGNUM))]
  "reload_completed"
  "ct\t%%ctpr3"
  [(set_attr "type" "ct")])

;; A return under a predicate, in a function that prepared %ctpr3 at its
;; entry (e2k_cond_returns).  A plain SET, as GCC wants a conditional
;; return; the function's end uses %ctpr3 (EPILOGUE_USES).
(define_insn "e2k_cond_return"
  [(set (pc)
	(if_then_else (match_operator 0 "e2k_pred_test_operator"
			[(match_operand:BI 1 "e2k_register_operand" "j")
			 (const_int 0)])
		      (return)
		      (pc)))]
  "e2k_epilogue_uses (CTPR3_REGNUM)"
  "ct\t%%ctpr3 ? %C0%1"
  [(set_attr "type" "ct")])

(define_expand "allocate_stack"
  [(match_operand:DI 0 "e2k_register_operand")
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
  [(match_operand:DI 0 "e2k_register_operand")
   (match_operand:DI 1 "e2k_register_operand")]
  ""
{
  rtx delta = expand_binop (DImode, sub_optab, operands[1],
			    stack_pointer_rtx, NULL_RTX, 0, OPTAB_LIB_WIDEN);
  emit_insn (gen_e2k_getsp (stack_pointer_rtx, force_reg (DImode, delta)));
  DONE;
})

(define_expand "restore_stack_nonlocal"
  [(match_operand:DI 0 "e2k_register_operand")
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

;; The current procedure's return address is in %cr0.hi (its IP field,
;; bits 0-47, in bytes).
(define_insn "e2k_rrd_cr0hi"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(unspec_volatile:DI [(const_int 0)] UNSPECV_RRD_CR0HI))]
  ""
  "rrd\t%%cr0.hi, %0"
  [(set_attr "type" "getsp")])

;; The FP control and status registers, for TARGET_ATOMIC_ASSIGN_EXPAND_FENV.
;; Operand 1 selects the register: 0 %pfpfr (float and double), 1 %fpcr
;; and 2 %fpsr (80-bit operations, the x87 control and status words).
(define_insn "e2k_rrs"
  [(set (match_operand:SI 0 "e2k_register_operand" "=r")
	(unspec_volatile:SI [(match_operand 1 "const_int_operand")]
			    UNSPECV_RRS))]
  ""
  "rrs\t%%%R1, %0"
  [(set_attr "type" "getsp")])

(define_insn "e2k_rws"
  [(unspec_volatile [(match_operand 0 "const_int_operand")
		     (match_operand:SI 1 "e2k_register_operand" "r")]
		    UNSPECV_RWS)]
  ""
  "rws\t%1, %%%R0"
  [(set_attr "type" "getsp")])

;; The end of a C++ thunk (e2k_output_mi_thunk): transfer to the target
;; with ct, without a call, so it runs in the thunk's caller's call.
(define_insn "e2k_thunk_jump"
  [(unspec_volatile [(match_operand:DI 0 "e2k_symbolic_operand")]
		    UNSPECV_THUNK_JUMP)]
  ""
  ".accept\tstrict_delay\n\t{\n\tdisp\t%%ctpr1, %0\n\t}\n\t{\n\tct\t%%ctpr1\n\t}\n\t.ignore\tstrict_delay"
  [(set_attr "type" "raw")])

;; Nonlocal goto, also used by __builtin_setjmp/__builtin_longjmp: see
;; e2k_expand_save_stack_nonlocal.
(define_expand "save_stack_nonlocal"
  [(use (match_operand:DI 0 "memory_operand"))
   (use (match_operand:DI 1 "e2k_register_operand"))]
  ""
{
  e2k_expand_save_stack_nonlocal (operands[0]);
  DONE;
})

(define_expand "nonlocal_goto"
  [(use (match_operand 0 "general_operand"))
   (use (match_operand 1 "general_operand"))
   (use (match_operand 2 "general_operand"))
   (use (match_operand 3 "general_operand"))]
  ""
{
  e2k_expand_nonlocal_goto (operands[1], operands[2]);
  DONE;
})

;; __builtin_eh_return: MCST's unwinder installs the target frame with the
;; set_backtrace system call and then simply returns, so there is nothing
;; to do here.
(define_expand "eh_return"
  [(use (match_operand:DI 0 "general_operand"))]
  ""
{
  DONE;
})

;; ---------------------------------------------------------------------
;; PIC and TLS
;; ---------------------------------------------------------------------

;; GOT address: rrd %ip and the PC-relative _GLOBAL_OFFSET_TABLE_ literal
;; must be in the same wide instruction (spec/abi/elf.md).
(define_insn "e2k_gotbase"
  [(set (match_operand:DI 0 "e2k_register_operand" "=&r")
	(unspec:DI [(const_int 0)] UNSPEC_GOTBASE))
   (clobber (match_scratch:DI 1 "=&r"))]
  ""
  "%<rrd\t%%ip, %0\n\taddd\t0x0, _GLOBAL_OFFSET_TABLE_, %1%>%#addd\t%0, %1, %0"
  [(set_attr "type" "multi")])

(define_insn "*tls_le"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(plus:DI (reg:DI TP_REGNUM)
		 (unspec:DI [(match_operand:DI 1 "e2k_symbolic_operand")]
			    UNSPEC_TLS_LE)))]
  ""
  "addd\t%%g13, %1@TLS_LE, %0")

(define_insn "*gotoff"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(plus:DI (match_operand:DI 1 "e2k_register_operand" "r")
		 (unspec:DI [(match_operand:DI 2 "e2k_symbolic_operand")]
			    UNSPEC_GOTOFF)))]
  ""
  "addd\t%1, %2@GOTOFF, %0")

;; The stack protector's guard is glibc's, at TP - 8 (spec/abi/elf.md,
;; "Stack protector"; MCST's glibc has no __stack_chk_guard), so the
;; guard hook gives no decl and these read it.  The read is volatile:
;; nothing may keep the guard in a register between the two.
(define_expand "stack_protect_set"
  [(match_operand:DI 0 "memory_operand")
   (match_operand:DI 1 "")]
  ""
{
  rtx t = gen_reg_rtx (DImode);
  emit_move_insn (t, e2k_ssp_guard ());
  emit_move_insn (operands[0], t);
  DONE;
})

(define_expand "stack_protect_test"
  [(match_operand:DI 0 "memory_operand")
   (match_operand:DI 1 "")
   (match_operand 2 "")]
  ""
{
  rtx a = force_reg (DImode, operands[0]);
  rtx b = force_reg (DImode, e2k_ssp_guard ());
  emit_cmp_and_jump_insns (a, b, EQ, NULL_RTX, DImode, 1, operands[2]);
  DONE;
})

;; A copy GCC can't see through: the address of the buffer for results
;; over 64 bytes, so that stores into it aren't deleted as dead before
;; the epilogue (which copies it out) exists.
(define_insn "e2k_opaque_copy"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(unspec:DI [(match_operand:DI 1 "e2k_register_operand" "r")] UNSPEC_OPAQUE))]
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
;; let gas pad them (.accept strict_delay), as lcc does.  The nops after
;; the load are lcc's v3 ones, the cheapest there and on the 8C2: a
;; spacing one cycle off costs a whole 4-cycle stall step.  On the 2C3
;; the cheapest are one cycle longer (E2K_LAT6; relcc2 findings A21:
;; lcc's v6 build pays about 3 cycles an atomic over them).
;; ---------------------------------------------------------------------

(define_mode_iterator ATM [QI HI SI DI])
(define_mode_attr ldsz [(QI "b") (HI "h") (SI "w") (DI "d")])
;; Width of the ALU operation on the loaded value.
(define_mode_attr opsz [(QI "s") (HI "s") (SI "s") (DI "d")])

(define_expand "atomic_compare_and_swap<mode>"
  [(match_operand:SI 0 "e2k_register_operand")	;; bool success
   (match_operand:ATM 1 "e2k_register_operand")	;; old value
   (match_operand:ATM 2 "memory_operand")	;; memory
   (match_operand:ATM 3 "e2k_register_operand")	;; expected
   (match_operand:ATM 4 "e2k_register_operand")	;; desired
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
  [(set (match_operand:DI 0 "e2k_register_operand" "=&r")
	(unspec_volatile:DI [(match_operand:ATM 2 "memory_operand" "+m")
			     (match_operand:DI 3 "e2k_register_operand" "r")
			     (match_operand:DI 4 "e2k_register_operand" "r")]
			    UNSPECV_CAS))
   (set (match_dup 2) (unspec_volatile:ATM [(const_int 0)] UNSPECV_CAS))
   (set (match_operand:DI 1 "e2k_register_operand" "=&r")
	(unspec_volatile:DI [(const_int 0)] UNSPECV_CAS))
   (clobber (match_scratch:BI 5 "=&j"))
   (clobber (match_scratch:DI 6 "=&r"))]
  ""
{
  return (E2K_LAT6
	  ? ".accept\tstrict_delay\n1:\n\tnop\t1\n\t{\n\tld<ldsz>,0\t%2, %0, mas = 0x7\n\tnop\t3\n\t}\n\t{\n\tcmpe<opsz>b,0\t%0, %3, %5\n\tnop\t1\n\t}\n\t{\n\tmerge<opsz>,0\t%0, %4, %6, %5\n\tmerged,1\t0x0, 0x1, %1, %5\n\t}\n\t{\n\tst<ldsz>,2\t%2, %6, mas = 0x2\n\trbranch\t1b\n\t}\n\t.ignore\tstrict_delay"
	  : ".accept\tstrict_delay\n1:\n\tnop\t1\n\t{\n\tld<ldsz>,0\t%2, %0, mas = 0x7\n\tnop\t2\n\t}\n\t{\n\tcmpe<opsz>b,0\t%0, %3, %5\n\tnop\t1\n\t}\n\t{\n\tmerge<opsz>,0\t%0, %4, %6, %5\n\tmerged,1\t0x0, 0x1, %1, %5\n\t}\n\t{\n\tst<ldsz>,2\t%2, %6, mas = 0x2\n\trbranch\t1b\n\t}\n\t.ignore\tstrict_delay");
}
  [(set_attr "type" "raw")])

(define_code_iterator ATOP [plus minus and ior xor])
(define_code_attr atop [(plus "add") (minus "sub") (and "and") (ior "or")
			(xor "xor")])
(define_code_attr atop_name [(plus "add") (minus "sub") (and "and")
			     (ior "or") (xor "xor")])

(define_expand "atomic_fetch_<atop_name><mode>"
  [(match_operand:ATM 0 "e2k_register_operand")
   (match_operand:ATM 1 "memory_operand")
   (ATOP:ATM (match_dup 1) (match_operand:ATM 2 "e2k_register_operand"))
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
  [(set (match_operand:ATM 0 "e2k_register_operand" "=&r")
	(match_operand:ATM 1 "memory_operand" "+m"))
   (set (match_dup 1)
	(unspec_volatile:ATM [(ATOP:ATM (match_dup 1)
					(match_operand:ATM 2 "e2k_register_operand" "r"))]
			     UNSPECV_ATOMIC))
   (clobber (match_scratch:DI 3 "=&r"))]
  ""
{
  return (E2K_LAT6
	  ? ".accept\tstrict_delay\n1:\n\tnop\t1\n\t{\n\tld<ldsz>,0\t%1, %0, mas = 0x7\n\tnop\t5\n\t}\n\t{\n\t<atop><opsz>,0\t%0, %2, %3\n\t}\n\t{\n\tst<ldsz>,2\t%1, %3, mas = 0x2\n\trbranch\t1b\n\t}\n\t.ignore\tstrict_delay"
	  : ".accept\tstrict_delay\n1:\n\tnop\t1\n\t{\n\tld<ldsz>,0\t%1, %0, mas = 0x7\n\tnop\t4\n\t}\n\t{\n\t<atop><opsz>,0\t%0, %2, %3\n\t}\n\t{\n\tst<ldsz>,2\t%1, %3, mas = 0x2\n\trbranch\t1b\n\t}\n\t.ignore\tstrict_delay");
}
  [(set_attr "type" "raw")])

(define_expand "atomic_exchange<mode>"
  [(match_operand:ATM 0 "e2k_register_operand")
   (match_operand:ATM 1 "memory_operand")
   (match_operand:ATM 2 "e2k_register_operand")
   (match_operand:SI 3 "const_int_operand")]
  ""
{
  rtx mem = e2k_atomic_mem (operands[1]);
  emit_insn (gen_e2k_exchange<mode> (operands[0], mem,
				     force_reg (<MODE>mode, operands[2])));
  DONE;
})

(define_insn "e2k_exchange<mode>"
  [(set (match_operand:ATM 0 "e2k_register_operand" "=&r")
	(match_operand:ATM 1 "memory_operand" "+m"))
   (set (match_dup 1)
	(unspec_volatile:ATM [(match_operand:ATM 2 "e2k_register_operand" "r")]
			     UNSPECV_ATOMIC))]
  ""
{
  return (E2K_LAT6
	  ? ".accept\tstrict_delay\n1:\n\tnop\t1\n\t{\n\tld<ldsz>,0\t%1, %0, mas = 0x7\n\tnop\t2\n\t}\n\t{\n\tst<ldsz>,2\t%1, %2, mas = 0x2\n\trbranch\t1b\n\t}\n\t.ignore\tstrict_delay"
	  : ".accept\tstrict_delay\n1:\n\tnop\t1\n\t{\n\tld<ldsz>,0\t%1, %0, mas = 0x7\n\tnop\t1\n\t}\n\t{\n\tst<ldsz>,2\t%1, %2, mas = 0x2\n\trbranch\t1b\n\t}\n\t.ignore\tstrict_delay");
}
  [(set_attr "type" "raw")])

;; Loads: acquire adds a dummy use that waits for the value; seq_cst also
;; waits for earlier loads and stores first.  Stores: release waits
;; first; seq_cst also waits for the store to complete.
(define_expand "atomic_load<mode>"
  [(match_operand:ATM 0 "e2k_register_operand")
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
   (match_operand:ATM 1 "e2k_register_operand")
   (match_operand:SI 2 "const_int_operand")]
  ""
{
  enum memmodel model = memmodel_from_int (INTVAL (operands[2]));
  if (!is_mm_relaxed (model))
    emit_insn (gen_e2k_atomic_store_rel<mode> (operands[0],
						force_reg (<MODE>mode,
							   operands[1])));
  else
    emit_move_insn (operands[0], force_reg (<MODE>mode, operands[1]));
  if (is_mm_seq_cst (model))
    emit_insn (gen_e2k_wait_st (e2k_barrier_mem ()));
  DONE;
})

;; A release store as lcc writes it (spec/abi/atomics.md): the wait and
;; the store in one wide instruction (13.8 cycles a store back to back,
;; 15.8 in two); on v5 (lcc's 8C2 code) the wait takes v5's sal and sas,
;; after an empty instruction (the E8C2's soft-wait erratum: a nop
;; before sal or lal, spec/isa/hwbugs.md): 6.4 cycles a store.
(define_insn "e2k_atomic_store_rel<mode>"
  [(set (match_operand:ATM 0 "memory_operand" "=m")
	(unspec_volatile:ATM [(match_operand:ATM 1 "e2k_register_operand" "r")]
			     UNSPECV_ATOMIC))]
  ""
  {
    return (e2k_arch == 5
	    ? ".accept\tstrict_delay\n\t{\n\tnop\n\t}\n\t{\n\twait\tld_c = 1, sal = 1, st_c = 1, sas = 1\n\tst<ldsz>\t%0, %1\n\t}\n\t.ignore\tstrict_delay"
	    : ".accept\tstrict_delay\n\t{\n\twait\tld_c = 1, st_c = 1\n\tst<ldsz>\t%0, %1\n\t}\n\t.ignore\tstrict_delay");
  }
  [(set_attr "type" "raw")])

;; 16-byte atomics on v5 and later (spec/abi/atomics.md, "16-byte
;; atomics"), as lcc writes them: ldqp and stqp move the value whole,
;; in one 128-bit register (a DImode scratch here: on v5 every register
;; is 128 bits), which qppackdl builds from the TImode pair and
;; qpswitchd (high half) and a 64-bit read (low half) take apart.  A
;; compare-exchange is the lock-wait loop of the narrower ones with the
;; compare done on both halves (v5: qpcmpeqd, qpswitchd, qpand, qpmerge;
;; v6: qpcmpeqdap into a predicate and qpmrgp); GCC builds exchange and
;; the fetch operations as loops around it, which is lcc's shape too.
;; Functions using them get setwd nfx = 0 (e2k_nfx): a window spill
;; with nfx = 1 loses the high halves (spec/abi/registers.md).  On v3
;; and v4, or with -mno-quad-memory-atomic, they call libatomic.
(define_expand "atomic_compare_and_swapti"
  [(match_operand:SI 0 "e2k_register_operand")	;; bool success
   (match_operand:TI 1 "e2k_register_operand")	;; old value
   (match_operand:TI 2 "memory_operand")	;; memory
   (match_operand:TI 3 "e2k_register_operand")	;; expected
   (match_operand:TI 4 "e2k_register_operand")	;; desired
   (match_operand:SI 5 "const_int_operand")	;; is_weak
   (match_operand:SI 6 "const_int_operand")	;; success model
   (match_operand:SI 7 "const_int_operand")]	;; failure model
  "e2k_arch >= 5 && e2k_quad_atomic"
{
  rtx mem = e2k_atomic_mem (operands[2]);
  rtx old = gen_reg_rtx (TImode);
  rtx ok = gen_reg_rtx (DImode);
  emit_insn (gen_e2k_casti (old, ok, mem, force_reg (TImode, operands[3]),
			    force_reg (TImode, operands[4])));
  emit_move_insn (operands[1], old);
  emit_move_insn (operands[0], gen_lowpart (SImode, ok));
  DONE;
})

(define_insn "e2k_casti"
  [(set (match_operand:TI 0 "e2k_register_operand" "=&r")
	(unspec_volatile:TI [(match_operand:TI 2 "memory_operand" "+m")
			     (match_operand:TI 3 "e2k_register_operand" "r")
			     (match_operand:TI 4 "e2k_register_operand" "r")]
			    UNSPECV_CAS))
   (set (match_dup 2) (unspec_volatile:TI [(const_int 0)] UNSPECV_CAS))
   (set (match_operand:DI 1 "e2k_register_operand" "=&r")
	(unspec_volatile:DI [(const_int 0)] UNSPECV_CAS))
   (clobber (match_scratch:DI 5 "=&r"))
   (clobber (match_scratch:DI 6 "=&r"))
   (clobber (match_scratch:DI 7 "=&r"))
   (clobber (match_scratch:DI 8 "=&r"))
   (clobber (match_scratch:DI 9 "=&r"))
   (clobber (match_scratch:BI 10 "=&j"))]
  "e2k_arch >= 5 && e2k_quad_atomic"
{
  if (e2k_arch >= 6)
    return ".accept\tstrict_delay\n\t{\n\tqppackdl\t%H3, %3, %6\n\tqppackdl\t%H4, %4, %9\n\t}\n1:\n\tnop\t1\n\t{\n\tldqp,0\t%2, %5, mas = 0x7\n\tnop\t7\n\t}\n\t{\n\tqpcmpeqdap,0\t%5, %6, %10\n\t}\n\t{\n\tqpmrgp,0\t%5, %9, %7, %10\n\tmerged,1\t0x0, 0x1, %1, %10\n\t}\n\t{\n\tstqp,2\t%2, %7, mas = 0x2\n\trbranch\t1b\n\t}\n\t{\n\tqpswitchd,0\t%5, %H0\n\taddd,1\t0x0, %5, %0\n\t}\n\t.ignore\tstrict_delay";
  return ".accept\tstrict_delay\n\t{\n\tqppackdl\t%H3, %3, %6\n\tqppackdl\t%H4, %4, %9\n\t}\n1:\n\t{\n\tldqp,0\t%2, %5, mas = 0x7\n\tnop\t2\n\t}\n\t{\n\tqpcmpeqd,0\t%5, %6, %7\n\t}\n\t{\n\tqpswitchd,0\t%7, %8\n\t}\n\t{\n\tqpand,0\t%7, %8, %7\n\t}\n\t{\n\tqpmerge,0\t%5, %9, %7, %7\n\tandd,1\t%7, 0x1, %1\n\tnop\t3\n\t}\n\t{\n\tstqp,2\t%2, %7, mas = 0x2\n\trbranch\t1b\n\t}\n\t{\n\tqpswitchd,0\t%5, %H0\n\taddd,1\t0x0, %5, %0\n\t}\n\t.ignore\tstrict_delay";
}
  [(set_attr "type" "raw")])

;; Loads: ldqp whole; acquire adds the dummy use, seq_cst a wait before.
(define_expand "atomic_loadti"
  [(match_operand:TI 0 "e2k_register_operand")
   (match_operand:TI 1 "memory_operand")
   (match_operand:SI 2 "const_int_operand")]
  "e2k_arch >= 5 && e2k_quad_atomic"
{
  emit_insn (gen_e2k_atomic_loadti (operands[0],
				    e2k_atomic_mem (operands[1]),
				    operands[2]));
  DONE;
})

(define_insn "e2k_atomic_loadti"
  [(set (match_operand:TI 0 "e2k_register_operand" "=&r")
	(unspec_volatile:TI [(match_operand:TI 1 "memory_operand" "m")
			     (match_operand:SI 2 "const_int_operand")]
			    UNSPECV_ATOMIC))
   (clobber (match_scratch:DI 3 "=&r"))]
  "e2k_arch >= 5 && e2k_quad_atomic"
{
  enum memmodel model = memmodel_from_int (INTVAL (operands[2]));
  static char buf[256];
  snprintf (buf, sizeof buf,
	    ".accept\tstrict_delay\n\t{\n\t%sldqp\t%%1, %%3\n\tnop\t%d\n\t}"
	    "%s\n\t{\n\tqpswitchd,0\t%%3, %%H0\n\taddd,1\t0x0, %%3, %%0\n\t}"
	    "\n\t.ignore\tstrict_delay",
	    is_mm_seq_cst (model) ? "wait\tld_c = 1, st_c = 1\n\t" : "",
	    e2k_arch >= 6 ? 4 : 2,
	    is_mm_relaxed (model) ? ""
	    : "\n\t{\n\tadds,s\t%3, 0x0, %%empty\n\t}");
  return buf;
}
  [(set_attr "type" "raw")])

;; Stores: release waits first (on v5 with the soft-wait erratum's empty
;; instruction and sal/sas, as lcc's 8C2 code), seq_cst also after.
(define_expand "atomic_storeti"
  [(match_operand:TI 0 "memory_operand")
   (match_operand:TI 1 "e2k_register_operand")
   (match_operand:SI 2 "const_int_operand")]
  "e2k_arch >= 5 && e2k_quad_atomic"
{
  emit_insn (gen_e2k_atomic_storeti (e2k_atomic_mem (operands[0]),
				     force_reg (TImode, operands[1]),
				     operands[2]));
  DONE;
})

(define_insn "e2k_atomic_storeti"
  [(set (match_operand:TI 0 "memory_operand" "=m")
	(unspec_volatile:TI [(match_operand:TI 1 "e2k_register_operand" "r")
			     (match_operand:SI 2 "const_int_operand")]
			    UNSPECV_ATOMIC))
   (clobber (match_scratch:DI 3 "=&r"))]
  "e2k_arch >= 5 && e2k_quad_atomic"
{
  enum memmodel model = memmodel_from_int (INTVAL (operands[2]));
  static char buf[256];
  const char *body
    = (is_mm_relaxed (model) ? "\n\t{\n\tstqp\t%0, %3\n\t}"
       : e2k_arch == 5
       ? "\n\t{\n\tnop\n\t}\n\t{\n\twait\tld_c = 1, sal = 1, st_c = 1, sas = 1\n\tstqp\t%0, %3\n\t}"
       : "\n\t{\n\twait\tld_c = 1, st_c = 1\n\tstqp\t%0, %3\n\t}");
  snprintf (buf, sizeof buf,
	    ".accept\tstrict_delay\n\t{\n\tqppackdl\t%%H1, %%1, %%3\n\t}%s%s"
	    "\n\t.ignore\tstrict_delay",
	    body,
	    is_mm_seq_cst (model) ? "\n\t{\n\twait\tst_c = 1\n\t}" : "");
  return buf;
}
  [(set_attr "type" "raw")])

(define_insn "e2k_dummy_use"
  [(set (match_operand:BLK 0 "")
	(unspec:BLK [(match_dup 0)
		     (match_operand:SI 1 "e2k_register_operand" "r")] UNSPEC_WAIT))]
  ""
  "adds,sm\t%1, 0x0, %%empty"
  [(set_attr "type" "alu")])

(define_insn "e2k_wait_st"
  [(set (match_operand:BLK 0 "")
	(unspec:BLK [(match_dup 0) (const_int 1)] UNSPEC_WAIT))]
  ""
  "wait\tst_c = 1"
  [(set_attr "type" "wait")])

(include "e2k-vect.md")
