;; 64-bit vectors in the integer registers for the E2K (Elbrus) port.
;; Written by Claude (Anthropic) as an experiment; see README.claude.
;;
;; This file is part of GCC.
;;
;; GCC is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; The packed operations of v1-v4 work on a whole 64-bit register as 8
;; bytes, 4 halfwords, 2 words or 2 floats, lane 0 in the low bits
;; (spec/isa/semantics.md, "Packed operations of v3"; operand order from
;; the community qemu's helper_vec.c, which the 4C and the 8C2 match).
;; The vectors live where everything else does, so moves and logic are
;; the 64-bit integer operations, which issue in all six channels and
;; hand their results on in 1 cycle.  Channels on v3
;; (spec/isa/binutils-ops.yaml): add, subtract, min/max, compares, signs
;; and horizontal adds in ALC0/3 ("pint"); unpacks in ALC1/4 ("pint14");
;; multiplies and psadbw there at 2 cycles ("pmul"); shifts, pshufb and
;; pmerge in ALC0/1/3/4 ("pany"); the float forms as the scalar ones.
;; Integer operations get packed results 4 cycles after their issue
;; (spec/isa/timing.md).

(define_mode_iterator V8 [V8QI V4HI V2SI V2SF])
(define_mode_iterator VI8 [V8QI V4HI V2SI])
(define_mode_iterator VI12 [V8QI V4HI])
(define_mode_iterator VI24 [V4HI V2SI])

(define_mode_attr vs [(V8QI "b") (V4HI "h") (V2SI "w")])
(define_mode_attr velt [(V8QI "QI") (V4HI "HI") (V2SI "SI") (V2SF "SF")])
(define_mode_attr velt_l [(V8QI "qi") (V4HI "hi") (V2SI "si") (V2SF "sf")])
;; Lanes of half the width: what an unpack to MODE widens, what a pack
;; from MODE gives.
(define_mode_attr V_half [(V4HI "V8QI") (V2SI "V4HI")])
(define_mode_attr v_half [(V4HI "v8qi") (V2SI "v4hi")])
(define_mode_attr V_half_s [(V4HI "b") (V2SI "h")])
;; And twice the width.
(define_mode_attr V_wide [(V8QI "V4HI") (V4HI "V2SI")])

;; ---------------------------------------------------------------------
;; Moves

(define_expand "mov<mode>"
  [(set (match_operand:V8 0 "nonimmediate_operand")
	(match_operand:V8 1 "general_operand"))]
  ""
{
  if (MEM_P (operands[0]) && !register_operand (operands[1], <MODE>mode))
    operands[1] = force_reg (<MODE>mode, operands[1]);
})

(define_insn "*mov<mode>_insn"
  [(set (match_operand:V8 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:V8 1 "e2k_move_operand"      "r,i,m,r"))]
  "register_operand (operands[0], <MODE>mode)
   || register_operand (operands[1], <MODE>mode)"
  "@
   addd\t%1, 0x0, %0%?
   addd\t0x0, %1, %0%?
   ldd\t%1, %0%?
   std\t%0, %1%?"
  [(set_attr "type" "alu,alu,load,store")
   (set_attr "predicable" "yes,yes,yes,yes")])

;; ---------------------------------------------------------------------
;; Integer lanes

(define_insn "add<mode>3"
  [(set (match_operand:VI8 0 "e2k_register_operand" "=r")
	(plus:VI8 (match_operand:VI8 1 "e2k_register_operand" "%r")
		  (match_operand:VI8 2 "e2k_register_operand" "r")))]
  ""
  "padd<vs>\t%1, %2, %0"
  [(set_attr "type" "pint")])

(define_insn "sub<mode>3"
  [(set (match_operand:VI8 0 "e2k_register_operand" "=r")
	(minus:VI8 (match_operand:VI8 1 "e2k_register_operand" "r")
		   (match_operand:VI8 2 "e2k_register_operand" "r")))]
  ""
  "psub<vs>\t%1, %2, %0"
  [(set_attr "type" "pint")])

(define_code_iterator SATADD [ss_plus us_plus ss_minus us_minus])
(define_code_attr satop [(ss_plus "padds") (us_plus "paddus")
			 (ss_minus "psubs") (us_minus "psubus")])
(define_code_attr satname [(ss_plus "ssadd") (us_plus "usadd")
			   (ss_minus "sssub") (us_minus "ussub")])

(define_insn "<satname><mode>3"
  [(set (match_operand:VI12 0 "e2k_register_operand" "=r")
	(SATADD:VI12 (match_operand:VI12 1 "e2k_register_operand" "r")
		     (match_operand:VI12 2 "e2k_register_operand" "r")))]
  ""
  "<satop><vs>\t%1, %2, %0"
  [(set_attr "type" "pint")])

(define_code_iterator VMINMAX [smin smax umin umax])
(define_code_attr mmop [(smin "pmins") (smax "pmaxs")
			(umin "pminu") (umax "pmaxu")])

(define_insn "<code><mode>3"
  [(set (match_operand:VI8 0 "e2k_register_operand" "=r")
	(VMINMAX:VI8 (match_operand:VI8 1 "e2k_register_operand" "%r")
		     (match_operand:VI8 2 "e2k_register_operand" "r")))]
  ""
  "<mmop><vs>\t%1, %2, %0"
  [(set_attr "type" "pint")])

(define_insn "mulv4hi3"
  [(set (match_operand:V4HI 0 "e2k_register_operand" "=r")
	(mult:V4HI (match_operand:V4HI 1 "e2k_register_operand" "%r")
		   (match_operand:V4HI 2 "e2k_register_operand" "r")))]
  ""
  "pmullh\t%1, %2, %0"
  [(set_attr "type" "pmul")])

(define_insn "smulv4hi3_highpart"
  [(set (match_operand:V4HI 0 "e2k_register_operand" "=r")
	(smul_highpart:V4HI (match_operand:V4HI 1 "e2k_register_operand" "%r")
			    (match_operand:V4HI 2 "e2k_register_operand" "r")))]
  ""
  "pmulhh\t%1, %2, %0"
  [(set_attr "type" "pmul")])

(define_insn "umulv4hi3_highpart"
  [(set (match_operand:V4HI 0 "e2k_register_operand" "=r")
	(umul_highpart:V4HI (match_operand:V4HI 1 "e2k_register_operand" "%r")
			    (match_operand:V4HI 2 "e2k_register_operand" "r")))]
  ""
  "pmulhuh\t%1, %2, %0"
  [(set_attr "type" "pmul")])

;; v5 multiplies words too.
(define_insn "mulv2si3"
  [(set (match_operand:V2SI 0 "e2k_register_operand" "=r")
	(mult:V2SI (match_operand:V2SI 1 "e2k_register_operand" "%r")
		   (match_operand:V2SI 2 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "pmullw\t%1, %2, %0"
  [(set_attr "type" "pmul")])

;; Logic: the 64-bit integer operations, all lanes alike.
(define_code_iterator VLOGIC [and ior xor])
(define_code_attr vlogop [(and "andd") (ior "ord") (xor "xord")])

(define_insn "<code><mode>3"
  [(set (match_operand:V8 0 "e2k_register_operand" "=r")
	(VLOGIC:V8 (match_operand:V8 1 "e2k_register_operand" "%r")
		   (match_operand:V8 2 "e2k_src2_operand" "ri")))]
  ""
  "<vlogop>\t%1, %2, %0"
  [(set_attr "type" "alu")])

(define_insn "one_cmpl<mode>2"
  [(set (match_operand:VI8 0 "e2k_register_operand" "=r")
	(not:VI8 (match_operand:VI8 1 "e2k_register_operand" "r")))]
  ""
  "xornd\t%1, 0x0, %0"
  [(set_attr "type" "alu")])

;; a & ~b
(define_insn "*andn<mode>3"
  [(set (match_operand:VI8 0 "e2k_register_operand" "=r")
	(and:VI8 (not:VI8 (match_operand:VI8 1 "e2k_register_operand" "r"))
		 (match_operand:VI8 2 "e2k_register_operand" "r")))]
  ""
  "andnd\t%2, %1, %0"
  [(set_attr "type" "alu")])

(define_insn "neg<mode>2"
  [(set (match_operand:VI8 0 "e2k_register_operand" "=r")
	(neg:VI8 (match_operand:VI8 1 "e2k_register_operand" "r")))]
  ""
  "psub<vs>\t0x0, %1, %0"
  [(set_attr "type" "pint")])

;; |x|: psign negates the first operand's lanes where the second's are
;; negative and zeroes them where it is zero.
(define_insn "abs<mode>2"
  [(set (match_operand:VI8 0 "e2k_register_operand" "=r")
	(abs:VI8 (match_operand:VI8 1 "e2k_register_operand" "r")))]
  ""
  "psign<vs>\t%1, %1, %0"
  [(set_attr "type" "pint")])

;; Shifts of every lane by a scalar count.  The hardware reads the whole
;; 64-bit count (past the lane: 0, or the sign), but SHIFT_COUNT_TRUNCATED
;; lets GCC pass a count with garbage above its low bits, as the scalar
;; shifts ignore it: expand_shift_1 hands over the wider register of a
;; lowpart subreg (gcc.dg/vect/pr88903-1.c shifted a V2SI by both of its
;; lanes' counts).  So the count is masked to the lane, and the shifts
;; are unspecs, out of reach of the simplifications that would drop the
;; mask again.  No byte forms.
(define_int_iterator VSHIFTU [UNSPEC_PSLL UNSPEC_PSRL UNSPEC_PSRA])
(define_int_attr vshop [(UNSPEC_PSLL "psll") (UNSPEC_PSRL "psrl")
			(UNSPEC_PSRA "psra")])
(define_int_attr vshname [(UNSPEC_PSLL "ashl") (UNSPEC_PSRL "lshr")
			  (UNSPEC_PSRA "ashr")])

(define_expand "<vshname><mode>3"
  [(set (match_operand:VI24 0 "e2k_register_operand")
	(unspec:VI24 [(match_operand:VI24 1 "e2k_register_operand")
		      (match_operand:DI 2 "e2k_src2_operand")]
		     VSHIFTU))]
  ""
{
  HOST_WIDE_INT mask = GET_MODE_UNIT_BITSIZE (<MODE>mode) - 1;
  if (CONST_INT_P (operands[2]))
    operands[2] = GEN_INT (INTVAL (operands[2]) & mask);
  else
    operands[2] = expand_simple_binop (DImode, AND, operands[2],
				       GEN_INT (mask), NULL_RTX, 1,
				       OPTAB_DIRECT);
})

(define_insn "*<vshname><mode>3_insn"
  [(set (match_operand:VI24 0 "e2k_register_operand" "=r")
	(unspec:VI24 [(match_operand:VI24 1 "e2k_register_operand" "r")
		      (match_operand:DI 2 "e2k_src2_operand" "ri")]
		     VSHIFTU))]
  ""
  "<vshop><vs>\t%1, %2, %0"
  [(set_attr "type" "pany")])

;; ---------------------------------------------------------------------
;; Compares and selects

(define_insn "*eq<mode>3"
  [(set (match_operand:VI8 0 "e2k_register_operand" "=r")
	(eq:VI8 (match_operand:VI8 1 "e2k_register_operand" "%r")
		(match_operand:VI8 2 "e2k_register_operand" "r")))]
  ""
  "pcmpeq<vs>\t%1, %2, %0"
  [(set_attr "type" "pint")])

(define_insn "*gt<mode>3"
  [(set (match_operand:VI8 0 "e2k_register_operand" "=r")
	(gt:VI8 (match_operand:VI8 1 "e2k_reg_or_zero_operand" "rZ")
		(match_operand:VI8 2 "e2k_register_operand" "r")))]
  ""
  "pcmpgt<vs>\t%1, %2, %0"
  [(set_attr "type" "pint")])

(define_expand "vec_cmp<mode><mode>"
  [(set (match_operand:VI8 0 "e2k_register_operand")
	(match_operator:VI8 1 "comparison_operator"
	  [(match_operand:VI8 2 "e2k_register_operand")
	   (match_operand:VI8 3 "e2k_register_operand")]))]
  ""
{
  e2k_expand_vec_cmp (operands[0], GET_CODE (operands[1]), operands[2],
		      operands[3]);
  DONE;
})

(define_expand "vec_cmpu<mode><mode>"
  [(set (match_operand:VI8 0 "e2k_register_operand")
	(match_operator:VI8 1 "comparison_operator"
	  [(match_operand:VI8 2 "e2k_register_operand")
	   (match_operand:VI8 3 "e2k_register_operand")]))]
  ""
{
  e2k_expand_vec_cmp (operands[0], GET_CODE (operands[1]), operands[2],
		      operands[3]);
  DONE;
})

;; pmerge a, b, m: b's byte where m's byte is negative, else a's.
(define_insn "e2k_pmerge<mode>"
  [(set (match_operand:V8 0 "e2k_register_operand" "=r")
	(unspec:V8 [(match_operand:V8 1 "e2k_register_operand" "r")
		    (match_operand:V8 2 "e2k_register_operand" "r")
		    (match_operand:V8 3 "e2k_register_operand" "r")]
		   UNSPEC_PMERGE))]
  ""
  "pmerge\t%1, %2, %3, %0"
  [(set_attr "type" "pany")])

;; An inverted mask swaps the sources.
(define_insn "*e2k_pmerge<mode>_not"
  [(set (match_operand:V8 0 "e2k_register_operand" "=r")
	(unspec:V8 [(match_operand:V8 1 "e2k_register_operand" "r")
		    (match_operand:V8 2 "e2k_register_operand" "r")
		    (not:V8 (match_operand:V8 3 "e2k_register_operand" "r"))]
		   UNSPEC_PMERGE))]
  ""
  "pmerge\t%2, %1, %3, %0"
  [(set_attr "type" "pany")])

;; Operand 3 ? operand 1 : operand 2, lane by lane, for a mask of
;; all-ones or zero lanes.
(define_expand "vcond_mask_<mode><mode>"
  [(match_operand:VI8 0 "e2k_register_operand")
   (match_operand:VI8 1 "e2k_register_operand")
   (match_operand:VI8 2 "e2k_register_operand")
   (match_operand:VI8 3 "e2k_register_operand")]
  ""
{
  emit_insn (gen_e2k_pmerge<mode> (operands[0], operands[2], operands[1],
				   operands[3]));
  DONE;
})

;; ---------------------------------------------------------------------
;; Lanes in and out

;; pshufb a, b, m: byte i is byte m[i] & 7 of a (m[i] bit 3 set) or of
;; b, or a constant (bit 7 set; 0x80: zero).  Bits 4-6 of a selection
;; mean something only on v5, so the port leaves them clear.
(define_insn "e2k_pshufb<mode>"
  [(set (match_operand:V8 0 "e2k_register_operand" "=r")
	(unspec:V8 [(match_operand:V8 1 "e2k_register_operand" "r")
		    (match_operand:V8 2 "e2k_register_operand" "r")
		    (match_operand:DI 3 "e2k_register_operand" "r")]
		   UNSPEC_PSHUFB))]
  ""
  "pshufb\t%1, %2, %3, %0"
  [(set_attr "type" "pany")])

(define_expand "vec_duplicate<mode>"
  [(match_operand:V8 0 "e2k_register_operand")
   (match_operand:<velt> 1 "e2k_register_operand")]
  ""
{
  e2k_expand_vec_duplicate (operands[0], operands[1]);
  DONE;
})

(define_expand "vec_init<mode><velt_l>"
  [(match_operand:V8 0 "e2k_register_operand")
   (match_operand 1 "")]
  ""
{
  e2k_expand_vec_init (operands[0], operands[1]);
  DONE;
})

(define_expand "vec_extract<mode><velt_l>"
  [(match_operand:<velt> 0 "e2k_register_operand")
   (match_operand:V8 1 "e2k_register_operand")
   (match_operand 2 "const_int_operand")]
  ""
{
  e2k_expand_vec_extract (operands[0], operands[1], INTVAL (operands[2]));
  DONE;
})

;; The whole vector shifted towards lane 0 by operand 2 bits (for
;; reductions).
(define_expand "vec_shr_<mode>"
  [(match_operand:V8 0 "e2k_register_operand")
   (match_operand:V8 1 "e2k_register_operand")
   (match_operand:DI 2 "const_int_operand")]
  ""
{
  rtx t = gen_reg_rtx (DImode);
  emit_insn (gen_lshrdi3 (t, gen_lowpart (DImode, operands[1]), operands[2]));
  emit_move_insn (operands[0], gen_lowpart (<MODE>mode, t));
  DONE;
})

;; ---------------------------------------------------------------------
;; Reductions, dot products, sums of differences

;; psadbw a, b: the sum of |a[i] - b[i]| over the unsigned bytes, in the
;; low halfword (the rest zero).
(define_insn "e2k_psadbw"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(unspec:DI [(match_operand:V8QI 1 "e2k_register_operand" "r")
		    (match_operand:V8QI 2 "e2k_reg_or_zero_operand" "rZ")]
		   UNSPEC_PSADBW))]
  ""
  "psadbw\t%1, %2, %0"
  [(set_attr "type" "pmul")])

;; Bytes add up modulo 256 alike, signed or not: their sum of absolute
;; differences against 0, truncated.
(define_expand "reduc_plus_scal_v8qi"
  [(match_operand:QI 0 "e2k_register_operand")
   (match_operand:V8QI 1 "e2k_register_operand")]
  ""
{
  rtx t = gen_reg_rtx (DImode);
  emit_insn (gen_e2k_psadbw (t, operands[1], CONST0_RTX (V8QImode)));
  emit_move_insn (operands[0], gen_lowpart (QImode, t));
  DONE;
})

;; phadd a, b: sums of adjacent lanes, a's in the low half.
(define_insn "e2k_phadd<vs>"
  [(set (match_operand:VI24 0 "e2k_register_operand" "=r")
	(unspec:VI24 [(match_operand:VI24 1 "e2k_register_operand" "r")
		      (match_operand:VI24 2 "e2k_register_operand" "r")]
		     UNSPEC_PHADD))]
  ""
  "phadd<vs>\t%1, %2, %0"
  [(set_attr "type" "pint")])

(define_expand "reduc_plus_scal_<mode>"
  [(match_operand:<velt> 0 "e2k_register_operand")
   (match_operand:VI24 1 "e2k_register_operand")]
  ""
{
  rtx t = gen_reg_rtx (<MODE>mode);
  emit_insn (gen_e2k_phadd<vs> (t, operands[1], operands[1]));
  if (<MODE>mode == V4HImode)
    {
      rtx u = gen_reg_rtx (<MODE>mode);
      emit_insn (gen_e2k_phadd<vs> (u, t, t));
      t = u;
    }
  e2k_expand_vec_extract (operands[0], t, 0);
  DONE;
})

;; pmaddh: x86 pmaddwd, products of adjacent halfwords summed into words.
(define_insn "e2k_pmaddh"
  [(set (match_operand:V2SI 0 "e2k_register_operand" "=r")
	(unspec:V2SI [(match_operand:V4HI 1 "e2k_register_operand" "r")
		      (match_operand:V4HI 2 "e2k_register_operand" "r")]
		     UNSPEC_PMADDH))]
  ""
  "pmaddh\t%1, %2, %0"
  [(set_attr "type" "pmul")])

(define_expand "sdot_prodv2siv4hi"
  [(match_operand:V2SI 0 "e2k_register_operand")
   (match_operand:V4HI 1 "e2k_register_operand")
   (match_operand:V4HI 2 "e2k_register_operand")
   (match_operand:V2SI 3 "e2k_register_operand")]
  ""
{
  rtx t = gen_reg_rtx (V2SImode);
  emit_insn (gen_e2k_pmaddh (t, operands[1], operands[2]));
  emit_insn (gen_addv2si3 (operands[0], t, operands[3]));
  DONE;
})

(define_expand "usadv8qi"
  [(match_operand:V2SI 0 "e2k_register_operand")
   (match_operand:V8QI 1 "e2k_register_operand")
   (match_operand:V8QI 2 "e2k_register_operand")
   (match_operand:V2SI 3 "e2k_register_operand")]
  ""
{
  rtx t = gen_reg_rtx (DImode);
  emit_insn (gen_e2k_psadbw (t, operands[1], operands[2]));
  emit_insn (gen_addv2si3 (operands[0], gen_lowpart (V2SImode, t),
			   operands[3]));
  DONE;
})

;; ---------------------------------------------------------------------
;; Widening and narrowing

;; punpckl/h a, b: the low (high) halves' lanes interleaved, b's at the
;; even positions, so a gives the upper half of each wide lane.
(define_insn "e2k_punpckl<vs>"
  [(set (match_operand:VI24 0 "e2k_register_operand" "=r")
	(unspec:VI24 [(match_operand:<V_half> 1 "e2k_reg_or_zero_operand" "rZ")
		      (match_operand:<V_half> 2 "e2k_register_operand" "r")]
		     UNSPEC_PUNPCKL))]
  ""
  "punpckl<V_half_s><vs>\t%1, %2, %0"
  [(set_attr "type" "pint14")])

(define_insn "e2k_punpckh<vs>"
  [(set (match_operand:VI24 0 "e2k_register_operand" "=r")
	(unspec:VI24 [(match_operand:<V_half> 1 "e2k_reg_or_zero_operand" "rZ")
		      (match_operand:<V_half> 2 "e2k_register_operand" "r")]
		     UNSPEC_PUNPCKH))]
  ""
  "punpckh<V_half_s><vs>\t%1, %2, %0"
  [(set_attr "type" "pint14")])

(define_expand "vec_unpacku_lo_<mode>"
  [(match_operand:<V_wide> 0 "e2k_register_operand")
   (match_operand:VI12 1 "e2k_register_operand")]
  ""
{
  e2k_expand_vec_unpack (operands[0], operands[1], false, false);
  DONE;
})

(define_expand "vec_unpacku_hi_<mode>"
  [(match_operand:<V_wide> 0 "e2k_register_operand")
   (match_operand:VI12 1 "e2k_register_operand")]
  ""
{
  e2k_expand_vec_unpack (operands[0], operands[1], false, true);
  DONE;
})

(define_expand "vec_unpacks_lo_<mode>"
  [(match_operand:<V_wide> 0 "e2k_register_operand")
   (match_operand:VI12 1 "e2k_register_operand")]
  ""
{
  e2k_expand_vec_unpack (operands[0], operands[1], true, false);
  DONE;
})

(define_expand "vec_unpacks_hi_<mode>"
  [(match_operand:<V_wide> 0 "e2k_register_operand")
   (match_operand:VI12 1 "e2k_register_operand")]
  ""
{
  e2k_expand_vec_unpack (operands[0], operands[1], true, true);
  DONE;
})

;; Two vectors' lanes cut to half their width, the first's in the low
;; half: a pshufb of their low bytes.
(define_expand "vec_pack_trunc_<mode>"
  [(match_operand:<V_half> 0 "e2k_register_operand")
   (match_operand:VI24 1 "e2k_register_operand")
   (match_operand:VI24 2 "e2k_register_operand")]
  ""
{
  e2k_expand_vec_pack_trunc (operands[0], operands[1], operands[2]);
  DONE;
})

;; ---------------------------------------------------------------------
;; Float lanes

(define_code_iterator VFOP [plus minus mult])
(define_code_attr vfop [(plus "pfadds") (minus "pfsubs") (mult "pfmuls")])
(define_code_attr vfname [(plus "add") (minus "sub") (mult "mul")])

(define_insn "<vfname>v2sf3"
  [(set (match_operand:V2SF 0 "e2k_register_operand" "=r")
	(VFOP:V2SF (match_operand:V2SF 1 "e2k_register_operand" "r")
		   (match_operand:V2SF 2 "e2k_register_operand" "r")))]
  ""
  "<vfop>\t%1, %2, %0"
  [(set_attr "type" "fp")
   (set_attr "ales" "yes")])

;; Both lanes rounded to integral with roundss' immediate, as the scalar
;; forms (e2k.md, FRINT): pfstoifs, v3+.
(define_insn "<frint>v2sf2"
  [(set (match_operand:V2SF 0 "e2k_register_operand" "=r")
	(unspec:V2SF [(match_operand:V2SF 1 "e2k_register_operand" "r")]
		     FRINT))]
  ""
  "pfstoifs\t<frint_imm>, %1, %0"
  [(set_attr "type" "fcvt")])

;; Sign bits by integer logic, as the scalar forms.
(define_expand "negv2sf2"
  [(match_operand:V2SF 0 "e2k_register_operand")
   (match_operand:V2SF 1 "e2k_register_operand")]
  ""
{
  emit_insn (gen_xordi3 (gen_lowpart (DImode, operands[0]),
			 gen_lowpart (DImode, operands[1]),
			 gen_int_mode (HOST_WIDE_INT_C (0x8000000080000000),
				       DImode)));
  DONE;
})

(define_expand "absv2sf2"
  [(match_operand:V2SF 0 "e2k_register_operand")
   (match_operand:V2SF 1 "e2k_register_operand")]
  ""
{
  emit_insn (gen_anddi3 (gen_lowpart (DImode, operands[0]),
			 gen_lowpart (DImode, operands[1]),
			 gen_int_mode (HOST_WIDE_INT_C (0x7fffffff7fffffff),
				       DImode)));
  DONE;
})

(define_insn "fix_truncv2sfv2si2"
  [(set (match_operand:V2SI 0 "e2k_register_operand" "=r")
	(fix:V2SI (match_operand:V2SF 1 "e2k_register_operand" "r")))]
  ""
  "pfstoistr\t%1, %0"
  [(set_attr "type" "fcvt")])

(define_insn "floatv2siv2sf2"
  [(set (match_operand:V2SF 0 "e2k_register_operand" "=r")
	(float:V2SF (match_operand:V2SI 1 "e2k_register_operand" "r")))]
  ""
  "pistofs\t%1, %0"
  [(set_attr "type" "fcvt")])
;; ---------------------------------------------------------------------
;; 128-bit vectors (v5 and later)
;;
;; From v5 every register holds 128 bits: its extended part is 64 bits,
;; and the qp operations work on all of it (spec/isa/operations-v5.md,
;; "What v5 changes for a compiler"); 64-bit operations read the low
;; half.  So a 16-byte vector mode takes one register here
;; (e2k_hard_regno_nregs), never a pair, and a function holding one
;; runs with setwd nfx = 0, without which a spill of its window loses
;; the high halves (spec/abi/registers.md, "nfx"; e2k_nfx).  Moves and
;; the halves: qpor copies, qppackdl builds a value from two 64-bit ones
;; (high first), qpswitchd swaps the halves, so its low half is the
;; source's high one.  Loads on v5 are two ldd and qppackdl, as lcc's:
;; ldqp is served by L2 (11 cycles; timing.md, "Elbrus-8C2"); v6 loads
;; through L1, and takes ldqp.  Stores take stqp where the address is
;; 16-byte aligned (v5 needs that: SIGBUS), else two std.  Every qp
;; operation has an ALES (spec/isa/reservations.yaml); the channels and
;; latencies are those of the 64-bit operations they widen.

(define_mode_iterator V16 [V16QI V8HI V4SI V2DI V4SF V2DF])
(define_mode_iterator VI16 [V16QI V8HI V4SI V2DI])
(define_mode_iterator VF16 [V4SF V2DF])

(define_mode_attr qvs [(V16QI "b") (V8HI "h") (V4SI "w") (V2DI "d")])
(define_mode_attr qfs [(V4SF "s") (V2DF "d")])
(define_mode_attr qelt [(V16QI "QI") (V8HI "HI") (V4SI "SI") (V2DI "DI")
			(V4SF "SF") (V2DF "DF")])
(define_mode_attr qelt_l [(V16QI "qi") (V8HI "hi") (V4SI "si") (V2DI "di")
			  (V4SF "sf") (V2DF "df")])

(define_expand "mov<mode>"
  [(set (match_operand:V16 0 "nonimmediate_operand")
	(match_operand:V16 1 "general_operand"))]
  "e2k_arch >= 5"
{
  if (e2k_expand_move_v16 (operands))
    DONE;
})

(define_insn "*mov<mode>_v16"
  [(set (match_operand:V16 0 "nonimmediate_operand" "=r,r,r,m")
	(match_operand:V16 1 "e2k_v16_move_operand" "r,Z,m,r"))]
  "e2k_arch >= 5
   && (register_operand (operands[0], <MODE>mode)
       || register_operand (operands[1], <MODE>mode))"
  "@
   qpor\t%1, %1, %0%?
   qppackdl\t0x0, 0x0, %0%?
   ldqp\t%1, %0%?
   stqp\t%0, %1%?"
  [(set_attr "type" "pany,pany,load,store")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

;; An ldqp through two registers, which the 16-byte modes' addresses
;; don't take (e2k_legitimate_address_p keeps them splittable at +8):
;; the prologue's copy of a v5 vector load that a pipelined kernel reads
;; with movaqp (e2k_ms_mark_apb), its halves addressed so.
(define_insn "*e2k_ldqp_rr<mode>"
  [(set (match_operand:V16 0 "e2k_register_operand" "=r")
	(mem:V16 (plus:DI (match_operand:DI 1 "e2k_register_operand" "r")
			  (match_operand:DI 2 "e2k_register_operand" "r"))))]
  "e2k_arch >= 5"
  "ldqp\t%1, %2, %0%?"
  [(set_attr "type" "load")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

;; The halves of a 128-bit value as 64-bit ones, and a 128-bit value
;; from two (operand 1 the high half).
(define_insn "@e2k_qplo<mode>"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(unspec:DI [(match_operand:V16 1 "e2k_register_operand" "r")]
		   UNSPEC_QPLO))]
  "e2k_arch >= 5"
  "addd\t%1, 0x0, %0%?"
  [(set_attr "predicable" "yes")])

(define_insn "@e2k_qphi<mode>"
  [(set (match_operand:DI 0 "e2k_register_operand" "=r")
	(unspec:DI [(match_operand:V16 1 "e2k_register_operand" "r")]
		   UNSPEC_QPHI))]
  "e2k_arch >= 5"
  "qpswitchd\t%1, %0%?"
  [(set_attr "type" "pany")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_insn "@e2k_qppack<mode>"
  [(set (match_operand:V16 0 "e2k_register_operand" "=r")
	(unspec:V16 [(match_operand:DI 1 "e2k_src1_operand" "rI")
		     (match_operand:DI 2 "e2k_src2_operand" "ri")]
		    UNSPEC_QPPACK))]
  "e2k_arch >= 5"
  "qppackdl\t%1, %2, %0%?"
  [(set_attr "type" "pany")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_expand "vec_init<mode><qelt_l>"
  [(match_operand:V16 0 "e2k_register_operand")
   (match_operand 1 "")]
  "e2k_arch >= 5"
{
  e2k_expand_vec_init_v16 (operands[0], operands[1]);
  DONE;
})

(define_expand "vec_extract<mode><qelt_l>"
  [(match_operand:<qelt> 0 "e2k_register_operand")
   (match_operand:V16 1 "e2k_register_operand")
   (match_operand 2 "const_int_operand")]
  "e2k_arch >= 5"
{
  e2k_expand_vec_extract_v16 (operands[0], operands[1], INTVAL (operands[2]));
  DONE;
})

(define_expand "vec_duplicate<mode>"
  [(match_operand:V16 0 "e2k_register_operand")
   (match_operand:<qelt> 1 "e2k_register_operand")]
  "e2k_arch >= 5"
{
  e2k_expand_vec_duplicate_v16 (operands[0], operands[1]);
  DONE;
})

;; Integer lanes: add and subtract in ALC0/3, logic in ALC0/1/3/4.
(define_insn "add<mode>3"
  [(set (match_operand:VI16 0 "e2k_register_operand" "=r")
	(plus:VI16 (match_operand:VI16 1 "e2k_register_operand" "r")
		   (match_operand:VI16 2 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "qpadd<qvs>\t%1, %2, %0%?"
  [(set_attr "type" "pint")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_insn "sub<mode>3"
  [(set (match_operand:VI16 0 "e2k_register_operand" "=r")
	(minus:VI16 (match_operand:VI16 1 "e2k_register_operand" "r")
		    (match_operand:VI16 2 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "qpsub<qvs>\t%1, %2, %0%?"
  [(set_attr "type" "pint")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_code_iterator QLOGIC [and ior xor])
(define_code_attr qlogic [(and "qpand") (ior "qpor") (xor "qpxor")])

(define_insn "<code><mode>3"
  [(set (match_operand:VI16 0 "e2k_register_operand" "=r")
	(QLOGIC:VI16 (match_operand:VI16 1 "e2k_register_operand" "r")
		     (match_operand:VI16 2 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "<qlogic>\t%1, %2, %0%?"
  [(set_attr "type" "pany")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

;; qpandn a, b is a & ~b.
(define_insn "*andn<mode>3_v16"
  [(set (match_operand:VI16 0 "e2k_register_operand" "=r")
	(and:VI16 (not:VI16 (match_operand:VI16 2 "e2k_register_operand" "r"))
		  (match_operand:VI16 1 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "qpandn\t%1, %2, %0%?"
  [(set_attr "type" "pany")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_expand "one_cmpl<mode>2"
  [(set (match_operand:VI16 0 "e2k_register_operand")
	(xor:VI16 (match_operand:VI16 1 "e2k_register_operand")
		  (match_dup 2)))]
  "e2k_arch >= 5"
{
  operands[2] = force_reg (<MODE>mode, CONSTM1_RTX (<MODE>mode));
})

(define_expand "neg<mode>2"
  [(set (match_operand:VI16 0 "e2k_register_operand")
	(minus:VI16 (match_dup 2)
		    (match_operand:VI16 1 "e2k_register_operand")))]
  "e2k_arch >= 5"
{
  operands[2] = force_reg (<MODE>mode, CONST0_RTX (<MODE>mode));
})

;; FP lanes: add, subtract and multiply in all six channels (fp), 4
;; cycles.
(define_code_iterator QFARITH [plus minus mult])
(define_code_attr qfarith [(plus "qpfadd") (minus "qpfsub") (mult "qpfmul")])
(define_code_attr qfop [(plus "add") (minus "sub") (mult "mul")])

(define_insn "<qfop><mode>3"
  [(set (match_operand:VF16 0 "e2k_register_operand" "=r")
	(QFARITH:VF16 (match_operand:VF16 1 "e2k_register_operand" "r")
		      (match_operand:VF16 2 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "<qfarith><qfs>\t%1, %2, %0%?"
  [(set_attr "type" "fp")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

;; Sign bit flips and clears, with the sign mask in a register.
(define_expand "neg<mode>2"
  [(set (match_operand:VF16 0 "e2k_register_operand")
	(neg:VF16 (match_operand:VF16 1 "e2k_register_operand")))]
  "e2k_arch >= 5"
{
  e2k_expand_v16_signop (operands[0], operands[1], false);
  DONE;
})

(define_expand "abs<mode>2"
  [(set (match_operand:VF16 0 "e2k_register_operand")
	(abs:VF16 (match_operand:VF16 1 "e2k_register_operand")))]
  "e2k_arch >= 5"
{
  e2k_expand_v16_signop (operands[0], operands[1], true);
  DONE;
})

;; Sums of all lanes, for the vectorizer's reductions: the halves added
;; as 64-bit values (the 64-bit vector modes' own reduction for more
;; than one lane a half).
(define_expand "reduc_plus_scal_<mode>"
  [(match_operand:<qelt> 0 "e2k_register_operand")
   (match_operand:V16 1 "e2k_register_operand")]
  "e2k_arch >= 5"
{
  e2k_expand_reduc_plus_v16 (operands[0], operands[1]);
  DONE;
})

;; What the vectorizer needs of them (-mvect128, e2k_preferred_simd_mode).

;; Misaligned accesses: on v5 two ldd or std (e2k_expand_move_v16), on
;; v6+ ldqp and stqp at any address (spec/isa/operations-v5.md,
;; "Memory": misaligned ldqp/stqp are SIGBUS on v5, fine on v6).
(define_expand "movmisalign<mode>"
  [(set (match_operand:V16 0 "nonimmediate_operand")
	(match_operand:V16 1 "general_operand"))]
  "e2k_arch >= 5"
{
  if (e2k_expand_move_v16 (operands))
    DONE;
})

(define_mode_iterator VI124_16 [V16QI V8HI V4SI])
(define_mode_iterator VI24_16 [V8HI V4SI])

(define_insn "mulv8hi3"
  [(set (match_operand:V8HI 0 "e2k_register_operand" "=r")
	(mult:V8HI (match_operand:V8HI 1 "e2k_register_operand" "%r")
		   (match_operand:V8HI 2 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "qpmullh\t%1, %2, %0%?"
  [(set_attr "type" "pmul")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_insn "mulv4si3"
  [(set (match_operand:V4SI 0 "e2k_register_operand" "=r")
	(mult:V4SI (match_operand:V4SI 1 "e2k_register_operand" "%r")
		   (match_operand:V4SI 2 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "qpmullw\t%1, %2, %0%?"
  [(set_attr "type" "pmul")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_code_attr qmmop [(smin "qpmins") (smax "qpmaxs")
			 (umin "qpminu") (umax "qpmaxu")])

(define_insn "<code><mode>3"
  [(set (match_operand:VI124_16 0 "e2k_register_operand" "=r")
	(VMINMAX:VI124_16 (match_operand:VI124_16 1 "e2k_register_operand" "%r")
			  (match_operand:VI124_16 2 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "<qmmop><qvs>\t%1, %2, %0%?"
  [(set_attr "type" "pint")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

;; FP min and max are x86's (the second operand when either is a NaN or
;; both are zeros; spec/isa/semantics.md): smin and smax, which GCC
;; uses only where that doesn't matter.  2 cycles.
(define_code_iterator QFMINMAX [smin smax])
(define_code_attr qfmm [(smin "qpfmin") (smax "qpfmax")])

(define_insn "<code><mode>3"
  [(set (match_operand:VF16 0 "e2k_register_operand" "=r")
	(QFMINMAX:VF16 (match_operand:VF16 1 "e2k_register_operand" "r")
		       (match_operand:VF16 2 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "<qfmm><qfs>\t%1, %2, %0%?"
  [(set_attr "type" "fcmp")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

;; Shifts by one count for every lane (counts at or past the lane width
;; give 0, the sign for qpsra: masked to the lane as for the 64-bit
;; ones).  No 64-bit arithmetic right shift before v6.
(define_expand "<vshname><mode>3"
  [(set (match_operand:VI24_16 0 "e2k_register_operand")
	(unspec:VI24_16 [(match_operand:VI24_16 1 "e2k_register_operand")
			 (match_operand:DI 2 "e2k_src2_operand")]
			VSHIFTU))]
  "e2k_arch >= 5"
{
  HOST_WIDE_INT mask = GET_MODE_UNIT_BITSIZE (<MODE>mode) - 1;
  if (CONST_INT_P (operands[2]))
    operands[2] = GEN_INT (INTVAL (operands[2]) & mask);
  else
    operands[2] = expand_simple_binop (DImode, AND, operands[2],
				       GEN_INT (mask), NULL_RTX, 1,
				       OPTAB_DIRECT);
})

(define_insn "*<vshname><mode>3_v16"
  [(set (match_operand:VI24_16 0 "e2k_register_operand" "=r")
	(unspec:VI24_16 [(match_operand:VI24_16 1 "e2k_register_operand" "r")
			 (match_operand:DI 2 "e2k_src2_operand" "ri")]
			VSHIFTU))]
  "e2k_arch >= 5"
  "q<vshop><qvs>\t%1, %2, %0%?"
  [(set_attr "type" "pany")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_int_iterator VSHIFTL [UNSPEC_PSLL UNSPEC_PSRL])

(define_expand "<vshname>v2di3"
  [(set (match_operand:V2DI 0 "e2k_register_operand")
	(unspec:V2DI [(match_operand:V2DI 1 "e2k_register_operand")
		      (match_operand:DI 2 "e2k_src2_operand")]
		     VSHIFTL))]
  "e2k_arch >= 5"
{
  if (CONST_INT_P (operands[2]))
    operands[2] = GEN_INT (INTVAL (operands[2]) & 63);
  else
    operands[2] = expand_simple_binop (DImode, AND, operands[2],
				       GEN_INT (63), NULL_RTX, 1,
				       OPTAB_DIRECT);
})

(define_insn "*<vshname>v2di3_v16"
  [(set (match_operand:V2DI 0 "e2k_register_operand" "=r")
	(unspec:V2DI [(match_operand:V2DI 1 "e2k_register_operand" "r")
		      (match_operand:DI 2 "e2k_src2_operand" "ri")]
		     VSHIFTL))]
  "e2k_arch >= 5"
  "q<vshop>d\t%1, %2, %0%?"
  [(set_attr "type" "pany")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

;; Integer compares: equal and signed greater (ALC0/3); the rest as the
;; 64-bit ones (e2k_expand_vec_cmp).
(define_insn "*eq<mode>3_v16"
  [(set (match_operand:VI16 0 "e2k_register_operand" "=r")
	(eq:VI16 (match_operand:VI16 1 "e2k_register_operand" "%r")
		 (match_operand:VI16 2 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "qpcmpeq<qvs>\t%1, %2, %0%?"
  [(set_attr "type" "pint")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_insn "*gt<mode>3_v16"
  [(set (match_operand:VI16 0 "e2k_register_operand" "=r")
	(gt:VI16 (match_operand:VI16 1 "e2k_register_operand" "r")
		 (match_operand:VI16 2 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "qpcmpgt<qvs>\t%1, %2, %0%?"
  [(set_attr "type" "pint")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_expand "vec_cmp<mode><mode>"
  [(set (match_operand:VI16 0 "e2k_register_operand")
	(match_operator:VI16 1 "comparison_operator"
	  [(match_operand:VI16 2 "e2k_register_operand")
	   (match_operand:VI16 3 "e2k_register_operand")]))]
  "e2k_arch >= 5"
{
  e2k_expand_vec_cmp (operands[0], GET_CODE (operands[1]), operands[2],
		      operands[3]);
  DONE;
})

(define_expand "vec_cmpu<mode><mode>"
  [(set (match_operand:VI16 0 "e2k_register_operand")
	(match_operator:VI16 1 "comparison_operator"
	  [(match_operand:VI16 2 "e2k_register_operand")
	   (match_operand:VI16 3 "e2k_register_operand")]))]
  "e2k_arch >= 5"
{
  e2k_expand_vec_cmp (operands[0], GET_CODE (operands[1]), operands[2],
		      operands[3]);
  DONE;
})

;; FP compares into lane masks: eq, lt, le, uod, neq, nlt, nle, od,
;; quiet for eq, neq, od and uod (spec/isa/operations-v5.md).  Operand 3
;; is the predicate's number, as the operation's suffix.
(define_mode_attr qfmask [(V4SF "V4SI") (V2DF "V2DI")])
(define_mode_attr qfmask_l [(V4SF "v4si") (V2DF "v2di")])

(define_insn "@e2k_qpfcmp<mode>"
  [(set (match_operand:<qfmask> 0 "e2k_register_operand" "=r")
	(unspec:<qfmask> [(match_operand:VF16 1 "e2k_register_operand" "r")
			  (match_operand:VF16 2 "e2k_register_operand" "r")
			  (match_operand 3 "const_int_operand")]
			 UNSPEC_QPFCMP))]
  "e2k_arch >= 5"
  { return e2k_output_qpfcmp (operands, <MODE>mode == V4SFmode); }
  [(set_attr "type" "fcmp")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_expand "vec_cmp<mode><qfmask_l>"
  [(set (match_operand:<qfmask> 0 "e2k_register_operand")
	(match_operator:<qfmask> 1 "comparison_operator"
	  [(match_operand:VF16 2 "e2k_register_operand")
	   (match_operand:VF16 3 "e2k_register_operand")]))]
  "e2k_arch >= 5"
{
  e2k_expand_vec_fcmp_v16 (operands[0], GET_CODE (operands[1]), operands[2],
			   operands[3]);
  DONE;
})

;; qpmerge a, b, m: byte i is b's where m's byte is negative, else a's.
(define_insn "@e2k_qpmerge<mode>"
  [(set (match_operand:V16 0 "e2k_register_operand" "=r")
	(unspec:V16 [(match_operand:V16 1 "e2k_register_operand" "r")
		     (match_operand:V16 2 "e2k_register_operand" "r")
		     (match_operand 3 "e2k_register_operand" "r")]
		    UNSPEC_QPMERGE))]
  "e2k_arch >= 5"
  "qpmerge\t%1, %2, %3, %0%?"
  [(set_attr "type" "pany")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_expand "vcond_mask_<mode><mode>"
  [(match_operand:VI16 0 "e2k_register_operand")
   (match_operand:VI16 1 "e2k_register_operand")
   (match_operand:VI16 2 "e2k_register_operand")
   (match_operand:VI16 3 "e2k_register_operand")]
  "e2k_arch >= 5"
{
  emit_insn (gen_e2k_qpmerge (<MODE>mode, operands[0], operands[2],
			      operands[1], operands[3]));
  DONE;
})

(define_expand "vcond_mask_<mode><qfmask_l>"
  [(match_operand:VF16 0 "e2k_register_operand")
   (match_operand:VF16 1 "e2k_register_operand")
   (match_operand:VF16 2 "e2k_register_operand")
   (match_operand:<qfmask> 3 "e2k_register_operand")]
  "e2k_arch >= 5"
{
  emit_insn (gen_e2k_qpmerge (<MODE>mode, operands[0], operands[2],
			      operands[1], operands[3]));
  DONE;
})

;; Same-width conversions (4 cycles to a consumer of their format).
(define_insn "floatv4siv4sf2"
  [(set (match_operand:V4SF 0 "e2k_register_operand" "=r")
	(float:V4SF (match_operand:V4SI 1 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "qpistofs\t%1, %0%?"
  [(set_attr "type" "fcvt")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_insn "floatv2div2df2"
  [(set (match_operand:V2DF 0 "e2k_register_operand" "=r")
	(float:V2DF (match_operand:V2DI 1 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "qpidtofd\t%1, %0%?"
  [(set_attr "type" "fcvt")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_insn "fix_truncv4sfv4si2"
  [(set (match_operand:V4SI 0 "e2k_register_operand" "=r")
	(fix:V4SI (match_operand:V4SF 1 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "qpfstoistr\t%1, %0%?"
  [(set_attr "type" "fcvt")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

(define_insn "fix_truncv2dfv2di2"
  [(set (match_operand:V2DI 0 "e2k_register_operand" "=r")
	(fix:V2DI (match_operand:V2DF 1 "e2k_register_operand" "r")))]
  "e2k_arch >= 5"
  "qpfdtoidtr\t%1, %0%?"
  [(set_attr "type" "fcvt")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

;; qppermb a, b, c: byte i is byte c[i] & 15 of a (c[i] bit 4 set) or
;; of b; bits 5-7 would invert, reverse or sign-fill it, so the port
;; leaves them clear.  Two-source permutes (e2k_vectorize_vec_perm_const).
(define_insn "@e2k_qppermb<mode>"
  [(set (match_operand:V16 0 "e2k_register_operand" "=r")
	(unspec:V16 [(match_operand:V16 1 "e2k_register_operand" "r")
		     (match_operand:V16 2 "e2k_register_operand" "r")
		     (match_operand:V16QI 3 "e2k_register_operand" "r")]
		    UNSPEC_QPPERMB))]
  "e2k_arch >= 5"
  "qppermb\t%1, %2, %3, %0%?"
  [(set_attr "type" "pany")
   (set_attr "ales" "yes")
   (set_attr "predicable" "yes")])

