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
  [(set_attr "type" "fp")])

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
