import FloatSpec.src.IEEE754.SourceCorrectnessAliases
import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! Regression checks: compatibility correctness names must be exact aliases of
the translated Flocq contracts, never independently inhabitable `Unit` values. -/

example : @binary_add_correct = @Bplus_correct := rfl
example : @binary_mul_correct = @Bmult_correct := rfl

/-! The remaining source contracts are exported under their exact Flocq names;
the older local `binary_*_correct` declarations remain compatibility results. -/

#check @Bminus_correct
#check @Bfma_correct
#check @Bdiv_correct
#check @Bsqrt_correct

/-! The complete FLoCq `Binary` surface is published on the proof-carrying
carrier.  These checks deliberately use the qualified source namespace so a
wider `Binary754` compatibility declaration cannot satisfy the regression. -/

#check @Binary.B2SF_B2BSN
#check @Binary.B2R_B2BSN
#check @Binary.B2SF_FF2B
#check @Binary.FF2SF_B2FF
#check @Binary.B2FF_FF2B
#check @Binary.FF2B_B2FF
#check @Binary.FF2B_B2FF_valid
#check @Binary.B2R_FF2B
#check @Binary.B2R_inj
#check @Binary.B2R_Bsign_inj
#check @Binary.Bcompare_correct
#check @Binary.Bnearbyint_correct
#check @Binary.Btrunc_correct
#check @Binary.Bone_correct
#check @Binary.Bldexp_correct
#check @Binary.Bfrexp_correct
#check @Bulp_correct
#check @Binary.Bsucc_correct
#check @Binary.Bpred_correct
#check @Binary.binary_round_aux_correct
#check @Binary.binary_round_correct
#check @Binary.binary_normalize_correct
#check @Binary.shl_align_fexp_correct
#check @Binary.eq_binary_overflow_FF2SF
#check @Beqb
#check @Beqb_correct
#check @Beqb_refl
#check @Bltb
#check @Bltb_correct
#check @Bleb
#check @Bleb_correct
#check @canonical_canonical_mantissa
#check @generic_format_B2R
#check @FLT_format_B2R
#check @BinarySingleNaN.binary_float
#check @BinarySingleNaN.B2R
#check @BinarySingleNaN.Beqb_correct
#check @BinarySingleNaN.Bltb_correct
#check @BinarySingleNaN.Bleb_correct
#check @BinarySingleNaN.generic_format_B2R
#check @BinarySingleNaN.FLT_format_B2R
#check @BinarySingleNaN.Bopp
#check @BinarySingleNaN.Bopp_involutive
#check @BinarySingleNaN.B2R_Bopp
#check @BinarySingleNaN.is_nan_Bopp
#check @BinarySingleNaN.is_finite_Bopp
#check @BinarySingleNaN.is_finite_strict_Bopp
#check @BinarySingleNaN.Bsign_Bopp
#check @BinarySingleNaN.Bmult
#check @BinarySingleNaN.Bmult_correct
#check @BinarySingleNaN.Bplus
#check @BinarySingleNaN.Bplus_correct
#check @BinarySingleNaN.Bminus
#check @BinarySingleNaN.Bminus_correct
#check @BinarySingleNaN.Bfma
#check @BinarySingleNaN.Bfma_correct
#check @BinarySingleNaN.Bdiv
#check @BinarySingleNaN.Bdiv_correct
#check @BinarySingleNaN.Bsqrt
#check @BinarySingleNaN.Bsqrt_correct_aux
#check @BinarySingleNaN.Bsqrt_correct
#check @BinarySingleNaN.erase
#check @BinarySingleNaN.erase_correct
#check @BinarySingleNaN.Babs
#check @BinarySingleNaN.B2R_Babs
#check @BinarySingleNaN.Bcompare
#check @BinarySingleNaN.Bcompare_correct
#check @BinarySingleNaN.bounded_le_emax_minus_prec
#check @BinarySingleNaN.abs_B2R_lt_emax
#check @BinarySingleNaN.binary_round_aux
#check @BinarySingleNaN.binary_round_aux_correct'
#check @BinarySingleNaN.binary_round_aux_correct
#check @BinarySingleNaN.binary_round
#check @BinarySingleNaN.binary_round_correct
#check @BinarySingleNaN.is_nan_binary_round
#check @BinarySingleNaN.binary_normalize
#check @BinarySingleNaN.binary_normalize_correct
#check @BinarySingleNaN.Bnearbyint
#check @BinarySingleNaN.Bnearbyint_correct
#check @BinarySingleNaN.Bnearbyint_correct_aux
#check @BinarySingleNaN.sign_plus_overflow
#check @BinarySingleNaN.Btrunc
#check @BinarySingleNaN.Btrunc_correct
#check @BinarySingleNaN.Bone
#check @BinarySingleNaN.Bone_correct
#check @BinarySingleNaN.Bmax_float
#check @BinarySingleNaN.Bnormfr_mantissa
#check @BinarySingleNaN.Bldexp
#check @BinarySingleNaN.Bldexp_correct
#check @BinarySingleNaN.Bfrexp
#check @BinarySingleNaN.Bfrexp_correct

example :
    @BinarySingleNaN.Bfrexp 1 1 ⟨by omega⟩
        (BinarySingleNaNFloat.B754_zero false) =
      (BinarySingleNaNFloat.B754_zero false, -3) := by
  rfl

example :
    @BinarySingleNaN.Bnearbyint 0 1 ⟨by omega⟩ RoundingMode.RNE
        (BinarySingleNaNFloat.B754_zero false) =
      BinarySingleNaNFloat.B754_zero false := by
  rfl

example :
    is_nan_SF (@BinarySingleNaN.binary_overflow 0 0 RoundingMode.RNE false) = false :=
  @BinarySingleNaN.is_nan_binary_overflow 0 0 RoundingMode.RNE false
#check @BinarySingleNaN.Bulp
#check @BinarySingleNaN.Bulp_correct
#check @BinarySingleNaN.Bulp'
#check @BinarySingleNaN.Bulp'_correct
#check @BinarySingleNaN.Bsucc
#check @BinarySingleNaN.Bsucc_correct
#check @BinarySingleNaN.Bpred
#check @BinarySingleNaN.Bpred_correct
#check @BinarySingleNaN.Bpred_pos'
#check @BinarySingleNaN.Bpred_pos'_correct
#check @BinarySingleNaN.Bsucc'
#check @BinarySingleNaN.Bsucc'_correct

/-- `Binary.B2FF` preserves the sign and payload of a source-valid NaN. -/
example (prec emax : Int) (p : FloatSpec.Core.Zaux.Positive)
    (hp : nan_pl prec p = true) :
    Binary.B2FF (prec := prec) (emax := emax)
        (binary_float.B754_nan true p hp) =
      FullFloat.F754_nan true (FloatSpec.Core.Zaux.positiveToNat p) := rfl

/-- Source `Bopp` and `Babs` must invoke the supplied NaN handler. -/
example (prec emax : Int) (p : FloatSpec.Core.Zaux.Positive)
    (hp : nan_pl prec p = true) :
    let nan := binary_float.B754_nan (prec:=prec) (emax:=emax) true p hp
    let choosePositive : Binary.BoppNaNHandler prec emax := fun _ =>
      ⟨binary_float.B754_nan false p hp, rfl⟩
    Binary.Bopp choosePositive nan = binary_float.B754_nan false p hp := rfl

example (prec emax : Int) (p : FloatSpec.Core.Zaux.Positive)
    (hp : nan_pl prec p = true) :
    let source := full_float.F754_nan true p
    Binary.B2FF_exact (Binary.FF2B (prec:=prec) (emax:=emax) source hp) = source := rfl

/-! Overflow is part of the observable source semantics.  These examples guard
the finite RTZ branch and both directions of sign-sensitive rounding. -/

example : binary_overflow 3 10 RoundingMode.RTZ false =
    FullFloat.F754_finite false 7 7 := rfl
example : binary_overflow 3 10 RoundingMode.RNE true =
    FullFloat.F754_infinity true := rfl
example : binary_overflow 3 10 RoundingMode.RTP false =
    FullFloat.F754_infinity false := rfl
example : binary_overflow 3 10 RoundingMode.RTP true =
    FullFloat.F754_finite true 7 7 := rfl
example : binary_overflow 3 10 RoundingMode.RTN false =
    FullFloat.F754_finite false 7 7 := rfl
example : binary_overflow 3 10 RoundingMode.RTN true =
    FullFloat.F754_infinity true := rfl

/-! The exact SingleNaN sign theorem includes the NaN case, matching the
source theorem's unrestricted quantification. -/

example {prec emax : Int} :
    BinarySingleNaN.Bsign
        (@BinarySingleNaN.SF2B prec emax StandardFloat.S754_nan rfl) =
      sign_SF StandardFloat.S754_nan :=
  @BinarySingleNaN.Bsign_SF2B prec emax StandardFloat.S754_nan rfl

/-! Coq's `comparison` is represented by `Ordering`; NaN remains unordered,
and the old integer implementation is connected by checked -1/0/1 cases. -/

example : BinarySingleNaN.orderingOfCompareCode (-1) = Ordering.lt := by simp
example : BinarySingleNaN.orderingOfCompareCode 0 = Ordering.eq := by simp
example : BinarySingleNaN.orderingOfCompareCode 1 = Ordering.gt := by simp

example :
    @BinarySingleNaN.Bcompare 1 1 BinarySingleNaNFloat.B754_nan
      (BinarySingleNaNFloat.B754_zero false) = none := by
  rfl

/-! These function-type checks fail if an internal `Valid_exp` or
`Monotone_exp` proof leaks into the source-facing arithmetic signatures. -/

noncomputable section

namespace FloatSpec.IEEE754.BinarySingleNaN.Source

example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    mode → _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax :=
  @Bmult prec emax _ _

example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    mode → _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax :=
  @Bplus prec emax _ _

example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    mode → _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax :=
  @Bminus prec emax _ _

example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    mode → _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax :=
  @Bfma prec emax _ _

example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    mode → _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax :=
  @Bdiv prec emax _ _

example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    mode → _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax :=
  @Bsqrt prec emax _ _

#check @Bmult_correct
#check @Bplus_correct
#check @Bminus_correct
#check @Bfma_correct
#check @Bdiv_correct
#check @Bsqrt_correct_aux
#check @Bsqrt_correct

end FloatSpec.IEEE754.BinarySingleNaN.Source

end
