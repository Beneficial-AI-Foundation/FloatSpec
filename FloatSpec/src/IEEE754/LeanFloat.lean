import FloatSpec.src.IEEE754.PrimFloat

/-! Compatibility names for the native adapters now owned by the source modules. -/

namespace FloatSpec.IEEE754.LeanFloat

open Float.Model

abbrev unpackedOfStandardFloat :=
  FloatSpec.IEEE754.Native.unpackedOfStandardFloat

abbrev standardFloatOfUnpacked :=
  FloatSpec.IEEE754.Native.standardFloatOfUnpacked

theorem standardFloatOfUnpacked_unpackedOfStandardFloat
    (x : StandardFloat)
    (hvalid : match x with | .S754_finite _ m _ => 0 < m | _ => True) :
    standardFloatOfUnpacked (unpackedOfStandardFloat x) = x :=
  FloatSpec.IEEE754.Native.standardFloatOfUnpacked_unpackedOfStandardFloat x hvalid

@[simp] theorem unpackedOfStandardFloat_standardFloatOfUnpacked
    (x : UnpackedFloat) :
    unpackedOfStandardFloat (standardFloatOfUnpacked x) = x :=
  FloatSpec.IEEE754.Native.unpackedOfStandardFloat_standardFloatOfUnpacked x

abbrev model64OfStandardFloat :=
  FloatSpec.IEEE754.Native.model64OfStandardFloat

abbrev model32OfStandardFloat :=
  FloatSpec.IEEE754.Native.model32OfStandardFloat

abbrev standardFloatOfModel64 :=
  FloatSpec.IEEE754.Native.standardFloatOfModel64

abbrev standardFloatOfModel32 :=
  FloatSpec.IEEE754.Native.standardFloatOfModel32

abbrev model64OfBinarySingleNaNFloat :=
  FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat

abbrev model32OfBinarySingleNaNFloat :=
  FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat

theorem model64OfStandardFloat_binaryRoundAux
    (s : Bool) (m : Nat) (e : Int) (l : Loc) (hm : 0 < m) :
    model64OfStandardFloat
        (binary_round_aux (prec := 53) (emax := 1024) RoundingMode.RNE s m e l) =
      Float.Model.pack
        (UnpackedFloat.roundWithAccuracy Format.binary64
          (FloatSpec.IEEE754.Native.modelSignOfBool s) m e
          (FloatSpec.IEEE754.Native.accuracyOfLocation l)) :=
  FloatSpec.IEEE754.Native.model64OfStandardFloat_binaryRoundAux s m e l hm

theorem model32OfStandardFloat_binaryRoundAux
    (s : Bool) (m : Nat) (e : Int) (l : Loc) (hm : 0 < m) :
    model32OfStandardFloat
        (binary_round_aux (prec := 24) (emax := 128) RoundingMode.RNE s m e l) =
      Float32.Model.pack
        (UnpackedFloat.roundWithAccuracy Format.binary32
          (FloatSpec.IEEE754.Native.modelSignOfBool s) m e
          (FloatSpec.IEEE754.Native.accuracyOfLocation l)) :=
  FloatSpec.IEEE754.Native.model32OfStandardFloat_binaryRoundAux s m e l hm

private theorem unpack_model64OfBinarySingleNaNFloat
    (x : BinarySingleNaNFloat 53 1024) :
    (model64OfBinarySingleNaNFloat x).unpack =
      FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat x := by
  have h := congrArg FloatSpec.IEEE754.Native.unpackedOfStandardFloat
    (FloatSpec.IEEE754.Native.standardFloatOfModel64_model64OfStandardFloat
      (binarySingleNaNFloatToStandardFloat x)
      (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat x))
  simpa [FloatSpec.IEEE754.Native.standardFloatOfModel64,
    FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat,
    FloatSpec.IEEE754.Native.unpackedOfStandardFloat_binarySingleNaNFloatToStandardFloat]
    using h

private theorem unpack_model32OfBinarySingleNaNFloat
    (x : BinarySingleNaNFloat 24 128) :
    (model32OfBinarySingleNaNFloat x).unpack =
      FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat x := by
  have h := congrArg FloatSpec.IEEE754.Native.unpackedOfStandardFloat
    (FloatSpec.IEEE754.Native.standardFloatOfModel32_model32OfStandardFloat
      (binarySingleNaNFloatToStandardFloat x)
      (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat x))
  simpa [FloatSpec.IEEE754.Native.standardFloatOfModel32,
    FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat_eq_model32OfStandardFloat,
    FloatSpec.IEEE754.Native.unpackedOfStandardFloat_binarySingleNaNFloatToStandardFloat]
    using h

private theorem positiveFiniteValue_lt_of_exp_lt
    {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mx my : Nat) (ex ey : Int)
    (hmx : 0 < mx) (hmy : 0 < my)
    (hx : specFloat_bounded (prec := prec) (emax := emax) mx ex = true)
    (hy : specFloat_bounded (prec := prec) (emax := emax) my ey = true)
    (he : ex < ey) :
    SF2R 2 (StandardFloat.S754_finite false mx ex) <
      SF2R 2 (StandardFloat.S754_finite false my ey) := by
  let fexp := FLT_exp (3 - emax - prec) prec
  let hvalid : FloatSpec.Core.Generic_fmt.Valid_exp fexp :=
    @FloatSpec.Core.FLT.FLT_exp_valid prec (3 - emax - prec) (inferInstance)
  let hmono : FloatSpec.Core.Generic_fmt.Monotone_exp fexp :=
    FloatSpec.Core.FLT.FLT_exp_monotone prec (3 - emax - prec)
  let fx : FloatSpec.Core.Defs.FlocqFloat 2 := ⟨mx, ex⟩
  let fy : FloatSpec.Core.Defs.FlocqFloat 2 := ⟨my, ey⟩
  have hcxTrip := canonical_bounded_of_specFloat_bounded
    (prec := prec) (emax := emax) false mx ex hmx hx
  have hcyTrip := canonical_bounded_of_specFloat_bounded
    (prec := prec) (emax := emax) false my ey hmy hy
  have hcx : FloatSpec.Core.Generic_fmt.canonical 2 fexp fx := by
    simpa [fexp, fx, Std.Do.wp, Std.Do.PostCond.noThrow, pure] using hcxTrip trivial
  have hcy : FloatSpec.Core.Generic_fmt.canonical 2 fexp fy := by
    simpa [fexp, fy, Std.Do.wp, Std.Do.PostCond.noThrow, pure] using hcyTrip trivial
  have hcex : FloatSpec.Core.Generic_fmt.cexp 2 fexp (F2R fx) = ex := by
    simpa [FloatSpec.Core.Generic_fmt.cexp, fexp, fx] using hcx.symm
  have hcey : FloatSpec.Core.Generic_fmt.cexp 2 fexp (F2R fy) = ey := by
    simpa [FloatSpec.Core.Generic_fmt.cexp, fexp, fy] using hcy.symm
  have hfy : 0 < F2R fy := by
    simp [fy, F2R, FloatSpec.Core.Defs.F2R]
    positivity
  have hcexpLt :
      FloatSpec.Core.Generic_fmt.cexp 2 fexp (F2R fx) <
        FloatSpec.Core.Generic_fmt.cexp 2 fexp (F2R fy) := by
    rw [hcex, hcey]
    exact he
  have hlt := @FloatSpec.Core.Generic_fmt.lt_cexp_pos 2 (inferInstance) fexp
    hvalid hmono (F2R fx) (F2R fy) (by norm_num) hfy hcexpLt
  simpa [SF2R, fx, fy] using hlt

private theorem positiveFiniteValue_lt_of_mantissa_lt
    (mx my : Nat) (e : Int) (hm : mx < my) :
    SF2R 2 (StandardFloat.S754_finite false mx e) <
      SF2R 2 (StandardFloat.S754_finite false my e) := by
  simp [SF2R, F2R, FloatSpec.Core.Defs.F2R]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hm) (zpow_pos (by norm_num) e)

private theorem positiveFiniteValue_pos (m : Nat) (e : Int) (hm : 0 < m) :
    0 < SF2R 2 (StandardFloat.S754_finite false m e) := by
  simp [SF2R, F2R, FloatSpec.Core.Defs.F2R]
  positivity

private theorem positiveFiniteCompare_eq_SFcompare
    {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mx my : Nat) (ex ey : Int)
    (hmx : 0 < mx) (hmy : 0 < my)
    (hx : specFloat_bounded (prec := prec) (emax := emax) mx ex = true)
    (hy : specFloat_bounded (prec := prec) (emax := emax) my ey = true) :
    some ((compare ex ey).then (compare mx my)) =
      FaithfulPrimFloat.SFcompare
        (StandardFloat.S754_finite false mx ex)
        (StandardFloat.S754_finite false my ey) := by
  rcases lt_trichotomy ex ey with he | he | he
  · have hxy := positiveFiniteValue_lt_of_exp_lt mx my ex ey hmx hmy hx hy he
    have hyx : ¬SF2R 2 (StandardFloat.S754_finite false my ey) <
        SF2R 2 (StandardFloat.S754_finite false mx ex) := not_lt_of_ge hxy.le
    rw [Int.compare_eq_lt.mpr he]
    simp [FaithfulPrimFloat.SFcompare, FaithfulPrimFloat.SFltb, hxy]
  · subst ey
    rw [Int.compare_eq_eq.mpr rfl]
    rcases lt_trichotomy mx my with hm | hm | hm
    · have hxy := positiveFiniteValue_lt_of_mantissa_lt mx my ex hm
      have hyx : ¬SF2R 2 (StandardFloat.S754_finite false my ex) <
          SF2R 2 (StandardFloat.S754_finite false mx ex) := not_lt_of_ge hxy.le
      rw [Nat.compare_eq_lt.mpr hm]
      simp [FaithfulPrimFloat.SFcompare, FaithfulPrimFloat.SFltb, hxy]
    · subst my
      rw [Nat.compare_eq_eq.mpr rfl]
      simp [FaithfulPrimFloat.SFcompare, FaithfulPrimFloat.SFltb]
    · have hyx := positiveFiniteValue_lt_of_mantissa_lt my mx ex hm
      have hxy : ¬SF2R 2 (StandardFloat.S754_finite false mx ex) <
          SF2R 2 (StandardFloat.S754_finite false my ex) := not_lt_of_ge hyx.le
      rw [Nat.compare_eq_gt.mpr hm]
      simp [FaithfulPrimFloat.SFcompare, FaithfulPrimFloat.SFltb, hxy, hyx]
  · have hyx := positiveFiniteValue_lt_of_exp_lt my mx ey ex hmy hmx hy hx he
    have hxy : ¬SF2R 2 (StandardFloat.S754_finite false mx ex) <
        SF2R 2 (StandardFloat.S754_finite false my ey) := not_lt_of_ge hyx.le
    rw [Int.compare_eq_gt.mpr he]
    simp [FaithfulPrimFloat.SFcompare, FaithfulPrimFloat.SFltb, hxy, hyx]

private theorem unpackedCompare_eq_SFcompare
    {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x y : BinarySingleNaNFloat prec emax) :
    (FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat x).compare
        (FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat y) =
      FaithfulPrimFloat.SFcompare
        (binarySingleNaNFloatToStandardFloat x)
        (binarySingleNaNFloatToStandardFloat y) := by
  cases x with
  | B754_nan => cases y <;> rfl
  | B754_zero sx =>
      cases y with
      | B754_nan => rfl
      | B754_zero sy =>
          have hx0 : SF2R 2 (StandardFloat.S754_zero sx) = 0 := rfl
          have hy0 : SF2R 2 (StandardFloat.S754_zero sy) = 0 := rfl
          cases sx <;> cases sy <;>
            simp [FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat,
              binarySingleNaNFloatToStandardFloat, FaithfulPrimFloat.SFcompare,
              FaithfulPrimFloat.SFltb,
              FloatSpec.IEEE754.Native.modelSignOfBool,
              Float.Model.UnpackedFloat.compare, hx0, hy0]
      | B754_infinity sy => cases sx <;> cases sy <;> rfl
      | B754_finite sy m e hm hb =>
          have hp := positiveFiniteValue_pos m e hm
          simp [SF2R, F2R, FloatSpec.Core.Defs.F2R] at hp
          cases sx <;> cases sy <;>
            simp [FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat,
              binarySingleNaNFloatToStandardFloat, FaithfulPrimFloat.SFcompare,
              FaithfulPrimFloat.SFltb, SF2R, F2R, FloatSpec.Core.Defs.F2R,
              FloatSpec.IEEE754.Native.modelSignOfBool,
              Float.Model.UnpackedFloat.compare, hp,
              not_lt_of_ge hp.le]
  | B754_infinity sx =>
      cases y with
      | B754_nan => rfl
      | B754_zero sy => cases sx <;> cases sy <;> rfl
      | B754_infinity sy => cases sx <;> cases sy <;> rfl
      | B754_finite sy m e hm hb => cases sx <;> cases sy <;> rfl
  | B754_finite sx mx ex hmx hx =>
      cases y with
      | B754_nan => rfl
      | B754_zero sy =>
          have hp := positiveFiniteValue_pos mx ex hmx
          simp [SF2R, F2R, FloatSpec.Core.Defs.F2R] at hp
          cases sx <;> cases sy <;>
            simp [FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat,
              binarySingleNaNFloatToStandardFloat, FaithfulPrimFloat.SFcompare,
              FaithfulPrimFloat.SFltb, SF2R, F2R, FloatSpec.Core.Defs.F2R,
              FloatSpec.IEEE754.Native.modelSignOfBool,
              Float.Model.UnpackedFloat.compare, hp,
              not_lt_of_ge hp.le]
      | B754_infinity sy => cases sx <;> cases sy <;> rfl
      | B754_finite sy my ey hmy hy =>
          cases sx <;> cases sy
          · simpa [FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat,
              binarySingleNaNFloatToStandardFloat,
              FloatSpec.IEEE754.Native.modelSignOfBool,
              Float.Model.UnpackedFloat.compare] using
                positiveFiniteCompare_eq_SFcompare mx my ex ey hmx hmy hx hy
          · have hpx := positiveFiniteValue_pos mx ex hmx
            have hpy := positiveFiniteValue_pos my ey hmy
            have hxy : ¬ SF2R 2 (StandardFloat.S754_finite false mx ex) <
                -SF2R 2 (StandardFloat.S754_finite false my ey) := by
              linarith
            have hyx : -SF2R 2 (StandardFloat.S754_finite false my ey) <
                SF2R 2 (StandardFloat.S754_finite false mx ex) := by
              linarith
            simp [SF2R, F2R, FloatSpec.Core.Defs.F2R] at hxy hyx hpx hpy
            simp [FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat,
              binarySingleNaNFloatToStandardFloat, FaithfulPrimFloat.SFcompare,
              FaithfulPrimFloat.SFltb, SF2R, F2R, FloatSpec.Core.Defs.F2R,
              FloatSpec.IEEE754.Native.modelSignOfBool,
              Float.Model.UnpackedFloat.compare, hxy, hyx]
          · have hpx := positiveFiniteValue_pos mx ex hmx
            have hpy := positiveFiniteValue_pos my ey hmy
            have hxy : -SF2R 2 (StandardFloat.S754_finite false mx ex) <
                SF2R 2 (StandardFloat.S754_finite false my ey) := by
              linarith
            have hyx : ¬ SF2R 2 (StandardFloat.S754_finite false my ey) <
                -SF2R 2 (StandardFloat.S754_finite false mx ex) := by
              linarith
            simp [SF2R, F2R, FloatSpec.Core.Defs.F2R] at hxy hyx hpx hpy
            simp [FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat,
              binarySingleNaNFloatToStandardFloat, FaithfulPrimFloat.SFcompare,
              FaithfulPrimFloat.SFltb, SF2R, F2R, FloatSpec.Core.Defs.F2R,
              FloatSpec.IEEE754.Native.modelSignOfBool,
              Float.Model.UnpackedFloat.compare, hxy]
          · have h := positiveFiniteCompare_eq_SFcompare
                my mx ey ex hmy hmx hy hx
            have hswap :
                ((compare ex ey).then (compare mx my)).swap =
                  (compare ey ex).then (compare my mx) := by
              rw [Ordering.swap_then, Int.compare_swap, Nat.compare_swap]
            change some (((compare ex ey).then (compare mx my)).swap) = _
            rw [hswap]
            simpa [FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat,
              binarySingleNaNFloatToStandardFloat, FaithfulPrimFloat.SFcompare,
              FaithfulPrimFloat.SFltb, SF2R, F2R, FloatSpec.Core.Defs.F2R,
              FloatSpec.IEEE754.Native.modelSignOfBool,
              Float.Model.UnpackedFloat.compare] using h

theorem model64OfBinarySingleNaNFloat_compare
    (x y : BinarySingleNaNFloat 53 1024) :
    Float.Model.compare (model64OfBinarySingleNaNFloat x)
        (model64OfBinarySingleNaNFloat y) =
      FaithfulPrimFloat.SFcompare
        (binarySingleNaNFloatToStandardFloat x)
        (binarySingleNaNFloatToStandardFloat y) := by
  unfold Float.Model.compare
  rw [unpack_model64OfBinarySingleNaNFloat, unpack_model64OfBinarySingleNaNFloat]
  exact @unpackedCompare_eq_SFcompare 53 1024
    ⟨by norm_num⟩ ⟨by norm_num⟩ x y

theorem model32OfBinarySingleNaNFloat_compare
    (x y : BinarySingleNaNFloat 24 128) :
    Float32.Model.compare (model32OfBinarySingleNaNFloat x)
        (model32OfBinarySingleNaNFloat y) =
      FaithfulPrimFloat.SFcompare
        (binarySingleNaNFloatToStandardFloat x)
        (binarySingleNaNFloatToStandardFloat y) := by
  unfold Float32.Model.compare
  rw [unpack_model32OfBinarySingleNaNFloat, unpack_model32OfBinarySingleNaNFloat]
  exact @unpackedCompare_eq_SFcompare 24 128
    ⟨by norm_num⟩ ⟨by norm_num⟩ x y

theorem model64OfBinarySingleNaNFloat_Bmult_RNE
    (x y : BinarySingleNaNFloat 53 1024) :
    model64OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bmult 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float.Model.mul (model64OfBinarySingleNaNFloat x)
        (model64OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bmult 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bmult_RNE]
  unfold Float.Model.mul
  rw [unpack_model64OfBinarySingleNaNFloat, unpack_model64OfBinarySingleNaNFloat]

theorem model32OfBinarySingleNaNFloat_Bmult_RNE
    (x y : BinarySingleNaNFloat 24 128) :
    model32OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bmult 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float32.Model.mul (model32OfBinarySingleNaNFloat x)
        (model32OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bmult 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat_Bmult_RNE]
  unfold Float32.Model.mul
  rw [unpack_model32OfBinarySingleNaNFloat, unpack_model32OfBinarySingleNaNFloat]

theorem model64OfBinarySingleNaNFloat_Bplus_RNE
    (x y : BinarySingleNaNFloat 53 1024) :
    model64OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bplus 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float.Model.add (model64OfBinarySingleNaNFloat x)
        (model64OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bplus 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bplus_RNE]
  unfold Float.Model.add
  rw [unpack_model64OfBinarySingleNaNFloat, unpack_model64OfBinarySingleNaNFloat]

theorem model32OfBinarySingleNaNFloat_Bplus_RNE
    (x y : BinarySingleNaNFloat 24 128) :
    model32OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bplus 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float32.Model.add (model32OfBinarySingleNaNFloat x)
        (model32OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bplus 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat_Bplus_RNE]
  unfold Float32.Model.add
  rw [unpack_model32OfBinarySingleNaNFloat, unpack_model32OfBinarySingleNaNFloat]

theorem model64OfBinarySingleNaNFloat_Bminus_RNE
    (x y : BinarySingleNaNFloat 53 1024) :
    model64OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bminus 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float.Model.sub (model64OfBinarySingleNaNFloat x)
        (model64OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bminus 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bminus_RNE]
  unfold Float.Model.sub
  rw [unpack_model64OfBinarySingleNaNFloat, unpack_model64OfBinarySingleNaNFloat]

theorem model32OfBinarySingleNaNFloat_Bminus_RNE
    (x y : BinarySingleNaNFloat 24 128) :
    model32OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bminus 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float32.Model.sub (model32OfBinarySingleNaNFloat x)
        (model32OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bminus 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat_Bminus_RNE]
  unfold Float32.Model.sub
  rw [unpack_model32OfBinarySingleNaNFloat, unpack_model32OfBinarySingleNaNFloat]

theorem model64OfBinarySingleNaNFloat_Bsqrt_RNE
    (x : BinarySingleNaNFloat 53 1024) :
    model64OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bsqrt 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x) =
      Float.Model.sqrt (model64OfBinarySingleNaNFloat x) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bsqrt 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x) = _
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bsqrt_RNE]
  unfold Float.Model.sqrt
  rw [unpack_model64OfBinarySingleNaNFloat]

theorem model32OfBinarySingleNaNFloat_Bsqrt_RNE
    (x : BinarySingleNaNFloat 24 128) :
    model32OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bsqrt 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x) =
      Float32.Model.sqrt (model32OfBinarySingleNaNFloat x) := by
  change FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bsqrt 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x) = _
  rw [FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat_Bsqrt_RNE]
  unfold Float32.Model.sqrt
  rw [unpack_model32OfBinarySingleNaNFloat]

theorem model64OfBinarySingleNaNFloat_Bdiv_RNE
    (x y : BinarySingleNaNFloat 53 1024) :
    model64OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bdiv 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float.Model.div (model64OfBinarySingleNaNFloat x)
        (model64OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bdiv 53 1024 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bdiv_RNE]
  unfold Float.Model.div
  rw [unpack_model64OfBinarySingleNaNFloat, unpack_model64OfBinarySingleNaNFloat]

theorem model32OfBinarySingleNaNFloat_Bdiv_RNE
    (x y : BinarySingleNaNFloat 24 128) :
    model32OfBinarySingleNaNFloat
        (@BinarySingleNaN.Bdiv 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
          RoundingMode.RNE x y) =
      Float32.Model.div (model32OfBinarySingleNaNFloat x)
        (model32OfBinarySingleNaNFloat y) := by
  change FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat
      (@BinarySingleNaN.Bdiv 24 128 ⟨by norm_num⟩ ⟨by norm_num⟩
        RoundingMode.RNE x y) = _
  rw [FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat_Bdiv_RNE]
  unfold Float32.Model.div
  rw [unpack_model32OfBinarySingleNaNFloat, unpack_model32OfBinarySingleNaNFloat]

theorem validStandardFloatOfModel64 (x : Float.Model) :
    validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024)
      (standardFloatOfModel64 x) = true :=
  FloatSpec.IEEE754.Native.validStandardFloatOfModel64 x

theorem validStandardFloatOfModel32 (x : Float32.Model) :
    validBinarySingleNaNStandardFloat (prec := 24) (emax := 128)
      (standardFloatOfModel32 x) = true :=
  FloatSpec.IEEE754.Native.validStandardFloatOfModel32 x

@[simp] theorem standardFloatOfModel64_model64OfStandardFloat
    (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) x = true) :
    standardFloatOfModel64 (model64OfStandardFloat x) = x :=
  FloatSpec.IEEE754.Native.standardFloatOfModel64_model64OfStandardFloat x hx

@[simp] theorem standardFloatOfModel32_model32OfStandardFloat
    (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 24) (emax := 128) x = true) :
    standardFloatOfModel32 (model32OfStandardFloat x) = x :=
  FloatSpec.IEEE754.Native.standardFloatOfModel32_model32OfStandardFloat x hx

@[simp] theorem model64OfStandardFloat_isNaN (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) x = true) :
    Float.Model.isNaN (model64OfStandardFloat x) = is_nan_SF x :=
  FloatSpec.IEEE754.Native.model64OfStandardFloat_isNaN x hx

@[simp] theorem model32OfStandardFloat_isNaN (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 24) (emax := 128) x = true) :
    Float32.Model.isNaN (model32OfStandardFloat x) = is_nan_SF x :=
  FloatSpec.IEEE754.Native.model32OfStandardFloat_isNaN x hx

@[simp] theorem model64OfStandardFloat_isFinite (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) x = true) :
    Float.Model.isFinite (model64OfStandardFloat x) = is_finite_SF x :=
  FloatSpec.IEEE754.Native.model64OfStandardFloat_isFinite x hx

@[simp] theorem model32OfStandardFloat_isFinite (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 24) (emax := 128) x = true) :
    Float32.Model.isFinite (model32OfStandardFloat x) = is_finite_SF x :=
  FloatSpec.IEEE754.Native.model32OfStandardFloat_isFinite x hx

theorem model64OfStandardFloat_SFopp (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) x = true) :
    model64OfStandardFloat (FaithfulPrimFloat.SFopp x) =
      Float.Model.neg (model64OfStandardFloat x) :=
  FloatSpec.IEEE754.Native.model64OfStandardFloat_SFopp x hx

theorem model32OfStandardFloat_SFopp (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 24) (emax := 128) x = true) :
    model32OfStandardFloat (FaithfulPrimFloat.SFopp x) =
      Float32.Model.neg (model32OfStandardFloat x) :=
  FloatSpec.IEEE754.Native.model32OfStandardFloat_SFopp x hx

theorem model64OfStandardFloat_SFabs (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) x = true) :
    model64OfStandardFloat (FaithfulPrimFloat.SFabs x) =
      Float.Model.abs (model64OfStandardFloat x) :=
  FloatSpec.IEEE754.Native.model64OfStandardFloat_SFabs x hx

theorem model32OfStandardFloat_SFabs (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 24) (emax := 128) x = true) :
    model32OfStandardFloat (FaithfulPrimFloat.SFabs x) =
      Float32.Model.abs (model32OfStandardFloat x) :=
  FloatSpec.IEEE754.Native.model32OfStandardFloat_SFabs x hx

namespace PrimitiveFloat

abbrev toModel := FaithfulPrimFloat.PrimitiveFloat.toModel
abbrev toFloat := FaithfulPrimFloat.PrimitiveFloat.toFloat
abbrev ofModel := FaithfulPrimFloat.PrimitiveFloat.ofModel
abbrev ofFloat := FaithfulPrimFloat.PrimitiveFloat.ofFloat

@[simp] theorem toModel_ofModel (x : Float.Model) :
    toModel (ofModel x) = x :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_ofModel x

@[simp] theorem ofModel_toModel (x : FaithfulPrimFloat.PrimitiveFloat) :
    ofModel (toModel x) = x :=
  FaithfulPrimFloat.PrimitiveFloat.ofModel_toModel x

@[simp] theorem toModel_neg (x : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (-x) = Float.Model.neg (toModel x) :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_neg x

@[simp] theorem toModel_abs (x : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (FaithfulPrimFloat.abs x) = Float.Model.abs (toModel x) :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_abs x

@[simp] theorem toModel_isNaN (x : FaithfulPrimFloat.PrimitiveFloat) :
    Float.Model.isNaN (toModel x) = FaithfulPrimFloat.is_nan x :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_isNaN x

@[simp] theorem toModel_isFinite (x : FaithfulPrimFloat.PrimitiveFloat) :
    Float.Model.isFinite (toModel x) = FaithfulPrimFloat.is_finite x :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_isFinite x

theorem toModel_compare (x y : FaithfulPrimFloat.PrimitiveFloat) :
    Float.Model.compare (toModel x) (toModel y) =
      FaithfulPrimFloat.SFcompare
        (FaithfulPrimFloat.Prim2SF x) (FaithfulPrimFloat.Prim2SF y) := by
  change Float.Model.compare
      (model64OfBinarySingleNaNFloat (FaithfulPrimFloat.Prim2B x))
      (model64OfBinarySingleNaNFloat (FaithfulPrimFloat.Prim2B y)) = _
  rw [model64OfBinarySingleNaNFloat_compare]
  exact congrArg₂ FaithfulPrimFloat.SFcompare
    (FaithfulPrimFloat.B2SF_Prim2B x) (FaithfulPrimFloat.B2SF_Prim2B y)

@[simp] theorem toModel_mul (x y : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (x * y) = Float.Model.mul (toModel x) (toModel y) :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_mul x y

@[simp] theorem toModel_add (x y : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (x + y) = Float.Model.add (toModel x) (toModel y) :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_add x y

@[simp] theorem toModel_sub (x y : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (x - y) = Float.Model.sub (toModel x) (toModel y) :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_sub x y

@[simp] theorem toModel_div (x y : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (x / y) = Float.Model.div (toModel x) (toModel y) :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_div x y

@[simp] theorem toModel_sqrt (x : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (FaithfulPrimFloat.sqrt x) = Float.Model.sqrt (toModel x) :=
  FaithfulPrimFloat.PrimitiveFloat.toModel_sqrt x

end PrimitiveFloat

end FloatSpec.IEEE754.LeanFloat
