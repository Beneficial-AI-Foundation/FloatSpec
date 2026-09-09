import FloatSpec.src.IEEE754.BinarySingleNaN

open Std.Do

/-!
# Source-faithful rounding-mode boundary

`BinarySingleNaN.v` exposes a five-constructor `mode` datatype and a
`round_mode` interpretation.  FloatSpec's integrated IEEE layer uses the
idiomatic `RoundingMode` names instead.  This facade preserves the exact Coq
surface and proves that it is only a renaming, not a second rounding model.
-/

namespace FloatSpec.IEEE754.BinarySingleNaN.Source

/-- Coq `BinarySingleNaN.mode`, with the source constructor names and order. -/
inductive mode where
  | mode_NE
  | mode_ZR
  | mode_DN
  | mode_UP
  | mode_NA
deriving DecidableEq, Repr

/-- Embed the source-facing mode into FloatSpec's integrated IEEE API. -/
def mode.toRoundingMode : mode → RoundingMode
  | mode.mode_NE => RoundingMode.RNE
  | mode.mode_ZR => RoundingMode.RTZ
  | mode.mode_DN => RoundingMode.RTN
  | mode.mode_UP => RoundingMode.RTP
  | mode.mode_NA => RoundingMode.RNA

/-- Recover the exact source-facing constructor from the integrated API. -/
def mode.ofRoundingMode : RoundingMode → mode
  | RoundingMode.RNE => mode.mode_NE
  | RoundingMode.RTZ => mode.mode_ZR
  | RoundingMode.RTN => mode.mode_DN
  | RoundingMode.RTP => mode.mode_UP
  | RoundingMode.RNA => mode.mode_NA

@[simp] theorem mode.ofRoundingMode_toRoundingMode (m : mode) :
    mode.ofRoundingMode m.toRoundingMode = m := by
  cases m <;> rfl

@[simp] theorem mode.toRoundingMode_ofRoundingMode (m : RoundingMode) :
    (mode.ofRoundingMode m).toRoundingMode = m := by
  cases m <;> rfl

/-- Coq `BinarySingleNaN.round_mode`.

The five branches are definitionally the same functions as the integrated
`rnd_of_mode`; spelling them through that implementation prevents the source
facade and the reusable API from drifting apart.
-/
noncomputable def round_mode (m : mode) : Real → Int :=
  rnd_of_mode m.toRoundingMode

@[simp] theorem round_mode_eq_rnd_of_mode (m : mode) :
    round_mode m = rnd_of_mode m.toRoundingMode := by
  rfl

noncomputable instance valid_rnd_round_mode (m : mode) :
    FloatSpec.Core.Generic_fmt.Valid_rnd (round_mode m) := by
  unfold round_mode
  infer_instance

/-- Compatibility name retained for the earlier facade API. -/
noncomputable abbrev valid_round_mode := valid_rnd_round_mode

end FloatSpec.IEEE754.BinarySingleNaN.Source

/-! Source-qualified names for the remaining proof-carrying SingleNaN API.
The algorithms below are the existing checked implementations; this file only
restores the Coq module boundary where `Binary.v` and `BinarySingleNaN.v`
otherwise have colliding unqualified names. -/

namespace BinarySingleNaN

-- Source ID: IEEE754/BinarySingleNaN.v:SF2R_B2SF:2984
-- Target: BinarySingleNaN.SF2R_B2SF
@[simp] theorem SF2R_B2SF {prec emax : Int} (x : binary_float prec emax) :
    SF2R 2 (B2SF x) = B2R x := by
  cases x <;> rfl

-- Source ID: IEEE754/BinarySingleNaN.v:valid_binary_B2SF:3201
-- Target: BinarySingleNaN.valid_binary_B2SF
@[simp] theorem valid_binary_B2SF {prec emax : Int}
    (x : binary_float prec emax) :
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) (B2SF x) = true :=
  validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat x

-- Source ID: IEEE754/BinarySingleNaN.v:SF2B_B2SF:3320
-- Target: BinarySingleNaN.SF2B_B2SF
@[simp] theorem SF2B_B2SF {prec emax : Int} (x : binary_float prec emax)
    (h : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
      (B2SF x) = true) :
    SF2B (B2SF x) h = x := by
  cases x <;> rfl

-- Source ID: IEEE754/BinarySingleNaN.v:SF2B_B2SF_valid:3468
-- Target: BinarySingleNaN.SF2B_B2SF_valid
@[simp] theorem SF2B_B2SF_valid {prec emax : Int}
    (x : binary_float prec emax) :
    SF2B (B2SF x) (valid_binary_B2SF x) = x :=
  SF2B_B2SF x (valid_binary_B2SF x)

-- Source ID: IEEE754/BinarySingleNaN.v:match_SF2B:3705
-- Target: BinarySingleNaN.match_SF2B
theorem match_SF2B {prec emax : Int} {T : Type}
    (fz fi : Bool → T) (fn : T) (ff : Bool → Nat → Int → T)
    (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true) :
    (match SF2B x hx with
      | BinarySingleNaNFloat.B754_zero sx => fz sx
      | BinarySingleNaNFloat.B754_infinity sx => fi sx
      | BinarySingleNaNFloat.B754_nan => fn
      | BinarySingleNaNFloat.B754_finite sx mx ex _ _ => ff sx mx ex) =
    match x with
      | StandardFloat.S754_zero sx => fz sx
      | StandardFloat.S754_infinity sx => fi sx
      | StandardFloat.S754_nan => fn
      | StandardFloat.S754_finite sx mx ex => ff sx mx ex := by
  cases x <;> rfl

-- Source ID: IEEE754/BinarySingleNaN.v:B2SF_inj:5484
-- Target: BinarySingleNaN.B2SF_inj
theorem B2SF_inj {prec emax : Int} (x y : binary_float prec emax)
    (h : B2SF x = B2SF y) : x = y := by
  cases x <;> cases y <;>
    simp_all [B2SF, binarySingleNaNFloatToStandardFloat]

-- Source ID: IEEE754/BinarySingleNaN.v:SF2B'_B2SF:5815
-- Target: BinarySingleNaN.SF2B'_B2SF
@[simp] theorem SF2B'_B2SF {prec emax : Int} (x : binary_float prec emax) :
    SF2B' (B2SF x) = x :=
  standardFloatToBinarySingleNaNFloat'_binarySingleNaNFloatToStandardFloat x

-- Source ID: IEEE754/BinarySingleNaN.v:is_finite_strict_B2R:6245
-- Target: BinarySingleNaN.is_finite_strict_B2R
theorem is_finite_strict_B2R {prec emax : Int} (x : binary_float prec emax)
    (h : B2R x ≠ 0) : is_finite_strict x = true := by
  cases x with
  | B754_zero s =>
      simp [B2R, binarySingleNaNFloatToB754, B754_to_R] at h
  | B754_infinity s =>
      simp [B2R, binarySingleNaNFloatToB754, B754_to_R] at h
  | B754_nan =>
      simp [B2R, binarySingleNaNFloatToB754, B754_to_R] at h
  | B754_finite s m e hm hb => rfl

-- Source ID: IEEE754/BinarySingleNaN.v:is_finite_SF_B2SF:8115
-- Target: BinarySingleNaN.is_finite_SF_B2SF
@[simp] theorem is_finite_SF_B2SF {prec emax : Int}
    (x : binary_float prec emax) :
    is_finite_SF (B2SF x) = is_finite x := by
  cases x <;> rfl

-- Source ID: IEEE754/BinarySingleNaN.v:is_nan_SF_B2SF:9183
-- Target: BinarySingleNaN.is_nan_SF_B2SF
@[simp] theorem is_nan_SF_B2SF {prec emax : Int}
    (x : binary_float prec emax) :
    is_nan_SF (B2SF x) = is_nan x := by
  cases x <;> rfl

def erase {prec emax : Int} (x : binary_float prec emax) : binary_float prec emax := x

@[simp] theorem erase_correct {prec emax : Int} (x : binary_float prec emax) :
    erase x = x := rfl

def Babs {prec emax : Int} : binary_float prec emax → binary_float prec emax
  | BinarySingleNaNFloat.B754_zero _ => BinarySingleNaNFloat.B754_zero false
  | BinarySingleNaNFloat.B754_infinity _ => BinarySingleNaNFloat.B754_infinity false
  | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_finite _ m e hm hb =>
      BinarySingleNaNFloat.B754_finite false m e hm hb

@[simp] theorem B2R_Babs {prec emax : Int} (x : binary_float prec emax) :
    B2R (Babs x) = |B2R x| := by
  cases x with
  | B754_zero s => simp [Babs, B2R, binarySingleNaNFloatToB754, B754_to_R]
  | B754_infinity s => simp [Babs, B2R, binarySingleNaNFloatToB754, B754_to_R]
  | B754_nan => simp [Babs, B2R, binarySingleNaNFloatToB754, B754_to_R]
  | B754_finite s m e hm hb =>
      have hp : 0 ≤ FloatSpec.Core.Raux.bpow 2 e :=
        le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e)
      cases s <;>
        simp [Babs, B2R, binarySingleNaNFloatToB754, B754_to_R,
          F2R, FloatSpec.Core.Defs.F2R, abs_mul]

@[simp] theorem is_nan_Babs {prec emax : Int} (x : binary_float prec emax) :
    is_nan (Babs x) = is_nan x := by
  cases x <;> rfl

@[simp] theorem is_finite_Babs {prec emax : Int} (x : binary_float prec emax) :
    is_finite (Babs x) = is_finite x := by
  cases x <;> rfl

@[simp] theorem is_finite_strict_Babs {prec emax : Int}
    (x : binary_float prec emax) :
    is_finite_strict (Babs x) = is_finite_strict x := by
  cases x <;> rfl

@[simp] theorem Bsign_Babs {prec emax : Int} (x : binary_float prec emax) :
    Bsign (Babs x) = false := by
  cases x <;> rfl

@[simp] theorem Babs_idempotent {prec emax : Int} (x : binary_float prec emax) :
    Babs (Babs x) = Babs x := by
  cases x <;> rfl

@[simp] theorem Babs_Bopp {prec emax : Int} (x : binary_float prec emax) :
    Babs (Bopp x) = Babs x := by
  cases x <;> rfl

private def toCompat {prec emax : Int} (x : binary_float prec emax) :
    Binary754 prec emax :=
  { val := SF2FF (B2SF x), valid := by intro; trivial }

private theorem is_finite_toCompat {prec emax : Int} (x : binary_float prec emax) :
    is_finite_B (toCompat x) = is_finite x := by
  cases x <;> rfl

private theorem B2R_toCompat {prec emax : Int} (x : binary_float prec emax) :
    _root_.B2R (toCompat x) = B2R x := by
  unfold toCompat _root_.B2R
  rw [FF2R_SF2FF]
  cases x <;> rfl

/-! The integrated `Binary` implementation still uses the historical integer
comparison codes.  Keep that endpoint explicit, then bridge the three source
codes to Lean's `Ordering`, which is the direct counterpart of Coq's
`comparison`. -/

noncomputable def BcompareIntCompat {prec emax : Int}
    (x y : binary_float prec emax) : Option Int :=
  _root_.Bcompare (toCompat x) (toCompat y)

def orderingOfCompareCode (c : Int) : Ordering :=
  if c < 0 then Ordering.lt else if c = 0 then Ordering.eq else Ordering.gt

@[simp] theorem orderingOfCompareCode_neg_one :
    orderingOfCompareCode (-1) = Ordering.lt := by
  simp [orderingOfCompareCode]

@[simp] theorem orderingOfCompareCode_zero :
    orderingOfCompareCode 0 = Ordering.eq := by
  simp [orderingOfCompareCode]

@[simp] theorem orderingOfCompareCode_one :
    orderingOfCompareCode 1 = Ordering.gt := by
  simp [orderingOfCompareCode]

@[simp] theorem orderingOfCompareCode_neg (c : Int) :
    orderingOfCompareCode (-c) = (orderingOfCompareCode c).swap := by
  by_cases hcneg : c < 0
  · have hnegpos : ¬ -c < 0 := by omega
    have hcnonpos : c ≤ 0 := le_of_lt hcneg
    have hcne : c ≠ 0 := by omega
    have hnegne : -c ≠ 0 := by omega
    simp [orderingOfCompareCode, hcneg, hnegpos, hcnonpos, hcne, hnegne]
  · by_cases hczero : c = 0
    · subst c
      simp [orderingOfCompareCode]
    · have hcpos : 0 < c := by omega
      have hnegneg : -c < 0 := by omega
      simp [orderingOfCompareCode, hcneg, hczero, hcpos, hnegneg]

noncomputable def RcompareOrdering (x y : ℝ) : Ordering :=
  if x < y then Ordering.lt else if x = y then Ordering.eq else Ordering.gt

theorem orderingOfCompareCode_Rcompare (x y : ℝ) :
    orderingOfCompareCode (FloatSpec.Core.Raux.Rcompare x y) =
      RcompareOrdering x y := by
  by_cases hxy : x < y
  · simp [FloatSpec.Core.Raux.Rcompare, RcompareOrdering,
      orderingOfCompareCode, hxy]
  · by_cases heq : x = y
    · simp [FloatSpec.Core.Raux.Rcompare, RcompareOrdering,
        orderingOfCompareCode, hxy, heq]
    · simp [FloatSpec.Core.Raux.Rcompare, RcompareOrdering,
        orderingOfCompareCode, hxy, heq]

noncomputable def Bcompare {prec emax : Int}
    (x y : binary_float prec emax) : Option Ordering :=
  (BcompareIntCompat x y).map orderingOfCompareCode

theorem Bcompare_correct {prec emax : Int} (x y : binary_float prec emax)
    (hx : is_finite x = true) (hy : is_finite y = true) :
    Bcompare x y = some (RcompareOrdering (B2R x) (B2R y)) := by
  have h := _root_.Bcompare_correct_compat (toCompat x) (toCompat y)
    (by simpa [is_finite_toCompat] using hx)
    (by simpa [is_finite_toCompat] using hy)
  have hcode : BcompareIntCompat x y =
      some (FloatSpec.Core.Raux.Rcompare (B2R x) (B2R y)) := by
    simpa [BcompareIntCompat, B2R_toCompat, wp, Std.Do.PostCond.noThrow,
      pure, _root_.Bcompare_check] using h trivial
  simp [Bcompare, hcode, orderingOfCompareCode_Rcompare]

theorem Bcompare_swap {prec emax : Int} (x y : binary_float prec emax) :
    Bcompare y x = match Bcompare x y with
      | some c => some c.swap
      | none => none := by
  have h := _root_.Bcompare_swap_compat (toCompat x) (toCompat y)
  have hcode : BcompareIntCompat y x = match BcompareIntCompat x y with
      | some c => some (-c)
      | none => none := by
    exact h trivial
  unfold Bcompare
  rw [hcode]
  cases BcompareIntCompat x y <;> simp

theorem B2R_inj {prec emax : Int}
    (x y : binary_float prec emax)
    (hx : is_finite_strict x = true) (hy : is_finite_strict y = true)
    (hR : B2R x = B2R y) : x = y := by
  cases x with
  | B754_zero sx =>
      simp [BinarySingleNaN.is_finite_strict, binarySingleNaNFloatToB754,
        BSN_is_finite_strict] at hx
  | B754_infinity sx =>
      simp [BinarySingleNaN.is_finite_strict, binarySingleNaNFloatToB754,
        BSN_is_finite_strict] at hx
  | B754_nan =>
      simp [BinarySingleNaN.is_finite_strict, binarySingleNaNFloatToB754,
        BSN_is_finite_strict] at hx
  | B754_finite sx mx ex hmx Hx =>
      cases y with
      | B754_zero sy =>
          simp [BinarySingleNaN.is_finite_strict, binarySingleNaNFloatToB754,
            BSN_is_finite_strict] at hy
      | B754_infinity sy =>
          simp [BinarySingleNaN.is_finite_strict, binarySingleNaNFloatToB754,
            BSN_is_finite_strict] at hy
      | B754_nan =>
          simp [BinarySingleNaN.is_finite_strict, binarySingleNaNFloatToB754,
            BSN_is_finite_strict] at hy
      | B754_finite sy my ey hmy Hy =>
          let px := binaryPositiveOfNat mx hmx
          let py := binaryPositiveOfNat my hmy
          let fx : FloatSpec.Core.Defs.FlocqFloat 2 :=
            ⟨if sx then -(mx : Int) else (mx : Int), ex⟩
          let fy : FloatSpec.Core.Defs.FlocqFloat 2 :=
            ⟨if sy then -(my : Int) else (my : Int), ey⟩
          have hcx : FloatSpec.Core.Generic_fmt.canonical 2
              (FLT_exp (3 - emax - prec) prec) fx := by
            have h := _root_.canonical_canonical_mantissa
              (prec:=prec) (emax:=emax) sx px ex
              (by simpa [px, binaryPositiveOfNat_spec] using
                canonical_mantissa_of_specFloat_bounded Hx)
            simpa [fx, px, binaryPositiveOfNat_spec] using h
          have hcy : FloatSpec.Core.Generic_fmt.canonical 2
              (FLT_exp (3 - emax - prec) prec) fy := by
            have h := _root_.canonical_canonical_mantissa
              (prec:=prec) (emax:=emax) sy py ey
              (by simpa [py, binaryPositiveOfNat_spec] using
                canonical_mantissa_of_specFloat_bounded Hy)
            simpa [fy, py, binaryPositiveOfNat_spec] using h
          have hxy : fx = fy := FloatSpec.Core.Generic_fmt.canonical_unique
            2 (by norm_num) (FLT_exp (3 - emax - prec) prec) fx fy hcx hcy (by
              cases sx <;> cases sy <;>
                simpa [fx, fy, B2R, binarySingleNaNFloatToB754, B754_to_R,
                  F2R, FloatSpec.Core.Defs.F2R] using hR)
          have hmEq : (if sx then -(mx : Int) else (mx : Int)) =
              (if sy then -(my : Int) else (my : Int)) := by
            exact congrArg FloatSpec.Core.Defs.FlocqFloat.Fnum hxy
          have heEq : ex = ey := congrArg FloatSpec.Core.Defs.FlocqFloat.Fexp hxy
          have hsm : sx = sy ∧ mx = my := by
            cases sx <;> cases sy <;> simp at hmEq ⊢ <;> omega
          rcases hsm with ⟨rfl, rfl⟩
          subst ey
          rfl

private theorem finite_B2R_ne_zero {prec emax : Int}
    (s : Bool) (m : Nat) (e : Int) (hm : 0 < m)
    (hb : specFloat_bounded (prec:=prec) (emax:=emax) m e = true) :
    B2R (BinarySingleNaNFloat.B754_finite s m e hm hb) ≠ 0 := by
  have hm' : (if s then -(m : Int) else (m : Int)) ≠ 0 := by
    cases s <;> simp <;> omega
  exact FloatSpec.Core.Float_prop.F2R_neq_0
    (beta:=2)
    (f:=FloatSpec.Core.Defs.FlocqFloat.mk
      (if s then -(m : Int) else (m : Int)) e)
    (by norm_num) hm'

theorem B2R_Bsign_inj {prec emax : Int}
    (x y : binary_float prec emax)
    (hx : is_finite x = true) (hy : is_finite y = true)
    (hR : B2R x = B2R y) (hs : Bsign x = Bsign y) : x = y := by
  cases x with
  | B754_zero sx =>
      cases y with
      | B754_zero sy =>
          simpa [Bsign, binarySingleNaNFloatToB754, BSN_sign] using hs
      | B754_infinity sy =>
          simp [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754,
            BSN_is_finite] at hy
      | B754_nan =>
          simp [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754,
            BSN_is_finite] at hy
      | B754_finite sy m e hm hb =>
          exact False.elim (finite_B2R_ne_zero sy m e hm hb hR.symm)
  | B754_infinity sx =>
      simp [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754,
        BSN_is_finite] at hx
  | B754_nan =>
      simp [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754,
        BSN_is_finite] at hx
  | B754_finite sx m ex hm hbx =>
      cases y with
      | B754_zero sy => exact False.elim (finite_B2R_ne_zero sx m ex hm hbx hR)
      | B754_infinity sy =>
          simp [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754,
            BSN_is_finite] at hy
      | B754_nan =>
          simp [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754,
            BSN_is_finite] at hy
      | B754_finite sy n ey hn hby =>
          exact B2R_inj
            (BinarySingleNaNFloat.B754_finite sx m ex hm hbx)
            (BinarySingleNaNFloat.B754_finite sy n ey hn hby) rfl rfl hR

theorem bounded_le_emax_minus_prec {prec emax : Int}
    [Prec_gt_0 prec] (m : FloatSpec.Core.Zaux.Positive) (e : Int)
    (hb : bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true) :
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Zaux.positiveToNat m : Int) e :
        FloatSpec.Core.Defs.FlocqFloat 2) ≤
      FloatSpec.Core.Raux.bpow 2 emax -
        FloatSpec.Core.Raux.bpow 2 (emax - prec) :=
  Binary.bounded_le_emax_minus_prec m e hb

theorem bounded_lt_emax {prec emax : Int}
    (m : FloatSpec.Core.Zaux.Positive) (e : Int)
    (hb : bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true) :
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Zaux.positiveToNat m : Int) e :
        FloatSpec.Core.Defs.FlocqFloat 2) < FloatSpec.Core.Raux.bpow 2 emax :=
  Binary.bounded_lt_emax m e hb

theorem bounded_ge_emin {prec emax : Int}
    (m : FloatSpec.Core.Zaux.Positive) (e : Int)
    (hb : bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true) :
    FloatSpec.Core.Raux.bpow 2 (3 - emax - prec) ≤
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk
        (FloatSpec.Core.Zaux.positiveToNat m : Int) e :
          FloatSpec.Core.Defs.FlocqFloat 2) :=
  Binary.bounded_ge_emin m e hb

theorem abs_B2R_le_emax_minus_prec {prec emax : Int}
    [Prec_gt_0 prec]
    (x : binary_float prec emax) :
    |B2R x| ≤ FloatSpec.Core.Raux.bpow 2 emax -
      FloatSpec.Core.Raux.bpow 2 (emax - prec) := by
  cases x with
  | B754_zero s | B754_infinity s | B754_nan =>
      have hprec := (inferInstance : Prec_gt_0 prec).pos
      have htrip := FloatSpec.Core.Raux.bpow_le 2 (emax - prec) emax
        (by norm_num) (by omega)
      have hpow : FloatSpec.Core.Raux.bpow 2 (emax - prec) ≤
          FloatSpec.Core.Raux.bpow 2 emax := by
        simpa [wp, Std.Do.PostCond.noThrow, pure,
          FloatSpec.Core.Raux.bpow_le_check, FloatSpec.Core.Raux.bpow] using
          htrip trivial
      simp [B2R, binarySingleNaNFloatToB754, B754_to_R]
      exact hpow
  | B754_finite s m e hm hb =>
      let mp := binaryPositiveOfNat m hm
      have hrange := range_bounded_of_specFloat_bounded m e hm hb
      have h := bounded_le_emax_minus_prec mp e (by
        simpa [mp, binaryPositiveOfNat_spec] using hrange)
      have hp : 0 ≤ FloatSpec.Core.Raux.bpow 2 e :=
        le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e)
      cases s <;>
        simpa [B2R, binarySingleNaNFloatToB754, B754_to_R,
          F2R, FloatSpec.Core.Defs.F2R, mp, binaryPositiveOfNat_spec,
          abs_mul, abs_of_nonneg hp] using h

theorem abs_B2R_lt_emax {prec emax : Int}
    (x : binary_float prec emax) :
    |B2R x| < FloatSpec.Core.Raux.bpow 2 emax := by
  cases x with
  | B754_zero s | B754_infinity s | B754_nan =>
      simpa [B2R, binarySingleNaNFloatToB754, B754_to_R,
        FloatSpec.Core.Raux.bpow] using
        (zpow_pos (by norm_num : (0 : ℝ) < 2) emax)
  | B754_finite s m e hm hb =>
      let mp := binaryPositiveOfNat m hm
      have hrange := range_bounded_of_specFloat_bounded m e hm hb
      have h := bounded_lt_emax mp e (by
        simpa [mp, binaryPositiveOfNat_spec] using hrange)
      have hp : 0 ≤ FloatSpec.Core.Raux.bpow 2 e :=
        le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e)
      cases s <;>
        simpa [B2R, binarySingleNaNFloatToB754, B754_to_R,
          F2R, FloatSpec.Core.Defs.F2R, mp, binaryPositiveOfNat_spec,
          abs_mul, abs_of_nonneg hp] using h

theorem abs_B2R_ge_emin {prec emax : Int}
    (x : binary_float prec emax) (hx : is_finite_strict x = true) :
    FloatSpec.Core.Raux.bpow 2 (3 - emax - prec) ≤ |B2R x| := by
  cases x with
  | B754_zero s | B754_infinity s | B754_nan =>
      simp [is_finite_strict, binarySingleNaNFloatToB754,
        BSN_is_finite_strict] at hx
  | B754_finite s m e hm hb =>
      let mp := binaryPositiveOfNat m hm
      have hrange := range_bounded_of_specFloat_bounded m e hm hb
      have h := bounded_ge_emin mp e (by
        simpa [mp, binaryPositiveOfNat_spec] using hrange)
      have hp : 0 ≤ FloatSpec.Core.Raux.bpow 2 e :=
        le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e)
      cases s <;>
        simpa [B2R, binarySingleNaNFloatToB754, B754_to_R,
          F2R, FloatSpec.Core.Defs.F2R, mp, binaryPositiveOfNat_spec,
          abs_mul, abs_of_nonneg hp] using h

theorem bounded_canonical_lt_emax {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : FloatSpec.Core.Zaux.Positive) (e : Int)
    (hc : FloatSpec.Core.Generic_fmt.canonical 2
      (FLT_exp (3 - emax - prec) prec)
      (FloatSpec.Core.Defs.FlocqFloat.mk
        (FloatSpec.Core.Zaux.positiveToNat m : Int) e))
    (hlt : F2R (FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Zaux.positiveToNat m : Int) e :
        FloatSpec.Core.Defs.FlocqFloat 2) < FloatSpec.Core.Raux.bpow 2 emax) :
    bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true :=
  Binary.bounded_canonical_lt_emax m e hc hlt

abbrev shl_align_fexp {prec emax : Int} := @Binary.shl_align_fexp prec emax

abbrev shl_align_fexp_correct {prec emax : Int} :=
  @Binary.shl_align_fexp_correct prec emax

noncomputable abbrev shr_fexp {prec emax : Int} := @Binary.shr_fexp prec emax

abbrev shr_fexp_truncate {prec emax : Int} := @Binary.shr_fexp_truncate prec emax

noncomputable abbrev binary_round_aux {prec emax : Int} :=
  @_root_.binary_round_aux prec emax

noncomputable def binary_round {prec emax : Int}
    (mode : RoundingMode) (s : Bool) (m : FloatSpec.Core.Zaux.Positive)
    (e : Int) : StandardFloat :=
  _root_.binary_round (prec:=prec) (emax:=emax) mode s
    (FloatSpec.Core.Zaux.positiveToNat m) e

abbrev binary_round_aux_correct' {prec emax : Int} :=
  @_root_.binary_round_aux_correct' prec emax

theorem binary_round_aux_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : ℝ) (m : FloatSpec.Core.Zaux.Positive)
    (e : Int) (l : Loc)
    (hbetween : FloatSpec.Calc.Bracket.inbetween_float 2
      (FloatSpec.Core.Zaux.positiveToNat m : Int) e |x| l)
    (hexp : e ≤ FLT_exp (3 - emax - prec) prec
      (FloatSpec.Core.Digits.Zdigits 2
        (FloatSpec.Core.Zaux.positiveToNat m : Int) + e)) :
    let z := binary_round_aux (prec:=prec) (emax:=emax) mode
      (FloatSpec.Core.Raux.Rlt_bool x 0)
      (FloatSpec.Core.Zaux.positiveToNat m : Int) e l
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      if FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        SF2R 2 z = FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x ∧
          is_finite_SF z = true ∧
          sign_SF z = FloatSpec.Core.Raux.Rlt_bool x 0
      else z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode
        (FloatSpec.Core.Raux.Rlt_bool x 0) := by
  exact _root_.binary_round_aux_correct (prec:=prec) (emax:=emax)
    mode x (FloatSpec.Core.Zaux.positiveToNat m) e l
      (FloatSpec.Core.Zaux.positiveToNat_pos m) hbetween hexp

theorem binary_round_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (s : Bool) (m : FloatSpec.Core.Zaux.Positive)
    (e : Int) :
    let z := binary_round (prec:=prec) (emax:=emax) mode s m e
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      let x := SF2R 2 (StandardFloat.S754_finite s
        (FloatSpec.Core.Zaux.positiveToNat m) e)
      if FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        SF2R 2 z = FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x ∧
          is_finite_SF z = true ∧ sign_SF z = s
      else z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode s := by
  exact _root_.binary_round_correct (prec:=prec) (emax:=emax)
    mode s (FloatSpec.Core.Zaux.positiveToNat m) e
      (FloatSpec.Core.Zaux.positiveToNat_pos m)

abbrev binary_overflow {prec emax : Int} :=
  @bsn_binary_overflow prec emax

theorem is_nan_binary_round {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (s : Bool) (m : FloatSpec.Core.Zaux.Positive) (e : Int) :
    is_nan_SF (binary_round (prec:=prec) (emax:=emax) mode s m e) = false :=
  _root_.is_nan_binary_round (prec:=prec) (emax:=emax) mode s
    (FloatSpec.Core.Zaux.positiveToNat m) e

theorem is_nan_binary_overflow {prec emax : Int}
    (mode : RoundingMode) (s : Bool) :
    is_nan_SF (binary_overflow (prec:=prec) (emax:=emax) mode s) = false :=
  _root_.is_nan_binary_overflow (prec:=prec) (emax:=emax) mode s

theorem binary_overflow_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (s : Bool) :
    valid_binary_SF (prec:=prec) (emax:=emax)
      (binary_overflow (prec:=prec) (emax:=emax) mode s) = true :=
  _root_.binary_overflow_correct (prec:=prec) (emax:=emax) mode s

noncomputable def binary_normalize {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (m e : Int) (szero : Bool) : binary_float prec emax :=
  Binary.B2BSN (Binary.normalize (prec:=prec) (emax:=emax) mode m e szero)

theorem binary_normalize_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (m e : Int) (szero : Bool) :
    let input := F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
      FloatSpec.Core.Defs.FlocqFloat 2)
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
          (rnd_of_mode mode) input| (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (binary_normalize (prec:=prec) (emax:=emax) mode m e szero) =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
            (rnd_of_mode mode) input ∧
      is_finite (binary_normalize (prec:=prec) (emax:=emax) mode m e szero) = true ∧
      Bsign (binary_normalize (prec:=prec) (emax:=emax) mode m e szero) =
        (if input = 0 then szero else decide (input < 0))
    else
      B2SF (binary_normalize (prec:=prec) (emax:=emax) mode m e szero) =
        bsn_binary_overflow (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool input 0) := by
  simpa [binary_normalize] using
    normalize_B2BSN_correct (prec:=prec) (emax:=emax) mode m e szero

theorem is_nan_binary_normalize {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (m e : Int) (szero : Bool) :
    is_nan (binary_normalize (prec:=prec) (emax:=emax) mode m e szero) = false := by
  have hc := binary_normalize_correct (prec:=prec) (emax:=emax) mode m e szero
  dsimp only at hc
  cases hr : binary_normalize (prec:=prec) (emax:=emax) mode m e szero with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_finite s n f hn hb => rfl
  | B754_nan =>
      by_cases hlt : FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
            (rnd_of_mode mode)
            (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
              FloatSpec.Core.Defs.FlocqFloat 2))|
          (FloatSpec.Core.Raux.bpow 2 emax) = true
      · rw [ite_eq_left hlt] at hc
        rw [hr] at hc
        simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hc
      · rw [ite_eq_right hlt] at hc
        rw [hr] at hc
        cases hs : FloatSpec.Core.Raux.Rlt_bool
            (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
              FloatSpec.Core.Defs.FlocqFloat 2)) 0 <;>
          cases mode <;>
          simp_all [B2SF, binarySingleNaNFloatToStandardFloat,
            binary_overflow, bsn_binary_overflow, overflow_to_inf]

noncomputable abbrev Bnearbyint {prec emax : Int}
    [Prec_lt_emax prec emax] :=
  @Binary.BnearbyintSingle prec emax _

theorem Bnearbyint_correct {prec emax : Int}
    [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : binary_float prec emax) :
    B2R (Bnearbyint mode x) =
        FloatSpec.Core.Generic_fmt.roundR 2 (FloatSpec.Core.FIX.FIX_exp 0)
          (rnd_of_mode mode) (B2R x) ∧
      is_finite (Bnearbyint mode x) = is_finite x ∧
      (is_nan (Bnearbyint mode x) = false → Bsign (Bnearbyint mode x) = Bsign x) := by
  have hround0 : FloatSpec.Core.Generic_fmt.roundR 2
      (FloatSpec.Core.FIX.FIX_exp 0) (rnd_of_mode mode) 0 = 0 := by
    simpa only [FloatSpec.Core.Generic_fmt.round_to_generic] using
      round_to_generic_rnd_of_mode_zero mode (FloatSpec.Core.FIX.FIX_exp 0)
  cases x with
  | B754_zero s =>
      simp [Bnearbyint, Binary.BnearbyintSingle, B2R, Bsign, is_finite,
        is_nan, binarySingleNaNFloatToB754, B754_to_R, hround0]
  | B754_infinity s =>
      simp [Bnearbyint, Binary.BnearbyintSingle, B2R, Bsign, is_finite,
        is_nan, binarySingleNaNFloatToB754, B754_to_R, hround0]
  | B754_nan =>
      simp [Bnearbyint, Binary.BnearbyintSingle, B2R, Bsign, is_finite,
        is_nan, binarySingleNaNFloatToB754, B754_to_R, hround0]
  | B754_finite s m e hm hb =>
      let z := SFnearbyint_binary (prec:=prec) (emax:=emax) mode s m e
      have hc := _root_.Bnearbyint_correct_aux_nat (prec:=prec) (emax:=emax)
        mode s m e hm hb
      have hn : is_nan_SF z = false := by
        have hf : is_finite_SF z = true := hc.2.2.1
        cases hz : z <;> simp [hz, is_finite_SF, is_nan_SF] at hf ⊢
      change B2R (Binary.BnearbyintSingle mode
          (BinarySingleNaNFloat.B754_finite s m e hm hb)) =
            FloatSpec.Core.Generic_fmt.roundR 2 (FloatSpec.Core.FIX.FIX_exp 0)
              (rnd_of_mode mode)
              (B2R (BinarySingleNaNFloat.B754_finite s m e hm hb)) ∧
        is_finite (Binary.BnearbyintSingle mode
          (BinarySingleNaNFloat.B754_finite s m e hm hb)) = true ∧
        (is_nan (Binary.BnearbyintSingle mode
            (BinarySingleNaNFloat.B754_finite s m e hm hb)) = false →
          Bsign (Binary.BnearbyintSingle mode
            (BinarySingleNaNFloat.B754_finite s m e hm hb)) = s)
      rw [show Binary.BnearbyintSingle mode
          (BinarySingleNaNFloat.B754_finite s m e hm hb) =
          standardFloatToBinarySingleNaNFloat z hc.1 by rfl]
      constructor
      · change B754_to_R (binarySingleNaNFloatToB754
            (standardFloatToBinarySingleNaNFloat z hc.1)) = _
        rw [Binary.B2R_standardFloatToBinarySingleNaNFloat]
        simpa [z, B2R, binarySingleNaNFloatToB754, B754_to_R,
          SF2R] using hc.2.1
      · constructor
        · change BSN_is_finite (binarySingleNaNFloatToB754
              (standardFloatToBinarySingleNaNFloat z hc.1)) = true
          rw [Binary.is_finite_standardFloatToBinarySingleNaNFloat]
          exact hc.2.2.1
        · intro _
          change BSN_sign (binarySingleNaNFloatToB754
            (standardFloatToBinarySingleNaNFloat z hc.1)) = s
          rw [Binary.Bsign_standardFloatToBinarySingleNaNFloat _ _ hn]
          exact hc.2.2.2 hn

theorem Bnearbyint_correct_aux {prec emax : Int}
    [Prec_lt_emax prec emax]
    (mode : RoundingMode) (sx : Bool)
    (mx : FloatSpec.Core.Zaux.Positive) (ex : Int)
    (Hx : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mx) ex = true) :
    let x := SF2R 2 (StandardFloat.S754_finite sx
      (FloatSpec.Core.Zaux.positiveToNat mx) ex)
    let z := SFnearbyint_binary (prec:=prec) (emax:=emax) mode sx
      (FloatSpec.Core.Zaux.positiveToNat mx) ex
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      SF2R 2 z = FloatSpec.Core.Generic_fmt.roundR 2
        (FloatSpec.Core.FIX.FIX_exp 0) (rnd_of_mode mode) x ∧
      is_finite_SF z = true ∧
      (is_nan_SF z = false → sign_SF z = sx) :=
  _root_.Bnearbyint_correct_aux (prec:=prec) (emax:=emax) mode sx mx ex Hx

theorem sign_plus_overflow {prec emax : Int}
    [Prec_gt_0 prec]
    (mode : RoundingMode)
    (sx : Bool) (mx : FloatSpec.Core.Zaux.Positive) (ex : Int)
    (sy : Bool) (my : FloatSpec.Core.Zaux.Positive) (ey : Int)
    (Hx : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mx) ex = true)
    (Hy : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat my) ey = true) :
    let z :=
      (SF2R 2 (StandardFloat.S754_finite sx
          (FloatSpec.Core.Zaux.positiveToNat mx) ex) +
        SF2R 2 (StandardFloat.S754_finite sy
          (FloatSpec.Core.Zaux.positiveToNat my) ey))
    FloatSpec.Core.Raux.bpow 2 emax ≤
      |FloatSpec.Core.Generic_fmt.round_to_generic 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) z| →
    sx = FloatSpec.Core.Raux.Rlt_bool z 0 ∧ sx = sy :=
  _root_.sign_plus_overflow (prec:=prec) (emax:=emax)
    mode sx mx ex sy my ey Hx Hy

noncomputable def Btrunc {prec emax : Int} (x : binary_float prec emax) : Int :=
  FloatSpec.Core.Raux.Ztrunc (B2R x)

theorem Btrunc_correct {prec emax : Int} (x : binary_float prec emax) :
    (Btrunc x : ℝ) =
      FloatSpec.Core.Generic_fmt.round_to_generic 2
        (FloatSpec.Core.FIX.FIX_exp 0) FloatSpec.Core.Raux.Ztrunc (B2R x) := by
  have h := FloatSpec.Core.FIX.round_FIX_IZR FloatSpec.Core.Raux.Ztrunc (B2R x)
  simpa [Btrunc, wp, Std.Do.PostCond.noThrow, pure] using (h trivial).symm

noncomputable abbrev Bone {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :=
  @Binary.BoneSingle prec emax _ _

abbrev Bmax_float {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :=
  @Binary.BmaxFloatSingle prec emax _ _

abbrev Bnormfr_mantissa {prec emax : Int} :=
  @BinarySingleNaNFloat.Bnormfr_mantissa prec emax

noncomputable abbrev Bldexp {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :=
  @Binary.BldexpSingle prec emax _ _

private theorem is_nan_eq_internal {prec emax : Int}
    (x : binary_float prec emax) : is_nan x = Binary.is_nan_BSN x := by
  cases x <;> rfl

theorem is_nan_Bldexp {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : binary_float prec emax) (k : Int) :
    is_nan (Bldexp mode x k) = is_nan x := by
  have href := Binary.is_nan_BldexpSingle (prec:=prec) (emax:=emax) mode x k
  simpa [Bldexp, is_nan_eq_internal] using href

theorem Bldexp_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : binary_float prec emax) (k : Int) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
          (rnd_of_mode mode) (B2R x * FloatSpec.Core.Raux.bpow 2 k)|
        (FloatSpec.Core.Raux.bpow 2 emax) = true then
      B2R (Bldexp mode x k) =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
            (rnd_of_mode mode) (B2R x * FloatSpec.Core.Raux.bpow 2 k) ∧
        is_finite (Bldexp mode x k) = is_finite x ∧
        Bsign (Bldexp mode x k) = Bsign x
    else B2SF (Bldexp mode x k) =
      binary_overflow (prec:=prec) (emax:=emax) mode (Bsign x) := by
  have hround0 : FloatSpec.Core.Generic_fmt.roundR 2
      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) 0 = 0 := by
    simpa only [FloatSpec.Core.Generic_fmt.round_to_generic] using
      round_to_generic_rnd_of_mode_zero mode (FLT_exp (3 - emax - prec) prec)
  have hbpow : 0 < FloatSpec.Core.Raux.bpow 2 emax :=
    zpow_pos (by norm_num : (0 : ℝ) < 2) emax
  cases x with
  | B754_zero s =>
      simp [Bldexp, Binary.BldexpSingle, B2R, B2SF, Bsign, is_finite,
        binarySingleNaNFloatToB754, binarySingleNaNFloatToStandardFloat,
        B754_to_R, hround0, FloatSpec.Core.Raux.Rlt_bool, hbpow]
  | B754_infinity s =>
      simp [Bldexp, Binary.BldexpSingle, B2R, B2SF, Bsign, is_finite,
        binarySingleNaNFloatToB754, binarySingleNaNFloatToStandardFloat,
        B754_to_R, hround0, FloatSpec.Core.Raux.Rlt_bool, hbpow]
  | B754_nan =>
      simp [Bldexp, Binary.BldexpSingle, B2R, B2SF, Bsign, is_finite,
        binarySingleNaNFloatToB754, binarySingleNaNFloatToStandardFloat,
        B754_to_R, hround0, FloatSpec.Core.Raux.Rlt_bool, hbpow]
  | B754_finite s m e hm hb =>
      let z := _root_.binary_round (prec:=prec) (emax:=emax) mode s m (e + k)
      have hc := _root_.binary_round_correct (prec:=prec) (emax:=emax)
        mode s m (e + k) hm
      have hinput : SF2R 2 (StandardFloat.S754_finite s m (e + k)) =
          B2R (BinarySingleNaNFloat.B754_finite s m e hm hb) *
            FloatSpec.Core.Raux.bpow 2 k := by
        have h2 : (2 : ℝ) ≠ 0 := by norm_num
        cases s <;>
          simp [SF2R, B2R, binarySingleNaNFloatToB754, B754_to_R,
            F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Raux.bpow] <;>
          rw [zpow_add₀ h2] <;> ring
      have hout : Bldexp mode
          (BinarySingleNaNFloat.B754_finite s m e hm hb) k =
          standardFloatToBinarySingleNaNFloat z hc.1 := by rfl
      have hvalue : B2R (Bldexp mode
          (BinarySingleNaNFloat.B754_finite s m e hm hb) k) = SF2R 2 z := by
        rw [hout]
        change B754_to_R (binarySingleNaNFloatToB754
          (standardFloatToBinarySingleNaNFloat z hc.1)) = _
        exact Binary.B2R_standardFloatToBinarySingleNaNFloat z hc.1
      have hfinite : is_finite (Bldexp mode
          (BinarySingleNaNFloat.B754_finite s m e hm hb) k) = is_finite_SF z := by
        rw [hout]
        change BSN_is_finite (binarySingleNaNFloatToB754
          (standardFloatToBinarySingleNaNFloat z hc.1)) = _
        exact Binary.is_finite_standardFloatToBinarySingleNaNFloat z hc.1
      have hn : is_nan_SF z = false := by
        simpa [z] using _root_.is_nan_binary_round (prec:=prec) (emax:=emax)
          mode s m (e + k)
      have hsign : Bsign (Bldexp mode
          (BinarySingleNaNFloat.B754_finite s m e hm hb) k) = sign_SF z := by
        rw [hout]
        change BSN_sign (binarySingleNaNFloatToB754
          (standardFloatToBinarySingleNaNFloat z hc.1)) = _
        exact Binary.Bsign_standardFloatToBinarySingleNaNFloat z hc.1 hn
      have hbranch := hc.2
      rw [hinput] at hbranch
      by_cases hlt : FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
            (rnd_of_mode mode)
            (B2R (BinarySingleNaNFloat.B754_finite s m e hm hb) *
              FloatSpec.Core.Raux.bpow 2 k)|
          (FloatSpec.Core.Raux.bpow 2 emax) = true
      · rw [ite_eq_left hlt] at hbranch ⊢
        exact ⟨hvalue.trans hbranch.1, hfinite.trans hbranch.2.1,
          hsign.trans (by simpa [Bsign, binarySingleNaNFloatToB754,
            BSN_sign] using hbranch.2.2)⟩
      · rw [ite_eq_right hlt] at hbranch ⊢
        rw [hout, B2SF_SF2B]
        exact hbranch

private theorem toB754_inj {prec emax : Int} {x y : binary_float prec emax}
    (h : binarySingleNaNFloatToB754 x = binarySingleNaNFloatToB754 y) : x = y := by
  cases x <;> cases y <;> simp_all [binarySingleNaNFloatToB754]

private theorem Bopp_toB754 {prec emax : Int} (x : binary_float prec emax) :
    binarySingleNaNFloatToB754 (Bopp x) =
      ExperimentalSingleNaNArithmetic.Bopp_bsn (binarySingleNaNFloatToB754 x) := by
  cases x <;> rfl

private theorem normalize_toB754 {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (m e : Int) (szero : Bool) :
    binarySingleNaNFloatToB754
        (Binary.B2BSN (Binary.normalize (prec:=prec) (emax:=emax)
          mode m e szero)) =
      _root_.binary_normalize (prec:=prec) (emax:=emax) mode m e szero := by
  by_cases hm0 : m = 0
  · simp [Binary.normalize, _root_.binary_normalize, hm0, Binary.B2BSN,
      binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754]
  · by_cases hmpos : 0 < m
    · simp only [Binary.normalize, _root_.binary_normalize, hm0, hmpos,
        dite_false, dite_true, ite_false, ite_true]
      apply Binary.binarySingleNaNFloatToB754_standardFloatToBinaryFloatOfNotNaN
    · simp only [Binary.normalize, _root_.binary_normalize, hm0, hmpos,
        dite_false, ite_false]
      apply Binary.binarySingleNaNFloatToB754_standardFloatToBinaryFloatOfNotNaN

private theorem Bplus_toB754 {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y : binary_float prec emax) :
    binarySingleNaNFloatToB754 (Bplus mode x y) =
      ExperimentalSingleNaNArithmetic.Bplus (prec:=prec) (emax:=emax)
        mode (binarySingleNaNFloatToB754 x) (binarySingleNaNFloatToB754 y) := by
  cases x with
  | B754_zero sx =>
      cases y with
      | B754_zero sy =>
          by_cases h : sx = sy
          · simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
              binarySingleNaNFloatToB754, h]
          · cases mode <;>
              simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
                binarySingleNaNFloatToB754, h]
      | B754_infinity sy | B754_nan | B754_finite sy my ey hmy hy =>
          simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binarySingleNaNFloatToB754]
  | B754_infinity sx =>
      cases y with
      | B754_infinity sy =>
          by_cases h : sx = sy <;>
            simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
              binarySingleNaNFloatToB754, h]
      | B754_zero sy | B754_nan | B754_finite sy my ey hmy hy =>
          simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binarySingleNaNFloatToB754]
  | B754_nan =>
      cases y <;>
        simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
          binarySingleNaNFloatToB754]
  | B754_finite sx mx ex hmx hx =>
      cases y with
      | B754_zero sy =>
          simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binarySingleNaNFloatToB754]
      | B754_infinity sy =>
          simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binarySingleNaNFloatToB754]
      | B754_nan =>
          simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binarySingleNaNFloatToB754]
      | B754_finite sy my ey hmy hy =>
          exact normalize_toB754 mode
            (Fplus_naive sx mx ex sy my ey (min ex ey)) (min ex ey)
            (match mode with | RoundingMode.RTN => true | _ => false)

private theorem Bminus_toB754 {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y : binary_float prec emax) :
    binarySingleNaNFloatToB754 (Bminus mode x y) =
      ExperimentalSingleNaNArithmetic.Bminus (prec:=prec) (emax:=emax)
        mode (binarySingleNaNFloatToB754 x) (binarySingleNaNFloatToB754 y) := by
  rw [show Bminus mode x y = Bplus mode x (Bopp y) by rfl,
    Bplus_toB754, Bopp_toB754]
  rfl

private theorem Bldexp_toB754 {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : binary_float prec emax) (k : Int) :
    binarySingleNaNFloatToB754 (Bldexp mode x k) =
      ExperimentalSingleNaNArithmetic.Bldexp (prec:=prec) (emax:=emax)
        mode (binarySingleNaNFloatToB754 x) k := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => rfl
  | B754_finite s m e hm hb =>
      let z := _root_.binary_round (prec:=prec) (emax:=emax) mode s m (e + k)
      have hc := _root_.binary_round_correct (prec:=prec) (emax:=emax)
        mode s m (e + k) hm
      change binarySingleNaNFloatToB754
          (standardFloatToBinarySingleNaNFloat z hc.1) = _root_.SF2B z
      exact binarySingleNaNFloatToB754_standardFloatToBinarySingleNaNFloat z hc.1

theorem Bldexp_Bopp_NE {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) (k : Int) :
    Bldexp RoundingMode.RNE (Bopp x) k = Bopp (Bldexp RoundingMode.RNE x k) := by
  apply toB754_inj
  have href := ExperimentalSingleNaNArithmetic.Bldexp_Bopp_NE
    (prec:=prec) (emax:=emax) (binarySingleNaNFloatToB754 x) k
  have hraw : ExperimentalSingleNaNArithmetic.Bldexp (prec:=prec) (emax:=emax)
        RoundingMode.RNE
        (ExperimentalSingleNaNArithmetic.Bopp_bsn (binarySingleNaNFloatToB754 x)) k =
      ExperimentalSingleNaNArithmetic.Bopp_bsn
        (ExperimentalSingleNaNArithmetic.Bldexp (prec:=prec) (emax:=emax)
          RoundingMode.RNE (binarySingleNaNFloatToB754 x) k) := by
    simpa [wp, Std.Do.PostCond.noThrow, pure,
      ExperimentalSingleNaNArithmetic.Bldexp_Bopp_NE_check] using href trivial
  calc
    binarySingleNaNFloatToB754 (Bldexp RoundingMode.RNE (Bopp x) k) =
        ExperimentalSingleNaNArithmetic.Bldexp (prec:=prec) (emax:=emax)
          RoundingMode.RNE (binarySingleNaNFloatToB754 (Bopp x)) k :=
      Bldexp_toB754 RoundingMode.RNE (Bopp x) k
    _ = ExperimentalSingleNaNArithmetic.Bldexp (prec:=prec) (emax:=emax)
          RoundingMode.RNE
          (ExperimentalSingleNaNArithmetic.Bopp_bsn
            (binarySingleNaNFloatToB754 x)) k := by rw [Bopp_toB754]
    _ = ExperimentalSingleNaNArithmetic.Bopp_bsn
          (ExperimentalSingleNaNArithmetic.Bldexp (prec:=prec) (emax:=emax)
            RoundingMode.RNE (binarySingleNaNFloatToB754 x) k) := hraw
    _ = ExperimentalSingleNaNArithmetic.Bopp_bsn
          (binarySingleNaNFloatToB754 (Bldexp RoundingMode.RNE x k)) := by
      rw [Bldexp_toB754]
    _ = binarySingleNaNFloatToB754 (Bopp (Bldexp RoundingMode.RNE x k)) := by
      rw [Bopp_toB754]

private theorem Bldexp_Bone_spec {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (k : Int) (hmin : 3 - emax - prec ≤ k) (hmax : k < emax) :
    B2R (Bldexp RoundingMode.RNE (Bone (prec:=prec) (emax:=emax)) k) =
        FloatSpec.Core.Raux.bpow 2 k ∧
      is_finite (Bldexp RoundingMode.RNE (Bone (prec:=prec) (emax:=emax)) k) = true ∧
      Bsign (Bldexp RoundingMode.RNE (Bone (prec:=prec) (emax:=emax)) k) = false := by
  have hfmtTrip := FloatSpec.Core.FLT.generic_format_FLT_bpow
    (prec:=prec) (emin:=3 - emax - prec) (beta:=2) (e:=k)
  have hfmt : FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec) (FloatSpec.Core.Raux.bpow 2 k) := by
    simpa [FLT_exp, wp, Std.Do.PostCond.noThrow, pure,
      FloatSpec.Core.Raux.bpow] using
      hfmtTrip ⟨by norm_num, hmin⟩
  have hround := FloatSpec.Core.Generic_fmt.roundR_generic
    (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
    (rnd:=rnd_of_mode RoundingMode.RNE)
    (x:=FloatSpec.Core.Raux.bpow 2 k) (hβ:=by norm_num) hfmt
  have hltTrip := FloatSpec.Core.Raux.bpow_lt 2 k emax (by norm_num) hmax
  have hlt : FloatSpec.Core.Raux.bpow 2 k < FloatSpec.Core.Raux.bpow 2 emax := by
    simpa [FloatSpec.Core.Raux.bpow_lt_check, FloatSpec.Core.Raux.bpow,
      wp, Std.Do.PostCond.noThrow, pure] using hltTrip trivial
  have hbone := Binary.BoneSingle_value_finite_sign (prec:=prec) (emax:=emax)
  have hinput : B2R (Bone (prec:=prec) (emax:=emax)) *
      FloatSpec.Core.Raux.bpow 2 k = FloatSpec.Core.Raux.bpow 2 k := by
    change B754_to_R (binarySingleNaNFloatToB754
      (Binary.BoneSingle (prec:=prec) (emax:=emax))) * _ = _
    rw [hbone.1]
    ring
  have hcond : FloatSpec.Core.Raux.Rlt_bool
      |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
        (rnd_of_mode RoundingMode.RNE)
        (B2R (Bone (prec:=prec) (emax:=emax)) *
          FloatSpec.Core.Raux.bpow 2 k)|
      (FloatSpec.Core.Raux.bpow 2 emax) = true := by
    rw [hinput, hround]
    have hpowpos : 0 < FloatSpec.Core.Raux.bpow 2 k := by
      exact zpow_pos (by norm_num : (0 : ℝ) < 2) k
    rw [abs_of_pos hpowpos]
    simp [FloatSpec.Core.Raux.Rlt_bool, hlt]
  have hc := Bldexp_correct (prec:=prec) (emax:=emax)
    RoundingMode.RNE (Bone (prec:=prec) (emax:=emax)) k
  rw [ite_eq_left hcond] at hc
  exact ⟨hc.1.trans (by rw [hinput, hround]), hc.2.1.trans hbone.2.1,
    hc.2.2.trans hbone.2.2⟩

private theorem Bldexp_Bone_to_raw {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (k : Int) (hmin : 3 - emax - prec ≤ k) (hmax : k < emax) :
    binarySingleNaNFloatToB754
        (Bldexp RoundingMode.RNE (Bone (prec:=prec) (emax:=emax)) k) =
      ExperimentalSingleNaNArithmetic.Bldexp (prec:=prec) (emax:=emax)
        RoundingMode.RNE _root_.Bone k := by
  let r := Bldexp RoundingMode.RNE (Bone (prec:=prec) (emax:=emax)) k
  let z := _root_.binary_round (prec:=prec) (emax:=emax)
    RoundingMode.RNE false 1 k
  have hr := Bldexp_Bone_spec (prec:=prec) (emax:=emax) k hmin hmax
  have hz := ExperimentalSingleNaNArithmetic.binary_round_one_payload
    (prec:=prec) (emax:=emax) RoundingMode.RNE k hmin hmax
  change B2R r = FloatSpec.Core.Raux.bpow 2 k ∧
      is_finite r = true ∧ Bsign r = false at hr
  have hfiniteR : is_finite_SF (B2SF r) = true := by
    have hobs : is_finite_SF (B2SF r) = is_finite r := by
      cases r <;> rfl
    exact hobs.trans hr.2.1
  have hvalueR : SF2R 2 (B2SF r) = FloatSpec.Core.Raux.bpow 2 k := by
    have hobs : SF2R 2 (B2SF r) = B2R r := by
      cases r <;> rfl
    exact hobs.trans hr.1
  have hsignR : sign_SF (B2SF r) = false := by
    have hobs : sign_SF (B2SF r) = Bsign r := by
      cases r <;> rfl
    exact hobs.trans hr.2.2
  have hstd : B2SF r = z :=
    ExperimentalSingleNaNArithmetic.standardFloat_eq_of_valid_finite_sign_value
      prec emax (B2SF r) z
      (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat r)
      hz.1 hfiniteR hz.2.2.1 (hvalueR.trans hz.2.1.symm)
      (hsignR.trans hz.2.2.2.symm)
  calc
    binarySingleNaNFloatToB754
        (Bldexp RoundingMode.RNE (Bone (prec:=prec) (emax:=emax)) k) =
        _root_.SF2B (B2SF r) := by
          change binarySingleNaNFloatToB754 r = _root_.SF2B (B2SF r)
          cases r <;> rfl
    _ = _root_.SF2B z := congrArg _root_.SF2B hstd
    _ = ExperimentalSingleNaNArithmetic.Bldexp (prec:=prec) (emax:=emax)
        RoundingMode.RNE _root_.Bone k := by
          simp [ExperimentalSingleNaNArithmetic.Bldexp, _root_.Bone, _root_.SF2B, z]

noncomputable def Bfrexp {prec emax : Int}
    [Prec_gt_0 prec]
    (x : binary_float prec emax) : binary_float prec emax × Int :=
  match x with
  | BinarySingleNaNFloat.B754_finite s m e hm hb =>
      let core := ExperimentalSingleNaNArithmetic.Ffrexp_core_binary
        (prec:=prec) (emax:=emax) s m e
      have hc := ExperimentalSingleNaNArithmetic.Bfrexp_correct_aux
        (prec:=prec) (emax:=emax) s m e hm hb
      (standardFloatToBinarySingleNaNFloat core.1 hc.1, core.2)
  | x => (x, -2 * emax - prec)

theorem is_nan_Bfrexp {prec emax : Int}
    [Prec_gt_0 prec]
    (x : binary_float prec emax) : is_nan (Bfrexp x).1 = is_nan x := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => rfl
  | B754_finite s m e hm hb =>
      let core := ExperimentalSingleNaNArithmetic.Ffrexp_core_binary
        (prec:=prec) (emax:=emax) s m e
      have hc := ExperimentalSingleNaNArithmetic.Bfrexp_correct_aux
        (prec:=prec) (emax:=emax) s m e hm hb
      change is_nan (standardFloatToBinarySingleNaNFloat core.1 hc.1) = false
      rw [is_nan_eq_internal, Binary.is_nan_standardFloatToBinarySingleNaNFloat]
      simp [core, ExperimentalSingleNaNArithmetic.Ffrexp_core_binary, is_nan_SF]
      split_ifs <;> rfl

theorem Bfrexp_correct {prec emax : Int}
    [Prec_gt_0 prec]
    (x : binary_float prec emax) (hfinite : is_finite_strict x = true) :
    let z := (Bfrexp x).1
    let e := (Bfrexp x).2
    B2R x = B2R z * FloatSpec.Core.Raux.bpow 2 e ∧
      (2 < emax →
        (1 / 2 : ℝ) ≤ |B2R z| ∧ |B2R z| < 1 ∧
        e = FloatSpec.Core.Raux.mag 2 (B2R x)) := by
  cases x with
  | B754_zero s =>
      simp [BinarySingleNaN.is_finite_strict, binarySingleNaNFloatToB754,
        BSN_is_finite_strict] at hfinite
  | B754_infinity s =>
      simp [BinarySingleNaN.is_finite_strict, binarySingleNaNFloatToB754,
        BSN_is_finite_strict] at hfinite
  | B754_nan =>
      simp [BinarySingleNaN.is_finite_strict, binarySingleNaNFloatToB754,
        BSN_is_finite_strict] at hfinite
  | B754_finite s m ex hm hb =>
      let core := ExperimentalSingleNaNArithmetic.Ffrexp_core_binary
        (prec:=prec) (emax:=emax) s m ex
      have hc := ExperimentalSingleNaNArithmetic.Bfrexp_correct_aux
        (prec:=prec) (emax:=emax) s m ex hm hb
      have hvalue : B2R ((Bfrexp
          (BinarySingleNaNFloat.B754_finite s m ex hm hb)).1) = SF2R 2 core.1 := by
        change B2R (standardFloatToBinarySingleNaNFloat core.1 hc.1) = _
        change B754_to_R (binarySingleNaNFloatToB754
          (standardFloatToBinarySingleNaNFloat core.1 hc.1)) = _
        exact Binary.B2R_standardFloatToBinarySingleNaNFloat core.1 hc.1
      have hinput : B2R
          (BinarySingleNaNFloat.B754_finite s m ex hm hb) =
          SF2R 2 (StandardFloat.S754_finite s m ex) := by rfl
      have hexp : (Bfrexp
          (BinarySingleNaNFloat.B754_finite s m ex hm hb)).2 = core.2 := by rfl
      have hdecomp := hc.2.2
      dsimp only
      rw [hvalue, hinput, hexp]
      constructor
      · exact hdecomp
      · intro hmax
        have hnorm := hc.2.1 hmax
        have hz : SF2R 2 core.1 ≠ 0 := by
          intro hz
          rw [hz, abs_zero] at hnorm
          norm_num at hnorm
        have hmag0 : FloatSpec.Core.Raux.mag 2 (SF2R 2 core.1) = 0 := by
          exact (FloatSpec.Core.Raux.mag_unique 2 (SF2R 2 core.1) 0
            (by norm_num)
            (by norm_num; exact hnorm.1)
            (by norm_num; exact hnorm.2)) trivial
        have hmagMul := FloatSpec.Core.Raux.mag_mult_bpow
          2 (SF2R 2 core.1) core.2 (by norm_num) hz
        have hmagEq : FloatSpec.Core.Raux.mag 2
            (SF2R 2 (StandardFloat.S754_finite s m ex)) =
            FloatSpec.Core.Raux.mag 2 (SF2R 2 core.1) + core.2 := by
          rw [hdecomp]
          simpa [FloatSpec.Core.Raux.bpow] using hmagMul
        rw [hmag0] at hmagEq
        exact ⟨hnorm.1, hnorm.2, by omega⟩

private theorem Bfrexp_toB754 {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) :
    (binarySingleNaNFloatToB754 (Bfrexp x).1, (Bfrexp x).2) =
      ExperimentalSingleNaNArithmetic.Bfrexp_bsn (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 x) := by
  cases x with
  | B754_zero s | B754_infinity s | B754_nan => rfl
  | B754_finite s m e hm hb =>
      let core := ExperimentalSingleNaNArithmetic.Ffrexp_core_binary
        (prec:=prec) (emax:=emax) s m e
      have hc := ExperimentalSingleNaNArithmetic.Bfrexp_correct_aux
        (prec:=prec) (emax:=emax) s m e hm hb
      change (binarySingleNaNFloatToB754
          (standardFloatToBinarySingleNaNFloat core.1 hc.1), core.2) =
        (_root_.SF2B core.1, core.2)
      rw [binarySingleNaNFloatToB754_standardFloatToBinarySingleNaNFloat]

theorem Bulp_correct_aux {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    bounded (prec:=prec) (emax:=emax) 1 (3 - emax - prec) = true :=
  ExperimentalSingleNaNArithmetic.Bulp_correct_aux prec emax

noncomputable def Bulp {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | BinarySingleNaNFloat.B754_zero _ =>
      BinarySingleNaNFloat.B754_finite false 1 (3 - emax - prec)
        (by norm_num) (Binary.specFloat_bounded_one_emin (prec:=prec) (emax:=emax))
  | BinarySingleNaNFloat.B754_infinity _ =>
      BinarySingleNaNFloat.B754_infinity false
  | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_finite _ _ e _ _ =>
      let z := _root_.binary_round (prec:=prec) (emax:=emax)
        RoundingMode.RTZ false 1 e
      have hc := _root_.binary_round_correct (prec:=prec) (emax:=emax)
        RoundingMode.RTZ false 1 e (by norm_num)
      standardFloatToBinarySingleNaNFloat z hc.1

private theorem Bulp_toB754 {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) :
    binarySingleNaNFloatToB754 (Bulp x) =
      ExperimentalSingleNaNArithmetic.Bulp (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 x) := by
  cases x with
  | B754_zero s =>
      simp [Bulp, ExperimentalSingleNaNArithmetic.Bulp,
        binarySingleNaNFloatToB754]
  | B754_infinity s =>
      simp [Bulp, ExperimentalSingleNaNArithmetic.Bulp,
        binarySingleNaNFloatToB754]
  | B754_nan =>
      simp [Bulp, ExperimentalSingleNaNArithmetic.Bulp,
        binarySingleNaNFloatToB754]
  | B754_finite s m e hm hb =>
      let z := _root_.binary_round (prec:=prec) (emax:=emax)
        RoundingMode.RTZ false 1 e
      have hc := _root_.binary_round_correct (prec:=prec) (emax:=emax)
        RoundingMode.RTZ false 1 e (by norm_num)
      change binarySingleNaNFloatToB754
          (standardFloatToBinarySingleNaNFloat z hc.1) = _
      rw [binarySingleNaNFloatToB754_standardFloatToBinarySingleNaNFloat]
      simp [ExperimentalSingleNaNArithmetic.Bulp, _root_.binary_normalize,
        binarySingleNaNFloatToB754, z]

theorem is_nan_Bulp {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) : is_nan (Bulp x) = is_nan x := by
  have href := ExperimentalSingleNaNArithmetic.is_nan_Bulp
    (prec:=prec) (emax:=emax) (binarySingleNaNFloatToB754 x)
  rw [← Bulp_toB754 x] at href
  simpa [is_nan, binarySingleNaNFloatToB754] using href

theorem Bulp_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) (hfinite : is_finite x = true) :
    B2R (Bulp x) = FloatSpec.Core.Ulp.ulp 2
        (FLT_exp (3 - emax - prec) prec) (B2R x) ∧
      is_finite (Bulp x) = true ∧ Bsign (Bulp x) = false := by
  have href := ExperimentalSingleNaNArithmetic.Bulp_correct
    (prec:=prec) (emax:=emax) x (by
      simpa [is_finite, binarySingleNaNFloatToB754] using hfinite)
  rw [← Bulp_toB754 x] at href
  simpa [B2R, is_finite, Bsign, binarySingleNaNFloatToB754] using href

theorem is_finite_strict_Bulp {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) :
    is_finite_strict (Bulp x) = is_finite x := by
  have href := ExperimentalSingleNaNArithmetic.is_finite_strict_Bulp
    (prec:=prec) (emax:=emax) x
  rw [← Bulp_toB754 x] at href
  simpa [is_finite_strict, is_finite, binarySingleNaNFloatToB754] using href

noncomputable def Bulp' {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) : binary_float prec emax :=
  Bldexp RoundingMode.RNE (Bone (prec:=prec) (emax:=emax))
    (FLT_exp (3 - emax - prec) prec (Bfrexp x).2)

theorem Bulp'_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (hmax : 2 < emax) (x : binary_float prec emax)
    (hfinite : is_finite x = true) : Bulp' x = Bulp x := by
  have hulp := Bulp_correct (prec:=prec) (emax:=emax) x hfinite
  cases x with
  | B754_zero s =>
      have hsentinel : FLT_exp (3 - emax - prec) prec (-2 * emax - prec) =
          3 - emax - prec := by
        unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
        apply max_eq_right
        have hp := (inferInstance : Prec_gt_0 prec).pos
        omega
      have hsentinel' : FLT_exp (3 - emax - prec) prec (-(2 * emax) - prec) =
          3 - emax - prec := by
        convert hsentinel using 1 <;> ring
      have heminmax : 3 - emax - prec < emax := by
        have hp := (inferInstance : Prec_gt_0 prec).pos
        omega
      have hb := Bldexp_Bone_spec (prec:=prec) (emax:=emax)
        (3 - emax - prec) (le_refl _) heminmax
      have hb' : B2R (Bulp'
            (BinarySingleNaNFloat.B754_zero (prec:=prec) (emax:=emax) s)) =
            FloatSpec.Core.Raux.bpow 2 (3 - emax - prec) ∧
          is_finite (Bulp'
            (BinarySingleNaNFloat.B754_zero (prec:=prec) (emax:=emax) s)) = true ∧
          Bsign (Bulp'
            (BinarySingleNaNFloat.B754_zero (prec:=prec) (emax:=emax) s)) = false := by
        simpa [Bulp', Bfrexp, hsentinel, hsentinel'] using hb
      have hulp0Trip := FloatSpec.Core.FLT.ulp_FLT_0
        (prec:=prec) (emin:=3 - emax - prec) (beta:=2)
      have hulp0 : FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec) 0 =
          FloatSpec.Core.Raux.bpow 2 (3 - emax - prec) := by
        simpa [FLT_exp, wp, Std.Do.PostCond.noThrow, pure,
          FloatSpec.Core.Raux.bpow] using
          hulp0Trip trivial
      apply B2R_Bsign_inj _ _ hb'.2.1 hulp.2.1
      · rw [hb'.1, hulp.1]
        simpa [B2R, binarySingleNaNFloatToB754, B754_to_R] using hulp0.symm
      · rw [hb'.2.2, hulp.2.2]
  | B754_infinity s =>
      simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hfinite
  | B754_nan =>
      simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hfinite
  | B754_finite s m e hm hb =>
      let xf : binary_float prec emax :=
        BinarySingleNaNFloat.B754_finite s m e hm hb
      have hfr := Bfrexp_correct (prec:=prec) (emax:=emax) xf (by rfl)
      have hexp : (Bfrexp xf).2 = FloatSpec.Core.Raux.mag 2 (B2R xf) :=
        (hfr.2 hmax).2.2
      have hxne : B2R xf ≠ 0 := finite_B2R_ne_zero s m e hm hb
      have hmagTrip := FloatSpec.Core.Raux.mag_le_bpow 2 (B2R xf) emax
        (by norm_num) hxne (abs_B2R_lt_emax xf)
      have hmagLe : FloatSpec.Core.Raux.mag 2 (B2R xf) ≤ emax := by
        simpa [wp, Std.Do.PostCond.noThrow, pure] using hmagTrip trivial
      let k := FLT_exp (3 - emax - prec) prec (Bfrexp xf).2
      have hkmin : 3 - emax - prec ≤ k := by
        simp [k, FLT_exp, FloatSpec.Core.FLT.FLT_exp]
      have hkmax : k < emax := by
        unfold k FLT_exp FloatSpec.Core.FLT.FLT_exp
        apply max_lt
        · rw [hexp]
          have hp := (inferInstance : Prec_gt_0 prec).pos
          omega
        · have hp := (inferInstance : Prec_gt_0 prec).pos
          omega
      have hbprime := Bldexp_Bone_spec (prec:=prec) (emax:=emax)
        k hkmin hkmax
      have hbprime' : B2R (Bulp' xf) = FloatSpec.Core.Raux.bpow 2 k ∧
          is_finite (Bulp' xf) = true ∧ Bsign (Bulp' xf) = false := by
        simpa [Bulp', k] using hbprime
      have hulpEq : FloatSpec.Core.Ulp.ulp 2
          (FLT_exp (3 - emax - prec) prec) (B2R xf) =
          FloatSpec.Core.Raux.bpow 2 k := by
        simp [FloatSpec.Core.Ulp.ulp, hxne,
          FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Raux.bpow, k, hexp]
      apply B2R_Bsign_inj _ _ hbprime'.2.1 hulp.2.1
      · rw [hbprime'.1, hulp.1, hulpEq]
      · rw [hbprime'.2.2, hulp.2.2]

noncomputable def Bpred_pos' {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | BinarySingleNaNFloat.B754_finite _ m _ _ _ =>
      let d :=
        if 2 * m == (2 : Nat) ^ prec.toNat then
          Bldexp RoundingMode.RNE (Bone (prec:=prec) (emax:=emax))
            (FLT_exp (3 - emax - prec) prec ((Bfrexp x).2 - 1))
        else
          Bulp' x
      Bminus RoundingMode.RNE x d
  | _ => x

noncomputable def Bsucc' {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | BinarySingleNaNFloat.B754_zero _ =>
      Bldexp RoundingMode.RNE (Bone (prec:=prec) (emax:=emax))
        (3 - emax - prec)
  | BinarySingleNaNFloat.B754_infinity false => x
  | BinarySingleNaNFloat.B754_infinity true => Bopp Bmax_float
  | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_finite false _ _ _ _ =>
      Bplus RoundingMode.RNE x (Bulp x)
  | BinarySingleNaNFloat.B754_finite true _ _ _ _ =>
      Bopp (Bpred_pos' (Bopp x))

noncomputable abbrev Bsucc {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :=
  @Binary.BsuccSingle prec emax _ _

noncomputable abbrev Bpred {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :=
  @Binary.BpredSingle prec emax _ _

theorem Bnormfr_mantissa_correct {prec emax : Int}
    [Prec_lt_emax prec emax]
    (x : binary_float prec emax)
    (hx : (1 / 2 : ℝ) ≤ |B2R x| ∧ |B2R x| < 1) :
    match x with
    | BinarySingleNaNFloat.B754_finite _ m e _ _ =>
        Bnormfr_mantissa x = m ∧
          FloatSpec.Core.Digits.digits2_pos m = prec ∧
          e = -prec
    | _ => False := by
  cases x with
  | B754_zero s =>
      simpa [Bnormfr_mantissa] using
        (_root_.Bnormfr_mantissa_correct
          (BinarySingleNaNFloat.B754_zero (prec:=prec) (emax:=emax) s) (by
            simpa [B2R] using hx))
  | B754_infinity s =>
      simpa [Bnormfr_mantissa] using
        (_root_.Bnormfr_mantissa_correct
          (BinarySingleNaNFloat.B754_infinity (prec:=prec) (emax:=emax) s) (by
            simpa [B2R] using hx))
  | B754_nan =>
      simpa [Bnormfr_mantissa] using
        (_root_.Bnormfr_mantissa_correct
          (BinarySingleNaNFloat.B754_nan (prec:=prec) (emax:=emax)) (by
            simpa [B2R] using hx))
  | B754_finite s m e hm hb =>
      simpa [Bnormfr_mantissa] using
        (_root_.Bnormfr_mantissa_correct
          (BinarySingleNaNFloat.B754_finite s m e hm hb) (by
            simpa [B2R] using hx))

theorem Bone_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    B2R (Bone (prec:=prec) (emax:=emax)) = 1 :=
  (Binary.BoneSingle_value_finite_sign (prec:=prec) (emax:=emax)).1

theorem is_finite_Bone {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    is_finite (Bone (prec:=prec) (emax:=emax)) = true :=
  (Binary.BoneSingle_value_finite_sign (prec:=prec) (emax:=emax)).2.1

theorem Bsign_Bone {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    Bsign (Bone (prec:=prec) (emax:=emax)) = false :=
  (Binary.BoneSingle_value_finite_sign (prec:=prec) (emax:=emax)).2.2

theorem is_finite_strict_Bone {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    is_finite_strict (Bone (prec:=prec) (emax:=emax)) = true := by
  have hv := Bone_correct (prec:=prec) (emax:=emax)
  cases h : Bone (prec:=prec) (emax:=emax) <;>
    simp [is_finite_strict, B2R, binarySingleNaNFloatToB754, B754_to_R,
      BSN_is_finite_strict, h] at hv ⊢

theorem is_nan_Bone {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    is_nan (Bone (prec:=prec) (emax:=emax)) = false := by
  have hs := is_finite_strict_Bone (prec:=prec) (emax:=emax)
  cases h : Bone (prec:=prec) (emax:=emax) <;>
    simp [is_finite_strict, is_nan, binarySingleNaNFloatToB754,
      BSN_is_finite_strict, BSN_is_nan, h] at hs ⊢

theorem is_nan_Bsucc {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) : is_nan (Bsucc x) = is_nan x := by
  have href := Binary.is_nan_BsuccSingle (prec:=prec) (emax:=emax) x
  simpa [Bsucc, is_nan_eq_internal] using href

theorem is_nan_Bpred {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) : is_nan (Bpred x) = is_nan x := by
  have href := Binary.is_nan_BpredSingle (prec:=prec) (emax:=emax) x
  simpa [Bpred, is_nan_eq_internal] using href

theorem Bsucc_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) (hfinite : is_finite x = true) :
    let successor := FloatSpec.Core.Ulp.succ 2
      (FLT_exp (3 - emax - prec) prec) (B2R x)
    if FloatSpec.Core.Raux.Rlt_bool successor
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (Bsucc x) = successor ∧ is_finite (Bsucc x) = true ∧
        Bsign (Bsucc x) = (Bsign x && is_finite_strict x)
    else B2SF (Bsucc x) = StandardFloat.S754_infinity false := by
  have href := ExperimentalSingleNaNArithmetic.Bsucc_correct
    (prec:=prec) (emax:=emax) x (by
      simpa [is_finite, binarySingleNaNFloatToB754] using hfinite)
  dsimp only at href
  rw [← Binary.BsuccSingle_toB754 (prec:=prec) (emax:=emax) x] at href
  simpa [Bsucc, B2R, B2SF, Bsign, is_finite, is_finite_strict,
    B2SF_BSN_binarySingleNaNFloatToB754] using href

theorem Bpred_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) (hfinite : is_finite x = true) :
    let predecessor := FloatSpec.Core.Ulp.pred 2
      (FLT_exp (3 - emax - prec) prec) (B2R x)
    if FloatSpec.Core.Raux.Rlt_bool
        (-FloatSpec.Core.Raux.bpow 2 emax) predecessor then
      B2R (Bpred x) = predecessor ∧ is_finite (Bpred x) = true ∧
        Bsign (Bpred x) = (Bsign x || !is_finite_strict x)
    else B2SF (Bpred x) = StandardFloat.S754_infinity true := by
  have href := ExperimentalSingleNaNArithmetic.Bpred_correct
    (prec:=prec) (emax:=emax) x (by
      simpa [is_finite, binarySingleNaNFloatToB754] using hfinite)
  dsimp only at href
  rw [← Binary.BpredSingle_toB754 (prec:=prec) (emax:=emax) x] at href
  simpa [Bpred, B2R, B2SF, Bsign, is_finite, is_finite_strict,
    B2SF_BSN_binarySingleNaNFloatToB754] using href

private theorem BulpPrime_toB754 {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (hmax : 2 < emax) (x : binary_float prec emax)
    (hfinite : is_finite x = true) :
    binarySingleNaNFloatToB754 (Bulp' x) =
      ExperimentalSingleNaNArithmetic.Bulp' (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 x) := by
  calc
    binarySingleNaNFloatToB754 (Bulp' x) =
        binarySingleNaNFloatToB754 (Bulp x) :=
      congrArg binarySingleNaNFloatToB754 (Bulp'_correct hmax x hfinite)
    _ = ExperimentalSingleNaNArithmetic.Bulp (prec:=prec) (emax:=emax)
          (binarySingleNaNFloatToB754 x) := Bulp_toB754 x
    _ = ExperimentalSingleNaNArithmetic.Bulp' (prec:=prec) (emax:=emax)
          (binarySingleNaNFloatToB754 x) :=
      (ExperimentalSingleNaNArithmetic.Bulp'_correct
        (prec:=prec) (emax:=emax) hmax x (by
          simpa [is_finite, binarySingleNaNFloatToB754] using hfinite)).symm

private theorem BpredPosPrime_toB754 {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (hmax : 2 < emax) (x : binary_float prec emax) :
    binarySingleNaNFloatToB754 (Bpred_pos' x) =
      ExperimentalSingleNaNArithmetic.Bpred_pos' (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 x) := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => rfl
  | B754_finite s m e hm hb =>
      let xf : binary_float prec emax :=
        BinarySingleNaNFloat.B754_finite s m e hm hb
      let raw := B754.B754_finite s m e
      have hfr := Bfrexp_correct (prec:=prec) (emax:=emax) xf (by rfl)
      have hexp : (Bfrexp xf).2 = FloatSpec.Core.Raux.mag 2 (B2R xf) :=
        (hfr.2 hmax).2.2
      have hxne : B2R xf ≠ 0 := finite_B2R_ne_zero s m e hm hb
      have hmagTrip := FloatSpec.Core.Raux.mag_le_bpow 2 (B2R xf) emax
        (by norm_num) hxne (abs_B2R_lt_emax xf)
      have hmagLe : FloatSpec.Core.Raux.mag 2 (B2R xf) ≤ emax := by
        simpa [wp, Std.Do.PostCond.noThrow, pure] using hmagTrip trivial
      let k := FLT_exp (3 - emax - prec) prec ((Bfrexp xf).2 - 1)
      have hkmin : 3 - emax - prec ≤ k := by
        simp [k, FLT_exp, FloatSpec.Core.FLT.FLT_exp]
      have hkmax : k < emax := by
        unfold k FLT_exp FloatSpec.Core.FLT.FLT_exp
        apply max_lt
        · rw [hexp]
          have hp := (inferInstance : Prec_gt_0 prec).pos
          omega
        · have hp := (inferInstance : Prec_gt_0 prec).pos
          omega
      have hfrexp := Bfrexp_toB754 (prec:=prec) (emax:=emax) xf
      have hexpRaw : (Bfrexp xf).2 =
          (ExperimentalSingleNaNArithmetic.Bfrexp_bsn
            (prec:=prec) (emax:=emax) raw).2 := by
        simpa [raw, xf, binarySingleNaNFloatToB754] using congrArg Prod.snd hfrexp
      change binarySingleNaNFloatToB754
          (Bminus RoundingMode.RNE xf
            (if 2 * m == (2 : Nat) ^ prec.toNat then
              Bldexp RoundingMode.RNE (Bone (prec:=prec) (emax:=emax)) k
            else Bulp' xf)) =
        ExperimentalSingleNaNArithmetic.Bminus (prec:=prec) (emax:=emax)
          RoundingMode.RNE raw
          (if 2 * m == (2 : Nat) ^ prec.toNat then
            ExperimentalSingleNaNArithmetic.Bldexp (prec:=prec) (emax:=emax)
              RoundingMode.RNE _root_.Bone
              (FLT_exp (3 - emax - prec) prec
                ((ExperimentalSingleNaNArithmetic.Bfrexp_bsn
                  (prec:=prec) (emax:=emax) raw).2 - 1))
          else ExperimentalSingleNaNArithmetic.Bulp' (prec:=prec) (emax:=emax) raw)
      rw [Bminus_toB754]
      congr 1
      by_cases hboundary : 2 * m == (2 : Nat) ^ prec.toNat
      · rw [ite_eq_left hboundary, ite_eq_left hboundary]
        calc
          binarySingleNaNFloatToB754
              (Bldexp RoundingMode.RNE (Bone (prec:=prec) (emax:=emax)) k) =
              ExperimentalSingleNaNArithmetic.Bldexp (prec:=prec) (emax:=emax)
                RoundingMode.RNE _root_.Bone k :=
            Bldexp_Bone_to_raw k hkmin hkmax
          _ = ExperimentalSingleNaNArithmetic.Bldexp (prec:=prec) (emax:=emax)
                RoundingMode.RNE _root_.Bone
                (FLT_exp (3 - emax - prec) prec
                  ((ExperimentalSingleNaNArithmetic.Bfrexp_bsn
                    (prec:=prec) (emax:=emax) raw).2 - 1)) := by
              rw [← hexpRaw]
      · rw [ite_eq_right hboundary, ite_eq_right hboundary]
        exact BulpPrime_toB754 hmax xf (by rfl)

theorem Bpred_pos'_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (hmax : 2 < emax) (x : binary_float prec emax)
    (hxpos : 0 < B2R x) : Bpred_pos' x = Bpred x := by
  apply toB754_inj
  calc
    binarySingleNaNFloatToB754 (Bpred_pos' x) =
        ExperimentalSingleNaNArithmetic.Bpred_pos' (prec:=prec) (emax:=emax)
          (binarySingleNaNFloatToB754 x) := BpredPosPrime_toB754 hmax x
    _ = ExperimentalSingleNaNArithmetic.Bpred (prec:=prec) (emax:=emax)
          (binarySingleNaNFloatToB754 x) :=
      ExperimentalSingleNaNArithmetic.Bpred_pos'_correct
        (prec:=prec) (emax:=emax) hmax x (by simpa [B2R] using hxpos)
    _ = binarySingleNaNFloatToB754 (Bpred x) :=
      (Binary.BpredSingle_toB754 (prec:=prec) (emax:=emax) x).symm

private theorem BsuccPrime_toB754 {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (hmax : 2 < emax) (x : binary_float prec emax) :
    binarySingleNaNFloatToB754 (Bsucc' x) =
      ExperimentalSingleNaNArithmetic.Bsucc' (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 x) := by
  cases x with
  | B754_zero s =>
      have heminMax : 3 - emax - prec < emax := by
        have hp := (inferInstance : Prec_gt_0 prec).pos
        omega
      simpa [Bsucc', ExperimentalSingleNaNArithmetic.Bsucc',
        binarySingleNaNFloatToB754] using
        (Bldexp_Bone_to_raw (prec:=prec) (emax:=emax)
          (3 - emax - prec) (le_refl _) heminMax)
  | B754_infinity s =>
      cases s
      · rfl
      · simpa [Bsucc', ExperimentalSingleNaNArithmetic.Bsucc', Bmax_float,
          Binary.BmaxFloatSingle, ExperimentalSingleNaNArithmetic.Bmax_float,
          binarySingleNaNFloatToB754] using
          (Bopp_toB754 (Bmax_float (prec:=prec) (emax:=emax)))
  | B754_nan => rfl
  | B754_finite s m e hm hb =>
      let xf : binary_float prec emax :=
        BinarySingleNaNFloat.B754_finite s m e hm hb
      cases s
      · change binarySingleNaNFloatToB754
            (Bplus RoundingMode.RNE xf (Bulp xf)) =
          ExperimentalSingleNaNArithmetic.Bplus (prec:=prec) (emax:=emax)
            RoundingMode.RNE (binarySingleNaNFloatToB754 xf)
              (ExperimentalSingleNaNArithmetic.Bulp (prec:=prec) (emax:=emax)
                (binarySingleNaNFloatToB754 xf))
        rw [Bplus_toB754, Bulp_toB754]
      · change binarySingleNaNFloatToB754
            (Bopp (Bpred_pos' (Bopp xf))) =
          ExperimentalSingleNaNArithmetic.Bopp_bsn
            (ExperimentalSingleNaNArithmetic.Bpred_pos' (prec:=prec) (emax:=emax)
              (ExperimentalSingleNaNArithmetic.Bopp_bsn
                (binarySingleNaNFloatToB754 xf)))
        rw [Bopp_toB754, BpredPosPrime_toB754 hmax, Bopp_toB754]

theorem Bsucc'_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (hmax : 2 < emax) (x : binary_float prec emax)
    (hfinite : is_finite x = true) : Bsucc' x = Bsucc x := by
  apply toB754_inj
  calc
    binarySingleNaNFloatToB754 (Bsucc' x) =
        ExperimentalSingleNaNArithmetic.Bsucc' (prec:=prec) (emax:=emax)
          (binarySingleNaNFloatToB754 x) := BsuccPrime_toB754 hmax x
    _ = ExperimentalSingleNaNArithmetic.Bsucc (prec:=prec) (emax:=emax)
          (binarySingleNaNFloatToB754 x) :=
      ExperimentalSingleNaNArithmetic.Bsucc'_correct
        (prec:=prec) (emax:=emax) hmax x (by
          simpa [is_finite, binarySingleNaNFloatToB754] using hfinite)
    _ = binarySingleNaNFloatToB754 (Bsucc x) :=
      (Binary.BsuccSingle_toB754 (prec:=prec) (emax:=emax) x).symm

end BinarySingleNaN

namespace FloatSpec.IEEE754.BinarySingleNaN.Source

/-! Source-mode arithmetic facade.  The Coq section exposes only the precision
and exponent-range hypotheses; the canonical FLT validity and monotonicity
instances are resolved by the implementation and do not become proof payloads
in this API. -/

-- Source ID: IEEE754/BinarySingleNaN.v:Bmult:43454
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bmult
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bmult:43454`. -/
noncomputable def Bmult {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y : _root_.BinarySingleNaN.binary_float prec emax) :
    _root_.BinarySingleNaN.binary_float prec emax :=
  _root_.BinarySingleNaN.Bmult m.toRoundingMode x y

-- Source ID: IEEE754/BinarySingleNaN.v:Bplus:53668
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bplus
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bplus:53668`. -/
noncomputable def Bplus {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y : _root_.BinarySingleNaN.binary_float prec emax) :
    _root_.BinarySingleNaN.binary_float prec emax :=
  _root_.BinarySingleNaN.Bplus m.toRoundingMode x y

-- Source ID: IEEE754/BinarySingleNaN.v:Bminus:56616
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bminus
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bminus:56616`. -/
noncomputable def Bminus {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y : _root_.BinarySingleNaN.binary_float prec emax) :
    _root_.BinarySingleNaN.binary_float prec emax :=
  _root_.BinarySingleNaN.Bminus m.toRoundingMode x y

-- Source ID: IEEE754/BinarySingleNaN.v:Bfma:58551
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bfma
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bfma:58551`. -/
noncomputable def Bfma {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y z : _root_.BinarySingleNaN.binary_float prec emax) :
    _root_.BinarySingleNaN.binary_float prec emax :=
  _root_.BinarySingleNaN.Bfma m.toRoundingMode x y z

-- Source ID: IEEE754/BinarySingleNaN.v:Bdiv:66074
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bdiv
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bdiv:66074`. -/
noncomputable def Bdiv {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y : _root_.BinarySingleNaN.binary_float prec emax) :
    _root_.BinarySingleNaN.binary_float prec emax :=
  _root_.BinarySingleNaN.Bdiv m.toRoundingMode x y

-- Source ID: IEEE754/BinarySingleNaN.v:Bsqrt:70887
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bsqrt
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bsqrt:70887`. -/
noncomputable def Bsqrt {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x : _root_.BinarySingleNaN.binary_float prec emax) :
    _root_.BinarySingleNaN.binary_float prec emax :=
  _root_.BinarySingleNaN.Bsqrt m.toRoundingMode x

-- Source ID: IEEE754/BinarySingleNaN.v:Bmult_correct:44194
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bmult_correct
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bmult_correct:44194`. -/
theorem Bmult_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y : _root_.BinarySingleNaN.binary_float prec emax) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (round_mode m)
            (_root_.BinarySingleNaN.B2R x * _root_.BinarySingleNaN.B2R y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      _root_.BinarySingleNaN.B2R (Bmult m x y) =
          FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (round_mode m)
              (_root_.BinarySingleNaN.B2R x * _root_.BinarySingleNaN.B2R y) ∧
      _root_.BinarySingleNaN.is_finite (Bmult m x y) =
          (_root_.BinarySingleNaN.is_finite x &&
            _root_.BinarySingleNaN.is_finite y) ∧
      (_root_.BinarySingleNaN.is_nan (Bmult m x y) = false →
        _root_.BinarySingleNaN.Bsign (Bmult m x y) =
          Bool.xor (_root_.BinarySingleNaN.Bsign x)
            (_root_.BinarySingleNaN.Bsign y))
    else
      _root_.BinarySingleNaN.B2SF (Bmult m x y) =
        _root_.bsn_binary_overflow (prec:=prec) (emax:=emax)
          m.toRoundingMode
          (Bool.xor (_root_.BinarySingleNaN.Bsign x)
            (_root_.BinarySingleNaN.Bsign y)) := by
  rw [round_mode_eq_rnd_of_mode]
  simpa only [Bmult] using
    (_root_.BinarySingleNaN.Bmult_correct (prec:=prec) (emax:=emax)
      m.toRoundingMode x y)

-- Source ID: IEEE754/BinarySingleNaN.v:Bplus_correct:54285
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bplus_correct
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bplus_correct:54285`. -/
theorem Bplus_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y : _root_.BinarySingleNaN.binary_float prec emax)
    (hx : _root_.BinarySingleNaN.is_finite x = true)
    (hy : _root_.BinarySingleNaN.is_finite y = true) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (round_mode m)
            (_root_.BinarySingleNaN.B2R x + _root_.BinarySingleNaN.B2R y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      _root_.BinarySingleNaN.B2R (Bplus m x y) =
          FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (round_mode m)
              (_root_.BinarySingleNaN.B2R x + _root_.BinarySingleNaN.B2R y) ∧
      _root_.BinarySingleNaN.is_finite (Bplus m x y) = true ∧
      _root_.BinarySingleNaN.Bsign (Bplus m x y) =
        _root_.binaryPlusResultSign m.toRoundingMode
          (_root_.BinarySingleNaN.Bsign x) (_root_.BinarySingleNaN.Bsign y)
          (_root_.BinarySingleNaN.B2R x + _root_.BinarySingleNaN.B2R y)
    else
      _root_.BinarySingleNaN.B2SF (Bplus m x y) =
          _root_.bsn_binary_overflow (prec:=prec) (emax:=emax)
            m.toRoundingMode (_root_.BinarySingleNaN.Bsign x) ∧
        _root_.BinarySingleNaN.Bsign x = _root_.BinarySingleNaN.Bsign y := by
  rw [round_mode_eq_rnd_of_mode]
  simpa only [Bplus] using
    (_root_.BinarySingleNaN.Bplus_correct (prec:=prec) (emax:=emax)
      m.toRoundingMode x y hx hy)

-- Source ID: IEEE754/BinarySingleNaN.v:Bminus_correct:57333
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bminus_correct
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bminus_correct:57333`. -/
theorem Bminus_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y : _root_.BinarySingleNaN.binary_float prec emax)
    (hx : _root_.BinarySingleNaN.is_finite x = true)
    (hy : _root_.BinarySingleNaN.is_finite y = true) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (round_mode m)
            (_root_.BinarySingleNaN.B2R x - _root_.BinarySingleNaN.B2R y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      _root_.BinarySingleNaN.B2R (Bminus m x y) =
          FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (round_mode m)
              (_root_.BinarySingleNaN.B2R x - _root_.BinarySingleNaN.B2R y) ∧
      _root_.BinarySingleNaN.is_finite (Bminus m x y) = true ∧
      _root_.BinarySingleNaN.Bsign (Bminus m x y) =
        _root_.binaryMinusResultSign m.toRoundingMode
          (_root_.BinarySingleNaN.Bsign x) (_root_.BinarySingleNaN.Bsign y)
          (_root_.BinarySingleNaN.B2R x - _root_.BinarySingleNaN.B2R y)
    else
      _root_.BinarySingleNaN.B2SF (Bminus m x y) =
          _root_.bsn_binary_overflow (prec:=prec) (emax:=emax)
            m.toRoundingMode (_root_.BinarySingleNaN.Bsign x) ∧
        _root_.BinarySingleNaN.Bsign x = !(_root_.BinarySingleNaN.Bsign y) := by
  rw [round_mode_eq_rnd_of_mode]
  simpa only [Bminus] using
    (_root_.BinarySingleNaN.Bminus_correct (prec:=prec) (emax:=emax)
      m.toRoundingMode x y hx hy)

-- Source ID: IEEE754/BinarySingleNaN.v:Bfma_correct:60206
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bfma_correct
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bfma_correct:60206`. -/
theorem Bfma_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y z : _root_.BinarySingleNaN.binary_float prec emax)
    (hx : _root_.BinarySingleNaN.is_finite x = true)
    (hy : _root_.BinarySingleNaN.is_finite y = true)
    (hz : _root_.BinarySingleNaN.is_finite z = true) :
    let res := _root_.BinarySingleNaN.B2R x *
      _root_.BinarySingleNaN.B2R y + _root_.BinarySingleNaN.B2R z
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (round_mode m) res|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      _root_.BinarySingleNaN.B2R (Bfma m x y z) =
          FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (round_mode m) res ∧
      _root_.BinarySingleNaN.is_finite (Bfma m x y z) = true ∧
      _root_.BinarySingleNaN.Bsign (Bfma m x y z) =
        _root_.BinarySingleNaN.binaryFmaResultSign m.toRoundingMode x y z res
    else
      _root_.BinarySingleNaN.B2SF (Bfma m x y z) =
        _root_.bsn_binary_overflow (prec:=prec) (emax:=emax)
          m.toRoundingMode (FloatSpec.Core.Raux.Rlt_bool res 0) := by
  rw [round_mode_eq_rnd_of_mode]
  simpa only [Bfma] using
    (_root_.BinarySingleNaN.Bfma_correct (prec:=prec) (emax:=emax)
      m.toRoundingMode x y z hx hy hz)

-- Source ID: IEEE754/BinarySingleNaN.v:Bdiv_correct:66775
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bdiv_correct
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bdiv_correct:66775`. -/
theorem Bdiv_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y : _root_.BinarySingleNaN.binary_float prec emax)
    (hy : _root_.BinarySingleNaN.B2R y ≠ 0) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (round_mode m)
            (_root_.BinarySingleNaN.B2R x / _root_.BinarySingleNaN.B2R y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      _root_.BinarySingleNaN.B2R (Bdiv m x y) =
          FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (round_mode m)
              (_root_.BinarySingleNaN.B2R x / _root_.BinarySingleNaN.B2R y) ∧
      _root_.BinarySingleNaN.is_finite (Bdiv m x y) =
          _root_.BinarySingleNaN.is_finite x ∧
      (_root_.BinarySingleNaN.is_nan (Bdiv m x y) = false →
        _root_.BinarySingleNaN.Bsign (Bdiv m x y) =
          Bool.xor (_root_.BinarySingleNaN.Bsign x)
            (_root_.BinarySingleNaN.Bsign y))
    else
      _root_.BinarySingleNaN.B2SF (Bdiv m x y) =
        _root_.bsn_binary_overflow (prec:=prec) (emax:=emax)
          m.toRoundingMode
          (Bool.xor (_root_.BinarySingleNaN.Bsign x)
            (_root_.BinarySingleNaN.Bsign y)) := by
  rw [round_mode_eq_rnd_of_mode]
  simpa only [Bdiv] using
    (_root_.BinarySingleNaN.Bdiv_correct (prec:=prec) (emax:=emax)
      m.toRoundingMode x y hy)

-- Source ID: IEEE754/BinarySingleNaN.v:Bsqrt_correct_aux:67779
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bsqrt_correct_aux
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bsqrt_correct_aux:67779`. -/
theorem Bsqrt_correct_aux {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (mx : FloatSpec.Core.Zaux.Positive) (ex : Int)
    (Hx : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mx) ex = true) :
    let input := F2R
      (FloatSpec.Core.Defs.FlocqFloat.mk
        (FloatSpec.Core.Zaux.positiveToNat mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2)
    let result := _root_.SFsqrt_core_binary prec emax
      (FloatSpec.Core.Zaux.positiveToNat mx : Int) ex
    let z := _root_.binary_round_aux (prec:=prec) (emax:=emax)
      m.toRoundingMode false result.1 result.2.1 result.2.2
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      SF2R 2 z = FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (round_mode m)
          (Real.sqrt input) ∧
      is_finite_SF z = true ∧ sign_SF z = false := by
  simpa only [round_mode] using
    (_root_.BinarySingleNaN.Bsqrt_correct_aux (prec:=prec) (emax:=emax)
      m.toRoundingMode mx ex Hx)

-- Source ID: IEEE754/BinarySingleNaN.v:Bsqrt_correct:71164
-- Target: FloatSpec.IEEE754.BinarySingleNaN.Source.Bsqrt_correct
/-- Source ID: `IEEE754/BinarySingleNaN.v:Bsqrt_correct:71164`. -/
theorem Bsqrt_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x : _root_.BinarySingleNaN.binary_float prec emax) :
    _root_.BinarySingleNaN.B2R (Bsqrt m x) =
        FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (round_mode m)
            (Real.sqrt (_root_.BinarySingleNaN.B2R x)) ∧
    _root_.BinarySingleNaN.is_finite (Bsqrt m x) =
      (match x with
      | _root_.BinarySingleNaNFloat.B754_zero _ => true
      | _root_.BinarySingleNaNFloat.B754_finite false _ _ _ _ => true
      | _ => false) ∧
    (_root_.BinarySingleNaN.is_nan (Bsqrt m x) = false →
      _root_.BinarySingleNaN.Bsign (Bsqrt m x) =
        _root_.BinarySingleNaN.Bsign x) := by
  rw [round_mode_eq_rnd_of_mode]
  exact _root_.BinarySingleNaN.Bsqrt_correct (prec:=prec) (emax:=emax)
    m.toRoundingMode x

end FloatSpec.IEEE754.BinarySingleNaN.Source
