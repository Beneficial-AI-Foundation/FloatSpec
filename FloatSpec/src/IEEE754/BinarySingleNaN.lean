-- Binary single NaN operations
-- Translated from Coq file: flocq/src/IEEE754/BinarySingleNaN.v

import FloatSpec.src.IEEE754.Binary
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Div
import FloatSpec.src.Calc.Round
import FloatSpec.src.Calc.Sqrt
import Init.Data.Float
import Std.Do.Triple
import Std.Tactic.Do
import Mathlib.Data.Real.Basic
import Batteries.Data.Float.Lemmas

open Real
open Std.Do

variable (prec emax : Int)
variable [Prec_gt_0 prec]
variable [Prec_lt_emax prec emax]

-- Binary float with single NaN representation
inductive B754 where
  | B754_zero (s : Bool) : B754
  | B754_infinity (s : Bool) : B754
  | B754_nan : B754
  | B754_finite (s : Bool) (m : Nat) (e : Int) : B754

-- Conversion to real number
noncomputable def B754_to_R (x : B754) : ℝ :=
  match x with
  | B754.B754_finite s m e =>
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (if s then -(m : Int) else (m : Int)) e : FloatSpec.Core.Defs.FlocqFloat 2)
  | _ => 0

-- Bridge from Binary754 to single-NaN binary (Coq: B2BSN)
def B2BSN {prec emax} (x : Binary754 prec emax) : B754 :=
  match x.val with
  | FullFloat.F754_finite s m e => B754.B754_finite s m e
  | FullFloat.F754_infinity s => B754.B754_infinity s
  | FullFloat.F754_zero s => B754.B754_zero s
  | FullFloat.F754_nan _ _ => B754.B754_nan

-- View a single-NaN binary into the standard IEEE 754 float
def B2SF_BSN (x : B754) : StandardFloat :=
  match x with
  | B754.B754_finite s m e => StandardFloat.S754_finite s m e
  | B754.B754_infinity s => StandardFloat.S754_infinity s
  | B754.B754_zero s => StandardFloat.S754_zero s
  | B754.B754_nan => StandardFloat.S754_nan

-- Bridge from StandardFloat to BinarySingleNaN (Coq: SF2B)
def SF2B (x : StandardFloat) : B754 :=
  match x with
  | StandardFloat.S754_finite s m e => B754.B754_finite s m e
  | StandardFloat.S754_infinity s => B754.B754_infinity s
  | StandardFloat.S754_zero s => B754.B754_zero s
  | StandardFloat.S754_nan => B754.B754_nan

-- Total bridge from StandardFloat to BinarySingleNaN (Coq: SF2B')
def SF2B' {prec emax : Int} (x : StandardFloat) : B754 :=
  match x with
  | StandardFloat.S754_zero s => B754.B754_zero s
  | StandardFloat.S754_infinity s => B754.B754_infinity s
  | StandardFloat.S754_nan => B754.B754_nan
  | StandardFloat.S754_finite s m e =>
      if bounded (prec:=prec) (emax:=emax) m e then
        B754.B754_finite s m e
      else
        B754.B754_nan

-- Coq's `B754_finite` constructor carries this proof.  The local raw `B754`
-- type is permissive, so exact `SF2B'` roundtrips must quantify over this view.
def B754_bounded {prec emax : Int} (x : B754) : Prop :=
  match x with
  | B754.B754_finite _ m e => bounded (prec:=prec) (emax:=emax) m e = true
  | B754.B754_zero _ => Unit = Unit
  | B754.B754_infinity _ => Unit = Unit
  | B754.B754_nan => Unit = Unit

-- Coq: SF2B'_B2SF
theorem SF2B'_B2SF {prec emax : Int}
    (x : { x : B754 // B754_bounded (prec:=prec) (emax:=emax) x }) :
    SF2B' (prec:=prec) (emax:=emax) (B2SF_BSN x.val) = x.val := by
  rcases x with ⟨x, hx⟩
  cases x <;> simp [SF2B', B2SF_BSN, B754_bounded] at hx ⊢
  exact hx

private theorem positiveToNat_pos_bsn (p : FloatSpec.Core.Zaux.Positive) :
    0 < FloatSpec.Core.Zaux.positiveToNat p := by
  induction p with
  | xH => simp [FloatSpec.Core.Zaux.positiveToNat]
  | xO p hp => simp [FloatSpec.Core.Zaux.positiveToNat, hp]
  | xI p hp => simp [FloatSpec.Core.Zaux.positiveToNat]

-- Coq `BinarySingleNaN.v:binary_float`, kept separate from the permissive
-- raw `B754` compatibility surface above. Coq uses a `positive` mantissa and
-- its `bounded` notation is `SpecFloat.bounded`, i.e. canonical mantissa plus
-- the upper exponent bound.
inductive BinarySingleNaNFloat (prec emax : Int) where
  | B754_zero (s : Bool) : BinarySingleNaNFloat prec emax
  | B754_infinity (s : Bool) : BinarySingleNaNFloat prec emax
  | B754_nan : BinarySingleNaNFloat prec emax
  | B754_finite (s : Bool) (m : Nat) (e : Int) :
      0 < m →
      specFloat_bounded (prec:=prec) (emax:=emax) m e = true →
        BinarySingleNaNFloat prec emax

-- Compatibility validity check for the Coq-shaped Binary carrier. Since
-- `Binary.binary_float` finite constructors now carry `specFloat_bounded`, this
-- predicate is derivable for every Binary value.
def validBinaryFloatAsSingleNaN {prec emax : Int} (x : binary_float prec emax) : Bool :=
  match x with
  | binary_float.B754_finite _ m e _ =>
      specFloat_bounded (prec:=prec) (emax:=emax)
        (FloatSpec.Core.Zaux.positiveToNat m) e
  | binary_float.B754_zero _ => true
  | binary_float.B754_infinity _ => true
  | binary_float.B754_nan _ _ _ => true

theorem validBinaryFloatAsSingleNaN_true {prec emax : Int}
    (x : binary_float prec emax) :
    validBinaryFloatAsSingleNaN (prec:=prec) (emax:=emax) x = true := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan s payload hPayload => rfl
  | B754_finite s m e hBounded =>
      simpa [validBinaryFloatAsSingleNaN] using hBounded

-- Coq `Binary.v:B2BSN`, on the proof-carrying Binary and SingleNaN carriers.
-- Binary NaN signs/payloads collapse to the unique SingleNaN constructor;
-- finite boundedness evidence is passed through unchanged.
def binaryFloatToBinarySingleNaNFloat {prec emax : Int}
    (x : binary_float prec emax) :
    BinarySingleNaNFloat prec emax :=
  match x with
  | binary_float.B754_zero s =>
      BinarySingleNaNFloat.B754_zero (prec:=prec) (emax:=emax) s
  | binary_float.B754_infinity s =>
      BinarySingleNaNFloat.B754_infinity (prec:=prec) (emax:=emax) s
  | binary_float.B754_nan _ _ _ =>
      BinarySingleNaNFloat.B754_nan (prec:=prec) (emax:=emax)
  | binary_float.B754_finite s m e hBounded =>
      BinarySingleNaNFloat.B754_finite (prec:=prec) (emax:=emax) s
        (FloatSpec.Core.Zaux.positiveToNat m) e (positiveToNat_pos_bsn m) hBounded

-- Single-NaN validity for `StandardFloat`: finite values must be bounded,
-- while zero, infinity, and the single NaN are always valid. This mirrors the
-- `valid_binary` predicate consumed by upstream `SF2B`.
def validBinarySingleNaNStandardFloat {prec emax : Int} (x : StandardFloat) : Bool :=
  match x with
  | StandardFloat.S754_finite _ m e =>
      decide (0 < m) && specFloat_bounded (prec:=prec) (emax:=emax) m e
  | StandardFloat.S754_zero _ => true
  | StandardFloat.S754_infinity _ => true
  | StandardFloat.S754_nan => true

-- Coq `SF2B` on the proof-carrying SingleNaN carrier.
def standardFloatToBinarySingleNaNFloat {prec emax : Int} (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true) :
    BinarySingleNaNFloat prec emax :=
  match x with
  | StandardFloat.S754_finite s m e =>
      have h' : decide (0 < m) = true ∧
          specFloat_bounded (prec:=prec) (emax:=emax) m e = true := by
        simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hx
      BinarySingleNaNFloat.B754_finite (prec:=prec) (emax:=emax) s m e
        (of_decide_eq_true h'.1) h'.2
  | StandardFloat.S754_infinity s =>
      BinarySingleNaNFloat.B754_infinity (prec:=prec) (emax:=emax) s
  | StandardFloat.S754_zero s =>
      BinarySingleNaNFloat.B754_zero (prec:=prec) (emax:=emax) s
  | StandardFloat.S754_nan =>
      BinarySingleNaNFloat.B754_nan (prec:=prec) (emax:=emax)

-- Coq `SF2B'` on the proof-carrying SingleNaN carrier.
def standardFloatToBinarySingleNaNFloat' {prec emax : Int} (x : StandardFloat) :
    BinarySingleNaNFloat prec emax :=
  match x with
  | StandardFloat.S754_zero s =>
      BinarySingleNaNFloat.B754_zero (prec:=prec) (emax:=emax) s
  | StandardFloat.S754_infinity s =>
      BinarySingleNaNFloat.B754_infinity (prec:=prec) (emax:=emax) s
  | StandardFloat.S754_nan =>
      BinarySingleNaNFloat.B754_nan (prec:=prec) (emax:=emax)
  | StandardFloat.S754_finite s m e =>
      if h : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
          (StandardFloat.S754_finite s m e) = true then
        standardFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
          (StandardFloat.S754_finite s m e) h
      else
        BinarySingleNaNFloat.B754_nan (prec:=prec) (emax:=emax)

-- Coq `B2SF` on the proof-carrying SingleNaN carrier.
def binarySingleNaNFloatToStandardFloat {prec emax : Int}
    (x : BinarySingleNaNFloat prec emax) : StandardFloat :=
  match x with
  | BinarySingleNaNFloat.B754_finite s m e _ _ => StandardFloat.S754_finite s m e
  | BinarySingleNaNFloat.B754_infinity s => StandardFloat.S754_infinity s
  | BinarySingleNaNFloat.B754_zero s => StandardFloat.S754_zero s
  | BinarySingleNaNFloat.B754_nan => StandardFloat.S754_nan

-- Erase the proof-carrying carrier back to the historical raw `B754`.
def binarySingleNaNFloatToB754 {prec emax : Int}
    (x : BinarySingleNaNFloat prec emax) : B754 :=
  match x with
  | BinarySingleNaNFloat.B754_finite s m e _ _ => B754.B754_finite s m e
  | BinarySingleNaNFloat.B754_infinity s => B754.B754_infinity s
  | BinarySingleNaNFloat.B754_zero s => B754.B754_zero s
  | BinarySingleNaNFloat.B754_nan => B754.B754_nan

-- Raw erasure of the Coq-shaped total `SF2B'` path. This intentionally does
-- not replace the historical range-only `SF2B'` compatibility API above.
def SF2BSpec' {prec emax : Int} (x : StandardFloat) : B754 :=
  binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
    (standardFloatToBinarySingleNaNFloat' (prec:=prec) (emax:=emax) x)

theorem binaryFloatToBinarySingleNaNFloat_nan {prec emax : Int}
    (s : Bool) (payload : FloatSpec.Core.Zaux.Positive)
    (hPayload : nan_pl prec payload = true) :
    binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
      (binary_float.B754_nan (prec:=prec) (emax:=emax) s payload hPayload) =
        BinarySingleNaNFloat.B754_nan (prec:=prec) (emax:=emax) := by
  rfl

theorem binarySingleNaNFloatToB754_binaryFloatToBinarySingleNaNFloat
    {prec emax : Int} (x : binary_float prec emax) :
    binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
      (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x) =
        match x with
        | binary_float.B754_zero s => B754.B754_zero s
        | binary_float.B754_infinity s => B754.B754_infinity s
        | binary_float.B754_nan _ _ _ => B754.B754_nan
        | binary_float.B754_finite s m e _ =>
            B754.B754_finite s (FloatSpec.Core.Zaux.positiveToNat m) e := by
  cases x <;> simp [binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754]

theorem binarySingleNaNFloatToStandardFloat_standardFloatToBinarySingleNaNFloat
    {prec emax : Int} (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true) :
    binarySingleNaNFloatToStandardFloat (prec:=prec) (emax:=emax)
      (standardFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x hx) = x := by
  cases x <;> rfl

-- Coq `valid_binary_B2SF` on the proof-carrying SingleNaN carrier.
theorem validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat
    {prec emax : Int} (x : BinarySingleNaNFloat prec emax) :
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
      (binarySingleNaNFloatToStandardFloat (prec:=prec) (emax:=emax) x) = true := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => rfl
  | B754_finite s m e hPos hBounded =>
      simp [binarySingleNaNFloatToStandardFloat,
        validBinarySingleNaNStandardFloat, hPos, hBounded]

-- Coq `SF2B_B2SF_valid` on the proof-carrying SingleNaN carrier.
theorem standardFloatToBinarySingleNaNFloat_binarySingleNaNFloatToStandardFloat
    {prec emax : Int} (x : BinarySingleNaNFloat prec emax) :
    standardFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
      (binarySingleNaNFloatToStandardFloat (prec:=prec) (emax:=emax) x)
      (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat
        (prec:=prec) (emax:=emax) x) = x := by
  cases x <;> simp [standardFloatToBinarySingleNaNFloat,
    binarySingleNaNFloatToStandardFloat]

theorem standardFloatToBinarySingleNaNFloat'_binarySingleNaNFloatToStandardFloat
    {prec emax : Int} (x : BinarySingleNaNFloat prec emax) :
    standardFloatToBinarySingleNaNFloat' (prec:=prec) (emax:=emax)
      (binarySingleNaNFloatToStandardFloat (prec:=prec) (emax:=emax) x) = x := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => rfl
  | B754_finite s m e hPos hBounded =>
      simp [standardFloatToBinarySingleNaNFloat',
        standardFloatToBinarySingleNaNFloat, binarySingleNaNFloatToStandardFloat,
        validBinarySingleNaNStandardFloat, hPos, hBounded]

theorem B754_bounded_binarySingleNaNFloatToB754 {prec emax : Int}
    (x : BinarySingleNaNFloat prec emax) :
    B754_bounded (prec:=prec) (emax:=emax)
      (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => rfl
  | B754_finite s m e hPos hBounded =>
      simpa [binarySingleNaNFloatToB754, B754_bounded] using
        range_bounded_of_specFloat_bounded (prec:=prec) (emax:=emax) m e hPos hBounded

theorem B2SF_BSN_binarySingleNaNFloatToB754 {prec emax : Int}
    (x : BinarySingleNaNFloat prec emax) :
    B2SF_BSN (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) =
      binarySingleNaNFloatToStandardFloat (prec:=prec) (emax:=emax) x := by
  cases x <;> rfl

theorem binarySingleNaNFloatToB754_standardFloatToBinarySingleNaNFloat
    {prec emax : Int} (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true) :
    binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
      (standardFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x hx) = SF2B x := by
  cases x <;> simp [standardFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754, SF2B]

theorem binarySingleNaNFloatToB754_standardFloatToBinarySingleNaNFloat'
    {prec emax : Int} (x : StandardFloat) :
    binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
      (standardFloatToBinarySingleNaNFloat' (prec:=prec) (emax:=emax) x) =
        SF2BSpec' (prec:=prec) (emax:=emax) x := by
  rfl

-- Coq: SFnormfr_mantissa
def SFnormfr_mantissa (prec : Int) (x : StandardFloat) : Nat :=
  match x with
  | StandardFloat.S754_finite _ m e =>
      if e == -prec then m else 0
  | _ => 0

namespace BinarySingleNaNFloat

-- Coq: Bnormfr_mantissa := SFnormfr_mantissa prec (B2SF x).
def Bnormfr_mantissa {prec emax : Int}
    (x : BinarySingleNaNFloat prec emax) : Nat :=
  SFnormfr_mantissa prec
    (binarySingleNaNFloatToStandardFloat (prec:=prec) (emax:=emax) x)

end BinarySingleNaNFloat

-- Coq: Bnormfr_mantissa_correct
theorem Bnormfr_mantissa_correct {prec emax : Int}
    [Prec_lt_emax prec emax]
    (x : BinarySingleNaNFloat prec emax)
    (hx :
      (1 / 2 : ℝ) ≤
          |SF2R 2 (binarySingleNaNFloatToStandardFloat
            (prec:=prec) (emax:=emax) x)| ∧
        |SF2R 2 (binarySingleNaNFloatToStandardFloat
            (prec:=prec) (emax:=emax) x)| < 1) :
    match x with
    | BinarySingleNaNFloat.B754_finite _ m e _ _ =>
        BinarySingleNaNFloat.Bnormfr_mantissa x = m ∧
          FloatSpec.Core.Digits.digits2_pos m = prec ∧
          e = -prec
    | _ => False := by
  cases x with
  | B754_zero s =>
      norm_num [binarySingleNaNFloatToStandardFloat, SF2R] at hx
  | B754_infinity s =>
      norm_num [binarySingleNaNFloatToStandardFloat, SF2R] at hx
  | B754_nan =>
      norm_num [binarySingleNaNFloatToStandardFloat, SF2R] at hx
  | B754_finite s m e hm_pos hbounded =>
      have hmag0 :
          FloatSpec.Core.Raux.mag 2
            (SF2R 2 (binarySingleNaNFloatToStandardFloat
              (prec:=prec) (emax:=emax)
              (BinarySingleNaNFloat.B754_finite s m e hm_pos hbounded))) = 0 := by
        have hlow :
            ((2 : ℝ) ^ ((0 : Int) - 1)) ≤
              |SF2R 2 (binarySingleNaNFloatToStandardFloat
                (prec:=prec) (emax:=emax)
                (BinarySingleNaNFloat.B754_finite s m e hm_pos hbounded))| := by
          norm_num
          exact hx.1
        have hupp :
            |SF2R 2 (binarySingleNaNFloatToStandardFloat
              (prec:=prec) (emax:=emax)
              (BinarySingleNaNFloat.B754_finite s m e hm_pos hbounded))| <
              ((2 : ℝ) ^ (0 : Int)) := by
          norm_num
          exact hx.2
        have htrip := FloatSpec.Core.Raux.mag_unique 2
          (SF2R 2 (binarySingleNaNFloatToStandardFloat
            (prec:=prec) (emax:=emax)
            (BinarySingleNaNFloat.B754_finite s m e hm_pos hbounded)))
          0 (by norm_num : (1 : Int) < 2) hlow hupp
        simpa [wp, PostCond.noThrow, pure] using htrip trivial
      have hsigned_ne :
          (if s then -(m : Int) else (m : Int)) ≠ 0 := by
        have hm_int_ne : (m : Int) ≠ 0 := by
          exact_mod_cast (Nat.pos_iff_ne_zero.mp hm_pos)
        cases s
        · simpa using hm_int_ne
        · simpa using neg_ne_zero.mpr hm_int_ne
      have hmag_digits :=
        FloatSpec.Core.Float_prop.Raux_mag_F2R_Zdigits
          (beta := 2) (m := if s then -(m : Int) else (m : Int)) (e := e)
          (by norm_num : (1 : Int) < 2) hsigned_ne
      have hsum_signed :
          FloatSpec.Core.Digits.Zdigits 2 (if s then -(m : Int) else (m : Int)) + e = 0 := by
        rw [← hmag_digits]
        simpa [binarySingleNaNFloatToStandardFloat, SF2R, F2R,
          FloatSpec.Core.Defs.F2R] using hmag0
      have hzdigits_signed :
          FloatSpec.Core.Digits.Zdigits 2 (if s then -(m : Int) else (m : Int)) =
            FloatSpec.Core.Digits.Zdigits 2 (m : Int) := by
        have htrip :=
          FloatSpec.Core.Digits.Zdigits_cond_Zopp (beta := 2) (b := s) (n := (m : Int))
        simpa [wp, PostCond.noThrow, pure] using htrip trivial
      have hsum :
          FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e = 0 := by
        simpa [hzdigits_signed] using hsum_signed
      have hcanon :
          canonical_mantissa (prec:=prec) (emax:=emax) m e = true :=
        canonical_mantissa_of_specFloat_bounded (prec:=prec) (emax:=emax) hbounded
      have he_canon :
          e = FLT_exp (3 - emax - prec) prec
            (FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e) := by
        unfold canonical_mantissa at hcanon
        exact eq_of_beq hcanon
      have he_max : e = max (-prec) (3 - emax - prec) := by
        rw [he_canon, hsum]
        unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
        ring_nf
      have hzdigits_pos :
          0 < FloatSpec.Core.Digits.Zdigits 2 (m : Int) := by
        have hm_int_ne : (m : Int) ≠ 0 := by
          exact_mod_cast (Nat.pos_iff_ne_zero.mp hm_pos)
        have htrip := FloatSpec.Core.Digits.Zdigits_gt_0
          (beta := 2) (n := (m : Int)) (by norm_num : (2 : Int) > 1) hm_int_ne
        simpa [wp, PostCond.noThrow, pure] using htrip
      have hprec_pos : 0 < prec := by
        have hleft :
            FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e - prec ≤ e := by
          calc
            FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e - prec
                ≤ max (FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e - prec)
                    (3 - emax - prec) := le_max_left _ _
            _ = e := he_canon.symm
        omega
      have he_neg : e = -prec := by
        by_cases h3 : 3 ≤ emax
        · rw [he_max]
          exact max_eq_left (by omega)
        · have hemax2 : emax = 2 := by
            have hprec_lt := (inferInstance : Prec_lt_emax prec emax).prec_lt_emax
            have hemax_ge2 : 2 ≤ emax := by omega
            omega
          have hprec1 : prec = 1 := by
            have hprec_lt := (inferInstance : Prec_lt_emax prec emax).prec_lt_emax
            omega
          have he_zero : e = 0 := by
            rw [he_max, hemax2, hprec1]
            norm_num
          have hzdigits_zero :
              FloatSpec.Core.Digits.Zdigits 2 (m : Int) = 0 := by
            omega
          omega
      have hzdigits_prec :
          FloatSpec.Core.Digits.Zdigits 2 (m : Int) = prec := by
        omega
      have hdigits2 :
          FloatSpec.Core.Digits.digits2_pos m = prec := by
        have htrip := FloatSpec.Core.Digits.Zpos_digits2_pos m
        have hzdigits_digits2 :
            FloatSpec.Core.Digits.Zdigits 2 (m : Int) =
              FloatSpec.Core.Digits.digits2_pos m :=
          (htrip hm_pos).symm
        omega
      refine ⟨?hmant, hdigits2, he_neg⟩
      simp [BinarySingleNaNFloat.Bnormfr_mantissa, SFnormfr_mantissa,
        binarySingleNaNFloatToStandardFloat, he_neg]

-- Coq: match_SF2B — pattern match through SF2B corresponds to match on source
def match_SF2B_check {T : Type}
  (fz : Bool → T) (fi : Bool → T) (fn : T) (ff : Bool → Nat → Int → T)
  (x : StandardFloat) : T :=
    match x with
    | StandardFloat.S754_zero sx => fz sx
    | StandardFloat.S754_infinity sx => fi sx
    | StandardFloat.S754_nan => fn
    | StandardFloat.S754_finite sx mx ex => ff sx mx ex

theorem match_SF2B {T : Type}
  (fz : Bool → T) (fi : Bool → T) (fn : T) (ff : Bool → Nat → Int → T)
  (x : StandardFloat) :
  ⦃⌜True⌝⦄
  (pure (match_SF2B_check fz fi fn ff x) : Id T)
  ⦃⇓result => ⌜result =
      (match SF2B x with
       | B754.B754_zero sx => fz sx
       | B754.B754_infinity sx => fi sx
       | B754.B754_nan => fn
       | B754.B754_finite sx mx ex => ff sx mx ex)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold match_SF2B_check SF2B
  cases x <;> rfl

-- Coq: canonical_canonical_mantissa (SingleNaN side)
-- Mirror the Binary.lean style: hoare-triple statement yielding canonicality.
def canonical_canonical_mantissa_bsn_check
  (sx : Bool) (mx : Nat) (ex : Int) : Unit :=
  ()

omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
theorem canonical_canonical_mantissa_bsn
  (sx : Bool) (mx : Nat) (ex : Int)
  (hmx_pos : 0 < mx)  -- IEEE 754: finite floats have positive mantissa; zero is B754_zero
  (h : canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true) :
  ⦃⌜True⌝⦄
  (pure (canonical_canonical_mantissa_bsn_check sx mx ex) : Id Unit)
  ⦃⇓_ => ⌜FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
            (FloatSpec.Core.Defs.FlocqFloat.mk (if sx then -(mx : Int) else (mx : Int)) ex)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Extract equality from boolean hypothesis
  have heq : ex = FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 mx + ex) :=
    eq_of_beq h
  -- Unfold canonical to show the goal is about F2R and mag
  unfold FloatSpec.Core.Generic_fmt.canonical
  simp only [FloatSpec.Core.Defs.FlocqFloat.Fexp]
  -- Goal: ex = FLT_exp ... (mag 2 (F2R f)) where f.Fnum = if sx then -mx else mx
  -- We need to show mag 2 (F2R f) = Zdigits 2 mx + ex
  -- F2R f = (signed mantissa) * 2^ex
  -- By mag_mult_bpow_eq: mag 2 (m * 2^ex) = mag 2 m + ex
  -- And mag 2 (±mx) = mag 2 mx = Zdigits 2 mx (for mx > 0)
  -- With hmx_pos : 0 < mx, we go directly to the non-zero case
  have hmx : mx ≠ 0 := Nat.pos_iff_ne_zero.mp hmx_pos
  have hmx_int_pos : (0 : Int) < (mx : Int) := Nat.cast_pos.mpr hmx_pos
  have hmx_real_ne : ((mx : Int) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (Int.ofNat_ne_zero.mpr hmx)
  -- Get mag 2 mx = Zdigits 2 mx
  have h2gt1 : (1 : Int) < 2 := by norm_num
  have hmag_eq := FloatSpec.Calc.Sqrt.mag_eq_Zdigits 2 (mx : Int) hmx_int_pos h2gt1
  -- Show signed mantissa ≠ 0
  have hsigned_ne : (if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) ≠ 0 := by
    cases sx <;> simp [hmx_real_ne, hmx]
  -- Use mag_mult_bpow_eq: mag 2 (m * 2^ex) = mag 2 m + ex
  have hmag_mult := FloatSpec.Calc.Sqrt.mag_mult_bpow_eq 2
    (if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) ex hsigned_ne h2gt1
  -- Rewrite F2R
  simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
             FloatSpec.Core.Defs.FlocqFloat.Fexp]
  -- Normalize coercions: push Int cast inside the if expression to match hmag_mult pattern
  simp only [Int.cast_ite, Int.cast_neg, Int.cast_natCast]
  -- Establish mag of signed mantissa equals Zdigits
  have hmag_signed : FloatSpec.Core.Raux.mag 2
      (if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) =
      FloatSpec.Core.Digits.Zdigits 2 (mx : Int) := by
    cases sx
    · -- sx = false: straightforward
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hmag_eq
    · -- sx = true: use mag(-x) = mag(x)
      simp only [↓reduceIte]
      -- mag 2 (-mx) = mag 2 mx
      unfold FloatSpec.Core.Raux.mag
      -- Explicitly prove -↑↑mx ≠ 0 so simp can eliminate the if-condition
      have hmx_neg_ne : -((mx : Int) : ℝ) ≠ 0 := neg_ne_zero.mpr hmx_real_ne
      simp only [hmx_neg_ne, ↓reduceIte, abs_neg]
      -- Now both sides simplify to the same thing
      unfold FloatSpec.Core.Raux.mag at hmag_eq
      simp only [hmx_real_ne, ↓reduceIte] at hmag_eq
      exact hmag_eq
  -- Now build the full magnitude equation
  -- Note: hmag_mult uses ↑2 ^ ex (Int 2 cast to ℝ), so we state hmag_full the same way
  have hmag_full : FloatSpec.Core.Raux.mag 2
      ((if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) * ((2 : Int) : ℝ) ^ ex) =
      FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex := by
    rw [hmag_mult, hmag_signed]
  -- The goal is: ex = FLT_exp ... (mag 2 ((if sx then -↑mx else ↑mx) * 2^ex))
  -- We need to show this equals heq: ex = FLT_exp ... (Zdigits 2 mx + ex)
  -- First convert the goal to use our magnitude equation
  calc ex = FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex) := heq
    _ = FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Raux.mag 2
          ((if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) * ((2 : Int) : ℝ) ^ ex)) := by
      rw [hmag_full]

private theorem canonical_mantissa_bsn_of_canonical
  (sx : Bool) (mx : Nat) (ex : Int)
  (hmx_pos : 0 < mx)
  (hcanon : FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
      (FloatSpec.Core.Defs.FlocqFloat.mk (if sx then -(mx : Int) else (mx : Int)) ex)) :
  canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true := by
  unfold canonical_mantissa
  apply beq_iff_eq.mpr
  unfold FloatSpec.Core.Generic_fmt.canonical at hcanon
  simp only [FloatSpec.Core.Defs.FlocqFloat.Fexp] at hcanon
  have hsigned_ne :
      (if sx then -(mx : Int) else (mx : Int)) ≠ 0 := by
    have hmx_ne : (mx : Int) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hmx_pos)
    cases sx
    · simpa using hmx_ne
    · simpa using neg_ne_zero.mpr hmx_ne
  have hmag :=
    FloatSpec.Core.Float_prop.Raux_mag_F2R_Zdigits
      (beta := 2) (m := if sx then -(mx : Int) else (mx : Int)) (e := ex)
      (by norm_num : (1 : Int) < 2) hsigned_ne
  have hzdigits_signed :
      FloatSpec.Core.Digits.Zdigits 2 (if sx then -(mx : Int) else (mx : Int)) =
        FloatSpec.Core.Digits.Zdigits 2 (mx : Int) := by
    have htrip :=
      FloatSpec.Core.Digits.Zdigits_cond_Zopp (beta := 2) (b := sx) (n := (mx : Int))
    simpa [wp, PostCond.noThrow, pure] using htrip trivial
  have hmag_unsigned :
      FloatSpec.Core.Raux.mag 2
          (FloatSpec.Core.Defs.F2R (FloatSpec.Core.Defs.FlocqFloat.mk
            (if sx then -(mx : Int) else (mx : Int)) ex :
              FloatSpec.Core.Defs.FlocqFloat 2)) =
        FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex := by
    simpa [hzdigits_signed] using hmag
  calc
    ex = FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Raux.mag 2
          (FloatSpec.Core.Defs.F2R (FloatSpec.Core.Defs.FlocqFloat.mk
            (if sx then -(mx : Int) else (mx : Int)) ex :
              FloatSpec.Core.Defs.FlocqFloat 2))) := hcanon
    _ = FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex) := by
          rw [hmag_unsigned]

private theorem canonical_mantissa_bsn_of_repr_cexp
    (mx : Nat) (ex : Int) (x : ℝ)
    (hmx_pos : 0 < mx)
    (hx : x = F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
      FloatSpec.Core.Defs.FlocqFloat 2))
    (hexp : ex =
      FloatSpec.Core.Generic_fmt.cexp 2 (FLT_exp (3 - emax - prec) prec) x) :
    canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true := by
  unfold canonical_mantissa
  apply beq_iff_eq.mpr
  have hmx_ne : (mx : Int) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hmx_pos)
  have hmag :=
    FloatSpec.Core.Float_prop.Raux_mag_F2R_Zdigits
      (beta := 2) (m := (mx : Int)) (e := ex)
      (by norm_num : (1 : Int) < 2) hmx_ne
  calc
    ex = FloatSpec.Core.Generic_fmt.cexp 2 (FLT_exp (3 - emax - prec) prec) x := hexp
    _ = FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Raux.mag 2 x) := rfl
    _ = FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Raux.mag 2
          (F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
            FloatSpec.Core.Defs.FlocqFloat 2))) := by
          rw [hx]
    _ = FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex) := by
          simpa [F2R] using
            congrArg (fun t => FLT_exp (3 - emax - prec) prec t) hmag

-- Coq: canonical_bounded — `SpecFloat.bounded` implies canonical format.
-- The Coq mantissa has type `positive`; using `Positive` here avoids introducing
-- a Lean-only positivity precondition.  The range-only compatibility predicate
-- `bounded` is deliberately not used by this source-facing theorem.
def canonical_bounded_check (sx : Bool) (mx : Nat) (ex : Int) : Unit :=
  ()

omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
theorem canonical_bounded
  (sx : Bool) (mx : FloatSpec.Core.Zaux.Positive) (ex : Int)
  (h_bounded : specFloat_bounded (prec:=prec) (emax:=emax)
    (FloatSpec.Core.Zaux.positiveToNat mx) ex = true) :
  ⦃⌜True⌝⦄
  (pure (canonical_bounded_check sx (FloatSpec.Core.Zaux.positiveToNat mx) ex) : Id Unit)
  ⦃⇓_ => ⌜FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
            (FloatSpec.Core.Defs.FlocqFloat.mk
              (if sx then -(FloatSpec.Core.Zaux.positiveToNat mx : Int)
               else (FloatSpec.Core.Zaux.positiveToNat mx : Int)) ex)⌝⦄ := by
  exact canonical_canonical_mantissa_bsn (prec:=prec) (emax:=emax) sx
    (FloatSpec.Core.Zaux.positiveToNat mx) ex (positiveToNat_pos_bsn mx)
    (canonical_mantissa_of_specFloat_bounded h_bounded)

-- Compatibility theorem for local Nat-based callers.  Its name makes the
-- representation bridge explicit rather than weakening the source theorem.
omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
theorem canonical_bounded_nat
  (sx : Bool) (mx : Nat) (ex : Int)
  (hmx_pos : 0 < mx)
  (h_bounded : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true) :
  ⦃⌜True⌝⦄
  (pure (canonical_bounded_check sx mx ex) : Id Unit)
  ⦃⇓_ => ⌜FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
            (FloatSpec.Core.Defs.FlocqFloat.mk (if sx then -(mx : Int) else (mx : Int)) ex)⌝⦄ := by
  exact canonical_canonical_mantissa_bsn (prec:=prec) (emax:=emax) sx mx ex hmx_pos
    (canonical_mantissa_of_specFloat_bounded h_bounded)

alias canonical_bounded_of_specFloat_bounded := canonical_bounded_nat

-- Coq `BinarySingleNaN.canonical_canonical_mantissa`, published on the
-- proof-carrying carrier's positive mantissa boundary.
omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
theorem canonical_canonical_mantissa
    (sx : Bool) (mx : FloatSpec.Core.Zaux.Positive) (ex : Int)
    (h : canonical_mantissa (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mx) ex = true) :
    FloatSpec.Core.Generic_fmt.canonical 2
      (FLT_exp (3 - emax - prec) prec)
      (FloatSpec.Core.Defs.FlocqFloat.mk
        (if sx then -(FloatSpec.Core.Zaux.positiveToNat mx : Int)
         else (FloatSpec.Core.Zaux.positiveToNat mx : Int)) ex) := by
  have htrip := canonical_canonical_mantissa_bsn (prec:=prec) (emax:=emax)
    sx (FloatSpec.Core.Zaux.positiveToNat mx) ex (positiveToNat_pos_bsn mx) h
  simpa [wp, PostCond.noThrow, pure] using htrip trivial

/- Coq `BinarySingleNaN.generic_format_B2R`. -/
omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
theorem generic_format_B2R
    (x : BinarySingleNaNFloat prec emax) :
    FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec)
      (B754_to_R (binarySingleNaNFloatToB754 x)) := by
  cases x with
  | B754_zero s | B754_infinity s | B754_nan =>
      simp [binarySingleNaNFloatToB754, B754_to_R,
        FloatSpec.Core.Generic_fmt.generic_format,
        FloatSpec.Core.Generic_fmt.scaled_mantissa,
        FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Raux.mag,
        FloatSpec.Core.Raux.Ztrunc]
  | B754_finite s m e hm hb =>
      apply FloatSpec.Core.Generic_fmt.generic_format_canonical
      have htrip := canonical_canonical_mantissa_bsn (prec:=prec) (emax:=emax)
        s m e hm (canonical_mantissa_of_specFloat_bounded hb)
      simpa [wp, PostCond.noThrow, pure, binarySingleNaNFloatToB754, B754_to_R]
        using htrip trivial

/- Coq `BinarySingleNaN.FLT_format_B2R`. -/
omit [Prec_lt_emax prec emax] in
theorem FLT_format_B2R
    (x : BinarySingleNaNFloat prec emax) :
    FloatSpec.Core.FLT.FLT_format (prec:=prec) (emin:=3 - emax - prec)
      2 (B754_to_R (binarySingleNaNFloatToB754 x)) := by
  exact FloatSpec.Core.FLT.FLT_format_generic
    (prec := prec) (emin := 3 - emax - prec) 2 _
    (generic_format_B2R (prec := prec) (emax := emax) x)

-- Coq: B2SF_SF2B — standard view after SF2B is identity
def B2SF_SF2B_check (x : StandardFloat) : StandardFloat :=
  (B2SF_BSN (SF2B x))

theorem B2SF_SF2B (x : StandardFloat) :
  ⦃⌜True⌝⦄
  (pure (B2SF_SF2B_check x) : Id StandardFloat)
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2SF_SF2B_check
  cases x <;> rfl

-- Finite/NaN/sign classifiers on the BinarySingleNaN side
def BSN_is_finite (x : B754) : Bool :=
  match x with
  | B754.B754_finite _ _ _ => true
  | B754.B754_zero _ => true
  | _ => false

def BSN_is_nan (x : B754) : Bool :=
  match x with
  | B754.B754_nan => true
  | _ => false

def BSN_sign (x : B754) : Bool :=
  match x with
  | B754.B754_zero s => s
  | B754.B754_infinity s => s
  | B754.B754_finite s _ _ => s
  | B754.B754_nan => false

/-- Coq `BinarySingleNaN.Beqb`, on the proof-carrying single-NaN carrier. -/
noncomputable def Beqb {prec emax : Int}
    (f1 f2 : BinarySingleNaNFloat prec emax) : Bool :=
  match binarySingleNaNFloatToStandardFloat f1,
      binarySingleNaNFloatToStandardFloat f2 with
  | StandardFloat.S754_nan, _ => false
  | _, StandardFloat.S754_nan => false
  | StandardFloat.S754_infinity s1, StandardFloat.S754_infinity s2 => s1 == s2
  | StandardFloat.S754_infinity _, _ => false
  | _, StandardFloat.S754_infinity _ => false
  | _, _ => FloatSpec.Core.Raux.Req_bool
      (B754_to_R (binarySingleNaNFloatToB754 f1))
      (B754_to_R (binarySingleNaNFloatToB754 f2))

/-- Coq `BinarySingleNaN.Beqb_correct`. -/
theorem Beqb_correct {prec emax : Int}
    (f1 f2 : BinarySingleNaNFloat prec emax)
    (h1 : BSN_is_finite (binarySingleNaNFloatToB754 f1) = true)
    (h2 : BSN_is_finite (binarySingleNaNFloatToB754 f2) = true) :
    Beqb f1 f2 = FloatSpec.Core.Raux.Req_bool
      (B754_to_R (binarySingleNaNFloatToB754 f1))
      (B754_to_R (binarySingleNaNFloatToB754 f2)) := by
  cases f1 <;> cases f2 <;>
    simp [BSN_is_finite, Beqb, binarySingleNaNFloatToB754,
      binarySingleNaNFloatToStandardFloat] at h1 h2 ⊢

/-- Coq `BinarySingleNaN.Beqb_refl`; only NaN is non-reflexive. -/
theorem Beqb_refl {prec emax : Int} (f : BinarySingleNaNFloat prec emax) :
    Beqb f f = !(BSN_is_nan (binarySingleNaNFloatToB754 f)) := by
  cases f <;>
    simp [Beqb, BSN_is_nan, B754_to_R, binarySingleNaNFloatToB754,
      binarySingleNaNFloatToStandardFloat, FloatSpec.Core.Raux.Req_bool]

/-- Coq `BinarySingleNaN.Bltb`, on the proof-carrying single-NaN carrier. -/
noncomputable def Bltb {prec emax : Int}
    (f1 f2 : BinarySingleNaNFloat prec emax) : Bool :=
  match binarySingleNaNFloatToStandardFloat f1,
      binarySingleNaNFloatToStandardFloat f2 with
  | StandardFloat.S754_nan, _ => false
  | _, StandardFloat.S754_nan => false
  | StandardFloat.S754_infinity s1, StandardFloat.S754_infinity s2 => s1 && !s2
  | StandardFloat.S754_infinity s1, _ => s1
  | _, StandardFloat.S754_infinity s2 => !s2
  | _, _ => FloatSpec.Core.Raux.Rlt_bool
      (B754_to_R (binarySingleNaNFloatToB754 f1))
      (B754_to_R (binarySingleNaNFloatToB754 f2))

/-- Coq `BinarySingleNaN.Bltb_correct`. -/
theorem Bltb_correct {prec emax : Int}
    (f1 f2 : BinarySingleNaNFloat prec emax)
    (h1 : BSN_is_finite (binarySingleNaNFloatToB754 f1) = true)
    (h2 : BSN_is_finite (binarySingleNaNFloatToB754 f2) = true) :
    Bltb f1 f2 = FloatSpec.Core.Raux.Rlt_bool
      (B754_to_R (binarySingleNaNFloatToB754 f1))
      (B754_to_R (binarySingleNaNFloatToB754 f2)) := by
  cases f1 <;> cases f2 <;>
    simp [BSN_is_finite, Bltb, binarySingleNaNFloatToB754,
      binarySingleNaNFloatToStandardFloat] at h1 h2 ⊢

/-- Coq `BinarySingleNaN.Bleb`. -/
noncomputable def Bleb {prec emax : Int}
    (f1 f2 : BinarySingleNaNFloat prec emax) : Bool :=
  Bltb f1 f2 || Beqb f1 f2

/-- Coq `BinarySingleNaN.Bleb_correct`. -/
theorem Bleb_correct {prec emax : Int}
    (f1 f2 : BinarySingleNaNFloat prec emax)
    (h1 : BSN_is_finite (binarySingleNaNFloatToB754 f1) = true)
    (h2 : BSN_is_finite (binarySingleNaNFloatToB754 f2) = true) :
    Bleb f1 f2 = FloatSpec.Core.Raux.Rle_bool
      (B754_to_R (binarySingleNaNFloatToB754 f1))
      (B754_to_R (binarySingleNaNFloatToB754 f2)) := by
  rw [Bleb, Bltb_correct f1 f2 h1 h2, Beqb_correct f1 f2 h1 h2]
  simp [FloatSpec.Core.Raux.Rlt_bool, FloatSpec.Core.Raux.Req_bool,
    FloatSpec.Core.Raux.Rle_bool, le_iff_lt_or_eq]

-- Strict finiteness on StandardFloat (true iff finite, not considering zeros specially)
def is_finite_strict_SF (x : StandardFloat) : Bool :=
  match x with
  | StandardFloat.S754_finite _ _ _ => true
  | _ => false

-- Coq: B2SF_B2BSN — standard view commutes with bridge to single-NaN
def B2SF_B2BSN_check {prec emax} (x : Binary754 prec emax) : StandardFloat :=
  (B2SF_BSN (B2BSN (prec:=prec) (emax:=emax) x))

theorem B2SF_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  (pure (B2SF_B2BSN_check (prec:=prec) (emax:=emax) x) : Id StandardFloat)
  ⦃⇓result => ⌜result = B2SF (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2SF_B2BSN_check B2BSN B2SF_BSN B2SF FF2SF
  cases x.val <;> rfl

-- Coq: is_finite_B2BSN — finiteness preserved by the bridge
def is_finite_B2BSN_check {prec emax} (x : Binary754 prec emax) : Bool :=
  (BSN_is_finite (B2BSN (prec:=prec) (emax:=emax) x))

theorem is_finite_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  (pure (is_finite_B2BSN_check (prec:=prec) (emax:=emax) x) : Id Bool)
  ⦃⇓result => ⌜result = is_finite_B (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_B2BSN_check BSN_is_finite B2BSN is_finite_B is_finite_FF
  cases x.val <;> rfl

-- Strict finiteness (finite-but-not-zero) classifiers, used for missing Coq theorems.
def BSN_is_finite_strict (x : B754) : Bool :=
  match x with
  | B754.B754_finite _ _ _ => true
  | _ => false

-- Coq: Bone
def Bone : B754 :=
  SF2B (StandardFloat.S754_finite false 1 0)

-- Coq: is_finite_strict_Bone
theorem is_finite_strict_Bone :
    BSN_is_finite_strict Bone = true := by
  rfl

-- Coq: is_nan_Bone
theorem is_nan_Bone :
    BSN_is_nan Bone = false := by
  rfl

def is_finite_strict_B {prec emax} (x : Binary754 prec emax) : Bool :=
  match x.val with
  | FullFloat.F754_finite _ _ _ => true
  | _ => false

-- Coq: is_finite_strict_B2BSN — strict finiteness preserved by the bridge
def is_finite_strict_B2BSN_check {prec emax} (x : Binary754 prec emax) : Bool :=
  (BSN_is_finite_strict (B2BSN (prec:=prec) (emax:=emax) x))

theorem is_finite_strict_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  (pure (is_finite_strict_B2BSN_check (prec:=prec) (emax:=emax) x) : Id Bool)
  ⦃⇓result => ⌜result = is_finite_strict_B (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_strict_B2BSN_check BSN_is_finite_strict B2BSN is_finite_strict_B
  cases x.val <;> rfl

-- Coq: is_nan_B2BSN — NaN preserved by the bridge
def is_nan_B2BSN_check {prec emax} (x : Binary754 prec emax) : Bool :=
  (BSN_is_nan (B2BSN (prec:=prec) (emax:=emax) x))

theorem is_nan_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  (pure (is_nan_B2BSN_check (prec:=prec) (emax:=emax) x) : Id Bool)
  ⦃⇓result => ⌜result = is_nan_B (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_nan_B2BSN_check BSN_is_nan B2BSN is_nan_B is_nan_FF
  cases x.val <;> rfl

-- Coq: Bsign_B2BSN — sign preserved by the bridge (for non-NaN values)
def Bsign_B2BSN_check {prec emax} (x : Binary754 prec emax) : Bool :=
  (BSN_sign (B2BSN (prec:=prec) (emax:=emax) x))

theorem Bsign_B2BSN {prec emax} (x : Binary754 prec emax)
  (hx : is_nan_B (prec:=prec) (emax:=emax) x = false) :
  ⦃⌜True⌝⦄
  (pure (Bsign_B2BSN_check (prec:=prec) (emax:=emax) x) : Id Bool)
  ⦃⇓result => ⌜result = Bsign (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold Bsign_B2BSN_check BSN_sign B2BSN Bsign sign_FF
  cases h : x.val <;> simp_all [is_nan_B, is_nan_FF]

-- Coq: B2R_B2BSN — real semantics commutes with bridge to single-NaN
noncomputable def B2R_B2BSN_check {prec emax} (x : Binary754 prec emax) : ℝ :=
  (B754_to_R (B2BSN (prec:=prec) (emax:=emax) x))

theorem B2R_B2BSN {prec emax} (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  (pure (B2R_B2BSN_check (prec:=prec) (emax:=emax) x) : Id ℝ)
  ⦃⇓result => ⌜result = B2R (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2R_B2BSN_check B754_to_R B2BSN B2R FF2R
  cases x.val <;> rfl

-- Coq: emin_lt_emax — the minimal exponent is strictly less than emax
-- We state it using the hoare‑triple style used throughout this project.
def emin_lt_emax_check : Unit :=
  ()

theorem emin_lt_emax :
  ⦃⌜True⌝⦄
  (pure emin_lt_emax_check : Id Unit)
  ⦃⇓_ => ⌜(3 - emax - prec) < emax⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, emin_lt_emax_check, Id.run, PredTrans.pure, PredTrans.apply]
  have hprec := (inferInstance : Prec_lt_emax prec emax).prec_lt_emax
  have hemax := (inferInstance : Prec_lt_emax prec emax).emax_ge_2
  have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
  have h : (3 - emax - prec) < emax := by linarith
  trivial

-- Coq: is_finite_strict_B2R — nonzero real semantics implies strict finiteness
-- Stated for the single-NaN binary `B754` using `B754_to_R` as semantics.
def is_finite_strict_B2R_check (x : B754) : Bool :=
  (BSN_is_finite_strict x)

theorem is_finite_strict_B2R (x : B754)
  (h : B754_to_R x ≠ 0) :
  ⦃⌜True⌝⦄
  (pure (is_finite_strict_B2R_check x) : Id Bool)
  ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Case split on x; non-finite cases have B754_to_R = 0, contradicting h
  cases x with
  | B754_zero s => simp [B754_to_R] at h
  | B754_infinity s => simp [B754_to_R] at h
  | B754_nan => simp [B754_to_R] at h
  | B754_finite s m e =>
    -- BSN_is_finite_strict (B754_finite s m e) = true by definition
    simp [is_finite_strict_B2R_check, BSN_is_finite_strict]

-- Coq: SF2R_B2SF — Real semantics after mapping to StandardFloat
-- We state it in hoare-triple style around a pure computation.
noncomputable def SF2R_B2SF_check (x : B754) : ℝ :=
  (SF2R 2 (B2SF_BSN x))

theorem SF2R_B2SF (x : B754) :
  ⦃⌜True⌝⦄
  (pure (SF2R_B2SF_check x) : Id ℝ)
  ⦃⇓result => ⌜result = B754_to_R x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold SF2R_B2SF_check B2SF_BSN SF2R B754_to_R
  cases x <;> rfl

-- Coq: SF2B_B2SF — roundtrip from B2SF back to B754 via SF2B
def SF2B_B2SF_check (x : B754) : B754 :=
  (SF2B (B2SF_BSN x))

theorem SF2B_B2SF (x : B754) :
  ⦃⌜True⌝⦄
  (pure (SF2B_B2SF_check x) : Id B754)
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold SF2B_B2SF_check SF2B B2SF_BSN
  cases x <;> rfl

-- Coq: valid_binary_B2SF — validity of `B2SF` image
def valid_binary_B2SF_check {prec emax : Int} (x : B754) : Bool :=
  (valid_binary_SF (prec:=prec) (emax:=emax) (B2SF_BSN x))

theorem valid_binary_B2SF {prec emax} (x : B754) :
  ⦃⌜True⌝⦄
  (pure (valid_binary_B2SF_check (prec:=prec) (emax:=emax) x) : Id Bool)
  ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Holds by the current definition of valid_binary_SF.
  unfold valid_binary_B2SF_check
  rfl

-- Coq: SF2B_B2SF_valid — roundtrip with validity argument
def SF2B_B2SF_valid_check (x : B754) : B754 :=
  (SF2B (B2SF_BSN x))

theorem SF2B_B2SF_valid (x : B754) :
  ⦃⌜True⌝⦄
  (pure (SF2B_B2SF_valid_check x) : Id B754)
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  -- Same computation as SF2B_B2SF.
  unfold SF2B_B2SF_valid_check SF2B B2SF_BSN
  cases x <;> rfl

-- Coq: Bsign_SF2B — sign is preserved by SF2B.
def Bsign_SF2B_check (x : StandardFloat) : Bool :=
  BSN_sign (SF2B x)

omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
theorem Bsign_SF2B (x : StandardFloat)
  (_Hx : valid_binary_SF (prec:=prec) (emax:=emax) x = true) :
  ⦃⌜True⌝⦄
  (pure (Bsign_SF2B_check x) : Id Bool)
  ⦃⇓result => ⌜result = sign_SF x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold Bsign_SF2B_check BSN_sign SF2B sign_SF
  cases x <;> rfl

-- Coq: is_finite_SF2B — finiteness is preserved by SF2B.
def is_finite_SF2B_check (x : StandardFloat) : Bool :=
  (BSN_is_finite (SF2B x))

omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
theorem is_finite_SF2B (x : StandardFloat)
  (_Hx : valid_binary_SF (prec:=prec) (emax:=emax) x = true) :
  ⦃⌜True⌝⦄
  (pure (is_finite_SF2B_check x) : Id Bool)
  ⦃⇓result => ⌜result = is_finite_SF x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_SF2B_check BSN_is_finite SF2B is_finite_SF
  cases x <;> rfl

-- Coq: is_nan_SF2B — NaN status is preserved by SF2B.
def is_nan_SF2B_check (x : StandardFloat) : Bool :=
  BSN_is_nan (SF2B x)

omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
theorem is_nan_SF2B (x : StandardFloat)
  (_Hx : valid_binary_SF (prec:=prec) (emax:=emax) x = true) :
  ⦃⌜True⌝⦄
  (pure (is_nan_SF2B_check x) : Id Bool)
  ⦃⇓result => ⌜result = is_nan_SF x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_nan_SF2B_check BSN_is_nan SF2B is_nan_SF
  cases x <;> rfl

-- Coq: is_finite_strict_SF2B — strict finiteness preserved by SF2B
def is_finite_strict_SF2B_check (x : StandardFloat) : Bool :=
  (BSN_is_finite_strict (SF2B x))

theorem is_finite_strict_SF2B (x : StandardFloat) :
  ⦃⌜True⌝⦄
  (pure (is_finite_strict_SF2B_check x) : Id Bool)
  ⦃⇓result => ⌜result = is_finite_strict_SF x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_strict_SF2B_check BSN_is_finite_strict SF2B is_finite_strict_SF
  cases x <;> rfl

-- Coq: B2SF_inj — injectivity of B2SF on non-NaN values
theorem B2SF_inj (x y : B754)
  (hx : BSN_is_nan x = false)
  (hy : BSN_is_nan y = false)
  (h : B2SF_BSN x = B2SF_BSN y) : x = y := by
  -- Proof by cases on x and y; NaN excluded by hypotheses.
  -- Cases with NaN lead to contradiction via hx/hy; different constructors
  -- lead to contradiction via h being an impossible equality.
  cases x <;> cases y <;> simp_all [BSN_is_nan, B2SF_BSN]

-- Bridge back from single-NaN view to FullFloat (Coq: BSN2B)
def BSN2B (s : Bool) (payload : Nat) (x : B754) : FullFloat :=
  match x with
  | B754.B754_nan => FullFloat.F754_nan s payload
  | B754.B754_zero b => FullFloat.F754_zero b
  | B754.B754_infinity b => FullFloat.F754_infinity b
  | B754.B754_finite b m e => FullFloat.F754_finite b m e

-- A variant of the bridge that requires a non-NaN witness, mirroring Coq's `BSN2B'`.
-- For non-NaN inputs, it returns the corresponding `FullFloat` without needing a NaN payload.
def BSN2B' (x : B754) (nx : BSN_is_nan x = false) : FullFloat :=
  match x with
  | B754.B754_zero b => FullFloat.F754_zero b
  | B754.B754_infinity b => FullFloat.F754_infinity b
  | B754.B754_finite b m e => FullFloat.F754_finite b m e
  | B754.B754_nan => nomatch nx

-- Coq: B2BSN_BSN2B — roundtrip through the bridge
def B2BSN_BSN2B_check {prec emax : Int} (s : Bool) (payload : Nat) (x : B754) : B754 :=
  (B2BSN (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) (BSN2B s payload x)))

theorem B2BSN_BSN2B {prec emax : Int} (s : Bool) (payload : Nat) (x : B754) :
  ⦃⌜True⌝⦄
  (pure (B2BSN_BSN2B_check (prec:=prec) (emax:=emax) s payload x) : Id B754)
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2BSN_BSN2B_check BSN2B B2BSN FF2B
  cases x <;> rfl

-- Coq: Bsign_BSN2B — sign preserved by BSN2B on non-NaN values
def Bsign_BSN2B_check (s : Bool) (payload : Nat) (x : B754) : Bool :=
  (sign_FF (BSN2B s payload x))

theorem Bsign_BSN2B (s : Bool) (payload : Nat) (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (Bsign_BSN2B_check s payload x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_sign x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold Bsign_BSN2B_check
  cases x <;> simp [BSN_is_nan, BSN2B, sign_FF, BSN_sign] at nx ⊢

-- A lifting combinator mirroring Coq's `lift` (Binary.v)
-- If `x` is NaN, return `x`; otherwise, rebuild a full float from `y`.
def lift (x : FullFloat) (y : B754)
  (Ny : BSN_is_nan y = is_nan_FF x) : FullFloat :=
  match h:is_nan_FF x with
  | true => x
  | false => BSN2B' y (by simpa [h] using Ny)

-- Coq: B2BSN_lift — viewing the lifted value back to BSN yields `y`
def B2BSN_lift_check {prec emax : Int}
  (x : FullFloat) (y : B754)
  (Ny : BSN_is_nan y = is_nan_FF x) : B754 :=
  (B2BSN (prec:=prec) (emax:=emax)
          (FF2B (prec:=prec) (emax:=emax)
            (lift x y Ny)))

theorem B2BSN_lift {prec emax : Int}
  (x : FullFloat) (y : B754)
  (Ny : BSN_is_nan y = is_nan_FF x) :
  ⦃⌜True⌝⦄
  (pure (B2BSN_lift_check (prec:=prec) (emax:=emax) x y Ny) : Id B754)
  ⦃⇓result => ⌜result = y⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2BSN_lift_check lift
  split
  · -- Case is_nan_FF x = true: lift returns x
    rename_i h_nan
    -- From Ny and h_nan, y must be B754_nan
    -- First case on x to get its NaN form
    cases hx : x with
    | F754_zero s => simp only [hx, is_nan_FF] at h_nan; exact absurd h_nan Bool.false_ne_true
    | F754_infinity s => simp only [hx, is_nan_FF] at h_nan; exact absurd h_nan Bool.false_ne_true
    | F754_nan s pl =>
      -- x is NaN, so by Ny, y must also be NaN
      simp only [hx] at Ny
      cases y with
      | B754_zero s => simp [BSN_is_nan, is_nan_FF] at Ny
      | B754_infinity s => simp [BSN_is_nan, is_nan_FF] at Ny
      | B754_nan => simp [B2BSN, FF2B, hx]
      | B754_finite s m e => simp [BSN_is_nan, is_nan_FF] at Ny
    | F754_finite s m e => simp only [hx, is_nan_FF] at h_nan; exact absurd h_nan Bool.false_ne_true
  · -- Case is_nan_FF x = false: lift returns BSN2B' y nx
    rename_i h_not_nan
    unfold BSN2B' B2BSN FF2B
    cases y with
    | B754_zero s => rfl
    | B754_infinity s => rfl
    | B754_nan =>
      -- Contradiction: BSN_is_nan B754_nan = true but is_nan_FF x = false
      simp [BSN_is_nan] at Ny
      rw [Ny] at h_not_nan
      simp at h_not_nan
    | B754_finite s m e => rfl

-- Coq: B2BSN_BSN2B' — roundtrip through the non-NaN bridge
def B2BSN_BSN2B'_check {prec emax : Int} (x : B754)
  (nx : BSN_is_nan x = false) : B754 :=
  (B2BSN (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) (BSN2B' x nx)))

theorem B2BSN_BSN2B' {prec emax : Int} (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (B2BSN_BSN2B'_check (prec:=prec) (emax:=emax) x nx) : Id B754)
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2BSN_BSN2B'_check BSN2B' B2BSN FF2B
  cases x <;> simp [BSN_is_nan] at nx <;> rfl

-- Coq: B2R_BSN2B' — real semantics preserved through BSN2B' on non-NaN values
noncomputable def B2R_BSN2B'_check (x : B754)
  (nx : BSN_is_nan x = false) : ℝ :=
  (FF2R 2 (BSN2B' x nx))

theorem B2R_BSN2B' (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (B2R_BSN2B'_check x nx) : Id ℝ)
  ⦃⇓result => ⌜result = B754_to_R x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2R_BSN2B'_check BSN2B'
  cases x <;> simp [B754_to_R, BSN_is_nan] at nx <;> rfl

-- Coq: B2FF_BSN2B' — standard full-float view after BSN2B'
def B2FF_BSN2B'_check {prec emax : Int} (x : B754)
  (nx : BSN_is_nan x = false) : FullFloat :=
  (B2FF (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) (BSN2B' x nx)))

theorem B2FF_BSN2B' {prec emax : Int} (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (B2FF_BSN2B'_check (prec:=prec) (emax:=emax) x nx) : Id FullFloat)
  ⦃⇓result => ⌜result = SF2FF (B2SF_BSN x)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2FF_BSN2B'_check BSN2B' B2SF_BSN
  cases x <;> simp [BSN_is_nan] at nx <;> rfl

-- Coq: Bsign_BSN2B' — sign preserved through BSN2B' on non-NaN values
def Bsign_BSN2B'_check (x : B754)
  (nx : BSN_is_nan x = false) : Bool :=
  (sign_FF (BSN2B' x nx))

theorem Bsign_BSN2B' (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (Bsign_BSN2B'_check x nx) : Id Bool)
  ⦃⇓result => ⌜result = BSN_sign x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold Bsign_BSN2B'_check BSN2B'
  cases x <;> simp [BSN_is_nan, BSN_sign] at nx <;> rfl

-- Coq: is_finite_BSN2B' — finiteness preserved through BSN2B'
def is_finite_BSN2B'_check (x : B754)
  (nx : BSN_is_nan x = false) : Bool :=
  (is_finite_FF (BSN2B' x nx))

theorem is_finite_BSN2B' (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (is_finite_BSN2B'_check x nx) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_finite x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_BSN2B'_check BSN2B'
  cases x <;> simp [BSN_is_nan, BSN_is_finite] at nx <;> rfl

-- Coq: is_nan_BSN2B' — NaN predicate preserved through BSN2B' (trivially false)
def is_nan_BSN2B'_check (x : B754)
  (nx : BSN_is_nan x = false) : Bool :=
  (is_nan_FF (BSN2B' x nx))

theorem is_nan_BSN2B' (x : B754)
  (nx : BSN_is_nan x = false) :
  ⦃⌜True⌝⦄
  (pure (is_nan_BSN2B'_check x nx) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_nan_BSN2B'_check BSN2B'
  cases x <;> simp [BSN_is_nan] at nx <;> rfl

-- Coq: B2R_BSN2B — real semantics preserved through BSN2B
noncomputable def B2R_BSN2B_check (s : Bool) (payload : Nat) (x : B754) : ℝ :=
  (FF2R 2 (BSN2B s payload x))

theorem B2R_BSN2B (s : Bool) (payload : Nat) (x : B754) :
  ⦃⌜True⌝⦄
  (pure (B2R_BSN2B_check s payload x) : Id ℝ)
  ⦃⇓result => ⌜result = B754_to_R x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2R_BSN2B_check BSN2B FF2R B754_to_R
  cases x <;> rfl

-- Coq: B2R_SF2B — real semantics after SF2B equals SF2R of source
noncomputable def B2R_SF2B_check (x : StandardFloat) : ℝ :=
  (B754_to_R (SF2B x))

theorem B2R_SF2B (x : StandardFloat) :
  ⦃⌜True⌝⦄
  (pure (B2R_SF2B_check x) : Id ℝ)
  ⦃⇓result => ⌜result = SF2R 2 x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold B2R_SF2B_check B754_to_R SF2B SF2R
  cases x <;> rfl

-- Coq: is_nan_SF_B2SF — NaN predicate after B2SF matches BSN-side NaN
def is_nan_SF_B2SF_check (x : B754) : Bool :=
  (is_nan_SF (B2SF_BSN x))

theorem is_nan_SF_B2SF (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_nan_SF_B2SF_check x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_nan_SF_B2SF_check is_nan_SF B2SF_BSN BSN_is_nan
  cases x <;> rfl

-- Coq: is_finite_SF_B2SF — finiteness after B2SF matches BSN-side finiteness
def is_finite_SF_B2SF_check (x : B754) : Bool :=
  (is_finite_SF (B2SF_BSN x))

theorem is_finite_SF_B2SF (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_finite_SF_B2SF_check x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_finite x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_SF_B2SF_check is_finite_SF B2SF_BSN BSN_is_finite
  cases x <;> rfl

-- Coq: is_finite_BSN2B — finiteness preserved through BSN2B
def is_finite_BSN2B_check (s : Bool) (payload : Nat) (x : B754) : Bool :=
  (is_finite_FF (BSN2B s payload x))

theorem is_finite_BSN2B (s : Bool) (payload : Nat) (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_finite_BSN2B_check s payload x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_finite x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_BSN2B_check is_finite_FF BSN2B BSN_is_finite
  cases x <;> rfl

-- Coq: is_nan_BSN2B — NaN preserved through BSN2B
def is_nan_BSN2B_check (s : Bool) (payload : Nat) (x : B754) : Bool :=
  (is_nan_FF (BSN2B s payload x))

theorem is_nan_BSN2B (s : Bool) (payload : Nat) (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_nan_BSN2B_check s payload x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_nan_BSN2B_check is_nan_FF BSN2B BSN_is_nan
  cases x <;> rfl

-- Valid B754 predicate
def validB754 (x : B754) : Prop :=
  match x with
  | B754.B754_finite s m e =>
    -- Mantissa in range and exponent constraints
    (1 ≤ m : Prop) ∧ (m < 2^(Int.natAbs (prec - 1) : Nat) : Prop) ∧
    (3 - emax - prec ≤ e : Prop) ∧ (e ≤ emax - prec : Prop)
  | _ => True

-- Coq: shr_m_shr_record_of_loc
theorem shr_m_shr_record_of_loc (m : Int) (l : Loc) :
    (shr_record_of_loc m l).shr_m = m := by
  cases l with
  | loc_Exact => rfl
  | loc_Inexact ord =>
      cases ord <;> rfl

-- Coq: loc_of_shr_record_of_loc
theorem loc_of_shr_record_of_loc (m : Int) (l : Loc) :
    loc_of_shr_record (shr_record_of_loc m l) = l := by
  cases l with
  | loc_Exact => rfl
  | loc_Inexact ord =>
      cases ord <;> rfl

-- Coq: shr_1
def shr_1 (mrs : ShrRecord) : ShrRecord :=
  let sticky := mrs.shr_r || mrs.shr_s
  let half :=
    if mrs.shr_m < 0 then
      -(((mrs.shr_m.natAbs / 2 : Nat) : Int))
    else
      mrs.shr_m / 2
  { shr_m := half
    shr_r := decide (mrs.shr_m % 2 ≠ 0)
    shr_s := sticky }

private lemma shr_1_shr_m_of_nonneg (mrs : ShrRecord)
    (hm : 0 ≤ mrs.shr_m) :
    (shr_1 mrs).shr_m = mrs.shr_m / 2 := by
  simp [shr_1, not_lt.mpr hm]

private lemma loc_of_shr_record_shr_1_of_nonneg (mrs : ShrRecord)
    (_hm : 0 ≤ mrs.shr_m) :
    FloatSpec.Calc.Bracket.new_location (nb_steps := (2 : Int))
      (k := mrs.shr_m % 2) (loc_of_shr_record mrs) =
      loc_of_shr_record (shr_1 mrs) := by
  rcases mrs with ⟨m, r, s⟩
  rcases Int.emod_two_eq_zero_or_one m with hrem | hrem
  · cases r <;> cases s <;>
      simp [shr_1, loc_of_shr_record, FloatSpec.Calc.Bracket.new_location,
        FloatSpec.Calc.Bracket.new_location_even, hrem]
  · cases r <;> cases s <;>
      simp [shr_1, loc_of_shr_record, FloatSpec.Calc.Bracket.new_location,
        FloatSpec.Calc.Bracket.new_location_even, hrem]

-- Coq: inbetween_shr_1
theorem inbetween_shr_1 (x : ℝ) (mrs : ShrRecord) (e : Int)
    (Hm : 0 ≤ mrs.shr_m)
    (Hl : FloatSpec.Calc.Bracket.inbetween_float 2 mrs.shr_m e x
      (loc_of_shr_record mrs)) :
    FloatSpec.Calc.Bracket.inbetween_float 2 (shr_1 mrs).shr_m (e + 1) x
      (loc_of_shr_record (shr_1 mrs)) := by
  have hbase :=
    FloatSpec.Calc.Bracket.inbetween_float_new_location_single
      (beta := 2) (x := x) (m := mrs.shr_m) (e := e)
      (l := loc_of_shr_record mrs) (hbeta := by norm_num) Hl
  have hm_eq := shr_1_shr_m_of_nonneg mrs Hm
  have hloc_eq := loc_of_shr_record_shr_1_of_nonneg mrs Hm
  simpa [← hm_eq, hloc_eq] using hbase

-- Coq: shr
def shr (mrs : ShrRecord) (e n : Int) : ShrRecord × Int :=
  if 0 ≤ n then
    (FloatSpec.Core.Zaux.iter_nat shr_1 n.toNat mrs, e + n)
  else
    (mrs, e)

-- Coq: shr_nat
theorem shr_nat (mrs : ShrRecord) (e n : Int) (Hn : 0 ≤ n) :
    shr mrs e n = (FloatSpec.Core.Zaux.iter_nat shr_1 n.toNat mrs, e + n) := by
  simp [shr, Hn]

-- Coq: le_shr1_le
theorem le_shr1_le (mrs : ShrRecord) (Hm : 0 ≤ mrs.shr_m) :
    0 ≤ (shr_1 mrs).shr_m ∧
      (2 * (shr_1 mrs).shr_m ≤ mrs.shr_m ∧
        mrs.shr_m < 2 * ((shr_1 mrs).shr_m + 1)) := by
  have hm_eq := shr_1_shr_m_of_nonneg mrs Hm
  have hq_nonneg : 0 ≤ mrs.shr_m / 2 :=
    Int.ediv_nonneg Hm (by norm_num : (0 : Int) ≤ 2)
  have hmod_nonneg : 0 ≤ mrs.shr_m % 2 :=
    Int.emod_nonneg mrs.shr_m (by norm_num : (2 : Int) ≠ 0)
  have hmod_lt : mrs.shr_m % 2 < 2 :=
    Int.emod_lt_of_pos mrs.shr_m (by norm_num : (0 : Int) < 2)
  have hdivmod : 2 * (mrs.shr_m / 2) + mrs.shr_m % 2 = mrs.shr_m :=
    Int.mul_ediv_add_emod mrs.shr_m 2
  constructor
  · simpa [hm_eq] using hq_nonneg
  · constructor
    · grind
    · grind

-- Coq: inbetween_shr
theorem inbetween_shr (x : ℝ) (m e : Int) (l : Loc) (n : Int)
    (Hm : 0 ≤ m)
    (Hl : FloatSpec.Calc.Bracket.inbetween_float 2 m e x l) :
    let (mrs, e') := shr (shr_record_of_loc m l) e n
    FloatSpec.Calc.Bracket.inbetween_float 2 mrs.shr_m e' x
      (loc_of_shr_record mrs) := by
  by_cases Hn : 0 ≤ n
  · let start := shr_record_of_loc m l
    have hstart_nonneg : 0 ≤ start.shr_m := by
      simpa [start, shr_m_shr_record_of_loc] using Hm
    have hstart_between :
        FloatSpec.Calc.Bracket.inbetween_float 2 start.shr_m e x
          (loc_of_shr_record start) := by
      simpa [start, shr_m_shr_record_of_loc, loc_of_shr_record_of_loc] using Hl
    have hiter :
        ∀ k : Nat,
          0 ≤ (FloatSpec.Core.Zaux.iter_nat shr_1 k start).shr_m ∧
            FloatSpec.Calc.Bracket.inbetween_float 2
              (FloatSpec.Core.Zaux.iter_nat shr_1 k start).shr_m
              (e + (k : Int)) x
              (loc_of_shr_record (FloatSpec.Core.Zaux.iter_nat shr_1 k start)) := by
      intro k
      induction k with
      | zero =>
          constructor
          · simpa [FloatSpec.Core.Zaux.iter_nat] using hstart_nonneg
          · simpa [FloatSpec.Core.Zaux.iter_nat] using hstart_between
      | succ k ih =>
          have hstep :=
            inbetween_shr_1 x (FloatSpec.Core.Zaux.iter_nat shr_1 k start)
              (e + (k : Int)) ih.1 ih.2
          constructor
          · exact (le_shr1_le (FloatSpec.Core.Zaux.iter_nat shr_1 k start) ih.1).1
          · simpa [FloatSpec.Core.Zaux.iter_nat, Nat.cast_add, Nat.cast_one,
              add_assoc] using hstep
    have hn_cast : (n.toNat : Int) = n := Int.toNat_of_nonneg Hn
    have hres := (hiter n.toNat).2
    simpa [shr, Hn, start, hn_cast] using hres
  · simpa [shr, Hn, shr_m_shr_record_of_loc, loc_of_shr_record_of_loc] using Hl

-- Coq: le_shr_le
theorem le_shr_le (mrs : ShrRecord) (e n : Int)
    (Hmrs : 0 ≤ mrs.shr_m) (Hn : 0 ≤ n) :
    0 ≤ (shr mrs e n).1.shr_m ∧
      ((2 : Int) ^ n.toNat * (shr mrs e n).1.shr_m ≤ mrs.shr_m ∧
        mrs.shr_m < (2 : Int) ^ n.toNat * ((shr mrs e n).1.shr_m + 1)) := by
  have hiter :
      ∀ k : Nat,
        0 ≤ (FloatSpec.Core.Zaux.iter_nat shr_1 k mrs).shr_m ∧
          ((2 : Int) ^ k * (FloatSpec.Core.Zaux.iter_nat shr_1 k mrs).shr_m ≤
              mrs.shr_m ∧
            mrs.shr_m <
              (2 : Int) ^ k *
                ((FloatSpec.Core.Zaux.iter_nat shr_1 k mrs).shr_m + 1)) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simpa [FloatSpec.Core.Zaux.iter_nat] using Hmrs
        · constructor
          · simp [FloatSpec.Core.Zaux.iter_nat]
          · have : mrs.shr_m < mrs.shr_m + 1 := by omega
            simpa [FloatSpec.Core.Zaux.iter_nat] using this
    | succ k ih =>
        set prev := FloatSpec.Core.Zaux.iter_nat shr_1 k mrs
        have hp_nonneg : 0 ≤ (2 : Int) ^ k := pow_nonneg (by norm_num) k
        have hstep := le_shr1_le prev ih.1
        constructor
        · simpa [FloatSpec.Core.Zaux.iter_nat, prev] using hstep.1
        · constructor
          · have hmul :
                (2 : Int) ^ k * (2 * (shr_1 prev).shr_m) ≤
                  (2 : Int) ^ k * prev.shr_m :=
              mul_le_mul_of_nonneg_left hstep.2.1 hp_nonneg
            have htarget :
                (2 : Int) ^ (k + 1) * (shr_1 prev).shr_m ≤ mrs.shr_m := by
              apply le_trans ?_ ih.2.1
              calc
                (2 : Int) ^ (k + 1) * (shr_1 prev).shr_m
                    = (2 : Int) ^ k * (2 * (shr_1 prev).shr_m) := by
                        rw [pow_succ']
                        ring
                _ ≤ (2 : Int) ^ k * prev.shr_m := hmul
            simpa [FloatSpec.Core.Zaux.iter_nat, prev] using htarget
          · have hprev_le :
                prev.shr_m + 1 ≤ 2 * ((shr_1 prev).shr_m + 1) := by
              omega
            have hmul :
                (2 : Int) ^ k * (prev.shr_m + 1) ≤
                  (2 : Int) ^ k * (2 * ((shr_1 prev).shr_m + 1)) :=
              mul_le_mul_of_nonneg_left hprev_le hp_nonneg
            have htarget :
                mrs.shr_m <
                  (2 : Int) ^ (k + 1) * ((shr_1 prev).shr_m + 1) := by
              apply lt_of_lt_of_le ih.2.2
              calc
                (2 : Int) ^ k * (prev.shr_m + 1)
                    ≤ (2 : Int) ^ k * (2 * ((shr_1 prev).shr_m + 1)) := hmul
                _ = (2 : Int) ^ (k + 1) * ((shr_1 prev).shr_m + 1) := by
                    rw [pow_succ']
                    ring
            simpa [FloatSpec.Core.Zaux.iter_nat, prev] using htarget
  simpa [shr, Hn] using hiter n.toNat

private def zeroStickyShrRecord : ShrRecord :=
  { shr_m := 0, shr_r := false, shr_s := true }

private def zpow2 (e : Int) : Int :=
  if 0 ≤ e then (2 : Int) ^ e.toNat else 0

private lemma shr_1_zeroStickyShrRecord :
    shr_1 zeroStickyShrRecord = zeroStickyShrRecord := by
  simp [zeroStickyShrRecord, shr_1]

private lemma iter_nat_apply_comm {A : Type} (f : A → A) :
    ∀ (k : Nat) (x : A),
      FloatSpec.Core.Zaux.iter_nat f k (f x) =
        f (FloatSpec.Core.Zaux.iter_nat f k x)
  | 0, _ => rfl
  | k + 1, x => by
      simp [FloatSpec.Core.Zaux.iter_nat, iter_nat_apply_comm f k x]

private lemma shr_limit_nat (mrs : ShrRecord) :
    ∀ k : Nat,
      (0 < mrs.shr_m ∨
        mrs.shr_m = 0 ∧ (mrs.shr_r || mrs.shr_s = true)) →
      mrs.shr_m < (2 : Int) ^ k →
      FloatSpec.Core.Zaux.iter_nat shr_1 (k + 1) mrs = zeroStickyShrRecord
  | 0, Hmrs0, Hlt => by
      rcases mrs with ⟨m, r, s⟩
      change m < (2 : Int) ^ 0 at Hlt
      rcases Hmrs0 with hmpos | ⟨hmzero, hsticky⟩
      · change 0 < m at hmpos
        omega
      · change m = 0 at hmzero
        subst m
        cases r <;> cases s <;>
          simp [FloatSpec.Core.Zaux.iter_nat, zeroStickyShrRecord, shr_1] at hsticky ⊢
  | k + 1, Hmrs0, Hlt => by
      have hm_nonneg : 0 ≤ mrs.shr_m := by
        rcases Hmrs0 with hmpos | ⟨hmzero, _⟩
        · exact le_of_lt hmpos
        · omega
      have hstep := le_shr1_le mrs hm_nonneg
      have hnext0 :
          0 < (shr_1 mrs).shr_m ∨
            (shr_1 mrs).shr_m = 0 ∧
              ((shr_1 mrs).shr_r || (shr_1 mrs).shr_s = true) := by
        by_cases hpos : 0 < (shr_1 mrs).shr_m
        · exact Or.inl hpos
        · have hzero : (shr_1 mrs).shr_m = 0 := by omega
          refine Or.inr ⟨hzero, ?_⟩
          rcases mrs with ⟨m, r, s⟩
          rcases Hmrs0 with hmpos | ⟨hmzero, hsticky⟩
          · change 0 < m at hmpos
            have hm_lt_two : m < 2 := by
              simpa [hzero] using hstep.2.2
            have hm_one : m = 1 := by
              have hm_ge_one : 1 ≤ m := by omega
              omega
            simp [shr_1, hm_one]
          · change m = 0 at hmzero
            cases r <;> cases s <;>
              simp [shr_1, hmzero] at hsticky ⊢
      have hnext_lt : (shr_1 mrs).shr_m < (2 : Int) ^ k := by
        have hp_pos : 0 < (2 : Int) ^ k := pow_pos (by norm_num) k
        have hmul_lt :
            2 * (shr_1 mrs).shr_m < 2 * (2 : Int) ^ k := by
          calc
            2 * (shr_1 mrs).shr_m ≤ mrs.shr_m := hstep.2.1
            _ < (2 : Int) ^ (k + 1) := Hlt
            _ = 2 * (2 : Int) ^ k := by
                rw [pow_succ']
        exact (Int.mul_lt_mul_left (by norm_num : (0 : Int) < 2)).mp hmul_lt
      have ih := shr_limit_nat (shr_1 mrs) k hnext0 hnext_lt
      have hcomm := iter_nat_apply_comm shr_1 (k + 1) mrs
      change shr_1 (FloatSpec.Core.Zaux.iter_nat shr_1 (k + 1) mrs) =
        zeroStickyShrRecord
      rw [← hcomm]
      exact ih

-- Coq: shr_limit
theorem shr_limit (mrs : ShrRecord) (e n : Int)
    (Hmrs0 : 0 < mrs.shr_m ∨
      mrs.shr_m = 0 ∧ (mrs.shr_r || mrs.shr_s = true))
    (Hlt : mrs.shr_m < zpow2 (n - 1)) :
    (shr mrs e n).1 = zeroStickyShrRecord := by
  by_cases Hn1 : 0 ≤ n - 1
  · have hn_pos : 0 < n := by omega
    have hn_nonneg : 0 ≤ n := le_of_lt hn_pos
    have hn_pred_cast : ((n - 1).toNat : Int) = n - 1 :=
      Int.toNat_of_nonneg Hn1
    have hn_toNat_succ : n.toNat = (n - 1).toNat + 1 := by
      apply Int.ofNat.inj
      calc
        (n.toNat : Int) = n := Int.toNat_of_nonneg hn_nonneg
        _ = n - 1 + 1 := by ring
        _ = ((n - 1).toNat : Int) + 1 := by rw [hn_pred_cast]
        _ = (((n - 1).toNat + 1 : Nat) : Int) := by norm_num
    have hlt_pow : mrs.shr_m < (2 : Int) ^ (n - 1).toNat := by
      unfold zpow2 at Hlt
      rw [ite_eq_left Hn1] at Hlt
      exact Hlt
    have hlim := shr_limit_nat mrs (n - 1).toNat Hmrs0 hlt_pow
    rw [shr_nat mrs e n hn_nonneg]
    simp only [Prod.fst]
    rw [hn_toNat_succ]
    exact hlim
  · have hm_nonneg : 0 ≤ mrs.shr_m := by
      rcases Hmrs0 with hmpos | ⟨hmzero, _⟩
      · exact le_of_lt hmpos
      · omega
    have hlt_neg : mrs.shr_m < 0 := by
      unfold zpow2 at Hlt
      rw [ite_eq_right Hn1] at Hlt
      exact Hlt
    omega

private lemma shr_record_eq_of_m_loc (a b : ShrRecord)
    (Hm : a.shr_m = b.shr_m)
    (Hl : loc_of_shr_record a = loc_of_shr_record b) :
    a = b := by
  cases a with
  | mk am ar as =>
      cases b with
      | mk bm br bs =>
          cases ar <;> cases as <;> cases br <;> cases bs <;>
            simp [loc_of_shr_record] at Hm Hl ⊢ <;> assumption

-- Coq: shr_truncate
theorem shr_truncate (fexp : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp fexp]
    (m e : Int) (l : Loc) (Hm : 0 ≤ m) :
    shr (shr_record_of_loc m l) e
        (fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) - e) =
      let r := FloatSpec.Calc.Round.truncate_triple (beta := 2) (fexp := fexp) (m, e, l)
      let m' := r.1
      let e' := r.2.1
      let l' := r.2.2
      (shr_record_of_loc m' l', e') := by
  classical
  by_cases Hshift : 0 < fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) - e
  · set k : Int := fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) - e with hk
    have Hk : 0 < k := by simpa [hk] using Hshift
    have Hk_nonneg : 0 ≤ k := le_of_lt Hk
    rcases FloatSpec.Calc.Bracket.inbetween_float_ex
        (beta := 2) (m := m) (e := e) (l := l) (by norm_num) with ⟨x, Hx⟩
    have Hshr :=
      inbetween_shr x m e l k Hm Hx
    have Htrunc :=
      FloatSpec.Calc.Bracket.inbetween_float_new_location
        (beta := 2) (x := x) (m := m) (e := e) (l := l) (k := k)
        Hk (by norm_num) Hx
    let mrs := (FloatSpec.Core.Zaux.iter_nat shr_1 k.toNat (shr_record_of_loc m l))
    have Hshr' :
        FloatSpec.Calc.Bracket.inbetween_float 2 mrs.shr_m (e + k) x
          (loc_of_shr_record mrs) := by
      have hk_cast : (k.toNat : Int) = k := Int.toNat_of_nonneg Hk_nonneg
      simpa [mrs, shr, Hk_nonneg, hk_cast] using Hshr
    have Htrunc' :
        FloatSpec.Calc.Bracket.inbetween_float 2
          (m / (2 ^ k.natAbs)) (e + k) x
          (FloatSpec.Calc.Bracket.new_location (nb_steps := (2 : Int) ^ k.natAbs)
            (k := m % ((2 : Int) ^ k.natAbs)) l) := by
      simpa using Htrunc
    rcases FloatSpec.Calc.Bracket.inbetween_float_unique
        (beta := 2) (x := x) (e := e + k)
        (m := mrs.shr_m) (l := loc_of_shr_record mrs)
        (m' := m / (2 ^ k.natAbs))
        (l' := FloatSpec.Calc.Bracket.new_location (nb_steps := (2 : Int) ^ k.natAbs)
          (k := m % ((2 : Int) ^ k.natAbs)) l)
        Hshr' Htrunc' (by norm_num) with ⟨Hmant, Hloc⟩
    have Hrec :
        mrs =
          shr_record_of_loc (m / (2 ^ k.natAbs))
            (FloatSpec.Calc.Bracket.new_location (nb_steps := (2 : Int) ^ k.natAbs)
              (k := m % ((2 : Int) ^ k.natAbs)) l) := by
      apply shr_record_eq_of_m_loc
      · simpa [shr_m_shr_record_of_loc] using Hmant
      · simpa [loc_of_shr_record_of_loc] using Hloc
    have hk_cast : (k.toNat : Int) = k := Int.toNat_of_nonneg Hk_nonneg
    have Hk' : e < fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) := by
      rw [hk] at Hk
      omega
    have Hshift_nonneg : 0 ≤ fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) - e :=
      le_of_lt Hshift
    have Hrec_expr :
        FloatSpec.Core.Zaux.iter_nat shr_1
            (fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) - e).toNat
            (shr_record_of_loc m l) =
          shr_record_of_loc
            (m / (2 ^ (fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) - e).natAbs))
            (FloatSpec.Calc.Bracket.new_location
              (nb_steps := (2 : Int) ^ (fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) - e).natAbs)
              (k := m % ((2 : Int) ^ (fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) - e).natAbs))
              l) := by
      simpa [hk, mrs] using Hrec
    simp [shr, FloatSpec.Calc.Round.truncate_triple, FloatSpec.Calc.Round.truncate_aux,
      Hshift, Hshift_nonneg, Hk_nonneg, Hk', Hrec, Hrec_expr, hk, mrs]
    intro Hbad
    omega
  · by_cases Hshift_nonneg : 0 ≤ fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) - e
    · have Hshift_zero : fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) - e = 0 := by
        omega
      have Hf_eq : fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) = e := by
        omega
      have Hnot_lt : ¬ e < fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) := by
        omega
      simp [shr, FloatSpec.Core.Zaux.iter_nat, FloatSpec.Calc.Round.truncate_triple,
        Hshift, Hnot_lt,
        Hshift_nonneg, Hshift_zero, Hf_eq]
    · have Hnot_lt : ¬ e < fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) := by
        omega
      have Hnot_le : ¬ e ≤ fexp (FloatSpec.Core.Digits.Zdigits 2 m + e) := by
        omega
      simp [shr, FloatSpec.Calc.Round.truncate_triple, Hshift, Hnot_lt,
        Hshift_nonneg, Hnot_le]

-- Coq: choice_mode
def choice_mode (mode : RoundingMode) (sx : Bool) (mx : Int) (lx : Loc) : Int :=
  match mode with
  | RoundingMode.RNE =>
      FloatSpec.Calc.Round.cond_incr
        (FloatSpec.Calc.Round.round_N (!(decide (2 ∣ mx))) lx) mx
  | RoundingMode.RTZ => mx
  | RoundingMode.RTN =>
      FloatSpec.Calc.Round.cond_incr
        (FloatSpec.Calc.Round.round_sign_DN sx lx) mx
  | RoundingMode.RTP =>
      FloatSpec.Calc.Round.cond_incr
        (FloatSpec.Calc.Round.round_sign_UP sx lx) mx
  | RoundingMode.RNA =>
      FloatSpec.Calc.Round.cond_incr
        (FloatSpec.Calc.Round.round_N true lx) mx

-- Coq: le_choice_mode_le
theorem le_choice_mode_le (mode : RoundingMode) (sx : Bool) (mx : Int) (lx : Loc) :
    mx ≤ choice_mode mode sx mx lx ∧ choice_mode mode sx mx lx ≤ mx + 1 := by
  cases mode <;>
    simp [choice_mode, FloatSpec.Calc.Round.le_cond_incr_le]

-- Coq: round_mode_choice_mode
theorem round_mode_choice_mode (mode : RoundingMode) (x : ℝ) (m : Int) (l : Loc)
    (Hl : FloatSpec.Calc.Round.inbetween_int m |x| l) :
    rnd_of_mode mode x =
      FloatSpec.Core.Zaux.cond_Zopp (FloatSpec.Core.Raux.Rlt_bool x 0)
        (choice_mode mode (FloatSpec.Core.Raux.Rlt_bool x 0) m l) := by
  cases mode
  · simpa [choice_mode, rnd_of_mode] using
      (FloatSpec.Calc.Round.inbetween_int_NE_sign (x := x) (m := m) (l := l) Hl)
  · simpa [choice_mode, rnd_of_mode] using
      (FloatSpec.Calc.Round.inbetween_int_NA_sign (x := x) (m := m) (l := l) Hl)
  · simpa [choice_mode, rnd_of_mode] using
      (FloatSpec.Calc.Round.inbetween_int_UP_sign (x := x) (m := m) (l := l) Hl)
  · simpa [choice_mode, rnd_of_mode, FloatSpec.Calc.Round.round_sign_DN,
      FloatSpec.Calc.Round.round_sign_DN'] using
      (FloatSpec.Calc.Round.inbetween_int_DN_sign (x := x) (m := m) (l := l) Hl)
  · simpa [choice_mode, rnd_of_mode] using
      (FloatSpec.Calc.Round.inbetween_int_ZR_sign (x := x) (m := m) (l := l) Hl)

-- Coq: SFnearbyint_binary_aux
def SFnearbyint_binary_aux (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int) : Int :=
  if 0 ≤ ex then
    (mx : Int) * zpow2 ex
  else
    let mrs : ShrRecord := { shr_m := (mx : Int), shr_r := false, shr_s := false }
    let mrs' :=
      if ex < -prec then
        zeroStickyShrRecord
      else
        (shr mrs ex (-ex)).fst
    let l' := loc_of_shr_record mrs'
    let mx' := mrs'.shr_m
    choice_mode mode sx mx' l'

-- Coq: SFnearbyint_binary
def SFnearbyint_binary (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int) :
    StandardFloat :=
  if 0 ≤ ex then
    StandardFloat.S754_finite sx mx ex
  else
    let mx'' := SFnearbyint_binary_aux (prec:=prec) mode sx mx ex
    if 0 < mx'' then
      let aligned := shl_align_fexp (prec:=prec) (emax:=emax) mx''.toNat 0
      StandardFloat.S754_finite sx aligned.1 aligned.2
    else if mx'' < 0 then
      StandardFloat.S754_nan
    else
      StandardFloat.S754_zero sx

omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
private theorem Zdigits_le_prec_of_specFloat_bounded
    (m : Nat) (e : Int)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax) m e = true) :
    FloatSpec.Core.Digits.Zdigits 2 (m : Int) ≤ prec := by
  have hcanon := canonical_mantissa_of_specFloat_bounded
    (prec:=prec) (emax:=emax) hbounded
  have heq :
      e = FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e) :=
    eq_of_beq hcanon
  unfold FLT_exp FloatSpec.Core.FLT.FLT_exp at heq
  have hleft :
      FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e - prec ≤ e := by
    calc
      FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e - prec
          ≤ max (FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e - prec)
              (3 - emax - prec) := le_max_left _ _
      _ = e := heq.symm
  omega

omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
private theorem SFnearbyint_shr_record_eq
    (mx : Nat) (ex : Int)
    (hmx_pos : 0 < mx)
    (Hx : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true)
    (hex_neg : ex < 0) :
    let mrs : ShrRecord :=
      { shr_m := (mx : Int), shr_r := false, shr_s := false }
    let mrs' :=
      if ex < -prec then zeroStickyShrRecord else (shr mrs ex (-ex)).fst
    mrs' = (shr mrs ex (-ex)).fst := by
  dsimp only
  by_cases hfar : ex < -prec
  · simp only [hfar, ↓reduceIte]
    symm
    apply shr_limit
    · left
      change (0 : Int) < (mx : Int)
      exact_mod_cast hmx_pos
    · have hrange := range_bounded_of_specFloat_bounded
        (prec:=prec) (emax:=emax) mx ex hmx_pos Hx
      have hrange' :
          (mx < (2 : Nat) ^ prec.toNat ∧ 3 - emax - prec ≤ ex) ∧
            ex ≤ emax - prec := by
        simpa [bounded, Bool.and_eq_true, decide_eq_true_eq] using hrange
      have hmx_lt : mx < (2 : Nat) ^ prec.toNat := hrange'.1.1
      have hdigits := Zdigits_le_prec_of_specFloat_bounded
        (prec:=prec) (emax:=emax) mx ex Hx
      have hdigits_pos : 0 < FloatSpec.Core.Digits.Zdigits 2 (mx : Int) := by
        have hmx_ne : (mx : Int) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmx_pos)
        have htrip := FloatSpec.Core.Digits.Zdigits_gt_0
          (beta:=2) (n:=(mx : Int)) (by norm_num) hmx_ne
        simpa [wp, PostCond.noThrow, pure] using htrip
      have hprec_nonneg : 0 ≤ prec := by omega
      have hshift_nonneg : 0 ≤ -ex - 1 := by omega
      have hnat_le : prec.toNat ≤ (-ex - 1).toNat := by
        have hprec_cast : (prec.toNat : Int) = prec :=
          Int.toNat_of_nonneg hprec_nonneg
        have hshift_cast : ((-ex - 1).toNat : Int) = -ex - 1 :=
          Int.toNat_of_nonneg hshift_nonneg
        omega
      have hpow_le :
          (2 : Int) ^ prec.toNat ≤ (2 : Int) ^ (-ex - 1).toNat :=
        pow_le_pow_right₀ (by norm_num : (1 : Int) ≤ 2) hnat_le
      have hmx_lt_int : (mx : Int) < (2 : Int) ^ prec.toNat := by
        exact_mod_cast hmx_lt
      unfold zpow2
      rw [ite_eq_left hshift_nonneg]
      exact lt_of_lt_of_le hmx_lt_int hpow_le
  · simp only [hfar, ↓reduceIte]

omit [Prec_gt_0 prec] in
private theorem validBinarySingleNaNStandardFloat_shl_align_fexp_zero
    (sx : Bool) (m : Nat)
    (hm_pos : 0 < m)
    (hdigits_le : FloatSpec.Core.Digits.Zdigits 2 (m : Int) ≤ prec) :
    let aligned := shl_align_fexp (prec:=prec) (emax:=emax) m 0
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
      (StandardFloat.S754_finite sx aligned.1 aligned.2) = true := by
  let target := FLT_exp (3 - emax - prec) prec
    (FloatSpec.Core.Digits.Zdigits 2 (m : Int) + 0)
  have hprec_pos : 0 < prec := by
    have hm_ne : (m : Int) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm_pos)
    have hdigits_pos : 0 < FloatSpec.Core.Digits.Zdigits 2 (m : Int) := by
      have htrip := FloatSpec.Core.Digits.Zdigits_gt_0
        (beta:=2) (n:=(m : Int)) (by norm_num) hm_ne
      simpa [wp, PostCond.noThrow, pure] using htrip
    omega
  have hemin_nonpos : 3 - emax - prec ≤ 0 := by
    have hprec_lt := (inferInstance : Prec_lt_emax prec emax).prec_lt_emax
    omega
  have htarget_nonpos : target ≤ 0 := by
    simp only [target, FLT_exp, FloatSpec.Core.FLT.FLT_exp]
    apply max_le
    · omega
    · exact hemin_nonpos
  have haligned :
      shl_align_fexp (prec:=prec) (emax:=emax) m 0 =
        (m * 2 ^ (0 - target).toNat, target) := by
    change shl_align m 0 target = (m * 2 ^ (0 - target).toNat, target)
    simp [shl_align, htarget_nonpos]
  have hshift_nonneg : 0 ≤ 0 - target := by omega
  have hshift_abs : (0 - target).natAbs = (0 - target).toNat := by
    apply Nat.cast_injective (R := Int)
    rw [Int.natAbs_of_nonneg hshift_nonneg, Int.toNat_of_nonneg hshift_nonneg]
  have hm_ne_int : (m : Int) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hm_pos)
  have hdigits_shift :
      FloatSpec.Core.Digits.Zdigits 2
          ((m * 2 ^ (0 - target).toNat : Nat) : Int) =
        FloatSpec.Core.Digits.Zdigits 2 (m : Int) + (0 - target) := by
    have htrip := FloatSpec.Core.Digits.Zdigits_mult_Zpower
      (beta := 2) (n := (m : Int)) (k := 0 - target) (by norm_num)
    simp only [wp, PostCond.noThrow, pure] at htrip
    rcases htrip ⟨hm_ne_int, hshift_nonneg⟩ with ⟨d, hd, hprod⟩
    have hprod' :
        FloatSpec.Core.Digits.Zdigits 2
            ((m : Int) * (2 : Int) ^ (0 - target).natAbs) =
          d + (0 - target) := by
      simpa using hprod
    have hcast :
        ((m * 2 ^ (0 - target).toNat : Nat) : Int) =
          (m : Int) * (2 : Int) ^ (0 - target).natAbs := by
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [hshift_abs]
    rw [hcast, hprod', ← hd]
  have hcanon :
      canonical_mantissa (prec:=prec) (emax:=emax)
        (m * 2 ^ (0 - target).toNat) target = true := by
    unfold canonical_mantissa
    apply beq_iff_eq.mpr
    rw [hdigits_shift]
    calc
      target = FLT_exp (3 - emax - prec) prec
          (FloatSpec.Core.Digits.Zdigits 2 (m : Int) + 0) := by rfl
      _ = FLT_exp (3 - emax - prec) prec
          ((FloatSpec.Core.Digits.Zdigits 2 (m : Int) + (0 - target)) + target) := by
            congr 1
            ring
  have hupper : target ≤ emax - prec := by
    have hgap_nonneg : 0 ≤ emax - prec := by
      have hprec_lt := (inferInstance : Prec_lt_emax prec emax).prec_lt_emax
      omega
    exact le_trans htarget_nonpos hgap_nonneg
  have haligned_pos : 0 < m * 2 ^ (0 - target).toNat :=
    Nat.mul_pos hm_pos (pow_pos (by norm_num) _)
  rw [haligned]
  simp only [validBinarySingleNaNStandardFloat, Bool.and_eq_true,
    decide_eq_true_eq, specFloat_bounded]
  constructor
  · exact haligned_pos
  · constructor
    · simpa using hcanon
    · exact hupper

omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
private theorem SFnearbyint_binary_aux_digits_le_prec
    (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int)
    (hmx_pos : 0 < mx)
    (Hx : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true)
    (hex_neg : ex < 0)
    (hrounded_pos : 0 < SFnearbyint_binary_aux (prec:=prec) mode sx mx ex) :
    FloatSpec.Core.Digits.Zdigits 2
      ((SFnearbyint_binary_aux (prec:=prec) mode sx mx ex).toNat : Int) ≤ prec := by
  let mrs : ShrRecord :=
    { shr_m := (mx : Int), shr_r := false, shr_s := false }
  let mrs' :=
    if ex < -prec then zeroStickyShrRecord else (shr mrs ex (-ex)).fst
  let rounded := choice_mode mode sx mrs'.shr_m (loc_of_shr_record mrs')
  have haux : SFnearbyint_binary_aux (prec:=prec) mode sx mx ex = rounded := by
    simp [SFnearbyint_binary_aux, not_le.mpr hex_neg, mrs, mrs', rounded]
  rw [haux] at hrounded_pos ⊢
  have hmrs_eq : mrs' = (shr mrs ex (-ex)).fst := by
    simpa [mrs, mrs'] using
      SFnearbyint_shr_record_eq (prec:=prec) (emax:=emax)
        mx ex hmx_pos Hx hex_neg
  have hshift_nonneg : 0 ≤ -ex := by omega
  have hshift_nat_pos : 0 < (-ex).toNat := by
    have hcast : ((-ex).toNat : Int) = -ex :=
      Int.toNat_of_nonneg hshift_nonneg
    omega
  have hshr := le_shr_le mrs ex (-ex) (by simp [mrs]) hshift_nonneg
  have hmrs_nonneg : 0 ≤ mrs'.shr_m := by
    rw [hmrs_eq]
    exact hshr.1
  have hpow_mrs_le :
      (2 : Int) ^ (-ex).toNat * mrs'.shr_m ≤ (mx : Int) := by
    rw [hmrs_eq]
    exact hshr.2.1
  have hpow_ge_two : (2 : Int) ≤ (2 : Int) ^ (-ex).toNat := by
    have hone_le : 1 ≤ (-ex).toNat := hshift_nat_pos
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : Int) ≤ 2) hone_le
    simpa using hpow
  have htwo_mrs_le : 2 * mrs'.shr_m ≤ (mx : Int) := by
    calc
      2 * mrs'.shr_m ≤ (2 : Int) ^ (-ex).toNat * mrs'.shr_m :=
        mul_le_mul_of_nonneg_right hpow_ge_two hmrs_nonneg
      _ ≤ (mx : Int) := hpow_mrs_le
  have hrange := range_bounded_of_specFloat_bounded
    (prec:=prec) (emax:=emax) mx ex hmx_pos Hx
  have hrange' :
      (mx < (2 : Nat) ^ prec.toNat ∧ 3 - emax - prec ≤ ex) ∧
        ex ≤ emax - prec := by
    simpa [bounded, Bool.and_eq_true, decide_eq_true_eq] using hrange
  have hmx_lt_int : (mx : Int) < (2 : Int) ^ prec.toNat := by
    exact_mod_cast hrange'.1.1
  have hdigits_input := Zdigits_le_prec_of_specFloat_bounded
    (prec:=prec) (emax:=emax) mx ex Hx
  have hdigits_input_pos : 0 < FloatSpec.Core.Digits.Zdigits 2 (mx : Int) := by
    have hmx_ne : (mx : Int) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmx_pos)
    have htrip := FloatSpec.Core.Digits.Zdigits_gt_0
      (beta:=2) (n:=(mx : Int)) (by norm_num) hmx_ne
    simpa [wp, PostCond.noThrow, pure] using htrip
  have hprec_nonneg : 0 ≤ prec := by omega
  have hprec_nat_pos : 0 < prec.toNat := by
    have hcast : (prec.toNat : Int) = prec :=
      Int.toNat_of_nonneg hprec_nonneg
    omega
  have hpow_prec_ge_two : (2 : Int) ≤ (2 : Int) ^ prec.toNat := by
    have hone_le : 1 ≤ prec.toNat := hprec_nat_pos
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : Int) ≤ 2) hone_le
    simpa using hpow
  have hmrs_succ_lt : mrs'.shr_m + 1 < (2 : Int) ^ prec.toNat := by
    omega
  have hrounded_le : rounded ≤ mrs'.shr_m + 1 :=
    (le_choice_mode_le mode sx mrs'.shr_m (loc_of_shr_record mrs')).2
  have hrounded_lt : rounded < (2 : Int) ^ prec.toNat :=
    lt_of_le_of_lt hrounded_le hmrs_succ_lt
  have hrounded_cast : (rounded.toNat : Int) = rounded :=
    Int.toNat_of_nonneg (le_of_lt hrounded_pos)
  have hprec_abs : prec.natAbs = prec.toNat := by
    apply Nat.cast_injective (R := Int)
    rw [Int.natAbs_of_nonneg hprec_nonneg, Int.toNat_of_nonneg hprec_nonneg]
  have htrip := FloatSpec.Core.Digits.Zdigits_le_Zpower
    (beta := 2) (x := (rounded.toNat : Int)) (e := prec) (by norm_num)
  simp only [wp, PostCond.noThrow, pure] at htrip
  apply htrip
  constructor
  · exact hprec_nonneg
  · simpa [hrounded_cast, hprec_abs, abs_of_pos hrounded_pos] using hrounded_lt

theorem Bnearbyint_correct_aux_nat {prec emax : Int}
    [Prec_lt_emax prec emax]
    (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int)
    (hmx_pos : 0 < mx)
    (Hx : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true) :
    let x := SF2R 2 (StandardFloat.S754_finite sx mx ex)
    let z := SFnearbyint_binary (prec:=prec) (emax:=emax) mode sx mx ex
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      SF2R 2 z = FloatSpec.Core.Generic_fmt.roundR 2
        (FloatSpec.Core.FIX.FIX_exp 0) (rnd_of_mode mode) x ∧
      is_finite_SF z = true ∧
      (is_nan_SF z = false → sign_SF z = sx) := by
  classical
  dsimp only
  by_cases hex_nonneg : 0 ≤ ex
  · have hgeneric :
        FloatSpec.Core.Generic_fmt.generic_format 2
          (FloatSpec.Core.FIX.FIX_exp 0)
          (SF2R 2 (StandardFloat.S754_finite sx mx ex)) := by
      have htrip := FloatSpec.Core.Generic_fmt.generic_format_F2R
        (beta := 2) (fexp := FloatSpec.Core.FIX.FIX_exp 0)
        (m := if sx then -(mx : Int) else (mx : Int)) (e := ex)
      have hpre :
          (2 : Int) > 1 ∧
            ((if sx then -(mx : Int) else (mx : Int)) ≠ 0 →
              FloatSpec.Core.Generic_fmt.cexp 2
                (FloatSpec.Core.FIX.FIX_exp 0)
                (F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                  (if sx then -(mx : Int) else (mx : Int)) ex :
                    FloatSpec.Core.Defs.FlocqFloat 2)) ≤ ex) := by
        constructor
        · norm_num
        · intro _
          simpa [FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.FIX.FIX_exp]
            using hex_nonneg
      cases sx <;>
        simpa [wp, PostCond.noThrow, pure, SF2R, F2R,
          FloatSpec.Core.Defs.F2R] using htrip hpre
    have hround :
        FloatSpec.Core.Generic_fmt.roundR 2
            (FloatSpec.Core.FIX.FIX_exp 0) (rnd_of_mode mode)
            (SF2R 2 (StandardFloat.S754_finite sx mx ex)) =
          SF2R 2 (StandardFloat.S754_finite sx mx ex) :=
      FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := 2) (fexp := FloatSpec.Core.FIX.FIX_exp 0)
        (rnd := rnd_of_mode mode)
        (x := SF2R 2 (StandardFloat.S754_finite sx mx ex))
        (by norm_num) hgeneric
    simp [SFnearbyint_binary, hex_nonneg,
      validBinarySingleNaNStandardFloat,
      hmx_pos, Hx, hround, is_finite_SF, is_nan_SF, sign_SF]
  · have hex_neg : ex < 0 := lt_of_not_ge hex_nonneg
    let mrs : ShrRecord :=
      { shr_m := (mx : Int), shr_r := false, shr_s := false }
    let mrs' :=
      if ex < -prec then zeroStickyShrRecord else (shr mrs ex (-ex)).fst
    let rounded := choice_mode mode sx mrs'.shr_m (loc_of_shr_record mrs')
    have haux : SFnearbyint_binary_aux (prec:=prec) mode sx mx ex = rounded := by
      simp [SFnearbyint_binary_aux, hex_nonneg, mrs, mrs', rounded]
    have hmrs_eq : mrs' = (shr mrs ex (-ex)).fst := by
      simpa [mrs, mrs'] using
        SFnearbyint_shr_record_eq (prec:=prec) (emax:=emax)
          mx ex hmx_pos Hx hex_neg
    have hshift_nonneg : 0 ≤ -ex := by omega
    have hshr := le_shr_le mrs ex (-ex) (by simp [mrs]) hshift_nonneg
    have hmrs_nonneg : 0 ≤ mrs'.shr_m := by
      rw [hmrs_eq]
      exact hshr.1
    have hrounded_nonneg : 0 ≤ rounded :=
      le_trans hmrs_nonneg
        (le_choice_mode_le mode sx mrs'.shr_m (loc_of_shr_record mrs')).1
    have habs :
        |SF2R 2 (StandardFloat.S754_finite sx mx ex)| =
          F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
            FloatSpec.Core.Defs.FlocqFloat 2) := by
      have hpow_nonneg : 0 ≤ (2 : ℝ) ^ ex :=
        le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) ex)
      have hmx_nonneg : 0 ≤ ((mx : Int) : ℝ) := by
        exact_mod_cast (Nat.zero_le mx)
      cases sx <;>
        simp [SF2R, F2R, FloatSpec.Core.Defs.F2R, abs_mul,
          hpow_nonneg, hmx_nonneg, abs_of_nonneg]
    have hbetween :
        FloatSpec.Calc.Bracket.inbetween_float 2 (mx : Int) ex
          |SF2R 2 (StandardFloat.S754_finite sx mx ex)|
          FloatSpec.Calc.Bracket.Location.loc_Exact := by
      unfold FloatSpec.Calc.Bracket.inbetween_float
      exact FloatSpec.Calc.Bracket.inbetween.inbetween_Exact habs
    have hsx :
        FloatSpec.Core.Raux.Rlt_bool
          (SF2R 2 (StandardFloat.S754_finite sx mx ex)) 0 = sx := by
      have hmx_int_pos : (0 : Int) < (mx : Int) := by exact_mod_cast hmx_pos
      cases sx <;>
        simp [SF2R, F2R, FloatSpec.Core.Defs.F2R,
          FloatSpec.Core.Raux.Rlt_bool] <;> positivity
    let r := FloatSpec.Calc.Round.truncate_triple
      (beta := 2) (fexp := FloatSpec.Core.FIX.FIX_exp 0)
      ((mx : Int), ex, FloatSpec.Calc.Bracket.Location.loc_Exact)
    have hround_raw := FloatSpec.Calc.Round.round_trunc_sign_any_correct
      (beta := 2) (fexp := FloatSpec.Core.FIX.FIX_exp 0)
      (rnd := rnd_of_mode mode)
      (choice := fun s m l => choice_mode mode s m l)
      (Hc := by
        intro y m l Hy
        exact round_mode_choice_mode mode y m l Hy)
      (x := SF2R 2 (StandardFloat.S754_finite sx mx ex))
      (m := (mx : Int)) (e := ex)
      (l := FloatSpec.Calc.Bracket.Location.loc_Exact)
      hbetween (Or.inr rfl) (by norm_num : (1 : Int) < 2)
    have hshr_pair : shr mrs ex (-ex) = (mrs', 0) := by
      apply Prod.ext
      · exact hmrs_eq.symm
      · simp [shr, le_of_lt hex_neg]
    have htrunc := shr_truncate
      (fexp := FloatSpec.Core.FIX.FIX_exp 0)
      (m := (mx : Int)) (e := ex)
      (l := FloatSpec.Calc.Bracket.Location.loc_Exact)
      (by exact_mod_cast (Nat.zero_le mx))
    have htrunc_eq :
        (mrs', 0) =
          (shr_record_of_loc r.1 r.2.2, r.2.1) := by
      calc
        (mrs', 0) = shr mrs ex (-ex) := hshr_pair.symm
        _ = (shr_record_of_loc r.1 r.2.2, r.2.1) := by
          simpa [mrs, r, shr_record_of_loc, FloatSpec.Core.FIX.FIX_exp] using htrunc
    have hr_m : r.1 = mrs'.shr_m := by
      have h := congrArg (fun p => p.1.shr_m) htrunc_eq
      simpa [shr_m_shr_record_of_loc] using h.symm
    have hr_e : r.2.1 = 0 := by
      have h := congrArg Prod.snd htrunc_eq
      exact h.symm
    have hr_l : r.2.2 = loc_of_shr_record mrs' := by
      have h := congrArg (fun p => loc_of_shr_record p.1) htrunc_eq
      simpa [loc_of_shr_record_of_loc] using h.symm
    have hround_value :
        FloatSpec.Core.Generic_fmt.roundR 2
            (FloatSpec.Core.FIX.FIX_exp 0) (rnd_of_mode mode)
            (SF2R 2 (StandardFloat.S754_finite sx mx ex)) =
          F2R (FloatSpec.Core.Defs.FlocqFloat.mk
            (FloatSpec.Core.Zaux.cond_Zopp sx rounded) 0 :
              FloatSpec.Core.Defs.FlocqFloat 2) := by
      simpa [r, hr_m, hr_e, hr_l, hsx, rounded, F2R,
        FloatSpec.Core.Defs.F2R] using hround_raw
    by_cases hrounded_pos : 0 < rounded
    · have haux_pos :
          0 < SFnearbyint_binary_aux (prec:=prec) mode sx mx ex := by
        simpa [haux] using hrounded_pos
      have hdigits := SFnearbyint_binary_aux_digits_le_prec
        (prec:=prec) (emax:=emax) mode sx mx ex hmx_pos Hx hex_neg haux_pos
      rw [haux] at hdigits
      let aligned := shl_align_fexp (prec:=prec) (emax:=emax) rounded.toNat 0
      have hrounded_cast : (rounded.toNat : Int) = rounded :=
        Int.toNat_of_nonneg (le_of_lt hrounded_pos)
      have hrounded_nat_pos : 0 < rounded.toNat := by
        omega
      have haligned_valid :
          validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
            (StandardFloat.S754_finite sx aligned.1 aligned.2) = true := by
        simpa [aligned, haux] using
          validBinarySingleNaNStandardFloat_shl_align_fexp_zero
            (prec:=prec) (emax:=emax) sx rounded.toNat
              hrounded_nat_pos hdigits
      have halign_trip := shl_align_fexp_correct
        (prec:=prec) (emax:=emax) rounded.toNat 0
          (Nat.ne_of_gt hrounded_nat_pos)
      have halign :
          F2R (FloatSpec.Core.Defs.FlocqFloat.mk (aligned.1 : Int) aligned.2 :
              FloatSpec.Core.Defs.FlocqFloat 2) =
            F2R (FloatSpec.Core.Defs.FlocqFloat.mk (rounded.toNat : Int) 0 :
              FloatSpec.Core.Defs.FlocqFloat 2) := by
        have h := halign_trip (Nat.ne_of_gt hrounded_nat_pos)
        simpa [wp, PostCond.noThrow, pure, shl_align_fexp_check, aligned] using h.1
      have halign_signed :
          SF2R 2 (StandardFloat.S754_finite sx aligned.1 aligned.2) =
            F2R (FloatSpec.Core.Defs.FlocqFloat.mk
              (FloatSpec.Core.Zaux.cond_Zopp sx rounded) 0 :
                FloatSpec.Core.Defs.FlocqFloat 2) := by
        cases sx
        · simpa [SF2R, FloatSpec.Core.Zaux.cond_Zopp, hrounded_cast] using halign
        · have hneg := congrArg Neg.neg halign
          simpa [SF2R, F2R, FloatSpec.Core.Defs.F2R,
            FloatSpec.Core.Zaux.cond_Zopp, hrounded_cast] using hneg
      simp [SFnearbyint_binary, hex_nonneg, haux, hrounded_pos, aligned,
        haligned_valid, halign_signed, hround_value,
        is_finite_SF, is_nan_SF, sign_SF]
    · have hrounded_zero : rounded = 0 := by omega
      have hround_zero :
          FloatSpec.Core.Generic_fmt.roundR 2
              (FloatSpec.Core.FIX.FIX_exp 0) (rnd_of_mode mode)
              (SF2R 2 (StandardFloat.S754_finite sx mx ex)) = 0 := by
        cases sx <;>
          simpa [hrounded_zero, F2R, FloatSpec.Core.Defs.F2R,
            FloatSpec.Core.Zaux.cond_Zopp] using hround_value
      rw [hround_zero]
      simp [SFnearbyint_binary, hex_nonneg, haux, hrounded_zero,
        validBinarySingleNaNStandardFloat,
        is_finite_SF, is_nan_SF, sign_SF, SF2R]

-- Coq: Bnearbyint_correct_aux
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
      (is_nan_SF z = false → sign_SF z = sx) := by
  exact Bnearbyint_correct_aux_nat (prec:=prec) (emax:=emax) mode sx
    (FloatSpec.Core.Zaux.positiveToNat mx) ex
    (FloatSpec.Core.Zaux.positiveToNat_pos mx) Hx

-- Coq: overflow_to_inf
def overflow_to_inf (mode : RoundingMode) (s : Bool) : Bool :=
  match mode with
  | RoundingMode.RNE => true
  | RoundingMode.RNA => true
  | RoundingMode.RTZ => false
  | RoundingMode.RTP => !s
  | RoundingMode.RTN => s

-- Coq: binary_overflow
--
-- The root name `binary_overflow` is already used by the Binary.v port for the
-- FullFloat variant, so the SingleNaN operation is kept under a BSN-qualified
-- helper name while the public theorems below keep the upstream names.
def bsn_binary_overflow (mode : RoundingMode) (s : Bool) : StandardFloat :=
  if overflow_to_inf mode s then
    StandardFloat.S754_infinity s
  else
    StandardFloat.S754_finite s ((2 : Nat) ^ prec.toNat - 1) (emax - prec)

-- Coq: is_nan_binary_overflow
omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
theorem is_nan_binary_overflow (mode : RoundingMode) (s : Bool) :
    is_nan_SF (bsn_binary_overflow (prec:=prec) (emax:=emax) mode s) = false := by
  cases mode <;> cases s <;> rfl

-- Coq: binary_overflow_correct
theorem binary_overflow_correct (mode : RoundingMode) (s : Bool) :
    valid_binary_SF (prec:=prec) (emax:=emax)
      (bsn_binary_overflow (prec:=prec) (emax:=emax) mode s) = true := by
  rfl

-- Coq: binary_fit_aux
def binary_fit_aux (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int) :
    StandardFloat :=
  if ex ≤ emax - prec then
    StandardFloat.S754_finite sx mx ex
  else
    bsn_binary_overflow (prec:=prec) (emax:=emax) mode sx

private theorem binary_fit_aux_bounded_of_canonical_le
    (mx : Nat) (ex : Int) (hmx_pos : 0 < mx)
    (hcanon : canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true)
    (hex_le : ex ≤ emax - prec) :
    bounded (prec:=prec) (emax:=emax) mx ex = true := by
  have heq :
      ex = FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex) :=
    eq_of_beq hcanon
  have heq_max :
      ex = max (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex - prec)
        (3 - emax - prec) := by
    simpa [FLT_exp, FloatSpec.Core.FLT.FLT_exp] using heq
  have hmax_le_ex :
      max (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex - prec)
        (3 - emax - prec) ≤ ex := by
    rw [← heq_max]
  have hdigits_le_prec : FloatSpec.Core.Digits.Zdigits 2 (mx : Int) ≤ prec := by
    have hleft :
        FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex - prec ≤ ex :=
      le_trans (le_max_left _ _) hmax_le_ex
    omega
  have hemin_le : 3 - emax - prec ≤ ex :=
    le_trans (le_max_right _ _) hmax_le_ex
  have hmx_ne : (mx : Int) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hmx_pos)
  have hdigits_pos : 0 < FloatSpec.Core.Digits.Zdigits 2 (mx : Int) := by
    have htrip := FloatSpec.Core.Digits.Zdigits_gt_0 (beta := 2) (n := (mx : Int))
      (by norm_num : (2 : Int) > 1)
    simpa [wp, PostCond.noThrow, pure] using htrip hmx_ne
  have hprec_nonneg : 0 ≤ prec := le_trans (le_of_lt hdigits_pos) hdigits_le_prec
  have hpow_bound :
      (mx : Int) < (2 : Int) ^ prec.toNat := by
    have htrip := FloatSpec.Core.Digits.Zpower_gt_Zdigits
      (beta := 2) (h_beta := by norm_num) (e := prec) (x := (mx : Int))
    simp only [wp, PostCond.noThrow, pure, Id.run] at htrip
    have hpow := htrip trivial hdigits_le_prec
    have hprec_abs : prec.natAbs = prec.toNat := by
      have h1 : (prec.natAbs : Int) = prec := Int.natAbs_of_nonneg hprec_nonneg
      have h2 : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprec_nonneg
      omega
    simpa [hprec_abs] using hpow
  have hmx_lt : mx < (2 : Nat) ^ prec.toNat := by
    have hcast : (2 : Int) ^ prec.toNat = ↑((2 : Nat) ^ prec.toNat) := by
      simp
    rw [hcast] at hpow_bound
    exact Nat.cast_lt.mp hpow_bound
  simp [bounded, hmx_lt, hemin_le, hex_le]

private theorem abs_SF2R_finite_eq_unsigned (sx : Bool) (mx : Nat) (ex : Int) :
    |SF2R 2 (StandardFloat.S754_finite sx mx ex)| =
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2) := by
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ ex := le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) ex)
  have hmx_nonneg : 0 ≤ ((mx : Int) : ℝ) := by exact_mod_cast (Nat.zero_le mx)
  cases sx <;>
    simp [SF2R, F2R, FloatSpec.Core.Defs.F2R, abs_mul, hpow_nonneg, hmx_nonneg,
      abs_of_nonneg hpow_nonneg, abs_of_nonneg hmx_nonneg]

-- Coq: binary_fit_aux_correct
theorem binary_fit_aux_correct
    (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int)
    (hmx_pos : 0 < mx)
    (hcanon : canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true) :
    let x := SF2R 2 (StandardFloat.S754_finite sx mx ex)
    let z := binary_fit_aux (prec:=prec) (emax:=emax) mode sx mx ex
    valid_binary_SF (prec:=prec) (emax:=emax) z = true ∧
      if FloatSpec.Core.Raux.Rlt_bool |x| (FloatSpec.Core.Raux.bpow 2 emax) then
        SF2R 2 z = x ∧ is_finite_SF z = true ∧ sign_SF z = sx
      else
        z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode sx := by
  dsimp
  by_cases hex_le : ex ≤ emax - prec
  · have hbounded :
        bounded (prec:=prec) (emax:=emax) mx ex = true :=
      binary_fit_aux_bounded_of_canonical_le (prec:=prec) (emax:=emax)
        mx ex hmx_pos hcanon hex_le
    have hlt_unsigned :
        F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
          FloatSpec.Core.Defs.FlocqFloat 2) < FloatSpec.Core.Raux.bpow 2 emax := by
      have htrip := bounded_lt_emax (prec:=prec) (emax:=emax) mx ex hbounded
      simpa [wp, PostCond.noThrow, pure, Id.run] using htrip trivial
    have hlt :
        |SF2R 2 (StandardFloat.S754_finite sx mx ex)| <
          FloatSpec.Core.Raux.bpow 2 emax := by
      simpa [abs_SF2R_finite_eq_unsigned] using hlt_unsigned
    have hlt_bool :
        FloatSpec.Core.Raux.Rlt_bool
          |SF2R 2 (StandardFloat.S754_finite sx mx ex)|
          (FloatSpec.Core.Raux.bpow 2 emax) = true := by
      simp [FloatSpec.Core.Raux.Rlt_bool, hlt]
    simp only [binary_fit_aux, hex_le, ↓reduceIte]
    constructor
    · rfl
    · rw [hlt_bool]
      simp [SF2R, is_finite_SF, sign_SF]
  · have hnot_lt :
        ¬ |SF2R 2 (StandardFloat.S754_finite sx mx ex)| <
          FloatSpec.Core.Raux.bpow 2 emax := by
      intro hlt
      have hcanon_prop :
          FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
            (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex) := by
        have htrip := canonical_canonical_mantissa_bsn (prec:=prec) (emax:=emax)
          false mx ex hmx_pos hcanon
        simpa [wp, PostCond.noThrow, pure, Id.run] using htrip trivial
      have hlt_unsigned :
          F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
            FloatSpec.Core.Defs.FlocqFloat 2) < FloatSpec.Core.Raux.bpow 2 emax := by
        simpa [abs_SF2R_finite_eq_unsigned] using hlt
      have hbounded_trip := bounded_canonical_lt_emax
        (prec:=prec) (emax:=emax)
        (inferInstance : Prec_gt_0 prec).pos
        (inferInstance : Prec_lt_emax prec emax).prec_lt_emax
        mx ex hmx_pos hcanon_prop hlt_unsigned
      have hbounded : bounded (prec:=prec) (emax:=emax) mx ex = true := by
        simpa [wp, PostCond.noThrow, pure, Id.run] using hbounded_trip trivial
      simp only [bounded, Bool.and_eq_true, decide_eq_true_eq] at hbounded
      exact hex_le hbounded.2
    have hlt_bool :
        FloatSpec.Core.Raux.Rlt_bool
          |SF2R 2 (StandardFloat.S754_finite sx mx ex)|
          (FloatSpec.Core.Raux.bpow 2 emax) = false := by
      simp [FloatSpec.Core.Raux.Rlt_bool, hnot_lt]
    simp only [binary_fit_aux, hex_le, ↓reduceIte]
    constructor
    · rfl
    · rw [hlt_bool]
      simp

-- Coq: `shr_fexp`, specialized to the SingleNaN `FLT_exp` exponent function.
-- The root `shr_fexp` name is already used by the Binary.v compatibility
-- layer, so this local helper keeps the BSN payload explicit.
noncomputable def bsn_shr_fexp (m e : Int) (l : Loc) : ShrRecord × Int :=
  let r := FloatSpec.Calc.Round.truncate_triple
    (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec) (m, e, l)
  let m' := r.1
  let e' := r.2.1
  let l' := r.2.2
  (shr_record_of_loc m' l', e')

private theorem bsn_shr_fexp_truncate_eq (m e : Int) (l : Loc) :
    bsn_shr_fexp (prec:=prec) (emax:=emax) m e l =
      let r := FloatSpec.Calc.Round.truncate_triple
        (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec) (m, e, l)
      let m' := r.1
      let e' := r.2.1
      let l' := r.2.2
      (shr_record_of_loc m' l', e') := by
  rfl

private theorem shr_record_of_loc_shr_m (m : Int) (l : Loc) :
    (shr_record_of_loc m l).shr_m = m := by
  cases l with
  | loc_Exact => rfl
  | loc_Inexact ord =>
      cases ord <;> rfl

private theorem bsn_shr_fexp_nonneg (m e : Int) (l : Loc) (hm : 0 ≤ m) :
    0 ≤ (bsn_shr_fexp (prec:=prec) (emax:=emax) m e l).1.shr_m := by
  unfold bsn_shr_fexp
  set r := FloatSpec.Calc.Round.truncate_triple
    (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec) (m, e, l)
  change 0 ≤ (shr_record_of_loc r.1 r.2.2).shr_m
  rw [shr_record_of_loc_shr_m]
  subst r
  unfold FloatSpec.Calc.Round.truncate_triple
  by_cases hk :
      e < FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 m + e)
  · have hpow_nonneg :
        0 ≤ (2 : Int) ^
          (FLT_exp (3 - emax - prec) prec
            (FloatSpec.Core.Digits.Zdigits 2 m + e) - e).natAbs :=
      pow_nonneg (by norm_num : (0 : Int) ≤ 2) _
    simp [hk, FloatSpec.Calc.Round.truncate_aux,
      Int.ediv_nonneg hm hpow_nonneg]
  · simp [hk, hm]

private theorem choice_mode_nonneg_of_nonneg
    (mode : RoundingMode) (sx : Bool) (mx : Int) (lx : Loc) (hmx : 0 ≤ mx) :
    0 ≤ choice_mode mode sx mx lx := by
  have hle := (le_choice_mode_le mode sx mx lx).1
  omega

-- Coq: `binary_round_aux`.
noncomputable def binary_round_aux (mode : RoundingMode) (sx : Bool)
    (mx ex : Int) (lx : Loc) : StandardFloat :=
  let first := bsn_shr_fexp (prec:=prec) (emax:=emax) mx ex lx
  let roundedMant := choice_mode mode sx first.1.shr_m (loc_of_shr_record first.1)
  let second := bsn_shr_fexp (prec:=prec) (emax:=emax) roundedMant first.2
    FloatSpec.Calc.Bracket.Location.loc_Exact
  if second.1.shr_m = 0 then
    StandardFloat.S754_zero sx
  else if 0 < second.1.shr_m then
    binary_fit_aux (prec:=prec) (emax:=emax) mode sx second.1.shr_m.toNat second.2
  else
    StandardFloat.S754_nan

-- Proof-carrying adapter for the raw `binary_round_aux` compatibility API.
-- Upstream `B754_finite` carries validity evidence in the constructor; the
-- current raw `StandardFloat` result needs that proof supplied explicitly until
-- the faithful `binary_round_aux_correct` payload is available.
noncomputable def binaryRoundAuxToBinarySingleNaNFloat
    (mode : RoundingMode) (sx : Bool) (mx ex : Int) (lx : Loc)
    (hvalid :
      validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
        (binary_round_aux (prec:=prec) (emax:=emax) mode sx mx ex lx) = true) :
    BinarySingleNaNFloat prec emax :=
  standardFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
    (binary_round_aux (prec:=prec) (emax:=emax) mode sx mx ex lx) hvalid

theorem binarySingleNaNFloatToStandardFloat_binaryRoundAuxToBinarySingleNaNFloat
    (mode : RoundingMode) (sx : Bool) (mx ex : Int) (lx : Loc)
    (hvalid :
      validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
        (binary_round_aux (prec:=prec) (emax:=emax) mode sx mx ex lx) = true) :
    binarySingleNaNFloatToStandardFloat (prec:=prec) (emax:=emax)
      (binaryRoundAuxToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
        mode sx mx ex lx hvalid) =
      binary_round_aux (prec:=prec) (emax:=emax) mode sx mx ex lx := by
  simpa [binaryRoundAuxToBinarySingleNaNFloat] using
    binarySingleNaNFloatToStandardFloat_standardFloatToBinarySingleNaNFloat
      (prec:=prec) (emax:=emax)
      (binary_round_aux (prec:=prec) (emax:=emax) mode sx mx ex lx) hvalid

theorem binarySingleNaNFloatToB754_binaryRoundAuxToBinarySingleNaNFloat
    (mode : RoundingMode) (sx : Bool) (mx ex : Int) (lx : Loc)
    (hvalid :
      validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
        (binary_round_aux (prec:=prec) (emax:=emax) mode sx mx ex lx) = true) :
    binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
      (binaryRoundAuxToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
        mode sx mx ex lx hvalid) =
      SF2B (binary_round_aux (prec:=prec) (emax:=emax) mode sx mx ex lx) := by
  simpa [binaryRoundAuxToBinarySingleNaNFloat] using
    binarySingleNaNFloatToB754_standardFloatToBinarySingleNaNFloat
      (prec:=prec) (emax:=emax)
      (binary_round_aux (prec:=prec) (emax:=emax) mode sx mx ex lx) hvalid

-- Coq: `binary_round`.
noncomputable def binary_round (mode : RoundingMode) (sx : Bool)
    (mx : Nat) (ex : Int) : StandardFloat :=
  let aligned := shl_align_fexp (prec:=prec) (emax:=emax) mx ex
  binary_round_aux (prec:=prec) (emax:=emax) mode sx (aligned.1 : Int)
    aligned.2 FloatSpec.Calc.Bracket.Location.loc_Exact

private theorem is_nan_SF_binary_fit_aux (mode : RoundingMode) (sx : Bool)
    (mx : Nat) (ex : Int) :
    is_nan_SF (binary_fit_aux (prec:=prec) (emax:=emax) mode sx mx ex) = false := by
  unfold binary_fit_aux bsn_binary_overflow
  by_cases hex : ex ≤ emax - prec
  · simp [hex, is_nan_SF]
  · simp [hex, is_nan_SF]
    cases h : overflow_to_inf mode sx <;> rfl

theorem is_nan_binary_round_aux_of_nonneg (mode : RoundingMode) (sx : Bool)
    (mx ex : Int) (lx : Loc) (hmx_nonneg : 0 ≤ mx) :
    is_nan_SF
      (binary_round_aux (prec:=prec) (emax:=emax) mode sx mx ex lx) = false := by
  unfold binary_round_aux
  let first := bsn_shr_fexp (prec:=prec) (emax:=emax) mx ex lx
  let roundedMant := choice_mode mode sx first.1.shr_m (loc_of_shr_record first.1)
  let second := bsn_shr_fexp (prec:=prec) (emax:=emax) roundedMant first.2
    FloatSpec.Calc.Bracket.Location.loc_Exact
  have hfirst_nonneg : 0 ≤ first.1.shr_m := by
    simpa [first] using
      bsn_shr_fexp_nonneg (prec:=prec) (emax:=emax) mx ex lx hmx_nonneg
  have hrounded_nonneg : 0 ≤ roundedMant :=
    choice_mode_nonneg_of_nonneg mode sx first.1.shr_m
      (loc_of_shr_record first.1) hfirst_nonneg
  have hsecond_nonneg : 0 ≤ second.1.shr_m := by
    simpa [second] using
      bsn_shr_fexp_nonneg (prec:=prec) (emax:=emax)
        roundedMant first.2 FloatSpec.Calc.Bracket.Location.loc_Exact hrounded_nonneg
  change is_nan_SF
      (if second.1.shr_m = 0 then
        StandardFloat.S754_zero sx
      else if 0 < second.1.shr_m then
        binary_fit_aux (prec:=prec) (emax:=emax) mode sx second.1.shr_m.toNat second.2
      else
        StandardFloat.S754_nan) = false
  by_cases hzero : second.1.shr_m = 0
  · simp [hzero, is_nan_SF]
  · have hpos : 0 < second.1.shr_m := by omega
    simp [hzero, hpos, is_nan_SF]
    exact is_nan_SF_binary_fit_aux (prec:=prec) (emax:=emax)
      mode sx second.1.shr_m.toNat second.2

-- Coq: `is_nan_binary_round`.
theorem is_nan_binary_round (mode : RoundingMode) (sx : Bool)
    (mx : Nat) (ex : Int) :
    is_nan_SF (binary_round (prec:=prec) (emax:=emax) mode sx mx ex) = false := by
  unfold binary_round binary_round_aux
  let aligned := shl_align_fexp (prec:=prec) (emax:=emax) mx ex
  let first := bsn_shr_fexp (prec:=prec) (emax:=emax) (aligned.1 : Int) aligned.2
    FloatSpec.Calc.Bracket.Location.loc_Exact
  let roundedMant := choice_mode mode sx first.1.shr_m (loc_of_shr_record first.1)
  let second := bsn_shr_fexp (prec:=prec) (emax:=emax) roundedMant first.2
    FloatSpec.Calc.Bracket.Location.loc_Exact
  have hfirst_nonneg : 0 ≤ first.1.shr_m := by
    have haligned_nonneg : 0 ≤ (aligned.1 : Int) := by exact_mod_cast Nat.zero_le aligned.1
    simpa [first] using
      bsn_shr_fexp_nonneg (prec:=prec) (emax:=emax)
        (aligned.1 : Int) aligned.2 FloatSpec.Calc.Bracket.Location.loc_Exact
        haligned_nonneg
  have hrounded_nonneg : 0 ≤ roundedMant :=
    choice_mode_nonneg_of_nonneg mode sx first.1.shr_m
      (loc_of_shr_record first.1) hfirst_nonneg
  have hsecond_nonneg : 0 ≤ second.1.shr_m := by
    simpa [second] using
      bsn_shr_fexp_nonneg (prec:=prec) (emax:=emax)
        roundedMant first.2 FloatSpec.Calc.Bracket.Location.loc_Exact hrounded_nonneg
  change is_nan_SF
      (if second.1.shr_m = 0 then
        StandardFloat.S754_zero sx
      else if 0 < second.1.shr_m then
        binary_fit_aux (prec:=prec) (emax:=emax) mode sx second.1.shr_m.toNat second.2
      else
        StandardFloat.S754_nan) = false
  by_cases hzero : second.1.shr_m = 0
  · simp [hzero, is_nan_SF]
  · have hpos : 0 < second.1.shr_m := by omega
    simp [hzero, hpos, is_nan_SF]
    exact is_nan_SF_binary_fit_aux (prec:=prec) (emax:=emax)
      mode sx second.1.shr_m.toNat second.2

private theorem BSN_is_nan_SF2B_eq (x : StandardFloat) :
    BSN_is_nan (SF2B x) = is_nan_SF x := by
  cases x <;> rfl

-- Coq: `binary_normalize`.
noncomputable def binary_normalize (mode : RoundingMode) (m e : Int) (szero : Bool) :
    B754 :=
  if m = 0 then
    B754.B754_zero szero
  else if 0 < m then
    SF2B (binary_round (prec:=prec) (emax:=emax) mode false m.toNat e)
  else
    SF2B (binary_round (prec:=prec) (emax:=emax) mode true m.natAbs e)

-- Coq: `is_nan_binary_normalize`.
theorem is_nan_binary_normalize (mode : RoundingMode) (m e : Int) (szero : Bool) :
    BSN_is_nan (binary_normalize (prec:=prec) (emax:=emax) mode m e szero) = false := by
  unfold binary_normalize
  by_cases hzero : m = 0
  · simp [hzero, BSN_is_nan]
  · by_cases hpos : 0 < m
    · have hround :=
        is_nan_binary_round (prec:=prec) (emax:=emax) mode false m.toNat e
      simp [hzero, hpos, BSN_is_nan_SF2B_eq, hround]
    · have hround :=
        is_nan_binary_round (prec:=prec) (emax:=emax) mode true m.natAbs e
      simp [hzero, hpos, BSN_is_nan_SF2B_eq, hround]

-- Coq: shl_align_correct'
--
-- The `shl_align` implementation is defined in `Binary.lean` and is shared by
-- the Binary and BinarySingleNaN ports.  This theorem mirrors the
-- BinarySingleNaN.v prerequisite used by `Fplus_naive_correct`: if the target
-- exponent is no larger than the source exponent, the shifted mantissa at the
-- target exponent has the same real value and the returned exponent is exactly
-- the target.
theorem shl_align_correct' (mx : Nat) (ex e : Int) (he : e ≤ ex) :
    let (mx', ex') := shl_align mx ex e
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx' : Int) e :
        FloatSpec.Core.Defs.FlocqFloat 2) =
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2) ∧
    ex' = e := by
  unfold shl_align
  simp only [he, ↓reduceIte]
  constructor
  · simp only [F2R, FloatSpec.Core.Defs.F2R,
      FloatSpec.Core.Defs.FlocqFloat.Fnum, FloatSpec.Core.Defs.FlocqFloat.Fexp]
    have hshift_nonneg : 0 ≤ ex - e := by omega
    have hshift : ((ex - e).toNat : Int) = ex - e :=
      Int.toNat_of_nonneg hshift_nonneg
    have h2ne : (2 : ℝ) ≠ 0 := by norm_num
    push_cast
    rw [mul_assoc]
    congr 1
    rw [← zpow_natCast (2 : ℝ) (ex - e).toNat]
    rw [hshift]
    rw [← zpow_add₀ h2ne (ex - e) e]
    congr 1
    ring
  · trivial

-- Coq: shl_align_correct
theorem shl_align_correct (mx : Nat) (ex ex' : Int) :
    let (mx', ex'') := shl_align mx ex ex'
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2) =
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx' : Int) ex'' :
        FloatSpec.Core.Defs.FlocqFloat 2) ∧
    ex'' ≤ ex' := by
  by_cases he : ex' ≤ ex
  · cases h : shl_align mx ex ex' with
    | mk mx' ex'' =>
        have hcorr := shl_align_correct' mx ex ex' he
        rw [h] at hcorr
        dsimp at hcorr
        constructor
        · rw [hcorr.2]
          exact hcorr.1.symm
        · rw [hcorr.2]
  · have hex : ex ≤ ex' := le_of_lt (lt_of_not_ge he)
    unfold shl_align
    simp [he, hex]

-- Coq: snd_shl_align
theorem snd_shl_align (mx : Nat) (ex ex' : Int) (he : ex' ≤ ex) :
    (shl_align mx ex ex').snd = ex' := by
  have hcorr := shl_align_correct' mx ex ex' he
  cases h : shl_align mx ex ex' with
  | mk mx' ex'' =>
      rw [h] at hcorr
      exact hcorr.2

-- Coq: Fplus_naive
def Fplus_naive (sx : Bool) (mx : Nat) (ex : Int)
    (sy : Bool) (my : Nat) (ey ez : Int) : Int :=
  FloatSpec.Core.Zaux.cond_Zopp sx ((shl_align mx ex ez).fst : Int) +
    FloatSpec.Core.Zaux.cond_Zopp sy ((shl_align my ey ez).fst : Int)

-- Coq: Fplus_naive_correct
theorem Fplus_naive_correct (sx : Bool) (mx : Nat) (ex : Int)
    (sy : Bool) (my : Nat) (ey ez : Int)
    (Ex : ez ≤ ex) (Ey : ez ≤ ey) :
    let x :=
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk
        (FloatSpec.Core.Zaux.cond_Zopp sx (mx : Int)) ex :
        FloatSpec.Core.Defs.FlocqFloat 2)
    let y :=
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk
        (FloatSpec.Core.Zaux.cond_Zopp sy (my : Int)) ey :
        FloatSpec.Core.Defs.FlocqFloat 2)
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk
        (Fplus_naive sx mx ex sy my ey ez) ez :
        FloatSpec.Core.Defs.FlocqFloat 2) = x + y := by
  cases hmx : shl_align mx ex ez with
  | mk mx' ex' =>
      cases hmy : shl_align my ey ez with
      | mk my' ey' =>
          have Hx := shl_align_correct' mx ex ez Ex
          have Hy := shl_align_correct' my ey ez Ey
          rw [hmx] at Hx
          rw [hmy] at Hy
          dsimp at Hx Hy
          have Hxs :
              F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                (FloatSpec.Core.Zaux.cond_Zopp sx (mx' : Int)) ez :
                FloatSpec.Core.Defs.FlocqFloat 2) =
              F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                (FloatSpec.Core.Zaux.cond_Zopp sx (mx : Int)) ex :
                FloatSpec.Core.Defs.FlocqFloat 2) := by
            cases sx
            · simpa [FloatSpec.Core.Zaux.cond_Zopp] using Hx.1
            · change
                F2R (FloatSpec.Core.Defs.FlocqFloat.mk (-(mx' : Int)) ez :
                  FloatSpec.Core.Defs.FlocqFloat 2) =
                F2R (FloatSpec.Core.Defs.FlocqFloat.mk (-(mx : Int)) ex :
                  FloatSpec.Core.Defs.FlocqFloat 2)
              simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
                FloatSpec.Core.Defs.FlocqFloat.Fexp, Int.cast_neg]
              simpa [neg_mul] using congrArg (fun r : ℝ => -r) Hx.1
          have Hys :
              F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                (FloatSpec.Core.Zaux.cond_Zopp sy (my' : Int)) ez :
                FloatSpec.Core.Defs.FlocqFloat 2) =
              F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                (FloatSpec.Core.Zaux.cond_Zopp sy (my : Int)) ey :
                FloatSpec.Core.Defs.FlocqFloat 2) := by
            cases sy
            · simpa [FloatSpec.Core.Zaux.cond_Zopp] using Hy.1
            · change
                F2R (FloatSpec.Core.Defs.FlocqFloat.mk (-(my' : Int)) ez :
                  FloatSpec.Core.Defs.FlocqFloat 2) =
                F2R (FloatSpec.Core.Defs.FlocqFloat.mk (-(my : Int)) ey :
                  FloatSpec.Core.Defs.FlocqFloat 2)
              simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
                FloatSpec.Core.Defs.FlocqFloat.Fexp, Int.cast_neg]
              simpa [neg_mul] using congrArg (fun r : ℝ => -r) Hy.1
          dsimp
          unfold Fplus_naive
          rw [hmx, hmy]
          calc
            F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                (FloatSpec.Core.Zaux.cond_Zopp sx (mx' : Int) +
                  FloatSpec.Core.Zaux.cond_Zopp sy (my' : Int)) ez :
                FloatSpec.Core.Defs.FlocqFloat 2)
                =
              F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                (FloatSpec.Core.Zaux.cond_Zopp sx (mx' : Int)) ez :
                FloatSpec.Core.Defs.FlocqFloat 2) +
              F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                (FloatSpec.Core.Zaux.cond_Zopp sy (my' : Int)) ez :
                FloatSpec.Core.Defs.FlocqFloat 2) := by
                  exact (FloatSpec.Core.Defs.F2R_add_same_exp'
                    (beta := 2)
                    (m1 := FloatSpec.Core.Zaux.cond_Zopp sx (mx' : Int))
                    (m2 := FloatSpec.Core.Zaux.cond_Zopp sy (my' : Int))
                    (e := ez)).symm
              _ =
                F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                  (FloatSpec.Core.Zaux.cond_Zopp sx (mx : Int)) ex :
                  FloatSpec.Core.Defs.FlocqFloat 2) +
                  F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                    (FloatSpec.Core.Zaux.cond_Zopp sy (my : Int)) ey :
                    FloatSpec.Core.Defs.FlocqFloat 2) := by
                      rw [Hxs, Hys]

  namespace ExperimentalSingleNaNArithmetic

/-!
Experimental SingleNaN arithmetic surface.

The operations in this namespace remain a lightweight Lean model of the
SingleNaN surface.  They now compute by rounding the real-valued operation into
the existing binary representation instead of returning a fixed operand.
-/

noncomputable def B754_round_real (mode : RoundingMode) (x : ℝ) : B754 :=
  let fexp := FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec)
  let rounded := FloatSpec.Core.Generic_fmt.round_to_generic 2 fexp (rnd_of_mode mode) x
  B2BSN (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) (real_to_FullFloat rounded fexp))

noncomputable def B754_round_real_signed_zero (mode : RoundingMode) (s : Bool) (x : ℝ) : B754 :=
  let fexp := FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec)
  match mode with
  | RoundingMode.RNE =>
      let rounded := FloatSpec.Core.Generic_fmt.round_to_generic 2 fexp (rnd_of_mode mode) |x|
      if rounded = 0 then
        B754.B754_zero s
      else
        let exp := FloatSpec.Core.Generic_fmt.cexp 2 fexp rounded
        let mantissa := FloatSpec.Core.Raux.Ztrunc (rounded * (2 : ℝ) ^ (-exp))
        B754.B754_finite s mantissa.natAbs exp
  | _ =>
      let rounded := FloatSpec.Core.Generic_fmt.round_to_generic 2 fexp (rnd_of_mode mode) x
      if rounded = 0 then
        B754.B754_zero s
      else
        let exp := FloatSpec.Core.Generic_fmt.cexp 2 fexp rounded
        let mantissa := FloatSpec.Core.Raux.Ztrunc (rounded * (2 : ℝ) ^ (-exp))
        let sign := mantissa < 0
        B754.B754_finite (decide sign) mantissa.natAbs exp

private theorem BSN_is_nan_B754_round_real_signed_zero
    (mode : RoundingMode) (s : Bool) (x : ℝ) :
    BSN_is_nan (B754_round_real_signed_zero (prec:=prec) (emax:=emax) mode s x) = false := by
  unfold B754_round_real_signed_zero
  cases mode
  · by_cases h :
        FloatSpec.Core.Generic_fmt.round_to_generic 2
          (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))
          (rnd_of_mode RoundingMode.RNE) |x| = 0
    · simp [h, BSN_is_nan]
    · simp [h, BSN_is_nan]
  · by_cases h :
        FloatSpec.Core.Generic_fmt.round_to_generic 2
          (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))
          (rnd_of_mode RoundingMode.RNA) x = 0
    · simp [h, BSN_is_nan]
    · simp [h, BSN_is_nan]
  · by_cases h :
        FloatSpec.Core.Generic_fmt.round_to_generic 2
          (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))
          (rnd_of_mode RoundingMode.RTP) x = 0
    · simp [h, BSN_is_nan]
    · simp [h, BSN_is_nan]
  · by_cases h :
        FloatSpec.Core.Generic_fmt.round_to_generic 2
          (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))
          (rnd_of_mode RoundingMode.RTN) x = 0
    · simp [h, BSN_is_nan]
    · simp [h, BSN_is_nan]
  · by_cases h :
        FloatSpec.Core.Generic_fmt.round_to_generic 2
          (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))
          (rnd_of_mode RoundingMode.RTZ) x = 0
    · simp [h, BSN_is_nan]
    · simp [h, BSN_is_nan]

private theorem abs_F2R_neg_mantissa_eq (m : Nat) (e : Int) :
    |F2R ({ Fnum := -(m : Int), Fexp := e } : FloatSpec.Core.Defs.FlocqFloat 2)|
      = |F2R ({ Fnum := (m : Int), Fexp := e } : FloatSpec.Core.Defs.FlocqFloat 2)| := by
  unfold F2R FloatSpec.Core.Defs.F2R
  simp [abs_mul]

def B754_has_nan (x y : B754) : Bool :=
  match x, y with
  | B754.B754_nan, _ => true
  | _, B754.B754_nan => true
  | _, _ => false

-- Operations preserving single NaN
noncomputable def B754_plus (mode : RoundingMode) (x y : B754) : B754 :=
  if B754_has_nan x y then
    B754.B754_nan
  else
    B754_round_real (prec:=prec) (emax:=emax) mode (B754_to_R x + B754_to_R y)

noncomputable def B754_mult (mode : RoundingMode) (x y : B754) : B754 :=
  if B754_has_nan x y then
    B754.B754_nan
  else
    B754_round_real (prec:=prec) (emax:=emax) mode (B754_to_R x * B754_to_R y)

noncomputable def B754_div (mode : RoundingMode) (x y : B754) : B754 :=
  if B754_has_nan x y then
    B754.B754_nan
  else
    B754_round_real (prec:=prec) (emax:=emax) mode (B754_to_R x / B754_to_R y)

noncomputable def B754_sqrt (mode : RoundingMode) (x : B754) : B754 :=
  match x with
  | B754.B754_nan => B754.B754_nan
  | _ => B754_round_real (prec:=prec) (emax:=emax) mode (Real.sqrt (B754_to_R x))

-- Classification functions
def B754_is_finite (x : B754) : Bool :=
  match x with
  | B754.B754_finite _ _ _ => true
  | B754.B754_zero _ => true
  | _ => false

def B754_is_nan (x : B754) : Bool :=
  match x with
  | B754.B754_nan => true
  | _ => false

def B754_sign (x : B754) : Bool :=
  match x with
  | B754.B754_zero s => s
  | B754.B754_infinity s => s
  | B754.B754_finite s _ _ => s
  | B754.B754_nan => false

/-- Predicate capturing when a B754 float is in generic format.
    For finite floats, this requires the canonical exponent to be at most the float's exponent.
    This is the key constraint that Coq's `bounded mx ex = true` proof provides.
-/
noncomputable def B754_in_generic_format (x : B754) : Prop :=
  match x with
  | B754.B754_zero _ => True
  | B754.B754_infinity _ => True
  | B754.B754_nan => True
  | B754.B754_finite s m e =>
    let fnum : Int := if s then -(m : Int) else (m : Int)
    let f : FloatSpec.Core.Defs.FlocqFloat 2 := FloatSpec.Core.Defs.FlocqFloat.mk fnum e
    fnum ≠ 0 → FloatSpec.Core.Generic_fmt.cexp 2 (FLT_exp (3 - emax - prec) prec) (F2R f) ≤ e

-- Exponent scaling (Coq: Bldexp) at the SingleNaN level.
noncomputable def Bldexp (mode : RoundingMode) (x : B754) (e : Int) : B754 :=
  match x with
  | B754.B754_finite s m ex =>
      SF2B (binary_round (prec:=prec) (emax:=emax) mode s m (ex + e))
  | _ => x

noncomputable def is_nan_Bldexp_check (mode : RoundingMode) (x : B754) (e : Int) : Bool :=
  (BSN_is_nan (Bldexp (prec:=prec) (emax:=emax) mode x e))

-- Coq: is_nan_Bldexp — exponent scaling preserves NaN-ness
theorem is_nan_Bldexp (mode : RoundingMode) (x : B754) (e : Int) :
  ⦃⌜True⌝⦄
  (pure (is_nan_Bldexp_check (prec:=prec) (emax:=emax) mode x e) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => rfl
  | B754_finite s m e₀ =>
      change BSN_is_nan
          (SF2B (binary_round (prec:=prec) (emax:=emax) mode s m (e₀ + e))) = false
      rw [BSN_is_nan_SF2B_eq]
      exact is_nan_binary_round (prec:=prec) (emax:=emax) mode s m (e₀ + e)

-- Negation on SingleNaN binary floats (Coq: Bopp on B754)
def Bopp_bsn (x : B754) : B754 :=
  match x with
  | B754.B754_nan => B754.B754_nan
  | B754.B754_zero s => B754.B754_zero (!s)
  | B754.B754_infinity s => B754.B754_infinity (!s)
  | B754.B754_finite s m e => B754.B754_finite (!s) m e

def is_nan_Bopp_check (x : B754) : Bool :=
  BSN_is_nan (Bopp_bsn x)

-- Coq: is_nan_Bopp
theorem is_nan_Bopp (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_nan_Bopp_check x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_nan_Bopp_check Bopp_bsn BSN_is_nan
  cases x <;> rfl

def is_finite_strict_Bopp_check (x : B754) : Bool :=
  BSN_is_finite_strict (Bopp_bsn x)

-- Coq: is_finite_strict_Bopp
theorem is_finite_strict_Bopp (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_finite_strict_Bopp_check x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_finite_strict x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_strict_Bopp_check Bopp_bsn BSN_is_finite_strict
  cases x <;> rfl

-- Absolute value on SingleNaN binary floats (Coq: Babs on B754)
def Babs_bsn (x : B754) : B754 :=
  match x with
  | B754.B754_nan => B754.B754_nan
  | B754.B754_zero _ => B754.B754_zero false
  | B754.B754_infinity _ => B754.B754_infinity false
  | B754.B754_finite _ m e => B754.B754_finite false m e

def is_nan_Babs_check (x : B754) : Bool :=
  BSN_is_nan (Babs_bsn x)

-- Coq: is_nan_Babs
theorem is_nan_Babs (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_nan_Babs_check x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_nan_Babs_check Babs_bsn BSN_is_nan
  cases x <;> rfl

def is_finite_strict_Babs_check (x : B754) : Bool :=
  BSN_is_finite_strict (Babs_bsn x)

-- Coq: is_finite_strict_Babs
theorem is_finite_strict_Babs (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_finite_strict_Babs_check x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_finite_strict x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold is_finite_strict_Babs_check Babs_bsn BSN_is_finite_strict
  cases x <;> rfl

-- Hoare wrapper for `Bldexp_Bopp_NE`
noncomputable def Bldexp_Bopp_NE_check (x : B754) (e : Int) : B754 :=
  (Bldexp (prec:=prec) (emax:=emax) RoundingMode.RNE (Bopp_bsn x) e)

-- Coq: Bldexp_Bopp_NE
theorem Bldexp_Bopp_NE (x : B754) (e : Int) :
  ⦃⌜True⌝⦄
  (pure (Bldexp_Bopp_NE_check (prec:=prec) (emax:=emax) x e) : Id B754)
  ⦃⇓result => ⌜result = Bopp_bsn (Bldexp (prec:=prec) (emax:=emax) RoundingMode.RNE x e)⌝⦄ := by
  intro _
  change Bldexp_Bopp_NE_check (prec:=prec) (emax:=emax) x e =
    Bopp_bsn (Bldexp (prec:=prec) (emax:=emax) RoundingMode.RNE x e)
  cases x with
  | B754_zero s =>
      simp [Bldexp_Bopp_NE_check, Bldexp, Bopp_bsn]
  | B754_infinity s =>
      simp [Bldexp_Bopp_NE_check, Bldexp, Bopp_bsn]
  | B754_nan =>
      simp [Bldexp_Bopp_NE_check, Bldexp, Bopp_bsn]
  | B754_finite s m e₀ =>
      let aligned := shl_align_fexp (prec:=prec) (emax:=emax) m (e₀ + e)
      let first := bsn_shr_fexp (prec:=prec) (emax:=emax)
        (aligned.1 : Int) aligned.2 FloatSpec.Calc.Bracket.Location.loc_Exact
      let roundedMant := choice_mode RoundingMode.RNE false first.1.shr_m
        (loc_of_shr_record first.1)
      let second := bsn_shr_fexp (prec:=prec) (emax:=emax)
        roundedMant first.2 FloatSpec.Calc.Bracket.Location.loc_Exact
      have hfirst_nonneg : 0 ≤ first.1.shr_m := by
        apply bsn_shr_fexp_nonneg
        exact_mod_cast Nat.zero_le aligned.1
      have hrounded_nonneg : 0 ≤ roundedMant :=
        choice_mode_nonneg_of_nonneg RoundingMode.RNE false first.1.shr_m
          (loc_of_shr_record first.1) hfirst_nonneg
      have hsecond_nonneg : 0 ≤ second.1.shr_m := by
        exact bsn_shr_fexp_nonneg (prec:=prec) (emax:=emax) roundedMant first.2
          FloatSpec.Calc.Bracket.Location.loc_Exact hrounded_nonneg
      cases s <;>
        simp only [Bldexp_Bopp_NE_check, Bldexp, Bopp_bsn, Bool.not_false,
          Bool.not_true]
      all_goals
        simp only [binary_round, binary_round_aux, choice_mode]
        unfold binary_fit_aux bsn_binary_overflow overflow_to_inf SF2B
        by_cases hzero : second.1.shr_m = 0
        · simp_all [Bopp_bsn, choice_mode, aligned, first, roundedMant, second]
        · have hpos : 0 < second.1.shr_m := by omega
          simp_all [Bopp_bsn, choice_mode, aligned, first, roundedMant, second]
          split_ifs <;> rfl

-- Coq: Ffrexp_core_binary
def Ffrexp_core_binary (sx : Bool) (mx : Nat) (ex : Int) :
    StandardFloat × Int :=
  if FloatSpec.Core.Zaux.Zlt_bool (-prec) (3 - emax - prec) then
    (StandardFloat.S754_finite sx mx ex, 0)
  else if prec ≤ FloatSpec.Core.Digits.digits2_pos mx then
    (StandardFloat.S754_finite sx mx (-prec), ex + prec)
  else
    let d := prec - FloatSpec.Core.Digits.digits2_pos mx
    (StandardFloat.S754_finite sx (mx * 2 ^ d.toNat) (-prec), ex + prec - d)

-- Decomposition (Coq: Bfrexp on SingleNaN side)
def Bfrexp_bsn (x : B754) : B754 × Int :=
  match x with
  | B754.B754_finite s m e =>
      let result := Ffrexp_core_binary (prec:=prec) (emax:=emax) s m e
      (SF2B result.1, result.2)
  | _ => (x, -2 * emax - prec)

def is_nan_Bfrexp_check (x : B754) : Bool :=
  BSN_is_nan ((Bfrexp_bsn (prec:=prec) (emax:=emax) x).1)

-- Coq: is_nan_Bfrexp — NaN-ness preserved for the significand of Bfrexp
theorem is_nan_Bfrexp (x : B754) :
  ⦃⌜True⌝⦄
  (pure (is_nan_Bfrexp_check (prec:=prec) (emax:=emax) x) : Id Bool)
  ⦃⇓result => ⌜result = BSN_is_nan x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  cases x <;>
    simp [is_nan_Bfrexp_check, Bfrexp_bsn, Ffrexp_core_binary, BSN_is_nan] <;>
    split_ifs <;> rfl

-- Boolean xor used to combine signs (Coq: xorb)
def bxor (a b : Bool) : Bool :=
  (a && !b) || (!a && b)

-- Legacy payload adapter retained for downstream compatibility.  It is not
-- FLoCq's `Bfrexp_correct_aux`: the caller supplies the normalization fact.
noncomputable def Bfrexp_correct_aux_check_from_normalization_payload
  (sx : Bool) (mx : Nat) (ex : Int)
  (Hx : bounded (prec:=prec) (emax:=emax) mx ex = true) : (StandardFloat × Int) :=
  (StandardFloat.S754_finite sx mx ex, 0)

theorem Bfrexp_correct_aux_from_normalization_payload
  (sx : Bool) (mx : Nat) (ex : Int)
  (Hx : bounded (prec:=prec) (emax:=emax) mx ex = true)
  (hnorm : (2 : Int) < emax → ((1 : ℝ) / 2 ≤ |SF2R 2 (StandardFloat.S754_finite sx mx ex)| ∧
                               |SF2R 2 (StandardFloat.S754_finite sx mx ex)| < 1)) :
  ⦃⌜True⌝⦄
  (pure (Bfrexp_correct_aux_check_from_normalization_payload
    (prec:=prec) (emax:=emax) sx mx ex Hx) : Id (StandardFloat × Int))
  ⦃⇓res => ⌜
      let z := res.1; let e := res.2;
      valid_binary_SF (prec:=prec) (emax:=emax) z = true ∧
      ((2 : Int) < emax → ((1 : ℝ) / 2 ≤ |SF2R 2 z| ∧ |SF2R 2 z| < 1)) ∧
      SF2R 2 (StandardFloat.S754_finite sx mx ex)
        = SF2R 2 z * FloatSpec.Core.Raux.bpow 2 e⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold Bfrexp_correct_aux_check_from_normalization_payload
  constructor
  · rfl
  constructor
  · simp only [Id.run]
    exact hnorm
  · simp only [Id.run, FloatSpec.Core.Raux.bpow, zpow_zero, mul_one]

-- Coq: Bmax_float
def Bmax_float : B754 :=
  B754.B754_finite false ((2 : Nat) ^ prec.toNat - 1) (emax - prec)

-- Coq: Bmax_float_proof
--
-- The local `valid_binary_SF` surface is currently permissive, so the faithful
-- payload is stated over the nontrivial finite validity pieces: boundedness and
-- canonical mantissa for the maximal finite mantissa/exponent pair.
theorem Bmax_float_proof :
    bounded (prec:=prec) (emax:=emax) ((2 : Nat) ^ prec.toNat - 1) (emax - prec) = true ∧
    canonical_mantissa (prec:=prec) (emax:=emax)
      ((2 : Nat) ^ prec.toNat - 1) (emax - prec) = true := by
  have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
  have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
  have hprec_toNat : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprec_nonneg
  have hprec_toNat_ne : prec.toNat ≠ 0 := by
    intro hzero
    have : (prec.toNat : Int) = 0 := by simp [hzero]
    omega
  have hprec_natAbs : prec.natAbs = prec.toNat := by
    apply Nat.cast_injective (R := Int)
    rw [Int.natAbs_of_nonneg hprec_nonneg, hprec_toNat]
  have hpow_pos : 0 < (2 : Nat) ^ prec.toNat :=
    Nat.pow_pos (by decide : 0 < (2 : Nat))
  have hm_pos : 0 < (2 : Nat) ^ prec.toNat - 1 := by
    exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow hprec_toNat_ne)
  have hm_lt_pow : (2 : Nat) ^ prec.toNat - 1 < (2 : Nat) ^ prec.toNat :=
    Nat.sub_one_lt hpow_pos.ne'
  have hemax_ge_two := (inferInstance : Prec_lt_emax prec emax).emax_ge_2
  have hbound :
      bounded (prec:=prec) (emax:=emax) ((2 : Nat) ^ prec.toNat - 1) (emax - prec) = true := by
    unfold bounded
    rw [Bool.and_eq_true, Bool.and_eq_true]
    repeat rw [decide_eq_true_eq]
    constructor
    · constructor
      · exact hm_lt_pow
      · omega
    · rfl
  constructor
  · exact hbound
  · unfold canonical_mantissa
    apply beq_iff_eq.mpr
    have hm_int_pos : (0 : Int) < (((2 : Nat) ^ prec.toNat - 1 : Nat) : Int) :=
      by exact_mod_cast hm_pos
    have hm_nonzero : (((2 : Nat) ^ prec.toNat - 1 : Nat) : Int) ≠ 0 :=
      ne_of_gt hm_int_pos
    have hpow_int : (((2 : Nat) ^ prec.toNat : Nat) : Int) = (2 : Int) ^ prec.toNat := by
      norm_num
    have hm_upper :
        Int.natAbs ((((2 : Nat) ^ prec.toNat - 1 : Nat) : Int)) < (2 : Int) ^ prec.toNat := by
      rw [Int.natAbs_of_nonneg (le_of_lt hm_int_pos)]
      rw [hpow_int.symm]
      exact_mod_cast hm_lt_pow
    have hprec_pred_nonneg : 0 ≤ prec - 1 := by omega
    have hprec_pred_natAbs : (prec - 1).natAbs = prec.toNat - 1 := by
      apply Nat.cast_injective (R := Int)
      rw [Int.natAbs_of_nonneg hprec_pred_nonneg]
      have htoNat_sub : (((prec.toNat - 1 : Nat) : Int) = prec - 1) := by
        have hprec_toNat_pos : 0 < prec.toNat := by
          exact Nat.pos_iff_ne_zero.mpr hprec_toNat_ne
        omega
      exact htoNat_sub.symm
    have hm_lower :
        (2 : Int) ^ (prec - 1).natAbs ≤
          Int.natAbs ((((2 : Nat) ^ prec.toNat - 1 : Nat) : Int)) := by
      rw [Int.natAbs_of_nonneg (le_of_lt hm_int_pos), hprec_pred_natAbs]
      have hprec_toNat_pos : 0 < prec.toNat :=
        Nat.pos_iff_ne_zero.mpr hprec_toNat_ne
      have hpow_pred_le :
          (2 : Nat) ^ (prec.toNat - 1) ≤ (2 : Nat) ^ prec.toNat - 1 := by
        cases hprec_toNat_cases : prec.toNat with
        | zero => omega
        | succ k =>
            cases k with
            | zero =>
                simp [hprec_toNat_cases]
            | succ k =>
                have hpow_pos_nat : 0 < (2 : Nat) ^ (Nat.succ k) :=
                  Nat.pow_pos (by decide : 0 < (2 : Nat))
                calc
                  (2 : Nat) ^ (Nat.succ k) ≤
                      (2 : Nat) ^ (Nat.succ k) + ((2 : Nat) ^ (Nat.succ k) - 1) := by
                        exact Nat.le_add_right _ _
                  _ = (2 : Nat) ^ (Nat.succ (Nat.succ k)) - 1 := by
                        rw [pow_succ]
                        omega
      exact_mod_cast hpow_pred_le
    have hdigits :=
      (FloatSpec.Core.Digits.Zdigits_unique_from_nonzero_payload (beta := 2) (h_beta := by norm_num)
        (n := (((2 : Nat) ^ prec.toNat - 1 : Nat) : Int)) (e := prec) (hβ := by norm_num))
        ⟨hm_nonzero, by simpa using hm_lower, by simpa [hprec_natAbs] using hm_upper⟩
    have hdigits_eq :
        FloatSpec.Core.Digits.Zdigits 2 (((2 : Nat) ^ prec.toNat - 1 : Nat) : Int) = prec := by
      simpa [wp, PostCond.noThrow, pure] using hdigits
    have hflt :
        FLT_exp (3 - emax - prec) prec
          (FloatSpec.Core.Digits.Zdigits 2 (((2 : Nat) ^ prec.toNat - 1 : Nat) : Int)
            + (emax - prec)) = emax - prec := by
      rw [hdigits_eq]
      unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
      have hmax_eq :
          max (prec + (emax - prec) - prec) (3 - emax - prec) = emax - prec := by
        have hleft : prec + (emax - prec) - prec = emax - prec := by omega
        rw [hleft]
        apply max_eq_left
        omega
      simpa using hmax_eq
    simpa using hflt.symm

private theorem validBinarySingleNaNStandardFloat_bsn_binary_overflow
    (mode : RoundingMode) (sx : Bool) :
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
      (bsn_binary_overflow (prec:=prec) (emax:=emax) mode sx) = true := by
  have hmax_proof := Bmax_float_proof (prec:=prec) (emax:=emax)
  have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
  have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
  have hprec_toNat_ne : prec.toNat ≠ 0 := by
    intro hzero
    have htoNat : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprec_nonneg
    rw [hzero] at htoNat
    omega
  have hm_pos : 0 < (2 : Nat) ^ prec.toNat - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_two_pow hprec_toNat_ne)
  have hmax_spec :
      specFloat_bounded (prec:=prec) (emax:=emax)
        ((2 : Nat) ^ prec.toNat - 1) (emax - prec) = true := by
    simp [specFloat_bounded, hmax_proof.2]
  cases mode <;> cases sx <;>
    simp [bsn_binary_overflow, overflow_to_inf, validBinarySingleNaNStandardFloat,
      hm_pos, hmax_spec]

private theorem validBinarySingleNaNStandardFloat_binary_fit_aux
    (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int)
    (hmx_pos : 0 < mx)
    (hcanon : canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true) :
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
      (binary_fit_aux (prec:=prec) (emax:=emax) mode sx mx ex) = true := by
  by_cases hex_le : ex ≤ emax - prec
  · have hspec :
        specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true := by
      simp [specFloat_bounded, hcanon, hex_le]
    simp [binary_fit_aux, hex_le, validBinarySingleNaNStandardFloat, hmx_pos, hspec]
  · simpa [binary_fit_aux, hex_le] using
      validBinarySingleNaNStandardFloat_bsn_binary_overflow
        (prec:=prec) (emax:=emax) mode sx

private theorem binary_round_aux_correct_proof
    [FloatSpec.Core.Generic_fmt.Monotone_exp
      (FLT_exp (3 - emax - prec) prec)]
    (mode : RoundingMode) (x : ℝ) (mx ex : Int) (lx : Loc)
    (hx_ne : x ≠ 0)
    (Bx : FloatSpec.Calc.Bracket.inbetween_float 2 mx ex |x| lx)
    (Ex : ex ≤
      FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Digits.Zdigits 2 mx + ex)) :
    let z := binary_round_aux (prec:=prec) (emax:=emax) mode
      (FloatSpec.Core.Raux.Rlt_bool x 0) mx ex lx
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      if FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        SF2R 2 z =
            FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x ∧
          is_finite_SF z = true ∧
          sign_SF z = FloatSpec.Core.Raux.Rlt_bool x 0
      else
        z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool x 0) := by
  classical
  let fexp := FLT_exp (3 - emax - prec) prec
  let sx := FloatSpec.Core.Raux.Rlt_bool x 0
  let rounded := FloatSpec.Core.Generic_fmt.roundR 2 fexp (rnd_of_mode mode) x
  let r1 := FloatSpec.Calc.Round.truncate_triple
    (beta := 2) (fexp := fexp) (mx, ex, lx)
  let m1 := r1.1
  let e1 := r1.2.1
  let l1 := r1.2.2
  let m1' := choice_mode mode sx m1 l1
  have hx_abs_pos : 0 < |x| := abs_pos.mpr hx_ne
  have hround_repr :
      rounded =
        F2R (FloatSpec.Core.Defs.FlocqFloat.mk
          (FloatSpec.Core.Zaux.cond_Zopp sx m1') e1 :
          FloatSpec.Core.Defs.FlocqFloat 2) := by
    have h :=
      FloatSpec.Calc.Round.round_trunc_sign_any_correct
        (beta := 2) (fexp := fexp)
        (rnd := rnd_of_mode mode)
        (choice := fun s m l => choice_mode mode s m l)
        (Hc := by
          intro y m l Hy
          exact round_mode_choice_mode (mode := mode) (x := y) (m := m) (l := l) Hy)
        (x := x) (m := mx) (e := ex) (l := lx)
        (Hx := Bx) (Heq := Or.inl Ex)
        (Hβ := (by norm_num : (1 : Int) < 2))
    simpa (config := {zeta := true}) [rounded, fexp, sx, r1, m1, e1, l1, m1'] using h
  have htr1 :
      FloatSpec.Calc.Bracket.inbetween_float 2 m1 e1 |x| l1 ∧
        e1 = FloatSpec.Core.Generic_fmt.cexp 2 fexp |x| := by
    have h :=
      FloatSpec.Calc.Round.Audit.truncate_correct_partial
        (beta := 2) (fexp := fexp)
        (x := |x|) (m := mx) (e := ex) (l := lx)
        (by norm_num : (1 : Int) < 2) hx_abs_pos Bx Ex
    simpa [fexp, r1, m1, e1, l1] using h
  have hm1_le_m1' : m1 ≤ m1' := (le_choice_mode_le mode sx m1 l1).1
  have hfirst_nonneg : 0 ≤ m1 := by
    have hbounds :=
      FloatSpec.Calc.Bracket.inbetween_float_bounds
        (beta := 2) (x := |x|) (m := m1) (e := e1) (l := l1)
        htr1.1 (by norm_num : (1 : Int) < 2)
    have hupper_pos :
        0 < F2R (FloatSpec.Core.Defs.FlocqFloat.mk (m1 + 1) e1 :
          FloatSpec.Core.Defs.FlocqFloat 2) := lt_of_le_of_lt (abs_nonneg x) hbounds.2
    have hm1_add_pos :=
      FloatSpec.Core.Float_prop.gt_0_F2R
        (beta := 2)
        (f := FloatSpec.Core.Defs.FlocqFloat.mk (m1 + 1) e1)
        (by norm_num : (1 : Int) < 2) hupper_pos
    have hm1_add_pos_int : 0 < m1 + 1 := by
      simpa using hm1_add_pos
    omega
  have hm1'_nonneg : 0 ≤ m1' := le_trans hfirst_nonneg hm1_le_m1'
  have hrounded_abs :
      |rounded| =
        F2R (FloatSpec.Core.Defs.FlocqFloat.mk m1' e1 :
          FloatSpec.Core.Defs.FlocqFloat 2) := by
    have hcond_abs :
        |F2R (FloatSpec.Core.Defs.FlocqFloat.mk
          (FloatSpec.Core.Zaux.cond_Zopp sx m1') e1 :
          FloatSpec.Core.Defs.FlocqFloat 2)| =
          F2R (FloatSpec.Core.Defs.FlocqFloat.mk m1' e1 :
            FloatSpec.Core.Defs.FlocqFloat 2) := by
      have hm1'_real_nonneg : (0 : ℝ) ≤ (m1' : ℝ) := by exact_mod_cast hm1'_nonneg
      have hp_nonneg : 0 ≤ (2 : ℝ) ^ e1 :=
        le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e1)
      cases sx <;>
        simp [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Zaux.cond_Zopp,
          abs_mul, abs_of_nonneg hp_nonneg, abs_of_nonneg hm1'_real_nonneg]
    rw [hround_repr, hcond_abs]
  dsimp
  by_cases hm1'_zero : m1' = 0
  · have hrounded_zero : rounded = 0 := by
      have habs : |rounded| = 0 := by
        simpa [hm1'_zero, F2R, FloatSpec.Core.Defs.F2R] using hrounded_abs
      exact abs_eq_zero.mp habs
    have hsecond_zero :
        (bsn_shr_fexp (prec:=prec) (emax:=emax) 0 e1
          FloatSpec.Calc.Bracket.Location.loc_Exact).1.shr_m = 0 := by
      unfold bsn_shr_fexp
      set r := FloatSpec.Calc.Round.truncate_triple
        (beta := 2) (fexp := fexp) (0, e1,
          FloatSpec.Calc.Bracket.Location.loc_Exact)
      change (shr_record_of_loc r.1 r.2.2).shr_m = 0
      rw [shr_m_shr_record_of_loc]
      have h0 := FloatSpec.Calc.Round.Audit.truncate_0
        (beta := 2) (fexp := fexp) e1
        FloatSpec.Calc.Bracket.Location.loc_Exact
      simpa [r] using h0
    have hsecond_zero_raw :
        (FloatSpec.Calc.Round.truncate_triple
          (beta := 2) (fexp := fexp)
          (0, e1, FloatSpec.Calc.Bracket.Location.loc_Exact)).1 = 0 := by
      have h0 := FloatSpec.Calc.Round.Audit.truncate_0
        (beta := 2) (fexp := fexp) e1
        FloatSpec.Calc.Bracket.Location.loc_Exact
      simpa using h0
    have hlt :
        FloatSpec.Core.Raux.Rlt_bool |rounded|
          (FloatSpec.Core.Raux.bpow 2 emax) = true := by
      have hbpow_trip := FloatSpec.Core.Raux.bpow_gt_0 2 emax
        (by norm_num : (1 : Int) < 2)
      have hbpow_pos : 0 < FloatSpec.Core.Raux.bpow 2 emax := by
        simpa [wp, PostCond.noThrow, pure] using hbpow_trip trivial
      simp [FloatSpec.Core.Raux.Rlt_bool, hrounded_zero, hbpow_pos]
    constructor
    · simp [binary_round_aux, bsn_shr_fexp, fexp, sx, r1, m1, e1, l1, m1',
        hm1'_zero, hsecond_zero, hsecond_zero_raw, loc_of_shr_record_of_loc,
        shr_m_shr_record_of_loc, validBinarySingleNaNStandardFloat]
    · rw [hlt]
      simp [binary_round_aux, bsn_shr_fexp, fexp, sx, r1, m1, e1, l1, m1',
        hm1'_zero, hsecond_zero, hsecond_zero_raw, hrounded_zero, loc_of_shr_record_of_loc,
        shr_m_shr_record_of_loc, SF2R, is_finite_SF, sign_SF]
      simpa [rounded, fexp] using hrounded_zero.symm
  · have hm1'_pos : 0 < m1' := lt_of_le_of_ne hm1'_nonneg (Ne.symm hm1'_zero)
    let r2 := FloatSpec.Calc.Round.truncate_triple
      (beta := 2) (fexp := fexp) (m1', e1,
        FloatSpec.Calc.Bracket.Location.loc_Exact)
    let m2 := r2.1
    let e2 := r2.2.1
    let l2 := r2.2.2
    have hrounded_abs_pos :
        0 < |rounded| := by
      have hm1'_f_pos :
          0 < F2R (FloatSpec.Core.Defs.FlocqFloat.mk m1' e1 :
            FloatSpec.Core.Defs.FlocqFloat 2) :=
        FloatSpec.Core.Float_prop.F2R_gt_0
          (beta := 2)
          (f := FloatSpec.Core.Defs.FlocqFloat.mk m1' e1)
          (by norm_num : (1 : Int) < 2) hm1'_pos
      simpa [hrounded_abs] using hm1'_f_pos
    have hrounded_ne : rounded ≠ 0 := by
      exact abs_pos.mp hrounded_abs_pos
    have hcexp_abs_x :
        FloatSpec.Core.Generic_fmt.cexp 2 fexp |x| =
          FloatSpec.Core.Generic_fmt.cexp 2 fexp x := by
      have h := FloatSpec.Core.Generic_fmt.cexp_abs
        (beta := 2) (fexp := fexp) (x := x)
      simpa [wp, PostCond.noThrow, pure] using h (by norm_num : (1 : Int) < 2)
    have hcexp_abs_rounded :
        FloatSpec.Core.Generic_fmt.cexp 2 fexp |rounded| =
          FloatSpec.Core.Generic_fmt.cexp 2 fexp rounded := by
      have h := FloatSpec.Core.Generic_fmt.cexp_abs
        (beta := 2) (fexp := fexp) (x := rounded)
      simpa [wp, PostCond.noThrow, pure] using h (by norm_num : (1 : Int) < 2)
    have hcexp_rounded_repr :
        FloatSpec.Core.Generic_fmt.cexp 2 fexp |rounded| =
          fexp (FloatSpec.Core.Digits.Zdigits 2 m1' + e1) := by
      have hm1'_ne : m1' ≠ 0 := ne_of_gt hm1'_pos
      have hmag :=
        FloatSpec.Core.Float_prop.Raux_mag_F2R_Zdigits
          (beta := 2) (m := m1') (e := e1)
          (by norm_num : (1 : Int) < 2) hm1'_ne
      calc
        FloatSpec.Core.Generic_fmt.cexp 2 fexp |rounded|
            = fexp (FloatSpec.Core.Raux.mag 2 |rounded|) := rfl
        _ = fexp (FloatSpec.Core.Raux.mag 2
              (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m1' e1 :
                FloatSpec.Core.Defs.FlocqFloat 2))) := by rw [hrounded_abs]
        _ = fexp (FloatSpec.Core.Digits.Zdigits 2 m1' + e1) := by
              exact congrArg fexp hmag
    have He2 :
        e1 ≤ fexp (FloatSpec.Core.Digits.Zdigits 2 m1' + e1) := by
      have hround_ge :=
        FloatSpec.Core.Generic_fmt.cexp_round_ge
          (beta := 2) (fexp := fexp) (rnd := rnd_of_mode mode)
          (x := x) hrounded_ne
      calc
        e1 = FloatSpec.Core.Generic_fmt.cexp 2 fexp |x| := htr1.2
        _ = FloatSpec.Core.Generic_fmt.cexp 2 fexp x := hcexp_abs_x
        _ ≤ FloatSpec.Core.Generic_fmt.cexp 2 fexp rounded := by
              rw [FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR] at hround_ge
              exact hround_ge
        _ = FloatSpec.Core.Generic_fmt.cexp 2 fexp |rounded| := hcexp_abs_rounded.symm
        _ = fexp (FloatSpec.Core.Digits.Zdigits 2 m1' + e1) :=
              hcexp_rounded_repr
    have Br :
        FloatSpec.Calc.Bracket.inbetween_float 2 m1' e1 |rounded|
          FloatSpec.Calc.Bracket.Location.loc_Exact := by
      dsimp [FloatSpec.Calc.Bracket.inbetween_float]
      exact FloatSpec.Calc.Bracket.inbetween.inbetween_Exact hrounded_abs
    have htr2_format :
        |rounded| =
            F2R (FloatSpec.Core.Defs.FlocqFloat.mk m2 e2 :
              FloatSpec.Core.Defs.FlocqFloat 2) ∧
          e2 = FloatSpec.Core.Generic_fmt.cexp 2 fexp |rounded| := by
      have hfmt_round :
          FloatSpec.Core.Generic_fmt.generic_format 2 fexp rounded :=
        FloatSpec.Core.Generic_fmt.generic_format_round
          (beta := 2) (fexp := fexp) (rnd := rnd_of_mode mode) (x := x)
      have hfmt_abs :
          FloatSpec.Core.Generic_fmt.generic_format 2 fexp |rounded| :=
        FloatSpec.Core.Generic_fmt.generic_format_abs
          (beta := 2) (fexp := fexp) (x := rounded) hfmt_round
      have hfmt_repr :
          FloatSpec.Core.Generic_fmt.generic_format 2 fexp
            (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m1' e1 :
              FloatSpec.Core.Defs.FlocqFloat 2)) := by
        rw [← hrounded_abs]
        exact hfmt_abs
      have h :=
        FloatSpec.Calc.Round.Audit.truncate_correct_format
          (beta := 2) (fexp := fexp) (m := m1') (e := e1)
          (hm := ne_of_gt hm1'_pos) (Hβ := (by norm_num : (1 : Int) < 2))
          (Hx := hfmt_repr) (He := He2)
      constructor
      · calc
          |rounded| =
              F2R (FloatSpec.Core.Defs.FlocqFloat.mk m1' e1 :
                FloatSpec.Core.Defs.FlocqFloat 2) := hrounded_abs
          _ =
              F2R (FloatSpec.Core.Defs.FlocqFloat.mk m2 e2 :
                FloatSpec.Core.Defs.FlocqFloat 2) := by
                simpa [r2, m2, e2] using h.1
      · simpa [r2, e2, hrounded_abs] using h.2
    have hm2_pos : 0 < m2 := by
      have hpos :
          0 < F2R (FloatSpec.Core.Defs.FlocqFloat.mk m2 e2 :
            FloatSpec.Core.Defs.FlocqFloat 2) := by
        simpa [htr2_format.1] using hrounded_abs_pos
      exact FloatSpec.Core.Float_prop.gt_0_F2R
        (beta := 2)
        (f := FloatSpec.Core.Defs.FlocqFloat.mk m2 e2)
        (by norm_num : (1 : Int) < 2) hpos
    have hm2_nonneg : 0 ≤ m2 := le_of_lt hm2_pos
    have hm2_toNat_pos : 0 < m2.toNat := by
      have hcast : ((m2.toNat : Nat) : Int) = m2 :=
        Int.toNat_of_nonneg hm2_nonneg
      omega
    have hm2_toNat_cast : ((m2.toNat : Nat) : Int) = m2 :=
      Int.toNat_of_nonneg hm2_nonneg
    have hcanon2 :
        canonical_mantissa (prec:=prec) (emax:=emax) m2.toNat e2 = true := by
      apply canonical_mantissa_bsn_of_repr_cexp
        (prec:=prec) (emax:=emax) (mx := m2.toNat) (ex := e2)
        (x := |rounded|) hm2_toNat_pos
      · simpa [hm2_toNat_cast] using htr2_format.1
      · exact htr2_format.2
    have hvalid_fit :=
      validBinarySingleNaNStandardFloat_binary_fit_aux
        (prec:=prec) (emax:=emax) mode sx m2.toNat e2 hm2_toNat_pos hcanon2
    have hfit :=
      binary_fit_aux_correct (prec:=prec) (emax:=emax)
        mode sx m2.toNat e2 hm2_toNat_pos hcanon2
    have hsecond_shr :
        (bsn_shr_fexp (prec:=prec) (emax:=emax) m1' e1
          FloatSpec.Calc.Bracket.Location.loc_Exact).1.shr_m = m2 := by
      unfold bsn_shr_fexp
      change (shr_record_of_loc r2.1 r2.2.2).shr_m = m2
      simp [r2, m2, shr_m_shr_record_of_loc]
    have hsecond_exp :
        (bsn_shr_fexp (prec:=prec) (emax:=emax) m1' e1
          FloatSpec.Calc.Bracket.Location.loc_Exact).2 = e2 := by
      unfold bsn_shr_fexp
      simp [fexp, r2, e2]
    have hnot_zero : ¬m2 = 0 := by omega
    have hpos_bool : 0 < m2 := hm2_pos
    have hresult_eq :
        binary_round_aux (prec:=prec) (emax:=emax) mode sx mx ex lx =
          binary_fit_aux (prec:=prec) (emax:=emax) mode sx m2.toNat e2 := by
      simp [binary_round_aux, bsn_shr_fexp, fexp, sx, r1, m1, e1, l1, m1',
        r2, m2, e2, hm1'_zero, hsecond_shr, hsecond_exp, hm2_toNat_cast,
        hnot_zero, hpos_bool, loc_of_shr_record_of_loc, shr_m_shr_record_of_loc]
    have hresult_eq' :
        binary_round_aux (prec:=prec) (emax:=emax) mode
            (FloatSpec.Core.Raux.Rlt_bool x 0) mx ex lx =
          binary_fit_aux (prec:=prec) (emax:=emax) mode sx m2.toNat e2 := by
      simpa [sx] using hresult_eq
    have hsigned_fit :
        SF2R 2 (StandardFloat.S754_finite sx m2.toNat e2) = rounded := by
      have hunsigned :
          F2R (FloatSpec.Core.Defs.FlocqFloat.mk (m2.toNat : Int) e2 :
            FloatSpec.Core.Defs.FlocqFloat 2) = |rounded| := by
        simpa [hm2_toNat_cast] using htr2_format.1.symm
      have hpow1_pos : 0 < (2 : ℝ) ^ e1 :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) e1
      have hpow1_nonneg : 0 ≤ (2 : ℝ) ^ e1 := le_of_lt hpow1_pos
      have hm1'_real_pos : 0 < (m1' : ℝ) := by exact_mod_cast hm1'_pos
      cases hsx : sx
      · have hrounded_nonneg : 0 ≤ rounded := by
          rw [hround_repr]
          simp [hsx, SF2R, F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Zaux.cond_Zopp,
            le_of_lt hm1'_real_pos, hpow1_nonneg]
          exact mul_nonneg (le_of_lt hm1'_real_pos) hpow1_nonneg
        calc
          SF2R 2 (StandardFloat.S754_finite false m2.toNat e2)
              = F2R (FloatSpec.Core.Defs.FlocqFloat.mk (m2.toNat : Int) e2 :
                  FloatSpec.Core.Defs.FlocqFloat 2) := by
                    simp [SF2R, F2R, FloatSpec.Core.Defs.F2R]
          _ = |rounded| := hunsigned
          _ = rounded := abs_of_nonneg hrounded_nonneg
      · have hrounded_nonpos : rounded ≤ 0 := by
          rw [hround_repr]
          simp [hsx, SF2R, F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Zaux.cond_Zopp,
            le_of_lt hm1'_real_pos, hpow1_nonneg]
          exact mul_nonneg (le_of_lt hm1'_real_pos) hpow1_nonneg
        calc
          SF2R 2 (StandardFloat.S754_finite true m2.toNat e2)
              = -F2R (FloatSpec.Core.Defs.FlocqFloat.mk (m2.toNat : Int) e2 :
                  FloatSpec.Core.Defs.FlocqFloat 2) := by
                    simp [SF2R, F2R, FloatSpec.Core.Defs.F2R]
          _ = -|rounded| := by rw [hunsigned]
          _ = rounded := by
                rw [abs_of_nonpos hrounded_nonpos]
                ring
    have hsigned_fit_abs :
        |SF2R 2 (StandardFloat.S754_finite sx m2.toNat e2)| = |rounded| := by
      rw [hsigned_fit]
    constructor
    · simpa [hresult_eq'] using hvalid_fit
    · have hpayload := hfit.2
      simpa [hresult_eq', rounded, hsigned_fit, hsigned_fit_abs] using hpayload

private noncomputable def maxFiniteR (prec emax : Int) : ℝ :=
  F2R (FloatSpec.Core.Defs.FlocqFloat.mk
    (((2 : Nat) ^ prec.toNat - 1 : Nat) : Int) (emax - prec) :
    FloatSpec.Core.Defs.FlocqFloat 2)

private theorem maxFiniteR_eq {prec emax : Int} [Prec_gt_0 prec] :
    maxFiniteR prec emax =
      FloatSpec.Core.Raux.bpow 2 emax - FloatSpec.Core.Raux.bpow 2 (emax - prec) := by
  have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
  have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
  have hpow_ge_one : 1 ≤ (2 : Nat) ^ prec.toNat := Nat.one_le_two_pow
  have hcast_pow :
      (((2 : Nat) ^ prec.toNat : Nat) : ℝ) = (2 : ℝ) ^ prec := by
    rw [Nat.cast_pow]
    rw [← zpow_natCast]
    congr 1
    exact Int.toNat_of_nonneg hprec_nonneg
  have hmant :
      (((((2 : Nat) ^ prec.toNat - 1 : Nat) : Int) : ℝ)) =
        (2 : ℝ) ^ prec - 1 := by
    rw [Int.cast_natCast]
    rw [Nat.cast_sub hpow_ge_one]
    simp [hcast_pow]
  unfold maxFiniteR F2R FloatSpec.Core.Defs.F2R FloatSpec.Core.Raux.bpow
  simp only [FloatSpec.Core.Defs.FlocqFloat.Fnum, FloatSpec.Core.Defs.FlocqFloat.Fexp,
    hmant]
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  calc
    ((2 : ℝ) ^ prec - 1) * (2 : ℝ) ^ (emax - prec)
        = (2 : ℝ) ^ prec * (2 : ℝ) ^ (emax - prec) - (2 : ℝ) ^ (emax - prec) := by ring
    _ = (2 : ℝ) ^ (prec + (emax - prec)) - (2 : ℝ) ^ (emax - prec) := by
        rw [zpow_add₀ h2ne]
    _ = (2 : ℝ) ^ emax - (2 : ℝ) ^ (emax - prec) := by ring_nf

private theorem maxFiniteR_generic {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp (3 - emax - prec) prec)
      (maxFiniteR prec emax) := by
  have hproof := Bmax_float_proof (prec:=prec) (emax:=emax)
  have hcanon := hproof.2
  have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
  have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
  have hprec_toNat_ne : prec.toNat ≠ 0 := by
    intro hzero
    have : (prec.toNat : Int) = 0 := by simp [hzero]
    have htoNat : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprec_nonneg
    omega
  have hm_pos : 0 < (2 : Nat) ^ prec.toNat - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_two_pow hprec_toNat_ne)
  have hcan_trip := canonical_canonical_mantissa_bsn
    (prec:=prec) (emax:=emax) false ((2 : Nat) ^ prec.toNat - 1) (emax - prec)
    hm_pos hcanon
  have hcan :
      FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
        (FloatSpec.Core.Defs.FlocqFloat.mk
          (((2 : Nat) ^ prec.toNat - 1 : Nat) : Int) (emax - prec)) := by
    simpa [wp, PostCond.noThrow, pure] using hcan_trip trivial
  change FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp (3 - emax - prec) prec)
    (F2R (FloatSpec.Core.Defs.FlocqFloat.mk
      (((2 : Nat) ^ prec.toNat - 1 : Nat) : Int) (emax - prec) :
      FloatSpec.Core.Defs.FlocqFloat 2))
  exact FloatSpec.Core.Generic_fmt.generic_format_canonical
    (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec)
    (f := FloatSpec.Core.Defs.FlocqFloat.mk
      (((2 : Nat) ^ prec.toNat - 1 : Nat) : Int) (emax - prec)) hcan

private theorem maxFiniteR_lt_emax {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    maxFiniteR prec emax < FloatSpec.Core.Raux.bpow 2 emax := by
  have hproof := Bmax_float_proof (prec:=prec) (emax:=emax)
  have hlt := bounded_lt_emax (prec:=prec) (emax:=emax)
    ((2 : Nat) ^ prec.toNat - 1) (emax - prec) hproof.1
  simpa [wp, PostCond.noThrow, pure, maxFiniteR] using hlt trivial

private theorem unsigned_le_maxFiniteR {prec emax : Int} [Prec_gt_0 prec]
    (mx : Nat) (ex : Int)
    (h : bounded (prec:=prec) (emax:=emax) mx ex = true) :
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
      FloatSpec.Core.Defs.FlocqFloat 2) ≤ maxFiniteR prec emax := by
  have hle := bounded_le_emax_minus_prec (prec:=prec) (emax:=emax) mx ex h
  have hle' := by
    simpa [wp, PostCond.noThrow, pure] using hle trivial
  simpa [maxFiniteR_eq (prec:=prec) (emax:=emax)] using hle'

-- Coq: sign_plus_overflow
theorem sign_plus_overflow {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int)
    (sy : Bool) (my : Nat) (ey : Int)
    (Hx : bounded (prec:=prec) (emax:=emax) mx ex = true)
    (Hy : bounded (prec:=prec) (emax:=emax) my ey = true) :
    let z :=
      (SF2R 2 (StandardFloat.S754_finite sx mx ex) +
        SF2R 2 (StandardFloat.S754_finite sy my ey))
    FloatSpec.Core.Raux.bpow 2 emax ≤
      |FloatSpec.Core.Generic_fmt.round_to_generic 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) z| →
    sx = FloatSpec.Core.Raux.Rlt_bool z 0 ∧ sx = sy := by
  intro z Hover
  by_cases hs : sx = sy
  · constructor
    · subst sy
      cases sx
      · have hz_nonneg : 0 ≤ z := by
          dsimp [z, SF2R, F2R, FloatSpec.Core.Defs.F2R]
          positivity
        simp [FloatSpec.Core.Raux.Rlt_bool, hz_nonneg]
      · have hz_nonpos : z ≤ 0 := by
          dsimp [z, SF2R, F2R, FloatSpec.Core.Defs.F2R]
          have hx_nonneg : 0 ≤ (((mx : Int) : ℝ) * ((2 : Int) : ℝ) ^ ex) := by positivity
          have hy_nonneg : 0 ≤ (((my : Int) : ℝ) * ((2 : Int) : ℝ) ^ ey) := by positivity
          simp only [Int.cast_neg]
          nlinarith [hx_nonneg, hy_nonneg]
        have hz_ne : z ≠ 0 := by
          intro hz0
          have hround0 :
              FloatSpec.Core.Generic_fmt.round_to_generic 2
                (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) z = 0 := by
            simpa [hz0] using
              (round_to_generic_rnd_of_mode_zero (mode := mode)
                (fexp := FLT_exp (3 - emax - prec) prec))
          have hbpow_trip := FloatSpec.Core.Raux.bpow_gt_0 2 emax (by norm_num)
          have hbpow_pos : 0 < FloatSpec.Core.Raux.bpow 2 emax := by
            simpa [wp, PostCond.noThrow, pure] using hbpow_trip trivial
          rw [hround0, abs_zero] at Hover
          linarith
        have hz_neg : z < 0 := lt_of_le_of_ne hz_nonpos hz_ne
        simp [FloatSpec.Core.Raux.Rlt_bool, hz_neg]
    · exact hs
  · exfalso
    have hx_le := unsigned_le_maxFiniteR (prec:=prec) (emax:=emax) mx ex Hx
    have hy_le := unsigned_le_maxFiniteR (prec:=prec) (emax:=emax) my ey Hy
    have hx_nonneg :
        0 ≤ F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
          FloatSpec.Core.Defs.FlocqFloat 2) := by
      unfold F2R FloatSpec.Core.Defs.F2R
      positivity
    have hy_nonneg :
        0 ≤ F2R (FloatSpec.Core.Defs.FlocqFloat.mk (my : Int) ey :
          FloatSpec.Core.Defs.FlocqFloat 2) := by
      unfold F2R FloatSpec.Core.Defs.F2R
      positivity
    have hx_le_raw :
        (((mx : Int) : ℝ) * ((2 : Int) : ℝ) ^ ex) ≤ maxFiniteR prec emax := by
      simpa [F2R, FloatSpec.Core.Defs.F2R] using hx_le
    have hy_le_raw :
        (((my : Int) : ℝ) * ((2 : Int) : ℝ) ^ ey) ≤ maxFiniteR prec emax := by
      simpa [F2R, FloatSpec.Core.Defs.F2R] using hy_le
    have hx_nonneg_raw :
        0 ≤ (((mx : Int) : ℝ) * ((2 : Int) : ℝ) ^ ex) := by
      simpa [F2R, FloatSpec.Core.Defs.F2R] using hx_nonneg
    have hy_nonneg_raw :
        0 ≤ (((my : Int) : ℝ) * ((2 : Int) : ℝ) ^ ey) := by
      simpa [F2R, FloatSpec.Core.Defs.F2R] using hy_nonneg
    have hz_abs_le : |z| ≤ maxFiniteR prec emax := by
      cases sx <;> cases sy <;> simp at hs
      all_goals
        dsimp [z, SF2R, F2R, FloatSpec.Core.Defs.F2R]
        simp only [Int.cast_neg]
        rw [abs_le]
        constructor <;> nlinarith
          [hx_le_raw, hy_le_raw, hx_nonneg_raw, hy_nonneg_raw]
    have hround_le :
        |FloatSpec.Core.Generic_fmt.round_to_generic 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) z|
          ≤ maxFiniteR prec emax := by
      rw [FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR]
      rw [abs_le] at hz_abs_le ⊢
      have hfmt := maxFiniteR_generic (prec:=prec) (emax:=emax)
      have hfmt_neg :
          FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp (3 - emax - prec) prec)
            (-(maxFiniteR prec emax)) :=
        FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec)
          (x := maxFiniteR prec emax) hfmt
      constructor
      · exact FloatSpec.Core.Generic_fmt.roundR_ge_generic
          (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec)
          (rnd := rnd_of_mode mode) (x := -(maxFiniteR prec emax)) (y := z)
          (hβ := by norm_num) hfmt_neg hz_abs_le.1
      · exact FloatSpec.Core.Generic_fmt.roundR_le_generic
          (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec)
          (rnd := rnd_of_mode mode) (x := z) (y := maxFiniteR prec emax)
          (hβ := by norm_num) hfmt hz_abs_le.2
    have hmax_lt := maxFiniteR_lt_emax (prec:=prec) (emax:=emax)
    linarith

-- Coq: Bulp_correct_aux
theorem Bulp_correct_aux :
  bounded (prec:=prec) (emax:=emax) 1 (3 - emax - prec) = true := by
  unfold bounded
  rw [Bool.and_eq_true, Bool.and_eq_true]
  repeat rw [decide_eq_true_eq]
  constructor
  · constructor
    · have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
      have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
      have hprec_toNat_ne : prec.toNat ≠ 0 := by
        intro hzero
        have hcast : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprec_nonneg
        rw [hzero] at hcast
        grind
      exact Nat.one_lt_two_pow hprec_toNat_ne
    · rfl
  · have hemax_ge_two := (inferInstance : Prec_lt_emax prec emax).emax_ge_2
    grind

-- Coq: Bulp
noncomputable def Bulp (x : B754) : B754 :=
  match x with
  | B754.B754_zero _ => B754.B754_finite false 1 (3 - emax - prec)
  | B754.B754_infinity _ => B754.B754_infinity false
  | B754.B754_nan => B754.B754_nan
  | B754.B754_finite _ _ e =>
      binary_normalize (prec:=prec) (emax:=emax) RoundingMode.RTZ 1 e false

-- Coq: is_nan_Bulp
theorem is_nan_Bulp (x : B754) :
    BSN_is_nan (Bulp (prec:=prec) (emax:=emax) x) = BSN_is_nan x := by
  cases x with
  | B754_zero sx => rfl
  | B754_infinity sx => rfl
  | B754_nan => rfl
  | B754_finite sx mx e =>
      simpa [Bulp, BSN_is_nan] using
        is_nan_binary_normalize (prec:=prec) (emax:=emax)
          RoundingMode.RTZ 1 e false

-- Coq: Bulp'
noncomputable def Bulp' (x : B754) : B754 :=
  Bldexp (prec:=prec) (emax:=emax) RoundingMode.RNE Bone
    ((FLT_exp (3 - emax - prec) prec)
      (Bfrexp_bsn (prec:=prec) (emax:=emax) x).2)

-- Coq: Bplus
noncomputable def Bplus (mode : RoundingMode) (x y : B754) : B754 :=
  match x, y with
  | B754.B754_nan, _ => B754.B754_nan
  | _, B754.B754_nan => B754.B754_nan
  | B754.B754_infinity sx, B754.B754_infinity sy =>
      if sx == sy then x else B754.B754_nan
  | B754.B754_infinity _, _ => x
  | _, B754.B754_infinity _ => y
  | B754.B754_zero sx, B754.B754_zero sy =>
      if sx == sy then x
      else
        match mode with
        | RoundingMode.RTN => B754.B754_zero true
        | _ => B754.B754_zero false
  | B754.B754_zero _, _ => y
  | _, B754.B754_zero _ => x
  | B754.B754_finite sx mx ex, B754.B754_finite sy my ey =>
      let ez := min ex ey
      binary_normalize (prec:=prec) (emax:=emax) mode
        (Fplus_naive sx mx ex sy my ey ez) ez
        (match mode with
        | RoundingMode.RTN => true
        | _ => false)

-- Coq: Bminus. This is extensionally the constructor match used upstream:
-- subtraction is addition after flipping the second operand's sign.
noncomputable def Bminus (mode : RoundingMode) (x y : B754) : B754 :=
  Bplus (prec:=prec) (emax:=emax) mode x (Bopp_bsn y)

-- Coq: Bpred_pos'
noncomputable def Bpred_pos' (x : B754) : B754 :=
  match x with
  | B754.B754_finite _ mx _ =>
      let d :=
        if 2 * mx == (2 : Nat) ^ prec.toNat then
          Bldexp (prec:=prec) (emax:=emax) RoundingMode.RNE Bone
            ((FLT_exp (3 - emax - prec) prec)
              ((Bfrexp_bsn (prec:=prec) (emax:=emax) x).2 - 1))
        else
          Bulp' (prec:=prec) (emax:=emax) x
      Bminus (prec:=prec) (emax:=emax) RoundingMode.RNE x d
  | _ => x

-- Coq: Bsucc'
noncomputable def Bsucc' (x : B754) : B754 :=
  match x with
  | B754.B754_zero _ =>
      Bldexp (prec:=prec) (emax:=emax) RoundingMode.RNE Bone (3 - emax - prec)
  | B754.B754_infinity false => x
  | B754.B754_infinity true =>
      Bopp_bsn (Bmax_float (prec:=prec) (emax:=emax))
  | B754.B754_nan => B754.B754_nan
  | B754.B754_finite false _ _ =>
      Bplus (prec:=prec) (emax:=emax) RoundingMode.RNE x
        (Bulp (prec:=prec) (emax:=emax) x)
  | B754.B754_finite true _ _ =>
      Bopp_bsn (Bpred_pos' (prec:=prec) (emax:=emax) (Bopp_bsn x))

-- Coq: Bsucc
noncomputable def Bsucc (x : B754) : B754 :=
  match x with
  | B754.B754_zero _ => B754.B754_finite false 1 (3 - emax - prec)
  | B754.B754_infinity false => x
  | B754.B754_infinity true =>
      Bopp_bsn (Bmax_float (prec:=prec) (emax:=emax))
  | B754.B754_nan => B754.B754_nan
  | B754.B754_finite false mx ex =>
      SF2B (binary_round (prec:=prec) (emax:=emax) RoundingMode.RTP false (mx + 1) ex)
  | B754.B754_finite true mx ex =>
      SF2B (binary_round (prec:=prec) (emax:=emax) RoundingMode.RTZ true (2 * mx - 1) (ex - 1))

-- Coq: is_nan_Bsucc
theorem is_nan_Bsucc (x : B754) :
    BSN_is_nan (Bsucc (prec:=prec) (emax:=emax) x) = BSN_is_nan x := by
  cases x with
  | B754_zero sx => rfl
  | B754_infinity sx =>
      cases sx <;> rfl
  | B754_nan => rfl
  | B754_finite sx mx ex =>
      cases sx
      · rw [Bsucc, BSN_is_nan_SF2B_eq]
        exact is_nan_binary_round (prec:=prec) (emax:=emax)
          RoundingMode.RTP false (mx + 1) ex
      · rw [Bsucc, BSN_is_nan_SF2B_eq]
        exact is_nan_binary_round (prec:=prec) (emax:=emax)
          RoundingMode.RTZ true (2 * mx - 1) (ex - 1)

-- Coq: Bpred
noncomputable def Bpred (x : B754) : B754 :=
  Bopp_bsn (Bsucc (prec:=prec) (emax:=emax) (Bopp_bsn x))

-- Coq: is_nan_Bpred
theorem is_nan_Bpred (x : B754) :
    BSN_is_nan (Bpred (prec:=prec) (emax:=emax) x) = BSN_is_nan x := by
  unfold Bpred
  calc
    BSN_is_nan (Bopp_bsn (Bsucc (prec:=prec) (emax:=emax) (Bopp_bsn x)))
        = BSN_is_nan (Bsucc (prec:=prec) (emax:=emax) (Bopp_bsn x)) := by
            cases Bsucc (prec:=prec) (emax:=emax) (Bopp_bsn x) <;> rfl
    _ = BSN_is_nan (Bopp_bsn x) :=
        is_nan_Bsucc (prec:=prec) (emax:=emax) (Bopp_bsn x)
    _ = BSN_is_nan x := by
        cases x <;> rfl

-- Legacy compatibility endpoint: assumes the result equation instead of
-- deriving it. The source-shaped theorem is `BinarySingleNaN.Bsqrt_correct_aux`.
noncomputable def Bsqrt_correct_aux_from_assumed_rounding_check {prec emax : Int}
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (mode : RoundingMode)
  (mx : Nat) (ex : Int)
  (Hx : bounded (prec:=prec) (emax:=emax) mx ex = true) : StandardFloat :=
  StandardFloat.S754_finite false mx ex

theorem Bsqrt_correct_aux_from_assumed_rounding {prec emax : Int}
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (mode : RoundingMode) (rnd : ℝ → Int) (hrnd0 : rnd 0 = 0)
  (mx : Nat) (ex : Int)
  (Hx : bounded (prec:=prec) (emax:=emax) mx ex = true)
  (hsqrt : SF2R 2 (StandardFloat.S754_finite false mx ex) =
           FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) ⟨rnd, hrnd0⟩
           (Real.sqrt (SF2R 2 (StandardFloat.S754_finite false mx ex)))) :
  ⦃⌜True⌝⦄
  (pure (Bsqrt_correct_aux_from_assumed_rounding_check
    (prec:=prec) (emax:=emax) mode mx ex Hx) : Id StandardFloat)
  ⦃⇓z => ⌜
      let x := SF2R 2 (StandardFloat.S754_finite false mx ex);
      valid_binary_SF (prec:=prec) (emax:=emax) z = true ∧
      SF2R 2 z = FloatSpec.Calc.Round.round 2 (FLT_exp (3 - emax - prec) prec) ⟨rnd, hrnd0⟩ (Real.sqrt x) ∧
      is_finite_SF z = true ∧ sign_SF z = false⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure]
  unfold Bsqrt_correct_aux_from_assumed_rounding_check
  constructor
  · rfl
  constructor
  · simp only [Id.run]
    exact hsqrt
  constructor
  · rfl
  · rfl

end ExperimentalSingleNaNArithmetic

-- Coq: `SFdiv_core_binary`.
noncomputable def SFdiv_core_binary (prec emax : Int)
    (mx ex my ey : Int) : Int × Int × Loc :=
  FloatSpec.Calc.Div.Fdiv 2 (FLT_exp (3 - emax - prec) prec)
    (FloatSpec.Core.Defs.FlocqFloat.mk mx ex :
      FloatSpec.Core.Defs.FlocqFloat 2)
    (FloatSpec.Core.Defs.FlocqFloat.mk my ey :
      FloatSpec.Core.Defs.FlocqFloat 2)

private theorem SFdiv_core_binary_correct_data {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    [FloatSpec.Core.Generic_fmt.Monotone_exp
      (FLT_exp (3 - emax - prec) prec)]
    (mx ex my ey : Int) (hmx_pos : 0 < mx) (hmy_pos : 0 < my) :
    let result := SFdiv_core_binary prec emax mx ex my ey
    let quotient :=
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk mx ex :
        FloatSpec.Core.Defs.FlocqFloat 2) /
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk my ey :
        FloatSpec.Core.Defs.FlocqFloat 2)
    FloatSpec.Calc.Bracket.inbetween_float 2 result.1 result.2.1
        quotient result.2.2 ∧
      result.2.1 ≤ FloatSpec.Core.Generic_fmt.cexp 2
        (FLT_exp (3 - emax - prec) prec) quotient := by
  let X : FloatSpec.Core.Defs.FlocqFloat 2 :=
    FloatSpec.Core.Defs.FlocqFloat.mk mx ex
  let Y : FloatSpec.Core.Defs.FlocqFloat 2 :=
    FloatSpec.Core.Defs.FlocqFloat.mk my ey
  let fexp := FLT_exp (3 - emax - prec) prec
  let result := SFdiv_core_binary prec emax mx ex my ey
  let quotient := F2R X / F2R Y
  have hx_pos : 0 < F2R X :=
    FloatSpec.Core.Float_prop.F2R_gt_0
      (beta := 2) (f := X) (by norm_num) (by simpa [X] using hmx_pos)
  have hy_pos : 0 < F2R Y :=
    FloatSpec.Core.Float_prop.F2R_gt_0
      (beta := 2) (f := Y) (by norm_num) (by simpa [Y] using hmy_pos)
  have hdiv := FloatSpec.Calc.Div.Fdiv_correct
    (beta := 2) (fexp := fexp) X Y (by norm_num) hx_pos hy_pos
  have hbetween :
      FloatSpec.Calc.Bracket.inbetween_float 2 result.1 result.2.1
        quotient result.2.2 := by
    dsimp [result, SFdiv_core_binary, quotient, X, Y, fexp]
    exact (hdiv ⟨hx_pos, hy_pos⟩).2
  let d1 := FloatSpec.Core.Digits.Zdigits 2 mx
  let d2 := FloatSpec.Core.Digits.Zdigits 2 my
  let e' := (d1 + ex) - (d2 + ey)
  have hmag := FloatSpec.Calc.Div.mag_div_F2R
    (beta := 2) (m1 := mx) (e1 := ex) (m2 := my) (e2 := ey)
    hmx_pos hmy_pos (by norm_num)
  have hmag_bounds := hmag ⟨hmx_pos, hmy_pos⟩
  have hmagX :
      FloatSpec.Core.Raux.mag 2 (F2R X) = d1 + ex := by
    simpa [X, d1] using
      (FloatSpec.Core.Float_prop.Raux_mag_F2R_Zdigits
        (beta := 2) (m := mx) (e := ex) (by norm_num : (1 : Int) < 2)
        (ne_of_gt hmx_pos))
  have hmagY :
      FloatSpec.Core.Raux.mag 2 (F2R Y) = d2 + ey := by
    simpa [Y, d2] using
      (FloatSpec.Core.Float_prop.Raux_mag_F2R_Zdigits
        (beta := 2) (m := my) (e := ey) (by norm_num : (1 : Int) < 2)
        (ne_of_gt hmy_pos))
  have hmag_lower :
      e' ≤ FloatSpec.Core.Raux.mag 2 quotient := by
    have hraw := hmag_bounds.1
    change FloatSpec.Core.Raux.mag 2 (F2R X) -
        FloatSpec.Core.Raux.mag 2 (F2R Y) ≤
      FloatSpec.Core.Raux.mag 2 quotient at hraw
    rw [hmagX, hmagY] at hraw
    simpa [e'] using hraw
  have he_le_fexp : result.2.1 ≤ fexp e' := by
    simp [result, SFdiv_core_binary, FloatSpec.Calc.Div.Fdiv, fexp, e', d1, d2,
      X, Y]
  have hfexp_mono :
      fexp e' ≤ fexp (FloatSpec.Core.Raux.mag 2 quotient) :=
    FloatSpec.Core.Generic_fmt.Monotone_exp.mono hmag_lower
  have he_cexp :
      result.2.1 ≤ FloatSpec.Core.Generic_fmt.cexp 2 fexp quotient := by
    exact le_trans he_le_fexp hfexp_mono
  dsimp [result, quotient, SFdiv_core_binary, X, Y, fexp] at hbetween he_cexp ⊢
  exact ⟨hbetween, he_cexp⟩

-- Coq: `SFsqrt_core_binary`.
-- Specialize the generic square-root core to the binary FLT exponent used by
-- the IEEE layer.  Keeping the full location result is essential: it is the
-- rounding information consumed by `binary_round_aux`.
noncomputable def SFsqrt_core_binary (prec emax : Int) (mx ex : Int) :
    Int × Int × Loc :=
  FloatSpec.Calc.Sqrt.Fsqrt 2 (FLT_exp (3 - emax - prec) prec)
    (FloatSpec.Core.Defs.FlocqFloat.mk mx ex :
      FloatSpec.Core.Defs.FlocqFloat 2)

private theorem Fsqrt_core_fst_pos (mx ex ez : Int) (hmx_pos : 0 < mx)
    (hez : 2 * ez ≤ ex) :
    0 < (FloatSpec.Calc.Sqrt.Fsqrt_core 2 mx ex ez).1 := by
  let scaled := mx * FloatSpec.Core.Zaux.Zpower 2 (ex - 2 * ez)
  have hdiff : 0 ≤ ex - 2 * ez := by omega
  have hpow : FloatSpec.Core.Zaux.Zpower 2 (ex - 2 * ez) =
      (2 : Int) ^ Int.natAbs (ex - 2 * ez) :=
    FloatSpec.Core.Zaux.Zpower_Zpower_nat 2 (ex - 2 * ez) hdiff
  have hscaled_pos : 0 < scaled := by
    change 0 < mx * FloatSpec.Core.Zaux.Zpower 2 (ex - 2 * ez)
    rw [hpow]
    exact mul_pos hmx_pos (pow_pos (by norm_num : (0 : Int) < 2) _)
  have hscaled_toNat_pos : 0 < scaled.toNat := by omega
  change 0 < (if scaled < 0 then 0 else Int.sqrt scaled)
  rw [ite_eq_right (by omega)]
  unfold Int.sqrt
  exact_mod_cast (Nat.sqrt_pos.mpr hscaled_toNat_pos)

private theorem SFsqrt_core_binary_correct_data {prec emax : Int}
    [Prec_gt_0 prec]
    (mx ex : Int) (hmx_pos : 0 < mx) :
    let result := SFsqrt_core_binary prec emax mx ex
    0 < result.1 ∧
      FloatSpec.Calc.Bracket.inbetween_float 2 result.1 result.2.1
        (Real.sqrt
          (F2R (FloatSpec.Core.Defs.FlocqFloat.mk mx ex :
            FloatSpec.Core.Defs.FlocqFloat 2))) result.2.2 ∧
      result.2.1 ≤
        FLT_exp (3 - emax - prec) prec
          (FloatSpec.Core.Digits.Zdigits 2 result.1 + result.2.1) := by
  let input : FloatSpec.Core.Defs.FlocqFloat 2 :=
    FloatSpec.Core.Defs.FlocqFloat.mk mx ex
  have hx_pos : 0 < F2R input :=
    FloatSpec.Core.Float_prop.F2R_gt_0
      (beta := 2) (f := input) (by norm_num) (by simpa [input] using hmx_pos)
  have hsqrt := FloatSpec.Calc.Sqrt.Fsqrt_correct
    (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec)
    input hx_pos (by norm_num : (1 : Int) < 2)
  let result := SFsqrt_core_binary prec emax mx ex
  have hresult :
      result = FloatSpec.Calc.Sqrt.Fsqrt 2
        (FLT_exp (3 - emax - prec) prec) input := by
    rfl
  have hsqrt_result :
      result.2.1 ≤
          FloatSpec.Core.Generic_fmt.cexp 2
            (FLT_exp (3 - emax - prec) prec) (Real.sqrt (F2R input)) ∧
        FloatSpec.Calc.Bracket.inbetween_float 2 result.1 result.2.1
          (Real.sqrt (F2R input)) result.2.2 := by
    simpa [hresult] using hsqrt
  have hsqrt_pos : 0 < Real.sqrt (F2R input) := Real.sqrt_pos.2 hx_pos
  have hcexp := FloatSpec.Calc.Round.cexp_inbetween_float
    (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec)
    (x := Real.sqrt (F2R input)) (m := result.1) (e := result.2.1)
    (l := result.2.2) (by norm_num : (1 : Int) < 2) hsqrt_pos
    hsqrt_result.2 (Or.inl hsqrt_result.1)
  have hexp :
      result.2.1 ≤
        FLT_exp (3 - emax - prec) prec
          (FloatSpec.Core.Digits.Zdigits 2 result.1 + result.2.1) := by
    rw [hcexp] at hsqrt_result
    exact hsqrt_result.1
  have hmant : 0 < result.1 := by
    have hez :
        2 * min
            (FLT_exp (3 - emax - prec) prec
              ((FloatSpec.Core.Digits.Zdigits 2 mx + ex + 1) / 2))
            (ex / 2) ≤ ex := by
      calc
        2 * min
              (FLT_exp (3 - emax - prec) prec
                ((FloatSpec.Core.Digits.Zdigits 2 mx + ex + 1) / 2))
              (ex / 2) ≤ 2 * (ex / 2) :=
          Int.mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        _ ≤ ex := Int.mul_ediv_self_le (by norm_num : (2 : Int) ≠ 0)
    simpa [result, SFsqrt_core_binary, FloatSpec.Calc.Sqrt.Fsqrt, input] using
      Fsqrt_core_fst_pos mx ex
        (min
          (FLT_exp (3 - emax - prec) prec
            ((FloatSpec.Core.Digits.Zdigits 2 mx + ex + 1) / 2))
          (ex / 2)) hmx_pos hez
  exact ⟨hmant, hsqrt_result.2, hexp⟩

-- Coq: `binary_round_aux_correct'`.
theorem binary_round_aux_correct' {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    [FloatSpec.Core.Generic_fmt.Monotone_exp
      (FLT_exp (3 - emax - prec) prec)]
    (mode : RoundingMode) (x : ℝ) (mx ex : Int) (lx : Loc)
    (hx_ne : x ≠ 0)
    (Bx : FloatSpec.Calc.Bracket.inbetween_float 2 mx ex |x| lx)
    (Ex : ex ≤ FloatSpec.Core.Generic_fmt.cexp 2
      (FLT_exp (3 - emax - prec) prec) x) :
    let z := binary_round_aux (prec:=prec) (emax:=emax) mode
      (FloatSpec.Core.Raux.Rlt_bool x 0) mx ex lx
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      if FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        SF2R 2 z =
            FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x ∧
          is_finite_SF z = true ∧
          sign_SF z = FloatSpec.Core.Raux.Rlt_bool x 0
      else
        z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool x 0) := by
  have hx_abs_pos : 0 < |x| := abs_pos.mpr hx_ne
  have hcexp_abs :
      FloatSpec.Core.Generic_fmt.cexp 2 (FLT_exp (3 - emax - prec) prec) |x| =
        FloatSpec.Core.Generic_fmt.cexp 2 (FLT_exp (3 - emax - prec) prec) x := by
    have h := FloatSpec.Core.Generic_fmt.cexp_abs
      (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec) (x := x)
    simpa [wp, PostCond.noThrow, pure] using h (by norm_num : (1 : Int) < 2)
  have ExAbs :
      ex ≤ FloatSpec.Core.Generic_fmt.cexp 2
        (FLT_exp (3 - emax - prec) prec) |x| := by
    simpa [hcexp_abs] using Ex
  have hcexp := FloatSpec.Calc.Round.cexp_inbetween_float
    (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec)
    (x := |x|) (m := mx) (e := ex) (l := lx)
    (by norm_num : (1 : Int) < 2) hx_abs_pos Bx (Or.inl ExAbs)
  have ExDigits :
      ex ≤ FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Digits.Zdigits 2 mx + ex) := by
    simpa [hcexp] using ExAbs
  exact ExperimentalSingleNaNArithmetic.binary_round_aux_correct_proof
    (prec:=prec) (emax:=emax) mode x mx ex lx hx_ne Bx ExDigits

-- Coq: `binary_round_aux_correct`.
theorem binary_round_aux_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    [FloatSpec.Core.Generic_fmt.Monotone_exp
      (FLT_exp (3 - emax - prec) prec)]
    (mode : RoundingMode) (x : ℝ) (mx : Nat) (ex : Int) (lx : Loc)
    (hmx_pos : 0 < mx)
    (Bx : FloatSpec.Calc.Bracket.inbetween_float 2 (mx : Int) ex |x| lx)
    (Ex : ex ≤
      FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex)) :
    let z := binary_round_aux (prec:=prec) (emax:=emax) mode
      (FloatSpec.Core.Raux.Rlt_bool x 0) (mx : Int) ex lx
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      if FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        SF2R 2 z =
            FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x ∧
          is_finite_SF z = true ∧
          sign_SF z = FloatSpec.Core.Raux.Rlt_bool x 0
      else
        z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool x 0) := by
  have hx_abs_pos : 0 < |x| := by
    have hleft :=
      (FloatSpec.Calc.Bracket.inbetween_float_bounds
        (beta := 2) (x := |x|) (m := (mx : Int)) (e := ex) (l := lx)
        Bx (by norm_num : (1 : Int) < 2)).1
    have hmx_int_pos : (0 : Int) < (mx : Int) := by exact_mod_cast hmx_pos
    have hF_pos :
        0 < F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
          FloatSpec.Core.Defs.FlocqFloat 2) :=
      FloatSpec.Core.Float_prop.F2R_gt_0
        (beta := 2)
        (f := FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex)
        (by norm_num : (1 : Int) < 2) hmx_int_pos
    exact lt_of_lt_of_le hF_pos hleft
  have hx_ne : x ≠ 0 := abs_pos.mp hx_abs_pos
  exact ExperimentalSingleNaNArithmetic.binary_round_aux_correct_proof
    (prec:=prec) (emax:=emax) mode x (mx : Int) ex lx hx_ne Bx Ex

-- Coq: `Bdiv_correct_aux`.
theorem Bdiv_correct_aux {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    [FloatSpec.Core.Generic_fmt.Monotone_exp
      (FLT_exp (3 - emax - prec) prec)]
    (mode : RoundingMode) (sx : Bool) (mx : FloatSpec.Core.Zaux.Positive)
    (ex : Int) (sy : Bool) (my : FloatSpec.Core.Zaux.Positive) (ey : Int) :
    let mxn := FloatSpec.Core.Zaux.positiveToNat mx
    let myn := FloatSpec.Core.Zaux.positiveToNat my
    let x := SF2R 2 (StandardFloat.S754_finite sx mxn ex)
    let y := SF2R 2 (StandardFloat.S754_finite sy myn ey)
    let result := SFdiv_core_binary prec emax (mxn : Int) ex (myn : Int) ey
    let z := binary_round_aux (prec:=prec) (emax:=emax) mode
      (Bool.xor sx sy) result.1 result.2.1 result.2.2
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      if FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) (x / y)|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        SF2R 2 z =
            FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) (x / y) ∧
          is_finite_SF z = true ∧ sign_SF z = Bool.xor sx sy
      else
        z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode
          (Bool.xor sx sy) := by
  classical
  let mxn := FloatSpec.Core.Zaux.positiveToNat mx
  let myn := FloatSpec.Core.Zaux.positiveToNat my
  let unsignedX :=
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mxn : Int) ex :
      FloatSpec.Core.Defs.FlocqFloat 2)
  let unsignedY :=
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (myn : Int) ey :
      FloatSpec.Core.Defs.FlocqFloat 2)
  let x := SF2R 2 (StandardFloat.S754_finite sx mxn ex)
  let y := SF2R 2 (StandardFloat.S754_finite sy myn ey)
  let quotient := x / y
  let unsignedQuotient := unsignedX / unsignedY
  let result := SFdiv_core_binary prec emax (mxn : Int) ex (myn : Int) ey
  let z := binary_round_aux (prec:=prec) (emax:=emax) mode
    (Bool.xor sx sy) result.1 result.2.1 result.2.2
  have hmx_pos : 0 < mxn := positiveToNat_pos_bsn mx
  have hmy_pos : 0 < myn := positiveToNat_pos_bsn my
  have hmx_int_pos : (0 : Int) < (mxn : Int) := by exact_mod_cast hmx_pos
  have hmy_int_pos : (0 : Int) < (myn : Int) := by exact_mod_cast hmy_pos
  have hunsignedX_pos : 0 < unsignedX :=
    FloatSpec.Core.Float_prop.F2R_gt_0
      (beta := 2)
      (f := FloatSpec.Core.Defs.FlocqFloat.mk (mxn : Int) ex)
      (by norm_num : (1 : Int) < 2) hmx_int_pos
  have hunsignedY_pos : 0 < unsignedY :=
    FloatSpec.Core.Float_prop.F2R_gt_0
      (beta := 2)
      (f := FloatSpec.Core.Defs.FlocqFloat.mk (myn : Int) ey)
      (by norm_num : (1 : Int) < 2) hmy_int_pos
  have hx_repr : x = if sx then -unsignedX else unsignedX := by
    cases sx <;>
      simp [x, unsignedX, SF2R, F2R, FloatSpec.Core.Defs.F2R]
  have hy_repr : y = if sy then -unsignedY else unsignedY := by
    cases sy <;>
      simp [y, unsignedY, SF2R, F2R, FloatSpec.Core.Defs.F2R]
  have hunsignedQuotient_pos : 0 < unsignedQuotient :=
    div_pos hunsignedX_pos hunsignedY_pos
  have hquotient_repr :
      quotient = if Bool.xor sx sy then -unsignedQuotient else unsignedQuotient := by
    cases sx <;> cases sy <;>
      simp [quotient, unsignedQuotient, hx_repr, hy_repr, Bool.xor, div_neg, neg_div]
  have hquotient_abs : |quotient| = unsignedQuotient := by
    rw [hquotient_repr]
    split <;> simp [abs_of_pos hunsignedQuotient_pos]
  have hquotient_sign :
      FloatSpec.Core.Raux.Rlt_bool quotient 0 = Bool.xor sx sy := by
    rw [hquotient_repr]
    cases sx <;> cases sy <;>
      simp [Bool.xor, FloatSpec.Core.Raux.Rlt_bool, hunsignedQuotient_pos,
        not_lt.mpr (le_of_lt hunsignedQuotient_pos)]
  have hx_ne : x ≠ 0 := by
    rw [hx_repr]
    cases sx <;> simp [ne_of_gt hunsignedX_pos]
  have hy_ne : y ≠ 0 := by
    rw [hy_repr]
    cases sy <;> simp [ne_of_gt hunsignedY_pos]
  have hquotient_ne : quotient ≠ 0 := div_ne_zero hx_ne hy_ne
  have hdata := SFdiv_core_binary_correct_data (prec:=prec) (emax:=emax)
    (mxn : Int) ex (myn : Int) ey hmx_int_pos hmy_int_pos
  have hbetween :
      FloatSpec.Calc.Bracket.inbetween_float 2 result.1 result.2.1
        |quotient| result.2.2 := by
    simpa [result, unsignedQuotient, unsignedX, unsignedY, hquotient_abs] using
      hdata.1
  have hcexp_abs :
      FloatSpec.Core.Generic_fmt.cexp 2 (FLT_exp (3 - emax - prec) prec)
          |quotient| =
        FloatSpec.Core.Generic_fmt.cexp 2 (FLT_exp (3 - emax - prec) prec)
          quotient := by
    have h := FloatSpec.Core.Generic_fmt.cexp_abs
      (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec) (x := quotient)
    simpa [wp, PostCond.noThrow, pure] using h (by norm_num : (1 : Int) < 2)
  have hexp :
      result.2.1 ≤ FloatSpec.Core.Generic_fmt.cexp 2
        (FLT_exp (3 - emax - prec) prec) quotient := by
    calc
      result.2.1 ≤ FloatSpec.Core.Generic_fmt.cexp 2
          (FLT_exp (3 - emax - prec) prec) unsignedQuotient := by
            simpa [result, unsignedQuotient, unsignedX, unsignedY] using hdata.2
      _ = FloatSpec.Core.Generic_fmt.cexp 2
          (FLT_exp (3 - emax - prec) prec) |quotient| := by
            rw [hquotient_abs]
      _ = FloatSpec.Core.Generic_fmt.cexp 2
          (FLT_exp (3 - emax - prec) prec) quotient := hcexp_abs
  have hround := binary_round_aux_correct' (prec:=prec) (emax:=emax)
    mode quotient result.1 result.2.1 result.2.2 hquotient_ne hbetween hexp
  simpa [mxn, myn, x, y, quotient, result, z, hquotient_sign] using hround

-- Coq: `Bmult_correct_aux`.
theorem Bmult_correct_aux {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    [FloatSpec.Core.Generic_fmt.Monotone_exp
      (FLT_exp (3 - emax - prec) prec)]
    (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int)
    (hmx_pos : 0 < mx)
    (Hx : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true)
    (sy : Bool) (my : Nat) (ey : Int)
    (hmy_pos : 0 < my)
    (Hy : specFloat_bounded (prec:=prec) (emax:=emax) my ey = true) :
    let x := SF2R 2 (StandardFloat.S754_finite sx mx ex)
    let y := SF2R 2 (StandardFloat.S754_finite sy my ey)
    let z := binary_round_aux (prec:=prec) (emax:=emax) mode
      (Bool.xor sx sy) ((mx * my : Nat) : Int) (ex + ey)
      FloatSpec.Calc.Bracket.Location.loc_Exact
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      if FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) (x * y)|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        SF2R 2 z =
            FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) (x * y) ∧
          is_finite_SF z = true ∧ sign_SF z = Bool.xor sx sy
      else
        z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode (Bool.xor sx sy) := by
  classical
  let x := SF2R 2 (StandardFloat.S754_finite sx mx ex)
  let y := SF2R 2 (StandardFloat.S754_finite sy my ey)
  have hmxy_pos : 0 < mx * my := Nat.mul_pos hmx_pos hmy_pos
  have hmx_int_pos : (0 : Int) < (mx : Int) := by exact_mod_cast hmx_pos
  have hmy_int_pos : (0 : Int) < (my : Int) := by exact_mod_cast hmy_pos
  have hxy_abs :
      |x * y| =
        F2R (FloatSpec.Core.Defs.FlocqFloat.mk ((mx * my : Nat) : Int) (ex + ey) :
          FloatSpec.Core.Defs.FlocqFloat 2) := by
    have h2ne : (2 : ℝ) ≠ 0 := by norm_num
    have hpow_add :
        (2 : ℝ) ^ (ex + ey) = (2 : ℝ) ^ ex * (2 : ℝ) ^ ey :=
      zpow_add₀ h2ne ex ey
    cases sx <;> cases sy <;>
      simp [x, y, SF2R, F2R, FloatSpec.Core.Defs.F2R, Int.cast_mul,
        hpow_add, mul_comm, mul_left_comm, mul_assoc]
  have hBx :
      FloatSpec.Calc.Bracket.inbetween_float 2 ((mx * my : Nat) : Int) (ex + ey) |x * y|
        FloatSpec.Calc.Bracket.Location.loc_Exact := by
    unfold FloatSpec.Calc.Bracket.inbetween_float
    exact FloatSpec.Calc.Bracket.inbetween.inbetween_Exact hxy_abs
  have hx_sign :
      FloatSpec.Core.Raux.Rlt_bool (x * y) 0 = Bool.xor sx sy := by
    cases sx <;> cases sy <;>
      simp [x, y, SF2R, F2R, FloatSpec.Core.Defs.F2R, Bool.xor,
        FloatSpec.Core.Raux.Rlt_bool] <;> positivity
  have hcanon_x :
      canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true :=
    canonical_mantissa_of_specFloat_bounded (prec:=prec) (emax:=emax) Hx
  have hcanon_y :
      canonical_mantissa (prec:=prec) (emax:=emax) my ey = true :=
    canonical_mantissa_of_specFloat_bounded (prec:=prec) (emax:=emax) Hy
  have hx_exp :
      ex = FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex) :=
    eq_of_beq hcanon_x
  have hy_exp :
      ey = FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Digits.Zdigits 2 (my : Int) + ey) :=
    eq_of_beq hcanon_y
  have hdigits_mult :
      FloatSpec.Core.Digits.Zdigits 2 ((mx : Int) * (my : Int)) ≤
        FloatSpec.Core.Digits.Zdigits 2 (mx : Int) +
          FloatSpec.Core.Digits.Zdigits 2 (my : Int) := by
    have htrip := FloatSpec.Core.Digits.Zdigits_mult
      (beta := 2) (h_beta := by norm_num) (x := (mx : Int)) (y := (my : Int))
      (hβ := by norm_num)
    rcases htrip trivial with ⟨dx, dy, hdx, hdy, hdxy⟩
    simpa [hdx, hdy] using hdxy
  have hdigits_mult_ge :
      FloatSpec.Core.Digits.Zdigits 2 (mx : Int) +
          FloatSpec.Core.Digits.Zdigits 2 (my : Int) - 1 ≤
        FloatSpec.Core.Digits.Zdigits 2 ((mx : Int) * (my : Int)) := by
    have htrip := FloatSpec.Core.Digits.Zdigits_mult_ge
      (beta := 2) (h_beta := by norm_num) (x := (mx : Int)) (y := (my : Int))
      (hβ := by norm_num)
    have hmx_ne : (mx : Int) ≠ 0 := ne_of_gt hmx_int_pos
    have hmy_ne : (my : Int) ≠ 0 := ne_of_gt hmy_int_pos
    rcases htrip ⟨hmx_ne, hmy_ne⟩ with ⟨dx, dy, hdx, hdy, hdxy⟩
    simpa [hdx, hdy] using hdxy
  have hdigits_x_pos : 0 < FloatSpec.Core.Digits.Zdigits 2 (mx : Int) := by
    have h := FloatSpec.Core.Digits.Zdigits_gt_0
      (beta := 2) (n := (mx : Int)) (by norm_num : (2 : Int) > 1)
    exact h (ne_of_gt hmx_int_pos)
  have hdigits_y_pos : 0 < FloatSpec.Core.Digits.Zdigits 2 (my : Int) := by
    have h := FloatSpec.Core.Digits.Zdigits_gt_0
      (beta := 2) (n := (my : Int)) (by norm_num : (2 : Int) > 1)
    exact h (ne_of_gt hmy_int_pos)
  have hEx :
      ex + ey ≤
        FLT_exp (3 - emax - prec) prec
          (FloatSpec.Core.Digits.Zdigits 2 ((mx * my : Nat) : Int) + (ex + ey)) := by
    have hcast_digits :
        FloatSpec.Core.Digits.Zdigits 2 ((mx * my : Nat) : Int) =
          FloatSpec.Core.Digits.Zdigits 2 ((mx : Int) * (my : Int)) := by
      norm_num
    rw [hcast_digits]
    unfold FLT_exp FloatSpec.Core.FLT.FLT_exp at hx_exp hy_exp ⊢
    have hprec_lt := (inferInstance : Prec_lt_emax prec emax).prec_lt_emax
    omega
  have haux := binary_round_aux_correct (prec:=prec) (emax:=emax)
    mode (x * y) (mx * my) (ex + ey)
    FloatSpec.Calc.Bracket.Location.loc_Exact hmxy_pos hBx hEx
  simpa [x, y, hx_sign] using haux

-- Coq: `binary_round_correct`.
theorem binary_round_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    [FloatSpec.Core.Generic_fmt.Monotone_exp
      (FLT_exp (3 - emax - prec) prec)]
    (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int)
    (hmx_pos : 0 < mx) :
    let z := binary_round (prec:=prec) (emax:=emax) mode sx mx ex
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      let x := SF2R 2 (StandardFloat.S754_finite sx mx ex)
      if FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        SF2R 2 z =
            FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x ∧
          is_finite_SF z = true ∧ sign_SF z = sx
      else
        z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode sx := by
  classical
  let aligned := shl_align_fexp (prec:=prec) (emax:=emax) mx ex
  let x := SF2R 2 (StandardFloat.S754_finite sx mx ex)
  have hmx_ne : mx ≠ 0 := Nat.ne_of_gt hmx_pos
  have halign_trip := shl_align_fexp_correct (prec:=prec) (emax:=emax) mx ex hmx_ne
  have halign :
      (let mx' := aligned.1
       let ex' := aligned.2
       F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx' : Int) ex' :
          FloatSpec.Core.Defs.FlocqFloat 2) =
        F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
          FloatSpec.Core.Defs.FlocqFloat 2) ∧
       ex' ≤ FLT_exp (3 - emax - prec) prec
          (FloatSpec.Core.Digits.Zdigits 2 (mx' : Int) + ex')) := by
    simpa [wp, PostCond.noThrow, pure, shl_align_fexp_check, aligned] using
      halign_trip hmx_ne
  have halign_value :
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk (aligned.1 : Int) aligned.2 :
          FloatSpec.Core.Defs.FlocqFloat 2) =
        F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
          FloatSpec.Core.Defs.FlocqFloat 2) := halign.1
  have hEx : aligned.2 ≤ FLT_exp (3 - emax - prec) prec
      (FloatSpec.Core.Digits.Zdigits 2 (aligned.1 : Int) + aligned.2) := halign.2
  have hmx_nonneg_int : (0 : Int) ≤ (mx : Int) := by exact_mod_cast Nat.zero_le mx
  have hmx_pos_int : (0 : Int) < (mx : Int) := by exact_mod_cast hmx_pos
  have hunsigned_nonneg :
      0 ≤ F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2) :=
    FloatSpec.Core.Float_prop.F2R_ge_0
      (beta := 2)
      (f := FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex)
      (by norm_num : (1 : Int) < 2) hmx_nonneg_int
  have hunsigned_pos :
      0 < F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2) :=
    FloatSpec.Core.Float_prop.F2R_gt_0
      (beta := 2)
      (f := FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex)
      (by norm_num : (1 : Int) < 2) hmx_pos_int
  have hx_abs :
      |x| = F2R (FloatSpec.Core.Defs.FlocqFloat.mk (aligned.1 : Int) aligned.2 :
          FloatSpec.Core.Defs.FlocqFloat 2) := by
    cases sx
    · simpa [x, SF2R, F2R, FloatSpec.Core.Defs.F2R,
        abs_of_nonneg hunsigned_nonneg] using halign_value.symm
    · simpa [x, SF2R, F2R, FloatSpec.Core.Defs.F2R,
        abs_of_nonneg hunsigned_nonneg] using halign_value.symm
  have hBx :
      FloatSpec.Calc.Bracket.inbetween_float 2 (aligned.1 : Int) aligned.2 |x|
        FloatSpec.Calc.Bracket.Location.loc_Exact := by
    unfold FloatSpec.Calc.Bracket.inbetween_float
    exact FloatSpec.Calc.Bracket.inbetween.inbetween_Exact hx_abs
  have hsx : FloatSpec.Core.Raux.Rlt_bool x 0 = sx := by
    cases sx
    · have hx_nonneg : 0 ≤ x := by
        simpa [x, SF2R, F2R, FloatSpec.Core.Defs.F2R] using le_of_lt hunsigned_pos
      simpa [FloatSpec.Core.Raux.Rlt_bool] using not_lt.mpr hx_nonneg
    · have hx_neg : x < 0 := by
        simpa [x, SF2R, F2R, FloatSpec.Core.Defs.F2R] using neg_neg_of_pos hunsigned_pos
      simp [FloatSpec.Core.Raux.Rlt_bool, hx_neg]
  have haligned_pos : 0 < aligned.1 := by
    by_contra hnot
    have hzero : aligned.1 = 0 := Nat.eq_zero_of_not_pos hnot
    have hzeroF : F2R (FloatSpec.Core.Defs.FlocqFloat.mk (aligned.1 : Int) aligned.2 :
        FloatSpec.Core.Defs.FlocqFloat 2) = 0 := by
      simp [hzero, F2R, FloatSpec.Core.Defs.F2R]
    have hzero_orig : F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2) = 0 := by
      rw [← halign_value, hzeroF]
    linarith
  have haux := binary_round_aux_correct (prec:=prec) (emax:=emax) mode x aligned.1 aligned.2
    FloatSpec.Calc.Bracket.Location.loc_Exact haligned_pos hBx hEx
  simpa [binary_round, aligned, x, hsx] using haux

namespace ExperimentalSingleNaNArithmetic

-- Coq: Bulp_correct
theorem Bulp_correct
    (x : BinarySingleNaNFloat prec emax) :
    BSN_is_finite (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) = true →
      B754_to_R (Bulp (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x)) =
          FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec)
            (B754_to_R (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x)) ∧
      BSN_is_finite (Bulp (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x)) = true ∧
      BSN_sign (Bulp (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x)) = false := by
  intro hfinite
  cases x with
  | B754_zero sx =>
      have hzero := FloatSpec.Core.FLT.ulp_FLT_0
        (prec := prec) (emin := 3 - emax - prec) (beta := 2)
      have hulp0 :
          FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec) 0 =
            (2 : ℝ) ^ (3 - emax - prec) := by
        simpa [FLT_exp, wp, PostCond.noThrow, pure] using hzero trivial
      simp [binarySingleNaNFloatToB754, Bulp, B754_to_R, BSN_is_finite,
        BSN_sign, F2R, FloatSpec.Core.Defs.F2R, hulp0]
  | B754_infinity sx =>
      simp [binarySingleNaNFloatToB754, BSN_is_finite] at hfinite
  | B754_nan =>
      simp [binarySingleNaNFloatToB754, BSN_is_finite] at hfinite
  | B754_finite sx mx ex hmx_pos hbounded =>
      have hcanon_bool : canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true :=
        canonical_mantissa_of_specFloat_bounded (prec:=prec) (emax:=emax) hbounded
      have hex_upper : ex ≤ emax - prec :=
        exponent_le_of_specFloat_bounded (prec:=prec) (emax:=emax) hbounded
      have heq :
          ex = FLT_exp (3 - emax - prec) prec
            (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex) :=
        eq_of_beq hcanon_bool
      have hemin_le_ex : 3 - emax - prec ≤ ex := by
        rw [heq]
        simp [FLT_exp, FloatSpec.Core.FLT.FLT_exp]
      have hfmt_bpow :
          FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp (3 - emax - prec) prec)
            ((2 : ℝ) ^ ex) := by
        have htrip := FloatSpec.Core.FLT.generic_format_FLT_bpow
          (prec := prec) (emin := 3 - emax - prec) (beta := 2) (e := ex)
        simpa [FLT_exp, wp, PostCond.noThrow, pure] using
          htrip ⟨by norm_num, hemin_le_ex⟩
      have hround_eq :
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
              (rnd_of_mode RoundingMode.RTZ)
              (SF2R 2 (StandardFloat.S754_finite false 1 ex)) =
            (2 : ℝ) ^ ex := by
        have hrg := FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec)
          (rnd := rnd_of_mode RoundingMode.RTZ)
          (x := (2 : ℝ) ^ ex) (hβ := by norm_num) hfmt_bpow
        simpa [SF2R, F2R, FloatSpec.Core.Defs.F2R] using hrg
      have hex_lt_emax : ex < emax := by
        have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
        linarith
      have hbpow_lt : (2 : ℝ) ^ ex < FloatSpec.Core.Raux.bpow 2 emax := by
        have htrip := FloatSpec.Core.Raux.bpow_lt
          (beta := 2) (e1 := ex) (e2 := emax)
          (hβ := by norm_num) hex_lt_emax
        simpa [FloatSpec.Core.Raux.bpow_lt_check, FloatSpec.Core.Raux.bpow,
          wp, PostCond.noThrow, Id.run, pure] using htrip trivial
      have hover_true :
          FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
              (rnd_of_mode RoundingMode.RTZ)
              (SF2R 2 (StandardFloat.S754_finite false 1 ex))|
            (FloatSpec.Core.Raux.bpow 2 emax) = true := by
        have hpow_nonneg : 0 ≤ (2 : ℝ) ^ ex :=
          le_of_lt (zpow_pos (by norm_num) ex)
        simp [FloatSpec.Core.Raux.Rlt_bool, hround_eq,
          abs_of_nonneg hpow_nonneg, hbpow_lt]
      have hround := binary_round_correct (prec:=prec) (emax:=emax)
        RoundingMode.RTZ false 1 ex (by norm_num : 0 < (1 : Nat))
      have hpayload := hround.2
      dsimp at hpayload
      rw [hover_true] at hpayload
      simp at hpayload
      have hsf_value :
          SF2R 2 (binary_round (prec:=prec) (emax:=emax)
            RoundingMode.RTZ false 1 ex) = (2 : ℝ) ^ ex := by
        exact hpayload.1.trans hround_eq
      have hsf_finite :
          is_finite_SF (binary_round (prec:=prec) (emax:=emax)
            RoundingMode.RTZ false 1 ex) = true :=
        hpayload.2.1
      have hsf_sign :
          sign_SF (binary_round (prec:=prec) (emax:=emax)
            RoundingMode.RTZ false 1 ex) = false :=
        hpayload.2.2
      have hB2R_SF2B :
          B754_to_R (SF2B (binary_round (prec:=prec) (emax:=emax)
              RoundingMode.RTZ false 1 ex)) =
            SF2R 2 (binary_round (prec:=prec) (emax:=emax)
              RoundingMode.RTZ false 1 ex) := by
        have htrip := B2R_SF2B
          (binary_round (prec:=prec) (emax:=emax) RoundingMode.RTZ false 1 ex)
        simpa [B2R_SF2B_check, wp, PostCond.noThrow, pure] using htrip trivial
      have hfinite_SF2B :
          BSN_is_finite (SF2B (binary_round (prec:=prec) (emax:=emax)
            RoundingMode.RTZ false 1 ex)) = true := by
        cases z : binary_round (prec:=prec) (emax:=emax) RoundingMode.RTZ false 1 ex <;>
          simp [z, SF2B, BSN_is_finite, is_finite_SF] at hsf_finite ⊢
      have hsign_SF2B :
          BSN_sign (SF2B (binary_round (prec:=prec) (emax:=emax)
            RoundingMode.RTZ false 1 ex)) = false := by
        cases z : binary_round (prec:=prec) (emax:=emax) RoundingMode.RTZ false 1 ex <;>
          simp [z, SF2B, BSN_sign, sign_SF] at hsf_sign ⊢ <;> exact hsf_sign
      have hmx_int_ne : (if sx then -((mx : Int)) else (mx : Int)) ≠ 0 := by
        have hm_ne_nat : mx ≠ 0 := Nat.pos_iff_ne_zero.mp hmx_pos
        cases sx <;> simp [hm_ne_nat]
      have hcanon_trip := canonical_canonical_mantissa_bsn
        (prec:=prec) (emax:=emax) sx mx ex hmx_pos hcanon_bool
      have hcanon :
          FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
            (FloatSpec.Core.Defs.FlocqFloat.mk
              (if sx then -((mx : Int)) else (mx : Int)) ex) := by
        simpa [wp, PostCond.noThrow, pure] using hcanon_trip trivial
      have hulp_trip := FloatSpec.Core.Ulp.ulp_canonical
        (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec)
        (m := if sx then -((mx : Int)) else (mx : Int)) (e := ex)
        hmx_int_ne (by norm_num : (1 : Int) < 2) hcanon
      have hulp_eq :
          FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec)
            (B754_to_R (B754.B754_finite sx mx ex)) = (2 : ℝ) ^ ex := by
        simpa [B754_to_R, F2R, FloatSpec.Core.Defs.F2R,
          wp, PostCond.noThrow, pure] using hulp_trip trivial
      constructor
      · calc
          B754_to_R (Bulp (prec:=prec) (emax:=emax)
              (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
                (BinarySingleNaNFloat.B754_finite (prec:=prec) (emax:=emax)
                  sx mx ex hmx_pos hbounded)))
              = B754_to_R (SF2B (binary_round (prec:=prec) (emax:=emax)
                  RoundingMode.RTZ false 1 ex)) := by
                    simp [binarySingleNaNFloatToB754, Bulp, binary_normalize]
          _ = SF2R 2 (binary_round (prec:=prec) (emax:=emax)
                RoundingMode.RTZ false 1 ex) := hB2R_SF2B
          _ = (2 : ℝ) ^ ex := hsf_value
          _ = FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec)
                (B754_to_R (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
                  (BinarySingleNaNFloat.B754_finite (prec:=prec) (emax:=emax)
                    sx mx ex hmx_pos hbounded))) := by
                    simpa [binarySingleNaNFloatToB754] using hulp_eq.symm
      · constructor
        · simpa [binarySingleNaNFloatToB754, Bulp, binary_normalize] using hfinite_SF2B
        · simpa [binarySingleNaNFloatToB754, Bulp, binary_normalize] using hsign_SF2B

theorem standardFloat_eq_of_valid_finite_sign_value
    (x y : StandardFloat)
    (hvalidX : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true)
    (hvalidY : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) y = true)
    (hfiniteX : is_finite_SF x = true)
    (hfiniteY : is_finite_SF y = true)
    (hvalue : SF2R 2 x = SF2R 2 y)
    (hsign : sign_SF x = sign_SF y) :
    x = y := by
  cases x with
  | S754_zero sx =>
      cases y with
      | S754_zero sy =>
          have : sx = sy := by simpa [sign_SF] using hsign
          simp [this]
      | S754_infinity sy => simp [is_finite_SF] at hfiniteY
      | S754_nan => simp [is_finite_SF] at hfiniteY
      | S754_finite sy my ey =>
          have hmy : 0 < my := by
            have hparts : 0 < my ∧
                specFloat_bounded (prec:=prec) (emax:=emax) my ey = true := by
              simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hvalidY
            exact hparts.1
          have hmyR : (0 : ℝ) < (my : ℝ) := Nat.cast_pos.mpr hmy
          have hpow : (0 : ℝ) < (2 : ℝ) ^ ey := zpow_pos (by norm_num) ey
          cases sy
          · have hprod : 0 < (my : ℝ) * (2 : ℝ) ^ ey := mul_pos hmyR hpow
            simp [SF2R, F2R, FloatSpec.Core.Defs.F2R] at hvalue
            exfalso
            rcases hvalue with hmyZero | hpowZero
            · omega
            · exact (ne_of_gt hpow) hpowZero
          · have hprod : -(my : ℝ) * (2 : ℝ) ^ ey < 0 :=
              mul_neg_of_neg_of_pos (neg_neg_of_pos hmyR) hpow
            simp [SF2R, F2R, FloatSpec.Core.Defs.F2R] at hvalue
            exfalso
            rcases hvalue with hmyZero | hpowZero
            · omega
            · exact (ne_of_gt hpow) hpowZero
  | S754_infinity sx => simp [is_finite_SF] at hfiniteX
  | S754_nan => simp [is_finite_SF] at hfiniteX
  | S754_finite sx mx ex =>
      cases y with
      | S754_zero sy =>
          have hmx : 0 < mx := by
            have hparts : 0 < mx ∧
                specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true := by
              simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hvalidX
            exact hparts.1
          have hmxR : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hmx
          have hpow : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) ex
          cases sx
          · have hprod : 0 < (mx : ℝ) * (2 : ℝ) ^ ex := mul_pos hmxR hpow
            simp [SF2R, F2R, FloatSpec.Core.Defs.F2R] at hvalue
            exfalso
            rcases hvalue with hmxZero | hpowZero
            · omega
            · exact (ne_of_gt hpow) hpowZero
          · have hprod : -(mx : ℝ) * (2 : ℝ) ^ ex < 0 :=
              mul_neg_of_neg_of_pos (neg_neg_of_pos hmxR) hpow
            simp [SF2R, F2R, FloatSpec.Core.Defs.F2R] at hvalue
            exfalso
            rcases hvalue with hmxZero | hpowZero
            · omega
            · exact (ne_of_gt hpow) hpowZero
      | S754_infinity sy => simp [is_finite_SF] at hfiniteY
      | S754_nan => simp [is_finite_SF] at hfiniteY
      | S754_finite sy my ey =>
          have hxParts : 0 < mx ∧
              specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true := by
            simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hvalidX
          have hyParts : 0 < my ∧
              specFloat_bounded (prec:=prec) (emax:=emax) my ey = true := by
            simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hvalidY
          have hcanonXTrip := canonical_bounded_of_specFloat_bounded
            (prec:=prec) (emax:=emax) sx mx ex hxParts.1 hxParts.2
          have hcanonYTrip := canonical_bounded_of_specFloat_bounded
            (prec:=prec) (emax:=emax) sy my ey hyParts.1 hyParts.2
          have hcanonX : canonical_FF (prec:=prec) (emax:=emax)
              (SF2FF (StandardFloat.S754_finite sx mx ex)) := by
            simpa [canonical_FF, FF_to_FlocqFloat, SF2FF, wp, PostCond.noThrow, pure]
              using hcanonXTrip trivial
          have hcanonY : canonical_FF (prec:=prec) (emax:=emax)
              (SF2FF (StandardFloat.S754_finite sy my ey)) := by
            simpa [canonical_FF, FF_to_FlocqFloat, SF2FF, wp, PostCond.noThrow, pure]
              using hcanonYTrip trivial
          let bx := FF2B (prec:=prec) (emax:=emax)
            (SF2FF (StandardFloat.S754_finite sx mx ex))
          let byFloat := FF2B (prec:=prec) (emax:=emax)
            (SF2FF (StandardFloat.S754_finite sy my ey))
          have hbxy : bx = byFloat := B2R_Bsign_inj_compat bx byFloat
            (by rfl) (by rfl)
            (by simpa [valid_FF, bx, FF2B, SF2FF] using hxParts.1)
            (by simpa [valid_FF, byFloat, FF2B, SF2FF] using hyParts.1)
            (by simpa [bx, FF2B, SF2FF] using hcanonX)
            (by simpa [byFloat, FF2B, SF2FF] using hcanonY)
            (by simpa [bx, byFloat, B2R, SF2R, FF2R, F2R,
                FloatSpec.Core.Defs.F2R, FF2B, SF2FF] using hvalue)
            (by simpa [bx, byFloat, Bsign, sign_SF, sign_FF, FF2B, SF2FF] using hsign)
          have hff := congrArg (fun z => B2FF (prec:=prec) (emax:=emax) z) hbxy
          have hstd := congrArg FF2SF hff
          calc
            StandardFloat.S754_finite sx mx ex =
                FF2SF (SF2FF (StandardFloat.S754_finite sx mx ex)) := by
                  symm
                  exact FF2SF_SF2FF _
            _ = FF2SF (SF2FF (StandardFloat.S754_finite sy my ey)) := by
                  simpa [bx, byFloat, B2FF_FF2B_compat] using hstd
            _ = StandardFloat.S754_finite sy my ey := FF2SF_SF2FF _

private theorem B754_eq_of_valid_finite_sign_value
    (x y : B754)
    (hvalidX : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
      (B2SF_BSN x) = true)
    (hvalidY : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
      (B2SF_BSN y) = true)
    (hfiniteX : BSN_is_finite x = true)
    (hfiniteY : BSN_is_finite y = true)
    (hvalue : B754_to_R x = B754_to_R y)
    (hsign : BSN_sign x = BSN_sign y) :
    x = y := by
  have hxnan : BSN_is_nan x = false := by
    cases x <;> simp_all [BSN_is_nan, BSN_is_finite]
  have hynan : BSN_is_nan y = false := by
    cases y <;> simp_all [BSN_is_nan, BSN_is_finite]
  apply B2SF_inj x y hxnan hynan
  apply standardFloat_eq_of_valid_finite_sign_value (prec:=prec) (emax:=emax)
  · exact hvalidX
  · exact hvalidY
  · cases x <;> simpa [B2SF_BSN, is_finite_SF, BSN_is_finite] using hfiniteX
  · cases y <;> simpa [B2SF_BSN, is_finite_SF, BSN_is_finite] using hfiniteY
  · cases x <;> cases y <;>
      simpa [B2SF_BSN, SF2R, B754_to_R] using hvalue
  · cases x <;> cases y <;>
      simpa [B2SF_BSN, sign_SF, BSN_sign] using hsign

theorem binary_round_one_payload
    (mode : RoundingMode) (e : Int)
    (hemin : 3 - emax - prec ≤ e) (hemax : e < emax) :
    let z := binary_round (prec:=prec) (emax:=emax) mode false 1 e
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      SF2R 2 z = FloatSpec.Core.Raux.bpow 2 e ∧
      is_finite_SF z = true ∧ sign_SF z = false := by
  let z := binary_round (prec:=prec) (emax:=emax) mode false 1 e
  have hround := binary_round_correct (prec:=prec) (emax:=emax)
    mode false 1 e (by norm_num : 0 < (1 : Nat))
  have hformat :
      FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp (3 - emax - prec) prec)
        (FloatSpec.Core.Raux.bpow 2 e) := by
    change FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec) ((2 : ℝ) ^ e)
    have htrip := FloatSpec.Core.FLT.generic_format_FLT_bpow
      (prec:=prec) (emin:=3 - emax - prec) (beta:=2) (e:=e)
    simpa [FLT_exp, wp, PostCond.noThrow, pure] using
      htrip ⟨by norm_num, hemin⟩
  have hroundEq :
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
          (rnd_of_mode mode)
          (SF2R 2 (StandardFloat.S754_finite false 1 e)) =
        FloatSpec.Core.Raux.bpow 2 e := by
    have hgeneric := FloatSpec.Core.Generic_fmt.roundR_generic
      (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
      (rnd:=rnd_of_mode mode) (x:=FloatSpec.Core.Raux.bpow 2 e)
      (hβ:=by norm_num) hformat
    simpa [SF2R, F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Raux.bpow] using hgeneric
  have hlt : FloatSpec.Core.Raux.bpow 2 e < FloatSpec.Core.Raux.bpow 2 emax := by
    have htrip := FloatSpec.Core.Raux.bpow_lt
      (beta:=2) (e1:=e) (e2:=emax) (hβ:=by norm_num) hemax
    have hp := htrip trivial
    simpa [FloatSpec.Core.Raux.bpow_lt_check, FloatSpec.Core.Raux.bpow,
      wp, PostCond.noThrow, pure] using hp
  have hcond :
      FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
            (rnd_of_mode mode)
            (SF2R 2 (StandardFloat.S754_finite false 1 e))|
          (FloatSpec.Core.Raux.bpow 2 emax) = true := by
    have hnonneg : 0 ≤ FloatSpec.Core.Raux.bpow 2 e := by
      exact le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e)
    simp [FloatSpec.Core.Raux.Rlt_bool, hroundEq, abs_of_nonneg hnonneg, hlt]
  have hvalid :
      validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true := by
    simpa [z] using hround.1
  have hpayload := hround.2
  dsimp at hpayload
  rw [hcond] at hpayload
  refine ⟨hvalid, ?_⟩
  simpa [z, hroundEq] using hpayload

private theorem binary_round_one_mode_independent
    (mode₁ mode₂ : RoundingMode) (e : Int)
    (hemin : 3 - emax - prec ≤ e) (hemax : e < emax) :
    binary_round (prec:=prec) (emax:=emax) mode₁ false 1 e =
      binary_round (prec:=prec) (emax:=emax) mode₂ false 1 e := by
  have h₁ := binary_round_one_payload (prec:=prec) (emax:=emax)
    mode₁ e hemin hemax
  have h₂ := binary_round_one_payload (prec:=prec) (emax:=emax)
    mode₂ e hemin hemax
  exact standardFloat_eq_of_valid_finite_sign_value (prec:=prec) (emax:=emax)
    (binary_round (prec:=prec) (emax:=emax) mode₁ false 1 e)
    (binary_round (prec:=prec) (emax:=emax) mode₂ false 1 e)
    h₁.1 h₂.1 h₁.2.2.1 h₂.2.2.1
    (h₁.2.1.trans h₂.2.1.symm) (h₁.2.2.2.trans h₂.2.2.2.symm)

omit [Prec_lt_emax prec emax] in
private theorem Bfrexp_fexp_eq_of_finite
    (hmax : 2 < emax) (sx : Bool) (mx : Nat) (ex : Int)
    (hmx : 0 < mx)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true) :
    FLT_exp (3 - emax - prec) prec
        (Bfrexp_bsn (prec:=prec) (emax:=emax)
          (B754.B754_finite sx mx ex)).2 = ex := by
  have hfirst : FloatSpec.Core.Zaux.Zlt_bool (-prec) (3 - emax - prec) = false := by
    simp [FloatSpec.Core.Zaux.Zlt_bool]
    omega
  have hdigitTrip := FloatSpec.Core.Digits.Zpos_digits2_pos mx
  have hdigit :
      FloatSpec.Core.Digits.Zdigits 2 (mx : Int) =
        FloatSpec.Core.Digits.digits2_pos mx :=
    (hdigitTrip hmx).symm
  have hcanon := canonical_mantissa_of_specFloat_bounded
    (prec:=prec) (emax:=emax) hbounded
  have hcanonEq :
      ex = FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex) :=
    eq_of_beq hcanon
  have hemin : 3 - emax - prec ≤ ex := by
    unfold FLT_exp FloatSpec.Core.FLT.FLT_exp at hcanonEq
    have hle := le_max_right
      (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex - prec)
      (3 - emax - prec)
    omega
  by_cases hprecDigits : prec ≤ FloatSpec.Core.Digits.digits2_pos mx
  · simp [Bfrexp_bsn, Ffrexp_core_binary, hfirst, hprecDigits,
      FLT_exp, FloatSpec.Core.FLT.FLT_exp, hemin]
  · simp only [Bfrexp_bsn, Ffrexp_core_binary, hfirst, Bool.false_eq_true,
      ↓reduceIte, hprecDigits, Prod.snd]
    have harg :
        ex + prec - (prec - FloatSpec.Core.Digits.digits2_pos mx) =
          FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex := by
      rw [hdigit]
      ring
    rw [harg]
    exact hcanonEq.symm

omit [Prec_lt_emax prec emax] in
private theorem Bfrexp_exp_eq_mag_of_finite
    (hmax : 2 < emax) (sx : Bool) (mx : Nat) (ex : Int)
    (hmx : 0 < mx)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true) :
    (Bfrexp_bsn (prec:=prec) (emax:=emax)
      (B754.B754_finite sx mx ex)).2 =
      FloatSpec.Core.Raux.mag 2
        (B754_to_R (B754.B754_finite sx mx ex)) := by
  have hfirst : FloatSpec.Core.Zaux.Zlt_bool (-prec) (3 - emax - prec) = false := by
    simp [FloatSpec.Core.Zaux.Zlt_bool]
    omega
  have hdigitTrip := FloatSpec.Core.Digits.Zpos_digits2_pos mx
  have hdigit :
      FloatSpec.Core.Digits.Zdigits 2 (mx : Int) =
        FloatSpec.Core.Digits.digits2_pos mx :=
    (hdigitTrip hmx).symm
  have hdigitLe : FloatSpec.Core.Digits.Zdigits 2 (mx : Int) ≤ prec :=
    Zdigits_le_prec_of_specFloat_bounded (prec:=prec) (emax:=emax) mx ex hbounded
  have hmxInt : (mx : Int) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hmx)
  have hsignedInt : (if sx then -(mx : Int) else (mx : Int)) ≠ 0 := by
    cases sx <;> simp <;> omega
  have hmagSigned := FloatSpec.Core.Float_prop.Raux_mag_F2R_Zdigits
    (beta:=2) (m:=if sx then -(mx : Int) else (mx : Int)) (e:=ex)
    (by norm_num : (1 : Int) < 2) hsignedInt
  have hsignDigitsTrip := FloatSpec.Core.Digits.Zdigits_cond_Zopp
    (beta:=2) (b:=sx) (n:=(mx : Int))
  have hsignDigits :
      FloatSpec.Core.Digits.Zdigits 2 (if sx then -(mx : Int) else (mx : Int)) =
        FloatSpec.Core.Digits.Zdigits 2 (mx : Int) := by
    simpa [wp, PostCond.noThrow, pure] using hsignDigitsTrip trivial
  have hmag :
      FloatSpec.Core.Raux.mag 2
          (B754_to_R (B754.B754_finite sx mx ex)) =
        FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex := by
    simpa [B754_to_R, F2R, FloatSpec.Core.Defs.F2R, hsignDigits] using hmagSigned
  by_cases hprecDigits : prec ≤ FloatSpec.Core.Digits.digits2_pos mx
  · have hdigitEq : FloatSpec.Core.Digits.digits2_pos mx = prec := by
      rw [hdigit] at hdigitLe
      exact le_antisymm hdigitLe hprecDigits
    simp [Bfrexp_bsn, Ffrexp_core_binary, hfirst, hprecDigits, hmag, hdigit,
      hdigitEq]
    ring
  · simp [Bfrexp_bsn, Ffrexp_core_binary, hfirst, hprecDigits, hmag, hdigit]
    ring

-- Coq `BinarySingleNaN.v:Bfrexp_correct_aux`.  Unlike the legacy payload
-- adapter above, this theorem runs `Ffrexp_core_binary` and derives every
-- postcondition from the finite constructor evidence.
omit [Prec_lt_emax prec emax] in
theorem Bfrexp_correct_aux
    (sx : Bool) (mx : Nat) (ex : Int) (hmx : 0 < mx)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true) :
    let x := SF2R 2 (StandardFloat.S754_finite sx mx ex)
    let z := (Ffrexp_core_binary (prec:=prec) (emax:=emax) sx mx ex).1
    let e := (Ffrexp_core_binary (prec:=prec) (emax:=emax) sx mx ex).2
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      (2 < emax → (1 / 2 : ℝ) ≤ |SF2R 2 z| ∧ |SF2R 2 z| < 1) ∧
      x = SF2R 2 z * FloatSpec.Core.Raux.bpow 2 e := by
  dsimp only
  let core := Ffrexp_core_binary (prec:=prec) (emax:=emax) sx mx ex
  let x := SF2R 2 (StandardFloat.S754_finite sx mx ex)
  let z := core.1
  let e := core.2
  have hxne : x ≠ 0 := by
    unfold x SF2R F2R FloatSpec.Core.Defs.F2R
    apply mul_ne_zero
    · cases sx <;> simp [Nat.ne_of_gt hmx]
    · exact zpow_ne_zero ex (by norm_num)
  have hdigitTrip := FloatSpec.Core.Digits.Zpos_digits2_pos mx
  have hdigit :
      FloatSpec.Core.Digits.Zdigits 2 (mx : Int) =
        FloatSpec.Core.Digits.digits2_pos mx :=
    (hdigitTrip hmx).symm
  have hdigitLe : FloatSpec.Core.Digits.Zdigits 2 (mx : Int) ≤ prec :=
    Zdigits_le_prec_of_specFloat_bounded
      (prec:=prec) (emax:=emax) mx ex hbounded
  have hvalidDecomp :
      validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
        x = SF2R 2 z * FloatSpec.Core.Raux.bpow 2 e := by
    by_cases hfirst :
        FloatSpec.Core.Zaux.Zlt_bool (-prec) (3 - emax - prec) = true
    · have hcore : core = (StandardFloat.S754_finite sx mx ex, 0) := by
        simp [core, Ffrexp_core_binary, hfirst]
      constructor
      · simp [z, hcore, validBinarySingleNaNStandardFloat, hmx, hbounded]
      · simp [x, z, e, hcore, FloatSpec.Core.Raux.bpow]
    · have hemin : 3 - emax - prec ≤ -prec := by
        simp [FloatSpec.Core.Zaux.Zlt_bool] at hfirst
        omega
      by_cases hprecDigits : prec ≤ FloatSpec.Core.Digits.digits2_pos mx
      · have hdigitEq : FloatSpec.Core.Digits.digits2_pos mx = prec := by
          rw [hdigit] at hdigitLe
          exact le_antisymm hdigitLe hprecDigits
        have hcanon : canonical_mantissa (prec:=prec) (emax:=emax) mx (-prec) = true := by
          unfold canonical_mantissa
          apply beq_iff_eq.mpr
          rw [hdigit, hdigitEq]
          unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
          rw [max_eq_left]
          · ring
          · simpa using hemin
        have hupper : -prec ≤ emax - prec := by omega
        have hcore : core =
            (StandardFloat.S754_finite sx mx (-prec), ex + prec) := by
          simp [core, Ffrexp_core_binary, hfirst, hprecDigits]
        constructor
        · simp [z, hcore, validBinarySingleNaNStandardFloat,
            specFloat_bounded, hmx, hcanon, hupper]
        · have h2ne : (2 : ℝ) ≠ 0 := by norm_num
          simp only [x, z, e, hcore, SF2R, F2R, FloatSpec.Core.Defs.F2R,
            FloatSpec.Core.Raux.bpow]
          norm_num only [Int.cast_ofNat]
          have hpowEq : (2 : ℝ) ^ ex =
              (2 : ℝ) ^ (-prec) * (2 : ℝ) ^ (ex + prec) := by
            rw [← zpow_add₀ h2ne]
            congr 1
            ring
          rw [hpowEq, mul_assoc]
      · have hdigitLt :
            FloatSpec.Core.Digits.digits2_pos mx < prec := by
          omega
        let d := prec - FloatSpec.Core.Digits.digits2_pos mx
        have hdPos : 0 < d := by simp [d]; omega
        have hdNonneg : 0 ≤ d := le_of_lt hdPos
        have hdCast : (d.toNat : Int) = d := Int.toNat_of_nonneg hdNonneg
        have hpowCast :
            (((2 : Nat) ^ d.toNat : Nat) : Int) = (2 : Int) ^ d.toNat := by
          norm_num
        have hmulCast :
            ((mx * 2 ^ d.toNat : Nat) : Int) =
              (mx : Int) * (2 : Int) ^ d.toNat := by
          norm_num
        have hmxIntNe : (mx : Int) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt hmx)
        have hdigitShift :
            FloatSpec.Core.Digits.Zdigits 2
                ((mx * 2 ^ d.toNat : Nat) : Int) = prec := by
          have htrip := FloatSpec.Core.Digits.Zdigits_mult_Zpower
            (beta:=2) (n:=(mx : Int)) (k:=d) (by norm_num)
          simp only [wp, PostCond.noThrow, pure] at htrip
          rcases htrip ⟨hmxIntNe, hdNonneg⟩ with ⟨dn, hdn, hshift⟩
          rw [hmulCast]
          have hpowNatAbs : d.natAbs = d.toNat := by
            apply Nat.cast_injective (R:=Int)
            rw [Int.natAbs_of_nonneg hdNonneg, Int.toNat_of_nonneg hdNonneg]
          have hshift' :
              FloatSpec.Core.Digits.Zdigits 2
                  ((mx : Int) * (2 : Int) ^ d.natAbs) = dn + d := by
            simpa only [Id.run] using hshift
          rw [← hpowNatAbs, hshift', ← hdn, hdigit]
          simp [d]
        have hcanon : canonical_mantissa (prec:=prec) (emax:=emax)
            (mx * 2 ^ d.toNat) (-prec) = true := by
          unfold canonical_mantissa
          apply beq_iff_eq.mpr
          rw [hdigitShift]
          unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
          rw [max_eq_left]
          · ring
          · simpa using hemin
        have hupper : -prec ≤ emax - prec := by omega
        have hcore : core =
            (StandardFloat.S754_finite sx (mx * 2 ^ d.toNat) (-prec),
              ex + prec - d) := by
          simp [core, Ffrexp_core_binary, hfirst, hprecDigits, d]
        have hshiftPos : 0 < mx * 2 ^ d.toNat :=
          Nat.mul_pos hmx (pow_pos (by norm_num) _)
        constructor
        · simp [z, hcore, validBinarySingleNaNStandardFloat,
            specFloat_bounded, hshiftPos, hcanon, hupper]
        · have h2ne : (2 : ℝ) ≠ 0 := by norm_num
          have hpowReal : (((2 : Nat) ^ d.toNat : Nat) : ℝ) = (2 : ℝ) ^ d := by
            rw [Nat.cast_pow, ← zpow_natCast]
            congr 1
          have hpowEq : (2 : ℝ) ^ ex =
              (2 : ℝ) ^ d * (2 : ℝ) ^ (-prec) *
                (2 : ℝ) ^ (ex + prec - d) := by
            rw [← zpow_add₀ h2ne, ← zpow_add₀ h2ne]
            congr 1
            ring
          simp only [x, z, e, hcore, SF2R, F2R, FloatSpec.Core.Defs.F2R,
            FloatSpec.Core.Raux.bpow, Nat.cast_mul]
          cases sx with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_natCast,
                Int.cast_mul]
              norm_num only [Int.cast_ofNat]
              rw [hpowReal, hpowEq]
              ring
          | true =>
              simp only [↓reduceIte, Int.cast_neg, Int.cast_natCast, Int.cast_mul]
              norm_num only [Int.cast_ofNat]
              rw [hpowReal, hpowEq]
              ring
  refine ⟨hvalidDecomp.1, ?_, hvalidDecomp.2⟩
  intro hmax
  have heqMag : e = FloatSpec.Core.Raux.mag 2 x := by
    simpa [e, core, x, Bfrexp_bsn, B754_to_R, SF2R] using
      Bfrexp_exp_eq_mag_of_finite (prec:=prec) (emax:=emax)
        hmax sx mx ex hmx hbounded
  have hzne : SF2R 2 z ≠ 0 := by
    intro hz
    apply hxne
    rw [hvalidDecomp.2, hz, zero_mul]
  have hmagMul := FloatSpec.Core.Raux.mag_mult_bpow
    2 (SF2R 2 z) e (by norm_num) hzne
  have hmagZero : FloatSpec.Core.Raux.mag 2 (SF2R 2 z) = 0 := by
    have hmagEq : FloatSpec.Core.Raux.mag 2 x =
        FloatSpec.Core.Raux.mag 2 (SF2R 2 z) + e := by
      rw [hvalidDecomp.2]
      simpa [FloatSpec.Core.Raux.bpow] using hmagMul
    rw [← heqMag] at hmagEq
    omega
  have hlow := FloatSpec.Core.Raux.mag_lower_bound
    2 (SF2R 2 z) (by norm_num) hzne
  have hupp := FloatSpec.Core.Raux.mag_upper_bound
    2 (SF2R 2 z) (by norm_num) hzne
  constructor
  · have := hlow trivial
    rw [hmagZero] at this
    norm_num [FloatSpec.Core.Raux.bpow] at this ⊢
    exact this
  · have := hupp trivial
    rw [hmagZero] at this
    norm_num [FloatSpec.Core.Raux.bpow] at this ⊢
    exact this

-- Coq: Bulp'_correct
theorem Bulp'_correct
    (hmax : 2 < emax) (x : BinarySingleNaNFloat prec emax)
    (hfinite :
      BSN_is_finite (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) = true) :
    Bulp' (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) =
      Bulp (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) := by
  cases x with
  | B754_zero sx =>
      have hsentinel :
          FLT_exp (3 - emax - prec) prec (-2 * emax - prec) =
            3 - emax - prec := by
        unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
        apply max_eq_right
        have hprec := (inferInstance : Prec_gt_0 prec).pos
        omega
      have heminMax : 3 - emax - prec < emax := by
        have hprec := (inferInstance : Prec_gt_0 prec).pos
        omega
      have hrounded := binary_round_one_payload (prec:=prec) (emax:=emax)
        RoundingMode.RNE (3 - emax - prec) (le_refl _) heminMax
      have hdirectValid :
          validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
            (StandardFloat.S754_finite false 1 (3 - emax - prec)) = true := by
        have hcanonDirect :
            canonical_mantissa (prec:=prec) (emax:=emax) 1
              (3 - emax - prec) = true := by
          have hdigitTrip := FloatSpec.Core.Digits.Zpos_digits2_pos 1
          have hdigitOne : FloatSpec.Core.Digits.Zdigits 2 (1 : Int) = 1 := by
            simpa [FloatSpec.Core.Digits.digits2_pos,
              FloatSpec.Core.Digits.digits2_Pnat,
              FloatSpec.Core.Digits.digits2_Pnat_bitlength_payload] using
              (hdigitTrip (by norm_num : (0 : Nat) < 1)).symm
          unfold canonical_mantissa
          simp only [beq_iff_eq]
          change 3 - emax - prec =
            FLT_exp (3 - emax - prec) prec
              (FloatSpec.Core.Digits.Zdigits 2 (1 : Int) + (3 - emax - prec))
          rw [hdigitOne]
          unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
          have hprec := (inferInstance : Prec_gt_0 prec).pos
          symm
          apply max_eq_right
          omega
        have hupper : 3 - emax - prec ≤ emax - prec := by omega
        simp [validBinarySingleNaNStandardFloat, specFloat_bounded,
          hcanonDirect, hupper]
      have hstandard :
          binary_round (prec:=prec) (emax:=emax) RoundingMode.RNE false 1
              (3 - emax - prec) =
            StandardFloat.S754_finite false 1 (3 - emax - prec) := by
        apply standardFloat_eq_of_valid_finite_sign_value (prec:=prec) (emax:=emax)
        · exact hrounded.1
        · exact hdirectValid
        · exact hrounded.2.2.1
        · rfl
        · simpa [SF2R, F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Raux.bpow]
            using hrounded.2.1
        · exact hrounded.2.2.2
      have herased := congrArg SF2B hstandard
      change Bldexp (prec:=prec) (emax:=emax) RoundingMode.RNE Bone
          (FLT_exp (3 - emax - prec) prec (-2 * emax - prec)) =
        B754.B754_finite false 1 (3 - emax - prec)
      rw [hsentinel]
      simpa only [Bldexp, Bone, SF2B, zero_add] using herased
  | B754_infinity sx =>
      simp [binarySingleNaNFloatToB754, BSN_is_finite] at hfinite
  | B754_nan =>
      simp [binarySingleNaNFloatToB754, BSN_is_finite] at hfinite
  | B754_finite sx mx ex hmx hbounded =>
      have hfrexp := Bfrexp_fexp_eq_of_finite (prec:=prec) (emax:=emax)
        hmax sx mx ex hmx hbounded
      have hemin : 3 - emax - prec ≤ ex := by
        have hcanon := canonical_mantissa_of_specFloat_bounded
          (prec:=prec) (emax:=emax) hbounded
        have heq : ex = FLT_exp (3 - emax - prec) prec
            (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex) :=
          eq_of_beq hcanon
        unfold FLT_exp FloatSpec.Core.FLT.FLT_exp at heq
        have hle := le_max_right
          (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex - prec)
          (3 - emax - prec)
        omega
      have hemax : ex < emax := by
        have hupper := exponent_le_of_specFloat_bounded
          (prec:=prec) (emax:=emax) hbounded
        have hprec := (inferInstance : Prec_gt_0 prec).pos
        omega
      have hmode := binary_round_one_mode_independent (prec:=prec) (emax:=emax)
        RoundingMode.RNE RoundingMode.RTZ ex hemin hemax
      have herased := congrArg SF2B hmode
      change Bldexp (prec:=prec) (emax:=emax) RoundingMode.RNE Bone
          (FLT_exp (3 - emax - prec) prec
            (Bfrexp_bsn (prec:=prec) (emax:=emax)
              (B754.B754_finite sx mx ex)).2) =
        binary_normalize (prec:=prec) (emax:=emax) RoundingMode.RTZ 1 ex false
      rw [hfrexp]
      norm_num [Bldexp, Bone, SF2B, binary_normalize] at herased ⊢
      exact herased

-- Coq: is_finite_strict_Bulp
theorem is_finite_strict_Bulp
    (x : BinarySingleNaNFloat prec emax) :
    BSN_is_finite_strict (Bulp (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x)) =
      BSN_is_finite (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) := by
  cases x with
  | B754_zero sx =>
      simp [binarySingleNaNFloatToB754, Bulp, BSN_is_finite_strict, BSN_is_finite]
  | B754_infinity sx =>
      simp [binarySingleNaNFloatToB754, Bulp, BSN_is_finite_strict, BSN_is_finite]
  | B754_nan =>
      simp [binarySingleNaNFloatToB754, Bulp, BSN_is_finite_strict, BSN_is_finite]
  | B754_finite sx mx ex hmx_pos hbounded =>
      let xfin : BinarySingleNaNFloat prec emax :=
        BinarySingleNaNFloat.B754_finite (prec:=prec) (emax:=emax)
          sx mx ex hmx_pos hbounded
      have hcorr := Bulp_correct (prec:=prec) (emax:=emax) xfin (by
        simp [xfin, binarySingleNaNFloatToB754, BSN_is_finite])
      have hx_ne :
          B754_to_R (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) xfin) ≠ 0 := by
        have hmx_int_ne : (if sx then -((mx : Int)) else (mx : Int)) ≠ 0 := by
          have hm_ne : (mx : Int) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hmx_pos)
          cases sx
          · simpa using hm_ne
          · simpa using neg_ne_zero.mpr hm_ne
        exact FloatSpec.Core.Float_prop.F2R_neq_0
          (beta := 2)
          (f := FloatSpec.Core.Defs.FlocqFloat.mk
            (if sx then -((mx : Int)) else (mx : Int)) ex)
          (by norm_num : (1 : Int) < 2) hmx_int_ne
      have hulp_ne :
          FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec)
            (B754_to_R (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) xfin)) ≠ 0 := by
        have htrip := FloatSpec.Core.Ulp.ulp_neq_0
          (beta := 2) (fexp := FLT_exp (3 - emax - prec) prec)
          (x := B754_to_R (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) xfin))
          hx_ne
        have hulp_eq :
            FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec)
              (B754_to_R (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) xfin)) =
              (2 : ℝ) ^
                (FloatSpec.Core.Generic_fmt.cexp 2 (FLT_exp (3 - emax - prec) prec)
                  (B754_to_R (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) xfin))) := by
          simpa [wp, PostCond.noThrow, pure] using htrip trivial
        rw [hulp_eq]
        exact ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
      have hbulp_ne :
          B754_to_R (Bulp (prec:=prec) (emax:=emax)
            (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) xfin)) ≠ 0 := by
        rw [hcorr.1]
        exact hulp_ne
      have hstrict_trip := is_finite_strict_B2R
        (Bulp (prec:=prec) (emax:=emax)
          (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) xfin))
        hbulp_ne
      have hstrict :
          BSN_is_finite_strict (Bulp (prec:=prec) (emax:=emax)
            (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) xfin)) = true := by
        simpa [is_finite_strict_B2R_check, wp, PostCond.noThrow, pure] using
          hstrict_trip trivial
      simpa [xfin, binarySingleNaNFloatToB754, BSN_is_finite] using hstrict

end ExperimentalSingleNaNArithmetic

namespace Binary

noncomputable def B2R {prec emax : Int} (x : binary_float prec emax) : ℝ :=
  match x with
  | binary_float.B754_finite s m e _ =>
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk
        (if s then -((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int)
         else ((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int)) e :
          FloatSpec.Core.Defs.FlocqFloat 2)
  | _ => 0

def is_finite {prec emax : Int} (x : binary_float prec emax) : Bool :=
  match x with
  | binary_float.B754_zero _ => true
  | binary_float.B754_finite _ _ _ _ => true
  | _ => false

def Bsign {prec emax : Int} (x : binary_float prec emax) : Bool :=
  match x with
  | binary_float.B754_zero s => s
  | binary_float.B754_infinity s => s
  | binary_float.B754_nan s _ _ => s
  | binary_float.B754_finite s _ _ _ => s

def is_nan {prec emax : Int} (x : binary_float prec emax) : Bool :=
  match x with
  | binary_float.B754_nan _ _ _ => true
  | _ => false

def B2SF {prec emax : Int} (x : binary_float prec emax) : StandardFloat :=
  binarySingleNaNFloatToStandardFloat (prec:=prec) (emax:=emax)
    (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x)

def B2FF {prec emax : Int} (x : binary_float prec emax) : FullFloat :=
  (binary_float.toBinary754 x).val

-- Exact source representation bridges.  `B2FF` above is the established
-- Nat-payload compatibility observer; `B2FF_exact` retains Coq's Positive
-- payload carrier.
abbrev B2BSN {prec emax : Int} (x : binary_float prec emax) :
    BinarySingleNaNFloat prec emax :=
  binaryFloatToBinarySingleNaNFloat x

abbrev FF2B {prec emax : Int} (x : full_float)
    (hx : valid_full_float_binary (prec:=prec) (emax:=emax) x = true) :
    binary_float prec emax :=
  fullFloatToBinaryFloat x hx

abbrev B2FF_exact {prec emax : Int} (x : binary_float prec emax) : full_float :=
  binaryFloatToFullFloat x

theorem B2FF_eq_exact_embedding {prec emax : Int} (x : binary_float prec emax) :
    B2FF x = full_float.toFullFloat (B2FF_exact x) := by
  cases x <;> rfl

theorem B2SF_B2BSN {prec emax : Int} (x : binary_float prec emax) :
    binarySingleNaNFloatToStandardFloat (B2BSN x) = B2SF x := rfl

theorem B2R_B2BSN {prec emax : Int} (x : binary_float prec emax) :
    B754_to_R (binarySingleNaNFloatToB754 (B2BSN x)) = B2R x := by
  cases x <;> simp [B2BSN, binaryFloatToBinarySingleNaNFloat,
    binarySingleNaNFloatToB754, B754_to_R, B2R, F2R,
    FloatSpec.Core.Defs.F2R]

theorem SF2R_B2BSN {prec emax : Int} (x : binary_float prec emax) :
    SF2R 2 (binarySingleNaNFloatToStandardFloat (B2BSN x)) = B2R x := by
  cases x <;> simp [B2BSN, binaryFloatToBinarySingleNaNFloat,
    binarySingleNaNFloatToStandardFloat, SF2R, B2R, F2R,
    FloatSpec.Core.Defs.F2R]

theorem is_finite_B2BSN {prec emax : Int} (x : binary_float prec emax) :
    BSN_is_finite (binarySingleNaNFloatToB754 (B2BSN x)) = is_finite x := by
  cases x <;> rfl

theorem B2R_eq_exact_full_float {prec emax : Int} (x : binary_float prec emax) :
    B2R x = full_float.toReal 2 (B2FF_exact x) := by
  cases x <;> rfl

theorem B2FF_FF2B {prec emax : Int} (x : full_float)
    (hx : valid_full_float_binary (prec:=prec) (emax:=emax) x = true) :
    B2FF_exact (FF2B x hx) = x :=
  binaryFloatToFullFloat_fullFloatToBinaryFloat x hx

theorem valid_binary_B2FF {prec emax : Int} (x : binary_float prec emax) :
    valid_full_float_binary (prec:=prec) (emax:=emax) (B2FF_exact x) = true :=
  valid_full_float_binary_binaryFloatToFullFloat x

theorem FF2B_B2FF_valid {prec emax : Int} (x : binary_float prec emax) :
    FF2B (B2FF_exact x) (valid_binary_B2FF x) = x :=
  fullFloatToBinaryFloat_binaryFloatToFullFloat x

theorem FF2B_B2FF {prec emax : Int} (x : binary_float prec emax)
    (hx : valid_full_float_binary (prec:=prec) (emax:=emax) (B2FF_exact x) = true) :
    FF2B (B2FF_exact x) hx = x := by
  cases x <;> simp [FF2B, B2FF_exact, fullFloatToBinaryFloat,
    binaryFloatToFullFloat]

theorem FF2R_B2FF {prec emax : Int} (x : binary_float prec emax) :
    full_float.toReal 2 (B2FF_exact x) = B2R x := by
  exact (B2R_eq_exact_full_float x).symm

theorem B2R_FF2B {prec emax : Int} (x : full_float)
    (hx : valid_full_float_binary (prec:=prec) (emax:=emax) x = true) :
    B2R (FF2B x hx) = full_float.toReal 2 x := by
  cases x <;> rfl

theorem B2SF_FF2B {prec emax : Int} (x : full_float)
    (hx : valid_full_float_binary (prec:=prec) (emax:=emax) x = true) :
    B2SF (FF2B x hx) = full_float.toStandardFloat x := by
  cases x <;> rfl

theorem FF2SF_B2FF {prec emax : Int} (x : binary_float prec emax) :
    full_float.toStandardFloat (B2FF_exact x) = B2SF x := by
  cases x <;> rfl

theorem Bsign_FF2B {prec emax : Int} (x : full_float)
    (hx : valid_full_float_binary (prec:=prec) (emax:=emax) x = true) :
    Bsign (FF2B x hx) = full_float.sign x := by
  cases x <;> rfl

theorem is_finite_FF2B {prec emax : Int} (x : full_float)
    (hx : valid_full_float_binary (prec:=prec) (emax:=emax) x = true) :
    is_finite (FF2B x hx) = full_float.isFinite x := by
  cases x <;> rfl

theorem is_finite_B2FF {prec emax : Int} (x : binary_float prec emax) :
    full_float.isFinite (B2FF_exact x) = is_finite x := by
  cases x <;> rfl

theorem is_nan_FF2B {prec emax : Int} (x : full_float)
    (hx : valid_full_float_binary (prec:=prec) (emax:=emax) x = true) :
    is_nan (FF2B x hx) = full_float.isNaN x := by
  cases x <;> rfl

theorem is_nan_B2FF {prec emax : Int} (x : binary_float prec emax) :
    full_float.isNaN (B2FF_exact x) = is_nan x := by
  cases x <;> rfl

theorem match_FF2B {prec emax : Int} {T : Type}
    (fz fi : Bool → T)
    (fn : Bool → FloatSpec.Core.Zaux.Positive → T)
    (ff : Bool → FloatSpec.Core.Zaux.Positive → Int → T)
    (x : full_float)
    (hx : valid_full_float_binary (prec:=prec) (emax:=emax) x = true) :
    (match FF2B x hx with
      | binary_float.B754_zero s => fz s
      | binary_float.B754_infinity s => fi s
      | binary_float.B754_nan s p _ => fn s p
      | binary_float.B754_finite s m e _ => ff s m e) =
    (match x with
      | full_float.F754_zero s => fz s
      | full_float.F754_infinity s => fi s
      | full_float.F754_nan s p => fn s p
      | full_float.F754_finite s m e => ff s m e) := by
  cases x <;> rfl

theorem B2FF_inj {prec emax : Int} (x y : binary_float prec emax)
    (hxy : B2FF_exact x = B2FF_exact y) : x = y := by
  cases x <;> cases y <;>
    simp_all [B2FF_exact, binaryFloatToFullFloat]

private theorem B2R_finite_ne_zero {prec emax : Int}
    (s : Bool) (m : FloatSpec.Core.Zaux.Positive) (e : Int)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true) :
    B2R (binary_float.B754_finite s m e hbounded) ≠ 0 := by
  have hm : (0 : Int) < (FloatSpec.Core.Zaux.positiveToNat m : Int) := by
    exact_mod_cast FloatSpec.Core.Zaux.positiveToNat_pos m
  cases s
  · exact ne_of_gt (FloatSpec.Core.Float_prop.F2R_gt_0
      (beta:=2) (f:=FloatSpec.Core.Defs.FlocqFloat.mk
        (FloatSpec.Core.Zaux.positiveToNat m : Int) e) (by norm_num) hm)
  · exact ne_of_lt (FloatSpec.Core.Float_prop.F2R_lt_0
      (beta:=2) (f:=FloatSpec.Core.Defs.FlocqFloat.mk
        (-(FloatSpec.Core.Zaux.positiveToNat m : Int)) e) (by norm_num)
          (neg_neg_of_pos hm))

theorem B2R_Bsign_inj {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x y : binary_float prec emax)
    (hx : is_finite x = true) (hy : is_finite y = true)
    (hR : B2R x = B2R y) (hs : Bsign x = Bsign y) : x = y := by
  cases x with
  | B754_zero sx =>
      cases y with
      | B754_zero sy => simpa [Bsign] using hs
      | B754_infinity sy => simp [is_finite] at hy
      | B754_nan sy p hp => simp [is_finite] at hy
      | B754_finite sy m e hb =>
          exact False.elim (B2R_finite_ne_zero sy m e hb hR.symm)
  | B754_infinity sx => simp [is_finite] at hx
  | B754_nan sx p hp => simp [is_finite] at hx
  | B754_finite sx m ex hbx =>
      cases y with
      | B754_zero sy =>
          exact False.elim (B2R_finite_ne_zero sx m ex hbx hR)
      | B754_infinity sy => simp [is_finite] at hy
      | B754_nan sy p hp => simp [is_finite] at hy
      | B754_finite sy n ey hby =>
          apply _root_.B2R_inj
          · rfl
          · rfl
          · simpa [B2R, binary_float.B2R] using hR

theorem canonical_canonical_mantissa {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (sx : Bool) (mx : FloatSpec.Core.Zaux.Positive) (ex : Int)
    (hcanon : canonical_mantissa (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mx) ex = true) :
    FloatSpec.Core.Generic_fmt.canonical 2
      (FLT_exp (3 - emax - prec) prec)
      (FloatSpec.Core.Defs.FlocqFloat.mk
        (if sx then -(FloatSpec.Core.Zaux.positiveToNat mx : Int)
         else (FloatSpec.Core.Zaux.positiveToNat mx : Int)) ex) := by
  have h := _root_.canonical_canonical_mantissa_compat
    (prec:=prec) (emax:=emax) sx (FloatSpec.Core.Zaux.positiveToNat mx) ex
    (FloatSpec.Core.Zaux.positiveToNat_pos mx) hcanon
  simpa [wp, PostCond.noThrow, pure] using h trivial

theorem generic_format_B2R {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) :
    FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec) (B2R x) := by
  cases x with
  | B754_zero s | B754_infinity s | B754_nan s p hp =>
      simpa [B2R] using FloatSpec.Core.Generic_fmt.generic_format_0_run
        (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
  | B754_finite s m e hb =>
      apply FloatSpec.Core.Generic_fmt.generic_format_canonical
      exact canonical_canonical_mantissa s m e
        (canonical_mantissa_of_specFloat_bounded hb)

theorem FLT_format_B2R {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) :
    FloatSpec.Core.FLT.FLT_format (prec:=prec) (emin:=3 - emax - prec)
      2 (B2R x) := by
  exact FloatSpec.Core.FLT.FLT_format_generic
    (prec := prec) (emin := 3 - emax - prec) 2 _ (generic_format_B2R x)

theorem bounded_le_emax_minus_prec {prec emax : Int}
    [Prec_gt_0 prec] (mx : FloatSpec.Core.Zaux.Positive) (ex : Int)
    (hbounded : bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mx) ex = true) :
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Zaux.positiveToNat mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2) ≤
      FloatSpec.Core.Raux.bpow 2 emax -
        FloatSpec.Core.Raux.bpow 2 (emax - prec) := by
  exact (_root_.bounded_le_emax_minus_prec
    (FloatSpec.Core.Zaux.positiveToNat mx) ex hbounded) trivial

theorem bounded_lt_emax {prec emax : Int}
    (mx : FloatSpec.Core.Zaux.Positive) (ex : Int)
    (hbounded : bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mx) ex = true) :
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Zaux.positiveToNat mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2) < FloatSpec.Core.Raux.bpow 2 emax := by
  exact (_root_.bounded_lt_emax
    (FloatSpec.Core.Zaux.positiveToNat mx) ex hbounded) trivial

theorem bounded_ge_emin {prec emax : Int}
    (mx : FloatSpec.Core.Zaux.Positive) (ex : Int)
    (hbounded : bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mx) ex = true) :
    FloatSpec.Core.Raux.bpow 2 (3 - emax - prec) ≤
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk
        (FloatSpec.Core.Zaux.positiveToNat mx : Int) ex :
          FloatSpec.Core.Defs.FlocqFloat 2) := by
  exact (_root_.bounded_ge_emin
    (FloatSpec.Core.Zaux.positiveToNat mx) ex hbounded
      (FloatSpec.Core.Zaux.positiveToNat_pos mx)) trivial

theorem abs_B2R_le_emax_minus_prec {prec emax : Int}
    [Prec_gt_0 prec] (x : binary_float prec emax) :
    |B2R x| ≤ FloatSpec.Core.Raux.bpow 2 emax -
      FloatSpec.Core.Raux.bpow 2 (emax - prec) := by
  change |binary_float.B2R x| ≤ FloatSpec.Core.Raux.bpow 2 emax -
    FloatSpec.Core.Raux.bpow 2 (emax - prec)
  exact (_root_.abs_B2R_le_emax_minus_prec x) trivial

theorem abs_B2R_lt_emax {prec emax : Int}
    [Prec_gt_0 prec] (x : binary_float prec emax) :
    |B2R x| < FloatSpec.Core.Raux.bpow 2 emax := by
  change |binary_float.B2R x| < FloatSpec.Core.Raux.bpow 2 emax
  exact (_root_.abs_B2R_lt_emax x) trivial

theorem abs_B2R_ge_emin {prec emax : Int}
    (x : binary_float prec emax)
    (hx : binary_float.is_finite_strict x = true) :
    FloatSpec.Core.Raux.bpow 2 (3 - emax - prec) ≤ |B2R x| := by
  cases x with
  | B754_zero s | B754_infinity s | B754_nan s p hp =>
      simp [binary_float.is_finite_strict] at hx
  | B754_finite s m e hb =>
      have h := bounded_ge_emin m e
        (range_bounded_of_specFloat_bounded
          (FloatSpec.Core.Zaux.positiveToNat m) e
          (FloatSpec.Core.Zaux.positiveToNat_pos m) hb)
      have hbpow_nonneg : 0 ≤ FloatSpec.Core.Raux.bpow 2 e :=
        le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e)
      cases s <;>
        simpa [B2R, F2R, FloatSpec.Core.Defs.F2R, abs_mul,
          abs_of_nonneg hbpow_nonneg] using h

theorem bounded_canonical_lt_emax {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mx : FloatSpec.Core.Zaux.Positive) (ex : Int)
    (hcanon : FloatSpec.Core.Generic_fmt.canonical 2
      (FLT_exp (3 - emax - prec) prec)
      (FloatSpec.Core.Defs.FlocqFloat.mk
        (FloatSpec.Core.Zaux.positiveToNat mx : Int) ex))
    (hlt : F2R (FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Zaux.positiveToNat mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2) < FloatSpec.Core.Raux.bpow 2 emax) :
    bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mx) ex = true := by
  have h := _root_.bounded_canonical_lt_emax
    (inferInstance : Prec_gt_0 prec).pos
    (inferInstance : Prec_lt_emax prec emax).prec_lt_emax
    (FloatSpec.Core.Zaux.positiveToNat mx) ex
    (FloatSpec.Core.Zaux.positiveToNat_pos mx) hcanon hlt
  exact h trivial

private theorem shl_align_fexp_fst_pos {prec emax : Int}
    (mx : FloatSpec.Core.Zaux.Positive) (ex : Int) :
    0 < (_root_.shl_align_fexp (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mx) ex).1 := by
  simp only [_root_.shl_align_fexp]
  unfold _root_.shl_align
  split
  · exact Nat.mul_pos (FloatSpec.Core.Zaux.positiveToNat_pos mx) (by positivity)
  · exact FloatSpec.Core.Zaux.positiveToNat_pos mx

def shl_align_fexp {prec emax : Int}
    (mx : FloatSpec.Core.Zaux.Positive) (ex : Int) :
    FloatSpec.Core.Zaux.Positive × Int :=
  let r := _root_.shl_align_fexp (prec:=prec) (emax:=emax)
    (FloatSpec.Core.Zaux.positiveToNat mx) ex
  (binaryPositiveOfNat r.1 (shl_align_fexp_fst_pos mx ex), r.2)

theorem shl_align_fexp_correct {prec emax : Int}
    (mx : FloatSpec.Core.Zaux.Positive) (ex : Int) :
    let r := shl_align_fexp (prec:=prec) (emax:=emax) mx ex
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Zaux.positiveToNat r.1 : Int) r.2 :
        FloatSpec.Core.Defs.FlocqFloat 2) =
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk
        (FloatSpec.Core.Zaux.positiveToNat mx : Int) ex :
          FloatSpec.Core.Defs.FlocqFloat 2) ∧
    r.2 ≤ FLT_exp (3 - emax - prec) prec
      (FloatSpec.Core.Digits.Zdigits 2
        (FloatSpec.Core.Zaux.positiveToNat r.1 : Int) + r.2) := by
  let n := FloatSpec.Core.Zaux.positiveToNat mx
  have hn : n ≠ 0 := Nat.ne_of_gt (FloatSpec.Core.Zaux.positiveToNat_pos mx)
  have h := _root_.shl_align_fexp_correct (prec:=prec) (emax:=emax) n ex hn
  have hrun := h hn
  simp only [wp, PostCond.noThrow, pure, _root_.shl_align_fexp_check] at hrun
  cases hr : _root_.shl_align_fexp (prec:=prec) (emax:=emax) n ex with
  | mk n' e' =>
      rw [hr] at hrun
      simpa [shl_align_fexp, n, hr, binaryPositiveOfNat_spec] using hrun

noncomputable abbrev shr_fexp (m e : Int) (l : Loc) : ShrRecord × Int :=
  _root_.shr_fexp m e l

theorem shr_fexp_truncate (m e : Int) (l : Loc) (hm : 0 ≤ m) :
    shr_fexp m e l =
      let r := FloatSpec.Calc.Round.truncate (beta:=2)
        (f:=(FloatSpec.Core.Defs.FlocqFloat.mk m e :
          FloatSpec.Core.Defs.FlocqFloat 2)) (e:=e) (l:=l)
      (_root_.shr_record_of_loc r.1 r.2.2, r.2.1) := by
  have h := _root_.shr_fexp_truncate m e l hm
  simpa [wp, PostCond.noThrow, pure, _root_.shr_fexp_truncate_check,
    shr_fexp] using h trivial

def erase {prec emax : Int} (x : binary_float prec emax) : binary_float prec emax := x

theorem erase_correct {prec emax : Int} (x : binary_float prec emax) :
    erase x = x := rfl

def is_finite_strict {prec emax : Int} (x : binary_float prec emax) : Bool :=
  binary_float.is_finite_strict x

theorem B2R_inj {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x y : binary_float prec emax)
    (hx : is_finite_strict x = true)
    (hy : is_finite_strict y = true)
    (hR : B2R x = B2R y) : x = y := by
  apply _root_.B2R_inj
  · simpa [is_finite_strict] using hx
  · simpa [is_finite_strict] using hy
  · cases x <;> cases y <;>
      simpa [B2R, binary_float.B2R, F2R, FloatSpec.Core.Defs.F2R] using hR

theorem is_finite_strict_B2BSN {prec emax : Int} (x : binary_float prec emax) :
    BSN_is_finite_strict (binarySingleNaNFloatToB754 (B2BSN x)) =
      is_finite_strict x := by
  cases x <;> rfl

def get_nan_pl {prec emax : Int} (x : binary_float prec emax) :
    FloatSpec.Core.Zaux.Positive :=
  match x with
  | binary_float.B754_nan _ payload _ => payload
  | _ => FloatSpec.Core.Zaux.Positive.xH

def build_nan {prec emax : Int}
    (x : {x : binary_float prec emax // is_nan x = true}) :
    binary_float prec emax := x.1

theorem build_nan_correct {prec emax : Int}
    (x : {x : binary_float prec emax // is_nan x = true}) :
    build_nan x = x.1 := rfl

theorem B2R_build_nan {prec emax : Int}
    (x : {x : binary_float prec emax // is_nan x = true}) :
    B2R (build_nan x) = 0 := by
  rcases x with ⟨x, hx⟩
  cases x <;> simp [build_nan, is_nan, B2R] at hx ⊢

theorem is_finite_build_nan {prec emax : Int}
    (x : {x : binary_float prec emax // is_nan x = true}) :
    is_finite (build_nan x) = false := by
  rcases x with ⟨x, hx⟩
  cases x <;> simp [build_nan, is_nan, is_finite] at hx ⊢

theorem is_nan_build_nan {prec emax : Int}
    (x : {x : binary_float prec emax // is_nan x = true}) :
    is_nan (build_nan x) = true := x.2

def is_nan_BSN {prec emax : Int} : BinarySingleNaNFloat prec emax → Bool
  | BinarySingleNaNFloat.B754_nan => true
  | _ => false

theorem is_nan_B2BSN {prec emax : Int} (x : binary_float prec emax) :
    is_nan_BSN (B2BSN x) = is_nan x := by
  cases x <;> rfl

def BSN2B {prec emax : Int}
    (nan : {x : binary_float prec emax // is_nan x = true})
    (x : BinarySingleNaNFloat prec emax) : binary_float prec emax :=
  match x with
  | BinarySingleNaNFloat.B754_zero s => binary_float.B754_zero s
  | BinarySingleNaNFloat.B754_infinity s => binary_float.B754_infinity s
  | BinarySingleNaNFloat.B754_nan => build_nan nan
  | BinarySingleNaNFloat.B754_finite s m e hm hbounded =>
      binary_float.B754_finite s (binaryPositiveOfNat m hm) e (by
        simpa [binaryPositiveOfNat_spec] using hbounded)

theorem B2BSN_BSN2B {prec emax : Int}
    (nan : {x : binary_float prec emax // is_nan x = true})
    (x : BinarySingleNaNFloat prec emax) :
    B2BSN (BSN2B nan x) = x := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan =>
      rcases nan with ⟨n, hn⟩
      cases n <;> simp [BSN2B, build_nan, B2BSN, is_nan,
        binaryFloatToBinarySingleNaNFloat] at hn ⊢
  | B754_finite s m e hm hbounded =>
      simp [BSN2B, B2BSN, binaryFloatToBinarySingleNaNFloat,
        binaryPositiveOfNat_spec]

theorem B2R_BSN2B {prec emax : Int}
    (nan : {x : binary_float prec emax // is_nan x = true})
    (x : BinarySingleNaNFloat prec emax) :
    B2R (BSN2B nan x) =
      B754_to_R (binarySingleNaNFloatToB754 x) := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => simp [BSN2B, B2R_build_nan, binarySingleNaNFloatToB754,
      B754_to_R]
  | B754_finite s m e hm hbounded =>
      cases s <;> simp [BSN2B, B2R, binarySingleNaNFloatToB754, B754_to_R,
        binaryPositiveOfNat_spec]

theorem is_finite_BSN2B {prec emax : Int}
    (nan : {x : binary_float prec emax // is_nan x = true})
    (x : BinarySingleNaNFloat prec emax) :
    is_finite (BSN2B nan x) =
      BSN_is_finite (binarySingleNaNFloatToB754 x) := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => simpa [BSN2B, binarySingleNaNFloatToB754, BSN_is_finite]
      using is_finite_build_nan nan
  | B754_finite s m e hm hbounded => rfl

theorem is_nan_BSN2B {prec emax : Int}
    (nan : {x : binary_float prec emax // is_nan x = true})
    (x : BinarySingleNaNFloat prec emax) :
    is_nan (BSN2B nan x) = is_nan_BSN x := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => simpa [BSN2B, is_nan_BSN] using is_nan_build_nan nan
  | B754_finite s m e hm hbounded => rfl

theorem Bsign_B2BSN {prec emax : Int} (x : binary_float prec emax)
    (hx : is_nan x = false) :
    BSN_sign (binarySingleNaNFloatToB754 (B2BSN x)) = Bsign x := by
  cases x <;> simp [is_nan, B2BSN, binaryFloatToBinarySingleNaNFloat,
    binarySingleNaNFloatToB754, BSN_sign, Bsign] at hx ⊢

theorem Bsign_BSN2B {prec emax : Int}
    (nan : {x : binary_float prec emax // is_nan x = true})
    (x : BinarySingleNaNFloat prec emax) (hx : is_nan_BSN x = false) :
    Bsign (BSN2B nan x) = BSN_sign (binarySingleNaNFloatToB754 x) := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => simp [is_nan_BSN] at hx
  | B754_finite s m e hm hbounded => rfl

def BSN2B' {prec emax : Int} (x : BinarySingleNaNFloat prec emax)
    (hx : is_nan_BSN x = false) : binary_float prec emax :=
  match x with
  | BinarySingleNaNFloat.B754_zero s => binary_float.B754_zero s
  | BinarySingleNaNFloat.B754_infinity s => binary_float.B754_infinity s
  | BinarySingleNaNFloat.B754_nan => False.elim (by
      simp [is_nan_BSN] at hx)
  | BinarySingleNaNFloat.B754_finite s m e hm hbounded =>
      binary_float.B754_finite s (binaryPositiveOfNat m hm) e (by
        simpa [binaryPositiveOfNat_spec] using hbounded)

theorem B2BSN_BSN2B' {prec emax : Int} (x : BinarySingleNaNFloat prec emax)
    (hx : is_nan_BSN x = false) :
    B2BSN (BSN2B' x hx) = x := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => simp [is_nan_BSN] at hx
  | B754_finite s m e hm hbounded =>
      simp [BSN2B', B2BSN, binaryFloatToBinarySingleNaNFloat,
        binaryPositiveOfNat_spec]

theorem B2R_BSN2B' {prec emax : Int} (x : BinarySingleNaNFloat prec emax)
    (hx : is_nan_BSN x = false) :
    B2R (BSN2B' x hx) = B754_to_R (binarySingleNaNFloatToB754 x) := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => simp [is_nan_BSN] at hx
  | B754_finite s m e hm hbounded =>
      cases s <;> simp [BSN2B', B2R, binarySingleNaNFloatToB754, B754_to_R,
        binaryPositiveOfNat_spec]

theorem Bsign_BSN2B' {prec emax : Int} (x : BinarySingleNaNFloat prec emax)
    (hx : is_nan_BSN x = false) :
    Bsign (BSN2B' x hx) = BSN_sign (binarySingleNaNFloatToB754 x) := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => simp [is_nan_BSN] at hx
  | B754_finite s m e hm hbounded => rfl

theorem is_finite_BSN2B' {prec emax : Int}
    (x : BinarySingleNaNFloat prec emax) (hx : is_nan_BSN x = false) :
    is_finite (BSN2B' x hx) =
      BSN_is_finite (binarySingleNaNFloatToB754 x) := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => simp [is_nan_BSN] at hx
  | B754_finite s m e hm hbounded => rfl

theorem is_nan_BSN2B' {prec emax : Int}
    (x : BinarySingleNaNFloat prec emax) (hx : is_nan_BSN x = false) :
    is_nan (BSN2B' x hx) = false := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => simp [is_nan_BSN] at hx
  | B754_finite s m e hm hbounded => rfl

def lift {prec emax : Int} (x : binary_float prec emax)
    (y : BinarySingleNaNFloat prec emax)
    (hy : is_nan_BSN y = is_nan x) : binary_float prec emax :=
  if hx : is_nan x = true then x else
    BSN2B' y (by rw [hy]; exact Bool.eq_false_of_not_eq_true hx)

theorem B2BSN_lift {prec emax : Int} (x : binary_float prec emax)
    (y : BinarySingleNaNFloat prec emax)
    (hy : is_nan_BSN y = is_nan x) :
    B2BSN (lift x y hy) = y := by
  by_cases hx : is_nan x = true
  · cases x with
    | B754_zero s => simp [is_nan] at hx
    | B754_infinity s => simp [is_nan] at hx
    | B754_finite s m e hbounded => simp [is_nan] at hx
    | B754_nan s payload hpayload =>
        cases y with
        | B754_zero sy => simp [is_nan_BSN, is_nan] at hy
        | B754_infinity sy => simp [is_nan_BSN, is_nan] at hy
        | B754_finite sy m e hm hbounded => simp [is_nan_BSN, is_nan] at hy
        | B754_nan => simp [lift, is_nan, B2BSN,
            binaryFloatToBinarySingleNaNFloat]
  · have hyfalse : is_nan_BSN y = false := by
      rw [hy]
      exact Bool.eq_false_of_not_eq_true hx
    unfold lift
    rw [dite_eq_right hx]
    exact B2BSN_BSN2B' y hyfalse

theorem B2R_lift {prec emax : Int} (x : binary_float prec emax)
    (y : BinarySingleNaNFloat prec emax)
    (hy : is_nan_BSN y = is_nan x) :
    B2R (lift x y hy) = B754_to_R (binarySingleNaNFloatToB754 y) := by
  calc
    B2R (lift x y hy) = B754_to_R
        (binarySingleNaNFloatToB754 (B2BSN (lift x y hy))) :=
      (B2R_B2BSN (lift x y hy)).symm
    _ = B754_to_R (binarySingleNaNFloatToB754 y) := by rw [B2BSN_lift]

theorem is_finite_lift {prec emax : Int} (x : binary_float prec emax)
    (y : BinarySingleNaNFloat prec emax)
    (hy : is_nan_BSN y = is_nan x) :
    is_finite (lift x y hy) = BSN_is_finite (binarySingleNaNFloatToB754 y) := by
  calc
    is_finite (lift x y hy) = BSN_is_finite
        (binarySingleNaNFloatToB754 (B2BSN (lift x y hy))) :=
      (is_finite_B2BSN (lift x y hy)).symm
    _ = BSN_is_finite (binarySingleNaNFloatToB754 y) := by rw [B2BSN_lift]

theorem is_nan_lift {prec emax : Int} (x : binary_float prec emax)
    (y : BinarySingleNaNFloat prec emax)
    (hy : is_nan_BSN y = is_nan x) :
    is_nan (lift x y hy) = is_nan x := by
  calc
    is_nan (lift x y hy) = is_nan_BSN (B2BSN (lift x y hy)) :=
      (is_nan_B2BSN (lift x y hy)).symm
    _ = is_nan_BSN y := by rw [B2BSN_lift]
    _ = is_nan x := hy

theorem Bsign_lift {prec emax : Int} (x : binary_float prec emax)
    (y : BinarySingleNaNFloat prec emax)
    (hy : is_nan_BSN y = is_nan x) (hx : is_nan x = false) :
    Bsign (lift x y hy) = BSN_sign (binarySingleNaNFloatToB754 y) := by
  have hresult : is_nan (lift x y hy) = false := by rw [is_nan_lift, hx]
  calc
    Bsign (lift x y hy) = BSN_sign
        (binarySingleNaNFloatToB754 (B2BSN (lift x y hy))) :=
      (Bsign_B2BSN (lift x y hy) hresult).symm
    _ = BSN_sign (binarySingleNaNFloatToB754 y) := by rw [B2BSN_lift]

theorem B2FF_lift_of_not_nan {prec emax : Int} (x : binary_float prec emax)
    (y : BinarySingleNaNFloat prec emax)
    (hy : is_nan_BSN y = is_nan x) (hx : is_nan x = false) :
    B2FF (lift x y hy) = SF2FF (binarySingleNaNFloatToStandardFloat y) := by
  cases x with
  | B754_zero sx =>
      cases y <;> simp [is_nan, is_nan_BSN] at hy ⊢ <;>
        simp [lift, is_nan, is_nan_BSN, BSN2B', B2FF, SF2FF,
          binarySingleNaNFloatToStandardFloat, binary_float.toBinary754,
          binaryPositiveOfNat_spec]
  | B754_infinity sx =>
      cases y <;> simp [is_nan, is_nan_BSN] at hy ⊢ <;>
        simp [lift, is_nan, is_nan_BSN, BSN2B', B2FF, SF2FF,
          binarySingleNaNFloatToStandardFloat, binary_float.toBinary754,
          binaryPositiveOfNat_spec]
  | B754_nan sx payload hpayload => simp [is_nan] at hx
  | B754_finite sx m e hbounded =>
      cases y <;> simp [is_nan, is_nan_BSN] at hy ⊢ <;>
        simp [lift, is_nan, is_nan_BSN, BSN2B', B2FF, SF2FF,
          binarySingleNaNFloatToStandardFloat, binary_float.toBinary754,
          binaryPositiveOfNat_spec]

abbrev BmultNaNHandler (prec emax : Int) :=
  (x y : binary_float prec emax) →
    {nan : binary_float prec emax // is_nan (prec:=prec) (emax:=emax) nan = true}

abbrev BplusNaNHandler (prec emax : Int) :=
  (x y : binary_float prec emax) →
    {nan : binary_float prec emax // is_nan (prec:=prec) (emax:=emax) nan = true}

abbrev BminusNaNHandler (prec emax : Int) :=
  (x y : binary_float prec emax) →
    {nan : binary_float prec emax // is_nan (prec:=prec) (emax:=emax) nan = true}

abbrev BsqrtNaNHandler (prec emax : Int) :=
  (x : binary_float prec emax) →
    {nan : binary_float prec emax // is_nan (prec:=prec) (emax:=emax) nan = true}

abbrev BfmaNaNHandler (prec emax : Int) :=
  (x y z : binary_float prec emax) →
    {nan : binary_float prec emax // is_nan (prec:=prec) (emax:=emax) nan = true}

abbrev BdivNaNHandler (prec emax : Int) :=
  (x y : binary_float prec emax) →
    {nan : binary_float prec emax // is_nan (prec:=prec) (emax:=emax) nan = true}

-- Coq `Binary.v:binary_overflow`, on the proof-carrying Binary surface.
-- The older root-level `binary_overflow` helper in `Binary.lean` is a
-- compatibility constructor; this namespace-qualified bridge keeps the exact
-- upstream mode-sensitive SingleNaN payload.
def binary_overflow {prec emax : Int} (mode : RoundingMode) (s : Bool) : FullFloat :=
  SF2FF (bsn_binary_overflow (prec:=prec) (emax:=emax) mode s)

private theorem roundR_zero_of_mode {prec emax : Int} (mode : RoundingMode) :
    FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
      (rnd_of_mode mode) 0 = 0 := by
  cases mode <;> simp [FloatSpec.Core.Generic_fmt.roundR,
    FloatSpec.Core.Generic_fmt.scaled_mantissa, rnd_of_mode,
    FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil,
    FloatSpec.Core.Raux.Ztrunc, FloatSpec.Core.Generic_fmt.Znearest,
    FloatSpec.Core.Raux.Rcompare]

private theorem Rlt_bool_zero_bpow {emax : Int} :
    FloatSpec.Core.Raux.Rlt_bool (0 : ℝ)
      (FloatSpec.Core.Raux.bpow 2 emax) = true := by
  have hbpow_pos : 0 < FloatSpec.Core.Raux.bpow 2 emax := by
    exact zpow_pos (by norm_num : (0 : ℝ) < 2) emax
  simp [FloatSpec.Core.Raux.Rlt_bool, hbpow_pos]

private theorem bmult_correct_nan_result {prec emax : Int}
    (mult_nan : BmultNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax)
    (hprod : B2R (prec:=prec) (emax:=emax) x *
        B2R (prec:=prec) (emax:=emax) y = 0)
    (hfinite : (is_finite (prec:=prec) (emax:=emax) x &&
        is_finite (prec:=prec) (emax:=emax) y) = false) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (B2R (prec:=prec) (emax:=emax) x *
             B2R (prec:=prec) (emax:=emax) y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (prec:=prec) (emax:=emax) (mult_nan x y).1 =
        FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (B2R (prec:=prec) (emax:=emax) x *
             B2R (prec:=prec) (emax:=emax) y) ∧
      is_finite (prec:=prec) (emax:=emax) (mult_nan x y).1 =
        (is_finite (prec:=prec) (emax:=emax) x &&
          is_finite (prec:=prec) (emax:=emax) y) ∧
      (is_nan (prec:=prec) (emax:=emax) (mult_nan x y).1 = false →
        Bsign (prec:=prec) (emax:=emax) (mult_nan x y).1 =
          Bool.xor (Bsign (prec:=prec) (emax:=emax) x)
            (Bsign (prec:=prec) (emax:=emax) y))
    else
      B2FF (prec:=prec) (emax:=emax) (mult_nan x y).1 =
        binary_overflow (prec:=prec) (emax:=emax) mode
          (Bool.xor (Bsign (prec:=prec) (emax:=emax) x)
            (Bsign (prec:=prec) (emax:=emax) y)) := by
  rw [hprod, roundR_zero_of_mode (prec:=prec) (emax:=emax) mode]
  simp [Rlt_bool_zero_bpow, hfinite]
  rcases hmn : mult_nan x y with ⟨nan, hnan⟩
  cases nan <;> simp [is_nan, B2R, is_finite] at hnan ⊢

private theorem zdigits_one :
    FloatSpec.Core.Digits.Zdigits 2 (1 : Int) = 1 := by
  have h := FloatSpec.Core.Digits.Zdigits_unique_from_nonzero_payload (beta := 2) (h_beta := by norm_num)
    (n := (1 : Int)) (e := (1 : Int)) (hβ := by norm_num)
  simpa [wp, PostCond.noThrow, pure] using
    h ⟨by norm_num, by norm_num, by norm_num⟩

theorem specFloat_bounded_one_emin {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    specFloat_bounded (prec:=prec) (emax:=emax) 1 (3 - emax - prec) = true := by
  have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
  have hemax_ge_two := (inferInstance : Prec_lt_emax prec emax).emax_ge_2
  have hzd : FloatSpec.Core.Digits.Zdigits 2 ((1 : Nat) : Int) = 1 := by
    simpa using zdigits_one
  unfold specFloat_bounded canonical_mantissa
  rw [Bool.and_eq_true]
  constructor
  · apply beq_iff_eq.mpr
    rw [hzd]
    unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
    apply Eq.symm
    apply max_eq_right
    omega
  · apply decide_eq_true
    omega

def standardFloatToBinaryFloatOfNotNaN {prec emax : Int}
    (x : StandardFloat)
    (hvalid : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true)
    (hnotnan : is_nan_SF x = false) :
    binary_float prec emax :=
  match x with
  | StandardFloat.S754_zero s =>
      binary_float.B754_zero (prec:=prec) (emax:=emax) s
  | StandardFloat.S754_infinity s =>
      binary_float.B754_infinity (prec:=prec) (emax:=emax) s
  | StandardFloat.S754_nan =>
      False.elim (by simp [is_nan_SF] at hnotnan)
  | StandardFloat.S754_finite s m e =>
      have h' : decide (0 < m) = true ∧
          specFloat_bounded (prec:=prec) (emax:=emax) m e = true := by
        simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hvalid
      have hm_pos : 0 < m := of_decide_eq_true h'.1
      let p := binaryPositiveOfNat m hm_pos
      have hp : FloatSpec.Core.Zaux.positiveToNat p = m :=
        binaryPositiveOfNat_spec m hm_pos
      binary_float.B754_finite (prec:=prec) (emax:=emax) s p e (by
        simpa [hp] using h'.2)

-- Coq: `Binary.v:Bsqrt`.
noncomputable def Bsqrt {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (sqrt_nan : BsqrtNaNHandler prec emax)
    (mode : RoundingMode) (x : binary_float prec emax) :
    binary_float prec emax :=
  match x with
  | binary_float.B754_nan _ _ _ => (sqrt_nan x).1
  | binary_float.B754_infinity false => x
  | binary_float.B754_infinity true => (sqrt_nan x).1
  | binary_float.B754_zero _ => x
  | binary_float.B754_finite true _ _ _ => (sqrt_nan x).1
  | binary_float.B754_finite false mx ex _ =>
      let mxn := FloatSpec.Core.Zaux.positiveToNat mx
      let input := F2R
        (FloatSpec.Core.Defs.FlocqFloat.mk (mxn : Int) ex :
          FloatSpec.Core.Defs.FlocqFloat 2)
      let result := SFsqrt_core_binary prec emax (mxn : Int) ex
      have hdata := SFsqrt_core_binary_correct_data
        (prec:=prec) (emax:=emax) (mxn : Int) ex
        (by exact_mod_cast positiveToNat_pos_bsn mx)
      have hresult_pos : 0 < result.1 := by
        simpa [result] using hdata.1
      let mzn := result.1.toNat
      have hmzn_pos : 0 < mzn := by omega
      have hmzn_cast : (mzn : Int) = result.1 :=
        Int.toNat_of_nonneg (le_of_lt hresult_pos)
      let z := binary_round_aux (prec:=prec) (emax:=emax) mode false
        (mzn : Int) result.2.1 result.2.2
      have hbetween :
          FloatSpec.Calc.Bracket.inbetween_float 2 (mzn : Int) result.2.1
            |Real.sqrt input| result.2.2 := by
        simpa [input, result, hmzn_cast, abs_of_nonneg (Real.sqrt_nonneg _)] using
          hdata.2.1
      have hexp :
          result.2.1 ≤
            FLT_exp (3 - emax - prec) prec
              (FloatSpec.Core.Digits.Zdigits 2 (mzn : Int) + result.2.1) := by
        simpa [result, hmzn_cast] using hdata.2.2
      have haux := binary_round_aux_correct (prec:=prec) (emax:=emax)
        mode (Real.sqrt input) mzn result.2.1 result.2.2 hmzn_pos hbetween hexp
      have hsqrt_sign : FloatSpec.Core.Raux.Rlt_bool (Real.sqrt input) 0 = false := by
        simp [FloatSpec.Core.Raux.Rlt_bool, Real.sqrt_nonneg]
      have hvalid :
          validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true := by
        simpa [z, hsqrt_sign] using haux.1
      have hnotnan : is_nan_SF z = false := by
        have hmzn_nonneg : (0 : Int) ≤ (mzn : Int) := by exact_mod_cast Nat.zero_le mzn
        simpa [z] using
          is_nan_binary_round_aux_of_nonneg (prec:=prec) (emax:=emax)
            mode false (mzn : Int) result.2.1 result.2.2 hmzn_nonneg
      standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax) z hvalid hnotnan

theorem binarySingleNaNFloatToB754_standardFloatToBinaryFloatOfNotNaN
    {prec emax : Int}
    (x : StandardFloat)
    (hvalid : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true)
    (hnotnan : is_nan_SF x = false) :
    binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
      (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
        (standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax)
          x hvalid hnotnan)) = SF2B x := by
  cases x with
  | S754_zero s => rfl
  | S754_infinity s => rfl
  | S754_nan => simp [is_nan_SF] at hnotnan
  | S754_finite s m e =>
      dsimp [standardFloatToBinaryFloatOfNotNaN]
      simp [binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754, SF2B]
      exact binaryPositiveOfNat_spec m _

theorem B2R_standardFloatToBinaryFloatOfNotNaN {prec emax : Int}
    (x : StandardFloat)
    (hvalid : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true)
    (hnotnan : is_nan_SF x = false) :
    B2R (prec:=prec) (emax:=emax)
      (standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax)
        x hvalid hnotnan) = SF2R 2 x := by
  cases x with
  | S754_zero s => rfl
  | S754_infinity s => rfl
  | S754_nan => simp [is_nan_SF] at hnotnan
  | S754_finite s m e =>
      dsimp [standardFloatToBinaryFloatOfNotNaN]
      simp [B2R, SF2R, binaryPositiveOfNat_spec]

theorem is_finite_standardFloatToBinaryFloatOfNotNaN {prec emax : Int}
    (x : StandardFloat)
    (hvalid : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true)
    (hnotnan : is_nan_SF x = false) :
    is_finite (prec:=prec) (emax:=emax)
      (standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax)
        x hvalid hnotnan) = is_finite_SF x := by
  cases x with
  | S754_zero s => rfl
  | S754_infinity s => rfl
  | S754_nan => simp [is_nan_SF] at hnotnan
  | S754_finite s m e =>
      dsimp [standardFloatToBinaryFloatOfNotNaN]
      simp [is_finite, is_finite_SF]

theorem Bsign_standardFloatToBinaryFloatOfNotNaN {prec emax : Int}
    (x : StandardFloat)
    (hvalid : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true)
    (hnotnan : is_nan_SF x = false) :
    Bsign (prec:=prec) (emax:=emax)
      (standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax)
        x hvalid hnotnan) = sign_SF x := by
  cases x with
  | S754_zero s => rfl
  | S754_infinity s => rfl
  | S754_nan => simp [is_nan_SF] at hnotnan
  | S754_finite s m e =>
      dsimp [standardFloatToBinaryFloatOfNotNaN]
      simp [Bsign, sign_SF]

theorem B2FF_standardFloatToBinaryFloatOfNotNaN {prec emax : Int}
    (x : StandardFloat)
    (hvalid : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true)
    (hnotnan : is_nan_SF x = false) :
    B2FF (prec:=prec) (emax:=emax)
      (standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax)
        x hvalid hnotnan) = SF2FF x := by
  cases x with
  | S754_zero s => rfl
  | S754_infinity s => rfl
  | S754_nan => simp [is_nan_SF] at hnotnan
  | S754_finite s m e =>
      dsimp [standardFloatToBinaryFloatOfNotNaN]
      simp [B2FF, binary_float.toBinary754, SF2FF,
        binaryPositiveOfNat_spec]

def Bopp_preserve_nan {prec emax : Int}
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | binary_float.B754_zero s =>
      binary_float.B754_zero (prec:=prec) (emax:=emax) (!s)
  | binary_float.B754_infinity s =>
      binary_float.B754_infinity (prec:=prec) (emax:=emax) (!s)
  | binary_float.B754_nan s payload hPayload =>
      binary_float.B754_nan (prec:=prec) (emax:=emax) (!s) payload hPayload
  | binary_float.B754_finite s m e hBounded =>
      binary_float.B754_finite (prec:=prec) (emax:=emax) (!s) m e hBounded

theorem B2R_Bopp_preserve_nan {prec emax : Int} (x : binary_float prec emax) :
    B2R (prec:=prec) (emax:=emax) (Bopp_preserve_nan x) =
      -B2R (prec:=prec) (emax:=emax) x := by
  cases x with
  | B754_zero s => simp [Bopp_preserve_nan, B2R]
  | B754_infinity s => simp [Bopp_preserve_nan, B2R]
  | B754_nan s payload hPayload => simp [Bopp_preserve_nan, B2R]
  | B754_finite s m e hBounded =>
      cases s <;> simp [Bopp_preserve_nan, B2R, F2R, FloatSpec.Core.Defs.F2R]

theorem is_finite_Bopp_preserve_nan {prec emax : Int} (x : binary_float prec emax) :
    is_finite (prec:=prec) (emax:=emax) (Bopp_preserve_nan x) =
      is_finite (prec:=prec) (emax:=emax) x := by
  cases x <;> rfl

theorem Bsign_Bopp_preserve_nan {prec emax : Int} (x : binary_float prec emax) :
    Bsign (prec:=prec) (emax:=emax) (Bopp_preserve_nan x) =
      !Bsign (prec:=prec) (emax:=emax) x := by
  cases x <;> rfl

abbrev BoppNaNHandler (prec emax : Int) :=
  (x : binary_float prec emax) →
    {nan : binary_float prec emax // is_nan (prec:=prec) (emax:=emax) nan = true}

-- Coq `Binary.v:Bopp`: the caller chooses the NaN result.
def Bopp {prec emax : Int} (opp_nan : BoppNaNHandler prec emax)
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | binary_float.B754_nan _ _ _ => (opp_nan x).1
  | _ => Bopp_preserve_nan x

theorem Bopp_involutive {prec emax : Int} (opp_nan : BoppNaNHandler prec emax)
    (x : binary_float prec emax)
    (hx : is_nan (prec:=prec) (emax:=emax) x = false) :
    Bopp opp_nan (Bopp opp_nan x) = x := by
  cases x <;> simp [Bopp, Bopp_preserve_nan, is_nan] at hx ⊢

theorem B2R_Bopp {prec emax : Int} (opp_nan : BoppNaNHandler prec emax)
    (x : binary_float prec emax) :
    B2R (prec:=prec) (emax:=emax) (Bopp opp_nan x) =
      -B2R (prec:=prec) (emax:=emax) x := by
  cases x with
  | B754_nan s payload hpayload =>
      rcases h : opp_nan (binary_float.B754_nan s payload hpayload) with ⟨nan, hnan⟩
      cases nan <;> simp [Bopp, B2R, is_nan, h] at hnan ⊢
  | B754_zero s => simp [Bopp, B2R_Bopp_preserve_nan]
  | B754_infinity s => simp [Bopp, B2R_Bopp_preserve_nan]
  | B754_finite s m e hbounded => simp [Bopp, B2R_Bopp_preserve_nan]

theorem is_finite_Bopp {prec emax : Int} (opp_nan : BoppNaNHandler prec emax)
    (x : binary_float prec emax) :
    is_finite (prec:=prec) (emax:=emax) (Bopp opp_nan x) =
      is_finite (prec:=prec) (emax:=emax) x := by
  cases x with
  | B754_nan s payload hpayload =>
      rcases h : opp_nan (binary_float.B754_nan s payload hpayload) with ⟨nan, hnan⟩
      cases nan <;> simp [Bopp, is_nan, is_finite, h] at hnan ⊢
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_finite s m e hbounded => rfl

theorem Bsign_Bopp {prec emax : Int} (opp_nan : BoppNaNHandler prec emax)
    (x : binary_float prec emax)
    (hx : is_nan (prec:=prec) (emax:=emax) x = false) :
    Bsign (prec:=prec) (emax:=emax) (Bopp opp_nan x) =
      !Bsign (prec:=prec) (emax:=emax) x := by
  cases x <;> simp [Bopp, Bopp_preserve_nan, is_nan, Bsign] at hx ⊢

abbrev BabsNaNHandler (prec emax : Int) :=
  (x : binary_float prec emax) →
    {nan : binary_float prec emax // is_nan (prec:=prec) (emax:=emax) nan = true}

def Babs {prec emax : Int} (abs_nan : BabsNaNHandler prec emax)
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | binary_float.B754_nan _ _ _ => (abs_nan x).1
  | binary_float.B754_zero _ => binary_float.B754_zero false
  | binary_float.B754_infinity _ => binary_float.B754_infinity false
  | binary_float.B754_finite _ m e hbounded =>
      binary_float.B754_finite false m e hbounded

theorem B2R_Babs {prec emax : Int} (abs_nan : BabsNaNHandler prec emax)
    (x : binary_float prec emax) :
    B2R (prec:=prec) (emax:=emax) (Babs abs_nan x) =
      |B2R (prec:=prec) (emax:=emax) x| := by
  cases x with
  | B754_nan s payload hpayload =>
      rcases h : abs_nan (binary_float.B754_nan s payload hpayload) with ⟨nan, hnan⟩
      cases nan <;> simp [Babs, B2R, is_nan, h] at hnan ⊢
  | B754_zero s => simp [Babs, B2R]
  | B754_infinity s => simp [Babs, B2R]
  | B754_finite s m e hbounded =>
      have hbpow_nonneg :
          0 ≤ FloatSpec.Core.Raux.bpow 2 e :=
        le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e)
      cases s <;> simp [Babs, B2R, F2R, FloatSpec.Core.Defs.F2R,
        abs_mul, abs_of_nonneg hbpow_nonneg]

theorem is_finite_Babs {prec emax : Int} (abs_nan : BabsNaNHandler prec emax)
    (x : binary_float prec emax) :
    is_finite (prec:=prec) (emax:=emax) (Babs abs_nan x) =
      is_finite (prec:=prec) (emax:=emax) x := by
  cases x with
  | B754_nan s payload hpayload =>
      rcases h : abs_nan (binary_float.B754_nan s payload hpayload) with ⟨nan, hnan⟩
      cases nan <;> simp [Babs, is_nan, is_finite, h] at hnan ⊢
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_finite s m e hbounded => rfl

theorem Bsign_Babs {prec emax : Int} (abs_nan : BabsNaNHandler prec emax)
    (x : binary_float prec emax)
    (hx : is_nan (prec:=prec) (emax:=emax) x = false) :
    Bsign (prec:=prec) (emax:=emax) (Babs abs_nan x) = false := by
  cases x <;> simp [Babs, is_nan, Bsign] at hx ⊢

theorem Babs_idempotent {prec emax : Int} (abs_nan : BabsNaNHandler prec emax)
    (x : binary_float prec emax)
    (hx : is_nan (prec:=prec) (emax:=emax) x = false) :
    Babs abs_nan (Babs abs_nan x) = Babs abs_nan x := by
  cases x <;> simp [Babs, is_nan] at hx ⊢

theorem Babs_Bopp {prec emax : Int}
    (abs_nan : BabsNaNHandler prec emax) (opp_nan : BoppNaNHandler prec emax)
    (x : binary_float prec emax)
    (hx : is_nan (prec:=prec) (emax:=emax) x = false) :
    Babs abs_nan (Bopp opp_nan x) = Babs abs_nan x := by
  cases x <;> simp [Babs, Bopp, Bopp_preserve_nan, is_nan] at hx ⊢

noncomputable def Bcompare {prec emax : Int}
    (x y : binary_float prec emax) : Option Int :=
  _root_.Bcompare (binary_float.toBinary754 x) (binary_float.toBinary754 y)

private theorem is_finite_toBinary754 {prec emax : Int}
    (x : binary_float prec emax) :
    is_finite_B (binary_float.toBinary754 x) =
      is_finite (prec:=prec) (emax:=emax) x := by
  cases x <;> rfl

private theorem B2R_toBinary754 {prec emax : Int}
    (x : binary_float prec emax) :
    _root_.B2R (binary_float.toBinary754 x) =
      B2R (prec:=prec) (emax:=emax) x := by
  cases x <;> rfl

theorem Bcompare_correct {prec emax : Int} (x y : binary_float prec emax)
    (hx : is_finite (prec:=prec) (emax:=emax) x = true)
    (hy : is_finite (prec:=prec) (emax:=emax) y = true) :
    Bcompare x y = some (FloatSpec.Core.Raux.Rcompare
      (B2R (prec:=prec) (emax:=emax) x)
      (B2R (prec:=prec) (emax:=emax) y)) := by
  have hx' : is_finite_B (binary_float.toBinary754 x) = true := by
    simpa [is_finite_toBinary754] using hx
  have hy' : is_finite_B (binary_float.toBinary754 y) = true := by
    simpa [is_finite_toBinary754] using hy
  have h := _root_.Bcompare_correct_compat
    (binary_float.toBinary754 x) (binary_float.toBinary754 y) hx' hy'
  simpa [Bcompare, _root_.Bcompare_check, wp, PostCond.noThrow, pure,
    B2R_toBinary754] using h trivial

theorem Bcompare_swap {prec emax : Int} (x y : binary_float prec emax) :
    Bcompare y x =
      match Bcompare x y with
      | some c => some (-c)
      | none => none := by
  let xb := binary_float.toBinary754 x
  let yb := binary_float.toBinary754 y
  change _root_.Bcompare yb xb =
    match _root_.Bcompare xb yb with
    | some c => some (-c)
    | none => none
  have h := _root_.Bcompare_swap_compat xb yb
  have hs := h trivial
  change _root_.Bcompare yb xb =
    (match _root_.Bcompare xb yb with
    | some c => some (-c)
    | none => none) at hs
  exact hs

noncomputable def Btrunc {prec emax : Int} (x : binary_float prec emax) : Int :=
  FloatSpec.Core.Raux.Ztrunc (B2R x)

theorem Btrunc_correct {prec emax : Int} (x : binary_float prec emax) :
    (Btrunc x : ℝ) =
      FloatSpec.Core.Generic_fmt.round_to_generic 2
        (FloatSpec.Core.FIX.FIX_exp 0) FloatSpec.Core.Raux.Ztrunc (B2R x) := by
  have h := FloatSpec.Core.FIX.round_FIX_IZR FloatSpec.Core.Raux.Ztrunc (B2R x)
  have hr := h trivial
  simpa [Btrunc, wp, PostCond.noThrow, pure] using hr.symm

abbrev BnearbyintNaNHandler (prec emax : Int) :=
  (x : binary_float prec emax) →
    {nan : binary_float prec emax // is_nan (prec:=prec) (emax:=emax) nan = true}

theorem is_nan_standardFloatToBinarySingleNaNFloat {prec emax : Int}
    (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true) :
    is_nan_BSN (standardFloatToBinarySingleNaNFloat x hx) = is_nan_SF x := by
  cases x <;> rfl

theorem B2R_standardFloatToBinarySingleNaNFloat {prec emax : Int}
    (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true) :
    B754_to_R (binarySingleNaNFloatToB754
      (standardFloatToBinarySingleNaNFloat x hx)) = SF2R 2 x := by
  cases x <;> simp [standardFloatToBinarySingleNaNFloat,
    binarySingleNaNFloatToB754, B754_to_R, SF2R]

theorem is_finite_standardFloatToBinarySingleNaNFloat {prec emax : Int}
    (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true) :
    BSN_is_finite (binarySingleNaNFloatToB754
      (standardFloatToBinarySingleNaNFloat x hx)) = is_finite_SF x := by
  cases x <;> rfl

theorem Bsign_standardFloatToBinarySingleNaNFloat {prec emax : Int}
    (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true)
    (hn : is_nan_SF x = false) :
    BSN_sign (binarySingleNaNFloatToB754
      (standardFloatToBinarySingleNaNFloat x hx)) = sign_SF x := by
  cases x <;> simp [is_nan_SF, standardFloatToBinarySingleNaNFloat,
    binarySingleNaNFloatToB754, BSN_sign, sign_SF] at hn ⊢

noncomputable def BnearbyintSingle {prec emax : Int}
    [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : BinarySingleNaNFloat prec emax) :
    BinarySingleNaNFloat prec emax :=
  match x with
  | BinarySingleNaNFloat.B754_zero s =>
      BinarySingleNaNFloat.B754_zero s
  | BinarySingleNaNFloat.B754_infinity s =>
      BinarySingleNaNFloat.B754_infinity s
  | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_finite s m e hm hbounded =>
      let z := SFnearbyint_binary (prec:=prec) (emax:=emax) mode s m e
      have hcorrect := Bnearbyint_correct_aux_nat
        (prec:=prec) (emax:=emax) mode s m e hm hbounded
      standardFloatToBinarySingleNaNFloat z hcorrect.1

theorem is_nan_BnearbyintSingle {prec emax : Int}
    [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : BinarySingleNaNFloat prec emax) :
    is_nan_BSN (BnearbyintSingle mode x) = is_nan_BSN x := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => rfl
  | B754_finite s m e hm hbounded =>
      let z := SFnearbyint_binary (prec:=prec) (emax:=emax) mode s m e
      have hcorrect := Bnearbyint_correct_aux_nat
        (prec:=prec) (emax:=emax) mode s m e hm hbounded
      have hfinite : is_finite_SF z = true := hcorrect.2.2.1
      rw [show BnearbyintSingle mode
          (BinarySingleNaNFloat.B754_finite s m e hm hbounded) =
          standardFloatToBinarySingleNaNFloat z hcorrect.1 by rfl]
      rw [is_nan_standardFloatToBinarySingleNaNFloat]
      have hnotnan : is_nan_SF z = false := by
        cases hz : z <;> simp [hz, is_finite_SF, is_nan_SF] at hfinite ⊢
      simpa [is_nan_BSN] using hnotnan

-- Coq `Binary.v:Bnearbyint`: the numerical operation is performed on the
-- SingleNaN view and the caller supplies the result for an input NaN.
noncomputable def Bnearbyint {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (nearbyint_nan : BnearbyintNaNHandler prec emax)
    (mode : RoundingMode) (x : binary_float prec emax) :
    binary_float prec emax :=
  BSN2B (nearbyint_nan x) (BnearbyintSingle mode (B2BSN x))

theorem Bnearbyint_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (nearbyint_nan : BnearbyintNaNHandler prec emax)
    (mode : RoundingMode) (x : binary_float prec emax) :
    B2R (Bnearbyint nearbyint_nan mode x) =
        FloatSpec.Core.Generic_fmt.roundR 2 (FloatSpec.Core.FIX.FIX_exp 0)
          (rnd_of_mode mode) (B2R x) ∧
      is_finite (Bnearbyint nearbyint_nan mode x) = is_finite x ∧
      (is_nan (Bnearbyint nearbyint_nan mode x) = false →
        Bsign (Bnearbyint nearbyint_nan mode x) = Bsign x) := by
  have hround0 : FloatSpec.Core.Generic_fmt.roundR 2
      (FloatSpec.Core.FIX.FIX_exp 0) (rnd_of_mode mode) 0 = 0 := by
    simpa only [FloatSpec.Core.Generic_fmt.round_to_generic] using
      round_to_generic_rnd_of_mode_zero mode (FloatSpec.Core.FIX.FIX_exp 0)
  cases x with
  | B754_zero s =>
      simp [Bnearbyint, BnearbyintSingle, B2BSN, BSN2B, B2R, is_finite,
        is_nan, Bsign, hround0, binaryFloatToBinarySingleNaNFloat]
  | B754_infinity s =>
      simp [Bnearbyint, BnearbyintSingle, B2BSN, BSN2B, B2R, is_finite,
        is_nan, Bsign, hround0, binaryFloatToBinarySingleNaNFloat]
  | B754_nan s payload hpayload =>
      rcases hnan : nearbyint_nan
          (binary_float.B754_nan (prec:=prec) (emax:=emax) s payload hpayload) with
        ⟨nan, hn⟩
      cases nan <;>
        simp [Bnearbyint, BnearbyintSingle, B2BSN, BSN2B, B2R, is_finite,
          is_nan, Bsign, hround0, hnan,
          binaryFloatToBinarySingleNaNFloat, build_nan] at hn ⊢
  | B754_finite s m e hbounded =>
      let mn := FloatSpec.Core.Zaux.positiveToNat m
      have hm : 0 < mn := positiveToNat_pos_bsn m
      let z := SFnearbyint_binary (prec:=prec) (emax:=emax) mode s mn e
      have hc := Bnearbyint_correct_aux_nat (prec:=prec) (emax:=emax)
        mode s mn e hm (by simpa [mn] using hbounded)
      have hnotnan : is_nan_SF z = false := by
        have hf : is_finite_SF z = true := hc.2.2.1
        cases hz : z <;> simp [hz, is_finite_SF, is_nan_SF] at hf ⊢
      have hsingle : BnearbyintSingle mode
          (B2BSN (binary_float.B754_finite s m e hbounded)) =
          standardFloatToBinarySingleNaNFloat z hc.1 := by rfl
      constructor
      · rw [show Bnearbyint nearbyint_nan mode
            (binary_float.B754_finite s m e hbounded) =
            BSN2B (nearbyint_nan
              (binary_float.B754_finite s m e hbounded))
              (standardFloatToBinarySingleNaNFloat z hc.1) by
              simp [Bnearbyint, hsingle]]
        rw [B2R_BSN2B, B2R_standardFloatToBinarySingleNaNFloat]
        simpa [B2R, SF2R, F2R, FloatSpec.Core.Defs.F2R, mn, z] using hc.2.1
      · constructor
        · rw [show Bnearbyint nearbyint_nan mode
              (binary_float.B754_finite s m e hbounded) =
              BSN2B (nearbyint_nan
                (binary_float.B754_finite s m e hbounded))
                (standardFloatToBinarySingleNaNFloat z hc.1) by
                simp [Bnearbyint, hsingle]]
          rw [is_finite_BSN2B,
            is_finite_standardFloatToBinarySingleNaNFloat]
          simpa [is_finite] using hc.2.2.1
        · intro _
          rw [show Bnearbyint nearbyint_nan mode
              (binary_float.B754_finite s m e hbounded) =
              BSN2B (nearbyint_nan
                (binary_float.B754_finite s m e hbounded))
                (standardFloatToBinarySingleNaNFloat z hc.1) by
                simp [Bnearbyint, hsingle]]
          rw [Bsign_BSN2B _ _ (by
            rw [is_nan_standardFloatToBinarySingleNaNFloat]
            exact hnotnan)]
          rw [Bsign_standardFloatToBinarySingleNaNFloat _ _ hnotnan]
          simpa [Bsign] using hc.2.2.2 hnotnan

noncomputable def BoneSingle {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    BinarySingleNaNFloat prec emax :=
  let z := _root_.binary_round (prec:=prec) (emax:=emax)
    RoundingMode.RNE false 1 0
  have hcorrect := _root_.binary_round_correct (prec:=prec) (emax:=emax)
    RoundingMode.RNE false 1 0 (by norm_num : 0 < (1 : Nat))
  standardFloatToBinarySingleNaNFloat z hcorrect.1

-- Coq `Binary.v:Bone`, obtained from the exact SingleNaN rounding algorithm.
noncomputable def Bone {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    binary_float prec emax :=
  BSN2B' (BoneSingle (prec:=prec) (emax:=emax)) (by
    let z := _root_.binary_round (prec:=prec) (emax:=emax)
      RoundingMode.RNE false 1 0
    have hn := is_nan_binary_round (prec:=prec) (emax:=emax)
      RoundingMode.RNE false 1 0
    rw [show BoneSingle (prec:=prec) (emax:=emax) =
        standardFloatToBinarySingleNaNFloat z
          (_root_.binary_round_correct (prec:=prec) (emax:=emax)
            RoundingMode.RNE false 1 0 (by norm_num : 0 < (1 : Nat))).1 by rfl]
    rw [is_nan_standardFloatToBinarySingleNaNFloat]
    exact hn)

private theorem roundR_FLT_one {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
      (rnd_of_mode RoundingMode.RNE) 1 = 1 := by
  have hfmtTrip := FloatSpec.Core.FLT.generic_format_FLT_1
    prec (3 - emax - prec) 2
  have hfmt : FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec) 1 := by
    simpa [wp, PostCond.noThrow, pure] using hfmtTrip
      ⟨by norm_num, by
        have hp := (inferInstance : Prec_gt_0 prec).pos
        have he := (inferInstance : Prec_lt_emax prec emax).emax_ge_2
        omega⟩
  exact FloatSpec.Core.Generic_fmt.roundR_generic 2
    (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RNE) 1
    (by norm_num) hfmt

private theorem one_lt_bpow_emax {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    (1 : ℝ) < FloatSpec.Core.Raux.bpow 2 emax := by
  have he := (inferInstance : Prec_lt_emax prec emax).emax_ge_2
  have h := FloatSpec.Core.Raux.bpow_lt 2 0 emax (by norm_num) (by omega)
  simpa [wp, PostCond.noThrow, pure, FloatSpec.Core.Raux.bpow_lt_check,
    FloatSpec.Core.Raux.bpow] using h trivial

theorem BoneSingle_value_finite_sign {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    B754_to_R (binarySingleNaNFloatToB754
        (BoneSingle (prec:=prec) (emax:=emax))) = 1 ∧
      BSN_is_finite (binarySingleNaNFloatToB754
        (BoneSingle (prec:=prec) (emax:=emax))) = true ∧
      BSN_sign (binarySingleNaNFloatToB754
        (BoneSingle (prec:=prec) (emax:=emax))) = false := by
  let z := _root_.binary_round (prec:=prec) (emax:=emax)
    RoundingMode.RNE false 1 0
  have hc := _root_.binary_round_correct (prec:=prec) (emax:=emax)
    RoundingMode.RNE false 1 0 (by norm_num : 0 < (1 : Nat))
  have hround := roundR_FLT_one (prec:=prec) (emax:=emax)
  have hlt : FloatSpec.Core.Raux.Rlt_bool
      |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
        (rnd_of_mode RoundingMode.RNE)
        (SF2R 2 (StandardFloat.S754_finite false 1 0))|
      (FloatSpec.Core.Raux.bpow 2 emax) = true := by
    simp [SF2R, F2R, FloatSpec.Core.Defs.F2R, hround,
      FloatSpec.Core.Raux.Rlt_bool, one_lt_bpow_emax (prec:=prec) (emax:=emax)]
  have hb := hc.2
  rw [ite_eq_left hlt] at hb
  have hn : is_nan_SF z = false := by
    have hf : is_finite_SF z = true := by simpa [z] using hb.2.1
    cases hz : z <;> simp [hz, is_finite_SF, is_nan_SF] at hf ⊢
  rw [show BoneSingle (prec:=prec) (emax:=emax) =
      standardFloatToBinarySingleNaNFloat z hc.1 by rfl]
  constructor
  · rw [B2R_standardFloatToBinarySingleNaNFloat]
    simpa [SF2R, F2R, FloatSpec.Core.Defs.F2R, hround] using hb.1
  · constructor
    · rw [is_finite_standardFloatToBinarySingleNaNFloat]
      exact hb.2.1
    · rw [Bsign_standardFloatToBinarySingleNaNFloat _ _ hn]
      exact hb.2.2

theorem Bone_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    B2R (Bone (prec:=prec) (emax:=emax)) = 1 := by
  rw [Bone, B2R_BSN2B']
  exact (BoneSingle_value_finite_sign (prec:=prec) (emax:=emax)).1

theorem is_finite_Bone {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    is_finite (Bone (prec:=prec) (emax:=emax)) = true := by
  rw [Bone, is_finite_BSN2B']
  exact (BoneSingle_value_finite_sign (prec:=prec) (emax:=emax)).2.1

theorem Bsign_Bone {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    Bsign (Bone (prec:=prec) (emax:=emax)) = false := by
  rw [Bone, Bsign_BSN2B']
  exact (BoneSingle_value_finite_sign (prec:=prec) (emax:=emax)).2.2

private theorem maxFloatMantissa_pos {prec : Int} [Prec_gt_0 prec] :
    0 < (2 : Nat) ^ prec.toNat - 1 := by
  have hp : prec.toNat ≠ 0 := by
    intro hz
    have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
    have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
    have hc : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprec_nonneg
    have hz' : (prec.toNat : Int) = 0 := by simp [hz]
    omega
  exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow hp)

def BmaxFloatSingle {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    BinarySingleNaNFloat prec emax :=
  let m := (2 : Nat) ^ prec.toNat - 1
  have hp := ExperimentalSingleNaNArithmetic.Bmax_float_proof
    (prec:=prec) (emax:=emax)
  BinarySingleNaNFloat.B754_finite false m (emax - prec)
    (maxFloatMantissa_pos (prec:=prec)) (by
      simp [specFloat_bounded, m, hp.2])

-- Coq `Binary.v:Bmax_float`.
def Bmax_float {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] : binary_float prec emax :=
  BSN2B' (BmaxFloatSingle (prec:=prec) (emax:=emax)) (by rfl)

-- Coq `Binary.v:Bnormfr_mantissa`.
def Bnormfr_mantissa {prec emax : Int} (x : binary_float prec emax) : Nat :=
  BinarySingleNaNFloat.Bnormfr_mantissa (B2BSN x)

theorem Bnormfr_mantissa_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax)
    (hx : (1 / 2 : ℝ) ≤ |B2R x| ∧ |B2R x| < 1) :
    match x with
    | binary_float.B754_finite _ m e _ =>
        Bnormfr_mantissa x = FloatSpec.Core.Zaux.positiveToNat m ∧
          FloatSpec.Core.Digits.digits2_pos
            (FloatSpec.Core.Zaux.positiveToNat m) = prec ∧
          e = -prec
    | _ => False := by
  have hs := _root_.Bnormfr_mantissa_correct
    (prec:=prec) (emax:=emax) (B2BSN x) (by
      simpa [SF2R_B2BSN] using hx)
  cases x with
  | B754_zero s => exact hs
  | B754_infinity s => exact hs
  | B754_nan s payload hpayload => exact hs
  | B754_finite s m e hbounded =>
      simpa [Bnormfr_mantissa, B2BSN, binaryFloatToBinarySingleNaNFloat]
        using hs

noncomputable def BldexpSingle {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : BinarySingleNaNFloat prec emax) (k : Int) :
    BinarySingleNaNFloat prec emax :=
  match x with
  | BinarySingleNaNFloat.B754_finite s m e hm _ =>
      let z := _root_.binary_round (prec:=prec) (emax:=emax) mode s m (e + k)
      have hcorrect := _root_.binary_round_correct (prec:=prec) (emax:=emax)
        mode s m (e + k) hm
      standardFloatToBinarySingleNaNFloat z hcorrect.1
  | x => x

theorem is_nan_BldexpSingle {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : BinarySingleNaNFloat prec emax) (k : Int) :
    is_nan_BSN (BldexpSingle mode x k) = is_nan_BSN x := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => rfl
  | B754_finite s m e hm hbounded =>
      let z := _root_.binary_round (prec:=prec) (emax:=emax) mode s m (e + k)
      have hn := is_nan_binary_round (prec:=prec) (emax:=emax) mode s m (e + k)
      have hcorrect := _root_.binary_round_correct (prec:=prec) (emax:=emax)
        mode s m (e + k) hm
      rw [show BldexpSingle mode
          (BinarySingleNaNFloat.B754_finite s m e hm hbounded) k =
          standardFloatToBinarySingleNaNFloat z hcorrect.1 by rfl]
      rw [is_nan_standardFloatToBinarySingleNaNFloat]
      exact hn

-- Coq `Binary.v:Bldexp`, preserving the original Binary NaN payload.
noncomputable def Bldexp {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : binary_float prec emax) (k : Int) :
    binary_float prec emax :=
  lift x (BldexpSingle mode (B2BSN x) k) (by
    rw [is_nan_BldexpSingle]
    cases x <;> rfl)

theorem Bldexp_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : binary_float prec emax) (k : Int) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
          (rnd_of_mode mode)
          (B2R x * FloatSpec.Core.Raux.bpow 2 k)|
        (FloatSpec.Core.Raux.bpow 2 emax) = true then
      B2R (Bldexp mode x k) =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
            (rnd_of_mode mode) (B2R x * FloatSpec.Core.Raux.bpow 2 k) ∧
        is_finite (Bldexp mode x k) = is_finite x ∧
        Bsign (Bldexp mode x k) = Bsign x
    else
      B2FF (Bldexp mode x k) =
        binary_overflow (prec:=prec) (emax:=emax) mode (Bsign x) := by
  have hround0 : FloatSpec.Core.Generic_fmt.roundR 2
      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) 0 = 0 := by
    simpa only [FloatSpec.Core.Generic_fmt.round_to_generic] using
      round_to_generic_rnd_of_mode_zero mode (FLT_exp (3 - emax - prec) prec)
  have hbpow_pos : 0 < FloatSpec.Core.Raux.bpow 2 emax := by
    have h := FloatSpec.Core.Raux.bpow_gt_0 2 emax (by norm_num)
    simpa [wp, PostCond.noThrow, pure] using h trivial
  cases x with
  | B754_zero s =>
      simp [Bldexp, BldexpSingle, lift, B2BSN, is_nan, B2R, is_finite,
        Bsign, binaryFloatToBinarySingleNaNFloat, hround0,
        FloatSpec.Core.Raux.Rlt_bool, hbpow_pos, BSN2B', is_nan_BSN, B2FF]
  | B754_infinity s =>
      simp [Bldexp, BldexpSingle, lift, B2BSN, is_nan, B2R, is_finite,
        Bsign, binaryFloatToBinarySingleNaNFloat, hround0,
        FloatSpec.Core.Raux.Rlt_bool, hbpow_pos, BSN2B', is_nan_BSN, B2FF]
  | B754_nan s payload hpayload =>
      simp [Bldexp, BldexpSingle, lift, B2BSN, is_nan, B2R, is_finite,
        Bsign, binaryFloatToBinarySingleNaNFloat, hround0,
        FloatSpec.Core.Raux.Rlt_bool, hbpow_pos, BSN2B', is_nan_BSN, B2FF]
  | B754_finite s m e hbounded =>
      let mn := FloatSpec.Core.Zaux.positiveToNat m
      have hm : 0 < mn := positiveToNat_pos_bsn m
      let z := _root_.binary_round (prec:=prec) (emax:=emax) mode s mn (e + k)
      have hc := _root_.binary_round_correct (prec:=prec) (emax:=emax)
        mode s mn (e + k) hm
      have hn : is_nan_SF z = false := by
        simpa [z] using is_nan_binary_round (prec:=prec) (emax:=emax)
          mode s mn (e + k)
      have hsingle : BldexpSingle mode
          (B2BSN (binary_float.B754_finite s m e hbounded)) k =
          standardFloatToBinarySingleNaNFloat z hc.1 := by rfl
      have hinput : SF2R 2 (StandardFloat.S754_finite s mn (e + k)) =
          B2R (binary_float.B754_finite s m e hbounded) *
            FloatSpec.Core.Raux.bpow 2 k := by
        have h2ne : (2 : ℝ) ≠ 0 := by norm_num
        cases s <;>
          simp [SF2R, B2R, F2R, FloatSpec.Core.Defs.F2R,
            FloatSpec.Core.Raux.bpow, mn] <;>
          rw [zpow_add₀ h2ne] <;> ring
      have hvalue : B2R (Bldexp mode
          (binary_float.B754_finite s m e hbounded) k) = SF2R 2 z := by
        rw [Bldexp, B2R_lift, hsingle,
          B2R_standardFloatToBinarySingleNaNFloat]
      have hfinite : is_finite (Bldexp mode
          (binary_float.B754_finite s m e hbounded) k) = is_finite_SF z := by
        rw [Bldexp, is_finite_lift, hsingle,
          is_finite_standardFloatToBinarySingleNaNFloat]
      have hsign : Bsign (Bldexp mode
          (binary_float.B754_finite s m e hbounded) k) = sign_SF z := by
        rw [Bldexp, Bsign_lift _ _ _ (by rfl), hsingle,
          Bsign_standardFloatToBinarySingleNaNFloat _ _ hn]
      have hfull : B2FF (Bldexp mode
          (binary_float.B754_finite s m e hbounded) k) = SF2FF z := by
        rw [Bldexp, B2FF_lift_of_not_nan _ _ _ (by rfl), hsingle,
          binarySingleNaNFloatToStandardFloat_standardFloatToBinarySingleNaNFloat]
      have hb := hc.2
      rw [hinput] at hb
      by_cases hlt : FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
            (rnd_of_mode mode)
            (B2R (binary_float.B754_finite s m e hbounded) *
              FloatSpec.Core.Raux.bpow 2 k)|
          (FloatSpec.Core.Raux.bpow 2 emax) = true
      · rw [ite_eq_left hlt] at hb ⊢
        exact ⟨hvalue.trans hb.1, hfinite.trans hb.2.1,
          hsign.trans (by simpa [Bsign] using hb.2.2)⟩
      · have hfalse := Bool.eq_false_of_not_eq_true hlt
        rw [ite_eq_right hlt] at hb ⊢
        have hbz : z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode s := by
          simpa [z] using hb
        rw [hfull, hbz]
        rfl

noncomputable def BfrexpSingle {prec emax : Int}
    [Prec_gt_0 prec] (x : BinarySingleNaNFloat prec emax) :
    BinarySingleNaNFloat prec emax × Int :=
  match x with
  | BinarySingleNaNFloat.B754_finite s m e hm hbounded =>
      let core := ExperimentalSingleNaNArithmetic.Ffrexp_core_binary
        (prec:=prec) (emax:=emax) s m e
      have hc := ExperimentalSingleNaNArithmetic.Bfrexp_correct_aux
        (prec:=prec) (emax:=emax) s m e hm hbounded
      (standardFloatToBinarySingleNaNFloat core.1 hc.1, core.2)
  | x => (x, -2 * emax - prec)

theorem is_nan_BfrexpSingle {prec emax : Int}
    [Prec_gt_0 prec] (x : BinarySingleNaNFloat prec emax) :
    is_nan_BSN (BfrexpSingle x).1 = is_nan_BSN x := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => rfl
  | B754_finite s m e hm hbounded =>
      let core := ExperimentalSingleNaNArithmetic.Ffrexp_core_binary
        (prec:=prec) (emax:=emax) s m e
      have hc := ExperimentalSingleNaNArithmetic.Bfrexp_correct_aux
        (prec:=prec) (emax:=emax) s m e hm hbounded
      rw [show (BfrexpSingle
          (BinarySingleNaNFloat.B754_finite s m e hm hbounded)).1 =
          standardFloatToBinarySingleNaNFloat core.1 hc.1 by rfl]
      rw [is_nan_standardFloatToBinarySingleNaNFloat]
      simp [core, ExperimentalSingleNaNArithmetic.Ffrexp_core_binary,
        is_nan_SF, is_nan_BSN]
      split_ifs <;> rfl

-- Coq `Binary.v:Bfrexp`, using the source three-branch decomposition and
-- preserving a Binary NaN's sign and payload through `lift`.
-- Source ID: IEEE754/Binary.v:Bfrexp:34504
noncomputable def Bfrexp {prec emax : Int}
    [Prec_gt_0 prec] (x : binary_float prec emax) :
    binary_float prec emax × Int :=
  let y := BfrexpSingle (B2BSN x)
  (lift x y.1 (by
    rw [is_nan_BfrexpSingle, is_nan_B2BSN]), y.2)

-- Source ID: IEEE754/Binary.v:Bfrexp_correct:34702
theorem Bfrexp_correct {prec emax : Int}
    [Prec_gt_0 prec]
    (hmax : 2 < emax) (f : binary_float prec emax)
    (hfinite : is_finite_strict f = true) :
    let x := B2R f
    let z := (Bfrexp f).1
    let e := (Bfrexp f).2
    (1 / 2 : ℝ) ≤ |B2R z| ∧ |B2R z| < 1 ∧
      x = B2R z * FloatSpec.Core.Raux.bpow 2 e ∧
      e = FloatSpec.Core.Raux.mag 2 x := by
  cases f with
  | B754_zero s => simp [is_finite_strict, binary_float.is_finite_strict] at hfinite
  | B754_infinity s =>
      simp [is_finite_strict, binary_float.is_finite_strict] at hfinite
  | B754_nan s payload hpayload =>
      simp [is_finite_strict, binary_float.is_finite_strict] at hfinite
  | B754_finite s m ex hbounded =>
      let mn := FloatSpec.Core.Zaux.positiveToNat m
      have hmn : 0 < mn := positiveToNat_pos_bsn m
      have hbounded' :
          specFloat_bounded (prec:=prec) (emax:=emax) mn ex = true := by
        simpa [mn] using hbounded
      let core := ExperimentalSingleNaNArithmetic.Ffrexp_core_binary
        (prec:=prec) (emax:=emax) s mn ex
      have hc := ExperimentalSingleNaNArithmetic.Bfrexp_correct_aux
        (prec:=prec) (emax:=emax) s mn ex hmn hbounded'
      have hnorm : (1 / 2 : ℝ) ≤ |SF2R 2 core.1| ∧
          |SF2R 2 core.1| < 1 := by
        simpa [core] using hc.2.1 hmax
      have hzNe : SF2R 2 core.1 ≠ 0 := by
        intro hz
        rw [hz, abs_zero] at hnorm
        norm_num at hnorm
      have hmagZero : FloatSpec.Core.Raux.mag 2 (SF2R 2 core.1) = 0 := by
        have hlow : (2 : ℝ) ^ ((0 : Int) - 1) ≤ |SF2R 2 core.1| := by
          norm_num
          exact hnorm.1
        have hupp : |SF2R 2 core.1| < (2 : ℝ) ^ (0 : Int) := by
          norm_num
          exact hnorm.2
        exact (FloatSpec.Core.Raux.mag_unique
          2 (SF2R 2 core.1) 0 (by norm_num) hlow hupp) trivial
      have hdecomp :
          SF2R 2 (StandardFloat.S754_finite s mn ex) =
            SF2R 2 core.1 * FloatSpec.Core.Raux.bpow 2 core.2 := by
        simpa [core] using hc.2.2
      have hmagMul := FloatSpec.Core.Raux.mag_mult_bpow
        2 (SF2R 2 core.1) core.2 (by norm_num) hzNe
      have hexpMag : core.2 = FloatSpec.Core.Raux.mag 2
          (SF2R 2 (StandardFloat.S754_finite s mn ex)) := by
        have hmagEq : FloatSpec.Core.Raux.mag 2
            (SF2R 2 (StandardFloat.S754_finite s mn ex)) =
              FloatSpec.Core.Raux.mag 2 (SF2R 2 core.1) + core.2 := by
          rw [hdecomp]
          simpa [FloatSpec.Core.Raux.bpow] using hmagMul
        rw [hmagZero] at hmagEq
        omega
      have hresultValue : B2R
          ((Bfrexp
            (binary_float.B754_finite s m ex hbounded)).1) = SF2R 2 core.1 := by
        simp only [Bfrexp, BfrexpSingle, B2BSN,
          binaryFloatToBinarySingleNaNFloat, core, Prod.fst]
        rw [B2R_lift, B2R_standardFloatToBinarySingleNaNFloat]
      have hresultExp :
          (Bfrexp
            (binary_float.B754_finite s m ex hbounded)).2 = core.2 := by
        rfl
      have hinputValue : B2R
          (binary_float.B754_finite s m ex hbounded) =
            SF2R 2 (StandardFloat.S754_finite s mn ex) := by
        rfl
      dsimp only
      rw [hresultValue, hresultExp, hinputValue]
      exact ⟨hnorm.1, hnorm.2, hdecomp, hexpMag⟩

private def BoppSingle {prec emax : Int} :
    BinarySingleNaNFloat prec emax → BinarySingleNaNFloat prec emax
  | BinarySingleNaNFloat.B754_zero s =>
      BinarySingleNaNFloat.B754_zero (!s)
  | BinarySingleNaNFloat.B754_infinity s =>
      BinarySingleNaNFloat.B754_infinity (!s)
  | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_finite s m e hm hbounded =>
      BinarySingleNaNFloat.B754_finite (!s) m e hm hbounded

private theorem is_nan_BoppSingle {prec emax : Int}
    (x : BinarySingleNaNFloat prec emax) :
    is_nan_BSN (BoppSingle x) = is_nan_BSN x := by
  cases x <;> rfl

noncomputable def BsuccSingle {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    BinarySingleNaNFloat prec emax → BinarySingleNaNFloat prec emax
  | BinarySingleNaNFloat.B754_zero _ =>
      BinarySingleNaNFloat.B754_finite false 1 (3 - emax - prec)
        (by norm_num) (specFloat_bounded_one_emin (prec:=prec) (emax:=emax))
  | x@(BinarySingleNaNFloat.B754_infinity false) => x
  | BinarySingleNaNFloat.B754_infinity true =>
      BoppSingle (BmaxFloatSingle (prec:=prec) (emax:=emax))
  | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_finite false m e hm _ =>
      let z := _root_.binary_round (prec:=prec) (emax:=emax)
        RoundingMode.RTP false (m + 1) e
      have hc := _root_.binary_round_correct (prec:=prec) (emax:=emax)
        RoundingMode.RTP false (m + 1) e (by omega)
      standardFloatToBinarySingleNaNFloat z hc.1
  | BinarySingleNaNFloat.B754_finite true m e hm _ =>
      let m' := 2 * m - 1
      have hm' : 0 < m' := by omega
      let z := _root_.binary_round (prec:=prec) (emax:=emax)
        RoundingMode.RTZ true m' (e - 1)
      have hc := _root_.binary_round_correct (prec:=prec) (emax:=emax)
        RoundingMode.RTZ true m' (e - 1) hm'
      standardFloatToBinarySingleNaNFloat z hc.1

theorem is_nan_BsuccSingle {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : BinarySingleNaNFloat prec emax) :
    is_nan_BSN (BsuccSingle x) = is_nan_BSN x := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => cases s <;> rfl
  | B754_nan => rfl
  | B754_finite s m e hm hbounded =>
      cases s
      · let z := _root_.binary_round (prec:=prec) (emax:=emax)
          RoundingMode.RTP false (m + 1) e
        have hc := _root_.binary_round_correct (prec:=prec) (emax:=emax)
          RoundingMode.RTP false (m + 1) e (by omega)
        rw [show BsuccSingle
            (BinarySingleNaNFloat.B754_finite false m e hm hbounded) =
            standardFloatToBinarySingleNaNFloat z hc.1 by rfl]
        rw [is_nan_standardFloatToBinarySingleNaNFloat]
        exact is_nan_binary_round (prec:=prec) (emax:=emax)
          RoundingMode.RTP false (m + 1) e
      · let m' := 2 * m - 1
        have hm' : 0 < m' := by omega
        let z := _root_.binary_round (prec:=prec) (emax:=emax)
          RoundingMode.RTZ true m' (e - 1)
        have hc := _root_.binary_round_correct (prec:=prec) (emax:=emax)
          RoundingMode.RTZ true m' (e - 1) hm'
        rw [show BsuccSingle
            (BinarySingleNaNFloat.B754_finite true m e hm hbounded) =
            standardFloatToBinarySingleNaNFloat z hc.1 by rfl]
        rw [is_nan_standardFloatToBinarySingleNaNFloat]
        exact is_nan_binary_round (prec:=prec) (emax:=emax)
          RoundingMode.RTZ true m' (e - 1)

-- Coq `Binary.v:Bsucc`, preserving the source NaN when present.
noncomputable def Bsucc {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) : binary_float prec emax :=
  lift x (BsuccSingle (B2BSN x)) (by
    rw [is_nan_BsuccSingle, is_nan_B2BSN])

noncomputable def BpredSingle {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : BinarySingleNaNFloat prec emax) : BinarySingleNaNFloat prec emax :=
  BoppSingle (BsuccSingle (BoppSingle x))

theorem is_nan_BpredSingle {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : BinarySingleNaNFloat prec emax) :
    is_nan_BSN (BpredSingle x) = is_nan_BSN x := by
  simp only [BpredSingle, is_nan_BoppSingle, is_nan_BsuccSingle]

-- Coq `Binary.v:Bpred`, preserving the source NaN when present.
noncomputable def Bpred {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) : binary_float prec emax :=
  lift x (BpredSingle (B2BSN x)) (by
    rw [is_nan_BpredSingle, is_nan_B2BSN])

private theorem binarySingleNaNFloatToB754_of_is_nan {prec emax : Int}
    (x : binary_float prec emax)
    (hx : is_nan (prec:=prec) (emax:=emax) x = true) :
    binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
        (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x) =
      B754.B754_nan := by
  cases x <;>
    simp [is_nan, binaryFloatToBinarySingleNaNFloat,
      binarySingleNaNFloatToB754] at hx ⊢

noncomputable def Bplus {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (plus_nan : BplusNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax) :
    binary_float prec emax :=
  match x, y with
  | binary_float.B754_nan _ _ _, _ => (plus_nan x y).1
  | _, binary_float.B754_nan _ _ _ => (plus_nan x y).1
  | binary_float.B754_infinity sx, binary_float.B754_infinity sy =>
      if sx == sy then x else (plus_nan x y).1
  | binary_float.B754_infinity _, _ => x
  | _, binary_float.B754_infinity _ => y
  | binary_float.B754_zero sx, binary_float.B754_zero sy =>
      if sx == sy then x
      else
        match mode with
        | RoundingMode.RTN => binary_float.B754_zero (prec:=prec) (emax:=emax) true
        | _ => binary_float.B754_zero (prec:=prec) (emax:=emax) false
  | binary_float.B754_zero _, _ => y
  | _, binary_float.B754_zero _ => x
  | binary_float.B754_finite sx mx ex Hx, binary_float.B754_finite sy my ey Hy =>
      let mxn := FloatSpec.Core.Zaux.positiveToNat mx
      let myn := FloatSpec.Core.Zaux.positiveToNat my
      let ez := min ex ey
      let m := Fplus_naive sx mxn ex sy myn ey ez
      let szero :=
        match mode with
        | RoundingMode.RTN => true
        | _ => false
      if hm0 : m = 0 then
        binary_float.B754_zero (prec:=prec) (emax:=emax) szero
      else if hmpos : 0 < m then
        let z := binary_round (prec:=prec) (emax:=emax) mode false m.toNat ez
        have hmpos_nat : 0 < m.toNat := by
          have hcast : ((m.toNat : Nat) : Int) = m := Int.toNat_of_nonneg (le_of_lt hmpos)
          omega
        have hround := binary_round_correct (prec:=prec) (emax:=emax)
          mode false m.toNat ez hmpos_nat
        have hnotnan : is_nan_SF z = false := by
          simpa [z] using
            is_nan_binary_round (prec:=prec) (emax:=emax) mode false m.toNat ez
        standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax) z hround.1 hnotnan
      else
        let z := binary_round (prec:=prec) (emax:=emax) mode true m.natAbs ez
        have hmneg : m < 0 := lt_of_le_of_ne (le_of_not_gt hmpos) hm0
        have hmabs_pos : 0 < m.natAbs := Int.natAbs_pos.mpr (ne_of_lt hmneg)
        have hround := binary_round_correct (prec:=prec) (emax:=emax)
          mode true m.natAbs ez hmabs_pos
        have hnotnan : is_nan_SF z = false := by
          simpa [z] using
            is_nan_binary_round (prec:=prec) (emax:=emax) mode true m.natAbs ez
        standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax) z hround.1 hnotnan

theorem binarySingleNaNFloatToB754_Bplus {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (plus_nan : BplusNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax) :
    binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
        (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
          (Bplus (prec:=prec) (emax:=emax) plus_nan mode x y)) =
      ExperimentalSingleNaNArithmetic.Bplus (prec:=prec) (emax:=emax) mode
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
          (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x))
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
          (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) y)) := by
  cases x with
  | B754_zero sx =>
      cases y with
      | B754_zero sy =>
          by_cases hs : sx = sy
          · simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus, hs,
              binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754]
          · cases mode <;>
              simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus, hs,
                binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754]
      | B754_infinity sy =>
          simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754]
      | B754_nan sy payload hpayload =>
          have hnan := binarySingleNaNFloatToB754_of_is_nan
            (prec:=prec) (emax:=emax)
            (plus_nan (binary_float.B754_zero (prec:=prec) (emax:=emax) sx)
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sy payload hpayload)).1
            (plus_nan (binary_float.B754_zero (prec:=prec) (emax:=emax) sx)
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sy payload hpayload)).2
          simpa [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754] using hnan
      | B754_finite sy my ey Hy =>
          simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754]
  | B754_infinity sx =>
      cases y with
      | B754_zero sy =>
          simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754]
      | B754_infinity sy =>
          by_cases hs : sx = sy
          · simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus, hs,
              binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754]
          · have hnan := binarySingleNaNFloatToB754_of_is_nan
              (prec:=prec) (emax:=emax)
              (plus_nan
                (binary_float.B754_infinity (prec:=prec) (emax:=emax) sx)
                (binary_float.B754_infinity (prec:=prec) (emax:=emax) sy)).1
              (plus_nan
                (binary_float.B754_infinity (prec:=prec) (emax:=emax) sx)
                (binary_float.B754_infinity (prec:=prec) (emax:=emax) sy)).2
            simpa [Bplus, ExperimentalSingleNaNArithmetic.Bplus, hs,
              binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754] using hnan
      | B754_nan sy payload hpayload =>
          have hnan := binarySingleNaNFloatToB754_of_is_nan
            (prec:=prec) (emax:=emax)
            (plus_nan
              (binary_float.B754_infinity (prec:=prec) (emax:=emax) sx)
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sy payload hpayload)).1
            (plus_nan
              (binary_float.B754_infinity (prec:=prec) (emax:=emax) sx)
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sy payload hpayload)).2
          simpa [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754] using hnan
      | B754_finite sy my ey Hy =>
          simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754]
  | B754_nan sx payload hpayload =>
      cases y with
      | B754_zero sy =>
          have hnan := binarySingleNaNFloatToB754_of_is_nan
            (prec:=prec) (emax:=emax)
            (plus_nan
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hpayload)
              (binary_float.B754_zero (prec:=prec) (emax:=emax) sy)).1
            (plus_nan
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hpayload)
              (binary_float.B754_zero (prec:=prec) (emax:=emax) sy)).2
          simpa [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754] using hnan
      | B754_infinity sy =>
          have hnan := binarySingleNaNFloatToB754_of_is_nan
            (prec:=prec) (emax:=emax)
            (plus_nan
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hpayload)
              (binary_float.B754_infinity (prec:=prec) (emax:=emax) sy)).1
            (plus_nan
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hpayload)
              (binary_float.B754_infinity (prec:=prec) (emax:=emax) sy)).2
          simpa [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754] using hnan
      | B754_nan sy payloadY hpayloadY =>
          have hnan := binarySingleNaNFloatToB754_of_is_nan
            (prec:=prec) (emax:=emax)
            (plus_nan
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hpayload)
              (binary_float.B754_nan (prec:=prec) (emax:=emax)
                sy payloadY hpayloadY)).1
            (plus_nan
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hpayload)
              (binary_float.B754_nan (prec:=prec) (emax:=emax)
                sy payloadY hpayloadY)).2
          simpa [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754] using hnan
      | B754_finite sy my ey Hy =>
          have hnan := binarySingleNaNFloatToB754_of_is_nan
            (prec:=prec) (emax:=emax)
            (plus_nan
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hpayload)
              (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)).1
            (plus_nan
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hpayload)
              (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)).2
          simpa [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754] using hnan
  | B754_finite sx mx ex Hx =>
      cases y with
      | B754_zero sy =>
          simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754]
      | B754_infinity sy =>
          simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754]
      | B754_nan sy payload hpayload =>
          have hnan := binarySingleNaNFloatToB754_of_is_nan
            (prec:=prec) (emax:=emax)
            (plus_nan
              (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sy payload hpayload)).1
            (plus_nan
              (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sy payload hpayload)).2
          simpa [Bplus, ExperimentalSingleNaNArithmetic.Bplus,
            binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754] using hnan
      | B754_finite sy my ey Hy =>
          let mxn := FloatSpec.Core.Zaux.positiveToNat mx
          let myn := FloatSpec.Core.Zaux.positiveToNat my
          let ez := min ex ey
          let m := Fplus_naive sx mxn ex sy myn ey ez
          let szero :=
            match mode with
            | RoundingMode.RTN => true
            | _ => false
          by_cases hm0 : m = 0
          · simp [Bplus, ExperimentalSingleNaNArithmetic.Bplus, binary_normalize,
              binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754,
              mxn, myn, ez, m, szero, hm0]
          · by_cases hmpos : 0 < m
            · let z := binary_round (prec:=prec) (emax:=emax) mode false m.toNat ez
              have hmpos_nat : 0 < m.toNat := by
                have hcast : ((m.toNat : Nat) : Int) = m :=
                  Int.toNat_of_nonneg (le_of_lt hmpos)
                omega
              have hround := binary_round_correct (prec:=prec) (emax:=emax)
                mode false m.toNat ez hmpos_nat
              have hnotnan : is_nan_SF z = false := by
                simpa [z] using
                  is_nan_binary_round (prec:=prec) (emax:=emax)
                    mode false m.toNat ez
              have hstd := binarySingleNaNFloatToB754_standardFloatToBinaryFloatOfNotNaN
                (prec:=prec) (emax:=emax) z hround.1 hnotnan
              simpa [Bplus, ExperimentalSingleNaNArithmetic.Bplus, binary_normalize,
                binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754,
                mxn, myn, ez, m, szero, hm0, hmpos, z] using hstd
            · have hmneg : m < 0 := lt_of_le_of_ne (le_of_not_gt hmpos) hm0
              let z := binary_round (prec:=prec) (emax:=emax) mode true m.natAbs ez
              have hmabs_pos : 0 < m.natAbs :=
                Int.natAbs_pos.mpr (ne_of_lt hmneg)
              have hround := binary_round_correct (prec:=prec) (emax:=emax)
                mode true m.natAbs ez hmabs_pos
              have hnotnan : is_nan_SF z = false := by
                simpa [z] using
                  is_nan_binary_round (prec:=prec) (emax:=emax)
                    mode true m.natAbs ez
              have hstd := binarySingleNaNFloatToB754_standardFloatToBinaryFloatOfNotNaN
                (prec:=prec) (emax:=emax) z hround.1 hnotnan
              simpa [Bplus, ExperimentalSingleNaNArithmetic.Bplus, binary_normalize,
                binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754,
                mxn, myn, ez, m, szero, hm0, hmpos, z] using hstd

-- Coq: Binary.v:Bminus
-- Upstream defines this by subtracting through the SingleNaN operation and
-- lifting NaN results with the original `(x, y)` payload handler.
noncomputable def Bminus {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (minus_nan : BminusNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax) :
    binary_float prec emax :=
  match x, y with
  | binary_float.B754_nan _ _ _, _ => (minus_nan x y).1
  | _, binary_float.B754_nan _ _ _ => (minus_nan x y).1
  | binary_float.B754_infinity sx, binary_float.B754_infinity sy =>
      if sx == (!sy) then x else (minus_nan x y).1
  | binary_float.B754_infinity _, _ => x
  | _, binary_float.B754_infinity sy =>
      binary_float.B754_infinity (prec:=prec) (emax:=emax) (!sy)
  | binary_float.B754_zero sx, binary_float.B754_zero sy =>
      if sx == (!sy) then x
      else
        match mode with
        | RoundingMode.RTN => binary_float.B754_zero (prec:=prec) (emax:=emax) true
        | _ => binary_float.B754_zero (prec:=prec) (emax:=emax) false
  | binary_float.B754_zero _, _ => Bopp_preserve_nan y
  | _, binary_float.B754_zero _ => x
  | binary_float.B754_finite sx mx ex _,
      binary_float.B754_finite sy my ey _ =>
      let mxn := FloatSpec.Core.Zaux.positiveToNat mx
      let myn := FloatSpec.Core.Zaux.positiveToNat my
      let ez := min ex ey
      let m := Fplus_naive sx mxn ex (!sy) myn ey ez
      let szero :=
        match mode with
        | RoundingMode.RTN => true
        | _ => false
      if hm0 : m = 0 then
        binary_float.B754_zero (prec:=prec) (emax:=emax) szero
      else if hmpos : 0 < m then
        let z := binary_round (prec:=prec) (emax:=emax) mode false m.toNat ez
        have hmpos_nat : 0 < m.toNat := by
          have hcast : ((m.toNat : Nat) : Int) = m := Int.toNat_of_nonneg (le_of_lt hmpos)
          omega
        have hround := binary_round_correct (prec:=prec) (emax:=emax)
          mode false m.toNat ez hmpos_nat
        have hnotnan : is_nan_SF z = false := by
          simpa [z] using
            is_nan_binary_round (prec:=prec) (emax:=emax) mode false m.toNat ez
        standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax) z hround.1 hnotnan
      else
        let z := binary_round (prec:=prec) (emax:=emax) mode true m.natAbs ez
        have hmneg : m < 0 := lt_of_le_of_ne (le_of_not_gt hmpos) hm0
        have hmabs_pos : 0 < m.natAbs := Int.natAbs_pos.mpr (ne_of_lt hmneg)
        have hround := binary_round_correct (prec:=prec) (emax:=emax)
          mode true m.natAbs ez hmabs_pos
        have hnotnan : is_nan_SF z = false := by
          simpa [z] using
            is_nan_binary_round (prec:=prec) (emax:=emax) mode true m.natAbs ez
        standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax) z hround.1 hnotnan

theorem Bminus_eq_Bplus_Bopp {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (minus_nan : BminusNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax) :
    let plus_nan : BplusNaNHandler prec emax := fun _ _ => minus_nan x y
    Bminus minus_nan mode x y = Bplus plus_nan mode x (Bopp_preserve_nan y) := by
  dsimp
  cases x <;> cases y <;> cases mode <;>
    simp [Bminus, Bplus, Bopp_preserve_nan, Bool.xor]

noncomputable def Bmult {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mult_nan : BmultNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax) :
    binary_float prec emax :=
  match x, y with
  | binary_float.B754_nan _ _ _, _ => (mult_nan x y).1
  | _, binary_float.B754_nan _ _ _ => (mult_nan x y).1
  | binary_float.B754_infinity sx, binary_float.B754_infinity sy =>
      binary_float.B754_infinity (prec:=prec) (emax:=emax) (Bool.xor sx sy)
  | binary_float.B754_infinity sx, binary_float.B754_finite sy _ _ _ =>
      binary_float.B754_infinity (prec:=prec) (emax:=emax) (Bool.xor sx sy)
  | binary_float.B754_finite sx _ _ _, binary_float.B754_infinity sy =>
      binary_float.B754_infinity (prec:=prec) (emax:=emax) (Bool.xor sx sy)
  | binary_float.B754_infinity _, binary_float.B754_zero _ => (mult_nan x y).1
  | binary_float.B754_zero _, binary_float.B754_infinity _ => (mult_nan x y).1
  | binary_float.B754_finite sx _ _ _, binary_float.B754_zero sy =>
      binary_float.B754_zero (prec:=prec) (emax:=emax) (Bool.xor sx sy)
  | binary_float.B754_zero sx, binary_float.B754_finite sy _ _ _ =>
      binary_float.B754_zero (prec:=prec) (emax:=emax) (Bool.xor sx sy)
  | binary_float.B754_zero sx, binary_float.B754_zero sy =>
      binary_float.B754_zero (prec:=prec) (emax:=emax) (Bool.xor sx sy)
  | binary_float.B754_finite sx mx ex Hx, binary_float.B754_finite sy my ey Hy =>
      let mxn := FloatSpec.Core.Zaux.positiveToNat mx
      let myn := FloatSpec.Core.Zaux.positiveToNat my
      let z := binary_round_aux (prec:=prec) (emax:=emax) mode
        (Bool.xor sx sy) ((mxn * myn : Nat) : Int) (ex + ey)
        FloatSpec.Calc.Bracket.Location.loc_Exact
      have haux := Bmult_correct_aux (prec:=prec) (emax:=emax)
        mode sx mxn ex (positiveToNat_pos_bsn mx) Hx
        sy myn ey (positiveToNat_pos_bsn my) Hy
      have hnotnan : is_nan_SF z = false := by
        classical
        by_cases hlt :
            FloatSpec.Core.Raux.Rlt_bool
              |FloatSpec.Core.Generic_fmt.roundR 2
                (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                  ((SF2R 2 (StandardFloat.S754_finite sx mxn ex)) *
                   (SF2R 2 (StandardFloat.S754_finite sy myn ey)))|
              (FloatSpec.Core.Raux.bpow 2 emax) = true
        · have hfinite : is_finite_SF z = true := by
            have hbranch := haux.2
            simp [mxn, myn, hlt] at hbranch
            exact hbranch.2.1
          cases hz : z <;> simp [hz, is_nan_SF, is_finite_SF] at hfinite ⊢
        · have hover : z =
              bsn_binary_overflow (prec:=prec) (emax:=emax) mode (Bool.xor sx sy) := by
            have hlt_false :
                FloatSpec.Core.Raux.Rlt_bool
                  |FloatSpec.Core.Generic_fmt.roundR 2
                    (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                      ((SF2R 2 (StandardFloat.S754_finite sx mxn ex)) *
                       (SF2R 2 (StandardFloat.S754_finite sy myn ey)))|
                  (FloatSpec.Core.Raux.bpow 2 emax) = false :=
              Bool.eq_false_of_not_eq_true hlt
            have hbranch := haux.2
            simpa [z, mxn, myn, hlt_false] using hbranch
          rw [hover]
          exact is_nan_binary_overflow (prec:=prec) (emax:=emax) mode (Bool.xor sx sy)
      standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax) z haux.1 hnotnan

-- Coq: `Binary.v:Bdiv`.
noncomputable def Bdiv {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (div_nan : BdivNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax) :
    binary_float prec emax :=
  match x, y with
  | binary_float.B754_nan _ _ _, _ => (div_nan x y).1
  | _, binary_float.B754_nan _ _ _ => (div_nan x y).1
  | binary_float.B754_infinity _, binary_float.B754_infinity _ => (div_nan x y).1
  | binary_float.B754_infinity sx, binary_float.B754_finite sy _ _ _ =>
      binary_float.B754_infinity (prec:=prec) (emax:=emax) (Bool.xor sx sy)
  | binary_float.B754_finite sx _ _ _, binary_float.B754_infinity sy =>
      binary_float.B754_zero (prec:=prec) (emax:=emax) (Bool.xor sx sy)
  | binary_float.B754_infinity sx, binary_float.B754_zero sy =>
      binary_float.B754_infinity (prec:=prec) (emax:=emax) (Bool.xor sx sy)
  | binary_float.B754_zero sx, binary_float.B754_infinity sy =>
      binary_float.B754_zero (prec:=prec) (emax:=emax) (Bool.xor sx sy)
  | binary_float.B754_finite sx _ _ _, binary_float.B754_zero sy =>
      binary_float.B754_infinity (prec:=prec) (emax:=emax) (Bool.xor sx sy)
  | binary_float.B754_zero sx, binary_float.B754_finite sy _ _ _ =>
      binary_float.B754_zero (prec:=prec) (emax:=emax) (Bool.xor sx sy)
  | binary_float.B754_zero _, binary_float.B754_zero _ => (div_nan x y).1
  | binary_float.B754_finite sx mx ex _, binary_float.B754_finite sy my ey _ =>
      let mxn := FloatSpec.Core.Zaux.positiveToNat mx
      let myn := FloatSpec.Core.Zaux.positiveToNat my
      let result := SFdiv_core_binary prec emax (mxn : Int) ex (myn : Int) ey
      let z := binary_round_aux (prec:=prec) (emax:=emax) mode
        (Bool.xor sx sy) result.1 result.2.1 result.2.2
      have haux := Bdiv_correct_aux (prec:=prec) (emax:=emax)
        mode sx mx ex sy my ey
      have hnotnan : is_nan_SF z = false := by
        classical
        by_cases hlt :
            FloatSpec.Core.Raux.Rlt_bool
              |FloatSpec.Core.Generic_fmt.roundR 2
                (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                  ((SF2R 2 (StandardFloat.S754_finite sx mxn ex)) /
                   (SF2R 2 (StandardFloat.S754_finite sy myn ey)))|
              (FloatSpec.Core.Raux.bpow 2 emax) = true
        · have hfinite : is_finite_SF z = true := by
            have hbranch := haux.2
            simp [mxn, myn, result, z, hlt] at hbranch
            exact hbranch.2.1
          cases hz : z <;> simp [hz, is_nan_SF, is_finite_SF] at hfinite ⊢
        · have hover : z =
              bsn_binary_overflow (prec:=prec) (emax:=emax) mode
                (Bool.xor sx sy) := by
            have hlt_false :
                FloatSpec.Core.Raux.Rlt_bool
                  |FloatSpec.Core.Generic_fmt.roundR 2
                    (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                      ((SF2R 2 (StandardFloat.S754_finite sx mxn ex)) /
                       (SF2R 2 (StandardFloat.S754_finite sy myn ey)))|
                  (FloatSpec.Core.Raux.bpow 2 emax) = false :=
              Bool.eq_false_of_not_eq_true hlt
            have hbranch := haux.2
            simpa [mxn, myn, result, z, hlt_false] using hbranch
          rw [hover]
          exact is_nan_binary_overflow (prec:=prec) (emax:=emax) mode
            (Bool.xor sx sy)
      standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax) z haux.1 hnotnan

-- Coq: `Binary.v:Bfma_szero`, on the proof-carrying Binary surface.
def Bfma_szero {prec emax : Int} (mode : RoundingMode)
    (x y z : binary_float prec emax) : Bool :=
  let sxy := Bool.xor (Bsign (prec:=prec) (emax:=emax) x)
    (Bsign (prec:=prec) (emax:=emax) y)
  if sxy == Bsign (prec:=prec) (emax:=emax) z then sxy
  else
    match mode with
    | RoundingMode.RTN => true
    | _ => false

noncomputable def normalize {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (m e : Int) (szero : Bool) :
    binary_float prec emax :=
  if hm0 : m = 0 then
    binary_float.B754_zero (prec:=prec) (emax:=emax) szero
  else if hmpos : 0 < m then
    let z := binary_round (prec:=prec) (emax:=emax) mode false m.toNat e
    have hmpos_nat : 0 < m.toNat := by
      have hcast : ((m.toNat : Nat) : Int) = m :=
        Int.toNat_of_nonneg (le_of_lt hmpos)
      omega
    have hround := binary_round_correct (prec:=prec) (emax:=emax)
      mode false m.toNat e hmpos_nat
    have hnotnan : is_nan_SF z = false := by
      simpa [z] using
        is_nan_binary_round (prec:=prec) (emax:=emax) mode false m.toNat e
    standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax) z hround.1 hnotnan
  else
    let z := binary_round (prec:=prec) (emax:=emax) mode true m.natAbs e
    have hmneg : m < 0 := lt_of_le_of_ne (le_of_not_gt hmpos) hm0
    have hmabs_pos : 0 < m.natAbs := Int.natAbs_pos.mpr (ne_of_lt hmneg)
    have hround := binary_round_correct (prec:=prec) (emax:=emax)
      mode true m.natAbs e hmabs_pos
    have hnotnan : is_nan_SF z = false := by
      simpa [z] using
        is_nan_binary_round (prec:=prec) (emax:=emax) mode true m.natAbs e
    standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax) z hround.1 hnotnan

theorem normalize_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (m e : Int) (szero : Bool) :
    let input := F2R
      (FloatSpec.Core.Defs.FlocqFloat.mk m e :
        FloatSpec.Core.Defs.FlocqFloat 2)
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) input|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (prec:=prec) (emax:=emax) (normalize mode m e szero) =
          FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) input ∧
        is_finite (prec:=prec) (emax:=emax) (normalize mode m e szero) = true ∧
        Bsign (prec:=prec) (emax:=emax) (normalize mode m e szero) =
          if input = 0 then szero else decide (input < 0)
    else
      B2FF (prec:=prec) (emax:=emax) (normalize mode m e szero) =
        binary_overflow (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool input 0) := by
  dsimp
  by_cases hm0 : m = 0
  · subst m
    have hbtrip := FloatSpec.Core.Raux.bpow_gt_0 2 emax (by norm_num)
    have hb : 0 < FloatSpec.Core.Raux.bpow 2 emax := by
      simpa [wp, PostCond.noThrow, pure] using hbtrip trivial
    have hlt : FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (F2R (FloatSpec.Core.Defs.FlocqFloat.mk 0 e :
              FloatSpec.Core.Defs.FlocqFloat 2))|
        (FloatSpec.Core.Raux.bpow 2 emax) = true := by
      simp [F2R, FloatSpec.Core.Defs.F2R, Binary.roundR_zero_of_mode,
        FloatSpec.Core.Raux.Rlt_bool, hb]
    have hzlt : FloatSpec.Core.Raux.Rlt_bool 0
        (FloatSpec.Core.Raux.bpow 2 emax) = true := by
      simp [FloatSpec.Core.Raux.Rlt_bool, hb]
    simp [normalize, F2R, FloatSpec.Core.Defs.F2R,
      Binary.roundR_zero_of_mode, B2R, is_finite, Bsign, hlt, hzlt]
  · by_cases hmpos : 0 < m
    · let mn := m.toNat
      have hmn_cast : (mn : Int) = m := Int.toNat_of_nonneg (le_of_lt hmpos)
      have hmn_pos : 0 < mn := by
        have : (0 : Int) < (mn : Int) := by simpa [hmn_cast] using hmpos
        exact_mod_cast this
      let z := binary_round (prec:=prec) (emax:=emax) mode false mn e
      have hround := binary_round_correct (prec:=prec) (emax:=emax)
        mode false mn e hmn_pos
      have hnotnan : is_nan_SF z = false := by
        simpa [z] using
          is_nan_binary_round (prec:=prec) (emax:=emax) mode false mn e
      have hB2R : B2R (prec:=prec) (emax:=emax)
            (standardFloatToBinaryFloatOfNotNaN
              (prec:=prec) (emax:=emax) z hround.1 hnotnan) = SF2R 2 z :=
        B2R_standardFloatToBinaryFloatOfNotNaN z hround.1 hnotnan
      have hfinite : is_finite (prec:=prec) (emax:=emax)
            (standardFloatToBinaryFloatOfNotNaN
              (prec:=prec) (emax:=emax) z hround.1 hnotnan) = is_finite_SF z :=
        is_finite_standardFloatToBinaryFloatOfNotNaN z hround.1 hnotnan
      have hsign : Bsign (prec:=prec) (emax:=emax)
            (standardFloatToBinaryFloatOfNotNaN
              (prec:=prec) (emax:=emax) z hround.1 hnotnan) = sign_SF z :=
        Bsign_standardFloatToBinaryFloatOfNotNaN z hround.1 hnotnan
      have hB2FF : B2FF (prec:=prec) (emax:=emax)
            (standardFloatToBinaryFloatOfNotNaN
              (prec:=prec) (emax:=emax) z hround.1 hnotnan) = SF2FF z :=
        B2FF_standardFloatToBinaryFloatOfNotNaN z hround.1 hnotnan
      have hinput_pos : 0 < F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk m e :
            FloatSpec.Core.Defs.FlocqFloat 2) :=
        FloatSpec.Core.Float_prop.F2R_gt_0 (beta:=2)
          (f:=FloatSpec.Core.Defs.FlocqFloat.mk m e) (by norm_num) hmpos
      have hinput : SF2R 2 (StandardFloat.S754_finite false mn e) =
          F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
            FloatSpec.Core.Defs.FlocqFloat 2) := by
        simp [SF2R, hmn_cast]
      by_cases hlt : FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
              (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
                FloatSpec.Core.Defs.FlocqFloat 2))|
          (FloatSpec.Core.Raux.bpow 2 emax) = true
      · have hltProp :
            |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                ((m : ℝ) * (2 : ℝ) ^ e)| <
              FloatSpec.Core.Raux.bpow 2 emax := by
          simpa [FloatSpec.Core.Raux.Rlt_bool, F2R,
            FloatSpec.Core.Defs.F2R] using hlt
        simp only [F2R, FloatSpec.Core.Defs.F2R] at hlt
        rw [ite_eq_left hlt]
        have hbranch := hround.2
        have hlt' : FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                (SF2R 2 (StandardFloat.S754_finite false mn e))|
            (FloatSpec.Core.Raux.bpow 2 emax) = true := by simpa [hinput] using hlt
        simp [hlt'] at hbranch
        have hpowNe : (2 : ℝ) ^ e ≠ 0 := zpow_ne_zero e (by norm_num)
        have hinputPosRaw : 0 < (m : ℝ) * (2 : ℝ) ^ e := by
          simpa [F2R, FloatSpec.Core.Defs.F2R] using hinput_pos
        simpa [normalize, hm0, hmpos, mn, z, hB2R, hfinite, hsign,
          hinput, hltProp, hpowNe, ne_of_gt hinput_pos, hinputPosRaw,
          FloatSpec.Core.Raux.Rlt_bool, not_lt.mpr (le_of_lt hinputPosRaw)] using hbranch
      · have hnotltProp :
            ¬ |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                ((m : ℝ) * (2 : ℝ) ^ e)| <
              FloatSpec.Core.Raux.bpow 2 emax := by
          simpa [FloatSpec.Core.Raux.Rlt_bool, F2R,
            FloatSpec.Core.Defs.F2R] using hlt
        simp only [F2R, FloatSpec.Core.Defs.F2R] at hlt
        rw [ite_eq_right hlt]
        have hbranch := hround.2
        have hlt' : FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                (SF2R 2 (StandardFloat.S754_finite false mn e))|
            (FloatSpec.Core.Raux.bpow 2 emax) = false := by
          simpa [hinput] using Bool.eq_false_of_not_eq_true hlt
        simp [hlt'] at hbranch
        have hinputPosRaw : 0 < (m : ℝ) * (2 : ℝ) ^ e := by
          simpa [F2R, FloatSpec.Core.Defs.F2R] using hinput_pos
        calc
          B2FF (normalize (prec:=prec) (emax:=emax) mode m e szero) = SF2FF z := by
            simpa [normalize, hm0, hmpos, mn, z] using hB2FF
          _ = SF2FF (bsn_binary_overflow (prec:=prec) (emax:=emax) mode false) := by
            rw [show z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode false by
              simpa [z] using hbranch]
          _ = binary_overflow (prec:=prec) (emax:=emax) mode
              (FloatSpec.Core.Raux.Rlt_bool
                (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
                  FloatSpec.Core.Defs.FlocqFloat 2)) 0) := by
            simp [binary_overflow, FloatSpec.Core.Raux.Rlt_bool, F2R,
              FloatSpec.Core.Defs.F2R, not_lt.mpr (le_of_lt hinputPosRaw)]
    · have hmneg : m < 0 := lt_of_le_of_ne (le_of_not_gt hmpos) hm0
      let mn := m.natAbs
      have hmn_pos : 0 < mn := Int.natAbs_pos.mpr (ne_of_lt hmneg)
      have hmn_cast : (mn : Int) = -m := by
        rw [show (mn : Int) = |m| by simpa [mn] using Int.natCast_natAbs m,
          abs_of_nonpos (le_of_lt hmneg)]
      let z := binary_round (prec:=prec) (emax:=emax) mode true mn e
      have hround := binary_round_correct (prec:=prec) (emax:=emax)
        mode true mn e hmn_pos
      have hnotnan : is_nan_SF z = false := by
        simpa [z] using
          is_nan_binary_round (prec:=prec) (emax:=emax) mode true mn e
      have hB2R : B2R (prec:=prec) (emax:=emax)
            (standardFloatToBinaryFloatOfNotNaN
              (prec:=prec) (emax:=emax) z hround.1 hnotnan) = SF2R 2 z :=
        B2R_standardFloatToBinaryFloatOfNotNaN z hround.1 hnotnan
      have hfinite : is_finite (prec:=prec) (emax:=emax)
            (standardFloatToBinaryFloatOfNotNaN
              (prec:=prec) (emax:=emax) z hround.1 hnotnan) = is_finite_SF z :=
        is_finite_standardFloatToBinaryFloatOfNotNaN z hround.1 hnotnan
      have hsign : Bsign (prec:=prec) (emax:=emax)
            (standardFloatToBinaryFloatOfNotNaN
              (prec:=prec) (emax:=emax) z hround.1 hnotnan) = sign_SF z :=
        Bsign_standardFloatToBinaryFloatOfNotNaN z hround.1 hnotnan
      have hB2FF : B2FF (prec:=prec) (emax:=emax)
            (standardFloatToBinaryFloatOfNotNaN
              (prec:=prec) (emax:=emax) z hround.1 hnotnan) = SF2FF z :=
        B2FF_standardFloatToBinaryFloatOfNotNaN z hround.1 hnotnan
      have hinput_neg : F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk m e :
            FloatSpec.Core.Defs.FlocqFloat 2) < 0 :=
        FloatSpec.Core.Float_prop.F2R_lt_0 (beta:=2)
          (f:=FloatSpec.Core.Defs.FlocqFloat.mk m e) (by norm_num) hmneg
      have hinput : SF2R 2 (StandardFloat.S754_finite true mn e) =
          F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
            FloatSpec.Core.Defs.FlocqFloat 2) := by
        simp [SF2R, hmn_cast]
      by_cases hlt : FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
              (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
                FloatSpec.Core.Defs.FlocqFloat 2))|
          (FloatSpec.Core.Raux.bpow 2 emax) = true
      · have hltProp :
            |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                ((m : ℝ) * (2 : ℝ) ^ e)| <
              FloatSpec.Core.Raux.bpow 2 emax := by
          simpa [FloatSpec.Core.Raux.Rlt_bool, F2R,
            FloatSpec.Core.Defs.F2R] using hlt
        simp only [F2R, FloatSpec.Core.Defs.F2R] at hlt
        rw [ite_eq_left hlt]
        have hbranch := hround.2
        have hlt' : FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                (SF2R 2 (StandardFloat.S754_finite true mn e))|
            (FloatSpec.Core.Raux.bpow 2 emax) = true := by simpa [hinput] using hlt
        simp [hlt'] at hbranch
        have hpowNe : (2 : ℝ) ^ e ≠ 0 := zpow_ne_zero e (by norm_num)
        have hinputNegRaw : (m : ℝ) * (2 : ℝ) ^ e < 0 := by
          simpa [F2R, FloatSpec.Core.Defs.F2R] using hinput_neg
        simpa [normalize, hm0, hmpos, mn, z, hB2R, hfinite, hsign,
          hinput, hltProp, hpowNe, ne_of_lt hinput_neg, hinputNegRaw,
          FloatSpec.Core.Raux.Rlt_bool, decide_eq_true_eq.mpr hinputNegRaw] using hbranch
      · have hnotltProp :
            ¬ |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                ((m : ℝ) * (2 : ℝ) ^ e)| <
              FloatSpec.Core.Raux.bpow 2 emax := by
          simpa [FloatSpec.Core.Raux.Rlt_bool, F2R,
            FloatSpec.Core.Defs.F2R] using hlt
        simp only [F2R, FloatSpec.Core.Defs.F2R] at hlt
        rw [ite_eq_right hlt]
        have hbranch := hround.2
        have hlt' : FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                (SF2R 2 (StandardFloat.S754_finite true mn e))|
            (FloatSpec.Core.Raux.bpow 2 emax) = false := by
          simpa [hinput] using Bool.eq_false_of_not_eq_true hlt
        simp [hlt'] at hbranch
        have hinputNegRaw : (m : ℝ) * (2 : ℝ) ^ e < 0 := by
          simpa [F2R, FloatSpec.Core.Defs.F2R] using hinput_neg
        calc
          B2FF (normalize (prec:=prec) (emax:=emax) mode m e szero) = SF2FF z := by
            simpa [normalize, hm0, hmpos, mn, z] using hB2FF
          _ = SF2FF (bsn_binary_overflow (prec:=prec) (emax:=emax) mode true) := by
            rw [show z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode true by
              simpa [z] using hbranch]
          _ = binary_overflow (prec:=prec) (emax:=emax) mode
              (FloatSpec.Core.Raux.Rlt_bool
                (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
                  FloatSpec.Core.Defs.FlocqFloat 2)) 0) := by
            simp [binary_overflow, FloatSpec.Core.Raux.Rlt_bool, F2R,
              FloatSpec.Core.Defs.F2R, hinputNegRaw]

-- Coq: `Binary.v:Bfma`.
noncomputable def Bfma {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (fma_nan : BfmaNaNHandler prec emax)
    (mode : RoundingMode) (x y z : binary_float prec emax) :
    binary_float prec emax :=
  match x, y with
  | binary_float.B754_nan _ _ _, _ => (fma_nan x y z).1
  | _, binary_float.B754_nan _ _ _ => (fma_nan x y z).1
  | binary_float.B754_infinity _, binary_float.B754_zero _ => (fma_nan x y z).1
  | binary_float.B754_zero _, binary_float.B754_infinity _ => (fma_nan x y z).1
  | binary_float.B754_infinity sx, binary_float.B754_infinity sy
  | binary_float.B754_infinity sx, binary_float.B754_finite sy _ _ _
  | binary_float.B754_finite sx _ _ _, binary_float.B754_infinity sy =>
      let sxy := Bool.xor sx sy
      match z with
      | binary_float.B754_nan _ _ _ => (fma_nan x y z).1
      | binary_float.B754_infinity sz =>
          if sxy == sz then z else (fma_nan x y z).1
      | _ => binary_float.B754_infinity (prec:=prec) (emax:=emax) sxy
  | binary_float.B754_finite _ _ _ _, binary_float.B754_zero _
  | binary_float.B754_zero _, binary_float.B754_finite _ _ _ _
  | binary_float.B754_zero _, binary_float.B754_zero _ =>
      match z with
      | binary_float.B754_nan _ _ _ => (fma_nan x y z).1
      | binary_float.B754_zero _ =>
          binary_float.B754_zero (prec:=prec) (emax:=emax)
            (Bfma_szero mode x y z)
      | _ => z
  | binary_float.B754_finite sx mx ex _, binary_float.B754_finite sy my ey _ =>
      let X : FloatSpec.Core.Defs.FlocqFloat 2 :=
        FloatSpec.Core.Defs.FlocqFloat.mk
          (FloatSpec.Core.Zaux.cond_Zopp sx
            (FloatSpec.Core.Zaux.positiveToNat mx : Int)) ex
      let Y : FloatSpec.Core.Defs.FlocqFloat 2 :=
        FloatSpec.Core.Defs.FlocqFloat.mk
          (FloatSpec.Core.Zaux.cond_Zopp sy
            (FloatSpec.Core.Zaux.positiveToNat my : Int)) ey
      let product := FloatSpec.Calc.Operations.Fmult 2 X Y
      match z with
      | binary_float.B754_nan _ _ _ => (fma_nan x y z).1
      | binary_float.B754_infinity _ => z
      | binary_float.B754_zero _ =>
          normalize mode product.Fnum product.Fexp (Bfma_szero mode x y z)
      | binary_float.B754_finite sz mz ez _ =>
          let Z : FloatSpec.Core.Defs.FlocqFloat 2 :=
            FloatSpec.Core.Defs.FlocqFloat.mk
              (FloatSpec.Core.Zaux.cond_Zopp sz
                (FloatSpec.Core.Zaux.positiveToNat mz : Int)) ez
          let sum := FloatSpec.Calc.Operations.Fplus 2 product Z
          normalize mode sum.Fnum sum.Fexp (Bfma_szero mode x y z)

noncomputable def Bulp {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | binary_float.B754_zero _ =>
      binary_float.B754_finite (prec:=prec) (emax:=emax) false
        FloatSpec.Core.Zaux.Positive.xH (3 - emax - prec)
        (by simpa [FloatSpec.Core.Zaux.positiveToNat] using
          specFloat_bounded_one_emin (prec:=prec) (emax:=emax))
  | binary_float.B754_infinity _ =>
      binary_float.B754_infinity (prec:=prec) (emax:=emax) false
  | binary_float.B754_nan s payload hPayload =>
      binary_float.B754_nan (prec:=prec) (emax:=emax) s payload hPayload
  | binary_float.B754_finite _ _ e _ =>
      let z := binary_round (prec:=prec) (emax:=emax) RoundingMode.RTZ false 1 e
      have hround := binary_round_correct (prec:=prec) (emax:=emax)
        RoundingMode.RTZ false 1 e (by norm_num : 0 < (1 : Nat))
      standardFloatToBinaryFloatOfNotNaN (prec:=prec) (emax:=emax) z hround.1
        (by
          simpa [z] using
            is_nan_binary_round (prec:=prec) (emax:=emax) RoundingMode.RTZ false 1 e)

theorem B2R_binaryFloatToBinarySingleNaNFloat {prec emax : Int}
    (x : binary_float prec emax) :
    B754_to_R (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
      (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x)) =
      B2R (prec:=prec) (emax:=emax) x := by
  cases x <;> simp [B2R, binaryFloatToBinarySingleNaNFloat,
    binarySingleNaNFloatToB754, B754_to_R, F2R, FloatSpec.Core.Defs.F2R]

theorem is_finite_binaryFloatToBinarySingleNaNFloat {prec emax : Int}
    (x : binary_float prec emax) :
    BSN_is_finite (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
      (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x)) =
      is_finite (prec:=prec) (emax:=emax) x := by
  cases x <;> rfl

theorem Bsign_binaryFloatToBinarySingleNaNFloat_of_finite {prec emax : Int}
    (x : binary_float prec emax)
    (hx : is_finite (prec:=prec) (emax:=emax) x = true) :
    BSN_sign (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
      (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x)) =
      Bsign (prec:=prec) (emax:=emax) x := by
  cases x <;> simp [is_finite, Bsign, binaryFloatToBinarySingleNaNFloat,
    binarySingleNaNFloatToB754, BSN_sign] at hx ⊢

theorem binarySingleNaNFloatToB754_Bulp {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) :
    binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
      (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
        (Bulp (prec:=prec) (emax:=emax) x)) =
      ExperimentalSingleNaNArithmetic.Bulp (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
          (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x)) := by
  cases x with
  | B754_zero s =>
      simp [Bulp, binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754,
        ExperimentalSingleNaNArithmetic.Bulp, FloatSpec.Core.Zaux.positiveToNat]
  | B754_infinity s =>
      simp [Bulp, binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754,
        ExperimentalSingleNaNArithmetic.Bulp]
  | B754_nan s payload hPayload =>
      simp [Bulp, binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754,
        ExperimentalSingleNaNArithmetic.Bulp]
  | B754_finite s m e hBounded =>
      let z := binary_round (prec:=prec) (emax:=emax) RoundingMode.RTZ false 1 e
      have hround := binary_round_correct (prec:=prec) (emax:=emax)
        RoundingMode.RTZ false 1 e (by norm_num : 0 < (1 : Nat))
      have hnotnan :
          is_nan_SF z = false := by
        simpa [z] using
          is_nan_binary_round (prec:=prec) (emax:=emax) RoundingMode.RTZ false 1 e
      have hstd := binarySingleNaNFloatToB754_standardFloatToBinaryFloatOfNotNaN
        (prec:=prec) (emax:=emax) z hround.1 hnotnan
      calc
        binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
            (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
              (Bulp (prec:=prec) (emax:=emax)
                (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hBounded)))
            = SF2B z := by
              simpa [Bulp, z, hround] using hstd
        _ = ExperimentalSingleNaNArithmetic.Bulp (prec:=prec) (emax:=emax)
              (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
                (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hBounded))) := by
              simp [ExperimentalSingleNaNArithmetic.Bulp, binary_normalize,
                binaryFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754,
                z]

end Binary

/-! Exact source operations for `IEEE754/BinarySingleNaN.v`.

The earlier `BinarySingleNaN` namespace exposes the source observers and
comparisons.  These operations deliberately use the proof-carrying
`BinarySingleNaNFloat` carrier and the unique NaN constructor.  Finite
normalization is shared with the already proved `Binary` implementation; this
is representation reuse, not an extra NaN-policy argument absent from FLoCq.
-/

namespace BinarySingleNaN

abbrev binary_float := BinarySingleNaNFloat

def Bopp {prec emax : Int} : binary_float prec emax → binary_float prec emax
  | BinarySingleNaNFloat.B754_zero s =>
      BinarySingleNaNFloat.B754_zero (!s)
  | BinarySingleNaNFloat.B754_infinity s =>
      BinarySingleNaNFloat.B754_infinity (!s)
  | BinarySingleNaNFloat.B754_nan =>
      BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_finite s m e hm hb =>
      BinarySingleNaNFloat.B754_finite (!s) m e hm hb

noncomputable def Bmult {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y : binary_float prec emax) :
    binary_float prec emax :=
  match x, y with
  | BinarySingleNaNFloat.B754_nan, _
  | _, BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity sx,
      BinarySingleNaNFloat.B754_infinity sy
  | BinarySingleNaNFloat.B754_infinity sx,
      BinarySingleNaNFloat.B754_finite sy _ _ _ _
  | BinarySingleNaNFloat.B754_finite sx _ _ _ _,
      BinarySingleNaNFloat.B754_infinity sy =>
      BinarySingleNaNFloat.B754_infinity (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_infinity _, BinarySingleNaNFloat.B754_zero _
  | BinarySingleNaNFloat.B754_zero _, BinarySingleNaNFloat.B754_infinity _ =>
      BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_finite sx _ _ _ _,
      BinarySingleNaNFloat.B754_zero sy
  | BinarySingleNaNFloat.B754_zero sx,
      BinarySingleNaNFloat.B754_finite sy _ _ _ _
  | BinarySingleNaNFloat.B754_zero sx, BinarySingleNaNFloat.B754_zero sy =>
      BinarySingleNaNFloat.B754_zero (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx,
      BinarySingleNaNFloat.B754_finite sy my ey hmy Hy =>
      let z := binary_round_aux (prec:=prec) (emax:=emax) mode
        (Bool.xor sx sy) ((mx * my : Nat) : Int) (ex + ey)
        FloatSpec.Calc.Bracket.Location.loc_Exact
      have haux := _root_.Bmult_correct_aux (prec:=prec) (emax:=emax)
        mode sx mx ex hmx Hx sy my ey hmy Hy
      standardFloatToBinarySingleNaNFloat z haux.1

noncomputable def Bplus {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y : binary_float prec emax) :
    binary_float prec emax :=
  match x, y with
  | BinarySingleNaNFloat.B754_nan, _
  | _, BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity sx,
      BinarySingleNaNFloat.B754_infinity sy =>
      if sx == sy then x else BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity _, _ => x
  | _, BinarySingleNaNFloat.B754_infinity _ => y
  | BinarySingleNaNFloat.B754_zero sx, BinarySingleNaNFloat.B754_zero sy =>
      if sx == sy then x else
        match mode with
        | RoundingMode.RTN => BinarySingleNaNFloat.B754_zero true
        | _ => BinarySingleNaNFloat.B754_zero false
  | BinarySingleNaNFloat.B754_zero _, _ => y
  | _, BinarySingleNaNFloat.B754_zero _ => x
  | BinarySingleNaNFloat.B754_finite sx mx ex _ _,
      BinarySingleNaNFloat.B754_finite sy my ey _ _ =>
      let ez := min ex ey
      Binary.B2BSN (Binary.normalize (prec:=prec) (emax:=emax) mode
        (Fplus_naive sx mx ex sy my ey ez) ez
        (match mode with | RoundingMode.RTN => true | _ => false))

noncomputable def Bminus {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y : binary_float prec emax) :
    binary_float prec emax :=
  Bplus mode x (Bopp y)

def Bfma_szero {prec emax : Int} (mode : RoundingMode)
    (x y z : binary_float prec emax) : Bool :=
  let sxy := Bool.xor
    (BSN_sign (binarySingleNaNFloatToB754 x))
    (BSN_sign (binarySingleNaNFloatToB754 y))
  if sxy == BSN_sign (binarySingleNaNFloatToB754 z) then sxy
  else match mode with | RoundingMode.RTN => true | _ => false

noncomputable def Bfma {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y z : binary_float prec emax) :
    binary_float prec emax :=
  match x, y with
  | BinarySingleNaNFloat.B754_nan, _
  | _, BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity _, BinarySingleNaNFloat.B754_zero _
  | BinarySingleNaNFloat.B754_zero _, BinarySingleNaNFloat.B754_infinity _ =>
      BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity sx,
      BinarySingleNaNFloat.B754_infinity sy
  | BinarySingleNaNFloat.B754_infinity sx,
      BinarySingleNaNFloat.B754_finite sy _ _ _ _
  | BinarySingleNaNFloat.B754_finite sx _ _ _ _,
      BinarySingleNaNFloat.B754_infinity sy =>
      let sxy := Bool.xor sx sy
      match z with
      | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
      | BinarySingleNaNFloat.B754_infinity sz =>
          if sxy == sz then z else BinarySingleNaNFloat.B754_nan
      | _ => BinarySingleNaNFloat.B754_infinity sxy
  | BinarySingleNaNFloat.B754_finite _ _ _ _ _,
      BinarySingleNaNFloat.B754_zero _
  | BinarySingleNaNFloat.B754_zero _,
      BinarySingleNaNFloat.B754_finite _ _ _ _ _
  | BinarySingleNaNFloat.B754_zero _, BinarySingleNaNFloat.B754_zero _ =>
      match z with
      | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
      | BinarySingleNaNFloat.B754_zero _ =>
          BinarySingleNaNFloat.B754_zero (Bfma_szero mode x y z)
      | _ => z
  | BinarySingleNaNFloat.B754_finite sx mx ex _ _,
      BinarySingleNaNFloat.B754_finite sy my ey _ _ =>
      let X : FloatSpec.Core.Defs.FlocqFloat 2 :=
        FloatSpec.Core.Defs.FlocqFloat.mk
          (FloatSpec.Core.Zaux.cond_Zopp sx (mx : Int)) ex
      let Y : FloatSpec.Core.Defs.FlocqFloat 2 :=
        FloatSpec.Core.Defs.FlocqFloat.mk
          (FloatSpec.Core.Zaux.cond_Zopp sy (my : Int)) ey
      let product := FloatSpec.Calc.Operations.Fmult 2 X Y
      match z with
      | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
      | BinarySingleNaNFloat.B754_infinity _ => z
      | BinarySingleNaNFloat.B754_zero _ =>
          Binary.B2BSN (Binary.normalize (prec:=prec) (emax:=emax) mode
            product.Fnum product.Fexp (Bfma_szero mode x y z))
      | BinarySingleNaNFloat.B754_finite sz mz ez _ _ =>
          let Z : FloatSpec.Core.Defs.FlocqFloat 2 :=
            FloatSpec.Core.Defs.FlocqFloat.mk
              (FloatSpec.Core.Zaux.cond_Zopp sz (mz : Int)) ez
          let sum := FloatSpec.Calc.Operations.Fplus 2 product Z
          Binary.B2BSN (Binary.normalize (prec:=prec) (emax:=emax) mode
            sum.Fnum sum.Fexp (Bfma_szero mode x y z))

private noncomputable def Bdiv_finite {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int) (hmx : 0 < mx)
    (sy : Bool) (my : Nat) (ey : Int) (hmy : 0 < my) :
    binary_float prec emax :=
  let mxp := binaryPositiveOfNat mx hmx
  let myp := binaryPositiveOfNat my hmy
  let result := SFdiv_core_binary prec emax (mx : Int) ex (my : Int) ey
  let z := binary_round_aux (prec:=prec) (emax:=emax) mode
    (Bool.xor sx sy) result.1 result.2.1 result.2.2
  have haux := _root_.Bdiv_correct_aux (prec:=prec) (emax:=emax)
    mode sx mxp ex sy myp ey
  have hvalid : validBinarySingleNaNStandardFloat
      (prec:=prec) (emax:=emax) z = true := by
    simpa [mxp, myp, result, z, binaryPositiveOfNat_spec] using haux.1
  standardFloatToBinarySingleNaNFloat z hvalid

noncomputable def Bdiv {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y : binary_float prec emax) :
    binary_float prec emax :=
  match x, y with
  | BinarySingleNaNFloat.B754_nan, _
  | _, BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity _,
      BinarySingleNaNFloat.B754_infinity _
  | BinarySingleNaNFloat.B754_zero _, BinarySingleNaNFloat.B754_zero _ =>
      BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity sx,
      BinarySingleNaNFloat.B754_finite sy _ _ _ _
  | BinarySingleNaNFloat.B754_infinity sx, BinarySingleNaNFloat.B754_zero sy =>
      BinarySingleNaNFloat.B754_infinity (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_finite sx _ _ _ _,
      BinarySingleNaNFloat.B754_infinity sy
  | BinarySingleNaNFloat.B754_zero sx,
      BinarySingleNaNFloat.B754_infinity sy
  | BinarySingleNaNFloat.B754_zero sx,
      BinarySingleNaNFloat.B754_finite sy _ _ _ _ =>
      BinarySingleNaNFloat.B754_zero (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_finite sx _ _ _ _,
      BinarySingleNaNFloat.B754_zero sy =>
      BinarySingleNaNFloat.B754_infinity (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_finite sx mx ex hmx _,
      BinarySingleNaNFloat.B754_finite sy my ey hmy _ =>
      Bdiv_finite mode sx mx ex hmx sy my ey hmy

noncomputable def Bsqrt {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : binary_float prec emax) :
    binary_float prec emax :=
  match x with
  | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity false => x
  | BinarySingleNaNFloat.B754_infinity true => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_zero _ => x
  | BinarySingleNaNFloat.B754_finite true _ _ _ _ =>
      BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_finite false mx ex hmx _ =>
      let input := F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2)
      let result := SFsqrt_core_binary prec emax (mx : Int) ex
      have hdata := SFsqrt_core_binary_correct_data
        (prec:=prec) (emax:=emax) (mx : Int) ex (by exact_mod_cast hmx)
      have hresult_pos : 0 < result.1 := by simpa [result] using hdata.1
      let mzn := result.1.toNat
      have hmzn_pos : 0 < mzn := by omega
      have hmzn_cast : (mzn : Int) = result.1 :=
        Int.toNat_of_nonneg (le_of_lt hresult_pos)
      let z := binary_round_aux (prec:=prec) (emax:=emax) mode false
        (mzn : Int) result.2.1 result.2.2
      have hbetween : FloatSpec.Calc.Bracket.inbetween_float 2
          (mzn : Int) result.2.1 |Real.sqrt input| result.2.2 := by
        simpa [input, result, hmzn_cast, abs_of_nonneg (Real.sqrt_nonneg _)]
          using hdata.2.1
      have hexp : result.2.1 ≤ FLT_exp (3 - emax - prec) prec
          (FloatSpec.Core.Digits.Zdigits 2 (mzn : Int) + result.2.1) := by
        simpa [result, hmzn_cast] using hdata.2.2
      have haux := binary_round_aux_correct (prec:=prec) (emax:=emax)
        mode (Real.sqrt input) mzn result.2.1 result.2.2 hmzn_pos hbetween hexp
      have hsqrt_sign : FloatSpec.Core.Raux.Rlt_bool (Real.sqrt input) 0 = false := by
        simp [FloatSpec.Core.Raux.Rlt_bool, Real.sqrt_nonneg]
      have hvalid : validBinarySingleNaNStandardFloat
          (prec:=prec) (emax:=emax) z = true := by
        simpa [z, hsqrt_sign] using haux.1
      standardFloatToBinarySingleNaNFloat z hvalid

end BinarySingleNaN

/-!
Lean 4.34 exposes the logical models of native `Float` and `Float32`.  These
bridges are deliberately structural: the FLoCq carriers and specifications
remain authoritative, while native models provide executable IEEE encodings.
-/

namespace FloatSpec.IEEE754.Native

open Float.Model

def modelSignOfBool : Bool → UnpackedFloat.Sign
  | false => .positive
  | true => .negative

def boolOfModelSign : UnpackedFloat.Sign → Bool
  | .positive => false
  | .negative => true

@[simp] theorem boolOfModelSign_modelSignOfBool (s : Bool) :
    boolOfModelSign (modelSignOfBool s) = s := by cases s <;> rfl

@[simp] theorem modelSignOfBool_boolOfModelSign (s : UnpackedFloat.Sign) :
    modelSignOfBool (boolOfModelSign s) = s := by cases s <;> rfl

/-- Structural translation from FLoCq's single-NaN surface to Lean's unpacked model. -/
def unpackedOfStandardFloat : StandardFloat → UnpackedFloat
  | .S754_zero s => .zero (modelSignOfBool s)
  | .S754_infinity s => .infinity (modelSignOfBool s)
  | .S754_nan => .notANumber
  | .S754_finite s m e =>
      if hm : 0 < m then .finite (modelSignOfBool s) m e hm else .zero (modelSignOfBool s)

/-- Structural translation from Lean's unpacked model to FLoCq's single-NaN surface. -/
def standardFloatOfUnpacked : UnpackedFloat → StandardFloat
  | .zero s => .S754_zero (boolOfModelSign s)
  | .infinity s => .S754_infinity (boolOfModelSign s)
  | .notANumber => .S754_nan
  | .finite s m e _ => .S754_finite (boolOfModelSign s) m e

theorem standardFloatOfUnpacked_unpackedOfStandardFloat
    (x : StandardFloat)
    (hvalid : match x with | .S754_finite _ m _ => 0 < m | _ => True) :
    standardFloatOfUnpacked (unpackedOfStandardFloat x) = x := by
  cases x with
  | S754_zero s => cases s <;> rfl
  | S754_infinity s => cases s <;> rfl
  | S754_nan => rfl
  | S754_finite s m e =>
      cases s <;> simp_all [unpackedOfStandardFloat, standardFloatOfUnpacked]

@[simp] theorem unpackedOfStandardFloat_standardFloatOfUnpacked
    (x : UnpackedFloat) :
    unpackedOfStandardFloat (standardFloatOfUnpacked x) = x := by
  cases x with
  | infinity s => cases s <;> rfl
  | zero s => cases s <;> rfl
  | notANumber => rfl
  | finite s m e hm =>
      cases s <;> simp [unpackedOfStandardFloat, standardFloatOfUnpacked, hm]

/-- The exact proof-carrying FLoCq carrier as Lean's unpacked single-NaN model. -/
def unpackedOfBinarySingleNaNFloat {prec emax : Int} :
    BinarySingleNaNFloat prec emax → UnpackedFloat
  | .B754_zero s => .zero (modelSignOfBool s)
  | .B754_infinity s => .infinity (modelSignOfBool s)
  | .B754_nan => .notANumber
  | .B754_finite s m e hm _ => .finite (modelSignOfBool s) m e hm

@[simp] theorem standardFloatOfUnpacked_unpackedOfBinarySingleNaNFloat
  {prec emax : Int} (x : BinarySingleNaNFloat prec emax) :
    standardFloatOfUnpacked (unpackedOfBinarySingleNaNFloat x) =
      binarySingleNaNFloatToStandardFloat x := by
  cases x <;> simp [unpackedOfBinarySingleNaNFloat, standardFloatOfUnpacked,
    binarySingleNaNFloatToStandardFloat]

/-- Encode a FLoCq standard float in Lean's binary64 logical model. -/
def model64OfStandardFloat (x : StandardFloat) : Float.Model :=
  Float.Model.pack (unpackedOfStandardFloat x)

/-- Encode a FLoCq standard float in Lean's binary32 logical model. -/
def model32OfStandardFloat (x : StandardFloat) : Float32.Model :=
  Float32.Model.pack (unpackedOfStandardFloat x)

/-- Decode Lean's binary64 logical model to the FLoCq single-NaN surface. -/
def standardFloatOfModel64 (x : Float.Model) : StandardFloat :=
  standardFloatOfUnpacked x.unpack

/-- Decode Lean's binary32 logical model to the FLoCq single-NaN surface. -/
def standardFloatOfModel32 (x : Float32.Model) : StandardFloat :=
  standardFloatOfUnpacked x.unpack

@[simp] theorem model64OfStandardFloat_standardFloatOfModel64
    (x : Float.Model) :
    model64OfStandardFloat (standardFloatOfModel64 x) = x := by
  cases x with
  | mk bits valid =>
      rw [Float.Model.mk.injEq]
      apply UInt64.toBitVec_inj.mp
      simpa [model64OfStandardFloat, standardFloatOfModel64,
        Float.Model.pack, Float.Model.unpack] using
        Float.Model.UnpackedFloat.pack_unpack_of_valid valid

@[simp] theorem model32OfStandardFloat_standardFloatOfModel32
    (x : Float32.Model) :
    model32OfStandardFloat (standardFloatOfModel32 x) = x := by
  cases x with
  | mk bits valid =>
      rw [Float32.Model.mk.injEq]
      apply UInt32.toBitVec_inj.mp
      simpa [model32OfStandardFloat, standardFloatOfModel32,
        Float32.Model.pack, Float32.Model.unpack] using
        Float.Model.UnpackedFloat.pack_unpack_of_valid valid

/-- Encode an exact FLoCq binary64 single-NaN value as Lean's logical model. -/
def model64OfBinarySingleNaNFloat (x : BinarySingleNaNFloat 53 1024) : Float.Model :=
  Float.Model.pack (unpackedOfBinarySingleNaNFloat x)

/-- Encode an exact FLoCq binary32 single-NaN value as Lean's logical model. -/
def model32OfBinarySingleNaNFloat (x : BinarySingleNaNFloat 24 128) : Float32.Model :=
  Float32.Model.pack (unpackedOfBinarySingleNaNFloat x)

@[simp] theorem model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat
    (x : BinarySingleNaNFloat 53 1024) :
    model64OfBinarySingleNaNFloat x =
      model64OfStandardFloat (binarySingleNaNFloatToStandardFloat x) := by
  cases x <;> simp_all [model64OfBinarySingleNaNFloat, model64OfStandardFloat,
    unpackedOfBinarySingleNaNFloat, unpackedOfStandardFloat,
    binarySingleNaNFloatToStandardFloat]

@[simp] theorem model32OfBinarySingleNaNFloat_eq_model32OfStandardFloat
    (x : BinarySingleNaNFloat 24 128) :
    model32OfBinarySingleNaNFloat x =
      model32OfStandardFloat (binarySingleNaNFloatToStandardFloat x) := by
  cases x <;> simp_all [model32OfBinarySingleNaNFloat, model32OfStandardFloat,
    unpackedOfBinarySingleNaNFloat, unpackedOfStandardFloat,
    binarySingleNaNFloatToStandardFloat]

end FloatSpec.IEEE754.Native

/-! Source-qualified facade for declarations whose unqualified Coq names
collide with `IEEE754/Binary.v`.  Every definition below is a reducible name
for the already checked proof-carrying SingleNaN implementation. -/

namespace BinarySingleNaN

abbrev SF2B {prec emax : Int} :=
  @standardFloatToBinarySingleNaNFloat prec emax

abbrev SF2B' {prec emax : Int} :=
  @standardFloatToBinarySingleNaNFloat' prec emax

abbrev B2SF {prec emax : Int} :=
  @binarySingleNaNFloatToStandardFloat prec emax

noncomputable abbrev B2R {prec emax : Int}
    (x : binary_float prec emax) : ℝ :=
  B754_to_R (binarySingleNaNFloatToB754 x)

def Bsign {prec emax : Int} (x : binary_float prec emax) : Bool :=
  BSN_sign (binarySingleNaNFloatToB754 x)

def is_finite {prec emax : Int} (x : binary_float prec emax) : Bool :=
  BSN_is_finite (binarySingleNaNFloatToB754 x)

def is_finite_strict {prec emax : Int} (x : binary_float prec emax) : Bool :=
  BSN_is_finite_strict (binarySingleNaNFloatToB754 x)

def is_nan {prec emax : Int} (x : binary_float prec emax) : Bool :=
  BSN_is_nan (binarySingleNaNFloatToB754 x)

noncomputable abbrev Beqb {prec emax : Int} := @_root_.Beqb prec emax
noncomputable abbrev Bltb {prec emax : Int} := @_root_.Bltb prec emax
noncomputable abbrev Bleb {prec emax : Int} := @_root_.Bleb prec emax

theorem Beqb_correct {prec emax : Int}
    (f1 f2 : binary_float prec emax)
    (h1 : is_finite f1 = true) (h2 : is_finite f2 = true) :
    Beqb f1 f2 = FloatSpec.Core.Raux.Req_bool (B2R f1) (B2R f2) := by
  exact _root_.Beqb_correct f1 f2 h1 h2

theorem Beqb_refl {prec emax : Int} (f : binary_float prec emax) :
    Beqb f f = !(is_nan f) := by
  exact _root_.Beqb_refl f

theorem Bltb_correct {prec emax : Int}
    (f1 f2 : binary_float prec emax)
    (h1 : is_finite f1 = true) (h2 : is_finite f2 = true) :
    Bltb f1 f2 = FloatSpec.Core.Raux.Rlt_bool (B2R f1) (B2R f2) := by
  exact _root_.Bltb_correct f1 f2 h1 h2

theorem Bleb_correct {prec emax : Int}
    (f1 f2 : binary_float prec emax)
    (h1 : is_finite f1 = true) (h2 : is_finite f2 = true) :
    Bleb f1 f2 = FloatSpec.Core.Raux.Rle_bool (B2R f1) (B2R f2) := by
  exact _root_.Bleb_correct f1 f2 h1 h2

theorem canonical_canonical_mantissa {prec emax : Int}
    (sx : Bool) (mx : FloatSpec.Core.Zaux.Positive) (ex : Int)
    (h : canonical_mantissa (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mx) ex = true) :
    FloatSpec.Core.Generic_fmt.canonical 2
      (FLT_exp (3 - emax - prec) prec)
      (FloatSpec.Core.Defs.FlocqFloat.mk
        (if sx then -(FloatSpec.Core.Zaux.positiveToNat mx : Int)
         else (FloatSpec.Core.Zaux.positiveToNat mx : Int)) ex) := by
  exact _root_.canonical_canonical_mantissa (prec:=prec) (emax:=emax) sx mx ex h

theorem generic_format_B2R {prec emax : Int}
    (x : binary_float prec emax) :
    FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec) (B2R x) := by
  exact _root_.generic_format_B2R (prec:=prec) (emax:=emax) x

theorem FLT_format_B2R {prec emax : Int}
    [Prec_gt_0 prec]
    (x : binary_float prec emax) :
    FloatSpec.Core.FLT.FLT_format (prec:=prec) (emin:=3 - emax - prec)
      2 (B2R x) := by
  exact _root_.FLT_format_B2R (prec:=prec) (emax:=emax) x

end BinarySingleNaN

-- Coq: `Binary.v:Bulp_correct`, transported through the proof-carrying
-- Binary-to-SingleNaN bridge.
theorem Bulp_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) :
    Binary.is_finite (prec:=prec) (emax:=emax) x = true →
      Binary.B2R (prec:=prec) (emax:=emax)
          (Binary.Bulp (prec:=prec) (emax:=emax) x) =
        FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec)
          (Binary.B2R (prec:=prec) (emax:=emax) x) ∧
      Binary.is_finite (prec:=prec) (emax:=emax)
          (Binary.Bulp (prec:=prec) (emax:=emax) x) = true ∧
      Binary.Bsign (prec:=prec) (emax:=emax)
          (Binary.Bulp (prec:=prec) (emax:=emax) x) = false := by
  intro hfinite
  have hfinite_bsn :
      BSN_is_finite (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
        (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x)) = true := by
    simpa [Binary.is_finite_binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x]
      using hfinite
  have hcorr :=
    ExperimentalSingleNaNArithmetic.Bulp_correct (prec:=prec) (emax:=emax)
      (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x) hfinite_bsn
  have hbridge := Binary.binarySingleNaNFloatToB754_Bulp (prec:=prec) (emax:=emax) x
  constructor
  · calc
      Binary.B2R (prec:=prec) (emax:=emax)
          (Binary.Bulp (prec:=prec) (emax:=emax) x)
          = B754_to_R (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
              (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
                (Binary.Bulp (prec:=prec) (emax:=emax) x))) := by
                rw [Binary.B2R_binaryFloatToBinarySingleNaNFloat]
      _ = B754_to_R (ExperimentalSingleNaNArithmetic.Bulp (prec:=prec) (emax:=emax)
              (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
                (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x))) := by
                rw [hbridge]
      _ = FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec)
              (B754_to_R (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
                (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax) x))) := hcorr.1
      _ = FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec)
              (Binary.B2R (prec:=prec) (emax:=emax) x) := by
                rw [Binary.B2R_binaryFloatToBinarySingleNaNFloat]
  · constructor
    · have hfinite_bulp_bsn :
          BSN_is_finite (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
            (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
              (Binary.Bulp (prec:=prec) (emax:=emax) x))) = true := by
          rw [hbridge]
          exact hcorr.2.1
      simpa [Binary.is_finite_binaryFloatToBinarySingleNaNFloat
        (prec:=prec) (emax:=emax) (Binary.Bulp (prec:=prec) (emax:=emax) x)]
        using hfinite_bulp_bsn
    · have hfinite_bulp :
          Binary.is_finite (prec:=prec) (emax:=emax)
            (Binary.Bulp (prec:=prec) (emax:=emax) x) = true := by
          have hfinite_bulp_bsn :
              BSN_is_finite (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
                (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
                  (Binary.Bulp (prec:=prec) (emax:=emax) x))) = true := by
              rw [hbridge]
              exact hcorr.2.1
          simpa [Binary.is_finite_binaryFloatToBinarySingleNaNFloat
            (prec:=prec) (emax:=emax) (Binary.Bulp (prec:=prec) (emax:=emax) x)]
            using hfinite_bulp_bsn
      have hsign_bulp_bsn :
          BSN_sign (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax)
            (binaryFloatToBinarySingleNaNFloat (prec:=prec) (emax:=emax)
              (Binary.Bulp (prec:=prec) (emax:=emax) x))) = false := by
          rw [hbridge]
          exact hcorr.2.2
      simpa [Binary.Bsign_binaryFloatToBinarySingleNaNFloat_of_finite
        (prec:=prec) (emax:=emax) (Binary.Bulp (prec:=prec) (emax:=emax) x)
        hfinite_bulp] using hsign_bulp_bsn

-- Coq: `Binary.v:Bmult_correct`, on the proof-carrying Binary carrier.
theorem Bmult_correct_from_exp_instances {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mult_nan : Binary.BmultNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Binary.B2R (prec:=prec) (emax:=emax) x *
             Binary.B2R (prec:=prec) (emax:=emax) y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      Binary.B2R (prec:=prec) (emax:=emax)
          (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode x y) =
        FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Binary.B2R (prec:=prec) (emax:=emax) x *
             Binary.B2R (prec:=prec) (emax:=emax) y) ∧
      Binary.is_finite (prec:=prec) (emax:=emax)
          (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode x y) =
        (Binary.is_finite (prec:=prec) (emax:=emax) x &&
          Binary.is_finite (prec:=prec) (emax:=emax) y) ∧
      (Binary.is_nan (prec:=prec) (emax:=emax)
          (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode x y) = false →
        Binary.Bsign (prec:=prec) (emax:=emax)
            (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode x y) =
          Bool.xor (Binary.Bsign (prec:=prec) (emax:=emax) x)
            (Binary.Bsign (prec:=prec) (emax:=emax) y))
    else
      Binary.B2FF (prec:=prec) (emax:=emax)
          (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode x y) =
        Binary.binary_overflow (prec:=prec) (emax:=emax) mode
          (Bool.xor (Binary.Bsign (prec:=prec) (emax:=emax) x)
            (Binary.Bsign (prec:=prec) (emax:=emax) y)) := by
  classical
  cases x with
  | B754_zero sx =>
      cases y with
      | B754_zero sy =>
          simp [Binary.Bmult, Binary.B2R, Binary.is_finite, Binary.is_nan,
            Binary.Bsign, Binary.roundR_zero_of_mode,
            Binary.Rlt_bool_zero_bpow]
      | B754_infinity sy =>
          simpa [Binary.Bmult] using
            Binary.bmult_correct_nan_result (prec:=prec) (emax:=emax)
              mult_nan mode
              (binary_float.B754_zero (prec:=prec) (emax:=emax) sx)
              (binary_float.B754_infinity (prec:=prec) (emax:=emax) sy)
              (by simp [Binary.B2R])
              (by simp [Binary.is_finite])
      | B754_nan sy payload hy =>
          simpa [Binary.Bmult] using
            Binary.bmult_correct_nan_result (prec:=prec) (emax:=emax)
              mult_nan mode
              (binary_float.B754_zero (prec:=prec) (emax:=emax) sx)
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sy payload hy)
              (by simp [Binary.B2R])
              (by simp [Binary.is_finite])
      | B754_finite sy my ey Hy =>
          simp [Binary.Bmult, Binary.B2R, Binary.is_finite, Binary.is_nan,
            Binary.Bsign, Binary.roundR_zero_of_mode,
            Binary.Rlt_bool_zero_bpow]
  | B754_infinity sx =>
      cases y with
      | B754_zero sy =>
          simpa [Binary.Bmult] using
            Binary.bmult_correct_nan_result (prec:=prec) (emax:=emax)
              mult_nan mode
              (binary_float.B754_infinity (prec:=prec) (emax:=emax) sx)
              (binary_float.B754_zero (prec:=prec) (emax:=emax) sy)
              (by simp [Binary.B2R])
              (by simp [Binary.is_finite])
      | B754_infinity sy =>
          simp [Binary.Bmult, Binary.B2R, Binary.is_finite, Binary.is_nan,
            Binary.Bsign, Binary.roundR_zero_of_mode,
            Binary.Rlt_bool_zero_bpow]
      | B754_nan sy payload hy =>
          simpa [Binary.Bmult] using
            Binary.bmult_correct_nan_result (prec:=prec) (emax:=emax)
              mult_nan mode
              (binary_float.B754_infinity (prec:=prec) (emax:=emax) sx)
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sy payload hy)
              (by simp [Binary.B2R])
              (by simp [Binary.is_finite])
      | B754_finite sy my ey Hy =>
          simp [Binary.Bmult, Binary.B2R, Binary.is_finite, Binary.is_nan,
            Binary.Bsign, Binary.roundR_zero_of_mode,
            Binary.Rlt_bool_zero_bpow]
  | B754_nan sx payload hx =>
      cases y with
      | B754_zero sy =>
          simpa [Binary.Bmult] using
            Binary.bmult_correct_nan_result (prec:=prec) (emax:=emax)
              mult_nan mode
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hx)
              (binary_float.B754_zero (prec:=prec) (emax:=emax) sy)
              (by simp [Binary.B2R])
              (by simp [Binary.is_finite])
      | B754_infinity sy =>
          simpa [Binary.Bmult] using
            Binary.bmult_correct_nan_result (prec:=prec) (emax:=emax)
              mult_nan mode
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hx)
              (binary_float.B754_infinity (prec:=prec) (emax:=emax) sy)
              (by simp [Binary.B2R])
              (by simp [Binary.is_finite])
      | B754_nan sy payload' hy =>
          simpa [Binary.Bmult] using
            Binary.bmult_correct_nan_result (prec:=prec) (emax:=emax)
              mult_nan mode
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hx)
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sy payload' hy)
              (by simp [Binary.B2R])
              (by simp [Binary.is_finite])
      | B754_finite sy my ey Hy =>
          simpa [Binary.Bmult] using
            Binary.bmult_correct_nan_result (prec:=prec) (emax:=emax)
              mult_nan mode
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hx)
              (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)
              (by simp [Binary.B2R])
              (by simp [Binary.is_finite])
  | B754_finite sx mx ex Hx =>
      cases y with
      | B754_zero sy =>
          simp [Binary.Bmult, Binary.B2R, Binary.is_finite, Binary.is_nan,
            Binary.Bsign, Binary.roundR_zero_of_mode,
            Binary.Rlt_bool_zero_bpow]
      | B754_infinity sy =>
          simp [Binary.Bmult, Binary.B2R, Binary.is_finite, Binary.is_nan,
            Binary.Bsign, Binary.roundR_zero_of_mode,
            Binary.Rlt_bool_zero_bpow]
      | B754_nan sy payload hy =>
          simpa [Binary.Bmult] using
            Binary.bmult_correct_nan_result (prec:=prec) (emax:=emax)
              mult_nan mode
              (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sy payload hy)
              (by simp [Binary.B2R])
              (by simp [Binary.is_finite])
      | B754_finite sy my ey Hy =>
          let mxn := FloatSpec.Core.Zaux.positiveToNat mx
          let myn := FloatSpec.Core.Zaux.positiveToNat my
          let z := binary_round_aux (prec:=prec) (emax:=emax) mode
            (Bool.xor sx sy) ((mxn * myn : Nat) : Int) (ex + ey)
            FloatSpec.Calc.Bracket.Location.loc_Exact
          have haux := Bmult_correct_aux (prec:=prec) (emax:=emax)
            mode sx mxn ex (positiveToNat_pos_bsn mx) Hx
            sy myn ey (positiveToNat_pos_bsn my) Hy
          have hnotnan : is_nan_SF z = false := by
            classical
            by_cases hlt :
                FloatSpec.Core.Raux.Rlt_bool
                  |FloatSpec.Core.Generic_fmt.roundR 2
                    (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                      ((SF2R 2 (StandardFloat.S754_finite sx mxn ex)) *
                       (SF2R 2 (StandardFloat.S754_finite sy myn ey)))|
                  (FloatSpec.Core.Raux.bpow 2 emax) = true
            · have hfinite : is_finite_SF z = true := by
                have hbranch := haux.2
                simp [mxn, myn, hlt] at hbranch
                exact hbranch.2.1
              cases hz : z <;> simp [hz, is_nan_SF, is_finite_SF] at hfinite ⊢
            · have hover : z =
                  bsn_binary_overflow (prec:=prec) (emax:=emax) mode
                    (Bool.xor sx sy) := by
                have hlt_false :
                    FloatSpec.Core.Raux.Rlt_bool
                      |FloatSpec.Core.Generic_fmt.roundR 2
                        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                          ((SF2R 2 (StandardFloat.S754_finite sx mxn ex)) *
                           (SF2R 2 (StandardFloat.S754_finite sy myn ey)))|
                      (FloatSpec.Core.Raux.bpow 2 emax) = false :=
                  Bool.eq_false_of_not_eq_true hlt
                have hbranch := haux.2
                simpa [z, mxn, myn, hlt_false] using hbranch
              rw [hover]
              exact is_nan_binary_overflow (prec:=prec) (emax:=emax) mode
                (Bool.xor sx sy)
          have hB2R :
              Binary.B2R (prec:=prec) (emax:=emax)
                (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)) =
                SF2R 2 z := by
            simpa [Binary.Bmult, mxn, myn, z] using
              Binary.B2R_standardFloatToBinaryFloatOfNotNaN
                (prec:=prec) (emax:=emax) z haux.1 hnotnan
          have hfinite_bridge :
              Binary.is_finite (prec:=prec) (emax:=emax)
                (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)) =
                is_finite_SF z := by
            simpa [Binary.Bmult, mxn, myn, z] using
              Binary.is_finite_standardFloatToBinaryFloatOfNotNaN
                (prec:=prec) (emax:=emax) z haux.1 hnotnan
          have hsign_bridge :
              Binary.Bsign (prec:=prec) (emax:=emax)
                (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)) =
                sign_SF z := by
            simpa [Binary.Bmult, mxn, myn, z] using
              Binary.Bsign_standardFloatToBinaryFloatOfNotNaN
                (prec:=prec) (emax:=emax) z haux.1 hnotnan
          have hB2FF :
              Binary.B2FF (prec:=prec) (emax:=emax)
                (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)) =
                SF2FF z := by
            simpa [Binary.Bmult, mxn, myn, z] using
              Binary.B2FF_standardFloatToBinaryFloatOfNotNaN
                (prec:=prec) (emax:=emax) z haux.1 hnotnan
          have hmul :
              SF2R 2 (StandardFloat.S754_finite sx mxn ex) *
                  SF2R 2 (StandardFloat.S754_finite sy myn ey) =
                Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx) *
                  Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy) := by
            simp [SF2R, Binary.B2R, F2R, FloatSpec.Core.Defs.F2R, mxn, myn]
          by_cases hlt :
              FloatSpec.Core.Raux.Rlt_bool
                |FloatSpec.Core.Generic_fmt.roundR 2
                  (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                    (Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx) *
                     Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy))|
                (FloatSpec.Core.Raux.bpow 2 emax) = true
          · rw [ite_eq_left hlt]
            have hbranch := haux.2
            have hlt_aux :
                FloatSpec.Core.Raux.Rlt_bool
                  |FloatSpec.Core.Generic_fmt.roundR 2
                    (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                      ((SF2R 2 (StandardFloat.S754_finite sx mxn ex)) *
                       (SF2R 2 (StandardFloat.S754_finite sy myn ey)))|
                  (FloatSpec.Core.Raux.bpow 2 emax) = true := by
              simpa only [hmul] using hlt
            simp [mxn, myn, hlt_aux] at hbranch
            constructor
            · calc
                Binary.B2R (prec:=prec) (emax:=emax)
                    (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode
                      (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy))
                    = SF2R 2 z := hB2R
                _ = FloatSpec.Core.Generic_fmt.roundR 2
                    (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                    (Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx) *
                     Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)) := by
                    rw [← hmul]
                    simpa [z, mxn, myn] using hbranch.1
            · constructor
              · calc
                  Binary.is_finite (prec:=prec) (emax:=emax)
                      (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode
                        (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                        (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy))
                      = is_finite_SF z := hfinite_bridge
                  _ = true := hbranch.2.1
              · intro _
                calc
                  Binary.Bsign (prec:=prec) (emax:=emax)
                      (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode
                        (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                        (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy))
                      = sign_SF z := hsign_bridge
                  _ = Bool.xor sx sy := hbranch.2.2
          · rw [ite_eq_right hlt]
            have hlt_false :
                FloatSpec.Core.Raux.Rlt_bool
                  |FloatSpec.Core.Generic_fmt.roundR 2
                    (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                      ((SF2R 2 (StandardFloat.S754_finite sx mxn ex)) *
                       (SF2R 2 (StandardFloat.S754_finite sy myn ey)))|
                  (FloatSpec.Core.Raux.bpow 2 emax) = false := by
              have hlt_false' := Bool.eq_false_of_not_eq_true hlt
              simpa only [hmul] using hlt_false'
            have hbranch := haux.2
            have hover : z =
                bsn_binary_overflow (prec:=prec) (emax:=emax) mode
                  (Bool.xor sx sy) := by
              simpa [z, mxn, myn, hlt_false] using hbranch
            calc
              Binary.B2FF (prec:=prec) (emax:=emax)
                  (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode
                    (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                    (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy))
                  = SF2FF z := hB2FF
              _ = SF2FF (bsn_binary_overflow (prec:=prec) (emax:=emax) mode
                    (Bool.xor sx sy)) := by rw [hover]
              _ = Binary.binary_overflow (prec:=prec) (emax:=emax) mode
                    (Bool.xor sx sy) := rfl

-- Source ID: IEEE754/Binary.v:Bmult_correct:21817
-- Target: Bmult_correct
/-- Coq `Binary.v:Bmult_correct`; the FLT exponent instances are canonical
and therefore not caller-supplied source premises. -/
theorem Bmult_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mult_nan : Binary.BmultNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Binary.B2R (prec:=prec) (emax:=emax) x *
             Binary.B2R (prec:=prec) (emax:=emax) y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      Binary.B2R (prec:=prec) (emax:=emax)
          (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode x y) =
        FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Binary.B2R (prec:=prec) (emax:=emax) x *
             Binary.B2R (prec:=prec) (emax:=emax) y) ∧
      Binary.is_finite (prec:=prec) (emax:=emax)
          (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode x y) =
        (Binary.is_finite (prec:=prec) (emax:=emax) x &&
          Binary.is_finite (prec:=prec) (emax:=emax) y) ∧
      (Binary.is_nan (prec:=prec) (emax:=emax)
          (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode x y) = false →
        Binary.Bsign (prec:=prec) (emax:=emax)
            (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode x y) =
          Bool.xor (Binary.Bsign (prec:=prec) (emax:=emax) x)
            (Binary.Bsign (prec:=prec) (emax:=emax) y))
    else
      Binary.B2FF (prec:=prec) (emax:=emax)
          (Binary.Bmult (prec:=prec) (emax:=emax) mult_nan mode x y) =
        Binary.binary_overflow (prec:=prec) (emax:=emax) mode
          (Bool.xor (Binary.Bsign (prec:=prec) (emax:=emax) x)
            (Binary.Bsign (prec:=prec) (emax:=emax) y)) :=
  Bmult_correct_from_exp_instances mult_nan mode x y

/-- The sign clause in Flocq's `Bplus_correct`, written directly in terms of
the exact sum instead of Coq's three-way `Rcompare` result. -/
noncomputable def binaryPlusResultSign (mode : RoundingMode)
    (sx sy : Bool) (z : ℝ) : Bool :=
  if z = 0 then
    match mode with
    | RoundingMode.RTN => sx || sy
    | _ => sx && sy
  else
    decide (z < 0)

/-- The sign clause in Flocq's `Bminus_correct`. -/
noncomputable def binaryMinusResultSign (mode : RoundingMode)
    (sx sy : Bool) (z : ℝ) : Bool :=
  binaryPlusResultSign mode sx (!sy) z

/-- The sign clause in Flocq's `Bfma_correct`, expressed without encoding
Coq's three-way real comparison as an integer. -/
noncomputable def binaryFmaResultSign {prec emax : Int}
    (mode : RoundingMode) (x y z : binary_float prec emax) (res : ℝ) : Bool :=
  if res = 0 then Binary.Bfma_szero mode x y z else decide (res < 0)

private theorem binaryFinite_ne_zero {prec emax : Int}
    (s : Bool) (m : FloatSpec.Core.Zaux.Positive) (e : Int)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true) :
    Binary.B2R (prec:=prec) (emax:=emax)
      (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded) ≠ 0 := by
  have hm := positiveToNat_pos_bsn m
  have hmInt : (0 : Int) < (FloatSpec.Core.Zaux.positiveToNat m : Int) := by
    exact_mod_cast hm
  cases s
  · simp only [Binary.B2R]
    exact ne_of_gt (FloatSpec.Core.Float_prop.F2R_gt_0
      (beta:=2) (f:=FloatSpec.Core.Defs.FlocqFloat.mk
        (FloatSpec.Core.Zaux.positiveToNat m : Int) e) (by norm_num) hmInt)
  · simp only [Binary.B2R]
    exact ne_of_lt (FloatSpec.Core.Float_prop.F2R_lt_0
      (beta:=2) (f:=FloatSpec.Core.Defs.FlocqFloat.mk
        (-(FloatSpec.Core.Zaux.positiveToNat m : Int)) e) (by norm_num)
        (by
          change -(FloatSpec.Core.Zaux.positiveToNat m : Int) < 0
          omega))

private theorem binaryFinite_decide_lt_zero {prec emax : Int}
    (s : Bool) (m : FloatSpec.Core.Zaux.Positive) (e : Int)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true) :
    decide (Binary.B2R (prec:=prec) (emax:=emax)
      (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded) < 0) = s := by
  have hm := positiveToNat_pos_bsn m
  have hmInt : (0 : Int) < (FloatSpec.Core.Zaux.positiveToNat m : Int) := by
    exact_mod_cast hm
  cases s
  · have hpos := FloatSpec.Core.Float_prop.F2R_gt_0
      (beta:=2) (f:=FloatSpec.Core.Defs.FlocqFloat.mk
        (FloatSpec.Core.Zaux.positiveToNat m : Int) e) (by norm_num) hmInt
    simp only [Binary.B2R]
    exact decide_eq_false_iff_not.mpr (not_lt_of_ge (le_of_lt hpos))
  · have hneg := FloatSpec.Core.Float_prop.F2R_lt_0
      (beta:=2) (f:=FloatSpec.Core.Defs.FlocqFloat.mk
        (-(FloatSpec.Core.Zaux.positiveToNat m : Int)) e) (by norm_num)
        (by
          change -(FloatSpec.Core.Zaux.positiveToNat m : Int) < 0
          omega)
    simp only [Binary.B2R]
    exact decide_eq_true_eq.mpr hneg

private theorem Bfma_returned_zero_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (fma_nan : Binary.BfmaNaNHandler prec emax)
    (mode : RoundingMode) (x y z : binary_float prec emax)
    (hprod : Binary.B2R (prec:=prec) (emax:=emax) x *
      Binary.B2R (prec:=prec) (emax:=emax) y = 0)
    (hz : Binary.B2R (prec:=prec) (emax:=emax) z = 0)
    (hout : Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z =
      binary_float.B754_zero (prec:=prec) (emax:=emax)
        (Binary.Bfma_szero mode x y z)) :
    let res := Binary.B2R (prec:=prec) (emax:=emax) x *
        Binary.B2R (prec:=prec) (emax:=emax) y +
        Binary.B2R (prec:=prec) (emax:=emax) z
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      Binary.B2R (prec:=prec) (emax:=emax)
          (Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z) =
          FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res ∧
        Binary.is_finite (prec:=prec) (emax:=emax)
          (Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z) = true ∧
        Binary.Bsign (prec:=prec) (emax:=emax)
          (Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z) =
          binaryFmaResultSign mode x y z res
    else
      Binary.B2FF (prec:=prec) (emax:=emax)
          (Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z) =
        Binary.binary_overflow (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool res 0) := by
  dsimp
  have hres : Binary.B2R (prec:=prec) (emax:=emax) x *
      Binary.B2R (prec:=prec) (emax:=emax) y +
      Binary.B2R (prec:=prec) (emax:=emax) z = 0 := by rw [hprod, hz]; norm_num
  rw [hres, Binary.roundR_zero_of_mode, abs_zero, Binary.Rlt_bool_zero_bpow]
  simp [hout, Binary.B2R, Binary.is_finite, Binary.Bsign,
    binaryFmaResultSign]

private theorem binaryFiniteGenericFormat {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (s : Bool) (m : FloatSpec.Core.Zaux.Positive) (e : Int)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true) :
    FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec)
      (Binary.B2R (prec:=prec) (emax:=emax)
        (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded)) := by
  have hpositive := positiveToNat_pos_bsn m
  have hcanonTrip := canonical_bounded_of_specFloat_bounded
    (prec:=prec) (emax:=emax) s (FloatSpec.Core.Zaux.positiveToNat m) e
    hpositive hbounded
  have hcanon :
      FloatSpec.Core.Generic_fmt.canonical 2
        (FLT_exp (3 - emax - prec) prec)
        (FloatSpec.Core.Defs.FlocqFloat.mk
          (if s then -((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int)
           else ((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int)) e) := by
    simpa [wp, PostCond.noThrow, pure] using hcanonTrip trivial
  change FloatSpec.Core.Generic_fmt.generic_format 2
    (FLT_exp (3 - emax - prec) prec)
    (F2R (FloatSpec.Core.Defs.FlocqFloat.mk
      (if s then -((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int)
       else ((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int)) e :
        FloatSpec.Core.Defs.FlocqFloat 2))
  exact FloatSpec.Core.Generic_fmt.generic_format_canonical
    (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
    (f:=FloatSpec.Core.Defs.FlocqFloat.mk
      (if s then -((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int)
       else ((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int)) e)
    hcanon

private theorem absBinaryFiniteLtEmax {prec emax : Int}
    (s : Bool) (m : FloatSpec.Core.Zaux.Positive) (e : Int)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true) :
    |Binary.B2R (prec:=prec) (emax:=emax)
      (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded)| <
        FloatSpec.Core.Raux.bpow 2 emax := by
  have hpositive := positiveToNat_pos_bsn m
  have hrange := range_bounded_of_specFloat_bounded
    (prec:=prec) (emax:=emax) (FloatSpec.Core.Zaux.positiveToNat m) e
    hpositive hbounded
  have htrip := bounded_lt_emax
    (prec:=prec) (emax:=emax) (FloatSpec.Core.Zaux.positiveToNat m) e hrange
  have hunsigned :
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk
        ((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int) e :
          FloatSpec.Core.Defs.FlocqFloat 2) <
        FloatSpec.Core.Raux.bpow 2 emax := by
    simpa [wp, PostCond.noThrow, pure] using htrip trivial
  have hnonnegative :
      0 ≤ F2R (FloatSpec.Core.Defs.FlocqFloat.mk
        ((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int) e :
          FloatSpec.Core.Defs.FlocqFloat 2) := by
    unfold F2R FloatSpec.Core.Defs.F2R
    positivity
  have habs :
      |F2R (FloatSpec.Core.Defs.FlocqFloat.mk
        (if s then -((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int)
         else ((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int)) e :
          FloatSpec.Core.Defs.FlocqFloat 2)| =
        F2R (FloatSpec.Core.Defs.FlocqFloat.mk
          ((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int) e :
            FloatSpec.Core.Defs.FlocqFloat 2) := by
    cases s <;>
      simp [F2R, FloatSpec.Core.Defs.F2R, abs_mul,
        abs_of_nonneg (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e))]
  change
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk
      (if s then -((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int)
       else ((FloatSpec.Core.Zaux.positiveToNat m : Nat) : Int)) e :
        FloatSpec.Core.Defs.FlocqFloat 2)| <
      FloatSpec.Core.Raux.bpow 2 emax
  rw [habs]
  exact hunsigned

private theorem roundRBinaryFinite {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (s : Bool) (m : FloatSpec.Core.Zaux.Positive) (e : Int)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true) :
    FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
        (rnd_of_mode mode)
        (Binary.B2R (prec:=prec) (emax:=emax)
          (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded)) =
      Binary.B2R (prec:=prec) (emax:=emax)
        (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded) := by
  exact FloatSpec.Core.Generic_fmt.roundR_generic
    (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
    (rnd:=rnd_of_mode mode)
    (x:=Binary.B2R (prec:=prec) (emax:=emax)
      (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded))
    (hβ:=by norm_num)
    (binaryFiniteGenericFormat (prec:=prec) (emax:=emax) s m e hbounded)

/-- A positive bounded binary input cannot overflow when square-rooted.  The
proof uses the representable ceiling `2^(emax-1)`, avoiding any rounding-mode
specific error estimate. -/
private theorem roundRSqrtBinaryFiniteLtEmax {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (m : FloatSpec.Core.Zaux.Positive) (e : Int)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true) :
    |FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
        (Real.sqrt (Binary.B2R (prec:=prec) (emax:=emax)
          (binary_float.B754_finite (prec:=prec) (emax:=emax)
            false m e hbounded)))| <
      FloatSpec.Core.Raux.bpow 2 emax := by
  let input := Binary.B2R (prec:=prec) (emax:=emax)
    (binary_float.B754_finite (prec:=prec) (emax:=emax) false m e hbounded)
  have hmNat := positiveToNat_pos_bsn m
  have hmInt : (0 : Int) < (FloatSpec.Core.Zaux.positiveToNat m : Int) := by
    exact_mod_cast hmNat
  have hinputPos : 0 < input := by
    simpa [input, Binary.B2R] using
      (FloatSpec.Core.Float_prop.F2R_gt_0
        (beta:=2)
        (f:=FloatSpec.Core.Defs.FlocqFloat.mk
          (FloatSpec.Core.Zaux.positiveToNat m : Int) e)
        (by norm_num) hmInt)
  have hinputLt : input < FloatSpec.Core.Raux.bpow 2 emax := by
    have h := absBinaryFiniteLtEmax (prec:=prec) (emax:=emax)
      false m e hbounded
    simpa [input, abs_of_pos hinputPos] using h
  have hbpowPos : 0 < FloatSpec.Core.Raux.bpow 2 emax := by
    have htrip := FloatSpec.Core.Raux.bpow_gt_0 2 emax (by norm_num)
    simpa [wp, PostCond.noThrow, pure] using htrip trivial
  have hsqrtLt : Real.sqrt input <
      Real.sqrt (FloatSpec.Core.Raux.bpow 2 emax) :=
    Real.sqrt_lt_sqrt (le_of_lt hinputPos) hinputLt
  let ceiling := FloatSpec.Core.Raux.bpow 2 (emax - 1)
  have hceilingPos : 0 < ceiling := by
    have htrip := FloatSpec.Core.Raux.bpow_gt_0 2 (emax - 1) (by norm_num)
    simpa [wp, PostCond.noThrow, pure, ceiling] using htrip trivial
  have hpowSquare : FloatSpec.Core.Raux.bpow 2 emax ≤ ceiling ^ 2 := by
    have hexp : emax ≤ 2 * (emax - 1) := by
      have hemax := (inferInstance : Prec_lt_emax prec emax).emax_ge_2
      omega
    have htrip := FloatSpec.Core.Raux.bpow_le 2 emax (2 * (emax - 1))
      (by norm_num) hexp
    have hpow : FloatSpec.Core.Raux.bpow 2 emax ≤
        FloatSpec.Core.Raux.bpow 2 (2 * (emax - 1)) := by
      have hrun := htrip trivial
      change (2 : ℝ) ^ emax ≤ (2 : ℝ) ^ (2 * (emax - 1)) at hrun
      simpa [FloatSpec.Core.Raux.bpow] using hrun
    have htwoNe : (2 : ℝ) ≠ 0 := by norm_num
    have hsquare : ceiling ^ 2 =
        FloatSpec.Core.Raux.bpow 2 (2 * (emax - 1)) := by
      calc
        ceiling ^ 2 = (2 : ℝ) ^ (emax - 1) * (2 : ℝ) ^ (emax - 1) := by
          simp [ceiling, FloatSpec.Core.Raux.bpow, pow_two]
        _ = (2 : ℝ) ^ ((emax - 1) + (emax - 1)) := by
          rw [zpow_add₀ htwoNe]
        _ = FloatSpec.Core.Raux.bpow 2 (2 * (emax - 1)) := by
          congr 1
          ring
    simpa [hsquare] using hpow
  have hsqrtCeiling : Real.sqrt (FloatSpec.Core.Raux.bpow 2 emax) ≤ ceiling :=
    Real.sqrt_le_iff.mpr ⟨le_of_lt hceilingPos, hpowSquare⟩
  have hsqrtInputLe : Real.sqrt input ≤ ceiling :=
    le_trans (le_of_lt hsqrtLt) hsqrtCeiling
  have hceilingFormat : FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec) ceiling := by
    have hfexp : FLT_exp (3 - emax - prec) prec (emax - 1) ≤ emax - 1 := by
      unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
      have hprec := (inferInstance : Prec_gt_0 prec).pos
      have hemax := (inferInstance : Prec_lt_emax prec emax).emax_ge_2
      apply max_le
      · omega
      · omega
    have htrip := FloatSpec.Core.Generic_fmt.generic_format_bpow'
      2 (FLT_exp (3 - emax - prec) prec) (emax - 1)
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, pure, ceiling,
      FloatSpec.Core.Raux.bpow] using
      htrip ⟨by norm_num, hfexp⟩
  have hroundLe : FloatSpec.Core.Generic_fmt.roundR 2
      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
        (Real.sqrt input) ≤ ceiling :=
    FloatSpec.Core.Generic_fmt.roundR_le_generic
      (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
      (rnd:=rnd_of_mode mode) (x:=Real.sqrt input) (y:=ceiling)
      (by norm_num) hceilingFormat hsqrtInputLe
  have hceilingLt : ceiling < FloatSpec.Core.Raux.bpow 2 emax := by
    have htrip := FloatSpec.Core.Raux.bpow_lt 2 (emax - 1) emax
      (by norm_num) (by omega)
    have hrun := htrip trivial
    change (2 : ℝ) ^ (emax - 1) < (2 : ℝ) ^ emax at hrun
    simpa [FloatSpec.Core.Raux.bpow, ceiling] using hrun
  have hroundLt : FloatSpec.Core.Generic_fmt.roundR 2
      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
        (Real.sqrt input) < FloatSpec.Core.Raux.bpow 2 emax :=
    lt_of_le_of_lt hroundLe hceilingLt
  have hroundNonneg : 0 ≤ FloatSpec.Core.Generic_fmt.roundR 2
      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
        (Real.sqrt input) :=
    FloatSpec.Core.Generic_fmt.roundR_nonneg_of_nonneg
      (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
      (rnd:=rnd_of_mode mode) (x:=Real.sqrt input) (by norm_num)
      (Real.sqrt_nonneg input)
  simpa [input, abs_of_nonneg hroundNonneg] using hroundLt

private theorem Bfma_returned_finite_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (fma_nan : Binary.BfmaNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax)
    (s : Bool) (m : FloatSpec.Core.Zaux.Positive) (e : Int)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat m) e = true)
    (hprod : Binary.B2R (prec:=prec) (emax:=emax) x *
      Binary.B2R (prec:=prec) (emax:=emax) y = 0)
    (hout : Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y
        (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded) =
      binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded) :
    let z := binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded
    let res := Binary.B2R (prec:=prec) (emax:=emax) x *
        Binary.B2R (prec:=prec) (emax:=emax) y +
        Binary.B2R (prec:=prec) (emax:=emax) z
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      Binary.B2R (prec:=prec) (emax:=emax)
          (Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z) =
          FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res ∧
        Binary.is_finite (prec:=prec) (emax:=emax)
          (Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z) = true ∧
        Binary.Bsign (prec:=prec) (emax:=emax)
          (Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z) =
          binaryFmaResultSign mode x y z res
    else
      Binary.B2FF (prec:=prec) (emax:=emax)
          (Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z) =
        Binary.binary_overflow (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool res 0) := by
  dsimp
  have hres : Binary.B2R (prec:=prec) (emax:=emax) x *
      Binary.B2R (prec:=prec) (emax:=emax) y +
      Binary.B2R (prec:=prec) (emax:=emax)
        (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded) =
      Binary.B2R (prec:=prec) (emax:=emax)
        (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded) := by
    rw [hprod]; norm_num
  have hround := roundRBinaryFinite (prec:=prec) (emax:=emax) mode s m e hbounded
  have hlt := absBinaryFiniteLtEmax (prec:=prec) (emax:=emax) s m e hbounded
  have hcond : FloatSpec.Core.Raux.Rlt_bool
      |FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
          (Binary.B2R (prec:=prec) (emax:=emax) x *
            Binary.B2R (prec:=prec) (emax:=emax) y +
            Binary.B2R (prec:=prec) (emax:=emax)
              (binary_float.B754_finite (prec:=prec) (emax:=emax) s m e hbounded))|
      (FloatSpec.Core.Raux.bpow 2 emax) = true := by
    simp [hres, hround, FloatSpec.Core.Raux.Rlt_bool, hlt]
  rw [ite_eq_left hcond, hout]
  refine ⟨?_, rfl, ?_⟩
  · simpa [hres] using hround.symm
  · simp [binaryFmaResultSign, hres,
      binaryFinite_ne_zero (prec:=prec) (emax:=emax) s m e hbounded,
      binaryFinite_decide_lt_zero (prec:=prec) (emax:=emax) s m e hbounded,
      Binary.Bsign]

private theorem Bfma_normalized_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (fma_nan : Binary.BfmaNaNHandler prec emax)
    (mode : RoundingMode) (x y z : binary_float prec emax) (m e : Int)
    (hinput : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
        FloatSpec.Core.Defs.FlocqFloat 2) =
      Binary.B2R x * Binary.B2R y + Binary.B2R z)
    (hout : Binary.Bfma fma_nan mode x y z =
      Binary.normalize mode m e (Binary.Bfma_szero mode x y z)) :
    let res := Binary.B2R x * Binary.B2R y + Binary.B2R z
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      Binary.B2R (Binary.Bfma fma_nan mode x y z) =
          FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res ∧
        Binary.is_finite (Binary.Bfma fma_nan mode x y z) = true ∧
        Binary.Bsign (Binary.Bfma fma_nan mode x y z) =
          binaryFmaResultSign mode x y z res
    else
      Binary.B2FF (prec:=prec) (emax:=emax) (Binary.Bfma fma_nan mode x y z) =
        Binary.binary_overflow (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool res 0) := by
  have href := Binary.normalize_correct (prec:=prec) (emax:=emax)
    mode m e (Binary.Bfma_szero mode x y z)
  simp only [F2R, FloatSpec.Core.Defs.F2R] at hinput
  rw [← hinput]
  simpa [hout, binaryFmaResultSign, zpow_ne_zero] using href

-- Coq: `Binary.v:Bplus_correct`, on the proof-carrying Binary carrier.
theorem Bplus_correct_from_exp_instances {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (plus_nan : Binary.BplusNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax) :
    Binary.is_finite (prec:=prec) (emax:=emax) x = true →
    Binary.is_finite (prec:=prec) (emax:=emax) y = true →
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Binary.B2R (prec:=prec) (emax:=emax) x +
             Binary.B2R (prec:=prec) (emax:=emax) y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      Binary.B2R (prec:=prec) (emax:=emax)
          (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode x y) =
        FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Binary.B2R (prec:=prec) (emax:=emax) x +
             Binary.B2R (prec:=prec) (emax:=emax) y) ∧
      Binary.is_finite (prec:=prec) (emax:=emax)
          (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode x y) = true ∧
      Binary.Bsign (prec:=prec) (emax:=emax)
          (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode x y) =
        binaryPlusResultSign mode
          (Binary.Bsign (prec:=prec) (emax:=emax) x)
          (Binary.Bsign (prec:=prec) (emax:=emax) y)
          (Binary.B2R (prec:=prec) (emax:=emax) x +
           Binary.B2R (prec:=prec) (emax:=emax) y)
    else
      Binary.B2FF (prec:=prec) (emax:=emax)
          (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode x y) =
          Binary.binary_overflow (prec:=prec) (emax:=emax) mode
            (Binary.Bsign (prec:=prec) (emax:=emax) x) ∧
        Binary.Bsign (prec:=prec) (emax:=emax) x =
          Binary.Bsign (prec:=prec) (emax:=emax) y := by
  classical
  intro hx hy
  cases x with
  | B754_zero sx =>
      cases y with
      | B754_zero sy =>
          cases mode <;> cases sx <;> cases sy <;>
            simp [Binary.Bplus, Binary.B2R, Binary.is_finite, Binary.Bsign,
              Binary.roundR_zero_of_mode, Binary.Rlt_bool_zero_bpow,
              binaryPlusResultSign]
      | B754_infinity sy => simp [Binary.is_finite] at hy
      | B754_nan sy payload hpayload => simp [Binary.is_finite] at hy
      | B754_finite sy my ey Hy =>
          have hround := roundRBinaryFinite (prec:=prec) (emax:=emax)
            mode sy my ey Hy
          have hlt := absBinaryFiniteLtEmax (prec:=prec) (emax:=emax)
            sy my ey Hy
          have hcond :
              FloatSpec.Core.Raux.Rlt_bool
                |FloatSpec.Core.Generic_fmt.roundR 2
                  (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                  (0 + Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_finite (prec:=prec) (emax:=emax)
                      sy my ey Hy))|
                (FloatSpec.Core.Raux.bpow 2 emax) = true := by
            simp [hround, FloatSpec.Core.Raux.Rlt_bool, hlt]
          have hcond' :
              FloatSpec.Core.Raux.Rlt_bool
                |FloatSpec.Core.Generic_fmt.roundR 2
                  (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                  (Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_zero (prec:=prec) (emax:=emax) sx) +
                   Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_finite (prec:=prec) (emax:=emax)
                      sy my ey Hy))|
                (FloatSpec.Core.Raux.bpow 2 emax) = true := by
            simpa [Binary.B2R] using hcond
          rw [ite_eq_left hcond']
          constructor
          · simpa [Binary.Bplus, Binary.B2R] using hround.symm
          · constructor
            · simp [Binary.Bplus, Binary.is_finite]
            · have hmyPos := positiveToNat_pos_bsn my
              have hpowPos : (0 : ℝ) < (2 : ℝ) ^ ey := zpow_pos (by norm_num) ey
              cases sy
              · have hvaluePos :
                    0 < Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        false my ey Hy) := by
                    simp [Binary.B2R, F2R, FloatSpec.Core.Defs.F2R]
                    positivity
                change 0 < F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                  ((FloatSpec.Core.Zaux.positiveToNat my : Nat) : Int) ey :
                    FloatSpec.Core.Defs.FlocqFloat 2) at hvaluePos
                have hmReal : (0 : ℝ) < FloatSpec.Core.Zaux.positiveToNat my :=
                  Nat.cast_pos.mpr hmyPos
                simp [Binary.Bplus, Binary.Bsign, binaryPlusResultSign,
                  Binary.B2R, Nat.ne_of_gt hmyPos, ne_of_gt hpowPos,
                  ne_of_gt hvaluePos, le_of_lt hvaluePos,
                  mul_pos hmReal hpowPos] <;> positivity
              · have hvalueNeg :
                    Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        true my ey Hy) < 0 := by
                    simp [Binary.B2R, F2R, FloatSpec.Core.Defs.F2R]
                    positivity
                change F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                  (-((FloatSpec.Core.Zaux.positiveToNat my : Nat) : Int)) ey :
                    FloatSpec.Core.Defs.FlocqFloat 2) < 0 at hvalueNeg
                have hmReal : (0 : ℝ) < FloatSpec.Core.Zaux.positiveToNat my :=
                  Nat.cast_pos.mpr hmyPos
                simp [Binary.Bplus, Binary.Bsign, binaryPlusResultSign,
                  Binary.B2R, Nat.ne_of_gt hmyPos, ne_of_gt hpowPos,
                  ne_of_lt hvalueNeg, hvalueNeg, mul_pos hmReal hpowPos]
  | B754_infinity sx => simp [Binary.is_finite] at hx
  | B754_nan sx payload hpayload => simp [Binary.is_finite] at hx
  | B754_finite sx mx ex Hx =>
      cases y with
      | B754_zero sy =>
          have hround := roundRBinaryFinite (prec:=prec) (emax:=emax)
            mode sx mx ex Hx
          have hlt := absBinaryFiniteLtEmax (prec:=prec) (emax:=emax)
            sx mx ex Hx
          have hcond :
              FloatSpec.Core.Raux.Rlt_bool
                |FloatSpec.Core.Generic_fmt.roundR 2
                  (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                  (Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_finite (prec:=prec) (emax:=emax)
                      sx mx ex Hx) + 0)|
                (FloatSpec.Core.Raux.bpow 2 emax) = true := by
            simp [hround, FloatSpec.Core.Raux.Rlt_bool, hlt]
          have hcond' :
              FloatSpec.Core.Raux.Rlt_bool
                |FloatSpec.Core.Generic_fmt.roundR 2
                  (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                  (Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_finite (prec:=prec) (emax:=emax)
                      sx mx ex Hx) +
                   Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_zero (prec:=prec) (emax:=emax) sy))|
                (FloatSpec.Core.Raux.bpow 2 emax) = true := by
            simpa [Binary.B2R] using hcond
          rw [ite_eq_left hcond']
          constructor
          · simpa [Binary.Bplus, Binary.B2R] using hround.symm
          · constructor
            · simp [Binary.Bplus, Binary.is_finite]
            · have hmxPos := positiveToNat_pos_bsn mx
              have hpowPos : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) ex
              cases sx
              · have hvaluePos :
                    0 < Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        false mx ex Hx) := by
                    simp [Binary.B2R, F2R, FloatSpec.Core.Defs.F2R]
                    positivity
                change 0 < F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                  ((FloatSpec.Core.Zaux.positiveToNat mx : Nat) : Int) ex :
                    FloatSpec.Core.Defs.FlocqFloat 2) at hvaluePos
                have hmReal : (0 : ℝ) < FloatSpec.Core.Zaux.positiveToNat mx :=
                  Nat.cast_pos.mpr hmxPos
                simp [Binary.Bplus, Binary.Bsign, binaryPlusResultSign,
                  Binary.B2R, Nat.ne_of_gt hmxPos, ne_of_gt hpowPos,
                  ne_of_gt hvaluePos, le_of_lt hvaluePos,
                  mul_pos hmReal hpowPos] <;> positivity
              · have hvalueNeg :
                    Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        true mx ex Hx) < 0 := by
                    simp [Binary.B2R, F2R, FloatSpec.Core.Defs.F2R]
                    positivity
                change F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                  (-((FloatSpec.Core.Zaux.positiveToNat mx : Nat) : Int)) ex :
                    FloatSpec.Core.Defs.FlocqFloat 2) < 0 at hvalueNeg
                have hmReal : (0 : ℝ) < FloatSpec.Core.Zaux.positiveToNat mx :=
                  Nat.cast_pos.mpr hmxPos
                simp [Binary.Bplus, Binary.Bsign, binaryPlusResultSign,
                  Binary.B2R, Nat.ne_of_gt hmxPos, ne_of_gt hpowPos,
                  ne_of_lt hvalueNeg, hvalueNeg, mul_pos hmReal hpowPos]
      | B754_infinity sy => simp [Binary.is_finite] at hy
      | B754_nan sy payload hpayload => simp [Binary.is_finite] at hy
      | B754_finite sy my ey Hy =>
          let mxn := FloatSpec.Core.Zaux.positiveToNat mx
          let myn := FloatSpec.Core.Zaux.positiveToNat my
          let ez := min ex ey
          let m := Fplus_naive sx mxn ex sy myn ey ez
          have hsumRaw := Fplus_naive_correct sx mxn ex sy myn ey ez
            (min_le_left ex ey) (min_le_right ex ey)
          have hsum :
              F2R (FloatSpec.Core.Defs.FlocqFloat.mk m ez :
                FloatSpec.Core.Defs.FlocqFloat 2) =
                Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_finite (prec:=prec) (emax:=emax)
                      sx mx ex Hx) +
                  Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_finite (prec:=prec) (emax:=emax)
                      sy my ey Hy) := by
            simpa [m, ez, mxn, myn, Binary.B2R,
              FloatSpec.Core.Zaux.cond_Zopp] using hsumRaw
          by_cases hm0 : m = 0
          · have hsumZero :
                Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_finite (prec:=prec) (emax:=emax)
                      sx mx ex Hx) +
                  Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_finite (prec:=prec) (emax:=emax)
                      sy my ey Hy) = 0 := by
              have hFzero : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m ez :
                  FloatSpec.Core.Defs.FlocqFloat 2) = 0 := by
                rw [hm0]
                simp [F2R, FloatSpec.Core.Defs.F2R]
              exact hsum.symm.trans hFzero
            simp [hm0, F2R, FloatSpec.Core.Defs.F2R] at hsumRaw
            have hsNe : sx ≠ sy := by
              intro hs
              subst sy
              have hmxPos := positiveToNat_pos_bsn mx
              have hmyPos := positiveToNat_pos_bsn my
              have hxPowPos : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) ex
              have hyPowPos : (0 : ℝ) < (2 : ℝ) ^ ey := zpow_pos (by norm_num) ey
              cases sx
              · have hxPos :
                    0 < Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        false mx ex Hx) := by
                    simp [Binary.B2R, F2R, FloatSpec.Core.Defs.F2R]
                    positivity
                have hyPos :
                    0 < Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        false my ey Hy) := by
                    simp [Binary.B2R, F2R, FloatSpec.Core.Defs.F2R]
                    positivity
                linarith
              · have hxNeg :
                    Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        true mx ex Hx) < 0 := by
                    simp [Binary.B2R, F2R, FloatSpec.Core.Defs.F2R]
                    positivity
                have hyNeg :
                    Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        true my ey Hy) < 0 := by
                    simp [Binary.B2R, F2R, FloatSpec.Core.Defs.F2R]
                    positivity
                linarith
            cases mode <;> cases sx <;> cases sy <;>
              simp_all [Binary.Bplus, mxn, myn, ez, m, hm0,
                Binary.B2R, Binary.is_finite, Binary.Bsign,
                binaryPlusResultSign, Binary.roundR_zero_of_mode,
                Binary.Rlt_bool_zero_bpow,
                FloatSpec.Core.Zaux.cond_Zopp] <;>
              rw [← hsum] <;>
              simp [Binary.roundR_zero_of_mode, Binary.Rlt_bool_zero_bpow]
          · by_cases hmpos : 0 < m
            · let z := binary_round (prec:=prec) (emax:=emax)
                  mode false m.toNat ez
              have hmnonneg : 0 ≤ m := le_of_lt hmpos
              have hmcast : (m.toNat : Int) = m := Int.toNat_of_nonneg hmnonneg
              have hmnatPos : 0 < m.toNat := by
                omega
              have hround := binary_round_correct (prec:=prec) (emax:=emax)
                mode false m.toNat ez hmnatPos
              have hinput :
                  SF2R 2 (StandardFloat.S754_finite false m.toNat ez) =
                    Binary.B2R (prec:=prec) (emax:=emax)
                        (binary_float.B754_finite (prec:=prec) (emax:=emax)
                          sx mx ex Hx) +
                      Binary.B2R (prec:=prec) (emax:=emax)
                        (binary_float.B754_finite (prec:=prec) (emax:=emax)
                          sy my ey Hy) := by
                simpa [SF2R, F2R, FloatSpec.Core.Defs.F2R, hmcast] using hsum
              have hsumPos :
                  0 < Binary.B2R (prec:=prec) (emax:=emax)
                        (binary_float.B754_finite (prec:=prec) (emax:=emax)
                          sx mx ex Hx) +
                      Binary.B2R (prec:=prec) (emax:=emax)
                        (binary_float.B754_finite (prec:=prec) (emax:=emax)
                          sy my ey Hy) := by
                rw [← hsum]
                unfold F2R FloatSpec.Core.Defs.F2R
                exact mul_pos (by exact_mod_cast hmpos)
                  (zpow_pos (by norm_num : (0 : ℝ) < 2) ez)
              have hnotnan : is_nan_SF z = false := by
                simpa [z] using is_nan_binary_round (prec:=prec) (emax:=emax)
                  mode false m.toNat ez
              have hB2R :
                  Binary.B2R (prec:=prec) (emax:=emax)
                    (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sx mx ex Hx)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sy my ey Hy)) = SF2R 2 z := by
                simpa [Binary.Bplus, mxn, myn, ez, m, hm0, hmpos, z] using
                  Binary.B2R_standardFloatToBinaryFloatOfNotNaN
                    (prec:=prec) (emax:=emax) z hround.1 hnotnan
              have hfiniteBridge :
                  Binary.is_finite (prec:=prec) (emax:=emax)
                    (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sx mx ex Hx)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sy my ey Hy)) = is_finite_SF z := by
                simpa [Binary.Bplus, mxn, myn, ez, m, hm0, hmpos, z] using
                  Binary.is_finite_standardFloatToBinaryFloatOfNotNaN
                    (prec:=prec) (emax:=emax) z hround.1 hnotnan
              have hsignBridge :
                  Binary.Bsign (prec:=prec) (emax:=emax)
                    (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sx mx ex Hx)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sy my ey Hy)) = sign_SF z := by
                simpa [Binary.Bplus, mxn, myn, ez, m, hm0, hmpos, z] using
                  Binary.Bsign_standardFloatToBinaryFloatOfNotNaN
                    (prec:=prec) (emax:=emax) z hround.1 hnotnan
              have hB2FF :
                  Binary.B2FF (prec:=prec) (emax:=emax)
                    (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sx mx ex Hx)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sy my ey Hy)) = SF2FF z := by
                simpa [Binary.Bplus, mxn, myn, ez, m, hm0, hmpos, z] using
                  Binary.B2FF_standardFloatToBinaryFloatOfNotNaN
                    (prec:=prec) (emax:=emax) z hround.1 hnotnan
              by_cases hlt :
                  FloatSpec.Core.Raux.Rlt_bool
                    |FloatSpec.Core.Generic_fmt.roundR 2
                      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                        (Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sx mx ex Hx) +
                         Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sy my ey Hy))|
                    (FloatSpec.Core.Raux.bpow 2 emax) = true
              · rw [ite_eq_left hlt]
                have hltAux :
                    FloatSpec.Core.Raux.Rlt_bool
                      |FloatSpec.Core.Generic_fmt.roundR 2
                        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                        (SF2R 2 (StandardFloat.S754_finite false m.toNat ez))|
                      (FloatSpec.Core.Raux.bpow 2 emax) = true := by
                  simpa [hinput] using hlt
                have hbranch := hround.2
                dsimp at hbranch
                rw [hltAux] at hbranch
                constructor
                · calc
                    Binary.B2R (prec:=prec) (emax:=emax)
                        (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                          (binary_float.B754_finite (prec:=prec) (emax:=emax)
                            sx mx ex Hx)
                          (binary_float.B754_finite (prec:=prec) (emax:=emax)
                            sy my ey Hy)) = SF2R 2 z := hB2R
                    _ = FloatSpec.Core.Generic_fmt.roundR 2
                        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                        (Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sx mx ex Hx) +
                         Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sy my ey Hy)) := by simpa [z, hinput] using hbranch.1
                · constructor
                  · exact hfiniteBridge.trans hbranch.2.1
                  · calc
                      Binary.Bsign (prec:=prec) (emax:=emax)
                          (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sx mx ex Hx)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sy my ey Hy)) = sign_SF z := hsignBridge
                      _ = false := hbranch.2.2
                      _ = binaryPlusResultSign mode sx sy
                          (Binary.B2R (prec:=prec) (emax:=emax)
                              (binary_float.B754_finite (prec:=prec) (emax:=emax)
                                sx mx ex Hx) +
                           Binary.B2R (prec:=prec) (emax:=emax)
                              (binary_float.B754_finite (prec:=prec) (emax:=emax)
                                sy my ey Hy)) := by
                            simp [binaryPlusResultSign, ne_of_gt hsumPos,
                              not_lt_of_ge (le_of_lt hsumPos)]
              · rw [ite_eq_right hlt]
                have hltFalse :
                    FloatSpec.Core.Raux.Rlt_bool
                      |FloatSpec.Core.Generic_fmt.roundR 2
                        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                        (SF2R 2 (StandardFloat.S754_finite false m.toNat ez))|
                      (FloatSpec.Core.Raux.bpow 2 emax) = false := by
                  have := Bool.eq_false_of_not_eq_true hlt
                  simpa [hinput] using this
                have hbranch := hround.2
                dsimp at hbranch
                rw [hltFalse] at hbranch
                have hover : z = bsn_binary_overflow
                    (prec:=prec) (emax:=emax) mode false := by
                  simpa [z] using hbranch
                have hnotLt : ¬
                    |FloatSpec.Core.Generic_fmt.roundR 2
                      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                        (Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sx mx ex Hx) +
                         Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sy my ey Hy))| < FloatSpec.Core.Raux.bpow 2 emax := by
                  intro hreal
                  exact hlt (by simp [FloatSpec.Core.Raux.Rlt_bool, hreal])
                have hoverBound : FloatSpec.Core.Raux.bpow 2 emax ≤
                    |FloatSpec.Core.Generic_fmt.round_to_generic 2
                      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                        (Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sx mx ex Hx) +
                         Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sy my ey Hy))| := by
                  have := le_of_not_gt hnotLt
                  simpa [FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR]
                    using this
                have hxRange := range_bounded_of_specFloat_bounded
                  (prec:=prec) (emax:=emax) mxn ex (positiveToNat_pos_bsn mx) Hx
                have hyRange := range_bounded_of_specFloat_bounded
                  (prec:=prec) (emax:=emax) myn ey (positiveToNat_pos_bsn my) Hy
                have hsign := ExperimentalSingleNaNArithmetic.sign_plus_overflow
                  (prec:=prec) (emax:=emax) mode sx mxn ex sy myn ey
                  hxRange hyRange
                  (by simpa [mxn, myn, Binary.B2R, SF2R,
                      FloatSpec.Core.Zaux.cond_Zopp] using hoverBound)
                have hsxFalse : sx = false := by
                  calc
                    sx = FloatSpec.Core.Raux.Rlt_bool
                        (Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sx mx ex Hx) +
                         Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sy my ey Hy)) 0 := by
                          simpa [mxn, myn, Binary.B2R, SF2R,
                            FloatSpec.Core.Zaux.cond_Zopp] using hsign.1
                    _ = false := by
                          simp [FloatSpec.Core.Raux.Rlt_bool,
                            not_lt_of_ge (le_of_lt hsumPos)]
                constructor
                · calc
                    Binary.B2FF (prec:=prec) (emax:=emax)
                        (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                          (binary_float.B754_finite (prec:=prec) (emax:=emax)
                            sx mx ex Hx)
                          (binary_float.B754_finite (prec:=prec) (emax:=emax)
                            sy my ey Hy)) = SF2FF z := hB2FF
                    _ = SF2FF (bsn_binary_overflow
                          (prec:=prec) (emax:=emax) mode false) := by rw [hover]
                    _ = Binary.binary_overflow (prec:=prec) (emax:=emax)
                          mode sx := by simp [Binary.binary_overflow, hsxFalse]
                · exact hsign.2
            · have hmneg : m < 0 := lt_of_le_of_ne (le_of_not_gt hmpos) hm0
              let z := binary_round (prec:=prec) (emax:=emax)
                mode true m.natAbs ez
              have hmabsPos : 0 < m.natAbs := Int.natAbs_pos.mpr (ne_of_lt hmneg)
              have hmcast : -((m.natAbs : Nat) : Int) = m :=
                (Int.eq_neg_natAbs_of_nonpos (le_of_lt hmneg)).symm
              have hround := binary_round_correct (prec:=prec) (emax:=emax)
                mode true m.natAbs ez hmabsPos
              have hinput :
                  SF2R 2 (StandardFloat.S754_finite true m.natAbs ez) =
                    Binary.B2R (prec:=prec) (emax:=emax)
                        (binary_float.B754_finite (prec:=prec) (emax:=emax)
                          sx mx ex Hx) +
                      Binary.B2R (prec:=prec) (emax:=emax)
                        (binary_float.B754_finite (prec:=prec) (emax:=emax)
                          sy my ey Hy) := by
                calc
                  SF2R 2 (StandardFloat.S754_finite true m.natAbs ez) =
                      F2R (FloatSpec.Core.Defs.FlocqFloat.mk m ez :
                        FloatSpec.Core.Defs.FlocqFloat 2) := by
                    unfold SF2R F2R FloatSpec.Core.Defs.F2R
                    norm_num
                    rw [abs_of_neg (by exact_mod_cast hmneg)]
                    ring
                  _ = _ := hsum
              have hsumNeg :
                  Binary.B2R (prec:=prec) (emax:=emax)
                        (binary_float.B754_finite (prec:=prec) (emax:=emax)
                          sx mx ex Hx) +
                      Binary.B2R (prec:=prec) (emax:=emax)
                        (binary_float.B754_finite (prec:=prec) (emax:=emax)
                          sy my ey Hy) < 0 := by
                rw [← hsum]
                unfold F2R FloatSpec.Core.Defs.F2R
                exact mul_neg_of_neg_of_pos (by exact_mod_cast hmneg)
                  (zpow_pos (by norm_num : (0 : ℝ) < 2) ez)
              have hnotnan : is_nan_SF z = false := by
                simpa [z] using is_nan_binary_round (prec:=prec) (emax:=emax)
                  mode true m.natAbs ez
              have hB2R :
                  Binary.B2R (prec:=prec) (emax:=emax)
                    (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sx mx ex Hx)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sy my ey Hy)) = SF2R 2 z := by
                simpa [Binary.Bplus, mxn, myn, ez, m, hm0, hmpos, z] using
                  Binary.B2R_standardFloatToBinaryFloatOfNotNaN
                    (prec:=prec) (emax:=emax) z hround.1 hnotnan
              have hfiniteBridge :
                  Binary.is_finite (prec:=prec) (emax:=emax)
                    (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sx mx ex Hx)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sy my ey Hy)) = is_finite_SF z := by
                simpa [Binary.Bplus, mxn, myn, ez, m, hm0, hmpos, z] using
                  Binary.is_finite_standardFloatToBinaryFloatOfNotNaN
                    (prec:=prec) (emax:=emax) z hround.1 hnotnan
              have hsignBridge :
                  Binary.Bsign (prec:=prec) (emax:=emax)
                    (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sx mx ex Hx)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sy my ey Hy)) = sign_SF z := by
                simpa [Binary.Bplus, mxn, myn, ez, m, hm0, hmpos, z] using
                  Binary.Bsign_standardFloatToBinaryFloatOfNotNaN
                    (prec:=prec) (emax:=emax) z hround.1 hnotnan
              have hB2FF :
                  Binary.B2FF (prec:=prec) (emax:=emax)
                    (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sx mx ex Hx)
                      (binary_float.B754_finite (prec:=prec) (emax:=emax)
                        sy my ey Hy)) = SF2FF z := by
                simpa [Binary.Bplus, mxn, myn, ez, m, hm0, hmpos, z] using
                  Binary.B2FF_standardFloatToBinaryFloatOfNotNaN
                    (prec:=prec) (emax:=emax) z hround.1 hnotnan
              by_cases hlt :
                  FloatSpec.Core.Raux.Rlt_bool
                    |FloatSpec.Core.Generic_fmt.roundR 2
                      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                        (Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sx mx ex Hx) +
                         Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sy my ey Hy))|
                    (FloatSpec.Core.Raux.bpow 2 emax) = true
              · rw [ite_eq_left hlt]
                have hltAux :
                    FloatSpec.Core.Raux.Rlt_bool
                      |FloatSpec.Core.Generic_fmt.roundR 2
                        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                        (SF2R 2 (StandardFloat.S754_finite true m.natAbs ez))|
                      (FloatSpec.Core.Raux.bpow 2 emax) = true := by
                  simpa [hinput] using hlt
                have hbranch := hround.2
                dsimp at hbranch
                rw [hltAux] at hbranch
                constructor
                · calc
                    Binary.B2R (prec:=prec) (emax:=emax)
                        (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                          (binary_float.B754_finite (prec:=prec) (emax:=emax)
                            sx mx ex Hx)
                          (binary_float.B754_finite (prec:=prec) (emax:=emax)
                            sy my ey Hy)) = SF2R 2 z := hB2R
                    _ = FloatSpec.Core.Generic_fmt.roundR 2
                        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                        (Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sx mx ex Hx) +
                         Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sy my ey Hy)) := by simpa [z, hinput] using hbranch.1
                · constructor
                  · exact hfiniteBridge.trans hbranch.2.1
                  · calc
                      Binary.Bsign (prec:=prec) (emax:=emax)
                          (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sx mx ex Hx)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sy my ey Hy)) = sign_SF z := hsignBridge
                      _ = true := hbranch.2.2
                      _ = binaryPlusResultSign mode sx sy
                          (Binary.B2R (prec:=prec) (emax:=emax)
                              (binary_float.B754_finite (prec:=prec) (emax:=emax)
                                sx mx ex Hx) +
                           Binary.B2R (prec:=prec) (emax:=emax)
                              (binary_float.B754_finite (prec:=prec) (emax:=emax)
                                sy my ey Hy)) := by
                            simp [binaryPlusResultSign, ne_of_lt hsumNeg, hsumNeg]
              · rw [ite_eq_right hlt]
                have hltFalse :
                    FloatSpec.Core.Raux.Rlt_bool
                      |FloatSpec.Core.Generic_fmt.roundR 2
                        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                        (SF2R 2 (StandardFloat.S754_finite true m.natAbs ez))|
                      (FloatSpec.Core.Raux.bpow 2 emax) = false := by
                  have := Bool.eq_false_of_not_eq_true hlt
                  simpa [hinput] using this
                have hbranch := hround.2
                dsimp at hbranch
                rw [hltFalse] at hbranch
                have hover : z = bsn_binary_overflow
                    (prec:=prec) (emax:=emax) mode true := by
                  simpa [z] using hbranch
                have hnotLt : ¬
                    |FloatSpec.Core.Generic_fmt.roundR 2
                      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                        (Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sx mx ex Hx) +
                         Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sy my ey Hy))| < FloatSpec.Core.Raux.bpow 2 emax := by
                  intro hreal
                  exact hlt (by simp [FloatSpec.Core.Raux.Rlt_bool, hreal])
                have hoverBound : FloatSpec.Core.Raux.bpow 2 emax ≤
                    |FloatSpec.Core.Generic_fmt.round_to_generic 2
                      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                        (Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sx mx ex Hx) +
                         Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sy my ey Hy))| := by
                  have := le_of_not_gt hnotLt
                  simpa [FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR]
                    using this
                have hxRange := range_bounded_of_specFloat_bounded
                  (prec:=prec) (emax:=emax) mxn ex (positiveToNat_pos_bsn mx) Hx
                have hyRange := range_bounded_of_specFloat_bounded
                  (prec:=prec) (emax:=emax) myn ey (positiveToNat_pos_bsn my) Hy
                have hsign := ExperimentalSingleNaNArithmetic.sign_plus_overflow
                  (prec:=prec) (emax:=emax) mode sx mxn ex sy myn ey
                  hxRange hyRange
                  (by simpa [mxn, myn, Binary.B2R, SF2R,
                      FloatSpec.Core.Zaux.cond_Zopp] using hoverBound)
                have hsxTrue : sx = true := by
                  calc
                    sx = FloatSpec.Core.Raux.Rlt_bool
                        (Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sx mx ex Hx) +
                         Binary.B2R (prec:=prec) (emax:=emax)
                            (binary_float.B754_finite (prec:=prec) (emax:=emax)
                              sy my ey Hy)) 0 := by
                          simpa [mxn, myn, Binary.B2R, SF2R,
                            FloatSpec.Core.Zaux.cond_Zopp] using hsign.1
                    _ = true := by
                          simp [FloatSpec.Core.Raux.Rlt_bool, hsumNeg]
                constructor
                · calc
                    Binary.B2FF (prec:=prec) (emax:=emax)
                        (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode
                          (binary_float.B754_finite (prec:=prec) (emax:=emax)
                            sx mx ex Hx)
                          (binary_float.B754_finite (prec:=prec) (emax:=emax)
                            sy my ey Hy)) = SF2FF z := hB2FF
                    _ = SF2FF (bsn_binary_overflow
                          (prec:=prec) (emax:=emax) mode true) := by rw [hover]
                    _ = Binary.binary_overflow (prec:=prec) (emax:=emax)
                          mode sx := by simp [Binary.binary_overflow, hsxTrue]
                · exact hsign.2

-- Source ID: IEEE754/Binary.v:Bplus_correct:25364
-- Target: Bplus_correct
/-- Coq `Binary.v:Bplus_correct`; the FLT exponent instances are canonical
and therefore not caller-supplied source premises. -/
theorem Bplus_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (plus_nan : Binary.BplusNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax) :
    Binary.is_finite (prec:=prec) (emax:=emax) x = true →
    Binary.is_finite (prec:=prec) (emax:=emax) y = true →
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Binary.B2R (prec:=prec) (emax:=emax) x +
             Binary.B2R (prec:=prec) (emax:=emax) y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      Binary.B2R (prec:=prec) (emax:=emax)
          (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode x y) =
        FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Binary.B2R (prec:=prec) (emax:=emax) x +
             Binary.B2R (prec:=prec) (emax:=emax) y) ∧
      Binary.is_finite (prec:=prec) (emax:=emax)
          (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode x y) = true ∧
      Binary.Bsign (prec:=prec) (emax:=emax)
          (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode x y) =
        binaryPlusResultSign mode
          (Binary.Bsign (prec:=prec) (emax:=emax) x)
          (Binary.Bsign (prec:=prec) (emax:=emax) y)
          (Binary.B2R (prec:=prec) (emax:=emax) x +
           Binary.B2R (prec:=prec) (emax:=emax) y)
    else
      Binary.B2FF (prec:=prec) (emax:=emax)
          (Binary.Bplus (prec:=prec) (emax:=emax) plus_nan mode x y) =
          Binary.binary_overflow (prec:=prec) (emax:=emax) mode
            (Binary.Bsign (prec:=prec) (emax:=emax) x) ∧
        Binary.Bsign (prec:=prec) (emax:=emax) x =
          Binary.Bsign (prec:=prec) (emax:=emax) y :=
  Bplus_correct_from_exp_instances plus_nan mode x y

-- Source ID: IEEE754/Binary.v:Bminus_correct:26726
-- Target: Bminus_correct
-- Coq: `Binary.v:Bminus_correct`, reduced exactly as upstream to addition of
-- the negated right operand.
theorem Bminus_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (minus_nan : Binary.BminusNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax) :
    Binary.is_finite (prec:=prec) (emax:=emax) x = true →
    Binary.is_finite (prec:=prec) (emax:=emax) y = true →
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Binary.B2R (prec:=prec) (emax:=emax) x -
             Binary.B2R (prec:=prec) (emax:=emax) y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      Binary.B2R (prec:=prec) (emax:=emax)
          (Binary.Bminus (prec:=prec) (emax:=emax) minus_nan mode x y) =
        FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Binary.B2R (prec:=prec) (emax:=emax) x -
             Binary.B2R (prec:=prec) (emax:=emax) y) ∧
      Binary.is_finite (prec:=prec) (emax:=emax)
          (Binary.Bminus (prec:=prec) (emax:=emax) minus_nan mode x y) = true ∧
      Binary.Bsign (prec:=prec) (emax:=emax)
          (Binary.Bminus (prec:=prec) (emax:=emax) minus_nan mode x y) =
        binaryMinusResultSign mode
          (Binary.Bsign (prec:=prec) (emax:=emax) x)
          (Binary.Bsign (prec:=prec) (emax:=emax) y)
          (Binary.B2R (prec:=prec) (emax:=emax) x -
           Binary.B2R (prec:=prec) (emax:=emax) y)
    else
      Binary.B2FF (prec:=prec) (emax:=emax)
          (Binary.Bminus (prec:=prec) (emax:=emax) minus_nan mode x y) =
          Binary.binary_overflow (prec:=prec) (emax:=emax) mode
            (Binary.Bsign (prec:=prec) (emax:=emax) x) ∧
        Binary.Bsign (prec:=prec) (emax:=emax) x =
          !Binary.Bsign (prec:=prec) (emax:=emax) y := by
  intro hx hy
  let plus_nan : Binary.BplusNaNHandler prec emax := fun _ _ => minus_nan x y
  have hyopp : Binary.is_finite (prec:=prec) (emax:=emax)
      (Binary.Bopp_preserve_nan y) = true := by
    simpa [Binary.is_finite_Bopp_preserve_nan] using hy
  have hplus := Bplus_correct (prec:=prec) (emax:=emax)
    plus_nan mode x (Binary.Bopp_preserve_nan y) hx hyopp
  have hop := Binary.Bminus_eq_Bplus_Bopp (prec:=prec) (emax:=emax)
    minus_nan mode x y
  dsimp [plus_nan] at hplus hop
  rw [← hop] at hplus
  simpa [Binary.B2R_Bopp_preserve_nan, Binary.Bsign_Bopp_preserve_nan,
    sub_eq_add_neg,
    binaryMinusResultSign] using hplus

-- Source ID: IEEE754/Binary.v:Bfma_correct:28261
-- Target: Bfma_correct
-- Coq: `Binary.v:Bfma_correct`, on the proof-carrying Binary carrier.
theorem Bfma_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (fma_nan : Binary.BfmaNaNHandler prec emax)
    (mode : RoundingMode) (x y z : binary_float prec emax) :
    Binary.is_finite (prec:=prec) (emax:=emax) x = true →
    Binary.is_finite (prec:=prec) (emax:=emax) y = true →
    Binary.is_finite (prec:=prec) (emax:=emax) z = true →
    let res := Binary.B2R (prec:=prec) (emax:=emax) x *
        Binary.B2R (prec:=prec) (emax:=emax) y +
        Binary.B2R (prec:=prec) (emax:=emax) z
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      Binary.B2R (prec:=prec) (emax:=emax)
          (Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z) =
        FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res ∧
      Binary.is_finite (prec:=prec) (emax:=emax)
          (Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z) = true ∧
      Binary.Bsign (prec:=prec) (emax:=emax)
          (Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z) =
        binaryFmaResultSign mode x y z res
    else
      Binary.B2FF (prec:=prec) (emax:=emax)
          (Binary.Bfma (prec:=prec) (emax:=emax) fma_nan mode x y z) =
        Binary.binary_overflow (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool res 0) := by
  intro hx hy hz
  cases x with
  | B754_zero sx =>
      cases y with
      | B754_zero sy =>
          cases z with
          | B754_zero sz =>
              apply Bfma_returned_zero_correct fma_nan mode
                (binary_float.B754_zero sx) (binary_float.B754_zero sy)
                (binary_float.B754_zero sz)
              · simp [Binary.B2R]
              · simp [Binary.B2R]
              · simp [Binary.Bfma]
          | B754_infinity sz => simp [Binary.is_finite] at hz
          | B754_nan sz payload hpayload => simp [Binary.is_finite] at hz
          | B754_finite sz mz ez Hz =>
              apply Bfma_returned_finite_correct fma_nan mode
                (binary_float.B754_zero sx) (binary_float.B754_zero sy)
                sz mz ez Hz
              · simp [Binary.B2R]
              · simp [Binary.Bfma]
      | B754_infinity sy => simp [Binary.is_finite] at hy
      | B754_nan sy payload hpayload => simp [Binary.is_finite] at hy
      | B754_finite sy my ey Hy =>
          cases z with
          | B754_zero sz =>
              apply Bfma_returned_zero_correct fma_nan mode
                (binary_float.B754_zero sx)
                (binary_float.B754_finite sy my ey Hy)
                (binary_float.B754_zero sz)
              · simp [Binary.B2R]
              · simp [Binary.B2R]
              · simp [Binary.Bfma]
          | B754_infinity sz => simp [Binary.is_finite] at hz
          | B754_nan sz payload hpayload => simp [Binary.is_finite] at hz
          | B754_finite sz mz ez Hz =>
              apply Bfma_returned_finite_correct fma_nan mode
                (binary_float.B754_zero sx)
                (binary_float.B754_finite sy my ey Hy) sz mz ez Hz
              · simp [Binary.B2R]
              · simp [Binary.Bfma]
  | B754_infinity sx => simp [Binary.is_finite] at hx
  | B754_nan sx payload hpayload => simp [Binary.is_finite] at hx
  | B754_finite sx mx ex Hx =>
      cases y with
      | B754_zero sy =>
          cases z with
          | B754_zero sz =>
              apply Bfma_returned_zero_correct fma_nan mode
                (binary_float.B754_finite sx mx ex Hx)
                (binary_float.B754_zero sy) (binary_float.B754_zero sz)
              · simp [Binary.B2R]
              · simp [Binary.B2R]
              · simp [Binary.Bfma]
          | B754_infinity sz => simp [Binary.is_finite] at hz
          | B754_nan sz payload hpayload => simp [Binary.is_finite] at hz
          | B754_finite sz mz ez Hz =>
              apply Bfma_returned_finite_correct fma_nan mode
                (binary_float.B754_finite sx mx ex Hx)
                (binary_float.B754_zero sy) sz mz ez Hz
              · simp [Binary.B2R]
              · simp [Binary.Bfma]
      | B754_infinity sy => simp [Binary.is_finite] at hy
      | B754_nan sy payload hpayload => simp [Binary.is_finite] at hy
      | B754_finite sy my ey Hy =>
          let X : FloatSpec.Core.Defs.FlocqFloat 2 :=
            FloatSpec.Core.Defs.FlocqFloat.mk
              (FloatSpec.Core.Zaux.cond_Zopp sx
                (FloatSpec.Core.Zaux.positiveToNat mx : Int)) ex
          let Y : FloatSpec.Core.Defs.FlocqFloat 2 :=
            FloatSpec.Core.Defs.FlocqFloat.mk
              (FloatSpec.Core.Zaux.cond_Zopp sy
                (FloatSpec.Core.Zaux.positiveToNat my : Int)) ey
          let product := FloatSpec.Calc.Operations.Fmult 2 X Y
          have hmulTrip := FloatSpec.Calc.Operations.F2R_mult (beta:=2) X Y
          have hmul : F2R product = F2R X * F2R Y := by
            simpa [wp, PostCond.noThrow, pure, product] using
              hmulTrip (by norm_num)
          have hproductEta :
              (FloatSpec.Core.Defs.FlocqFloat.mk product.Fnum product.Fexp :
                FloatSpec.Core.Defs.FlocqFloat 2) = product := by
            cases hproduct : product
            rfl
          have hproductInput : F2R
                (FloatSpec.Core.Defs.FlocqFloat.mk product.Fnum product.Fexp :
                  FloatSpec.Core.Defs.FlocqFloat 2) =
              Binary.B2R (prec:=prec) (emax:=emax)
                  (binary_float.B754_finite sx mx ex Hx) *
                Binary.B2R (prec:=prec) (emax:=emax)
                  (binary_float.B754_finite sy my ey Hy) := by
            rw [hproductEta, hmul]
            rfl
          cases z with
          | B754_zero sz =>
              apply Bfma_normalized_correct fma_nan mode
                (binary_float.B754_finite sx mx ex Hx)
                (binary_float.B754_finite sy my ey Hy)
                (binary_float.B754_zero sz) product.Fnum product.Fexp
              · simpa only [Binary.B2R, add_zero] using hproductInput
              · simp [Binary.Bfma, X, Y, product]
          | B754_infinity sz => simp [Binary.is_finite] at hz
          | B754_nan sz payload hpayload => simp [Binary.is_finite] at hz
          | B754_finite sz mz ez Hz =>
              let Z : FloatSpec.Core.Defs.FlocqFloat 2 :=
                FloatSpec.Core.Defs.FlocqFloat.mk
                  (FloatSpec.Core.Zaux.cond_Zopp sz
                    (FloatSpec.Core.Zaux.positiveToNat mz : Int)) ez
              let sum := FloatSpec.Calc.Operations.Fplus 2 product Z
              have haddTrip := FloatSpec.Calc.Operations.F2R_plus
                (beta:=2) product Z
              have hadd : F2R sum = F2R product + F2R Z := by
                simpa [wp, PostCond.noThrow, pure, sum] using
                  haddTrip (by norm_num)
              have hsumEta :
                  (FloatSpec.Core.Defs.FlocqFloat.mk sum.Fnum sum.Fexp :
                    FloatSpec.Core.Defs.FlocqFloat 2) = sum := by
                cases hsum : sum
                rfl
              have hsumInput : F2R
                    (FloatSpec.Core.Defs.FlocqFloat.mk sum.Fnum sum.Fexp :
                      FloatSpec.Core.Defs.FlocqFloat 2) =
                  Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite sx mx ex Hx) *
                    Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite sy my ey Hy) +
                    Binary.B2R (prec:=prec) (emax:=emax)
                      (binary_float.B754_finite sz mz ez Hz) := by
                rw [hsumEta, hadd, hmul]
                rfl
              apply Bfma_normalized_correct fma_nan mode
                (binary_float.B754_finite sx mx ex Hx)
                (binary_float.B754_finite sy my ey Hy)
                (binary_float.B754_finite sz mz ez Hz) sum.Fnum sum.Fexp
              · exact hsumInput
              · simp [Binary.Bfma, X, Y, Z, product, sum]

-- Source ID: IEEE754/Binary.v:Bsqrt_correct:30636
-- Target: Bsqrt_correct
-- Coq: `Binary.v:Bsqrt_correct`, on the proof-carrying Binary carrier.
theorem Bsqrt_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (sqrt_nan : Binary.BsqrtNaNHandler prec emax)
    (mode : RoundingMode) (x : binary_float prec emax) :
    Binary.B2R (prec:=prec) (emax:=emax)
        (Binary.Bsqrt (prec:=prec) (emax:=emax) sqrt_nan mode x) =
      FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
          (Real.sqrt (Binary.B2R (prec:=prec) (emax:=emax) x)) ∧
    Binary.is_finite (prec:=prec) (emax:=emax)
        (Binary.Bsqrt (prec:=prec) (emax:=emax) sqrt_nan mode x) =
      (match x with
      | binary_float.B754_zero _ => true
      | binary_float.B754_finite false _ _ _ => true
      | _ => false) ∧
    (Binary.is_nan (prec:=prec) (emax:=emax)
        (Binary.Bsqrt (prec:=prec) (emax:=emax) sqrt_nan mode x) = false →
      Binary.Bsign (prec:=prec) (emax:=emax)
          (Binary.Bsqrt (prec:=prec) (emax:=emax) sqrt_nan mode x) =
        Binary.Bsign (prec:=prec) (emax:=emax) x) := by
  cases x with
  | B754_zero sx =>
      cases mode <;>
        simp [Binary.Bsqrt, Binary.B2R, Binary.is_finite, Binary.is_nan,
          Binary.Bsign, Binary.roundR_zero_of_mode]
  | B754_infinity sx =>
      cases sx
      · cases mode <;>
          simp [Binary.Bsqrt, Binary.B2R, Binary.is_finite, Binary.is_nan,
            Binary.Bsign, Binary.roundR_zero_of_mode]
      · rcases hnan : sqrt_nan
            (binary_float.B754_infinity (prec:=prec) (emax:=emax) true) with
          ⟨nan, hnanProp⟩
        cases nan <;>
          simp [Binary.Bsqrt, hnan, Binary.B2R, Binary.is_finite,
            Binary.is_nan, Binary.Bsign, Binary.roundR_zero_of_mode] at hnanProp ⊢
  | B754_nan sx payload hPayload =>
      rcases hnan : sqrt_nan
          (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hPayload) with
        ⟨nan, hnanProp⟩
      cases nan <;>
        simp [Binary.Bsqrt, hnan, Binary.B2R, Binary.is_finite,
          Binary.is_nan, Binary.Bsign, Binary.roundR_zero_of_mode] at hnanProp ⊢
  | B754_finite sx mx ex Hx =>
      cases sx
      · let mxn := FloatSpec.Core.Zaux.positiveToNat mx
        let input := F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk (mxn : Int) ex :
            FloatSpec.Core.Defs.FlocqFloat 2)
        let result := SFsqrt_core_binary prec emax (mxn : Int) ex
        have hdata := SFsqrt_core_binary_correct_data
          (prec:=prec) (emax:=emax) (mxn : Int) ex
          (by exact_mod_cast positiveToNat_pos_bsn mx)
        have hresult_pos : 0 < result.1 := by
          simpa [result] using hdata.1
        let mzn := result.1.toNat
        have hmzn_pos : 0 < mzn := by omega
        have hmzn_cast : (mzn : Int) = result.1 :=
          Int.toNat_of_nonneg (le_of_lt hresult_pos)
        let z := binary_round_aux (prec:=prec) (emax:=emax) mode false
          (mzn : Int) result.2.1 result.2.2
        have hbetween :
            FloatSpec.Calc.Bracket.inbetween_float 2 (mzn : Int) result.2.1
              |Real.sqrt input| result.2.2 := by
          simpa [input, result, hmzn_cast,
            abs_of_nonneg (Real.sqrt_nonneg _)] using hdata.2.1
        have hexp :
            result.2.1 ≤ FLT_exp (3 - emax - prec) prec
              (FloatSpec.Core.Digits.Zdigits 2 (mzn : Int) + result.2.1) := by
          simpa [result, hmzn_cast] using hdata.2.2
        have haux := binary_round_aux_correct (prec:=prec) (emax:=emax)
          mode (Real.sqrt input) mzn result.2.1 result.2.2
          hmzn_pos hbetween hexp
        have hsqrt_sign :
            FloatSpec.Core.Raux.Rlt_bool (Real.sqrt input) 0 = false := by
          simp [FloatSpec.Core.Raux.Rlt_bool, Real.sqrt_nonneg]
        have hvalid :
            validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true := by
          simpa [z, hsqrt_sign] using haux.1
        have hnotnan : is_nan_SF z = false := by
          have hmzn_nonneg : (0 : Int) ≤ (mzn : Int) := by
            exact_mod_cast Nat.zero_le mzn
          simpa [z] using
            is_nan_binary_round_aux_of_nonneg (prec:=prec) (emax:=emax)
              mode false (mzn : Int) result.2.1 result.2.2 hmzn_nonneg
        have hlt := roundRSqrtBinaryFiniteLtEmax
          (prec:=prec) (emax:=emax) mode mx ex Hx
        have hltInput : FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                (Real.sqrt input)|
            (FloatSpec.Core.Raux.bpow 2 emax) = true := by
          simp [FloatSpec.Core.Raux.Rlt_bool]
          simpa [input, mxn, Binary.B2R] using hlt
        have hbranch : SF2R 2 z =
              FloatSpec.Core.Generic_fmt.roundR 2
                (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                  (Real.sqrt input) ∧
            is_finite_SF z = true ∧ sign_SF z = false := by
          have h := haux.2
          simpa [z, hsqrt_sign, hltInput] using h
        have hresult : Binary.Bsqrt (prec:=prec) (emax:=emax) sqrt_nan mode
              (binary_float.B754_finite (prec:=prec) (emax:=emax)
                false mx ex Hx) =
            Binary.standardFloatToBinaryFloatOfNotNaN
              (prec:=prec) (emax:=emax) z hvalid hnotnan := by
          simp [Binary.Bsqrt, mxn, input, result, mzn, z]
        have hB2R := Binary.B2R_standardFloatToBinaryFloatOfNotNaN
          (prec:=prec) (emax:=emax) z hvalid hnotnan
        have hfinite := Binary.is_finite_standardFloatToBinaryFloatOfNotNaN
          (prec:=prec) (emax:=emax) z hvalid hnotnan
        have hsign := Binary.Bsign_standardFloatToBinaryFloatOfNotNaN
          (prec:=prec) (emax:=emax) z hvalid hnotnan
        rw [hresult]
        refine ⟨?_, ?_, ?_⟩
        · calc
            Binary.B2R (prec:=prec) (emax:=emax)
                (Binary.standardFloatToBinaryFloatOfNotNaN
                  (prec:=prec) (emax:=emax) z hvalid hnotnan) = SF2R 2 z := hB2R
            _ = _ := by simpa [input, mxn, Binary.B2R] using hbranch.1
        · exact hfinite.trans hbranch.2.1
        · intro _
          calc
            Binary.Bsign (prec:=prec) (emax:=emax)
                (Binary.standardFloatToBinaryFloatOfNotNaN
                  (prec:=prec) (emax:=emax) z hvalid hnotnan) = sign_SF z := hsign
            _ = false := hbranch.2.2
            _ = Binary.Bsign (prec:=prec) (emax:=emax)
                (binary_float.B754_finite (prec:=prec) (emax:=emax)
                  false mx ex Hx) := rfl
      · have hneg : Binary.B2R (prec:=prec) (emax:=emax)
            (binary_float.B754_finite (prec:=prec) (emax:=emax)
              true mx ex Hx) < 0 := by
          have hmNat := positiveToNat_pos_bsn mx
          have hmInt : (0 : Int) <
              (FloatSpec.Core.Zaux.positiveToNat mx : Int) := by
            exact_mod_cast hmNat
          change F2R (FloatSpec.Core.Defs.FlocqFloat.mk
            (-(FloatSpec.Core.Zaux.positiveToNat mx : Int)) ex :
              FloatSpec.Core.Defs.FlocqFloat 2) < 0
          exact FloatSpec.Core.Float_prop.F2R_lt_0
            (beta:=2)
            (f:=FloatSpec.Core.Defs.FlocqFloat.mk
              (-(FloatSpec.Core.Zaux.positiveToNat mx : Int)) ex)
            (by norm_num) (by
              change -(FloatSpec.Core.Zaux.positiveToNat mx : Int) < 0
              omega)
        have hsqrt0 : Real.sqrt (Binary.B2R (prec:=prec) (emax:=emax)
            (binary_float.B754_finite (prec:=prec) (emax:=emax)
              true mx ex Hx)) = 0 :=
          Real.sqrt_eq_zero_of_nonpos (le_of_lt hneg)
        have hround0 : FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
              (Real.sqrt (Binary.B2R (prec:=prec) (emax:=emax)
                (binary_float.B754_finite (prec:=prec) (emax:=emax)
                  true mx ex Hx))) = 0 := by
          rw [hsqrt0]
          exact Binary.roundR_zero_of_mode mode
        have hround0' : FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
              (Real.sqrt (F2R (FloatSpec.Core.Defs.FlocqFloat.mk
                (-(FloatSpec.Core.Zaux.positiveToNat mx : Int)) ex :
                  FloatSpec.Core.Defs.FlocqFloat 2))) = 0 := by
          simpa [Binary.B2R, FloatSpec.Core.Zaux.cond_Zopp] using hround0
        rcases hnan : sqrt_nan
            (binary_float.B754_finite (prec:=prec) (emax:=emax)
              true mx ex Hx) with ⟨nan, hnanProp⟩
        cases nan <;>
          simp [Binary.Bsqrt, hnan, hsqrt0, hround0, hround0', Binary.B2R, Binary.is_finite,
            Binary.is_nan, Binary.Bsign, Binary.roundR_zero_of_mode] at hnanProp ⊢ <;>
          simpa [F2R, FloatSpec.Core.Defs.F2R] using hround0'.symm

-- Source ID: IEEE754/Binary.v:Bdiv_correct:29372
-- Target: Bdiv_correct
-- Coq: `Binary.v:Bdiv_correct`, on the proof-carrying Binary carrier.
theorem Bdiv_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (div_nan : Binary.BdivNaNHandler prec emax)
    (mode : RoundingMode) (x y : binary_float prec emax) :
    Binary.B2R (prec:=prec) (emax:=emax) y ≠ 0 →
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Binary.B2R (prec:=prec) (emax:=emax) x /
             Binary.B2R (prec:=prec) (emax:=emax) y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      Binary.B2R (prec:=prec) (emax:=emax)
          (Binary.Bdiv (prec:=prec) (emax:=emax) div_nan mode x y) =
        FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Binary.B2R (prec:=prec) (emax:=emax) x /
             Binary.B2R (prec:=prec) (emax:=emax) y) ∧
      Binary.is_finite (prec:=prec) (emax:=emax)
          (Binary.Bdiv (prec:=prec) (emax:=emax) div_nan mode x y) =
        Binary.is_finite (prec:=prec) (emax:=emax) x ∧
      (Binary.is_nan (prec:=prec) (emax:=emax)
          (Binary.Bdiv (prec:=prec) (emax:=emax) div_nan mode x y) = false →
        Binary.Bsign (prec:=prec) (emax:=emax)
            (Binary.Bdiv (prec:=prec) (emax:=emax) div_nan mode x y) =
          Bool.xor (Binary.Bsign (prec:=prec) (emax:=emax) x)
            (Binary.Bsign (prec:=prec) (emax:=emax) y))
    else
      Binary.B2FF (prec:=prec) (emax:=emax)
          (Binary.Bdiv (prec:=prec) (emax:=emax) div_nan mode x y) =
        Binary.binary_overflow (prec:=prec) (emax:=emax) mode
          (Bool.xor (Binary.Bsign (prec:=prec) (emax:=emax) x)
            (Binary.Bsign (prec:=prec) (emax:=emax) y)) := by
  intro hy
  cases y with
  | B754_zero sy => simp [Binary.B2R] at hy
  | B754_infinity sy => simp [Binary.B2R] at hy
  | B754_nan sy payload hPayload => simp [Binary.B2R] at hy
  | B754_finite sy my ey Hy =>
      cases x with
      | B754_zero sx =>
          cases mode <;>
            simp [Binary.Bdiv, Binary.B2R, Binary.roundR_zero_of_mode,
              Binary.Rlt_bool_zero_bpow, Binary.is_finite, Binary.is_nan,
              Binary.Bsign]
      | B754_infinity sx =>
          cases mode <;>
            simp [Binary.Bdiv, Binary.B2R, Binary.roundR_zero_of_mode,
              Binary.Rlt_bool_zero_bpow, Binary.is_finite, Binary.is_nan,
              Binary.Bsign]
      | B754_nan sx payload hPayload =>
          rw [show Binary.B2R (prec:=prec) (emax:=emax)
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hPayload) /
                Binary.B2R (prec:=prec) (emax:=emax)
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy) = 0 by
            simp [Binary.B2R]]
          rw [Binary.roundR_zero_of_mode, abs_zero, Binary.Rlt_bool_zero_bpow]
          rcases hnan : div_nan
              (binary_float.B754_nan (prec:=prec) (emax:=emax) sx payload hPayload)
              (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy) with
            ⟨nan, hnanProp⟩
          cases nan <;>
            simp [Binary.Bdiv, hnan, Binary.B2R, Binary.is_finite, Binary.is_nan,
              Binary.Bsign] at hnanProp ⊢
      | B754_finite sx mx ex Hx =>
          let mxn := FloatSpec.Core.Zaux.positiveToNat mx
          let myn := FloatSpec.Core.Zaux.positiveToNat my
          let result := SFdiv_core_binary prec emax (mxn : Int) ex (myn : Int) ey
          let z := binary_round_aux (prec:=prec) (emax:=emax) mode
            (Bool.xor sx sy) result.1 result.2.1 result.2.2
          have haux := Bdiv_correct_aux (prec:=prec) (emax:=emax)
            mode sx mx ex sy my ey
          have hnotnan : is_nan_SF z = false := by
            by_cases hlt :
                FloatSpec.Core.Raux.Rlt_bool
                  |FloatSpec.Core.Generic_fmt.roundR 2
                    (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                      ((SF2R 2 (StandardFloat.S754_finite sx mxn ex)) /
                       (SF2R 2 (StandardFloat.S754_finite sy myn ey)))|
                  (FloatSpec.Core.Raux.bpow 2 emax) = true
            · have hfinite : is_finite_SF z = true := by
                have hbranch := haux.2
                simp [mxn, myn, result, z, hlt] at hbranch
                exact hbranch.2.1
              cases hz : z <;> simp [hz, is_nan_SF, is_finite_SF] at hfinite ⊢
            · have hover : z =
                  bsn_binary_overflow (prec:=prec) (emax:=emax) mode
                    (Bool.xor sx sy) := by
                have hltFalse := Bool.eq_false_of_not_eq_true hlt
                have hbranch := haux.2
                simpa [mxn, myn, result, z, hltFalse] using hbranch
              rw [hover]
              exact is_nan_binary_overflow (prec:=prec) (emax:=emax) mode
                (Bool.xor sx sy)
          have hresult :
              Binary.Bdiv (prec:=prec) (emax:=emax) div_nan mode
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy) =
                Binary.standardFloatToBinaryFloatOfNotNaN
                  (prec:=prec) (emax:=emax) z haux.1 hnotnan := by
            simp [Binary.Bdiv, mxn, myn, result, z]
          have hB2R : Binary.B2R (prec:=prec) (emax:=emax)
                (Binary.Bdiv (prec:=prec) (emax:=emax) div_nan mode
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)) =
              SF2R 2 z := by
            rw [hresult]
            exact Binary.B2R_standardFloatToBinaryFloatOfNotNaN z haux.1 hnotnan
          have hfinite : Binary.is_finite (prec:=prec) (emax:=emax)
                (Binary.Bdiv (prec:=prec) (emax:=emax) div_nan mode
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)) =
              is_finite_SF z := by
            rw [hresult]
            exact Binary.is_finite_standardFloatToBinaryFloatOfNotNaN z haux.1 hnotnan
          have hsign : Binary.Bsign (prec:=prec) (emax:=emax)
                (Binary.Bdiv (prec:=prec) (emax:=emax) div_nan mode
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)) =
              sign_SF z := by
            rw [hresult]
            exact Binary.Bsign_standardFloatToBinaryFloatOfNotNaN z haux.1 hnotnan
          have hB2FF : Binary.B2FF (prec:=prec) (emax:=emax)
                (Binary.Bdiv (prec:=prec) (emax:=emax) div_nan mode
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                  (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)) =
              SF2FF z := by
            rw [hresult]
            exact Binary.B2FF_standardFloatToBinaryFloatOfNotNaN z haux.1 hnotnan
          have hquot :
              Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_finite sx mx ex Hx) /
                  Binary.B2R (prec:=prec) (emax:=emax)
                    (binary_float.B754_finite sy my ey Hy) =
                SF2R 2 (StandardFloat.S754_finite sx mxn ex) /
                  SF2R 2 (StandardFloat.S754_finite sy myn ey) := by
            simp [Binary.B2R, SF2R, mxn, myn,
              FloatSpec.Core.Zaux.cond_Zopp]
          by_cases hlt :
              FloatSpec.Core.Raux.Rlt_bool
                |FloatSpec.Core.Generic_fmt.roundR 2
                  (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                    (Binary.B2R (prec:=prec) (emax:=emax)
                        (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx) /
                     Binary.B2R (prec:=prec) (emax:=emax)
                        (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy))|
                (FloatSpec.Core.Raux.bpow 2 emax) = true
          · rw [ite_eq_left hlt]
            have hbranch := haux.2
            have hltAux :
                FloatSpec.Core.Raux.Rlt_bool
                  |FloatSpec.Core.Generic_fmt.roundR 2
                    (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                      ((SF2R 2 (StandardFloat.S754_finite sx mxn ex)) /
                       (SF2R 2 (StandardFloat.S754_finite sy myn ey)))|
                  (FloatSpec.Core.Raux.bpow 2 emax) = true := by
              simpa only [hquot] using hlt
            simp [mxn, myn, hltAux] at hbranch
            constructor
            · exact hB2R.trans (by simpa only [hquot] using hbranch.1)
            · constructor
              · exact hfinite.trans hbranch.2.1
              · intro _
                exact hsign.trans hbranch.2.2
          · rw [ite_eq_right hlt]
            have hltFalse :
                FloatSpec.Core.Raux.Rlt_bool
                  |FloatSpec.Core.Generic_fmt.roundR 2
                    (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                      ((SF2R 2 (StandardFloat.S754_finite sx mxn ex)) /
                       (SF2R 2 (StandardFloat.S754_finite sy myn ey)))|
                  (FloatSpec.Core.Raux.bpow 2 emax) = false := by
              have := Bool.eq_false_of_not_eq_true hlt
              simpa only [hquot] using this
            have hover : z = bsn_binary_overflow
                (prec:=prec) (emax:=emax) mode (Bool.xor sx sy) := by
              have hbranch := haux.2
              simpa [z, mxn, myn, hltFalse] using hbranch
            calc
              Binary.B2FF (prec:=prec) (emax:=emax)
                  (Binary.Bdiv (prec:=prec) (emax:=emax) div_nan mode
                    (binary_float.B754_finite (prec:=prec) (emax:=emax) sx mx ex Hx)
                    (binary_float.B754_finite (prec:=prec) (emax:=emax) sy my ey Hy)) =
                SF2FF z := hB2FF
              _ = SF2FF (bsn_binary_overflow (prec:=prec) (emax:=emax) mode
                    (Bool.xor sx sy)) := by rw [hover]
              _ = Binary.binary_overflow (prec:=prec) (emax:=emax) mode
                    (Bool.xor sx sy) := rfl

-- Coq: sign_plus_overflow
theorem sign_plus_overflow_from_range_bounded {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int)
    (sy : Bool) (my : Nat) (ey : Int)
    (Hx : bounded (prec:=prec) (emax:=emax) mx ex = true)
    (Hy : bounded (prec:=prec) (emax:=emax) my ey = true) :
    let z :=
      (SF2R 2 (StandardFloat.S754_finite sx mx ex) +
        SF2R 2 (StandardFloat.S754_finite sy my ey))
    FloatSpec.Core.Raux.bpow 2 emax ≤
      |FloatSpec.Core.Generic_fmt.round_to_generic 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) z| →
    sx = FloatSpec.Core.Raux.Rlt_bool z 0 ∧ sx = sy := by
  intro z Hover
  exact ExperimentalSingleNaNArithmetic.sign_plus_overflow
    (prec:=prec) (emax:=emax) mode sx mx ex sy my ey Hx Hy Hover

-- Coq: sign_plus_overflow
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
    sx = FloatSpec.Core.Raux.Rlt_bool z 0 ∧ sx = sy := by
  intro z Hover
  let mxn := FloatSpec.Core.Zaux.positiveToNat mx
  let myn := FloatSpec.Core.Zaux.positiveToNat my
  have hmx : 0 < mxn := FloatSpec.Core.Zaux.positiveToNat_pos mx
  have hmy : 0 < myn := FloatSpec.Core.Zaux.positiveToNat_pos my
  have hxFmt : FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec)
      (SF2R 2 (StandardFloat.S754_finite sx mxn ex)) := by
    have h := _root_.generic_format_B2R (prec:=prec) (emax:=emax)
      (BinarySingleNaNFloat.B754_finite sx mxn ex hmx (by simpa [mxn] using Hx))
    simpa [binarySingleNaNFloatToB754, B754_to_R, SF2R] using h
  have hyFmt : FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec)
      (SF2R 2 (StandardFloat.S754_finite sy myn ey)) := by
    have h := _root_.generic_format_B2R (prec:=prec) (emax:=emax)
      (BinarySingleNaNFloat.B754_finite sy myn ey hmy (by simpa [myn] using Hy))
    simpa [binarySingleNaNFloatToB754, B754_to_R, SF2R] using h
  have hxRange := range_bounded_of_specFloat_bounded
    (prec:=prec) (emax:=emax) mxn ex hmx (by simpa [mxn] using Hx)
  have hyRange := range_bounded_of_specFloat_bounded
    (prec:=prec) (emax:=emax) myn ey hmy (by simpa [myn] using Hy)
  have hxLt : F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mxn : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2) < FloatSpec.Core.Raux.bpow 2 emax := by
    have h := _root_.bounded_lt_emax (prec:=prec) (emax:=emax) mxn ex hxRange
    simpa [wp, PostCond.noThrow, pure] using h trivial
  have hyLt : F2R (FloatSpec.Core.Defs.FlocqFloat.mk (myn : Int) ey :
        FloatSpec.Core.Defs.FlocqFloat 2) < FloatSpec.Core.Raux.bpow 2 emax := by
    have h := _root_.bounded_lt_emax (prec:=prec) (emax:=emax) myn ey hyRange
    simpa [wp, PostCond.noThrow, pure] using h trivial
  by_cases hs : sx = sy
  · constructor
    · subst sy
      cases sx
      · have hz : 0 ≤ z := by
          dsimp [z, mxn, myn, SF2R, F2R, FloatSpec.Core.Defs.F2R]
          positivity
        simp [FloatSpec.Core.Raux.Rlt_bool, hz]
      · have hz : z < 0 := by
          dsimp [z, mxn, myn, SF2R, F2R, FloatSpec.Core.Defs.F2R]
          have hxpos : 0 < (((mxn : Int) : Real) * (2 : Real) ^ ex) := by
            positivity
          have hypos : 0 < (((myn : Int) : Real) * (2 : Real) ^ ey) := by
            positivity
          norm_num only [Int.cast_neg]
          linarith
        simp [FloatSpec.Core.Raux.Rlt_bool, hz]
    · exact hs
  · exfalso
    apply (not_lt_of_ge Hover)
    rw [FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR, abs_lt]
    cases sx <;> cases sy
    · exact (hs rfl).elim
    · have hyLower : -FloatSpec.Core.Raux.bpow 2 emax <
          SF2R 2 (StandardFloat.S754_finite true myn ey) := by
        simpa [SF2R, F2R, FloatSpec.Core.Defs.F2R] using neg_lt_neg hyLt
      have hyLe : SF2R 2 (StandardFloat.S754_finite true myn ey) ≤ z := by
        rw [show z = SF2R 2 (StandardFloat.S754_finite false mxn ex) +
            SF2R 2 (StandardFloat.S754_finite true myn ey) by rfl]
        have h : 0 ≤ SF2R 2 (StandardFloat.S754_finite false mxn ex) := by
          dsimp [SF2R, F2R, FloatSpec.Core.Defs.F2R]
          positivity
        linarith
      have hzLe : z ≤ SF2R 2 (StandardFloat.S754_finite false mxn ex) := by
        rw [show z = SF2R 2 (StandardFloat.S754_finite false mxn ex) +
            SF2R 2 (StandardFloat.S754_finite true myn ey) by rfl]
        have h : SF2R 2 (StandardFloat.S754_finite true myn ey) ≤ 0 := by
          have hp : 0 ≤ (((myn : Int) : Real) * (2 : Real) ^ ey) := by positivity
          dsimp [SF2R, F2R, FloatSpec.Core.Defs.F2R]
          norm_num only [Int.cast_neg]
          linarith
        linarith
      have hLower := FloatSpec.Core.Generic_fmt.roundR_ge_generic
        (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
        (rnd:=rnd_of_mode mode)
        (x:=SF2R 2 (StandardFloat.S754_finite true myn ey)) (y:=z)
        (hβ:=by norm_num) hyFmt hyLe
      have hUpper := FloatSpec.Core.Generic_fmt.roundR_le_generic
        (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
        (rnd:=rnd_of_mode mode) (x:=z)
        (y:=SF2R 2 (StandardFloat.S754_finite false mxn ex))
        (hβ:=by norm_num) hxFmt hzLe
      exact ⟨lt_of_lt_of_le hyLower hLower,
        lt_of_le_of_lt hUpper (by simpa [SF2R] using hxLt)⟩
    · have hxLower : -FloatSpec.Core.Raux.bpow 2 emax <
          SF2R 2 (StandardFloat.S754_finite true mxn ex) := by
        simpa [SF2R, F2R, FloatSpec.Core.Defs.F2R] using neg_lt_neg hxLt
      have hxLe : SF2R 2 (StandardFloat.S754_finite true mxn ex) ≤ z := by
        rw [show z = SF2R 2 (StandardFloat.S754_finite true mxn ex) +
            SF2R 2 (StandardFloat.S754_finite false myn ey) by rfl]
        have h : 0 ≤ SF2R 2 (StandardFloat.S754_finite false myn ey) := by
          dsimp [SF2R, F2R, FloatSpec.Core.Defs.F2R]
          positivity
        linarith
      have hzLe : z ≤ SF2R 2 (StandardFloat.S754_finite false myn ey) := by
        rw [show z = SF2R 2 (StandardFloat.S754_finite true mxn ex) +
            SF2R 2 (StandardFloat.S754_finite false myn ey) by rfl]
        have h : SF2R 2 (StandardFloat.S754_finite true mxn ex) ≤ 0 := by
          have hp : 0 ≤ (((mxn : Int) : Real) * (2 : Real) ^ ex) := by positivity
          dsimp [SF2R, F2R, FloatSpec.Core.Defs.F2R]
          norm_num only [Int.cast_neg]
          linarith
        linarith
      have hLower := FloatSpec.Core.Generic_fmt.roundR_ge_generic
        (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
        (rnd:=rnd_of_mode mode)
        (x:=SF2R 2 (StandardFloat.S754_finite true mxn ex)) (y:=z)
        (hβ:=by norm_num) hxFmt hxLe
      have hUpper := FloatSpec.Core.Generic_fmt.roundR_le_generic
        (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
        (rnd:=rnd_of_mode mode) (x:=z)
        (y:=SF2R 2 (StandardFloat.S754_finite false myn ey))
        (hβ:=by norm_num) hyFmt hzLe
      exact ⟨lt_of_lt_of_le hxLower hLower,
        lt_of_le_of_lt hUpper (by simpa [SF2R] using hyLt)⟩
    · exact (hs rfl).elim

namespace ExperimentalSingleNaNArithmetic

private theorem Bplus_finite_nonnegative_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mx my : Nat) (ex ey : Int) (hmx : 0 < mx) (hmy : 0 < my)
    (hsumNonneg :
      0 ≤ B754_to_R (B754.B754_finite false mx ex) +
        B754_to_R (B754.B754_finite true my ey))
    (hlt : FloatSpec.Core.Raux.Rlt_bool
      |FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RNE)
        (B754_to_R (B754.B754_finite false mx ex) +
          B754_to_R (B754.B754_finite true my ey))|
      (FloatSpec.Core.Raux.bpow 2 emax) = true) :
    let r := Bplus (prec:=prec) (emax:=emax) RoundingMode.RNE
      (B754.B754_finite false mx ex) (B754.B754_finite true my ey)
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
        (B2SF_BSN r) = true ∧
      B754_to_R r = FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RNE)
        (B754_to_R (B754.B754_finite false mx ex) +
          B754_to_R (B754.B754_finite true my ey)) ∧
      BSN_is_finite r = true ∧ BSN_sign r = false := by
  let ez := min ex ey
  let m := Fplus_naive false mx ex true my ey ez
  let r := Bplus (prec:=prec) (emax:=emax) RoundingMode.RNE
    (B754.B754_finite false mx ex) (B754.B754_finite true my ey)
  change validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
      (B2SF_BSN r) = true ∧
    B754_to_R r = FloatSpec.Core.Generic_fmt.roundR 2
      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RNE)
      (B754_to_R (B754.B754_finite false mx ex) +
        B754_to_R (B754.B754_finite true my ey)) ∧
    BSN_is_finite r = true ∧ BSN_sign r = false
  have hsumRaw := Fplus_naive_correct false mx ex true my ey ez
    (min_le_left ex ey) (min_le_right ex ey)
  have hsum :
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk m ez :
        FloatSpec.Core.Defs.FlocqFloat 2) =
        B754_to_R (B754.B754_finite false mx ex) +
          B754_to_R (B754.B754_finite true my ey) := by
    simpa [m, ez, B754_to_R, FloatSpec.Core.Zaux.cond_Zopp] using hsumRaw
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ ez := zpow_pos (by norm_num) ez
  have hmNonneg : 0 ≤ m := by
    have hFNonneg :
        0 ≤ F2R (FloatSpec.Core.Defs.FlocqFloat.mk m ez :
          FloatSpec.Core.Defs.FlocqFloat 2) := by
      rw [hsum]
      exact hsumNonneg
    have hmRealNonneg : 0 ≤ (m : ℝ) := by
      rw [← mul_nonneg_iff_of_pos_right hpowPos]
      simpa [F2R, FloatSpec.Core.Defs.F2R] using hFNonneg
    exact_mod_cast hmRealNonneg
  by_cases hm0 : m = 0
  · have hsumZero :
        B754_to_R (B754.B754_finite false mx ex) +
            B754_to_R (B754.B754_finite true my ey) = 0 := by
      rw [← hsum]
      simp [hm0, F2R, FloatSpec.Core.Defs.F2R]
    have hroundZero :
        FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RNE)
          (B754_to_R (B754.B754_finite false mx ex) +
            B754_to_R (B754.B754_finite true my ey)) = 0 := by
      rw [hsumZero]
      exact Binary.roundR_zero_of_mode (prec:=prec) (emax:=emax) RoundingMode.RNE
    have hr : r = B754.B754_zero false := by
      simp [r, Bplus, binary_normalize, m, ez, hm0]
    rw [hr, hroundZero]
    simp [validBinarySingleNaNStandardFloat, B2SF_BSN, B754_to_R,
      BSN_is_finite, BSN_sign]
  · have hmpos : 0 < m := lt_of_le_of_ne hmNonneg (Ne.symm hm0)
    let z := binary_round (prec:=prec) (emax:=emax)
      RoundingMode.RNE false m.toNat ez
    have hmcast : (m.toNat : Int) = m := Int.toNat_of_nonneg hmNonneg
    have hmnatPos : 0 < m.toNat := by omega
    have hround := binary_round_correct (prec:=prec) (emax:=emax)
      RoundingMode.RNE false m.toNat ez hmnatPos
    have hinput :
        SF2R 2 (StandardFloat.S754_finite false m.toNat ez) =
          B754_to_R (B754.B754_finite false mx ex) +
            B754_to_R (B754.B754_finite true my ey) := by
      simpa [SF2R, F2R, FloatSpec.Core.Defs.F2R, hmcast] using hsum
    have hltAux :
        FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RNE)
            (SF2R 2 (StandardFloat.S754_finite false m.toNat ez))|
          (FloatSpec.Core.Raux.bpow 2 emax) = true := by
      simpa [hinput] using hlt
    have hbranch := hround.2
    dsimp at hbranch
    rw [hltAux] at hbranch
    simp at hbranch
    have hr : r = SF2B z := by
      simp [r, Bplus, binary_normalize, m, ez, hm0, hmpos, z]
    rw [hr]
    have hviewTrip := B2SF_SF2B z
    have hview : B2SF_BSN (SF2B z) = z := by
      simpa [B2SF_SF2B_check, wp, PostCond.noThrow, pure] using hviewTrip trivial
    have hfiniteTrip := is_finite_SF2B (prec:=prec) (emax:=emax) z (by rfl)
    have hfinite : BSN_is_finite (SF2B z) = is_finite_SF z := by
      simpa [is_finite_SF2B_check, wp, PostCond.noThrow, pure] using
        hfiniteTrip trivial
    have hsignTrip := Bsign_SF2B (prec:=prec) (emax:=emax) z (by rfl)
    have hsign : BSN_sign (SF2B z) = sign_SF z := by
      simpa [Bsign_SF2B_check, wp, PostCond.noThrow, pure] using hsignTrip trivial
    constructor
    · rw [hview]
      exact hround.1
    · constructor
      · have hB2R := B2R_SF2B z
        calc
          B754_to_R (SF2B z) = SF2R 2 z := by
            simpa [B2R_SF2B_check, wp, PostCond.noThrow, pure] using hB2R trivial
          _ = FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RNE)
              (B754_to_R (B754.B754_finite false mx ex) +
                B754_to_R (B754.B754_finite true my ey)) := by
            simpa [z, hinput] using hbranch.1
      · constructor
        · exact hfinite.trans hbranch.2.1
        · exact hsign.trans hbranch.2.2

private theorem roundR_RTZ_eq_floor_of_nonneg {prec emax : Int}
    (x : ℝ) (hx : 0 ≤ x) :
    FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RTZ) x =
      FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) FloatSpec.Core.Generic_fmt.rnd_floor x := by
  let sm := FloatSpec.Core.Generic_fmt.scaled_mantissa 2
    (FLT_exp (3 - emax - prec) prec) x
  have hpow : 0 ≤ (2 : ℝ) ^
      (-(FloatSpec.Core.Generic_fmt.cexp 2
        (FLT_exp (3 - emax - prec) prec) x)) :=
    le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
  have hsm : 0 ≤ sm := by
    simpa [sm, FloatSpec.Core.Generic_fmt.scaled_mantissa] using mul_nonneg hx hpow
  have hrnd : rnd_of_mode RoundingMode.RTZ sm =
      FloatSpec.Core.Generic_fmt.rnd_floor sm := by
    simpa [rnd_of_mode, FloatSpec.Core.Generic_fmt.rnd_floor] using
      (FloatSpec.Core.Raux.Ztrunc_floor sm hsm True.intro)
  simp only [FloatSpec.Core.Generic_fmt.roundR]
  rw [hrnd]

private theorem roundR_floor_minus_eps_pos {prec emax : Int}
    [FloatSpec.Core.Generic_fmt.Valid_exp (FLT_exp (3 - emax - prec) prec)]
    (x eps : ℝ) (hx : 0 < x)
    (hformat : FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec) x)
    (heps : 0 < eps ∧ eps ≤ FloatSpec.Core.Ulp.ulp 2
      (FLT_exp (3 - emax - prec) prec)
      (FloatSpec.Core.Ulp.pred 2 (FLT_exp (3 - emax - prec) prec) x)) :
    FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
        FloatSpec.Core.Generic_fmt.rnd_floor (x - eps) =
      FloatSpec.Core.Ulp.pred 2 (FLT_exp (3 - emax - prec) prec) x := by
  have hchosenTrip := FloatSpec.Core.Ulp.round_DN_minus_eps_pos
    (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
    (x:=x) hx hformat eps heps (by norm_num : (1 : Int) < 2)
  have hchosen :
      FloatSpec.Core.Generic_fmt.round_DN_to_format 2
          (FLT_exp (3 - emax - prec) prec) (x - eps) (by norm_num) =
        FloatSpec.Core.Ulp.pred 2 (FLT_exp (3 - emax - prec) prec) x := by
    simpa [wp, PostCond.noThrow, pure] using hchosenTrip trivial
  have hround := FloatSpec.Core.Generic_fmt.roundR_DN_pt
    (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
    (x:=x - eps) (by norm_num : (1 : Int) < 2)
  have hchosenSpec := Classical.choose_spec
    (FloatSpec.Core.Generic_fmt.round_DN_exists
      (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
      (x:=x - eps) (hβ:=by norm_num))
  have heq :
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
          FloatSpec.Core.Generic_fmt.rnd_floor (x - eps) =
        FloatSpec.Core.Generic_fmt.round_DN_to_format 2
          (FLT_exp (3 - emax - prec) prec) (x - eps) (by norm_num) := by
    apply le_antisymm
    · exact hchosenSpec.2.2.2 _ hround.1 hround.2.1
    · exact hround.2.2 _ hchosenSpec.1 hchosenSpec.2.2.1
  exact heq.trans hchosen

private theorem Zrnd_opp_RTZ :
    FloatSpec.Core.Generic_fmt.Zrnd_opp (rnd_of_mode RoundingMode.RTZ) =
      rnd_of_mode RoundingMode.RTZ := by
  funext x
  simp [FloatSpec.Core.Generic_fmt.Zrnd_opp, rnd_of_mode,
    FloatSpec.Core.Generic_fmt.Ztrunc_neg]

private theorem Bpred_positive_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mx : Nat) (ex : Int) (hmx : 0 < mx)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true) :
    let x := B754.B754_finite false mx ex
    let r := Bpred (prec:=prec) (emax:=emax) x
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) (B2SF_BSN r) = true ∧
      B754_to_R r = FloatSpec.Core.Ulp.pred_pos 2
        (FLT_exp (3 - emax - prec) prec) (B754_to_R x) ∧
      BSN_is_finite r = true ∧ BSN_sign r = false := by
  let x := B754.B754_finite false mx ex
  let xr := B754_to_R x
  let eps : ℝ := (2 : ℝ) ^ (ex - 1)
  have hmxR : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hmx
  have hpowEx : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) ex
  have hxrPos : 0 < xr := by
    simpa [xr, x, B754_to_R, F2R, FloatSpec.Core.Defs.F2R] using mul_pos hmxR hpowEx
  have hcanonBool : canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true :=
    canonical_mantissa_of_specFloat_bounded (prec:=prec) (emax:=emax) hbounded
  have hcanonTrip := canonical_canonical_mantissa_bsn
    (prec:=prec) (emax:=emax) false mx ex hmx hcanonBool
  have hcanon :
      FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
        (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex) := by
    simpa [wp, PostCond.noThrow, pure] using hcanonTrip trivial
  have hformat : FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec) xr := by
    change FloatSpec.Core.Generic_fmt.generic_format 2
      (FLT_exp (3 - emax - prec) prec)
      (F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2))
    exact FloatSpec.Core.Generic_fmt.generic_format_canonical
      (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
      (f:=FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex) hcanon
  have hulpXTrip := FloatSpec.Core.Ulp.ulp_canonical
    (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
    (m:=(mx : Int)) (e:=ex) (by exact_mod_cast (Nat.ne_of_gt hmx))
    (by norm_num : (1 : Int) < 2) hcanon
  have hulpX : FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec) xr =
      (2 : ℝ) ^ ex := by
    simpa [wp, PostCond.noThrow, pure, xr, x, B754_to_R] using hulpXTrip trivial
  have hulpPredCasesTrip := FloatSpec.Core.FLT.ulp_FLT_pred_pos
    (prec:=prec) (emin:=3 - emax - prec) (beta:=2) xr
  have hulpPredCases :
      FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec)
          (FloatSpec.Core.Ulp.pred 2 (FLT_exp (3 - emax - prec) prec) xr) =
            FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec) xr ∨
        (xr = (2 : ℝ) ^ (FloatSpec.Core.Raux.mag 2 xr - 1) ∧
          FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec)
              (FloatSpec.Core.Ulp.pred 2 (FLT_exp (3 - emax - prec) prec) xr) =
            FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec) xr / 2) := by
    simpa [FLT_exp, wp, PostCond.noThrow, pure] using
      hulpPredCasesTrip ⟨by norm_num, hformat, le_of_lt hxrPos⟩
  have hpowHalf : (2 : ℝ) ^ ex / 2 = eps := by
    calc
      (2 : ℝ) ^ ex / 2 = (2 : ℝ) ^ ex * (2 : ℝ) ^ (-1 : Int) := by ring_nf
      _ = (2 : ℝ) ^ (ex + (-1 : Int)) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = eps := by simp [eps, sub_eq_add_neg]
  have hepsLePredUlp : eps ≤ FloatSpec.Core.Ulp.ulp 2
      (FLT_exp (3 - emax - prec) prec)
      (FloatSpec.Core.Ulp.pred 2 (FLT_exp (3 - emax - prec) prec) xr) := by
    rcases hulpPredCases with hsame | ⟨_, hhalf⟩
    · rw [hsame, hulpX]
      exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    · rw [hhalf, hulpX, hpowHalf]
  have hepsPos : 0 < eps := by
    exact zpow_pos (by norm_num : (0 : ℝ) < 2) _
  have hepsLeX : eps ≤ xr := by
    have hpowLe : eps ≤ (2 : ℝ) ^ ex :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hmxOne : (1 : ℝ) ≤ (mx : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hmx)
    calc
      eps ≤ (2 : ℝ) ^ ex := hpowLe
      _ = 1 * (2 : ℝ) ^ ex := by ring
      _ ≤ (mx : ℝ) * (2 : ℝ) ^ ex :=
        mul_le_mul_of_nonneg_right hmxOne (le_of_lt hpowEx)
      _ = xr := by simp [xr, x, B754_to_R, F2R, FloatSpec.Core.Defs.F2R]
  let q := xr - eps
  have hqNonneg : 0 ≤ q := sub_nonneg.mpr hepsLeX
  have hfloorPred := roundR_floor_minus_eps_pos (prec:=prec) (emax:=emax)
    xr eps hxrPos hformat ⟨hepsPos, hepsLePredUlp⟩
  have hpredEqPosTrip := FloatSpec.Core.Ulp.pred_eq_pos
    (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec) xr (le_of_lt hxrPos)
  have hpredEqPos :
      FloatSpec.Core.Ulp.pred 2 (FLT_exp (3 - emax - prec) prec) xr =
        FloatSpec.Core.Ulp.pred_pos 2 (FLT_exp (3 - emax - prec) prec) xr := by
    simpa [wp, PostCond.noThrow, pure] using hpredEqPosTrip (by norm_num)
  have hrtzQ : FloatSpec.Core.Generic_fmt.roundR 2
      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RTZ) q =
        FloatSpec.Core.Ulp.pred_pos 2 (FLT_exp (3 - emax - prec) prec) xr := by
    rw [roundR_RTZ_eq_floor_of_nonneg (prec:=prec) (emax:=emax) q hqNonneg]
    simpa [q, hpredEqPos] using hfloorPred
  have hpredNonnegTrip := FloatSpec.Core.Ulp.pred_pos_ge_0
    (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec) xr hxrPos hformat
  have hpredNonneg : 0 ≤ FloatSpec.Core.Ulp.pred_pos 2
      (FLT_exp (3 - emax - prec) prec) xr := by
    simpa [wp, PostCond.noThrow, pure] using hpredNonnegTrip (by norm_num)
  let mn := 2 * mx - 1
  have hmnPos : 0 < mn := by simp [mn]; omega
  have hmnCast : (mn : ℝ) = 2 * (mx : ℝ) - 1 := by
    have hone : 1 ≤ 2 * mx := by omega
    simp [mn, Nat.cast_sub hone]
  have hpowSplit : (2 : ℝ) ^ ex = 2 * (2 : ℝ) ^ (ex - 1) := by
    calc
      (2 : ℝ) ^ ex = (2 : ℝ) ^ (1 + (ex - 1)) := by ring_nf
      _ = (2 : ℝ) ^ (1 : Int) * (2 : ℝ) ^ (ex - 1) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = 2 * (2 : ℝ) ^ (ex - 1) := by norm_num
  have hinput :
      SF2R 2 (StandardFloat.S754_finite true mn (ex - 1)) = -q := by
    simp [SF2R, F2R, FloatSpec.Core.Defs.F2R, q, xr, x, B754_to_R,
      eps, hmnCast, hpowSplit]
    ring
  have hroundOpp := FloatSpec.Core.Generic_fmt.roundR_opp
    (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
    (rnd:=rnd_of_mode RoundingMode.RTZ) q (by norm_num : (1 : Int) < 2)
  have hrtzNeg : FloatSpec.Core.Generic_fmt.roundR 2
      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RTZ) (-q) =
        -FloatSpec.Core.Ulp.pred_pos 2 (FLT_exp (3 - emax - prec) prec) xr := by
    calc
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
          (rnd_of_mode RoundingMode.RTZ) (-q) =
        -FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
          (FloatSpec.Core.Generic_fmt.Zrnd_opp (rnd_of_mode RoundingMode.RTZ)) q := hroundOpp
      _ = -FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
          (rnd_of_mode RoundingMode.RTZ) q := by rw [Zrnd_opp_RTZ]
      _ = -FloatSpec.Core.Ulp.pred_pos 2 (FLT_exp (3 - emax - prec) prec) xr := by
        rw [hrtzQ]
  have hrange := range_bounded_of_specFloat_bounded
    (prec:=prec) (emax:=emax) mx ex hmx hbounded
  have hxrLtTrip := bounded_lt_emax (prec:=prec) (emax:=emax) mx ex hrange
  have hxrLt : xr < FloatSpec.Core.Raux.bpow 2 emax := by
    simpa [wp, PostCond.noThrow, pure, xr, x, B754_to_R] using hxrLtTrip trivial
  have hpredLeTrip := FloatSpec.Core.Ulp.pred_le_id
    (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec) xr
  have hpredLe : FloatSpec.Core.Ulp.pred_pos 2
      (FLT_exp (3 - emax - prec) prec) xr ≤ xr := by
    have hle : FloatSpec.Core.Ulp.pred 2
        (FLT_exp (3 - emax - prec) prec) xr ≤ xr := by
      simpa [wp, PostCond.noThrow, pure] using hpredLeTrip (by norm_num)
    simpa [hpredEqPos] using hle
  have hover : FloatSpec.Core.Raux.Rlt_bool
      |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
        (rnd_of_mode RoundingMode.RTZ)
        (SF2R 2 (StandardFloat.S754_finite true mn (ex - 1)))|
      (FloatSpec.Core.Raux.bpow 2 emax) = true := by
    rw [hinput, hrtzNeg]
    simp [FloatSpec.Core.Raux.Rlt_bool, abs_of_nonneg hpredNonneg,
      lt_of_le_of_lt hpredLe hxrLt]
  let z := binary_round (prec:=prec) (emax:=emax)
    RoundingMode.RTZ true mn (ex - 1)
  have hround := binary_round_correct (prec:=prec) (emax:=emax)
    RoundingMode.RTZ true mn (ex - 1) hmnPos
  have hbranch := hround.2
  dsimp at hbranch
  rw [hover] at hbranch
  simp at hbranch
  have hr : Bpred (prec:=prec) (emax:=emax) x = Bopp_bsn (SF2B z) := by
    simp [x, Bpred, Bsucc, Bopp_bsn, z, mn]
  have hvalidZ : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true := by
    simpa [z] using hround.1
  have hvalueZ : SF2R 2 z = FloatSpec.Core.Generic_fmt.roundR 2
      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RTZ)
      (SF2R 2 (StandardFloat.S754_finite true mn (ex - 1))) := by
    simpa [z] using hbranch.1
  have hfiniteZ : is_finite_SF z = true := by
    simpa [z] using hbranch.2.1
  have hsignZ : sign_SF z = true := by
    simpa [z] using hbranch.2.2
  have hvalidOpp :
      validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
          (B2SF_BSN (Bopp_bsn (SF2B z))) =
        validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z := by
    cases z <;> rfl
  have hfiniteOpp : BSN_is_finite (Bopp_bsn (SF2B z)) = is_finite_SF z := by
    cases z <;> rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr, hvalidOpp, hvalidZ]
  · rw [hr]
    have hvalueOpp : B754_to_R (Bopp_bsn (SF2B z)) = -SF2R 2 z := by
      cases z with
      | S754_zero s => simp [B754_to_R, Bopp_bsn, SF2B, SF2R]
      | S754_infinity s => simp [B754_to_R, Bopp_bsn, SF2B, SF2R]
      | S754_nan => simp [B754_to_R, Bopp_bsn, SF2B, SF2R]
      | S754_finite s m e =>
          cases s <;> simp [B754_to_R, Bopp_bsn, SF2B, SF2R, F2R,
            FloatSpec.Core.Defs.F2R]
    rw [hvalueOpp, hvalueZ, hinput, hrtzNeg]
    ring
  · rw [hr, hfiniteOpp, hfiniteZ]
  · rw [hr]
    cases hz : z <;> simp [hz, BSN_sign, SF2B, Bopp_bsn, sign_SF] at hsignZ ⊢
    all_goals assumption

private theorem value_boundary_of_mantissa_boundary {prec : Int}
    [Prec_gt_0 prec]
    (mx : Nat) (ex : Int) (hboundary : 2 * mx = (2 : Nat) ^ prec.toNat) :
    B754_to_R (B754.B754_finite false mx ex) =
      (2 : ℝ) ^
        (FloatSpec.Core.Raux.mag 2
          (B754_to_R (B754.B754_finite false mx ex)) - 1) := by
  have hprecNonneg : 0 ≤ prec := le_of_lt (inferInstance : Prec_gt_0 prec).pos
  have hcastPow : (((2 : Nat) ^ prec.toNat : Nat) : ℝ) = (2 : ℝ) ^ prec := by
    rw [Nat.cast_pow, ← zpow_natCast]
    congr 1
    exact Int.toNat_of_nonneg hprecNonneg
  have hboundaryR : 2 * (mx : ℝ) = (2 : ℝ) ^ prec := by
    have hcast := congrArg (fun n : Nat => (n : ℝ)) hboundary
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcast
    simpa [hcastPow] using hcast
  have hpowSplit : (2 : ℝ) ^ prec = 2 * (2 : ℝ) ^ (prec - 1) := by
    calc
      (2 : ℝ) ^ prec = (2 : ℝ) ^ (1 + (prec - 1)) := by ring_nf
      _ = (2 : ℝ) ^ (1 : Int) * (2 : ℝ) ^ (prec - 1) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = 2 * (2 : ℝ) ^ (prec - 1) := by norm_num
  have hmxR : (mx : ℝ) = (2 : ℝ) ^ (prec - 1) := by
    linarith
  have hmxIR : ((mx : Int) : ℝ) = (2 : ℝ) ^ (prec - 1) := by
    simpa using hmxR
  let xr := B754_to_R (B754.B754_finite false mx ex)
  have hxrPower : xr = (2 : ℝ) ^ (prec + ex - 1) := by
    simp only [xr, B754_to_R, F2R, FloatSpec.Core.Defs.F2R,
      Bool.false_eq_true, ↓reduceIte]
    rw [hmxIR]
    change (2 : ℝ) ^ (prec - 1) * (2 : ℝ) ^ ex =
      (2 : ℝ) ^ (prec + ex - 1)
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  have hmagTrip := FloatSpec.Core.Raux.mag_bpow
    (beta:=2) (e:=prec + ex - 1) (by norm_num : (1 : Int) < 2)
  have hmag : FloatSpec.Core.Raux.mag 2 xr = prec + ex := by
    rw [hxrPower]
    simpa [wp, PostCond.noThrow, pure] using hmagTrip trivial
  change xr = (2 : ℝ) ^ (FloatSpec.Core.Raux.mag 2 xr - 1)
  rw [hmag, hxrPower]

private theorem ulp_eq_boundary_step_of_mantissa_nonboundary {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mx : Nat) (ex : Int) (hmx : 0 < mx)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true)
    (hmant : 2 * mx ≠ (2 : Nat) ^ prec.toNat)
    (hvalue : B754_to_R (B754.B754_finite false mx ex) =
      (2 : ℝ) ^
        (FloatSpec.Core.Raux.mag 2
          (B754_to_R (B754.B754_finite false mx ex)) - 1)) :
    FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec)
        (B754_to_R (B754.B754_finite false mx ex)) =
      (2 : ℝ) ^ (FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Raux.mag 2
          (B754_to_R (B754.B754_finite false mx ex)) - 1)) := by
  let xr := B754_to_R (B754.B754_finite false mx ex)
  let M := FloatSpec.Core.Raux.mag 2 xr
  have hcanonBool := canonical_mantissa_of_specFloat_bounded
    (prec:=prec) (emax:=emax) hbounded
  have hcanonTrip := canonical_canonical_mantissa_bsn
    (prec:=prec) (emax:=emax) false mx ex hmx hcanonBool
  have hcanon : FloatSpec.Core.Generic_fmt.canonical 2
      (FLT_exp (3 - emax - prec) prec)
      (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex) := by
    simpa [wp, PostCond.noThrow, pure] using hcanonTrip trivial
  have hexCanon : ex = FLT_exp (3 - emax - prec) prec M := by
    simpa [FloatSpec.Core.Generic_fmt.canonical, M, xr, B754_to_R] using hcanon
  have hulpTrip := FloatSpec.Core.Ulp.ulp_canonical
    (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
    (m:=(mx : Int)) (e:=ex) (by exact_mod_cast (Nat.ne_of_gt hmx))
    (by norm_num : (1 : Int) < 2) hcanon
  have hulp : FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec) xr =
      (2 : ℝ) ^ ex := by
    simpa [wp, PostCond.noThrow, pure, xr, B754_to_R, F2R,
      FloatSpec.Core.Defs.F2R] using hulpTrip trivial
  have hMsmall : M ≤ 3 - emax - prec + prec := by
    by_contra hnot
    have hlarge : 3 - emax - prec + prec < M := lt_of_not_ge hnot
    have hexLarge : ex = M - prec := by
      rw [hexCanon]
      unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
      rw [max_eq_left]
      omega
    have hxrepr : (mx : ℝ) * (2 : ℝ) ^ ex = (2 : ℝ) ^ (M - 1) := by
      simpa [xr, M, B754_to_R, F2R, FloatSpec.Core.Defs.F2R] using hvalue
    have hpowDecomp : (2 : ℝ) ^ (M - 1) =
        (2 : ℝ) ^ (M - prec) * (2 : ℝ) ^ (prec - 1) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      ring
    rw [hexLarge, hpowDecomp] at hxrepr
    have hpowPos : 0 < (2 : ℝ) ^ (M - prec) := zpow_pos (by norm_num) _
    have hmxR : (mx : ℝ) = (2 : ℝ) ^ (prec - 1) := by
      nlinarith
    have hprecNonneg : 0 ≤ prec := le_of_lt (inferInstance : Prec_gt_0 prec).pos
    have hcastPow : (((2 : Nat) ^ prec.toNat : Nat) : ℝ) = (2 : ℝ) ^ prec := by
      rw [Nat.cast_pow, ← zpow_natCast]
      congr 1
      exact Int.toNat_of_nonneg hprecNonneg
    have hpowSplit : (2 : ℝ) ^ prec = 2 * (2 : ℝ) ^ (prec - 1) := by
      calc
        (2 : ℝ) ^ prec = (2 : ℝ) ^ (1 + (prec - 1)) := by ring_nf
        _ = (2 : ℝ) ^ (1 : Int) * (2 : ℝ) ^ (prec - 1) := by
          rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ = 2 * (2 : ℝ) ^ (prec - 1) := by norm_num
    have hboundaryR : 2 * (mx : ℝ) = (2 : ℝ) ^ prec := by
      rw [hmxR, hpowSplit]
    have hboundaryCast : ((2 * mx : Nat) : ℝ) = (((2 : Nat) ^ prec.toNat : Nat) : ℝ) := by
      simpa [hcastPow] using hboundaryR
    have hboundary : 2 * mx = (2 : Nat) ^ prec.toNat := by
      exact_mod_cast hboundaryCast
    exact hmant hboundary
  have hstep : FLT_exp (3 - emax - prec) prec M =
      FLT_exp (3 - emax - prec) prec (M - 1) := by
    unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
    rw [max_eq_right, max_eq_right]
    · omega
    · omega
  change FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec) xr =
    (2 : ℝ) ^ (FLT_exp (3 - emax - prec) prec (M - 1))
  rw [hulp, hexCanon, hstep]

private theorem Bpred_pos'_positive_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (hmax : 2 < emax) (mx : Nat) (ex : Int) (hmx : 0 < mx)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true) :
    let x := B754.B754_finite false mx ex
    let r := Bpred_pos' (prec:=prec) (emax:=emax) x
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) (B2SF_BSN r) = true ∧
      B754_to_R r = FloatSpec.Core.Ulp.pred_pos 2
        (FLT_exp (3 - emax - prec) prec) (B754_to_R x) ∧
      BSN_is_finite r = true ∧ BSN_sign r = false := by
  let x := B754.B754_finite false mx ex
  let xr := B754_to_R x
  let fp := FLT_exp (3 - emax - prec) prec
  have hmxR : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hmx
  have hpowEx : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) ex
  have hxrPos : 0 < xr := by
    simpa [xr, x, B754_to_R, F2R, FloatSpec.Core.Defs.F2R] using mul_pos hmxR hpowEx
  have hcanonBool := canonical_mantissa_of_specFloat_bounded
    (prec:=prec) (emax:=emax) hbounded
  have hcanonTrip := canonical_canonical_mantissa_bsn
    (prec:=prec) (emax:=emax) false mx ex hmx hcanonBool
  have hcanon : FloatSpec.Core.Generic_fmt.canonical 2 fp
      (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex) := by
    simpa [fp, wp, PostCond.noThrow, pure] using hcanonTrip trivial
  have hformat : FloatSpec.Core.Generic_fmt.generic_format 2 fp xr := by
    change FloatSpec.Core.Generic_fmt.generic_format 2 fp
      (F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2))
    exact FloatSpec.Core.Generic_fmt.generic_format_canonical
      (beta:=2) (fexp:=fp)
      (f:=FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex) hcanon
  have hulpTrip := FloatSpec.Core.Ulp.ulp_canonical
    (beta:=2) (fexp:=fp) (m:=(mx : Int)) (e:=ex)
    (by exact_mod_cast (Nat.ne_of_gt hmx)) (by norm_num : (1 : Int) < 2) hcanon
  have hulp : FloatSpec.Core.Ulp.ulp 2 fp xr = (2 : ℝ) ^ ex := by
    simpa [fp, xr, x, B754_to_R, wp, PostCond.noThrow, pure] using hulpTrip trivial
  have hulpPos : 0 < FloatSpec.Core.Ulp.ulp 2 fp xr := by
    rw [hulp]
    exact hpowEx
  have hrange := range_bounded_of_specFloat_bounded
    (prec:=prec) (emax:=emax) mx ex hmx hbounded
  have hxrLtTrip := bounded_lt_emax (prec:=prec) (emax:=emax) mx ex hrange
  have hxrLt : xr < FloatSpec.Core.Raux.bpow 2 emax := by
    simpa [xr, x, B754_to_R, wp, PostCond.noThrow, pure] using hxrLtTrip trivial
  have hmagTrip := FloatSpec.Core.Raux.mag_le_bpow
    (beta:=2) (x:=xr) (e:=emax) (by norm_num : (1 : Int) < 2)
    (ne_of_gt hxrPos) (by
      simpa only [abs_of_pos hxrPos, FloatSpec.Core.Raux.bpow] using hxrLt)
  have hmagLe : FloatSpec.Core.Raux.mag 2 xr ≤ emax := by
    simpa [wp, PostCond.noThrow, pure] using hmagTrip trivial
  have hfrexpMag := Bfrexp_exp_eq_mag_of_finite (prec:=prec) (emax:=emax)
    hmax false mx ex hmx hbounded
  let ed := fp ((Bfrexp_bsn (prec:=prec) (emax:=emax) x).2 - 1)
  have hed : ed = fp (FloatSpec.Core.Raux.mag 2 xr - 1) := by
    simp [ed, fp, xr, x, hfrexpMag]
  have heminEd : 3 - emax - prec ≤ ed := by
    simp [ed, fp, FLT_exp, FloatSpec.Core.FLT.FLT_exp]
  have hedMax : ed < emax := by
    rw [hed]
    unfold fp FLT_exp FloatSpec.Core.FLT.FLT_exp
    apply max_lt
    · have hprecPos := (inferInstance : Prec_gt_0 prec).pos
      omega
    · have hprecPos := (inferInstance : Prec_gt_0 prec).pos
      omega
  let d := if 2 * mx == (2 : Nat) ^ prec.toNat then
      Bldexp (prec:=prec) (emax:=emax) RoundingMode.RNE Bone ed
    else Bulp' (prec:=prec) (emax:=emax) x
  have hdPayload :
      B754_to_R d = xr - FloatSpec.Core.Ulp.pred_pos 2 fp xr ∧
        0 < B754_to_R d ∧ BSN_is_finite d = true ∧ BSN_sign d = false := by
    by_cases hb : 2 * mx == (2 : Nat) ^ prec.toNat
    · have hboundary : 2 * mx = (2 : Nat) ^ prec.toNat := eq_of_beq hb
      have hvalueBoundary := value_boundary_of_mantissa_boundary
        (prec:=prec) mx ex hboundary
      let z := binary_round (prec:=prec) (emax:=emax) RoundingMode.RNE false 1 ed
      have hzPayload := binary_round_one_payload (prec:=prec) (emax:=emax)
        RoundingMode.RNE ed heminEd hedMax
      have hdEq : d = SF2B z := by
        simp [d, hb, Bldexp, Bone, SF2B, z]
      have hB2R : B754_to_R (SF2B z) = SF2R 2 z := by
        cases z <;> rfl
      have hfinite : BSN_is_finite (SF2B z) = is_finite_SF z := by
        cases z <;> rfl
      have hsign : BSN_sign (SF2B z) = sign_SF z := by
        cases z <;> rfl
      rw [hdEq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hB2R, hzPayload.2.1, hed]
        simp only [FloatSpec.Core.Raux.bpow]
        unfold FloatSpec.Core.Ulp.pred_pos
        rw [ite_eq_left (by simpa [xr, x] using hvalueBoundary)]
        ring
      · rw [hB2R, hzPayload.2.1]
        exact zpow_pos (by norm_num) _
      · exact hfinite.trans hzPayload.2.2.1
      · exact hsign.trans hzPayload.2.2.2
    · have hmant : 2 * mx ≠ (2 : Nat) ^ prec.toNat := by simpa using hb
      let xpf := BinarySingleNaNFloat.B754_finite (prec:=prec) (emax:=emax)
        false mx ex hmx hbounded
      have hxpf : binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) xpf = x := rfl
      have hulpEq := Bulp'_correct (prec:=prec) (emax:=emax) hmax xpf (by rfl)
      have hulpPayload := Bulp_correct (prec:=prec) (emax:=emax) xpf (by rfl)
      have hdEq : d = Bulp (prec:=prec) (emax:=emax) x := by
        calc
          d = Bulp' (prec:=prec) (emax:=emax) x := by simp [d, hb]
          _ = Bulp (prec:=prec) (emax:=emax) x := by
            rw [← hxpf]
            exact hulpEq
      have hdValue : B754_to_R d = FloatSpec.Core.Ulp.ulp 2 fp xr := by
        change B754_to_R d = FloatSpec.Core.Ulp.ulp 2
          (FLT_exp (3 - emax - prec) prec) (B754_to_R x)
        rw [hdEq]
        rw [← hxpf]
        exact hulpPayload.1
      rw [hdValue]
      refine ⟨?_, hulpPos, ?_, ?_⟩
      · by_cases hreal : xr = ((2 : Int) : ℝ) ^ (FloatSpec.Core.Raux.mag 2 xr - 1)
        · have hstep := ulp_eq_boundary_step_of_mantissa_nonboundary
            (prec:=prec) (emax:=emax) mx ex hmx hbounded hmant
            (by simpa [xr, x] using hreal)
          unfold FloatSpec.Core.Ulp.pred_pos
          rw [ite_eq_left hreal]
          have hstep' : FloatSpec.Core.Ulp.ulp 2 fp xr =
              ((2 : Int) : ℝ) ^ (fp (FloatSpec.Core.Raux.mag 2 xr - 1)) := by
            simpa [fp, xr, x] using hstep
          rw [hstep']
          ring
        · unfold FloatSpec.Core.Ulp.pred_pos
          rw [ite_eq_right hreal]
          ring
      · rw [hdEq]
        rw [← hxpf]
        exact hulpPayload.2.1
      · rw [hdEq]
        rw [← hxpf]
        exact hulpPayload.2.2
  have hpredNonnegTrip := FloatSpec.Core.Ulp.pred_pos_ge_0
    (beta:=2) (fexp:=fp) xr hxrPos hformat
  have hpredNonneg : 0 ≤ FloatSpec.Core.Ulp.pred_pos 2 fp xr := by
    simpa [wp, PostCond.noThrow, pure] using hpredNonnegTrip (by norm_num)
  have hdShape : ∃ my ey, d = B754.B754_finite false my ey ∧ 0 < my := by
    cases hd : d with
    | B754_zero sd =>
        simp [hd, B754_to_R] at hdPayload
    | B754_infinity sd =>
        simp [hd, BSN_is_finite] at hdPayload
    | B754_nan =>
        simp [hd, BSN_is_finite] at hdPayload
    | B754_finite sd my ey =>
        have hsd : sd = false := by
          simpa [hd, BSN_sign] using hdPayload.2.2.2
        subst sd
        have hmy : 0 < my := by
          by_contra hnot
          have hzero : my = 0 := Nat.eq_zero_of_not_pos hnot
          simp [hd, hzero, B754_to_R, F2R, FloatSpec.Core.Defs.F2R] at hdPayload
        exact ⟨my, ey, rfl, hmy⟩
  rcases hdShape with ⟨my, ey, hd, hmy⟩
  have hsum :
      B754_to_R (B754.B754_finite false mx ex) +
          B754_to_R (B754.B754_finite true my ey) =
        FloatSpec.Core.Ulp.pred_pos 2 fp xr := by
    have hdValue := hdPayload.1
    rw [hd] at hdValue
    simp [xr, x, B754_to_R, F2R, FloatSpec.Core.Defs.F2R] at hdValue ⊢
    linarith
  have hsumNonneg : 0 ≤
      B754_to_R (B754.B754_finite false mx ex) +
        B754_to_R (B754.B754_finite true my ey) := by
    rw [hsum]
    exact hpredNonneg
  have hpredFormatTrip := FloatSpec.Core.Ulp.generic_format_pred_pos
    (beta:=2) (fexp:=fp) xr hformat hxrPos (by norm_num : (1 : Int) < 2)
  have hpredFormat : FloatSpec.Core.Generic_fmt.generic_format 2 fp
      (FloatSpec.Core.Ulp.pred_pos 2 fp xr) := by
    simpa [wp, PostCond.noThrow, pure] using hpredFormatTrip trivial
  have hroundPred := FloatSpec.Core.Generic_fmt.roundR_generic
    (beta:=2) (fexp:=fp) (rnd:=rnd_of_mode RoundingMode.RNE)
    (x:=FloatSpec.Core.Ulp.pred_pos 2 fp xr) (by norm_num : (1 : Int) < 2)
    hpredFormat
  have hpredLe : FloatSpec.Core.Ulp.pred_pos 2 fp xr < xr := by
    linarith [hdPayload.2.1]
  have hpredLt : FloatSpec.Core.Ulp.pred_pos 2 fp xr <
      FloatSpec.Core.Raux.bpow 2 emax := lt_trans hpredLe hxrLt
  have hlt : FloatSpec.Core.Raux.Rlt_bool
      |FloatSpec.Core.Generic_fmt.roundR 2 fp (rnd_of_mode RoundingMode.RNE)
        (B754_to_R (B754.B754_finite false mx ex) +
          B754_to_R (B754.B754_finite true my ey))|
      (FloatSpec.Core.Raux.bpow 2 emax) = true := by
    rw [hsum, hroundPred]
    simp [FloatSpec.Core.Raux.Rlt_bool, abs_of_nonneg hpredNonneg, hpredLt]
  have hplus := Bplus_finite_nonnegative_correct (prec:=prec) (emax:=emax)
    mx my ex ey hmx hmy hsumNonneg hlt
  have hr : Bpred_pos' (prec:=prec) (emax:=emax) x =
      Bplus (prec:=prec) (emax:=emax) RoundingMode.RNE
        (B754.B754_finite false mx ex) (B754.B754_finite true my ey) := by
    change Bplus (prec:=prec) (emax:=emax) RoundingMode.RNE x (Bopp_bsn d) =
      Bplus (prec:=prec) (emax:=emax) RoundingMode.RNE
        (B754.B754_finite false mx ex) (B754.B754_finite true my ey)
    rw [hd]
    rfl
  change validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
      (B2SF_BSN (Bpred_pos' (prec:=prec) (emax:=emax) x)) = true ∧
    B754_to_R (Bpred_pos' (prec:=prec) (emax:=emax) x) =
        FloatSpec.Core.Ulp.pred_pos 2 fp xr ∧
      BSN_is_finite (Bpred_pos' (prec:=prec) (emax:=emax) x) = true ∧
        BSN_sign (Bpred_pos' (prec:=prec) (emax:=emax) x) = false
  rw [hr]
  refine ⟨hplus.1, ?_, hplus.2.2.1, hplus.2.2.2⟩
  rw [hplus.2.1, hsum, hroundPred]

-- Coq: Bpred_pos'_correct
theorem Bpred_pos'_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (hmax : 2 < emax) (x : BinarySingleNaNFloat prec emax)
    (hxpos : 0 < B754_to_R
      (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x)) :
    Bpred_pos' (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) =
      Bpred (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) := by
  cases x with
  | B754_zero sx =>
      simp [binarySingleNaNFloatToB754, B754_to_R] at hxpos
  | B754_infinity sx =>
      simp [binarySingleNaNFloatToB754, B754_to_R] at hxpos
  | B754_nan =>
      simp [binarySingleNaNFloatToB754, B754_to_R] at hxpos
  | B754_finite sx mx ex hmx hbounded =>
      cases sx with
      | false =>
          let raw := B754.B754_finite false mx ex
          have hopt := Bpred_pos'_positive_correct (prec:=prec) (emax:=emax)
            hmax mx ex hmx hbounded
          have href := Bpred_positive_correct (prec:=prec) (emax:=emax)
            mx ex hmx hbounded
          change Bpred_pos' (prec:=prec) (emax:=emax) raw =
            Bpred (prec:=prec) (emax:=emax) raw
          apply B754_eq_of_valid_finite_sign_value (prec:=prec) (emax:=emax)
          · exact hopt.1
          · exact href.1
          · exact hopt.2.2.1
          · exact href.2.2.1
          · exact hopt.2.1.trans href.2.1.symm
          · exact hopt.2.2.2.trans href.2.2.2.symm
      | true =>
          have hmxR : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hmx
          have hpow : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) ex
          have hneg : -(mx : ℝ) * (2 : ℝ) ^ ex < 0 :=
            mul_neg_of_neg_of_pos (neg_neg_of_pos hmxR) hpow
          simp [binarySingleNaNFloatToB754, B754_to_R, F2R,
            FloatSpec.Core.Defs.F2R] at hxpos
          linarith

private theorem Bplus_finite_positive_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mx my : Nat) (ex ey : Int) (hmx : 0 < mx) (hmy : 0 < my) :
    let x := B754.B754_finite false mx ex
    let y := B754.B754_finite false my ey
    let r := Bplus (prec:=prec) (emax:=emax) RoundingMode.RNE x y
    let rounded := FloatSpec.Core.Generic_fmt.roundR 2
      (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RNE)
      (B754_to_R x + B754_to_R y)
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
        (B2SF_BSN r) = true ∧
      if FloatSpec.Core.Raux.Rlt_bool |rounded|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        B754_to_R r = rounded ∧ BSN_is_finite r = true ∧ BSN_sign r = false
      else
        r = B754.B754_infinity false := by
  let x := B754.B754_finite false mx ex
  let y := B754.B754_finite false my ey
  let ez := min ex ey
  let m := Fplus_naive false mx ex false my ey ez
  let r := Bplus (prec:=prec) (emax:=emax) RoundingMode.RNE x y
  let rounded := FloatSpec.Core.Generic_fmt.roundR 2
    (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RNE)
    (B754_to_R x + B754_to_R y)
  have hsumRaw := Fplus_naive_correct false mx ex false my ey ez
    (min_le_left ex ey) (min_le_right ex ey)
  have hsum :
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk m ez :
        FloatSpec.Core.Defs.FlocqFloat 2) = B754_to_R x + B754_to_R y := by
    simpa [m, ez, x, y, B754_to_R, FloatSpec.Core.Zaux.cond_Zopp] using hsumRaw
  have hxPos : 0 < B754_to_R x := by
    have hmxR : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hmx
    have hpow : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) ex
    simpa [x, B754_to_R, F2R, FloatSpec.Core.Defs.F2R] using mul_pos hmxR hpow
  have hyPos : 0 < B754_to_R y := by
    have hmyR : (0 : ℝ) < (my : ℝ) := Nat.cast_pos.mpr hmy
    have hpow : (0 : ℝ) < (2 : ℝ) ^ ey := zpow_pos (by norm_num) ey
    simpa [y, B754_to_R, F2R, FloatSpec.Core.Defs.F2R] using mul_pos hmyR hpow
  have hsumPos : 0 < B754_to_R x + B754_to_R y := add_pos hxPos hyPos
  have hpowEz : (0 : ℝ) < (2 : ℝ) ^ ez := zpow_pos (by norm_num) ez
  have hmRealPos : (0 : ℝ) < (m : ℝ) := by
    apply (mul_pos_iff_of_pos_right hpowEz).mp
    have hF2RPos :
        0 < F2R (FloatSpec.Core.Defs.FlocqFloat.mk m ez :
          FloatSpec.Core.Defs.FlocqFloat 2) := by
      rw [hsum]
      exact hsumPos
    simpa [F2R, FloatSpec.Core.Defs.F2R] using hF2RPos
  have hmPos : 0 < m := by exact_mod_cast hmRealPos
  have hmNe : m ≠ 0 := ne_of_gt hmPos
  have hmNonneg : 0 ≤ m := le_of_lt hmPos
  have hmCast : (m.toNat : Int) = m := Int.toNat_of_nonneg hmNonneg
  have hmNatPos : 0 < m.toNat := by omega
  let z := binary_round (prec:=prec) (emax:=emax)
    RoundingMode.RNE false m.toNat ez
  have hround := binary_round_correct (prec:=prec) (emax:=emax)
    RoundingMode.RNE false m.toNat ez hmNatPos
  have hinput :
      SF2R 2 (StandardFloat.S754_finite false m.toNat ez) =
        B754_to_R x + B754_to_R y := by
    simpa [SF2R, F2R, FloatSpec.Core.Defs.F2R, hmCast] using hsum
  have hr : r = SF2B z := by
    simp [r, x, y, Bplus, binary_normalize, m, ez, hmNe, hmPos, z]
  have hview : B2SF_BSN (SF2B z) = z := by
    cases z <;> rfl
  have hvalueView : B754_to_R (SF2B z) = SF2R 2 z := by
    cases z <;> rfl
  have hfiniteView : BSN_is_finite (SF2B z) = is_finite_SF z := by
    cases z <;> rfl
  have hsignView : BSN_sign (SF2B z) = sign_SF z := by
    cases z <;> rfl
  change validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
      (B2SF_BSN r) = true ∧
    (if FloatSpec.Core.Raux.Rlt_bool |rounded|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B754_to_R r = rounded ∧ BSN_is_finite r = true ∧ BSN_sign r = false
    else
      r = B754.B754_infinity false)
  constructor
  · rw [hr, hview]
    exact hround.1
  · by_cases hlt : FloatSpec.Core.Raux.Rlt_bool |rounded|
        (FloatSpec.Core.Raux.bpow 2 emax) = true
    · rw [ite_eq_left hlt]
      have hltInput :
          FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RNE)
              (SF2R 2 (StandardFloat.S754_finite false m.toNat ez))|
            (FloatSpec.Core.Raux.bpow 2 emax) = true := by
        simpa [rounded, hinput] using hlt
      have hbranch := hround.2
      dsimp at hbranch
      rw [hltInput] at hbranch
      simp at hbranch
      refine ⟨?_, ?_, ?_⟩
      · rw [hr, hvalueView, hbranch.1]
        simp [rounded, hinput]
      · rw [hr, hfiniteView, hbranch.2.1]
      · rw [hr, hsignView, hbranch.2.2]
    · rw [ite_eq_right hlt]
      have hltInput :
          FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode RoundingMode.RNE)
              (SF2R 2 (StandardFloat.S754_finite false m.toNat ez))|
            (FloatSpec.Core.Raux.bpow 2 emax) = false := by
        have hfalse := Bool.eq_false_of_not_eq_true hlt
        simpa [rounded, hinput] using hfalse
      have hbranch := hround.2
      dsimp at hbranch
      rw [hltInput] at hbranch
      simp at hbranch
      have hover : z = bsn_binary_overflow (prec:=prec) (emax:=emax)
          RoundingMode.RNE false := by
        simpa [z] using hbranch
      rw [hr, hover]
      rfl

private theorem Bsucc_positive_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mx : Nat) (ex : Int) (hmx : 0 < mx)
    (hbounded : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true) :
    let x := B754.B754_finite false mx ex
    let r := Bsucc (prec:=prec) (emax:=emax) x
    let successor := FloatSpec.Core.Ulp.succ 2
      (FLT_exp (3 - emax - prec) prec) (B754_to_R x)
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
        (B2SF_BSN r) = true ∧
      if FloatSpec.Core.Raux.Rlt_bool |successor|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        B754_to_R r = successor ∧ BSN_is_finite r = true ∧ BSN_sign r = false
      else
        r = B754.B754_infinity false := by
  let x := B754.B754_finite false mx ex
  let xr := B754_to_R x
  let fp := FLT_exp (3 - emax - prec) prec
  let successor := FloatSpec.Core.Ulp.succ 2 fp xr
  let z := binary_round (prec:=prec) (emax:=emax)
    RoundingMode.RTP false (mx + 1) ex
  let r := Bsucc (prec:=prec) (emax:=emax) x
  have hmxR : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hmx
  have hpow : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) ex
  have hxrPos : 0 < xr := by
    simpa [xr, x, B754_to_R, F2R, FloatSpec.Core.Defs.F2R] using mul_pos hmxR hpow
  have hcanonBool := canonical_mantissa_of_specFloat_bounded
    (prec:=prec) (emax:=emax) hbounded
  have hcanonTrip := canonical_canonical_mantissa_bsn
    (prec:=prec) (emax:=emax) false mx ex hmx hcanonBool
  have hcanon : FloatSpec.Core.Generic_fmt.canonical 2 fp
      (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex) := by
    simpa [fp, wp, PostCond.noThrow, pure] using hcanonTrip trivial
  have hformat : FloatSpec.Core.Generic_fmt.generic_format 2 fp xr := by
    change FloatSpec.Core.Generic_fmt.generic_format 2 fp
      (F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2))
    exact FloatSpec.Core.Generic_fmt.generic_format_canonical
      (beta:=2) (fexp:=fp)
      (f:=FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex) hcanon
  have hulpTrip := FloatSpec.Core.Ulp.ulp_canonical
    (beta:=2) (fexp:=fp) (m:=(mx : Int)) (e:=ex)
    (by exact_mod_cast (Nat.ne_of_gt hmx)) (by norm_num : (1 : Int) < 2) hcanon
  have hulp : FloatSpec.Core.Ulp.ulp 2 fp xr = (2 : ℝ) ^ ex := by
    simpa [fp, xr, x, B754_to_R, wp, PostCond.noThrow, pure] using hulpTrip trivial
  have hsuccTrip := FloatSpec.Core.Ulp.succ_eq_pos
    (beta:=2) (fexp:=fp) xr (le_of_lt hxrPos)
  have hsuccEq : successor = xr + FloatSpec.Core.Ulp.ulp 2 fp xr := by
    simpa [successor, wp, PostCond.noThrow, pure] using hsuccTrip trivial
  have hinput :
      SF2R 2 (StandardFloat.S754_finite false (mx + 1) ex) = successor := by
    rw [hsuccEq, hulp]
    simp [SF2R, F2R, FloatSpec.Core.Defs.F2R, xr, x, B754_to_R]
    ring
  have hsuccFormatTrip := FloatSpec.Core.Ulp.generic_format_succ
    (beta:=2) (fexp:=fp) xr hformat (by norm_num : (1 : Int) < 2)
  have hsuccFormat : FloatSpec.Core.Generic_fmt.generic_format 2 fp successor := by
    simpa [successor, wp, PostCond.noThrow, pure] using hsuccFormatTrip trivial
  have hroundEq :
      FloatSpec.Core.Generic_fmt.roundR 2 fp (rnd_of_mode RoundingMode.RTP)
          (SF2R 2 (StandardFloat.S754_finite false (mx + 1) ex)) = successor := by
    rw [hinput]
    exact FloatSpec.Core.Generic_fmt.roundR_generic
      (beta:=2) (fexp:=fp) (rnd:=rnd_of_mode RoundingMode.RTP)
      (x:=successor) (by norm_num) hsuccFormat
  have hmxSucc : 0 < mx + 1 := by omega
  have hround := binary_round_correct (prec:=prec) (emax:=emax)
    RoundingMode.RTP false (mx + 1) ex hmxSucc
  have hr : r = SF2B z := by
    simp [r, x, Bsucc, z]
  have hview : B2SF_BSN (SF2B z) = z := by
    cases z <;> rfl
  have hvalueView : B754_to_R (SF2B z) = SF2R 2 z := by
    cases z <;> rfl
  have hfiniteView : BSN_is_finite (SF2B z) = is_finite_SF z := by
    cases z <;> rfl
  have hsignView : BSN_sign (SF2B z) = sign_SF z := by
    cases z <;> rfl
  change validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax)
      (B2SF_BSN r) = true ∧
    (if FloatSpec.Core.Raux.Rlt_bool |successor|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B754_to_R r = successor ∧ BSN_is_finite r = true ∧ BSN_sign r = false
    else
      r = B754.B754_infinity false)
  constructor
  · rw [hr, hview]
    exact hround.1
  · by_cases hlt : FloatSpec.Core.Raux.Rlt_bool |successor|
        (FloatSpec.Core.Raux.bpow 2 emax) = true
    · rw [ite_eq_left hlt]
      have hltInput :
          FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2 fp (rnd_of_mode RoundingMode.RTP)
              (SF2R 2 (StandardFloat.S754_finite false (mx + 1) ex))|
            (FloatSpec.Core.Raux.bpow 2 emax) = true := by
        simpa [hroundEq] using hlt
      have hbranch := hround.2
      dsimp at hbranch
      rw [hltInput] at hbranch
      simp at hbranch
      refine ⟨?_, ?_, ?_⟩
      · rw [hr, hvalueView, hbranch.1, hroundEq]
      · rw [hr, hfiniteView, hbranch.2.1]
      · rw [hr, hsignView, hbranch.2.2]
    · rw [ite_eq_right hlt]
      have hltInput :
          FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2 fp (rnd_of_mode RoundingMode.RTP)
              (SF2R 2 (StandardFloat.S754_finite false (mx + 1) ex))|
            (FloatSpec.Core.Raux.bpow 2 emax) = false := by
        have hfalse := Bool.eq_false_of_not_eq_true hlt
        simpa [hroundEq] using hfalse
      have hbranch := hround.2
      dsimp at hbranch
      rw [hltInput] at hbranch
      simp at hbranch
      have hover : z = bsn_binary_overflow (prec:=prec) (emax:=emax)
          RoundingMode.RTP false := by
        simpa [z] using hbranch
      rw [hr, hover]
      rfl

-- Coq: Bsucc'_correct
theorem Bsucc'_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (hmax : 2 < emax) (x : BinarySingleNaNFloat prec emax)
    (hfinite : BSN_is_finite
      (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) = true) :
    Bsucc' (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) =
      Bsucc (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) := by
  cases x with
  | B754_zero sx =>
      let xzero : BinarySingleNaNFloat prec emax :=
        BinarySingleNaNFloat.B754_zero sx
      have hulp := Bulp'_correct (prec:=prec) (emax:=emax) hmax xzero (by rfl)
      have hsentinel :
          FLT_exp (3 - emax - prec) prec (-2 * emax - prec) =
            3 - emax - prec := by
        unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
        apply max_eq_right
        have hprec := (inferInstance : Prec_gt_0 prec).pos
        omega
      change Bldexp (prec:=prec) (emax:=emax) RoundingMode.RNE Bone
          (FLT_exp (3 - emax - prec) prec (-2 * emax - prec)) =
        B754.B754_finite false 1 (3 - emax - prec) at hulp
      change Bldexp (prec:=prec) (emax:=emax) RoundingMode.RNE Bone
          (3 - emax - prec) =
        B754.B754_finite false 1 (3 - emax - prec)
      rw [hsentinel] at hulp
      exact hulp
  | B754_infinity sx =>
      simp [binarySingleNaNFloatToB754, BSN_is_finite] at hfinite
  | B754_nan =>
      simp [binarySingleNaNFloatToB754, BSN_is_finite] at hfinite
  | B754_finite sx mx ex hmx hbounded =>
      cases sx with
      | false =>
          let raw := B754.B754_finite false mx ex
          let xpf : BinarySingleNaNFloat prec emax :=
            BinarySingleNaNFloat.B754_finite false mx ex hmx hbounded
          let xr := B754_to_R raw
          let fp := FLT_exp (3 - emax - prec) prec
          let successor := FloatSpec.Core.Ulp.succ 2 fp xr
          let y := Bulp (prec:=prec) (emax:=emax) raw
          have hulp := Bulp_correct (prec:=prec) (emax:=emax) xpf (by rfl)
          have hulpY :
              B754_to_R y = FloatSpec.Core.Ulp.ulp 2 fp xr ∧
                BSN_is_finite y = true ∧ BSN_sign y = false := by
            simpa [y, fp, xr, raw, xpf, binarySingleNaNFloatToB754] using hulp
          have hcanonBool := canonical_mantissa_of_specFloat_bounded
            (prec:=prec) (emax:=emax) hbounded
          have hcanonTrip := canonical_canonical_mantissa_bsn
            (prec:=prec) (emax:=emax) false mx ex hmx hcanonBool
          have hcanon : FloatSpec.Core.Generic_fmt.canonical 2 fp
              (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex) := by
            simpa [fp, wp, PostCond.noThrow, pure] using hcanonTrip trivial
          have hformat : FloatSpec.Core.Generic_fmt.generic_format 2 fp xr := by
            change FloatSpec.Core.Generic_fmt.generic_format 2 fp
              (F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
                FloatSpec.Core.Defs.FlocqFloat 2))
            exact FloatSpec.Core.Generic_fmt.generic_format_canonical
              (beta:=2) (fexp:=fp)
              (f:=FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex) hcanon
          have hulpTrip := FloatSpec.Core.Ulp.ulp_canonical
            (beta:=2) (fexp:=fp) (m:=(mx : Int)) (e:=ex)
            (by exact_mod_cast (Nat.ne_of_gt hmx))
            (by norm_num : (1 : Int) < 2) hcanon
          have hulpPow : FloatSpec.Core.Ulp.ulp 2 fp xr = (2 : ℝ) ^ ex := by
            simpa [fp, xr, raw, B754_to_R, wp, PostCond.noThrow, pure] using
              hulpTrip trivial
          have hyPos : 0 < B754_to_R y := by
            rw [hulpY.1, hulpPow]
            exact zpow_pos (by norm_num) ex
          have hyShape : ∃ my ey,
              y = B754.B754_finite false my ey ∧ 0 < my := by
            cases hy : y with
            | B754_zero sy =>
                simp [hy, B754_to_R] at hyPos
            | B754_infinity sy =>
                have hfalse := hulpY.2.1
                rw [hy] at hfalse
                simp [BSN_is_finite] at hfalse
            | B754_nan =>
                have hfalse := hulpY.2.1
                rw [hy] at hfalse
                simp [BSN_is_finite] at hfalse
            | B754_finite sy my ey =>
                have hsy : sy = false := by
                  have hsign := hulpY.2.2
                  rw [hy] at hsign
                  simpa [BSN_sign] using hsign
                subst sy
                have hmy : 0 < my := by
                  by_contra hnot
                  have hzero : my = 0 := Nat.eq_zero_of_not_pos hnot
                  simp [hy, hzero, B754_to_R, F2R, FloatSpec.Core.Defs.F2R] at hyPos
                exact ⟨my, ey, rfl, hmy⟩
          rcases hyShape with ⟨my, ey, hy, hmy⟩
          have hsuccTrip := FloatSpec.Core.Ulp.succ_eq_pos
            (beta:=2) (fexp:=fp) xr (by
              have hmxR : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hmx
              have hpow : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) ex
              exact le_of_lt (by
                simpa [xr, raw, B754_to_R, F2R, FloatSpec.Core.Defs.F2R] using
                  mul_pos hmxR hpow))
          have hsuccEq :
              successor = xr + FloatSpec.Core.Ulp.ulp 2 fp xr := by
            simpa [successor, wp, PostCond.noThrow, pure] using hsuccTrip trivial
          have hsumEq :
              B754_to_R raw +
                  B754_to_R (B754.B754_finite false my ey) = successor := by
            calc
              B754_to_R raw + B754_to_R (B754.B754_finite false my ey) =
                  xr + B754_to_R y := by rw [hy]
              _ = xr + FloatSpec.Core.Ulp.ulp 2 fp xr := by
                    rw [hulpY.1]
              _ = successor := hsuccEq.symm
          have hsuccFormatTrip := FloatSpec.Core.Ulp.generic_format_succ
            (beta:=2) (fexp:=fp) xr hformat (by norm_num : (1 : Int) < 2)
          have hsuccFormat :
              FloatSpec.Core.Generic_fmt.generic_format 2 fp successor := by
            simpa [successor, wp, PostCond.noThrow, pure] using
              hsuccFormatTrip trivial
          have hroundSum :
              FloatSpec.Core.Generic_fmt.roundR 2 fp
                  (rnd_of_mode RoundingMode.RNE)
                  (B754_to_R raw +
                    B754_to_R (B754.B754_finite false my ey)) = successor := by
            rw [hsumEq]
            exact FloatSpec.Core.Generic_fmt.roundR_generic
              (beta:=2) (fexp:=fp) (rnd:=rnd_of_mode RoundingMode.RNE)
              (x:=successor) (by norm_num) hsuccFormat
          have hplus := Bplus_finite_positive_correct
            (prec:=prec) (emax:=emax) mx my ex ey hmx hmy
          have href := Bsucc_positive_correct (prec:=prec) (emax:=emax)
            mx ex hmx hbounded
          change Bplus (prec:=prec) (emax:=emax) RoundingMode.RNE raw y =
            Bsucc (prec:=prec) (emax:=emax) raw
          rw [hy]
          by_cases hlt : FloatSpec.Core.Raux.Rlt_bool |successor|
              (FloatSpec.Core.Raux.bpow 2 emax) = true
          · have hltPlus :
                FloatSpec.Core.Raux.Rlt_bool
                  |FloatSpec.Core.Generic_fmt.roundR 2 fp
                    (rnd_of_mode RoundingMode.RNE)
                    (B754_to_R raw +
                      B754_to_R (B754.B754_finite false my ey))|
                  (FloatSpec.Core.Raux.bpow 2 emax) = true := by
              simpa [hroundSum] using hlt
            have hplusBranch := hplus.2
            rw [ite_eq_left hltPlus] at hplusBranch
            have hrefBranch := href.2
            rw [ite_eq_left hlt] at hrefBranch
            apply B754_eq_of_valid_finite_sign_value (prec:=prec) (emax:=emax)
            · exact hplus.1
            · exact href.1
            · exact hplusBranch.2.1
            · exact hrefBranch.2.1
            · calc
                B754_to_R (Bplus (prec:=prec) (emax:=emax) RoundingMode.RNE raw
                    (B754.B754_finite false my ey)) =
                    FloatSpec.Core.Generic_fmt.roundR 2 fp
                      (rnd_of_mode RoundingMode.RNE)
                      (B754_to_R raw +
                        B754_to_R (B754.B754_finite false my ey)) := hplusBranch.1
                _ = successor := hroundSum
                _ = B754_to_R (Bsucc (prec:=prec) (emax:=emax) raw) :=
                  hrefBranch.1.symm
            · exact hplusBranch.2.2.trans hrefBranch.2.2.symm
          · have hltPlus :
                FloatSpec.Core.Raux.Rlt_bool
                  |FloatSpec.Core.Generic_fmt.roundR 2 fp
                    (rnd_of_mode RoundingMode.RNE)
                    (B754_to_R raw +
                      B754_to_R (B754.B754_finite false my ey))|
                  (FloatSpec.Core.Raux.bpow 2 emax) = false := by
              have hfalse := Bool.eq_false_of_not_eq_true hlt
              simpa [hroundSum] using hfalse
            have hplusBranch := hplus.2
            have hltPlusNot :
                ¬FloatSpec.Core.Raux.Rlt_bool
                  |FloatSpec.Core.Generic_fmt.roundR 2 fp
                    (rnd_of_mode RoundingMode.RNE)
                    (B754_to_R raw +
                      B754_to_R (B754.B754_finite false my ey))|
                  (FloatSpec.Core.Raux.bpow 2 emax) = true := by
              simp [hltPlus]
            rw [ite_eq_right hltPlusNot] at hplusBranch
            have hrefBranch := href.2
            rw [ite_eq_right hlt] at hrefBranch
            exact hplusBranch.trans hrefBranch.symm
      | true =>
          let xopp : BinarySingleNaNFloat prec emax :=
            BinarySingleNaNFloat.B754_finite false mx ex hmx hbounded
          have hxoppPos : 0 < B754_to_R
              (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) xopp) := by
            have hmxR : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hmx
            have hpow : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) ex
            simpa [xopp, binarySingleNaNFloatToB754, B754_to_R, F2R,
              FloatSpec.Core.Defs.F2R] using mul_pos hmxR hpow
          have hpred := Bpred_pos'_correct (prec:=prec) (emax:=emax)
            hmax xopp hxoppPos
          have hpredRaw :
              Bpred_pos' (prec:=prec) (emax:=emax)
                  (B754.B754_finite false mx ex) =
                Bpred (prec:=prec) (emax:=emax)
                  (B754.B754_finite false mx ex) := by
            simpa [xopp, binarySingleNaNFloatToB754] using hpred
          change Bopp_bsn
              (Bpred_pos' (prec:=prec) (emax:=emax)
                (B754.B754_finite false mx ex)) =
            Bsucc (prec:=prec) (emax:=emax) (B754.B754_finite true mx ex)
          rw [hpredRaw]
          unfold Bpred
          have hopp : ∀ z : B754, Bopp_bsn (Bopp_bsn z) = z := by
            intro z
            cases z <;> simp [Bopp_bsn]
          exact hopp (Bsucc (prec:=prec) (emax:=emax)
            (B754.B754_finite true mx ex))

-- Coq `BinarySingleNaN.v:Bsucc_correct`, restored on the proof-carrying
-- single-NaN input.  The raw result is safe here because the input supplies
-- the constructor invariants used by the proof.
theorem Bsucc_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : BinarySingleNaNFloat prec emax)
    (hfinite : BSN_is_finite
      (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) = true) :
    let raw := binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x
    let successor := FloatSpec.Core.Ulp.succ 2
      (FLT_exp (3 - emax - prec) prec) (B754_to_R raw)
    if FloatSpec.Core.Raux.Rlt_bool successor
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B754_to_R (Bsucc (prec:=prec) (emax:=emax) raw) = successor ∧
        BSN_is_finite (Bsucc (prec:=prec) (emax:=emax) raw) = true ∧
        BSN_sign (Bsucc (prec:=prec) (emax:=emax) raw) =
          (BSN_sign raw && BSN_is_finite_strict raw)
    else
      B2SF_BSN (Bsucc (prec:=prec) (emax:=emax) raw) =
        StandardFloat.S754_infinity false := by
  cases x with
  | B754_infinity s =>
      simp [binarySingleNaNFloatToB754, BSN_is_finite] at hfinite
  | B754_nan =>
      simp [binarySingleNaNFloatToB754, BSN_is_finite] at hfinite
  | B754_zero s =>
      have hsucc0 := FloatSpec.Core.Ulp.succ_0
        (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
      have hsucc : FloatSpec.Core.Ulp.succ 2
          (FLT_exp (3 - emax - prec) prec) 0 =
          FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec) 0 := by
        simpa [wp, PostCond.noThrow, pure] using hsucc0 trivial
      have hulp0 := FloatSpec.Core.FLT.ulp_FLT_0
        (prec:=prec) (emin:=3 - emax - prec) 2
      have hulp : FloatSpec.Core.Ulp.ulp 2
          (FLT_exp (3 - emax - prec) prec) 0 =
          FloatSpec.Core.Raux.bpow 2 (3 - emax - prec) := by
        simpa [wp, PostCond.noThrow, pure, FloatSpec.Core.Raux.bpow] using
          hulp0 trivial
      have heminLt : 3 - emax - prec < emax := by
        have hp := (inferInstance : Prec_gt_0 prec).pos
        have he := (inferInstance : Prec_lt_emax prec emax).emax_ge_2
        omega
      have hpowLt : FloatSpec.Core.Raux.bpow 2 (3 - emax - prec) <
          FloatSpec.Core.Raux.bpow 2 emax := by
        have htrip := FloatSpec.Core.Raux.bpow_lt 2 _ _ (by norm_num) heminLt
        have h := htrip trivial
        simpa [FloatSpec.Core.Raux.bpow_lt_check,
          FloatSpec.Core.Raux.bpow, wp, PostCond.noThrow, Id.run, pure] using h
      simp [binarySingleNaNFloatToB754, B754_to_R, hsucc, hulp,
        FloatSpec.Core.Raux.Rlt_bool, hpowLt, Bsucc, B2SF_BSN,
        BSN_is_finite, BSN_is_finite_strict, BSN_sign,
        FloatSpec.Core.Raux.bpow, F2R, FloatSpec.Core.Defs.F2R, heminLt]
  | B754_finite s mx ex hmx hbounded =>
      cases s with
      | false =>
          let raw := B754.B754_finite false mx ex
          let successor := FloatSpec.Core.Ulp.succ 2
            (FLT_exp (3 - emax - prec) prec) (B754_to_R raw)
          have href := Bsucc_positive_correct (prec:=prec) (emax:=emax)
            mx ex hmx hbounded
          dsimp only at href
          have hmxR : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hmx
          have hpow : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) ex
          have hrawPos : 0 < B754_to_R raw := by
            simpa [raw, B754_to_R, F2R, FloatSpec.Core.Defs.F2R] using
              mul_pos hmxR hpow
          have hsuccTrip := FloatSpec.Core.Ulp.succ_eq_pos
            (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
            (B754_to_R raw) (le_of_lt hrawPos)
          have hsuccEq : successor = B754_to_R raw +
              FloatSpec.Core.Ulp.ulp 2 (FLT_exp (3 - emax - prec) prec)
                (B754_to_R raw) := by
            simpa [successor, wp, PostCond.noThrow, pure] using hsuccTrip trivial
          have hulpPos : 0 < FloatSpec.Core.Ulp.ulp 2
              (FLT_exp (3 - emax - prec) prec) (B754_to_R raw) := by
            simp [FloatSpec.Core.Ulp.ulp, ne_of_gt hrawPos,
              zpow_pos (by norm_num : (0 : ℝ) < 2)]
          have hsuccPos : 0 < successor := by rw [hsuccEq]; positivity
          change if FloatSpec.Core.Raux.Rlt_bool successor
              (FloatSpec.Core.Raux.bpow 2 emax) then
            B754_to_R (Bsucc (prec:=prec) (emax:=emax) raw) = successor ∧
              BSN_is_finite (Bsucc (prec:=prec) (emax:=emax) raw) = true ∧
              BSN_sign (Bsucc (prec:=prec) (emax:=emax) raw) = false
          else B2SF_BSN (Bsucc (prec:=prec) (emax:=emax) raw) =
            StandardFloat.S754_infinity false
          by_cases hlt : FloatSpec.Core.Raux.Rlt_bool successor
              (FloatSpec.Core.Raux.bpow 2 emax) = true
          · rw [ite_eq_left hlt]
            have habs : |successor| = successor := abs_of_pos hsuccPos
            have hpayload := href.2
            have habsRaw :
                |FloatSpec.Core.Ulp.succ 2
                    (FLT_exp (3 - emax - prec) prec) (B754_to_R raw)| =
                  FloatSpec.Core.Ulp.succ 2
                    (FLT_exp (3 - emax - prec) prec) (B754_to_R raw) := by
              simpa [successor] using habs
            have hltAbs : FloatSpec.Core.Raux.Rlt_bool
                |FloatSpec.Core.Ulp.succ 2
                    (FLT_exp (3 - emax - prec) prec) (B754_to_R raw)|
                (FloatSpec.Core.Raux.bpow 2 emax) = true := by
              rw [habsRaw]
              simpa [successor] using hlt
            rw [ite_eq_left hltAbs] at hpayload
            simpa [raw, successor, binarySingleNaNFloatToB754,
              BSN_sign, BSN_is_finite_strict] using hpayload
          · rw [ite_eq_right hlt]
            have habs : |successor| = successor := abs_of_pos hsuccPos
            have hpayload := href.2
            have habsRaw :
                |FloatSpec.Core.Ulp.succ 2
                    (FLT_exp (3 - emax - prec) prec) (B754_to_R raw)| =
                  FloatSpec.Core.Ulp.succ 2
                    (FLT_exp (3 - emax - prec) prec) (B754_to_R raw) := by
              simpa [successor] using habs
            have hltAbs : ¬ FloatSpec.Core.Raux.Rlt_bool
                |FloatSpec.Core.Ulp.succ 2
                    (FLT_exp (3 - emax - prec) prec) (B754_to_R raw)|
                (FloatSpec.Core.Raux.bpow 2 emax) = true := by
              rw [habsRaw]
              simpa [successor] using hlt
            rw [ite_eq_right hltAbs] at hpayload
            rw [show Bsucc (prec:=prec) (emax:=emax) raw =
                B754.B754_infinity false by simpa [raw, successor] using hpayload]
            rfl
      | true =>
          let pos := B754.B754_finite false mx ex
          let neg := B754.B754_finite true mx ex
          let pred := Bpred (prec:=prec) (emax:=emax) pos
          let successor := FloatSpec.Core.Ulp.succ 2
            (FLT_exp (3 - emax - prec) prec) (B754_to_R neg)
          have href := Bpred_positive_correct (prec:=prec) (emax:=emax)
            mx ex hmx hbounded
          dsimp only at href
          have hr : Bsucc (prec:=prec) (emax:=emax) neg = Bopp_bsn pred := by
            unfold pred Bpred
            change Bsucc (prec:=prec) (emax:=emax) neg =
              Bopp_bsn (Bopp_bsn (Bsucc (prec:=prec) (emax:=emax) neg))
            cases Bsucc (prec:=prec) (emax:=emax) neg <;> simp [Bopp_bsn]
          have hf : BSN_is_finite pred = true := by
            simpa [pred, pos] using href.2.2.1
          have hs : BSN_sign pred = false := by
            simpa [pred, pos] using href.2.2.2
          have hpredValue : B754_to_R pred =
              FloatSpec.Core.Ulp.pred_pos 2
                (FLT_exp (3 - emax - prec) prec) (B754_to_R pos) := by
            simpa [pred, pos] using href.2.1
          have hpredNonneg : 0 ≤ B754_to_R pred := by
            cases hp : pred with
            | B754_zero sp => simp [hp, B754_to_R]
            | B754_infinity sp =>
                rw [hp] at hf
                simp [BSN_is_finite] at hf
            | B754_nan =>
                rw [hp] at hf
                simp [BSN_is_finite] at hf
            | B754_finite sp mp ep =>
                have hsp : sp = false := by
                  rw [hp] at hs
                  simpa [BSN_sign] using hs
                subst sp
                simp [hp, B754_to_R, F2R, FloatSpec.Core.Defs.F2R]
                positivity
          have hvalueOpp : B754_to_R (Bopp_bsn pred) = -B754_to_R pred := by
            cases pred with
            | B754_zero sp => simp [Bopp_bsn, B754_to_R]
            | B754_infinity sp => simp [Bopp_bsn, B754_to_R]
            | B754_nan => simp [Bopp_bsn, B754_to_R]
            | B754_finite sp mp ep =>
                cases sp <;> simp [Bopp_bsn, B754_to_R, F2R,
                  FloatSpec.Core.Defs.F2R] <;> ring
          have hfiniteOpp : BSN_is_finite (Bopp_bsn pred) = true := by
            have heq : BSN_is_finite (Bopp_bsn pred) =
                BSN_is_finite pred := by
              cases pred <;> rfl
            rw [heq, hf]
          have hsignOpp : BSN_sign (Bopp_bsn pred) = true := by
            cases hp : pred with
            | B754_zero sp =>
                rw [hp] at hs
                have hsp : sp = false := by simpa [BSN_sign] using hs
                subst sp
                rfl
            | B754_infinity sp =>
                rw [hp] at hf
                simp [BSN_is_finite] at hf
            | B754_nan =>
                rw [hp] at hf
                simp [BSN_is_finite] at hf
            | B754_finite sp mp ep =>
                rw [hp] at hs
                have hsp : sp = false := by simpa [BSN_sign] using hs
                subst sp
                rfl
          have hnegValue : B754_to_R neg = -B754_to_R pos := by
            simp [neg, pos, B754_to_R, F2R, FloatSpec.Core.Defs.F2R]
          have hsuccOpp := FloatSpec.Core.Ulp.succ_opp
            (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
            (B754_to_R pos)
          have hsuccValue : successor = -FloatSpec.Core.Ulp.pred 2
              (FLT_exp (3 - emax - prec) prec) (B754_to_R pos) := by
            simpa [successor, hnegValue, wp, PostCond.noThrow, pure] using
              hsuccOpp trivial
          have hposValue : 0 < B754_to_R pos := by
            have hp : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hmx
            have he : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) ex
            simpa [pos, B754_to_R, F2R, FloatSpec.Core.Defs.F2R] using mul_pos hp he
          have hpredEq := FloatSpec.Core.Ulp.pred_eq_pos
            (beta:=2) (fexp:=FLT_exp (3 - emax - prec) prec)
            (B754_to_R pos) (le_of_lt hposValue)
          have hpredEq' : FloatSpec.Core.Ulp.pred 2
              (FLT_exp (3 - emax - prec) prec) (B754_to_R pos) =
              FloatSpec.Core.Ulp.pred_pos 2
                (FLT_exp (3 - emax - prec) prec) (B754_to_R pos) := by
            simpa [wp, PostCond.noThrow, pure] using hpredEq (by norm_num)
          have hsuccessorValue : B754_to_R (Bsucc
              (prec:=prec) (emax:=emax) neg) = successor := by
            rw [hr, hvalueOpp, hpredValue, hsuccValue, hpredEq']
          have hsuccNonpos : successor ≤ 0 := by
            rw [hsuccValue, hpredEq', ← hpredValue]
            exact neg_nonpos.mpr hpredNonneg
          have hbpowPos : 0 < FloatSpec.Core.Raux.bpow 2 emax :=
            by
              have h := FloatSpec.Core.Raux.bpow_gt_0 2 emax (by norm_num)
              simpa [wp, PostCond.noThrow, pure] using h trivial
          have hlt : FloatSpec.Core.Raux.Rlt_bool successor
              (FloatSpec.Core.Raux.bpow 2 emax) = true := by
            simp [FloatSpec.Core.Raux.Rlt_bool, lt_of_le_of_lt hsuccNonpos hbpowPos]
          change if FloatSpec.Core.Raux.Rlt_bool successor
              (FloatSpec.Core.Raux.bpow 2 emax) then
            B754_to_R (Bsucc (prec:=prec) (emax:=emax) neg) = successor ∧
              BSN_is_finite (Bsucc (prec:=prec) (emax:=emax) neg) = true ∧
              BSN_sign (Bsucc (prec:=prec) (emax:=emax) neg) = true
          else B2SF_BSN (Bsucc (prec:=prec) (emax:=emax) neg) =
            StandardFloat.S754_infinity false
          rw [ite_eq_left hlt]
          exact ⟨hsuccessorValue,
            by rw [hr]; exact hfiniteOpp,
            by rw [hr]; exact hsignOpp⟩

-- Coq `BinarySingleNaN.v:Bpred_correct`, derived as in the source from
-- `Bsucc_correct` and `Bpred x = Bopp (Bsucc (Bopp x))`.
theorem Bpred_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : BinarySingleNaNFloat prec emax)
    (hfinite : BSN_is_finite
      (binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x) = true) :
    let raw := binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x
    let predecessor := FloatSpec.Core.Ulp.pred 2
      (FLT_exp (3 - emax - prec) prec) (B754_to_R raw)
    if FloatSpec.Core.Raux.Rlt_bool
        (-FloatSpec.Core.Raux.bpow 2 emax) predecessor then
      B754_to_R (Bpred (prec:=prec) (emax:=emax) raw) = predecessor ∧
        BSN_is_finite (Bpred (prec:=prec) (emax:=emax) raw) = true ∧
        BSN_sign (Bpred (prec:=prec) (emax:=emax) raw) =
          (BSN_sign raw || !BSN_is_finite_strict raw)
    else
      B2SF_BSN (Bpred (prec:=prec) (emax:=emax) raw) =
        StandardFloat.S754_infinity true := by
  let raw := binarySingleNaNFloatToB754 (prec:=prec) (emax:=emax) x
  let ox : BinarySingleNaNFloat prec emax :=
    match x with
    | BinarySingleNaNFloat.B754_zero s =>
        BinarySingleNaNFloat.B754_zero (!s)
    | BinarySingleNaNFloat.B754_infinity s =>
        BinarySingleNaNFloat.B754_infinity (!s)
    | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
    | BinarySingleNaNFloat.B754_finite s m e hm hb =>
        BinarySingleNaNFloat.B754_finite (!s) m e hm hb
  let oraw := binarySingleNaNFloatToB754
    (prec:=prec) (emax:=emax) ox
  let successor := FloatSpec.Core.Ulp.succ 2
    (FLT_exp (3 - emax - prec) prec) (B754_to_R oraw)
  let predecessor := FloatSpec.Core.Ulp.pred 2
    (FLT_exp (3 - emax - prec) prec) (B754_to_R raw)
  have horaw : oraw = Bopp_bsn raw := by
    cases x <;> rfl
  have horawValue : B754_to_R oraw = -B754_to_R raw := by
    rw [horaw]
    cases raw with
    | B754_zero s => simp [Bopp_bsn, B754_to_R]
    | B754_infinity s => simp [Bopp_bsn, B754_to_R]
    | B754_nan => simp [Bopp_bsn, B754_to_R]
    | B754_finite s m e =>
        cases s <;>
          simp [Bopp_bsn, B754_to_R, F2R, FloatSpec.Core.Defs.F2R]
  have hfiniteRaw : BSN_is_finite raw = true := by
    simpa [raw] using hfinite
  have hfiniteOpp : BSN_is_finite oraw = true := by
    rw [horaw]
    have hpreserve : BSN_is_finite (Bopp_bsn raw) =
        BSN_is_finite raw := by
      cases raw <;> rfl
    rw [hpreserve, hfiniteRaw]
  have href := Bsucc_correct (prec:=prec) (emax:=emax) ox hfiniteOpp
  have hpredEq : predecessor = -successor := by
    simp [predecessor, successor, FloatSpec.Core.Ulp.pred, horawValue]
  have hcondEq : FloatSpec.Core.Raux.Rlt_bool
      (-FloatSpec.Core.Raux.bpow 2 emax) predecessor =
      FloatSpec.Core.Raux.Rlt_bool successor
        (FloatSpec.Core.Raux.bpow 2 emax) := by
    simp [hpredEq, FloatSpec.Core.Raux.Rlt_bool]
  have hpredRaw : Bpred (prec:=prec) (emax:=emax) raw =
      Bopp_bsn (Bsucc (prec:=prec) (emax:=emax) oraw) := by
    simp [Bpred, horaw]
  have hvalueOpp (z : B754) : B754_to_R (Bopp_bsn z) = -B754_to_R z := by
    cases z with
    | B754_zero s => simp [Bopp_bsn, B754_to_R]
    | B754_infinity s => simp [Bopp_bsn, B754_to_R]
    | B754_nan => simp [Bopp_bsn, B754_to_R]
    | B754_finite s m e =>
        cases s <;>
          simp [Bopp_bsn, B754_to_R, F2R, FloatSpec.Core.Defs.F2R]
  have hfiniteOpp' (z : B754) :
      BSN_is_finite (Bopp_bsn z) = BSN_is_finite z := by
    cases z <;> rfl
  have hstrictOpp (z : B754) :
      BSN_is_finite_strict (Bopp_bsn z) = BSN_is_finite_strict z := by
    cases z <;> rfl
  have hstrictInput : BSN_is_finite_strict oraw =
      BSN_is_finite_strict raw := by
    rw [horaw, hstrictOpp]
  have hsignInput : BSN_sign oraw = !BSN_sign raw := by
    rw [horaw]
    cases hr : raw with
    | B754_zero s => simp [hr, Bopp_bsn, BSN_sign]
    | B754_infinity s => simp [hr, Bopp_bsn, BSN_sign]
    | B754_nan =>
        rw [hr] at hfiniteRaw
        simp [BSN_is_finite] at hfiniteRaw
    | B754_finite s m e => simp [hr, Bopp_bsn, BSN_sign]
  dsimp only at href ⊢
  rw [hcondEq]
  by_cases hlt : FloatSpec.Core.Raux.Rlt_bool successor
      (FloatSpec.Core.Raux.bpow 2 emax) = true
  · rw [ite_eq_left hlt]
    rw [ite_eq_left hlt] at href
    rcases href with ⟨hvalue, hfiniteResult, hsignResult⟩
    have hsignOppResult : BSN_sign
        (Bopp_bsn (Bsucc (prec:=prec) (emax:=emax) oraw)) =
        !BSN_sign (Bsucc (prec:=prec) (emax:=emax) oraw) := by
      cases hz : Bsucc (prec:=prec) (emax:=emax) oraw with
      | B754_zero s => simp [hz, Bopp_bsn, BSN_sign]
      | B754_infinity s =>
          rw [hz] at hfiniteResult
          simp [BSN_is_finite] at hfiniteResult
      | B754_nan =>
          rw [hz] at hfiniteResult
          simp [BSN_is_finite] at hfiniteResult
      | B754_finite s m e => simp [hz, Bopp_bsn, BSN_sign]
    constructor
    · rw [hpredRaw, hvalueOpp, hvalue]
      simpa [predecessor, successor] using hpredEq.symm
    constructor
    · rw [hpredRaw, hfiniteOpp', hfiniteResult]
    · rw [hpredRaw, hsignOppResult, hsignResult, hsignInput,
        hstrictInput]
      simpa [raw]
  · rw [ite_eq_right hlt]
    rw [ite_eq_right hlt] at href
    rw [hpredRaw]
    cases hz : Bsucc (prec:=prec) (emax:=emax) oraw with
    | B754_zero s =>
        rw [hz] at href
        simp [B2SF_BSN] at href
    | B754_infinity s =>
        rw [hz] at href
        have hs : s = false := by simpa [B2SF_BSN] using href
        subst s
        rfl
    | B754_nan =>
        rw [hz] at href
        simp [B2SF_BSN] at href
    | B754_finite s m e =>
        rw [hz] at href
        simp [B2SF_BSN] at href

end ExperimentalSingleNaNArithmetic

namespace Binary

theorem BoppSingle_toB754 {prec emax : Int}
    (x : BinarySingleNaNFloat prec emax) :
    binarySingleNaNFloatToB754 (BoppSingle x) =
      ExperimentalSingleNaNArithmetic.Bopp_bsn
        (binarySingleNaNFloatToB754 x) := by
  cases x <;> rfl

theorem BsuccSingle_toB754 {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : BinarySingleNaNFloat prec emax) :
    binarySingleNaNFloatToB754 (BsuccSingle x) =
      ExperimentalSingleNaNArithmetic.Bsucc (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 x) := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => cases s <;> rfl
  | B754_nan => rfl
  | B754_finite s m e hm hbounded =>
      cases s with
      | false =>
          let z := _root_.binary_round (prec:=prec) (emax:=emax)
            RoundingMode.RTP false (m + 1) e
          have hc := _root_.binary_round_correct (prec:=prec) (emax:=emax)
            RoundingMode.RTP false (m + 1) e (by omega)
          simpa [BsuccSingle, ExperimentalSingleNaNArithmetic.Bsucc, z,
            binarySingleNaNFloatToB754] using
            binarySingleNaNFloatToB754_standardFloatToBinarySingleNaNFloat
              z hc.1
      | true =>
          let m' := 2 * m - 1
          have hm' : 0 < m' := by omega
          let z := _root_.binary_round (prec:=prec) (emax:=emax)
            RoundingMode.RTZ true m' (e - 1)
          have hc := _root_.binary_round_correct (prec:=prec) (emax:=emax)
            RoundingMode.RTZ true m' (e - 1) hm'
          simpa [BsuccSingle, ExperimentalSingleNaNArithmetic.Bsucc, m', z,
            binarySingleNaNFloatToB754] using
            binarySingleNaNFloatToB754_standardFloatToBinarySingleNaNFloat
              z hc.1

theorem BpredSingle_toB754 {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : BinarySingleNaNFloat prec emax) :
    binarySingleNaNFloatToB754 (BpredSingle x) =
      ExperimentalSingleNaNArithmetic.Bpred (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 x) := by
  simp only [BpredSingle, ExperimentalSingleNaNArithmetic.Bpred,
    BoppSingle_toB754, BsuccSingle_toB754]

private theorem B2FF_exact_eq_infinity_of_BSN_view {prec emax : Int}
    (x : binary_float prec emax) (s : Bool)
    (h : binarySingleNaNFloatToStandardFloat (B2BSN x) =
      StandardFloat.S754_infinity s) :
    B2FF_exact x = full_float.F754_infinity s := by
  cases x <;> simp [B2BSN, binaryFloatToBinarySingleNaNFloat,
    binarySingleNaNFloatToStandardFloat, B2FF_exact,
    binaryFloatToFullFloat] at h ⊢ <;> assumption

-- Exact Positive-payload embedding used by FLoCq's `Binary.SF2FF` surface.
-- The zero-mantissa arm is outside the source `standard_float` carrier; all
-- source-facing correctness theorems establish validity before observing it.
def SF2FF_exact (x : StandardFloat) : full_float :=
  match x with
  | StandardFloat.S754_zero s => full_float.F754_zero s
  | StandardFloat.S754_infinity s => full_float.F754_infinity s
  | StandardFloat.S754_nan =>
      full_float.F754_nan false FloatSpec.Core.Zaux.Positive.xH
  | StandardFloat.S754_finite s m e =>
      if hm : 0 < m then
        full_float.F754_finite s (binaryPositiveOfNat m hm) e
      else
        full_float.F754_finite s FloatSpec.Core.Zaux.Positive.xH e

theorem B2FF_BSN2B' {prec emax : Int} (x : BinarySingleNaNFloat prec emax)
    (hx : is_nan_BSN x = false) :
    B2FF_exact (BSN2B' x hx) =
      SF2FF_exact (binarySingleNaNFloatToStandardFloat x) := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => simp [is_nan_BSN] at hx
  | B754_finite s m e hm hb =>
      simp [BSN2B', B2FF_exact, binaryFloatToFullFloat, SF2FF_exact,
        binarySingleNaNFloatToStandardFloat, hm, binaryPositiveOfNat_spec]

abbrev valid_binary {prec emax : Int} (x : full_float) : Bool :=
  valid_full_float_binary (prec:=prec) (emax:=emax) x

private theorem valid_binary_SF2FF_exact {prec emax : Int}
    [Prec_gt_0 prec]
    (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true)
    (hnotnan : is_nan_SF x = false) :
    valid_binary (prec:=prec) (emax:=emax) (SF2FF_exact x) = true := by
  cases x with
  | S754_zero s => rfl
  | S754_infinity s => rfl
  | S754_nan => simp [is_nan_SF] at hnotnan
  | S754_finite s m e =>
      have hparts : decide (0 < m) = true ∧
          specFloat_bounded (prec:=prec) (emax:=emax) m e = true := by
        simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hx
      have hp : 0 < m := of_decide_eq_true hparts.1
      have hb : specFloat_bounded (prec:=prec) (emax:=emax) m e = true :=
        hparts.2
      simp [SF2FF_exact, hp, valid_binary, valid_full_float_binary,
        binaryPositiveOfNat_spec, hb]

private theorem SF2FF_exact_toReal {prec emax : Int}
    (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true) :
    full_float.toReal 2 (SF2FF_exact x) = SF2R 2 x := by
  cases x with
  | S754_zero s => rfl
  | S754_infinity s => rfl
  | S754_nan => rfl
  | S754_finite s m e =>
      have hp : 0 < m := by
        have hparts : decide (0 < m) = true ∧
            specFloat_bounded (prec:=prec) (emax:=emax) m e = true := by
          simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hx
        exact of_decide_eq_true hparts.1
      cases s <;> simp [SF2FF_exact, hp, full_float.toReal, SF2R,
        F2R, FloatSpec.Core.Defs.F2R, binaryPositiveOfNat_spec]

private theorem SF2FF_exact_isFinite (x : StandardFloat) :
    full_float.isFinite (SF2FF_exact x) = is_finite_SF x := by
  cases x with
  | S754_zero s => rfl
  | S754_infinity s => rfl
  | S754_nan => rfl
  | S754_finite s m e =>
      by_cases hm : 0 < m <;>
        simp [SF2FF_exact, hm, full_float.isFinite, is_finite_SF]

private theorem SF2FF_exact_sign (x : StandardFloat) :
    full_float.sign (SF2FF_exact x) = sign_SF x := by
  cases x with
  | S754_zero s => rfl
  | S754_infinity s => rfl
  | S754_nan => rfl
  | S754_finite s m e =>
      by_cases hm : 0 < m <;>
        simp [SF2FF_exact, hm, full_float.sign, sign_SF]

private theorem B2FF_exact_standardFloatToBinaryFloatOfNotNaN
    {prec emax : Int} (x : StandardFloat)
    (hvalid : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) x = true)
    (hnotnan : is_nan_SF x = false) :
    B2FF_exact (standardFloatToBinaryFloatOfNotNaN
      (prec:=prec) (emax:=emax) x hvalid hnotnan) = SF2FF_exact x := by
  cases x with
  | S754_zero s => rfl
  | S754_infinity s => rfl
  | S754_nan => simp [is_nan_SF] at hnotnan
  | S754_finite s m e =>
      have hparts : decide (0 < m) = true ∧
          specFloat_bounded (prec:=prec) (emax:=emax) m e = true := by
        simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hvalid
      have hm : 0 < m := of_decide_eq_true hparts.1
      simp [standardFloatToBinaryFloatOfNotNaN, B2FF_exact,
        binaryFloatToFullFloat, SF2FF_exact, hm, binaryPositiveOfNat_spec]

-- Exact FLoCq full-float image of the SingleNaN overflow algorithm.
def binary_overflow_exact {prec emax : Int}
    (mode : RoundingMode) (s : Bool) : full_float :=
  SF2FF_exact (bsn_binary_overflow (prec:=prec) (emax:=emax) mode s)

theorem binary_overflow_eq_exact_embedding {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (s : Bool) :
    full_float.toFullFloat (binary_overflow_exact
      (prec:=prec) (emax:=emax) mode s) =
      binary_overflow (prec:=prec) (emax:=emax) mode s := by
  have hprec : 0 < prec := (inferInstance : Prec_gt_0 prec).pos
  have hm := maxFloatMantissa_pos (prec:=prec)
  cases mode <;> cases s <;>
    simp [binary_overflow_exact, binary_overflow, SF2FF_exact,
      bsn_binary_overflow, overflow_to_inf, full_float.toFullFloat,
      _root_.SF2FF, hprec, hm, binaryPositiveOfNat_spec]

theorem eq_binary_overflow_FF2SF {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : full_float) (mode : RoundingMode) (s : Bool)
    (hx : full_float.toStandardFloat x =
      bsn_binary_overflow (prec:=prec) (emax:=emax) mode s) :
    x = binary_overflow_exact (prec:=prec) (emax:=emax) mode s := by
  have hprec : 0 < prec := (inferInstance : Prec_gt_0 prec).pos
  have hm := maxFloatMantissa_pos (prec:=prec)
  cases mode <;> cases s <;> cases x <;>
    simp [full_float.toStandardFloat, bsn_binary_overflow,
      overflow_to_inf, binary_overflow_exact, SF2FF_exact,
      hprec, hm] at hx ⊢ <;>
    simp_all
  all_goals
    apply FloatSpec.Core.Zaux.positiveToNat_injective
    rw [binaryPositiveOfNat_spec]
    exact hx.2.1

private theorem is_nan_bsn_binary_overflow_false {prec emax : Int}
    (mode : RoundingMode) (s : Bool) :
    is_nan_SF (bsn_binary_overflow (prec:=prec) (emax:=emax) mode s) = false := by
  unfold bsn_binary_overflow
  cases mode <;> cases s <;> simp [overflow_to_inf, is_nan_SF]

-- Coq `Binary.v:binary_round_aux` on the exact full-float carrier.
noncomputable def binary_round_aux {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (sx : Bool) (mx ex : Int) (lx : Loc) : full_float :=
  SF2FF_exact (_root_.binary_round_aux (prec:=prec) (emax:=emax)
    mode sx mx ex lx)

-- Coq `Binary.v:binary_round`; the source mantissa is Positive.
noncomputable def binary_round {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (sx : Bool)
    (mx : FloatSpec.Core.Zaux.Positive) (ex : Int) : full_float :=
  SF2FF_exact (_root_.binary_round (prec:=prec) (emax:=emax) mode sx
    (FloatSpec.Core.Zaux.positiveToNat mx) ex)

-- Coq `Binary.v:binary_normalize`, constructing the proof-carrying result
-- directly from the already-verified SingleNaN rounding result.
noncomputable def binary_normalize {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (m e : Int) (szero : Bool) : binary_float prec emax :=
  if hm0 : m = 0 then binary_float.B754_zero szero
  else if hmp : 0 < m then
    let mn := m.toNat
    have hmn : 0 < mn := by omega
    let z := _root_.binary_round (prec:=prec) (emax:=emax) mode false mn e
    have hz := _root_.binary_round_correct (prec:=prec) (emax:=emax)
      mode false mn e hmn
    standardFloatToBinaryFloatOfNotNaN z hz.1
      (_root_.is_nan_binary_round (prec:=prec) (emax:=emax) mode false mn e)
  else
    let mn := m.natAbs
    have hmn : 0 < mn := Int.natAbs_pos.mpr hm0
    let z := _root_.binary_round (prec:=prec) (emax:=emax) mode true mn e
    have hz := _root_.binary_round_correct (prec:=prec) (emax:=emax)
      mode true mn e hmn
    standardFloatToBinaryFloatOfNotNaN z hz.1
      (_root_.is_nan_binary_round (prec:=prec) (emax:=emax) mode true mn e)

private theorem SF2FF_exact_correct {prec emax : Int}
    [Prec_gt_0 prec]
    (zS overflowS : StandardFloat) (cond : Bool) (value : ℝ) (sign : Bool)
    (hoverNotNaN : is_nan_SF overflowS = false)
    (hraw :
      validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) zS = true ∧
      if cond then
        SF2R 2 zS = value ∧ is_finite_SF zS = true ∧ sign_SF zS = sign
      else zS = overflowS) :
    valid_binary (prec:=prec) (emax:=emax) (SF2FF_exact zS) = true ∧
      if cond then
        full_float.toReal 2 (SF2FF_exact zS) = value ∧
          full_float.isFinite (SF2FF_exact zS) = true ∧
          full_float.sign (SF2FF_exact zS) = sign
      else SF2FF_exact zS = SF2FF_exact overflowS := by
  have hzNotNaN : is_nan_SF zS = false := by
    cases hc : cond with
    | false =>
        simp [hc] at hraw
        rw [hraw.2, hoverNotNaN]
    | true =>
        simp [hc] at hraw
        rcases hraw.2 with ⟨_, hf, _⟩
        cases hz : zS <;> simp [hz, is_finite_SF, is_nan_SF] at hf ⊢
  constructor
  · exact valid_binary_SF2FF_exact zS hraw.1 hzNotNaN
  · cases hc : cond with
    | false =>
        simp [hc]
        simp [hc] at hraw
        exact congrArg SF2FF_exact hraw.2
    | true =>
        simp [hc]
        simp [hc] at hraw
        rcases hraw.2 with ⟨hvalue, hfinite, hsign⟩
        exact ⟨(SF2FF_exact_toReal zS hraw.1).trans hvalue,
          (SF2FF_exact_isFinite zS).trans hfinite,
          (SF2FF_exact_sign zS).trans hsign⟩

-- Coq `Binary.v:binary_round_aux_correct'` on the exact full-float result.
theorem binary_round_aux_correct' {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : ℝ) (mx ex : Int) (lx : Loc)
    (hx : x ≠ 0)
    (hbetween : FloatSpec.Calc.Bracket.inbetween_float 2 mx ex |x| lx)
    (hex : ex ≤ FloatSpec.Core.Generic_fmt.cexp 2
      (FLT_exp (3 - emax - prec) prec) x) :
    let z := binary_round_aux (prec:=prec) (emax:=emax) mode
      (FloatSpec.Core.Raux.Rlt_bool x 0) mx ex lx
    valid_binary (prec:=prec) (emax:=emax) z = true ∧
      if FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        full_float.toReal 2 z = FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x ∧
          full_float.isFinite z = true ∧
          full_float.sign z = FloatSpec.Core.Raux.Rlt_bool x 0
      else
        z = binary_overflow_exact (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool x 0) := by
  have href := _root_.binary_round_aux_correct' (prec:=prec) (emax:=emax)
    mode x mx ex lx hx hbetween hex
  have hoverNotNaN := is_nan_bsn_binary_overflow_false
    (prec:=prec) (emax:=emax) mode (FloatSpec.Core.Raux.Rlt_bool x 0)
  simpa [binary_round_aux, binary_overflow_exact] using
    SF2FF_exact_correct
      (_root_.binary_round_aux (prec:=prec) (emax:=emax) mode
        (FloatSpec.Core.Raux.Rlt_bool x 0) mx ex lx)
      (bsn_binary_overflow (prec:=prec) (emax:=emax) mode
        (FloatSpec.Core.Raux.Rlt_bool x 0))
      (FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x|
        (FloatSpec.Core.Raux.bpow 2 emax))
      (FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x)
      (FloatSpec.Core.Raux.Rlt_bool x 0) hoverNotNaN href

-- Coq `Binary.v:binary_round_aux_correct`; Positive supplies the source's
-- nonzero mantissa invariant, so no target-only premise is exposed.
theorem binary_round_aux_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : ℝ)
    (mx : FloatSpec.Core.Zaux.Positive) (ex : Int) (lx : Loc)
    (hbetween : FloatSpec.Calc.Bracket.inbetween_float 2
      (FloatSpec.Core.Zaux.positiveToNat mx : Int) ex |x| lx)
    (hex : ex ≤ FLT_exp (3 - emax - prec) prec
      (FloatSpec.Core.Digits.Zdigits 2
        (FloatSpec.Core.Zaux.positiveToNat mx : Int) + ex)) :
    let z := binary_round_aux (prec:=prec) (emax:=emax) mode
      (FloatSpec.Core.Raux.Rlt_bool x 0)
      (FloatSpec.Core.Zaux.positiveToNat mx : Int) ex lx
    valid_binary (prec:=prec) (emax:=emax) z = true ∧
      if FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        full_float.toReal 2 z = FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x ∧
          full_float.isFinite z = true ∧
          full_float.sign z = FloatSpec.Core.Raux.Rlt_bool x 0
      else
        z = binary_overflow_exact (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool x 0) := by
  let mn := FloatSpec.Core.Zaux.positiveToNat mx
  have hmn : 0 < mn := positiveToNat_pos_bsn mx
  have href := _root_.binary_round_aux_correct (prec:=prec) (emax:=emax)
    mode x mn ex lx hmn hbetween hex
  have hoverNotNaN := is_nan_bsn_binary_overflow_false
    (prec:=prec) (emax:=emax) mode (FloatSpec.Core.Raux.Rlt_bool x 0)
  simpa [binary_round_aux, binary_overflow_exact, mn] using
    SF2FF_exact_correct
      (_root_.binary_round_aux (prec:=prec) (emax:=emax) mode
        (FloatSpec.Core.Raux.Rlt_bool x 0) (mn : Int) ex lx)
      (bsn_binary_overflow (prec:=prec) (emax:=emax) mode
        (FloatSpec.Core.Raux.Rlt_bool x 0))
      (FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x|
        (FloatSpec.Core.Raux.bpow 2 emax))
      (FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x)
      (FloatSpec.Core.Raux.Rlt_bool x 0) hoverNotNaN href

-- Coq `Binary.v:binary_round_correct` on Positive mantissas and exact output.
theorem binary_round_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (sx : Bool)
    (mx : FloatSpec.Core.Zaux.Positive) (ex : Int) :
    let z := binary_round (prec:=prec) (emax:=emax) mode sx mx ex
    valid_binary (prec:=prec) (emax:=emax) z = true ∧
      let x := SF2R 2 (StandardFloat.S754_finite sx
        (FloatSpec.Core.Zaux.positiveToNat mx) ex)
      if FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        full_float.toReal 2 z = FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x ∧
          full_float.isFinite z = true ∧ full_float.sign z = sx
      else z = binary_overflow_exact (prec:=prec) (emax:=emax) mode sx := by
  let mn := FloatSpec.Core.Zaux.positiveToNat mx
  let x := SF2R 2 (StandardFloat.S754_finite sx mn ex)
  have hmn : 0 < mn := positiveToNat_pos_bsn mx
  have href := _root_.binary_round_correct (prec:=prec) (emax:=emax)
    mode sx mn ex hmn
  have hoverNotNaN := is_nan_bsn_binary_overflow_false
    (prec:=prec) (emax:=emax) mode sx
  simpa [binary_round, binary_overflow_exact, mn, x] using
    SF2FF_exact_correct
      (_root_.binary_round (prec:=prec) (emax:=emax) mode sx mn ex)
      (bsn_binary_overflow (prec:=prec) (emax:=emax) mode sx)
      (FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x|
        (FloatSpec.Core.Raux.bpow 2 emax))
      (FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) x)
      sx hoverNotNaN href

noncomputable def binary_normalize_sign (x : ℝ) (szero : Bool) : Bool :=
  match FloatSpec.Core.Raux.Rcompare x 0 with
  | -1 => true
  | 0 => szero
  | _ => false

private theorem binary_normalize_sign_eq (x : ℝ) (szero : Bool) :
    binary_normalize_sign x szero =
      if x = 0 then szero else decide (x < 0) := by
  unfold binary_normalize_sign FloatSpec.Core.Raux.Rcompare
  by_cases hlt : x < 0
  · simp [hlt, ne_of_lt hlt]
  · by_cases heq : x = 0
    · simp [hlt, heq]
    · simp [hlt, heq]

private theorem binary_normalize_eq_normalize {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (m e : Int) (szero : Bool) :
    binary_normalize (prec:=prec) (emax:=emax) mode m e szero =
      normalize (prec:=prec) (emax:=emax) mode m e szero := by
  unfold binary_normalize normalize
  by_cases hm0 : m = 0
  · simp [hm0]
  · by_cases hmp : 0 < m
    · simp [hm0, hmp]
    · simp [hm0, hmp]

-- Coq `Binary.v:binary_normalize_correct` on the proof-carrying result and
-- exact Positive-payload full-float overflow view.
theorem binary_normalize_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (m e : Int) (szero : Bool) :
    let input := F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
      FloatSpec.Core.Defs.FlocqFloat 2)
    let z := binary_normalize (prec:=prec) (emax:=emax) mode m e szero
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) input|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R z = FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) input ∧
        is_finite z = true ∧
        Bsign z = binary_normalize_sign input szero
    else
      B2FF_exact z = binary_overflow_exact (prec:=prec) (emax:=emax) mode
        (FloatSpec.Core.Raux.Rlt_bool input 0) := by
  let input := F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
    FloatSpec.Core.Defs.FlocqFloat 2)
  have heq := binary_normalize_eq_normalize (prec:=prec) (emax:=emax)
    mode m e szero
  have href := normalize_correct (prec:=prec) (emax:=emax) mode m e szero
  dsimp only at href ⊢
  by_cases hlt : FloatSpec.Core.Raux.Rlt_bool
      |FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) input|
      (FloatSpec.Core.Raux.bpow 2 emax) = true
  · rw [ite_eq_left hlt]
    have hlt' : FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
              FloatSpec.Core.Defs.FlocqFloat 2))|
        (FloatSpec.Core.Raux.bpow 2 emax) = true := by
      simpa [input] using hlt
    rw [ite_eq_left hlt'] at href
    rw [heq]
    simpa [input, binary_normalize_sign_eq] using href
  · rw [ite_eq_right hlt]
    by_cases hm0 : m = 0
    · subst m
      have hb : 0 < FloatSpec.Core.Raux.bpow 2 emax :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) emax
      have hzeroRound : FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) 0 = 0 :=
        roundR_zero_of_mode (prec:=prec) (emax:=emax) mode
      exfalso
      apply hlt
      simp [input, F2R, FloatSpec.Core.Defs.F2R, hzeroRound,
        FloatSpec.Core.Raux.Rlt_bool, hb]
    · by_cases hmp : 0 < m
      · let mn := m.toNat
        have hmn : 0 < mn := by
          have hcast : (mn : Int) = m := Int.toNat_of_nonneg (le_of_lt hmp)
          omega
        let zS := _root_.binary_round (prec:=prec) (emax:=emax)
          mode false mn e
        have hraw := _root_.binary_round_correct (prec:=prec) (emax:=emax)
          mode false mn e hmn
        have hnotnan := _root_.is_nan_binary_round
          (prec:=prec) (emax:=emax) mode false mn e
        have hinput : SF2R 2 (StandardFloat.S754_finite false mn e) = input := by
          have hcast : (mn : Int) = m := Int.toNat_of_nonneg (le_of_lt hmp)
          simp [input, SF2R, hcast]
        have hltS : ¬ FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                (SF2R 2 (StandardFloat.S754_finite false mn e))|
            (FloatSpec.Core.Raux.bpow 2 emax) = true := by
          simpa [hinput] using hlt
        dsimp only at hraw
        rw [ite_eq_right hltS] at hraw
        have hnorm : binary_normalize (prec:=prec) (emax:=emax)
            mode m e szero = standardFloatToBinaryFloatOfNotNaN
              zS hraw.1 hnotnan := by
          simp [binary_normalize, hm0, hmp, mn, zS]
        rw [hnorm,
          B2FF_exact_standardFloatToBinaryFloatOfNotNaN zS hraw.1 hnotnan]
        change SF2FF_exact (_root_.binary_round (prec:=prec) (emax:=emax)
          mode false mn e) = _
        rw [hraw.2]
        have hvalue : 0 < F2R
            (FloatSpec.Core.Defs.FlocqFloat.mk m e :
              FloatSpec.Core.Defs.FlocqFloat 2) :=
          FloatSpec.Core.Float_prop.F2R_gt_0 (beta:=2)
            (f:=FloatSpec.Core.Defs.FlocqFloat.mk m e) (by norm_num) hmp
        have hvalueRaw : 0 < (m : ℝ) * (2 : ℝ) ^ e := by
          simpa [F2R, FloatSpec.Core.Defs.F2R] using hvalue
        simp [binary_overflow_exact, FloatSpec.Core.Raux.Rlt_bool,
          not_lt.mpr (le_of_lt hvalueRaw)]
      · have hmneg : m < 0 := lt_of_le_of_ne (le_of_not_gt hmp) hm0
        let mn := m.natAbs
        have hmn : 0 < mn := Int.natAbs_pos.mpr hm0
        let zS := _root_.binary_round (prec:=prec) (emax:=emax)
          mode true mn e
        have hraw := _root_.binary_round_correct (prec:=prec) (emax:=emax)
          mode true mn e hmn
        have hnotnan := _root_.is_nan_binary_round
          (prec:=prec) (emax:=emax) mode true mn e
        have hinput : SF2R 2 (StandardFloat.S754_finite true mn e) = input := by
          have hcast : (mn : Int) = -m := by
            simpa [mn, abs_of_neg hmneg] using Int.natCast_natAbs m
          simp [input, SF2R, hcast]
        have hltS : ¬ FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                (SF2R 2 (StandardFloat.S754_finite true mn e))|
            (FloatSpec.Core.Raux.bpow 2 emax) = true := by
          simpa [hinput] using hlt
        dsimp only at hraw
        rw [ite_eq_right hltS] at hraw
        have hnorm : binary_normalize (prec:=prec) (emax:=emax)
            mode m e szero = standardFloatToBinaryFloatOfNotNaN
              zS hraw.1 hnotnan := by
          simp [binary_normalize, hm0, hmp, mn, zS]
        rw [hnorm,
          B2FF_exact_standardFloatToBinaryFloatOfNotNaN zS hraw.1 hnotnan]
        change SF2FF_exact (_root_.binary_round (prec:=prec) (emax:=emax)
          mode true mn e) = _
        rw [hraw.2]
        have hvalue : F2R
            (FloatSpec.Core.Defs.FlocqFloat.mk m e :
              FloatSpec.Core.Defs.FlocqFloat 2) < 0 :=
          FloatSpec.Core.Float_prop.F2R_lt_0 (beta:=2)
            (f:=FloatSpec.Core.Defs.FlocqFloat.mk m e) (by norm_num) hmneg
        have hvalueRaw : (m : ℝ) * (2 : ℝ) ^ e < 0 := by
          simpa [F2R, FloatSpec.Core.Defs.F2R] using hvalue
        simp [binary_overflow_exact, FloatSpec.Core.Raux.Rlt_bool,
          hvalueRaw]

-- Coq `Binary.v:Bsucc_correct`, transported from the exact SingleNaN theorem
-- while retaining the proof-carrying source carrier and exact FullFloat view.
theorem Bsucc_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) (hfinite : is_finite x = true) :
    if FloatSpec.Core.Raux.Rlt_bool
        (FloatSpec.Core.Ulp.succ 2 (FLT_exp (3 - emax - prec) prec) (B2R x))
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (Bsucc x) = FloatSpec.Core.Ulp.succ 2
          (FLT_exp (3 - emax - prec) prec) (B2R x) ∧
        is_finite (Bsucc x) = true ∧
        Bsign (Bsucc x) = (Bsign x && is_finite_strict x)
    else
      B2FF_exact (Bsucc x) = full_float.F754_infinity false := by
  have hxNotNaN : is_nan x = false := by
    cases x <;> simp [is_finite, is_nan] at hfinite ⊢
  have hrawFinite : BSN_is_finite
      (binarySingleNaNFloatToB754 (B2BSN x)) = true := by
    rw [is_finite_B2BSN]
    exact hfinite
  have href := ExperimentalSingleNaNArithmetic.Bsucc_correct
    (prec:=prec) (emax:=emax) (B2BSN x) hrawFinite
  have hview : B2BSN (Bsucc x) = BsuccSingle (B2BSN x) := by
    unfold Bsucc
    apply B2BSN_lift
  have hrawResult : binarySingleNaNFloatToB754 (B2BSN (Bsucc x)) =
      ExperimentalSingleNaNArithmetic.Bsucc (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (B2BSN x)) := by
    rw [hview]
    exact BsuccSingle_toB754 (B2BSN x)
  rw [← B2R_B2BSN x]
  dsimp only at href ⊢
  by_cases hlt : FloatSpec.Core.Raux.Rlt_bool
      (FloatSpec.Core.Ulp.succ 2 (FLT_exp (3 - emax - prec) prec)
        (B754_to_R (binarySingleNaNFloatToB754 (B2BSN x))))
      (FloatSpec.Core.Raux.bpow 2 emax) = true
  · rw [ite_eq_left hlt]
    rw [ite_eq_left hlt] at href
    rcases href with ⟨hvalue, hfiniteResult, hsignResult⟩
    have hresultFinite : is_finite (Bsucc x) = true := by
      rw [← is_finite_B2BSN (Bsucc x), hrawResult]
      exact hfiniteResult
    have hresultNotNaN : is_nan (Bsucc x) = false := by
      cases hz : Bsucc x <;>
        simp [hz, is_finite, is_nan] at hresultFinite ⊢
    constructor
    · rw [← B2R_B2BSN (Bsucc x), hrawResult]
      exact hvalue
    constructor
    · exact hresultFinite
    · rw [← Bsign_B2BSN (Bsucc x) hresultNotNaN, hrawResult,
        hsignResult, Bsign_B2BSN x hxNotNaN,
        is_finite_strict_B2BSN]
  · rw [ite_eq_right hlt]
    rw [ite_eq_right hlt] at href
    apply B2FF_exact_eq_infinity_of_BSN_view (Bsucc x) false
    rw [← B2SF_BSN_binarySingleNaNFloatToB754, hrawResult]
    exact href

-- Coq `Binary.v:Bpred_correct`, transported without weakening its sign or
-- negative-overflow postconditions.
theorem Bpred_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (x : binary_float prec emax) (hfinite : is_finite x = true) :
    if FloatSpec.Core.Raux.Rlt_bool
        (-FloatSpec.Core.Raux.bpow 2 emax)
        (FloatSpec.Core.Ulp.pred 2 (FLT_exp (3 - emax - prec) prec) (B2R x))
    then
      B2R (Bpred x) = FloatSpec.Core.Ulp.pred 2
          (FLT_exp (3 - emax - prec) prec) (B2R x) ∧
        is_finite (Bpred x) = true ∧
        Bsign (Bpred x) = (Bsign x || !is_finite_strict x)
    else
      B2FF_exact (Bpred x) = full_float.F754_infinity true := by
  have hxNotNaN : is_nan x = false := by
    cases x <;> simp [is_finite, is_nan] at hfinite ⊢
  have hrawFinite : BSN_is_finite
      (binarySingleNaNFloatToB754 (B2BSN x)) = true := by
    rw [is_finite_B2BSN]
    exact hfinite
  have href := ExperimentalSingleNaNArithmetic.Bpred_correct
    (prec:=prec) (emax:=emax) (B2BSN x) hrawFinite
  have hview : B2BSN (Bpred x) = BpredSingle (B2BSN x) := by
    unfold Bpred
    apply B2BSN_lift
  have hrawResult : binarySingleNaNFloatToB754 (B2BSN (Bpred x)) =
      ExperimentalSingleNaNArithmetic.Bpred (prec:=prec) (emax:=emax)
        (binarySingleNaNFloatToB754 (B2BSN x)) := by
    rw [hview]
    exact BpredSingle_toB754 (B2BSN x)
  rw [← B2R_B2BSN x]
  dsimp only at href ⊢
  by_cases hlt : FloatSpec.Core.Raux.Rlt_bool
      (-FloatSpec.Core.Raux.bpow 2 emax)
      (FloatSpec.Core.Ulp.pred 2 (FLT_exp (3 - emax - prec) prec)
        (B754_to_R (binarySingleNaNFloatToB754 (B2BSN x)))) = true
  · rw [ite_eq_left hlt]
    rw [ite_eq_left hlt] at href
    rcases href with ⟨hvalue, hfiniteResult, hsignResult⟩
    have hresultFinite : is_finite (Bpred x) = true := by
      rw [← is_finite_B2BSN (Bpred x), hrawResult]
      exact hfiniteResult
    have hresultNotNaN : is_nan (Bpred x) = false := by
      cases hz : Bpred x <;>
        simp [hz, is_finite, is_nan] at hresultFinite ⊢
    constructor
    · rw [← B2R_B2BSN (Bpred x), hrawResult]
      exact hvalue
    constructor
    · exact hresultFinite
    · rw [← Bsign_B2BSN (Bpred x) hresultNotNaN, hrawResult,
        hsignResult, Bsign_B2BSN x hxNotNaN,
        is_finite_strict_B2BSN]
  · rw [ite_eq_right hlt]
    rw [ite_eq_right hlt] at href
    apply B2FF_exact_eq_infinity_of_BSN_view (Bpred x) true
    rw [← B2SF_BSN_binarySingleNaNFloatToB754, hrawResult]
    exact href

end Binary

namespace BinarySingleNaN

@[simp] theorem B2R_SF2B {prec emax : Int} (z : StandardFloat)
    (hz : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true) :
    B2R (SF2B z hz) = SF2R 2 z := by
  cases z <;> rfl

@[simp] theorem is_finite_SF2B {prec emax : Int} (z : StandardFloat)
    (hz : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true) :
    is_finite (SF2B z hz) = is_finite_SF z := by
  cases z <;> rfl

@[simp] theorem is_nan_SF2B {prec emax : Int} (z : StandardFloat)
    (hz : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true) :
    is_nan (SF2B z hz) = is_nan_SF z := by
  cases z <;> rfl

@[simp] theorem B2SF_SF2B {prec emax : Int} (z : StandardFloat)
    (hz : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true) :
    B2SF (SF2B z hz) = z :=
  binarySingleNaNFloatToStandardFloat_standardFloatToBinarySingleNaNFloat z hz

theorem Bsign_SF2B {prec emax : Int} (z : StandardFloat)
    (hz : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true) :
    Bsign (SF2B z hz) = sign_SF z := by
  cases z <;> rfl

@[simp] theorem Bopp_involutive {prec emax : Int}
    (x : binary_float prec emax) : Bopp (Bopp x) = x := by
  cases x <;> simp [Bopp]

@[simp] theorem B2R_Bopp {prec emax : Int} (x : binary_float prec emax) :
    B2R (Bopp x) = -B2R x := by
  cases x with
  | B754_zero s =>
      simp [Bopp, B2R, binarySingleNaNFloatToB754, B754_to_R]
  | B754_infinity s =>
      simp [Bopp, B2R, binarySingleNaNFloatToB754, B754_to_R]
  | B754_nan =>
      simp [Bopp, B2R, binarySingleNaNFloatToB754, B754_to_R]
  | B754_finite s m e hm hb =>
      cases s <;>
        simp [Bopp, B2R, binarySingleNaNFloatToB754, B754_to_R, F2R,
          FloatSpec.Core.Defs.F2R] <;> ring

@[simp] theorem is_nan_Bopp {prec emax : Int} (x : binary_float prec emax) :
    is_nan (Bopp x) = is_nan x := by
  cases x <;>
    simp [Bopp, is_nan, binarySingleNaNFloatToB754, BSN_is_nan]

@[simp] theorem is_finite_Bopp {prec emax : Int} (x : binary_float prec emax) :
    is_finite (Bopp x) = is_finite x := by
  cases x <;>
    simp [Bopp, is_finite, binarySingleNaNFloatToB754, BSN_is_finite]

@[simp] theorem is_finite_strict_Bopp {prec emax : Int}
    (x : binary_float prec emax) :
    is_finite_strict (Bopp x) = is_finite_strict x := by
  cases x <;>
    simp [Bopp, is_finite_strict, binarySingleNaNFloatToB754,
      BSN_is_finite_strict]

theorem Bsign_Bopp {prec emax : Int} (x : binary_float prec emax)
    (hx : is_nan x = false) : Bsign (Bopp x) = !Bsign x := by
  cases x <;>
    simp [Bopp, Bsign, is_nan, binarySingleNaNFloatToB754,
      BSN_sign, BSN_is_nan] at hx ⊢

theorem normalize_B2BSN_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (m e : Int) (szero : Bool) :
    let input := F2R
      (FloatSpec.Core.Defs.FlocqFloat.mk m e :
        FloatSpec.Core.Defs.FlocqFloat 2)
    let result := Binary.normalize (prec:=prec) (emax:=emax) mode m e szero
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) input|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (Binary.B2BSN result) = FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) input ∧
      is_finite (Binary.B2BSN result) = true ∧
      Bsign (Binary.B2BSN result) =
        (if input = 0 then szero else decide (input < 0))
    else
      B2SF (Binary.B2BSN result) =
        bsn_binary_overflow (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool input 0) := by
  dsimp only
  let result := Binary.normalize (prec:=prec) (emax:=emax) mode m e szero
  have href := Binary.normalize_correct (prec:=prec) (emax:=emax)
    mode m e szero
  dsimp only at href
  by_cases hlt : FloatSpec.Core.Raux.Rlt_bool
      |FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
          (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
            FloatSpec.Core.Defs.FlocqFloat 2))|
      (FloatSpec.Core.Raux.bpow 2 emax) = true
  · rw [ite_eq_left hlt] at href
    rw [ite_eq_left hlt]
    have hnotnan : Binary.is_nan result = false := by
      cases hr : result <;>
        simp [result, hr, Binary.is_finite, Binary.is_nan] at href ⊢
    exact ⟨(Binary.B2R_B2BSN result).trans href.1,
      (Binary.is_finite_B2BSN result).trans href.2.1,
      (Binary.Bsign_B2BSN result hnotnan).trans href.2.2⟩
  · rw [ite_eq_right hlt] at href
    rw [ite_eq_right hlt]
    have hstd := congrArg FF2SF href
    calc
      B2SF (Binary.B2BSN result) = Binary.B2SF result :=
        Binary.B2SF_B2BSN result
      _ = FF2SF (Binary.B2FF result) := by cases result <;> rfl
      _ = FF2SF (Binary.binary_overflow (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool
            (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
              FloatSpec.Core.Defs.FlocqFloat 2)) 0)) := hstd
      _ = bsn_binary_overflow (prec:=prec) (emax:=emax) mode
          (FloatSpec.Core.Raux.Rlt_bool
            (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
              FloatSpec.Core.Defs.FlocqFloat 2)) 0) := by
        cases hs : FloatSpec.Core.Raux.Rlt_bool
          (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
            FloatSpec.Core.Defs.FlocqFloat 2)) 0 <;>
          cases mode <;> rfl

private theorem roundR_single_finite {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (s : Bool) (m : Nat) (e : Int)
    (hm : 0 < m)
    (hb : specFloat_bounded (prec:=prec) (emax:=emax) m e = true) :
    FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (3 - emax - prec) prec)
        (rnd_of_mode mode)
        (B2R (BinarySingleNaNFloat.B754_finite s m e hm hb)) =
      B2R (BinarySingleNaNFloat.B754_finite s m e hm hb) := by
  let mp := binaryPositiveOfNat m hm
  have hbp : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mp) e = true := by
    simpa [mp, binaryPositiveOfNat_spec] using hb
  simpa [B2R, Binary.B2R, mp, binaryPositiveOfNat_spec,
    binarySingleNaNFloatToB754, B754_to_R] using
    roundRBinaryFinite (prec:=prec) (emax:=emax) mode s mp e hbp

private theorem abs_single_finite_lt_emax {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (s : Bool) (m : Nat) (e : Int) (hm : 0 < m)
    (hb : specFloat_bounded (prec:=prec) (emax:=emax) m e = true) :
    |B2R (BinarySingleNaNFloat.B754_finite s m e hm hb)| <
      FloatSpec.Core.Raux.bpow 2 emax := by
  let mp := binaryPositiveOfNat m hm
  have hbp : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mp) e = true := by
    simpa [mp, binaryPositiveOfNat_spec] using hb
  simpa [B2R, Binary.B2R, mp, binaryPositiveOfNat_spec,
    binarySingleNaNFloatToB754, B754_to_R] using
    absBinaryFiniteLtEmax (prec:=prec) (emax:=emax) s mp e hbp

private theorem single_finite_ne_zero_and_sign {prec emax : Int}
    (s : Bool) (m : Nat) (e : Int) (hm : 0 < m)
    (hb : specFloat_bounded (prec:=prec) (emax:=emax) m e = true) :
    B2R (BinarySingleNaNFloat.B754_finite s m e hm hb) ≠ 0 ∧
      decide (B2R (BinarySingleNaNFloat.B754_finite s m e hm hb) < 0) = s := by
  have hmInt : (0 : Int) < (m : Int) := by exact_mod_cast hm
  cases s
  · have hpos : 0 < B2R
        (BinarySingleNaNFloat.B754_finite false m e hm hb) := by
      change 0 < F2R (FloatSpec.Core.Defs.FlocqFloat.mk (m : Int) e :
        FloatSpec.Core.Defs.FlocqFloat 2)
      exact FloatSpec.Core.Float_prop.F2R_gt_0
        (beta:=2) (f:=FloatSpec.Core.Defs.FlocqFloat.mk (m : Int) e)
        (by norm_num) hmInt
    exact ⟨ne_of_gt hpos, by simp [not_lt_of_ge (le_of_lt hpos)]⟩
  · have hneg : B2R
        (BinarySingleNaNFloat.B754_finite true m e hm hb) < 0 := by
      change F2R (FloatSpec.Core.Defs.FlocqFloat.mk (-(m : Int)) e :
        FloatSpec.Core.Defs.FlocqFloat 2) < 0
      exact FloatSpec.Core.Float_prop.F2R_lt_0
        (beta:=2) (f:=FloatSpec.Core.Defs.FlocqFloat.mk (-(m : Int)) e)
        (by norm_num) (neg_neg_of_pos hmInt)
    exact ⟨ne_of_lt hneg, by simp [hneg]⟩

-- Coq `BinarySingleNaN.v:Bmult_correct` on the exact SingleNaN carrier.
theorem Bmult_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y : binary_float prec emax) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (B2R x * B2R y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (Bmult mode x y) = FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (B2R x * B2R y) ∧
      is_finite (Bmult mode x y) = (is_finite x && is_finite y) ∧
      (is_nan (Bmult mode x y) = false →
        Bsign (Bmult mode x y) = Bool.xor (Bsign x) (Bsign y))
    else
      B2SF (Bmult mode x y) =
        bsn_binary_overflow (prec:=prec) (emax:=emax) mode
          (Bool.xor (Bsign x) (Bsign y)) := by
  cases x with
  | B754_zero sx =>
      cases y <;>
        simp [Bmult, B2R, Bsign, is_finite, is_nan,
          binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
          BSN_is_nan, B2SF, binarySingleNaNFloatToStandardFloat,
          Binary.roundR_zero_of_mode, Binary.Rlt_bool_zero_bpow]
  | B754_infinity sx =>
      cases y <;>
        simp [Bmult, B2R, Bsign, is_finite, is_nan,
          binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
          BSN_is_nan, B2SF, binarySingleNaNFloatToStandardFloat,
          Binary.roundR_zero_of_mode, Binary.Rlt_bool_zero_bpow]
  | B754_nan =>
      cases y <;>
        simp [Bmult, B2R, Bsign, is_finite, is_nan,
          binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
          BSN_is_nan, B2SF, binarySingleNaNFloatToStandardFloat,
          Binary.roundR_zero_of_mode, Binary.Rlt_bool_zero_bpow]
  | B754_finite sx mx ex hmx Hx =>
      cases y with
      | B754_zero sy =>
          simp [Bmult, B2R, Bsign, is_finite, is_nan,
            binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
            BSN_is_nan, B2SF, binarySingleNaNFloatToStandardFloat,
            Binary.roundR_zero_of_mode, Binary.Rlt_bool_zero_bpow]
      | B754_infinity sy =>
          simp [Bmult, B2R, Bsign, is_finite, is_nan,
            binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
            BSN_is_nan, B2SF, binarySingleNaNFloatToStandardFloat,
            Binary.roundR_zero_of_mode, Binary.Rlt_bool_zero_bpow]
      | B754_nan =>
          simp [Bmult, B2R, Bsign, is_finite, is_nan,
            binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
            BSN_is_nan, B2SF, binarySingleNaNFloatToStandardFloat,
            Binary.roundR_zero_of_mode, Binary.Rlt_bool_zero_bpow]
      | B754_finite sy my ey hmy Hy =>
          let z := binary_round_aux (prec:=prec) (emax:=emax) mode
            (Bool.xor sx sy) ((mx * my : Nat) : Int) (ex + ey)
            FloatSpec.Calc.Bracket.Location.loc_Exact
          have haux := _root_.Bmult_correct_aux (prec:=prec) (emax:=emax)
            mode sx mx ex hmx Hx sy my ey hmy Hy
          have hinputX : B2R
              (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx) =
              SF2R 2 (StandardFloat.S754_finite sx mx ex) := by
            rfl
          have hinputY : B2R
              (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy) =
              SF2R 2 (StandardFloat.S754_finite sy my ey) := by
            rfl
          by_cases hlt : FloatSpec.Core.Raux.Rlt_bool
              |FloatSpec.Core.Generic_fmt.roundR 2
                (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                  (SF2R 2 (StandardFloat.S754_finite sx mx ex) *
                   SF2R 2 (StandardFloat.S754_finite sy my ey))|
              (FloatSpec.Core.Raux.bpow 2 emax) = true
          · rw [ite_eq_left (by simpa [hinputX, hinputY] using hlt)]
            have hbranch := haux.2
            rw [ite_eq_left hlt] at hbranch
            rcases hbranch with ⟨hvalue, hfinite, hsign⟩
            refine ⟨?_, ?_, ?_⟩
            · simpa [Bmult, z, hinputX, hinputY] using hvalue
            · rw [show Bmult mode
                  (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx)
                  (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy) =
                    standardFloatToBinarySingleNaNFloat z haux.1 by rfl]
              change BSN_is_finite (binarySingleNaNFloatToB754
                (standardFloatToBinarySingleNaNFloat z haux.1)) = true
              rw [Binary.is_finite_standardFloatToBinarySingleNaNFloat]
              exact hfinite
            · intro _
              rw [show Bmult mode
                  (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx)
                  (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy) =
                    standardFloatToBinarySingleNaNFloat z haux.1 by rfl,
                Bsign_SF2B z haux.1]
              simpa [z, Bsign, binarySingleNaNFloatToB754, BSN_sign] using hsign
          · rw [ite_eq_right (by simpa [hinputX, hinputY] using hlt)]
            have hbranch := haux.2
            rw [ite_eq_right hlt] at hbranch
            simpa [Bmult, z, Bsign, binarySingleNaNFloatToB754, BSN_sign,
              is_finite]
              using hbranch

-- Coq `BinarySingleNaN.v:Bplus_correct`; the only hypotheses are the two
-- source finiteness assumptions.
theorem Bplus_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y : binary_float prec emax)
    (hx : is_finite x = true) (hy : is_finite y = true) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (B2R x + B2R y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (Bplus mode x y) = FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (B2R x + B2R y) ∧
      is_finite (Bplus mode x y) = true ∧
      Bsign (Bplus mode x y) =
        binaryPlusResultSign mode (Bsign x) (Bsign y) (B2R x + B2R y)
    else
      B2SF (Bplus mode x y) =
          bsn_binary_overflow (prec:=prec) (emax:=emax) mode (Bsign x) ∧
        Bsign x = Bsign y := by
  cases x with
  | B754_zero sx =>
      cases y with
      | B754_zero sy =>
          cases mode <;> cases sx <;> cases sy <;>
            simp [Bplus, B2R, Bsign, is_finite,
              binarySingleNaNFloatToB754, B754_to_R, BSN_sign,
              BSN_is_finite, binaryPlusResultSign, Binary.roundR_zero_of_mode,
              Binary.Rlt_bool_zero_bpow]
      | B754_infinity sy =>
          simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hy
      | B754_nan =>
          simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hy
      | B754_finite sy my ey hmy Hy =>
          have hround := roundR_single_finite (prec:=prec) (emax:=emax)
            mode sy my ey hmy Hy
          have habs := abs_single_finite_lt_emax (prec:=prec) (emax:=emax)
            sy my ey hmy Hy
          have hs := single_finite_ne_zero_and_sign
            (prec:=prec) (emax:=emax) sy my ey hmy Hy
          have hzR : B2R (BinarySingleNaNFloat.B754_zero
              (prec:=prec) (emax:=emax) sx) = 0 := rfl
          have hcond : FloatSpec.Core.Raux.Rlt_bool
              |FloatSpec.Core.Generic_fmt.roundR 2
                (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                  (B2R (BinarySingleNaNFloat.B754_zero
                    (prec:=prec) (emax:=emax) sx) +
                   B2R (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy))|
              (FloatSpec.Core.Raux.bpow 2 emax) = true := by
            rw [hzR, zero_add, hround]
            simp [FloatSpec.Core.Raux.Rlt_bool, habs]
          rw [ite_eq_left hcond]
          refine ⟨?_, rfl, ?_⟩
          · rw [show Bplus mode (BinarySingleNaNFloat.B754_zero sx)
                (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy) =
              BinarySingleNaNFloat.B754_finite sy my ey hmy Hy by rfl,
              hzR, zero_add]
            exact hround.symm
          · change sy = binaryPlusResultSign mode sx sy
              (B2R (BinarySingleNaNFloat.B754_zero sx) +
               B2R (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy))
            rw [hzR, zero_add]
            simp [binaryPlusResultSign, hs.1, hs.2]
  | B754_infinity sx =>
      simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hx
  | B754_nan =>
      simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hx
  | B754_finite sx mx ex hmx Hx =>
      cases y with
      | B754_zero sy =>
          have hround := roundR_single_finite (prec:=prec) (emax:=emax)
            mode sx mx ex hmx Hx
          have habs := abs_single_finite_lt_emax (prec:=prec) (emax:=emax)
            sx mx ex hmx Hx
          have hs := single_finite_ne_zero_and_sign
            (prec:=prec) (emax:=emax) sx mx ex hmx Hx
          have hzR : B2R (BinarySingleNaNFloat.B754_zero
              (prec:=prec) (emax:=emax) sy) = 0 := rfl
          have hcond : FloatSpec.Core.Raux.Rlt_bool
              |FloatSpec.Core.Generic_fmt.roundR 2
                (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                  (B2R (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx) +
                   B2R (BinarySingleNaNFloat.B754_zero
                    (prec:=prec) (emax:=emax) sy))|
              (FloatSpec.Core.Raux.bpow 2 emax) = true := by
            rw [hzR, add_zero, hround]
            simp [FloatSpec.Core.Raux.Rlt_bool, habs]
          rw [ite_eq_left hcond]
          refine ⟨?_, rfl, ?_⟩
          · rw [show Bplus mode
                (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx)
                (BinarySingleNaNFloat.B754_zero sy) =
              BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx by rfl,
              hzR, add_zero]
            exact hround.symm
          · change sx = binaryPlusResultSign mode sx sy
              (B2R (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx) +
               B2R (BinarySingleNaNFloat.B754_zero sy))
            rw [hzR, add_zero]
            simp [binaryPlusResultSign, hs.1, hs.2]
      | B754_infinity sy =>
          simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hy
      | B754_nan =>
          simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hy
      | B754_finite sy my ey hmy Hy =>
          let ez := min ex ey
          let m := Fplus_naive sx mx ex sy my ey ez
          let szero := match mode with
            | RoundingMode.RTN => true
            | _ => false
          have hsumRaw := Fplus_naive_correct sx mx ex sy my ey ez
            (min_le_left ex ey) (min_le_right ex ey)
          have hsum : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m ez :
                FloatSpec.Core.Defs.FlocqFloat 2) =
              B2R (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx) +
              B2R (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy) := by
            simpa [m, ez, B2R, FloatSpec.Core.Zaux.cond_Zopp,
              binarySingleNaNFloatToB754, B754_to_R] using hsumRaw
          have href := normalize_B2BSN_correct (prec:=prec) (emax:=emax)
            mode m ez szero
          dsimp only at href
          by_cases hlt : FloatSpec.Core.Raux.Rlt_bool
              |FloatSpec.Core.Generic_fmt.roundR 2
                (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                  (B2R (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx) +
                   B2R (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy))|
              (FloatSpec.Core.Raux.bpow 2 emax) = true
          · rw [ite_eq_left hlt]
            rw [hsum, ite_eq_left hlt] at href
            have hsign :
                (if B2R (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx) +
                      B2R (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy) = 0
                  then szero
                  else decide
                    (B2R (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx) +
                      B2R (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy) < 0)) =
                  binaryPlusResultSign mode sx sy
                    (B2R (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx) +
                     B2R (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy)) := by
              unfold binaryPlusResultSign
              by_cases hzero :
                  B2R (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx) +
                    B2R (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy) = 0
              · have hsne : sx ≠ sy := by
                  intro heq
                  subst sy
                  cases sx
                  · have hxpos := (single_finite_ne_zero_and_sign
                        (prec:=prec) (emax:=emax) false mx ex hmx Hx).2
                    have hypos := (single_finite_ne_zero_and_sign
                        (prec:=prec) (emax:=emax) false my ey hmy Hy).2
                    simp at hxpos hypos
                    have hx0 := (single_finite_ne_zero_and_sign
                        (prec:=prec) (emax:=emax) false mx ex hmx Hx).1
                    have hy0 := (single_finite_ne_zero_and_sign
                        (prec:=prec) (emax:=emax) false my ey hmy Hy).1
                    have hxnonneg : 0 ≤ B2R
                        (BinarySingleNaNFloat.B754_finite false mx ex hmx Hx) :=
                      le_of_not_gt (by simpa using hxpos)
                    have hynonneg : 0 ≤ B2R
                        (BinarySingleNaNFloat.B754_finite false my ey hmy Hy) :=
                      le_of_not_gt (by simpa using hypos)
                    exact hx0 (le_antisymm
                      (by linarith [hzero, hynonneg]) hxnonneg)
                  · have hxneg : B2R
                        (BinarySingleNaNFloat.B754_finite true mx ex hmx Hx) < 0 := by
                      simpa using of_decide_eq_true
                        (single_finite_ne_zero_and_sign
                          (prec:=prec) (emax:=emax) true mx ex hmx Hx).2
                    have hyneg : B2R
                        (BinarySingleNaNFloat.B754_finite true my ey hmy Hy) < 0 := by
                      simpa using of_decide_eq_true
                        (single_finite_ne_zero_and_sign
                          (prec:=prec) (emax:=emax) true my ey hmy Hy).2
                    linarith
                cases mode <;> cases sx <;> cases sy <;> simp_all [szero]
              · simp [hzero]
            refine ⟨?_, ?_, ?_⟩
            · simpa [Bplus, ez, m, szero] using href.1
            · simpa [Bplus, ez, m, szero] using href.2.1
            · simpa [Bplus, ez, m, szero, hsign, Bsign,
                binarySingleNaNFloatToB754, BSN_sign] using href.2.2
          · rw [ite_eq_right hlt]
            rw [hsum, ite_eq_right hlt] at href
            have hnotlt : ¬
                |FloatSpec.Core.Generic_fmt.roundR 2
                  (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                    (B2R (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx) +
                     B2R (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy))| <
                  FloatSpec.Core.Raux.bpow 2 emax := by
              intro hr
              exact hlt (by simp [FloatSpec.Core.Raux.Rlt_bool, hr])
            have hover : FloatSpec.Core.Raux.bpow 2 emax ≤
                |FloatSpec.Core.Generic_fmt.round_to_generic 2
                  (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                    (B2R (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx) +
                     B2R (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy))| := by
              simpa [FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR]
                using le_of_not_gt hnotlt
            have hxRange := range_bounded_of_specFloat_bounded
              (prec:=prec) (emax:=emax) mx ex hmx Hx
            have hyRange := range_bounded_of_specFloat_bounded
              (prec:=prec) (emax:=emax) my ey hmy Hy
            have hsign := ExperimentalSingleNaNArithmetic.sign_plus_overflow
              (prec:=prec) (emax:=emax) mode sx mx ex sy my ey hxRange hyRange
              (by simpa [B2R, SF2R, FloatSpec.Core.Zaux.cond_Zopp,
                  binarySingleNaNFloatToB754, B754_to_R] using hover)
            constructor
            · rw [show Bplus mode
                  (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx)
                  (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy) =
                Binary.B2BSN (Binary.normalize mode m ez szero) by rfl]
              rw [href]
              congr 1
              simpa [Bsign, B2R, SF2R, binarySingleNaNFloatToB754,
                B754_to_R, BSN_sign] using hsign.1.symm
            · exact hsign.2

-- Coq `BinarySingleNaN.v:Bminus_correct`; as upstream, subtraction is
-- addition of the exact opposite operand.
theorem Bminus_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y : binary_float prec emax)
    (hx : is_finite x = true) (hy : is_finite y = true) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (B2R x - B2R y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (Bminus mode x y) = FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (B2R x - B2R y) ∧
      is_finite (Bminus mode x y) = true ∧
      Bsign (Bminus mode x y) =
        binaryMinusResultSign mode (Bsign x) (Bsign y) (B2R x - B2R y)
    else
      B2SF (Bminus mode x y) =
          bsn_binary_overflow (prec:=prec) (emax:=emax) mode (Bsign x) ∧
        Bsign x = !Bsign y := by
  have hynan : is_nan y = false := by
    cases y <;>
      simp [is_finite, is_nan, binarySingleNaNFloatToB754,
        BSN_is_finite, BSN_is_nan] at hy ⊢
  have hyopp : is_finite (Bopp y) = true := by
    rw [is_finite_Bopp]
    exact hy
  have hplus := Bplus_correct (prec:=prec) (emax:=emax)
    mode x (Bopp y) hx hyopp
  have hvalue := B2R_Bopp y
  have hsign := Bsign_Bopp y hynan
  simpa [Bminus, hvalue, hsign, sub_eq_add_neg,
    binaryMinusResultSign] using hplus

noncomputable def binaryFmaResultSign {prec emax : Int}
    (mode : RoundingMode) (x y z : binary_float prec emax) (res : ℝ) : Bool :=
  if res = 0 then Bfma_szero mode x y z else decide (res < 0)

private theorem Bfma_returned_zero_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y z : binary_float prec emax)
    (hprod : B2R x * B2R y = 0) (hz : B2R z = 0)
    (hout : Bfma mode x y z =
      BinarySingleNaNFloat.B754_zero (Bfma_szero mode x y z)) :
    let res := B2R x * B2R y + B2R z
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (Bfma mode x y z) = FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res ∧
      is_finite (Bfma mode x y z) = true ∧
      Bsign (Bfma mode x y z) = binaryFmaResultSign mode x y z res
    else
      B2SF (Bfma mode x y z) = bsn_binary_overflow
        (prec:=prec) (emax:=emax) mode (FloatSpec.Core.Raux.Rlt_bool res 0) := by
  dsimp only
  have hres : B2R x * B2R y + B2R z = 0 := by rw [hprod, hz]; norm_num
  rw [hres, Binary.roundR_zero_of_mode, abs_zero,
    Binary.Rlt_bool_zero_bpow (emax:=emax), hout]
  simp [B2R, Bsign, is_finite, binaryFmaResultSign,
    binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite]

private theorem Bfma_returned_finite_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y : binary_float prec emax)
    (s : Bool) (m : Nat) (e : Int) (hm : 0 < m)
    (hb : specFloat_bounded (prec:=prec) (emax:=emax) m e = true)
    (hprod : B2R x * B2R y = 0)
    (hout : Bfma mode x y
      (BinarySingleNaNFloat.B754_finite s m e hm hb) =
        BinarySingleNaNFloat.B754_finite s m e hm hb) :
    let z := BinarySingleNaNFloat.B754_finite s m e hm hb
    let res := B2R x * B2R y + B2R z
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (Bfma mode x y z) = FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res ∧
      is_finite (Bfma mode x y z) = true ∧
      Bsign (Bfma mode x y z) = binaryFmaResultSign mode x y z res
    else
      B2SF (Bfma mode x y z) = bsn_binary_overflow
        (prec:=prec) (emax:=emax) mode (FloatSpec.Core.Raux.Rlt_bool res 0) := by
  dsimp only
  let z := BinarySingleNaNFloat.B754_finite s m e hm hb
  have hres : B2R x * B2R y + B2R z = B2R z := by rw [hprod]; norm_num
  have hround := roundR_single_finite (prec:=prec) (emax:=emax)
    mode s m e hm hb
  have habs := abs_single_finite_lt_emax (prec:=prec) (emax:=emax)
    s m e hm hb
  have hs := single_finite_ne_zero_and_sign
    (prec:=prec) (emax:=emax) s m e hm hb
  have hcond : FloatSpec.Core.Raux.Rlt_bool
      |FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
          (B2R x * B2R y + B2R z)|
      (FloatSpec.Core.Raux.bpow 2 emax) = true := by
    rw [hres, hround]
    simp [FloatSpec.Core.Raux.Rlt_bool, habs]
  rw [ite_eq_left hcond, hout]
  refine ⟨?_, rfl, ?_⟩
  · rw [hres]
    exact hround.symm
  · change s = binaryFmaResultSign mode x y z (B2R x * B2R y + B2R z)
    rw [hres]
    simp [binaryFmaResultSign, z, hs.1, hs.2]

private theorem Bfma_normalized_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y z : binary_float prec emax) (m e : Int)
    (hinput : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
        FloatSpec.Core.Defs.FlocqFloat 2) = B2R x * B2R y + B2R z)
    (hout : Bfma mode x y z = Binary.B2BSN
      (Binary.normalize mode m e (Bfma_szero mode x y z))) :
    let res := B2R x * B2R y + B2R z
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (Bfma mode x y z) = FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res ∧
      is_finite (Bfma mode x y z) = true ∧
      Bsign (Bfma mode x y z) = binaryFmaResultSign mode x y z res
    else
      B2SF (Bfma mode x y z) = bsn_binary_overflow
        (prec:=prec) (emax:=emax) mode (FloatSpec.Core.Raux.Rlt_bool res 0) := by
  have href := normalize_B2BSN_correct (prec:=prec) (emax:=emax)
    mode m e (Bfma_szero mode x y z)
  simp only [F2R, FloatSpec.Core.Defs.F2R] at hinput
  rw [← hinput]
  simpa [hout, binaryFmaResultSign, zpow_ne_zero] using href

-- Coq `BinarySingleNaN.v:Bfma_correct` on finite inputs.
theorem Bfma_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y z : binary_float prec emax)
    (hx : is_finite x = true) (hy : is_finite y = true)
    (hz : is_finite z = true) :
    let res := B2R x * B2R y + B2R z
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (Bfma mode x y z) = FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode) res ∧
      is_finite (Bfma mode x y z) = true ∧
      Bsign (Bfma mode x y z) = binaryFmaResultSign mode x y z res
    else
      B2SF (Bfma mode x y z) = bsn_binary_overflow
        (prec:=prec) (emax:=emax) mode (FloatSpec.Core.Raux.Rlt_bool res 0) := by
  cases x with
  | B754_infinity sx =>
      simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hx
  | B754_nan =>
      simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hx
  | B754_zero sx =>
      cases y with
      | B754_infinity sy =>
          simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hy
      | B754_nan =>
          simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hy
      | B754_zero sy =>
          cases z with
          | B754_infinity sz =>
              simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hz
          | B754_nan =>
              simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hz
          | B754_zero sz =>
              apply Bfma_returned_zero_correct mode
                (BinarySingleNaNFloat.B754_zero sx)
                (BinarySingleNaNFloat.B754_zero sy)
                (BinarySingleNaNFloat.B754_zero sz) <;>
                simp [B2R, binarySingleNaNFloatToB754, B754_to_R, Bfma]
          | B754_finite sz mz ez hmz Hz =>
              apply Bfma_returned_finite_correct mode
                (BinarySingleNaNFloat.B754_zero sx)
                (BinarySingleNaNFloat.B754_zero sy) sz mz ez hmz Hz <;>
                simp [B2R, binarySingleNaNFloatToB754, B754_to_R, Bfma]
      | B754_finite sy my ey hmy Hy =>
          cases z with
          | B754_infinity sz =>
              simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hz
          | B754_nan =>
              simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hz
          | B754_zero sz =>
              apply Bfma_returned_zero_correct mode
                (BinarySingleNaNFloat.B754_zero sx)
                (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy)
                (BinarySingleNaNFloat.B754_zero sz) <;>
                simp [B2R, binarySingleNaNFloatToB754, B754_to_R, Bfma]
          | B754_finite sz mz ez hmz Hz =>
              apply Bfma_returned_finite_correct mode
                (BinarySingleNaNFloat.B754_zero sx)
                (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy)
                sz mz ez hmz Hz <;>
                simp [B2R, binarySingleNaNFloatToB754, B754_to_R, Bfma]
  | B754_finite sx mx ex hmx Hx =>
      cases y with
      | B754_infinity sy =>
          simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hy
      | B754_nan =>
          simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hy
      | B754_zero sy =>
          cases z with
          | B754_infinity sz =>
              simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hz
          | B754_nan =>
              simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hz
          | B754_zero sz =>
              apply Bfma_returned_zero_correct mode
                (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx)
                (BinarySingleNaNFloat.B754_zero sy)
                (BinarySingleNaNFloat.B754_zero sz) <;>
                simp [B2R, binarySingleNaNFloatToB754, B754_to_R, Bfma]
          | B754_finite sz mz ez hmz Hz =>
              apply Bfma_returned_finite_correct mode
                (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx)
                (BinarySingleNaNFloat.B754_zero sy) sz mz ez hmz Hz <;>
                simp [B2R, binarySingleNaNFloatToB754, B754_to_R, Bfma]
      | B754_finite sy my ey hmy Hy =>
          let X : FloatSpec.Core.Defs.FlocqFloat 2 :=
            FloatSpec.Core.Defs.FlocqFloat.mk
              (FloatSpec.Core.Zaux.cond_Zopp sx (mx : Int)) ex
          let Y : FloatSpec.Core.Defs.FlocqFloat 2 :=
            FloatSpec.Core.Defs.FlocqFloat.mk
              (FloatSpec.Core.Zaux.cond_Zopp sy (my : Int)) ey
          let product := FloatSpec.Calc.Operations.Fmult 2 X Y
          have hmulTrip := FloatSpec.Calc.Operations.F2R_mult
            (beta:=2) X Y
          have hmul : F2R product = F2R X * F2R Y := by
            simpa [wp, PostCond.noThrow, pure, product] using
              hmulTrip (by norm_num)
          have hproductEta : (FloatSpec.Core.Defs.FlocqFloat.mk
              product.Fnum product.Fexp : FloatSpec.Core.Defs.FlocqFloat 2) =
              product := by cases product <;> rfl
          cases z with
          | B754_infinity sz =>
              simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hz
          | B754_nan =>
              simp [is_finite, binarySingleNaNFloatToB754, BSN_is_finite] at hz
          | B754_zero sz =>
              apply Bfma_normalized_correct mode
                (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx)
                (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy)
                (BinarySingleNaNFloat.B754_zero sz)
                product.Fnum product.Fexp
              · rw [hproductEta, hmul]
                change F2R X * F2R Y = F2R X * F2R Y + 0
                ring
              · rfl
          | B754_finite sz mz ez hmz Hz =>
              let Z : FloatSpec.Core.Defs.FlocqFloat 2 :=
                FloatSpec.Core.Defs.FlocqFloat.mk
                  (FloatSpec.Core.Zaux.cond_Zopp sz (mz : Int)) ez
              let sum := FloatSpec.Calc.Operations.Fplus 2 product Z
              have haddTrip := FloatSpec.Calc.Operations.F2R_plus
                (beta:=2) product Z
              have hadd : F2R sum = F2R product + F2R Z := by
                simpa [wp, PostCond.noThrow, pure, sum] using
                  haddTrip (by norm_num)
              have hsumEta : (FloatSpec.Core.Defs.FlocqFloat.mk
                  sum.Fnum sum.Fexp : FloatSpec.Core.Defs.FlocqFloat 2) =
                  sum := by cases sum <;> rfl
              apply Bfma_normalized_correct mode
                (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx)
                (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy)
                (BinarySingleNaNFloat.B754_finite sz mz ez hmz Hz)
                sum.Fnum sum.Fexp
              · rw [hsumEta, hadd, hmul]
                rfl
              · rfl

private theorem Bdiv_finite_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (sx : Bool) (mx : Nat) (ex : Int) (hmx : 0 < mx)
    (Hx : specFloat_bounded (prec:=prec) (emax:=emax) mx ex = true)
    (sy : Bool) (my : Nat) (ey : Int) (hmy : 0 < my)
    (Hy : specFloat_bounded (prec:=prec) (emax:=emax) my ey = true) :
    let x := BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx
    let y := BinarySingleNaNFloat.B754_finite sy my ey hmy Hy
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (B2R x / B2R y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (Bdiv_finite (prec:=prec) (emax:=emax)
          mode sx mx ex hmx sy my ey hmy) =
          FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
              (B2R x / B2R y) ∧
      is_finite (Bdiv_finite (prec:=prec) (emax:=emax)
          mode sx mx ex hmx sy my ey hmy) = true ∧
      (is_nan (Bdiv_finite (prec:=prec) (emax:=emax)
          mode sx mx ex hmx sy my ey hmy) = false →
        Bsign (Bdiv_finite (prec:=prec) (emax:=emax)
          mode sx mx ex hmx sy my ey hmy) = Bool.xor sx sy)
    else
      B2SF (Bdiv_finite (prec:=prec) (emax:=emax)
          mode sx mx ex hmx sy my ey hmy) =
        bsn_binary_overflow (prec:=prec) (emax:=emax) mode (Bool.xor sx sy) := by
  dsimp only
  let mxp := binaryPositiveOfNat mx hmx
  let myp := binaryPositiveOfNat my hmy
  let result := SFdiv_core_binary prec emax (mx : Int) ex (my : Int) ey
  let z := binary_round_aux (prec:=prec) (emax:=emax) mode
    (Bool.xor sx sy) result.1 result.2.1 result.2.2
  have haux := _root_.Bdiv_correct_aux (prec:=prec) (emax:=emax)
    mode sx mxp ex sy myp ey
  have haux' : validBinarySingleNaNStandardFloat
        (prec:=prec) (emax:=emax) z = true ∧
      if FloatSpec.Core.Raux.Rlt_bool
          |FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
              (SF2R 2 (StandardFloat.S754_finite sx mx ex) /
               SF2R 2 (StandardFloat.S754_finite sy my ey))|
          (FloatSpec.Core.Raux.bpow 2 emax) then
        SF2R 2 z = FloatSpec.Core.Generic_fmt.roundR 2
            (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
              (SF2R 2 (StandardFloat.S754_finite sx mx ex) /
               SF2R 2 (StandardFloat.S754_finite sy my ey)) ∧
        is_finite_SF z = true ∧ sign_SF z = Bool.xor sx sy
      else z = bsn_binary_overflow (prec:=prec) (emax:=emax) mode
          (Bool.xor sx sy) := by
    simpa [mxp, myp, result, z, binaryPositiveOfNat_spec] using haux
  let hvalid := haux'.1
  have hout : Bdiv_finite (prec:=prec) (emax:=emax)
      mode sx mx ex hmx sy my ey hmy =
      standardFloatToBinarySingleNaNFloat z hvalid := by
    rfl
  have hquot :
      B2R (BinarySingleNaNFloat.B754_finite sx mx ex hmx Hx) /
          B2R (BinarySingleNaNFloat.B754_finite sy my ey hmy Hy) =
        SF2R 2 (StandardFloat.S754_finite sx mx ex) /
          SF2R 2 (StandardFloat.S754_finite sy my ey) := by
    simp [B2R, SF2R, binarySingleNaNFloatToB754, B754_to_R]
  by_cases hlt : FloatSpec.Core.Raux.Rlt_bool
      |FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
          (SF2R 2 (StandardFloat.S754_finite sx mx ex) /
           SF2R 2 (StandardFloat.S754_finite sy my ey))|
      (FloatSpec.Core.Raux.bpow 2 emax) = true
  · rw [ite_eq_left (by simpa only [hquot] using hlt)]
    have hbranch := haux'.2
    rw [ite_eq_left hlt] at hbranch
    rcases hbranch with ⟨hvalue, hfinite, hsign⟩
    rw [hout]
    refine ⟨?_, ?_, ?_⟩
    · rw [B2R_SF2B z hvalid]
      simpa only [hquot] using hvalue
    · simpa using hfinite
    · intro _
      rw [Bsign_SF2B z hvalid]
      exact hsign
  · rw [ite_eq_right (by simpa only [hquot] using hlt)]
    have hbranch := haux'.2
    rw [ite_eq_right hlt] at hbranch
    rw [hout, B2SF_SF2B]
    exact hbranch

-- Coq `BinarySingleNaN.v:Bdiv_correct`; no finiteness hypothesis is added.
theorem Bdiv_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x y : binary_float prec emax)
    (hy : B2R y ≠ 0) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (B2R x / B2R y)|
        (FloatSpec.Core.Raux.bpow 2 emax) then
      B2R (Bdiv mode x y) = FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (B2R x / B2R y) ∧
      is_finite (Bdiv mode x y) = is_finite x ∧
      (is_nan (Bdiv mode x y) = false →
        Bsign (Bdiv mode x y) = Bool.xor (Bsign x) (Bsign y))
    else
      B2SF (Bdiv mode x y) =
        bsn_binary_overflow (prec:=prec) (emax:=emax) mode
          (Bool.xor (Bsign x) (Bsign y)) := by
  cases y with
  | B754_zero sy =>
      simp [B2R, binarySingleNaNFloatToB754, B754_to_R] at hy
  | B754_infinity sy =>
      simp [B2R, binarySingleNaNFloatToB754, B754_to_R] at hy
  | B754_nan =>
      simp [B2R, binarySingleNaNFloatToB754, B754_to_R] at hy
  | B754_finite sy my ey hmy Hy =>
      cases x with
      | B754_zero sx =>
          simp [Bdiv, B2R, Bsign, is_finite, is_nan,
            binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
            BSN_is_nan, B2SF, binarySingleNaNFloatToStandardFloat,
            Binary.roundR_zero_of_mode, Binary.Rlt_bool_zero_bpow]
      | B754_infinity sx =>
          simp [Bdiv, B2R, Bsign, is_finite, is_nan,
            binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
            BSN_is_nan, B2SF, binarySingleNaNFloatToStandardFloat,
            Binary.roundR_zero_of_mode, Binary.Rlt_bool_zero_bpow]
      | B754_nan =>
          simp [Bdiv, B2R, Bsign, is_finite, is_nan,
            binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
            BSN_is_nan, B2SF, binarySingleNaNFloatToStandardFloat,
            Binary.roundR_zero_of_mode, Binary.Rlt_bool_zero_bpow]
      | B754_finite sx mx ex hmx Hx =>
          simpa [Bdiv, B2R, Bsign, is_finite, is_nan,
            binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
            BSN_is_nan] using Bdiv_finite_correct
            mode sx mx ex hmx Hx sy my ey hmy Hy

-- Coq `BinarySingleNaN.v:Bsqrt_correct_aux`.
-- The source mantissa is positive, and `bounded` is `SpecFloat.bounded`.
theorem Bsqrt_correct_aux {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (mx : FloatSpec.Core.Zaux.Positive) (ex : Int)
    (Hx : specFloat_bounded (prec:=prec) (emax:=emax)
      (FloatSpec.Core.Zaux.positiveToNat mx) ex = true) :
    let input := F2R
      (FloatSpec.Core.Defs.FlocqFloat.mk
        (FloatSpec.Core.Zaux.positiveToNat mx : Int) ex :
        FloatSpec.Core.Defs.FlocqFloat 2)
    let result := SFsqrt_core_binary prec emax
      (FloatSpec.Core.Zaux.positiveToNat mx : Int) ex
    let z := _root_.binary_round_aux (prec:=prec) (emax:=emax) mode false
      result.1 result.2.1 result.2.2
    validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true ∧
      SF2R 2 z = FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
          (Real.sqrt input) ∧
      is_finite_SF z = true ∧ sign_SF z = false := by
  let mxn := FloatSpec.Core.Zaux.positiveToNat mx
  let input := F2R
    (FloatSpec.Core.Defs.FlocqFloat.mk (mxn : Int) ex :
      FloatSpec.Core.Defs.FlocqFloat 2)
  let result := SFsqrt_core_binary prec emax (mxn : Int) ex
  let z := _root_.binary_round_aux (prec:=prec) (emax:=emax) mode false
    result.1 result.2.1 result.2.2
  have hmxn_pos : 0 < mxn := positiveToNat_pos_bsn mx
  have hdata := SFsqrt_core_binary_correct_data
    (prec:=prec) (emax:=emax) (mxn : Int) ex (by exact_mod_cast hmxn_pos)
  have hresult_pos : 0 < result.1 := by
    simpa [result] using hdata.1
  let mzn := result.1.toNat
  have hmzn_pos : 0 < mzn := by omega
  have hmzn_cast : (mzn : Int) = result.1 :=
    Int.toNat_of_nonneg (le_of_lt hresult_pos)
  have hbetween : FloatSpec.Calc.Bracket.inbetween_float 2
      (mzn : Int) result.2.1 |Real.sqrt input| result.2.2 := by
    simpa [input, result, mxn, hmzn_cast,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hdata.2.1
  have hexp : result.2.1 ≤ FLT_exp (3 - emax - prec) prec
      (FloatSpec.Core.Digits.Zdigits 2 (mzn : Int) + result.2.1) := by
    simpa [result, hmzn_cast] using hdata.2.2
  have haux := _root_.binary_round_aux_correct (prec:=prec) (emax:=emax)
    mode (Real.sqrt input) mzn result.2.1 result.2.2
    hmzn_pos hbetween hexp
  have hsqrt_sign :
      FloatSpec.Core.Raux.Rlt_bool (Real.sqrt input) 0 = false := by
    simp [FloatSpec.Core.Raux.Rlt_bool, Real.sqrt_nonneg]
  have hvalid : validBinarySingleNaNStandardFloat
      (prec:=prec) (emax:=emax) z = true := by
    simpa [z, hmzn_cast, hsqrt_sign] using haux.1
  have hlt := roundRSqrtBinaryFiniteLtEmax
    (prec:=prec) (emax:=emax) mode mx ex Hx
  have hltInput : FloatSpec.Core.Raux.Rlt_bool
      |FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
          (Real.sqrt input)|
      (FloatSpec.Core.Raux.bpow 2 emax) = true := by
    simp [FloatSpec.Core.Raux.Rlt_bool]
    simpa [input, mxn, Binary.B2R] using hlt
  have hbranch : SF2R 2 z =
        FloatSpec.Core.Generic_fmt.roundR 2
          (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
            (Real.sqrt input) ∧
      is_finite_SF z = true ∧ sign_SF z = false := by
    have h := haux.2
    simpa [z, hmzn_cast, hsqrt_sign, hltInput] using h
  exact ⟨hvalid, hbranch⟩

-- Coq `BinarySingleNaN.v:Bsqrt_correct` on the exact SingleNaN carrier.
theorem Bsqrt_correct {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (x : binary_float prec emax) :
    B2R (Bsqrt mode x) = FloatSpec.Core.Generic_fmt.roundR 2
        (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
          (Real.sqrt (B2R x)) ∧
    is_finite (Bsqrt mode x) =
      (match x with
      | BinarySingleNaNFloat.B754_zero _ => true
      | BinarySingleNaNFloat.B754_finite false _ _ _ _ => true
      | _ => false) ∧
    (is_nan (Bsqrt mode x) = false → Bsign (Bsqrt mode x) = Bsign x) := by
  cases x with
  | B754_zero sx =>
      cases mode <;>
        simp [Bsqrt, B2R, Bsign, is_finite, is_nan,
          binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
          BSN_is_nan, Binary.roundR_zero_of_mode]
  | B754_infinity sx =>
      cases sx <;> cases mode <;>
        simp [Bsqrt, B2R, Bsign, is_finite, is_nan,
          binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
          BSN_is_nan, Binary.roundR_zero_of_mode]
  | B754_nan =>
      cases mode <;>
        simp [Bsqrt, B2R, Bsign, is_finite, is_nan,
          binarySingleNaNFloatToB754, B754_to_R, BSN_sign, BSN_is_finite,
          BSN_is_nan, Binary.roundR_zero_of_mode]
  | B754_finite sx mx ex hmx Hx =>
      cases sx
      · let input := F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex :
            FloatSpec.Core.Defs.FlocqFloat 2)
        let result := SFsqrt_core_binary prec emax (mx : Int) ex
        have hdata := SFsqrt_core_binary_correct_data
          (prec:=prec) (emax:=emax) (mx : Int) ex (by exact_mod_cast hmx)
        have hresult_pos : 0 < result.1 := by
          simpa [result] using hdata.1
        let mzn := result.1.toNat
        have hmzn_pos : 0 < mzn := by omega
        have hmzn_cast : (mzn : Int) = result.1 :=
          Int.toNat_of_nonneg (le_of_lt hresult_pos)
        let z := binary_round_aux (prec:=prec) (emax:=emax) mode false
          (mzn : Int) result.2.1 result.2.2
        have hbetween : FloatSpec.Calc.Bracket.inbetween_float 2
            (mzn : Int) result.2.1 |Real.sqrt input| result.2.2 := by
          simpa [input, result, hmzn_cast,
            abs_of_nonneg (Real.sqrt_nonneg _)] using hdata.2.1
        have hexp : result.2.1 ≤ FLT_exp (3 - emax - prec) prec
            (FloatSpec.Core.Digits.Zdigits 2 (mzn : Int) + result.2.1) := by
          simpa [result, hmzn_cast] using hdata.2.2
        have haux := binary_round_aux_correct (prec:=prec) (emax:=emax)
          mode (Real.sqrt input) mzn result.2.1 result.2.2
          hmzn_pos hbetween hexp
        have hsqrt_sign :
            FloatSpec.Core.Raux.Rlt_bool (Real.sqrt input) 0 = false := by
          simp [FloatSpec.Core.Raux.Rlt_bool, Real.sqrt_nonneg]
        have hvalid : validBinarySingleNaNStandardFloat
            (prec:=prec) (emax:=emax) z = true := by
          simpa [z, hsqrt_sign] using haux.1
        let mxp := binaryPositiveOfNat mx hmx
        have hbounded : specFloat_bounded (prec:=prec) (emax:=emax)
            (FloatSpec.Core.Zaux.positiveToNat mxp) ex = true := by
          simpa [mxp, binaryPositiveOfNat_spec] using Hx
        have hlt := roundRSqrtBinaryFiniteLtEmax
          (prec:=prec) (emax:=emax) mode mxp ex hbounded
        have hltInput : FloatSpec.Core.Raux.Rlt_bool
            |FloatSpec.Core.Generic_fmt.roundR 2
              (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                (Real.sqrt input)|
            (FloatSpec.Core.Raux.bpow 2 emax) = true := by
          simp [FloatSpec.Core.Raux.Rlt_bool]
          simpa [input, mxp, binaryPositiveOfNat_spec, Binary.B2R] using hlt
        have hbranch : SF2R 2 z =
              FloatSpec.Core.Generic_fmt.roundR 2
                (FLT_exp (3 - emax - prec) prec) (rnd_of_mode mode)
                  (Real.sqrt input) ∧
            is_finite_SF z = true ∧ sign_SF z = false := by
          have h := haux.2
          simpa [z, hsqrt_sign, hltInput] using h
        have hout : Bsqrt mode
              (BinarySingleNaNFloat.B754_finite false mx ex hmx Hx) =
            standardFloatToBinarySingleNaNFloat z hvalid := by
          rfl
        rw [hout]
        refine ⟨?_, ?_, ?_⟩
        · rw [B2R_SF2B z hvalid]
          simpa [input, B2R, binarySingleNaNFloatToB754, B754_to_R] using
            hbranch.1
        · simpa using hbranch.2.1
        · intro _
          rw [Bsign_SF2B z hvalid]
          exact hbranch.2.2
      · have hneg : B2R
            (BinarySingleNaNFloat.B754_finite true mx ex hmx Hx) < 0 := by
          have hmxInt : (0 : Int) < (mx : Int) := by exact_mod_cast hmx
          change F2R (FloatSpec.Core.Defs.FlocqFloat.mk (-(mx : Int)) ex :
            FloatSpec.Core.Defs.FlocqFloat 2) < 0
          exact FloatSpec.Core.Float_prop.F2R_lt_0
            (beta:=2)
            (f:=FloatSpec.Core.Defs.FlocqFloat.mk (-(mx : Int)) ex)
            (by norm_num) (neg_neg_of_pos hmxInt)
        have hsqrt0 : Real.sqrt (B2R
            (BinarySingleNaNFloat.B754_finite true mx ex hmx Hx)) = 0 :=
          Real.sqrt_eq_zero_of_nonpos (le_of_lt hneg)
        rw [show Bsqrt mode
            (BinarySingleNaNFloat.B754_finite true mx ex hmx Hx) =
              BinarySingleNaNFloat.B754_nan by rfl,
          hsqrt0, Binary.roundR_zero_of_mode]
        simp [B2R, Bsign, is_finite, is_nan, binarySingleNaNFloatToB754,
          B754_to_R, BSN_sign, BSN_is_finite, BSN_is_nan]

end BinarySingleNaN
