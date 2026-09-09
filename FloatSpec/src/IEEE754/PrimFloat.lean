-- Primitive floating-point operations
-- Translated from Coq file: flocq/src/IEEE754/PrimFloat.v

import FloatSpec.src.IEEE754.Binary
import FloatSpec.src.IEEE754.BinarySingleNaN
import FloatSpec.src.IEEE754.Bits
import FloatSpec.src.SimprocWP
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Classical
open Std.Do

namespace FaithfulPrimFloat

/-!
Proof-carrying model of Coq's primitive binary64 floats.  This is the only
PrimFloat model in the module: every value retains its `StandardFloat`
constructor (including NaN, infinities, and signed zero) together with the
binary64 validity proof required by Flocq's conversion layer.
-/

abbrev primPrec : Int := 53

abbrev primEmax : Int := 1024

-- Coq `FloatOps.shift = 2 * emax + prec`, used to encode the signed frexp
-- exponent in an unsigned 63-bit word.
abbrev shift : Int := 2 * primEmax + primPrec

private theorem primPrecGt0Witness : Prec_gt_0 primPrec :=
  ⟨by norm_num [primPrec]⟩

private theorem primPrecLtEmaxWitness : Prec_lt_emax primPrec primEmax :=
  ⟨by norm_num [primPrec, primEmax]⟩

-- These mirror Coq's `Local Instance Hprec` and `Local Instance Hmax`.
-- Keeping the registrations local prevents importing this module from
-- silently installing binary64 witnesses in an unrelated caller's instance
-- search, while all declarations below still elaborate with the witnesses.
local instance : Prec_gt_0 primPrec := primPrecGt0Witness

local instance : Prec_lt_emax primPrec primEmax := primPrecLtEmaxWitness

-- Coq's local binary64 instances, retained under their source names so the
-- extracted interface has a direct correspondence.
abbrev Hprec : Prec_gt_0 primPrec := primPrecGt0Witness

abbrev Hmax : Prec_lt_emax primPrec primEmax := primPrecLtEmaxWitness

private instance instPrimFLTExpMonotone :
    FloatSpec.Core.Generic_fmt.Monotone_exp
      (FLT_exp (3 - primEmax - primPrec) primPrec) := by
  simpa [FLT_exp] using
    (inferInstance :
      FloatSpec.Core.Generic_fmt.Monotone_exp
        (FloatSpec.Core.FLT.FLT_exp primPrec (3 - primEmax - primPrec)))

abbrev PrimBinaryFloat := BinarySingleNaNFloat primPrec primEmax

structure PrimitiveFloat where
  toStandardFloat : StandardFloat
  valid :
    validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax)
      toStandardFloat = true

def Prim2SF (x : PrimitiveFloat) : StandardFloat :=
  x.toStandardFloat

theorem Prim2SF_valid (x : PrimitiveFloat) :
    validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax)
      (Prim2SF x) = true :=
  x.valid

private def canonicalNaN : PrimitiveFloat :=
  ⟨StandardFloat.S754_nan, rfl⟩

def SF2Prim (x : StandardFloat) : PrimitiveFloat :=
  if hx : validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax) x = true then
    ⟨x, hx⟩
  else
    canonicalNaN

def SF2B (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax) x = true) :
    PrimBinaryFloat :=
  standardFloatToBinarySingleNaNFloat (prec := primPrec) (emax := primEmax) x hx

def B2SF (x : PrimBinaryFloat) : StandardFloat :=
  binarySingleNaNFloatToStandardFloat (prec := primPrec) (emax := primEmax) x

theorem B2SF_valid (x : PrimBinaryFloat) :
    validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax)
      (B2SF x) = true :=
  validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat
    (prec := primPrec) (emax := primEmax) x

-- Flocq `PrimFloat.v:Prim2B`.
def Prim2B (x : PrimitiveFloat) : PrimBinaryFloat :=
  SF2B (Prim2SF x) (Prim2SF_valid x)

-- Flocq `PrimFloat.v:B2Prim`.
def B2Prim (x : PrimBinaryFloat) : PrimitiveFloat :=
  SF2Prim (B2SF x)

theorem Prim2SF_SF2Prim (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax) x = true) :
    Prim2SF (SF2Prim x) = x := by
  simp [Prim2SF, SF2Prim, hx]

theorem SF2Prim_Prim2SF (x : PrimitiveFloat) :
    SF2Prim (Prim2SF x) = x := by
  rcases x with ⟨x, hx⟩
  simp [SF2Prim, Prim2SF, hx]

theorem B2SF_SF2B (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax) x = true) :
    B2SF (SF2B x hx) = x := by
  exact
    binarySingleNaNFloatToStandardFloat_standardFloatToBinarySingleNaNFloat
      (prec := primPrec) (emax := primEmax) x hx

private theorem B2SF_zero (s : Bool) :
    B2SF (BinarySingleNaNFloat.B754_zero (prec:=primPrec) (emax:=primEmax) s) =
      StandardFloat.S754_zero s :=
  rfl

private theorem B2SF_infinity (s : Bool) :
    B2SF (BinarySingleNaNFloat.B754_infinity (prec:=primPrec) (emax:=primEmax) s) =
      StandardFloat.S754_infinity s :=
  rfl

private theorem B2SF_nan :
    B2SF (BinarySingleNaNFloat.B754_nan (prec:=primPrec) (emax:=primEmax)) =
      StandardFloat.S754_nan :=
  rfl

private theorem B2SF_finite (s : Bool) (m : Nat) (e : Int)
    (hm : 0 < m) (hbounded : specFloat_bounded (prec:=primPrec) (emax:=primEmax) m e = true) :
    B2SF (BinarySingleNaNFloat.B754_finite (prec:=primPrec) (emax:=primEmax)
      s m e hm hbounded) = StandardFloat.S754_finite s m e :=
  rfl

theorem SF2B_B2SF (x : PrimBinaryFloat) :
    SF2B (B2SF x) (B2SF_valid x) = x := by
  exact
    standardFloatToBinarySingleNaNFloat_binarySingleNaNFloatToStandardFloat
      (prec := primPrec) (emax := primEmax) x

theorem B2Prim_Prim2B (x : PrimitiveFloat) :
    B2Prim (Prim2B x) = x := by
  rcases x with ⟨x, hx⟩
  simp [B2Prim, Prim2B, B2SF, SF2B, Prim2SF, SF2Prim, hx,
    binarySingleNaNFloatToStandardFloat_standardFloatToBinarySingleNaNFloat]

theorem Prim2B_B2Prim (x : PrimBinaryFloat) :
    Prim2B (B2Prim x) = x := by
  have hB2Prim :
      B2Prim x = ⟨B2SF x, B2SF_valid x⟩ := by
    simp [B2Prim, SF2Prim, B2SF_valid]
  rw [hB2Prim]
  simpa [Prim2B, Prim2SF] using SF2B_B2SF x

theorem Prim2B_inj (x y : PrimitiveFloat)
    (h : Prim2B x = Prim2B y) : x = y := by
  have h' := congrArg B2Prim h
  simpa [B2Prim_Prim2B] using h'

theorem B2SF_Prim2B (x : PrimitiveFloat) :
    B2SF (Prim2B x) = Prim2SF x := by
  exact B2SF_SF2B (Prim2SF x) (Prim2SF_valid x)

private theorem primitiveFloat_ext (x y : PrimitiveFloat)
    (h : Prim2SF x = Prim2SF y) : x = y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  simp [Prim2SF] at h
  subst y
  rfl

private theorem primBinaryFloat_ext (x y : PrimBinaryFloat)
    (h : B2Prim x = B2Prim y) : x = y := by
  have h' := congrArg Prim2B h
  simpa [Prim2B_B2Prim] using h'

private theorem primBinaryFloat_ext_sf (x y : PrimBinaryFloat)
    (h : B2SF x = B2SF y) : x = y := by
  cases x <;> cases y <;>
    simp_all [B2SF, binarySingleNaNFloatToStandardFloat]

/-! Source-visible primitive constants.  Unlike the removed real projection,
these are pairwise distinguishable wherever IEEE-754 distinguishes them. -/

def infinity : PrimitiveFloat :=
  ⟨StandardFloat.S754_infinity false, rfl⟩

def neg_infinity : PrimitiveFloat :=
  ⟨StandardFloat.S754_infinity true, rfl⟩

def nan : PrimitiveFloat := canonicalNaN

def zero : PrimitiveFloat :=
  ⟨StandardFloat.S754_zero false, rfl⟩

def neg_zero : PrimitiveFloat :=
  ⟨StandardFloat.S754_zero true, rfl⟩

def one : PrimitiveFloat :=
  ⟨StandardFloat.S754_finite false 4503599627370496 (-52), by decide⟩

-- Coq `BinarySingleNaN.Bone`, specialized to binary64.  Keep this model value
-- independent from the primitive `one`; the equivalence theorem below relates
-- the two representations instead of defining one through the other.
def Bone : PrimBinaryFloat :=
  BinarySingleNaNFloat.B754_finite
    (prec := primPrec) (emax := primEmax) false 4503599627370496 (-52)
    (by norm_num) (by decide)

theorem infinity_equiv :
    infinity = B2Prim
      (BinarySingleNaNFloat.B754_infinity
        (prec := primPrec) (emax := primEmax) false) := by
  apply primitiveFloat_ext
  rfl

theorem neg_infinity_equiv :
    neg_infinity = B2Prim
      (BinarySingleNaNFloat.B754_infinity
        (prec := primPrec) (emax := primEmax) true) := by
  apply primitiveFloat_ext
  rfl

theorem nan_equiv :
    nan = B2Prim
      (BinarySingleNaNFloat.B754_nan
        (prec := primPrec) (emax := primEmax)) := by
  apply primitiveFloat_ext
  rfl

theorem zero_equiv :
    zero = B2Prim
      (BinarySingleNaNFloat.B754_zero
        (prec := primPrec) (emax := primEmax) false) := by
  apply primitiveFloat_ext
  rfl

theorem neg_zero_equiv :
    neg_zero = B2Prim
      (BinarySingleNaNFloat.B754_zero
        (prec := primPrec) (emax := primEmax) true) := by
  apply primitiveFloat_ext
  rfl

theorem one_equiv :
    one = B2Prim Bone := by
  apply primitiveFloat_ext
  rfl

def SFopp : StandardFloat → StandardFloat
  | StandardFloat.S754_zero s => StandardFloat.S754_zero (!s)
  | StandardFloat.S754_infinity s => StandardFloat.S754_infinity (!s)
  | StandardFloat.S754_nan => StandardFloat.S754_nan
  | StandardFloat.S754_finite s m e => StandardFloat.S754_finite (!s) m e

def SFabs : StandardFloat → StandardFloat
  | StandardFloat.S754_zero _ => StandardFloat.S754_zero false
  | StandardFloat.S754_infinity _ => StandardFloat.S754_infinity false
  | StandardFloat.S754_nan => StandardFloat.S754_nan
  | StandardFloat.S754_finite _ m e => StandardFloat.S754_finite false m e

theorem SFopp_valid (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat
      (prec := primPrec) (emax := primEmax) x = true) :
    validBinarySingleNaNStandardFloat
      (prec := primPrec) (emax := primEmax) (SFopp x) = true := by
  cases x <;> simpa [SFopp, validBinarySingleNaNStandardFloat] using hx

theorem SFabs_valid (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat
      (prec := primPrec) (emax := primEmax) x = true) :
    validBinarySingleNaNStandardFloat
      (prec := primPrec) (emax := primEmax) (SFabs x) = true := by
  cases x <;> simpa [SFabs, validBinarySingleNaNStandardFloat] using hx

def opp (x : PrimitiveFloat) : PrimitiveFloat :=
  ⟨SFopp (Prim2SF x), SFopp_valid (Prim2SF x) (Prim2SF_valid x)⟩

instance : Neg PrimitiveFloat where
  neg := opp

def abs (x : PrimitiveFloat) : PrimitiveFloat :=
  ⟨SFabs (Prim2SF x), SFabs_valid (Prim2SF x) (Prim2SF_valid x)⟩

def Bopp (x : PrimBinaryFloat) : PrimBinaryFloat :=
  match x with
  | BinarySingleNaNFloat.B754_zero s =>
      BinarySingleNaNFloat.B754_zero (!s)
  | BinarySingleNaNFloat.B754_infinity s =>
      BinarySingleNaNFloat.B754_infinity (!s)
  | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_finite s m e hm hb =>
      BinarySingleNaNFloat.B754_finite (!s) m e hm hb

def Babs (x : PrimBinaryFloat) : PrimBinaryFloat :=
  match x with
  | BinarySingleNaNFloat.B754_zero _ =>
      BinarySingleNaNFloat.B754_zero false
  | BinarySingleNaNFloat.B754_infinity _ =>
      BinarySingleNaNFloat.B754_infinity false
  | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_finite _ m e hm hb =>
      BinarySingleNaNFloat.B754_finite false m e hm hb

theorem opp_equiv (x : PrimitiveFloat) :
    Prim2B (-x) = Bopp (Prim2B x) := by
  apply primBinaryFloat_ext_sf
  rw [B2SF_Prim2B]
  change SFopp (Prim2SF x) = B2SF (Bopp (Prim2B x))
  rw [← B2SF_Prim2B x]
  cases Prim2B x <;> rfl

theorem abs_equiv (x : PrimitiveFloat) :
    Prim2B (abs x) = Babs (Prim2B x) := by
  apply primBinaryFloat_ext_sf
  rw [B2SF_Prim2B]
  change SFabs (Prim2SF x) = B2SF (Babs (Prim2B x))
  rw [← B2SF_Prim2B x]
  cases Prim2B x <;> rfl

def is_nan (x : PrimitiveFloat) : Bool :=
  is_nan_SF (Prim2SF x)

def is_zero (x : PrimitiveFloat) : Bool :=
  match Prim2SF x with
  | StandardFloat.S754_zero _ => true
  | _ => false

def is_infinity (x : PrimitiveFloat) : Bool :=
  match Prim2SF x with
  | StandardFloat.S754_infinity _ => true
  | _ => false

def is_finite (x : PrimitiveFloat) : Bool :=
  is_finite_SF (Prim2SF x)

def get_sign (x : PrimitiveFloat) : Bool :=
  sign_SF (Prim2SF x)

def Bis_nan (x : PrimBinaryFloat) : Bool :=
  match x with
  | BinarySingleNaNFloat.B754_nan => true
  | _ => false

def Bis_zero (x : PrimBinaryFloat) : Bool :=
  match x with
  | BinarySingleNaNFloat.B754_zero _ => true
  | _ => false

def Bis_infinity (x : PrimBinaryFloat) : Bool :=
  match x with
  | BinarySingleNaNFloat.B754_infinity _ => true
  | _ => false

def Bis_finite (x : PrimBinaryFloat) : Bool :=
  match x with
  | BinarySingleNaNFloat.B754_zero _ => true
  | BinarySingleNaNFloat.B754_finite _ _ _ _ _ => true
  | _ => false

def Bsign (x : PrimBinaryFloat) : Bool :=
  match x with
  | BinarySingleNaNFloat.B754_zero s => s
  | BinarySingleNaNFloat.B754_infinity s => s
  | BinarySingleNaNFloat.B754_nan => false
  | BinarySingleNaNFloat.B754_finite s _ _ _ _ => s

theorem is_nan_equiv (x : PrimitiveFloat) :
    is_nan x = Bis_nan (Prim2B x) := by
  unfold is_nan
  rw [← B2SF_Prim2B x]
  cases Prim2B x <;> rfl

theorem is_zero_equiv (x : PrimitiveFloat) :
    is_zero x = Bis_zero (Prim2B x) := by
  unfold is_zero
  rw [← B2SF_Prim2B x]
  cases Prim2B x <;> rfl

theorem is_infinity_equiv (x : PrimitiveFloat) :
    is_infinity x = Bis_infinity (Prim2B x) := by
  unfold is_infinity
  rw [← B2SF_Prim2B x]
  cases Prim2B x <;> rfl

theorem is_finite_equiv (x : PrimitiveFloat) :
    is_finite x = Bis_finite (Prim2B x) := by
  unfold is_finite
  rw [← B2SF_Prim2B x]
  cases Prim2B x <;> rfl

theorem get_sign_equiv (x : PrimitiveFloat) :
    get_sign x = Bsign (Prim2B x) := by
  unfold get_sign
  rw [← B2SF_Prim2B x]
  cases Prim2B x <;> rfl

-- IEEE comparisons: NaN is unordered, infinities remain ordered, and the two
-- zero constructors compare equal through their common real value.
noncomputable def SFeqb (x y : StandardFloat) : Bool :=
  match x, y with
  | StandardFloat.S754_nan, _ => false
  | _, StandardFloat.S754_nan => false
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => sx == sy
  | StandardFloat.S754_infinity _, _ => false
  | _, StandardFloat.S754_infinity _ => false
  | x, y => decide (SF2R 2 x = SF2R 2 y)

noncomputable def SFltb (x y : StandardFloat) : Bool :=
  match x, y with
  | StandardFloat.S754_nan, _ => false
  | _, StandardFloat.S754_nan => false
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => sx && !sy
  | StandardFloat.S754_infinity sx, _ => sx
  | _, StandardFloat.S754_infinity sy => !sy
  | x, y => decide (SF2R 2 x < SF2R 2 y)

noncomputable def SFleb (x y : StandardFloat) : Bool :=
  SFltb x y || SFeqb x y

noncomputable def SFcompare (x y : StandardFloat) : Option Ordering :=
  match x, y with
  | StandardFloat.S754_nan, _ => none
  | _, StandardFloat.S754_nan => none
  | x, y =>
      if SFltb x y then some Ordering.lt
      else if SFltb y x then some Ordering.gt
      else some Ordering.eq

/-! Coq's primitive comparison has four observable outcomes.  In particular,
NaN is `FNotComparable`; it must not be collapsed into ordinary equality. -/

inductive float_comparison where
  | FNotComparable
  | FEq
  | FLt
  | FGt
deriving DecidableEq, Repr

abbrev FNotComparable : float_comparison :=
  float_comparison.FNotComparable

abbrev FEq : float_comparison :=
  float_comparison.FEq

abbrev FLt : float_comparison :=
  float_comparison.FLt

abbrev FGt : float_comparison :=
  float_comparison.FGt

-- Coq `FloatAxioms.flatten_cmp_opt`.
def flatten_cmp_opt : Option Ordering → float_comparison
  | none => FNotComparable
  | some Ordering.eq => FEq
  | some Ordering.lt => FLt
  | some Ordering.gt => FGt

noncomputable def eqb (x y : PrimitiveFloat) : Bool :=
  SFeqb (Prim2SF x) (Prim2SF y)

noncomputable def ltb (x y : PrimitiveFloat) : Bool :=
  SFltb (Prim2SF x) (Prim2SF y)

noncomputable def leb (x y : PrimitiveFloat) : Bool :=
  SFleb (Prim2SF x) (Prim2SF y)

noncomputable def compare (x y : PrimitiveFloat) : float_comparison :=
  flatten_cmp_opt (SFcompare (Prim2SF x) (Prim2SF y))

noncomputable def Beqb (x y : PrimBinaryFloat) : Bool :=
  SFeqb (B2SF x) (B2SF y)

noncomputable def Bltb (x y : PrimBinaryFloat) : Bool :=
  SFltb (B2SF x) (B2SF y)

noncomputable def Bleb (x y : PrimBinaryFloat) : Bool :=
  SFleb (B2SF x) (B2SF y)

noncomputable def Bcompare (x y : PrimBinaryFloat) : Option Ordering :=
  SFcompare (B2SF x) (B2SF y)

theorem compare_equiv (x y : PrimitiveFloat) :
    compare x y = flatten_cmp_opt (Bcompare (Prim2B x) (Prim2B y)) := by
  simp [compare, Bcompare, B2SF_Prim2B]

theorem eqb_equiv (x y : PrimitiveFloat) :
    eqb x y = Beqb (Prim2B x) (Prim2B y) := by
  simp [eqb, Beqb, B2SF_Prim2B]

theorem ltb_equiv (x y : PrimitiveFloat) :
    ltb x y = Bltb (Prim2B x) (Prim2B y) := by
  simp [ltb, Bltb, B2SF_Prim2B]

theorem leb_equiv (x y : PrimitiveFloat) :
    leb x y = Bleb (Prim2B x) (Prim2B y) := by
  simp [leb, Bleb, B2SF_Prim2B]

namespace Uint63

structure t where
  toNat : Nat
  isLt : toNat < 2 ^ 63

def to_Z (x : t) : Int :=
  Int.ofNat x.toNat

def ofInt (z : Int) (h0 : 0 ≤ z) (hlt : z < (2 : Int) ^ 63) : t :=
  ⟨z.toNat, by
    have hz : (z.toNat : Int) = z := Int.toNat_of_nonneg h0
    exact_mod_cast (hz ▸ hlt)⟩

theorem to_Z_ofInt (z : Int) (h0 : 0 ≤ z) (hlt : z < (2 : Int) ^ 63) :
    to_Z (ofInt z h0 hlt) = z := by
  exact Int.toNat_of_nonneg h0

end Uint63

namespace Z

def of_N (n : Nat) : Int :=
  Int.ofNat n

end Z

private theorem Bnormfr_mantissa_lt_uint63 (x : PrimBinaryFloat) :
    BinarySingleNaNFloat.Bnormfr_mantissa x < 2 ^ 63 := by
  cases x with
  | B754_zero s => norm_num [BinarySingleNaNFloat.Bnormfr_mantissa,
      SFnormfr_mantissa, binarySingleNaNFloatToStandardFloat]
  | B754_infinity s => norm_num [BinarySingleNaNFloat.Bnormfr_mantissa,
      SFnormfr_mantissa, binarySingleNaNFloatToStandardFloat]
  | B754_nan => norm_num [BinarySingleNaNFloat.Bnormfr_mantissa,
      SFnormfr_mantissa, binarySingleNaNFloatToStandardFloat]
  | B754_finite s m e hm hb =>
      have hrange := range_bounded_of_specFloat_bounded
        (prec := primPrec) (emax := primEmax) m e hm hb
      have hm_lt : m < 2 ^ primPrec.toNat := by
        have hrange' :
            (m < 2 ^ primPrec.toNat ∧
              3 - primEmax - primPrec ≤ e) ∧ e ≤ primEmax - primPrec := by
          simpa [bounded, Bool.and_eq_true] using hrange
        exact hrange'.1.1
      simp only [BinarySingleNaNFloat.Bnormfr_mantissa,
        binarySingleNaNFloatToStandardFloat, SFnormfr_mantissa]
      split
      · have hp : (2 : Nat) ^ 53 < 2 ^ 63 := by norm_num
        exact lt_trans hm_lt (by simpa [primPrec] using hp)
      · norm_num

private theorem SFnormfr_mantissa_lt_uint63 (x : PrimitiveFloat) :
    SFnormfr_mantissa primPrec (Prim2SF x) < 2 ^ 63 := by
  have h := Bnormfr_mantissa_lt_uint63 (Prim2B x)
  change SFnormfr_mantissa primPrec (B2SF (Prim2B x)) < 2 ^ 63 at h
  rw [B2SF_Prim2B] at h
  exact h

def normfr_mantissa (x : PrimitiveFloat) : Uint63.t :=
  ⟨SFnormfr_mantissa primPrec (Prim2SF x), SFnormfr_mantissa_lt_uint63 x⟩

theorem normfr_mantissa_spec (x : PrimitiveFloat) :
    Uint63.to_Z (normfr_mantissa x) =
      Z.of_N (SFnormfr_mantissa primPrec (Prim2SF x)) := by
  rfl

-- Coq `PrimFloat.v:normfr_mantissa_equiv`.
theorem normfr_mantissa_equiv (x : PrimitiveFloat) :
    Uint63.to_Z (normfr_mantissa x) =
      Z.of_N (BinarySingleNaNFloat.Bnormfr_mantissa (Prim2B x)) := by
  rw [normfr_mantissa_spec]
  rw [← B2SF_Prim2B x]
  cases Prim2B x <;> simp [Z.of_N, B2SF, BinarySingleNaNFloat.Bnormfr_mantissa,
    SFnormfr_mantissa, binarySingleNaNFloatToStandardFloat]

private def specRoundNearestEven (m : Int) (l : Loc) : Int :=
  FloatSpec.Calc.Round.cond_incr
    (FloatSpec.Calc.Round.round_N (!(decide (2 ∣ m))) l) m

private theorem specRoundNearestEven_eq_choiceMode
    (s : Bool) (m : Int) (l : Loc) :
    specRoundNearestEven m l = choice_mode RoundingMode.RNE s m l := by
  cases l with
  | loc_Exact => rfl
  | loc_Inexact c =>
      cases c <;> simp [specRoundNearestEven, choice_mode,
        FloatSpec.Calc.Round.cond_incr, FloatSpec.Calc.Round.round_N]

-- Coq `PrimFloat.v:round_nearest_even_equiv`.
theorem round_nearest_even_equiv (s : Bool) (m : Int) (l : Loc) :
    specRoundNearestEven m l = choice_mode RoundingMode.RNE s m l :=
  specRoundNearestEven_eq_choiceMode s m l

-- Coq `SpecFloat.binary_round_aux`, specialized to primitive binary64.
noncomputable def binary_round_aux (sx : Bool) (mx ex : Int) (lx : Loc) :
    StandardFloat :=
  let first := bsn_shr_fexp (prec:=primPrec) (emax:=primEmax) mx ex lx
  let roundedMant :=
    specRoundNearestEven first.1.shr_m (loc_of_shr_record first.1)
  let second := bsn_shr_fexp (prec:=primPrec) (emax:=primEmax)
    roundedMant first.2 FloatSpec.Calc.Bracket.Location.loc_Exact
  if second.1.shr_m = 0 then
    StandardFloat.S754_zero sx
  else if 0 < second.1.shr_m then
    binary_fit_aux (prec:=primPrec) (emax:=primEmax)
      RoundingMode.RNE sx second.1.shr_m.toNat second.2
  else
    StandardFloat.S754_nan

-- Coq `PrimFloat.v:binary_round_aux_equiv`.
theorem binary_round_aux_equiv (sx : Bool) (mx ex : Int) (lx : Loc) :
    binary_round_aux sx mx ex lx =
      _root_.binary_round_aux (prec:=primPrec) (emax:=primEmax)
        RoundingMode.RNE sx mx ex lx := by
  unfold binary_round_aux _root_.binary_round_aux
  simp (config := { zeta := true })
    [specRoundNearestEven_eq_choiceMode sx]

theorem Prim2SF_B2Prim (x : PrimBinaryFloat) :
    Prim2SF (B2Prim x) = B2SF x := by
  unfold B2Prim
  exact Prim2SF_SF2Prim (B2SF x) (B2SF_valid x)

theorem Prim2SF_inj (x y : PrimitiveFloat)
    (h : Prim2SF x = Prim2SF y) : x = y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  simp [Prim2SF] at h
  subst y
  rfl

theorem B2Prim_inj (x y : PrimBinaryFloat)
    (h : B2Prim x = B2Prim y) : x = y := by
  have h' := congrArg Prim2B h
  simpa [Prim2B_B2Prim] using h'

-- Coq `SpecFloat.SFmul`, specialized to primitive binary64.
noncomputable def SFmul (x y : StandardFloat) : StandardFloat :=
  match x, y with
  | StandardFloat.S754_nan, _ => StandardFloat.S754_nan
  | _, StandardFloat.S754_nan => StandardFloat.S754_nan
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy =>
      StandardFloat.S754_infinity (Bool.xor sx sy)
  | StandardFloat.S754_infinity sx, StandardFloat.S754_finite sy _ _ =>
      StandardFloat.S754_infinity (Bool.xor sx sy)
  | StandardFloat.S754_finite sx _ _, StandardFloat.S754_infinity sy =>
      StandardFloat.S754_infinity (Bool.xor sx sy)
  | StandardFloat.S754_infinity _, StandardFloat.S754_zero _ =>
      StandardFloat.S754_nan
  | StandardFloat.S754_zero _, StandardFloat.S754_infinity _ =>
      StandardFloat.S754_nan
  | StandardFloat.S754_finite sx _ _, StandardFloat.S754_zero sy =>
      StandardFloat.S754_zero (Bool.xor sx sy)
  | StandardFloat.S754_zero sx, StandardFloat.S754_finite sy _ _ =>
      StandardFloat.S754_zero (Bool.xor sx sy)
  | StandardFloat.S754_zero sx, StandardFloat.S754_zero sy =>
      StandardFloat.S754_zero (Bool.xor sx sy)
  | StandardFloat.S754_finite sx mx ex,
      StandardFloat.S754_finite sy my ey =>
      binary_round_aux (Bool.xor sx sy) ((mx * my : Nat) : Int) (ex + ey)
        FloatSpec.Calc.Bracket.Location.loc_Exact

theorem SFmul_valid (x y : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax) x = true)
    (hy : validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax) y = true) :
    validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax)
      (SFmul x y) = true := by
  cases x with
  | S754_zero sx =>
      cases y <;> simp [SFmul, validBinarySingleNaNStandardFloat]
  | S754_infinity sx =>
      cases y <;> simp [SFmul, validBinarySingleNaNStandardFloat]
  | S754_nan =>
      cases y <;> simp [SFmul, validBinarySingleNaNStandardFloat]
  | S754_finite sx mx ex =>
      cases y with
      | S754_zero sy =>
          simp [SFmul, validBinarySingleNaNStandardFloat]
      | S754_infinity sy =>
          simp [SFmul, validBinarySingleNaNStandardFloat]
      | S754_nan =>
          simp [SFmul, validBinarySingleNaNStandardFloat]
      | S754_finite sy my ey =>
          have hx' : decide (0 < mx) = true ∧
              specFloat_bounded (prec := primPrec) (emax := primEmax) mx ex = true := by
            simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hx
          have hy' : decide (0 < my) = true ∧
              specFloat_bounded (prec := primPrec) (emax := primEmax) my ey = true := by
            simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hy
          have haux := _root_.Bmult_correct_aux (prec:=primPrec) (emax:=primEmax)
            RoundingMode.RNE sx mx ex (of_decide_eq_true hx'.1) hx'.2
            sy my ey (of_decide_eq_true hy'.1) hy'.2
          simpa [SFmul, binary_round_aux_equiv] using haux.1

-- Coq primitive multiplication, independently defined through `Prim2SF`.
noncomputable def mul (x y : PrimitiveFloat) : PrimitiveFloat :=
  ⟨SFmul (Prim2SF x) (Prim2SF y),
    SFmul_valid (Prim2SF x) (Prim2SF y) (Prim2SF_valid x) (Prim2SF_valid y)⟩

noncomputable instance : Mul PrimitiveFloat where
  mul := FaithfulPrimFloat.mul

theorem mul_spec (x y : PrimitiveFloat) :
    Prim2SF (x * y) = SFmul (Prim2SF x) (Prim2SF y) := by
  rfl

-- Coq `BinarySingleNaN.Bmult`, specialized to primitive binary64.
noncomputable def Bmult (mode : RoundingMode)
    (x y : PrimBinaryFloat) : PrimBinaryFloat :=
  match x, y with
  | BinarySingleNaNFloat.B754_nan, _ => BinarySingleNaNFloat.B754_nan
  | _, BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity sx, BinarySingleNaNFloat.B754_infinity sy =>
      BinarySingleNaNFloat.B754_infinity (prec:=primPrec) (emax:=primEmax) (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_infinity sx, BinarySingleNaNFloat.B754_finite sy _ _ _ _ =>
      BinarySingleNaNFloat.B754_infinity (prec:=primPrec) (emax:=primEmax) (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_finite sx _ _ _ _, BinarySingleNaNFloat.B754_infinity sy =>
      BinarySingleNaNFloat.B754_infinity (prec:=primPrec) (emax:=primEmax) (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_infinity _, BinarySingleNaNFloat.B754_zero _ =>
      BinarySingleNaNFloat.B754_nan (prec:=primPrec) (emax:=primEmax)
  | BinarySingleNaNFloat.B754_zero _, BinarySingleNaNFloat.B754_infinity _ =>
      BinarySingleNaNFloat.B754_nan (prec:=primPrec) (emax:=primEmax)
  | BinarySingleNaNFloat.B754_finite sx _ _ _ _, BinarySingleNaNFloat.B754_zero sy =>
      BinarySingleNaNFloat.B754_zero (prec:=primPrec) (emax:=primEmax) (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_zero sx, BinarySingleNaNFloat.B754_finite sy _ _ _ _ =>
      BinarySingleNaNFloat.B754_zero (prec:=primPrec) (emax:=primEmax) (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_zero sx, BinarySingleNaNFloat.B754_zero sy =>
      BinarySingleNaNFloat.B754_zero (prec:=primPrec) (emax:=primEmax) (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_finite sx mx ex hmx_pos Hx,
      BinarySingleNaNFloat.B754_finite sy my ey hmy_pos Hy =>
      let z := _root_.binary_round_aux (prec:=primPrec) (emax:=primEmax)
        mode (Bool.xor sx sy) ((mx * my : Nat) : Int) (ex + ey)
        FloatSpec.Calc.Bracket.Location.loc_Exact
      have haux := _root_.Bmult_correct_aux (prec:=primPrec) (emax:=primEmax)
        mode sx mx ex hmx_pos Hx sy my ey hmy_pos Hy
      SF2B z haux.1

-- Coq `PrimFloat.v:mul_equiv`.
theorem mul_equiv (x y : PrimitiveFloat) :
    Prim2B (x * y) = Bmult RoundingMode.RNE (Prim2B x) (Prim2B y) := by
  apply B2Prim_inj
  rw [B2Prim_Prim2B]
  apply Prim2SF_inj
  rw [Prim2SF_B2Prim]
  rw [mul_spec]
  rw [← B2SF_Prim2B x, ← B2SF_Prim2B y]
  cases Prim2B x <;> cases Prim2B y <;>
    simp [SFmul, Bmult, B2SF_SF2B, B2SF_zero, B2SF_infinity, B2SF_nan,
      B2SF_finite, binary_round_aux_equiv]

-- Coq `SpecFloat.SFdiv`, specialized to primitive binary64.
noncomputable def SFdiv (x y : StandardFloat) : StandardFloat :=
  match x, y with
  | StandardFloat.S754_nan, _ => StandardFloat.S754_nan
  | _, StandardFloat.S754_nan => StandardFloat.S754_nan
  | StandardFloat.S754_infinity _, StandardFloat.S754_infinity _ =>
      StandardFloat.S754_nan
  | StandardFloat.S754_zero _, StandardFloat.S754_zero _ =>
      StandardFloat.S754_nan
  | StandardFloat.S754_infinity sx, StandardFloat.S754_zero sy =>
      StandardFloat.S754_infinity (Bool.xor sx sy)
  | StandardFloat.S754_infinity sx, StandardFloat.S754_finite sy _ _ =>
      StandardFloat.S754_infinity (Bool.xor sx sy)
  | StandardFloat.S754_zero sx, StandardFloat.S754_infinity sy =>
      StandardFloat.S754_zero (Bool.xor sx sy)
  | StandardFloat.S754_finite sx _ _, StandardFloat.S754_infinity sy =>
      StandardFloat.S754_zero (Bool.xor sx sy)
  | StandardFloat.S754_finite sx _ _, StandardFloat.S754_zero sy =>
      StandardFloat.S754_infinity (Bool.xor sx sy)
  | StandardFloat.S754_zero sx, StandardFloat.S754_finite sy _ _ =>
      StandardFloat.S754_zero (Bool.xor sx sy)
  | StandardFloat.S754_finite sx mx ex,
      StandardFloat.S754_finite sy my ey =>
      let result := SFdiv_core_binary primPrec primEmax (mx : Int) ex (my : Int) ey
      binary_round_aux (Bool.xor sx sy) result.1 result.2.1 result.2.2

theorem SFdiv_valid (x y : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat
      (prec := primPrec) (emax := primEmax) x = true)
    (hy : validBinarySingleNaNStandardFloat
      (prec := primPrec) (emax := primEmax) y = true) :
    validBinarySingleNaNStandardFloat
      (prec := primPrec) (emax := primEmax) (SFdiv x y) = true := by
  cases x with
  | S754_zero sx =>
      cases y <;> simp [SFdiv, validBinarySingleNaNStandardFloat]
  | S754_infinity sx =>
      cases y <;> simp [SFdiv, validBinarySingleNaNStandardFloat]
  | S754_nan =>
      cases y <;> simp [SFdiv, validBinarySingleNaNStandardFloat]
  | S754_finite sx mx ex =>
      cases y with
      | S754_zero sy =>
          simp [SFdiv, validBinarySingleNaNStandardFloat]
      | S754_infinity sy =>
          simp [SFdiv, validBinarySingleNaNStandardFloat]
      | S754_nan =>
          simp [SFdiv, validBinarySingleNaNStandardFloat]
      | S754_finite sy my ey =>
          have hx' : decide (0 < mx) = true ∧
              specFloat_bounded (prec := primPrec) (emax := primEmax) mx ex = true := by
            simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hx
          have hy' : decide (0 < my) = true ∧
              specFloat_bounded (prec := primPrec) (emax := primEmax) my ey = true := by
            simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hy
          let px := binaryPositiveOfNat mx (of_decide_eq_true hx'.1)
          let py := binaryPositiveOfNat my (of_decide_eq_true hy'.1)
          have haux := _root_.Bdiv_correct_aux
            (prec := primPrec) (emax := primEmax) RoundingMode.RNE
            sx px ex sy py ey
          simpa [SFdiv, px, py, binaryPositiveOfNat_spec,
            binary_round_aux_equiv] using haux.1

noncomputable def div (x y : PrimitiveFloat) : PrimitiveFloat :=
  ⟨SFdiv (Prim2SF x) (Prim2SF y),
    SFdiv_valid (Prim2SF x) (Prim2SF y) (Prim2SF_valid x) (Prim2SF_valid y)⟩

noncomputable instance : Div PrimitiveFloat where
  div := FaithfulPrimFloat.div

theorem div_spec (x y : PrimitiveFloat) :
    Prim2SF (x / y) = SFdiv (Prim2SF x) (Prim2SF y) := by
  rfl

noncomputable def Bdiv (mode : RoundingMode)
    (x y : PrimBinaryFloat) : PrimBinaryFloat :=
  match x, y with
  | BinarySingleNaNFloat.B754_nan, _ => BinarySingleNaNFloat.B754_nan
  | _, BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity _, BinarySingleNaNFloat.B754_infinity _ =>
      BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_zero _, BinarySingleNaNFloat.B754_zero _ =>
      BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity sx, BinarySingleNaNFloat.B754_zero sy =>
      BinarySingleNaNFloat.B754_infinity (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_infinity sx,
      BinarySingleNaNFloat.B754_finite sy _ _ _ _ =>
      BinarySingleNaNFloat.B754_infinity (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_zero sx, BinarySingleNaNFloat.B754_infinity sy =>
      BinarySingleNaNFloat.B754_zero (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_finite sx _ _ _ _,
      BinarySingleNaNFloat.B754_infinity sy =>
      BinarySingleNaNFloat.B754_zero (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_finite sx _ _ _ _,
      BinarySingleNaNFloat.B754_zero sy =>
      BinarySingleNaNFloat.B754_infinity (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_zero sx,
      BinarySingleNaNFloat.B754_finite sy _ _ _ _ =>
      BinarySingleNaNFloat.B754_zero (Bool.xor sx sy)
  | BinarySingleNaNFloat.B754_finite sx mx ex hmx hbx,
      BinarySingleNaNFloat.B754_finite sy my ey hmy hby =>
      let result := SFdiv_core_binary primPrec primEmax (mx : Int) ex (my : Int) ey
      have haux := _root_.Bdiv_correct_aux
        (prec := primPrec) (emax := primEmax) mode
        sx (binaryPositiveOfNat mx hmx) ex sy (binaryPositiveOfNat my hmy) ey
      SF2B
        (_root_.binary_round_aux (prec := primPrec) (emax := primEmax)
          mode (Bool.xor sx sy) result.1 result.2.1 result.2.2)
        (by simpa [binaryPositiveOfNat_spec] using haux.1)

theorem div_equiv (x y : PrimitiveFloat) :
    Prim2B (x / y) = Bdiv RoundingMode.RNE (Prim2B x) (Prim2B y) := by
  apply primBinaryFloat_ext_sf
  rw [B2SF_Prim2B, div_spec]
  rw [← B2SF_Prim2B x, ← B2SF_Prim2B y]
  cases Prim2B x <;> cases Prim2B y <;>
    simp [SFdiv, Bdiv, B2SF_SF2B, B2SF_zero, B2SF_infinity, B2SF_nan,
      B2SF_finite, binary_round_aux_equiv, binaryPositiveOfNat_spec]

-- Embed the source SingleNaN carrier into Flocq's payload-carrying binary64
-- carrier. The unique source NaN uses Flocq's canonical binary64 payload and
-- is immediately collapsed again after the operation.
private def BSN2Binary64 : PrimBinaryFloat → binary64
  | BinarySingleNaNFloat.B754_zero s =>
      binary_float.B754_zero (prec := primPrec) (emax := primEmax) s
  | BinarySingleNaNFloat.B754_infinity s =>
      binary_float.B754_infinity (prec := primPrec) (emax := primEmax) s
  | BinarySingleNaNFloat.B754_nan => default_nan_pl64.1
  | BinarySingleNaNFloat.B754_finite s m e hm hb =>
      binary_float.B754_finite (prec := primPrec) (emax := primEmax) s
        (binaryPositiveOfNat m hm) e (by
          simpa [binaryPositiveOfNat_spec] using hb)

private theorem binaryFloatToBSN_BSN2Binary64 (x : PrimBinaryFloat) :
    binaryFloatToBinarySingleNaNFloat (BSN2Binary64 x) = x := by
  cases x <;>
    simp [BSN2Binary64, default_nan_pl64, binaryFloatToBinarySingleNaNFloat,
      binaryPositiveOfNat_spec]

-- Coq `PrimFloat.sqrt` is the primitive binary64 square-root operation. Its
-- model is Flocq `BinarySingleNaN.Bsqrt mode_NE`; the payload bridge above is
-- observationally exact because that source carrier has exactly one NaN.
noncomputable def Bsqrt (mode : RoundingMode)
    (x : PrimBinaryFloat) : PrimBinaryFloat :=
  binaryFloatToBinarySingleNaNFloat
    (b64_sqrt mode (BSN2Binary64 x))

noncomputable def sqrt (x : PrimitiveFloat) : PrimitiveFloat :=
  B2Prim (Bsqrt RoundingMode.RNE (Prim2B x))

theorem sqrt_equiv (x : PrimitiveFloat) :
    Prim2B (sqrt x) = Bsqrt RoundingMode.RNE (Prim2B x) := by
  exact Prim2B_B2Prim _

-- Coq `SpecFloat.binary_round`, specialized to primitive binary64.  The
-- mantissa stays on Coq's nonzero `positive` domain; converting this binder to
-- `Nat` would silently admit the source-impossible input zero.
noncomputable def binary_round (sx : Bool)
    (mx : FloatSpec.Core.Zaux.Positive) (ex : Int) :
    StandardFloat :=
  let mxNat := FloatSpec.Core.Zaux.positiveToNat mx
  let aligned := shl_align_fexp (prec:=primPrec) (emax:=primEmax) mxNat ex
  binary_round_aux sx (aligned.1 : Int) aligned.2
    FloatSpec.Calc.Bracket.Location.loc_Exact

-- Coq `PrimFloat.v:binary_round_equiv`.
theorem binary_round_equiv (sx : Bool)
    (mx : FloatSpec.Core.Zaux.Positive) (ex : Int) :
    binary_round sx mx ex =
      _root_.binary_round (prec:=primPrec) (emax:=primEmax)
        RoundingMode.RNE sx (FloatSpec.Core.Zaux.positiveToNat mx) ex := by
  simp only [binary_round, _root_.binary_round]
  exact binary_round_aux_equiv _ _ _ _

private theorem rootBinaryRoundValid (mode : RoundingMode)
    (sx : Bool) (mx : Nat) (ex : Int)
    (hmx_pos : 0 < mx) :
    validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax)
      (_root_.binary_round (prec := primPrec) (emax := primEmax)
        mode sx mx ex) = true :=
  (_root_.binary_round_correct (prec := primPrec) (emax := primEmax)
    mode sx mx ex hmx_pos).1

-- Coq `SpecFloat.binary_normalize`, specialized to primitive binary64.
noncomputable def binary_normalize (m e : Int) (szero : Bool) :
    StandardFloat :=
  if hzero : m = 0 then
    StandardFloat.S754_zero szero
  else if hpos : 0 < m then
    have hm_toNat_pos : 0 < m.toNat := by
      have hcast : (0 : Int) < (m.toNat : Int) := by
        simpa [Int.toNat_of_nonneg (le_of_lt hpos)] using hpos
      exact_mod_cast hcast
    binary_round false (binaryPositiveOfNat m.toNat hm_toNat_pos) e
  else
    have hm_abs_pos : 0 < m.natAbs := Int.natAbs_pos.mpr hzero
    binary_round true (binaryPositiveOfNat m.natAbs hm_abs_pos) e

-- Coq `BinarySingleNaN.binary_normalize`, specialized to primitive binary64.
noncomputable def binary_normalize_bsn (mode : RoundingMode)
    (m e : Int) (szero : Bool) :
    PrimBinaryFloat :=
  if hzero : m = 0 then
    BinarySingleNaNFloat.B754_zero (prec := primPrec) (emax := primEmax) szero
  else if hpos : 0 < m then
    have hm_toNat_pos : 0 < m.toNat := by
      have hcast : (0 : Int) < (m.toNat : Int) := by
        simpa [Int.toNat_of_nonneg (le_of_lt hpos)] using hpos
      exact_mod_cast hcast
    SF2B
      (_root_.binary_round (prec := primPrec) (emax := primEmax)
        mode false m.toNat e)
      (rootBinaryRoundValid mode false m.toNat e hm_toNat_pos)
  else
    have hm_ne : m ≠ 0 := by
      intro h
      exact hzero h
    have hm_abs_pos : 0 < m.natAbs := Int.natAbs_pos.mpr hm_ne
    SF2B
      (_root_.binary_round (prec := primPrec) (emax := primEmax)
        mode true m.natAbs e)
      (rootBinaryRoundValid mode true m.natAbs e hm_abs_pos)

-- Coq `PrimFloat.v:binary_normalize_equiv`.
theorem binary_normalize_equiv (m e : Int) (szero : Bool) :
    binary_normalize m e szero =
      B2SF (binary_normalize_bsn RoundingMode.RNE m e szero) := by
  unfold binary_normalize binary_normalize_bsn
  by_cases hzero : m = 0
  · simp [hzero, B2SF, binarySingleNaNFloatToStandardFloat]
  · by_cases hpos : 0 < m
    · simp [hzero, hpos, B2SF_SF2B, binary_round_equiv,
        binaryPositiveOfNat_spec]
    · simp [hzero, hpos, B2SF_SF2B, binary_round_equiv,
        binaryPositiveOfNat_spec]

noncomputable def of_uint63 (i : Uint63.t) : PrimitiveFloat :=
  B2Prim
    (binary_normalize_bsn RoundingMode.RNE (Uint63.to_Z i) 0 false)

theorem of_int63_equiv (i : Uint63.t) :
    Prim2B (of_uint63 i) =
      binary_normalize_bsn RoundingMode.RNE (Uint63.to_Z i) 0 false := by
  exact Prim2B_B2Prim _

-- Coq `SpecFloat.SFldexp`, specialized to primitive binary64.
noncomputable def SFldexp (x : StandardFloat) (e : Int) : StandardFloat :=
  match x with
  | StandardFloat.S754_finite s m ex =>
      if hm : 0 < m then
        binary_round s (binaryPositiveOfNat m hm) (ex + e)
      else
        StandardFloat.S754_nan
  | _ => x

theorem SFldexp_valid (x : StandardFloat) (e : Int)
    (hx : validBinarySingleNaNStandardFloat
      (prec := primPrec) (emax := primEmax) x = true) :
    validBinarySingleNaNStandardFloat
      (prec := primPrec) (emax := primEmax) (SFldexp x e) = true := by
  cases x with
  | S754_zero s => simpa [SFldexp] using hx
  | S754_infinity s => simpa [SFldexp] using hx
  | S754_nan => simpa [SFldexp] using hx
  | S754_finite s m ex =>
      have hx' : decide (0 < m) = true ∧
          specFloat_bounded (prec := primPrec) (emax := primEmax) m ex = true := by
        simpa [validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hx
      have hm : 0 < m := of_decide_eq_true hx'.1
      rw [show SFldexp (StandardFloat.S754_finite s m ex) e =
          binary_round s (binaryPositiveOfNat m hm) (ex + e) by
        simp [SFldexp, hm]]
      rw [binary_round_equiv]
      simpa [binaryPositiveOfNat_spec] using
        rootBinaryRoundValid RoundingMode.RNE s m (ex + e) hm

noncomputable def ldexp (x : PrimitiveFloat) (e : Int) : PrimitiveFloat :=
  ⟨SFldexp (Prim2SF x) e,
    SFldexp_valid (Prim2SF x) e (Prim2SF_valid x)⟩

namespace Z

noncomputable def ldexp (x : PrimitiveFloat) (e : Int) : PrimitiveFloat :=
  FaithfulPrimFloat.ldexp x e

end Z

noncomputable def Bldexp (mode : RoundingMode)
    (x : PrimBinaryFloat) (e : Int) : PrimBinaryFloat :=
  match x with
  | BinarySingleNaNFloat.B754_finite s m ex hm _ =>
      SF2B
        (_root_.binary_round (prec := primPrec) (emax := primEmax)
          mode s m (ex + e))
        (rootBinaryRoundValid mode s m (ex + e) hm)
  | _ => x

theorem ldexp_equiv (x : PrimitiveFloat) (e : Int) :
    Prim2B (Z.ldexp x e) =
      Bldexp RoundingMode.RNE (Prim2B x) e := by
  apply primBinaryFloat_ext_sf
  rw [B2SF_Prim2B]
  change SFldexp (Prim2SF x) e = B2SF (Bldexp RoundingMode.RNE (Prim2B x) e)
  rw [← B2SF_Prim2B x]
  cases Prim2B x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => rfl
  | B754_finite s m ex hm hb =>
      rw [B2SF_finite]
      simp [SFldexp, Bldexp, hm, B2SF_SF2B, binary_round_equiv,
        binaryPositiveOfNat_spec]

-- Coq `BinarySingleNaN.Bfrexp`, specialized to binary64.  Non-finite values
-- use Flocq's exact sentinel exponent `-2 * emax - prec = -2101`.
noncomputable def Bfrexp (x : PrimBinaryFloat) : PrimBinaryFloat × Int :=
  match x with
  | BinarySingleNaNFloat.B754_finite s m e _ _ =>
      let result := ExperimentalSingleNaNArithmetic.Ffrexp_core_binary
        (prec := primPrec) (emax := primEmax) s m e
      (standardFloatToBinarySingleNaNFloat'
        (prec := primPrec) (emax := primEmax) result.1, result.2)
  | _ => (x, -2 * primEmax - primPrec)

namespace Z

noncomputable def frexp (x : PrimitiveFloat) : PrimitiveFloat × Int :=
  let result := Bfrexp (Prim2B x)
  (B2Prim result.1, result.2)

end Z

theorem frexp_equiv (x : PrimitiveFloat) :
    let result := Z.frexp x
    (Prim2B result.1, result.2) = Bfrexp (Prim2B x) := by
  unfold Z.frexp
  cases h : Bfrexp (Prim2B x) with
  | mk m e =>
      simp [h, Prim2B_B2Prim]

private theorem Bfrexp_shifted_exp_range (x : PrimBinaryFloat) :
    0 ≤ (Bfrexp x).2 + shift ∧
      (Bfrexp x).2 + shift < (2 : Int) ^ 63 := by
  cases x with
  | B754_zero s => norm_num [Bfrexp, shift, primEmax, primPrec]
  | B754_infinity s => norm_num [Bfrexp, shift, primEmax, primPrec]
  | B754_nan => norm_num [Bfrexp, shift, primEmax, primPrec]
  | B754_finite s m e hm hb =>
      have hrange := range_bounded_of_specFloat_bounded
        (prec := primPrec) (emax := primEmax) m e hm hb
      have hrange' :
          (m < 2 ^ primPrec.toNat ∧
            3 - primEmax - primPrec ≤ e) ∧ e ≤ primEmax - primPrec := by
        simpa [bounded, Bool.and_eq_true] using hrange
      have hemin : (-1074 : Int) ≤ e := by
        have := hrange'.1.2
        norm_num [primPrec, primEmax] at this ⊢
        exact this
      have hemax : e ≤ (971 : Int) := by
        have := hrange'.2
        norm_num [primPrec, primEmax] at this ⊢
        exact this
      have hdigits_pos : 0 < FloatSpec.Core.Digits.digits2_pos m := by
        simp [FloatSpec.Core.Digits.digits2_pos]
      have hfirst :
          FloatSpec.Core.Zaux.Zlt_bool (-primPrec)
            (3 - primEmax - primPrec) = false := by
        decide
      unfold Bfrexp
      dsimp only
      unfold ExperimentalSingleNaNArithmetic.Ffrexp_core_binary
      rw [hfirst]
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hdigits :
          53 ≤ FloatSpec.Core.Digits.digits2_pos m
      · simp [hdigits, shift, primPrec, primEmax]
        omega
      · have hdigits_lt : FloatSpec.Core.Digits.digits2_pos m < 53 := by
          omega
        simp [hdigits, shift, primPrec, primEmax]
        omega

noncomputable def ldshiftexp
    (x : PrimitiveFloat) (e : Uint63.t) : PrimitiveFloat :=
  Z.ldexp x (Uint63.to_Z e - shift)

theorem ldshiftexp_equiv (x : PrimitiveFloat) (e : Uint63.t) :
    Prim2B (ldshiftexp x e) =
      Bldexp RoundingMode.RNE (Prim2B x) (Uint63.to_Z e - shift) := by
  exact ldexp_equiv x (Uint63.to_Z e - shift)

noncomputable def frshiftexp
    (x : PrimitiveFloat) : PrimitiveFloat × Uint63.t :=
  let result := Bfrexp (Prim2B x)
  let hrange := Bfrexp_shifted_exp_range (Prim2B x)
  (B2Prim result.1,
    Uint63.ofInt (result.2 + shift) hrange.1 hrange.2)

theorem frshiftexp_equiv (x : PrimitiveFloat) :
    let result := frshiftexp x
    (Prim2B result.1, Uint63.to_Z result.2 - shift) =
      Bfrexp (Prim2B x) := by
  unfold frshiftexp
  dsimp only
  rw [Uint63.to_Z_ofInt]
  simp [Prim2B_B2Prim]

noncomputable def Bulp' (x : PrimBinaryFloat) : PrimBinaryFloat :=
  Bldexp RoundingMode.RNE Bone
    (FLT_exp (3 - primEmax - primPrec) primPrec (Bfrexp x).2)

noncomputable def ulp (x : PrimitiveFloat) : PrimitiveFloat :=
  B2Prim (Bulp' (Prim2B x))

theorem ulp_equiv (x : PrimitiveFloat) :
    Prim2B (ulp x) = Bulp' (Prim2B x) := by
  exact Prim2B_B2Prim _

private theorem minSubnormalBounded :
    specFloat_bounded (prec := primPrec) (emax := primEmax)
      1 (3 - primEmax - primPrec) = true := by
  decide

private theorem maxFiniteBounded :
    specFloat_bounded (prec := primPrec) (emax := primEmax)
      (2 ^ primPrec.toNat - 1) (primEmax - primPrec) = true := by
  decide

noncomputable def Bsucc (x : PrimBinaryFloat) : PrimBinaryFloat :=
  match x with
  | BinarySingleNaNFloat.B754_zero _ =>
      BinarySingleNaNFloat.B754_finite false 1
        (3 - primEmax - primPrec) (by norm_num) minSubnormalBounded
  | BinarySingleNaNFloat.B754_infinity false => x
  | BinarySingleNaNFloat.B754_infinity true =>
      BinarySingleNaNFloat.B754_finite true
        (2 ^ primPrec.toNat - 1) (primEmax - primPrec)
        (by decide) maxFiniteBounded
  | BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_finite false m e hm _ =>
      SF2B
        (_root_.binary_round (prec := primPrec) (emax := primEmax)
          RoundingMode.RTP false (m + 1) e)
        (rootBinaryRoundValid RoundingMode.RTP false (m + 1) e (by omega))
  | BinarySingleNaNFloat.B754_finite true m e hm _ =>
      SF2B
        (_root_.binary_round (prec := primPrec) (emax := primEmax)
          RoundingMode.RTZ true (2 * m - 1) (e - 1))
        (rootBinaryRoundValid RoundingMode.RTZ true (2 * m - 1) (e - 1)
          (by omega))

noncomputable def Bpred (x : PrimBinaryFloat) : PrimBinaryFloat :=
  Bopp (Bsucc (Bopp x))

noncomputable def next_up (x : PrimitiveFloat) : PrimitiveFloat :=
  B2Prim (Bsucc (Prim2B x))

noncomputable def next_down (x : PrimitiveFloat) : PrimitiveFloat :=
  B2Prim (Bpred (Prim2B x))

theorem next_up_equiv (x : PrimitiveFloat) :
    Prim2B (next_up x) = Bsucc (Prim2B x) := by
  exact Prim2B_B2Prim _

theorem next_down_equiv (x : PrimitiveFloat) :
    Prim2B (next_down x) = Bpred (Prim2B x) := by
  exact Prim2B_B2Prim _

-- Coq `SpecFloat.SFadd`, specialized to primitive binary64.
noncomputable def SFadd (x y : StandardFloat) : StandardFloat :=
  match x, y with
  | StandardFloat.S754_nan, _ => StandardFloat.S754_nan
  | _, StandardFloat.S754_nan => StandardFloat.S754_nan
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy =>
      if sx == sy then x else StandardFloat.S754_nan
  | StandardFloat.S754_infinity _, _ => x
  | _, StandardFloat.S754_infinity _ => y
  | StandardFloat.S754_zero sx, StandardFloat.S754_zero sy =>
      if sx == sy then x else StandardFloat.S754_zero false
  | StandardFloat.S754_zero _, _ => y
  | _, StandardFloat.S754_zero _ => x
  | StandardFloat.S754_finite sx mx ex,
      StandardFloat.S754_finite sy my ey =>
      let ez := min ex ey
      binary_normalize (Fplus_naive sx mx ex sy my ey ez) ez false

theorem SFadd_valid (x y : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax) x = true)
    (hy : validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax) y = true) :
    validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax)
      (SFadd x y) = true := by
  cases x with
  | S754_zero sx =>
      cases y with
      | S754_zero sy =>
          by_cases h : sx = sy <;> simp [SFadd, h, validBinarySingleNaNStandardFloat]
      | S754_infinity sy =>
          simp [SFadd, validBinarySingleNaNStandardFloat]
      | S754_nan =>
          simp [SFadd, validBinarySingleNaNStandardFloat]
      | S754_finite sy my ey =>
          simpa [SFadd, validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hy
  | S754_infinity sx =>
      cases y with
      | S754_zero sy =>
          simp [SFadd, validBinarySingleNaNStandardFloat]
      | S754_infinity sy =>
          by_cases h : sx = sy <;> simp [SFadd, h, validBinarySingleNaNStandardFloat]
      | S754_nan =>
          simp [SFadd, validBinarySingleNaNStandardFloat]
      | S754_finite sy my ey =>
          simp [SFadd, validBinarySingleNaNStandardFloat]
  | S754_nan =>
      cases y <;> simp [SFadd, validBinarySingleNaNStandardFloat]
  | S754_finite sx mx ex =>
      cases y with
      | S754_zero sy =>
          simpa [SFadd, validBinarySingleNaNStandardFloat, Bool.and_eq_true] using hx
      | S754_infinity sy =>
          simp [SFadd, validBinarySingleNaNStandardFloat]
      | S754_nan =>
          simp [SFadd, validBinarySingleNaNStandardFloat]
      | S754_finite sy my ey =>
          change validBinarySingleNaNStandardFloat
            (binary_normalize (Fplus_naive sx mx ex sy my ey (min ex ey))
              (min ex ey) false) = true
          rw [binary_normalize_equiv]
          exact B2SF_valid (binary_normalize_bsn RoundingMode.RNE
            (Fplus_naive sx mx ex sy my ey (min ex ey)) (min ex ey) false)

-- Coq primitive addition, independently defined through `Prim2SF`.
noncomputable def add (x y : PrimitiveFloat) : PrimitiveFloat :=
  ⟨SFadd (Prim2SF x) (Prim2SF y),
    SFadd_valid (Prim2SF x) (Prim2SF y) (Prim2SF_valid x) (Prim2SF_valid y)⟩

noncomputable instance : Add PrimitiveFloat where
  add := FaithfulPrimFloat.add

theorem add_spec (x y : PrimitiveFloat) :
    Prim2SF (x + y) = SFadd (Prim2SF x) (Prim2SF y) := by
  rfl

-- Coq `BinarySingleNaN.Bplus`, specialized to primitive binary64.
noncomputable def Bplus (mode : RoundingMode)
    (x y : PrimBinaryFloat) : PrimBinaryFloat :=
  match x, y with
  | BinarySingleNaNFloat.B754_nan, _ => BinarySingleNaNFloat.B754_nan
  | _, BinarySingleNaNFloat.B754_nan => BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity sx, BinarySingleNaNFloat.B754_infinity sy =>
      if sx == sy then x else BinarySingleNaNFloat.B754_nan
  | BinarySingleNaNFloat.B754_infinity _, _ => x
  | _, BinarySingleNaNFloat.B754_infinity _ => y
  | BinarySingleNaNFloat.B754_zero sx, BinarySingleNaNFloat.B754_zero sy =>
      if sx == sy then x
      else
        match mode with
        | RoundingMode.RTN =>
            BinarySingleNaNFloat.B754_zero (prec:=primPrec) (emax:=primEmax) true
        | _ =>
            BinarySingleNaNFloat.B754_zero (prec:=primPrec) (emax:=primEmax) false
  | BinarySingleNaNFloat.B754_zero _, _ => y
  | _, BinarySingleNaNFloat.B754_zero _ => x
  | BinarySingleNaNFloat.B754_finite sx mx ex _ _,
      BinarySingleNaNFloat.B754_finite sy my ey _ _ =>
      let ez := min ex ey
      let szero :=
        match mode with
        | RoundingMode.RTN => true
        | _ => false
      binary_normalize_bsn mode (Fplus_naive sx mx ex sy my ey ez) ez szero

-- Coq `PrimFloat.v:add_equiv`.
theorem add_equiv (x y : PrimitiveFloat) :
    Prim2B (x + y) = Bplus RoundingMode.RNE (Prim2B x) (Prim2B y) := by
  apply B2Prim_inj
  rw [B2Prim_Prim2B]
  apply Prim2SF_inj
  rw [Prim2SF_B2Prim]
  rw [add_spec]
  rw [← B2SF_Prim2B x, ← B2SF_Prim2B y]
  cases Prim2B x <;> cases Prim2B y <;>
    simp [SFadd, Bplus, B2SF_zero, B2SF_infinity, B2SF_nan,
      B2SF_finite, binary_normalize_equiv] <;>
      split_ifs <;> rfl

-- Coq's primitive literal `two`, expressed through the independently defined
-- primitive binary64 addition.  `two_equiv` below is then derived from the
-- operation equivalence rather than from a duplicated model-side constant.
noncomputable def two : PrimitiveFloat :=
  one + one

theorem two_equiv :
    two = B2Prim (Bplus RoundingMode.RNE Bone Bone) := by
  have hbone : Prim2B one = Bone := by
    have h := congrArg Prim2B one_equiv
    simpa [Prim2B_B2Prim] using h
  rw [← B2Prim_Prim2B two]
  apply congrArg B2Prim
  simpa [two, hbone] using add_equiv one one

noncomputable def sub (x y : PrimitiveFloat) : PrimitiveFloat :=
  x + (-y)

noncomputable instance : Sub PrimitiveFloat where
  sub := FaithfulPrimFloat.sub

noncomputable def Bminus (mode : RoundingMode)
    (x y : PrimBinaryFloat) : PrimBinaryFloat :=
  Bplus mode x (Bopp y)

theorem sub_equiv (x y : PrimitiveFloat) :
    Prim2B (x - y) = Bminus RoundingMode.RNE (Prim2B x) (Prim2B y) := by
  change Prim2B (x + (-y)) = Bplus RoundingMode.RNE (Prim2B x) (Bopp (Prim2B y))
  rw [add_equiv, opp_equiv]

end FaithfulPrimFloat

/-! Direct compatibility with Lean's binary64 logical and native carriers. -/

namespace FloatSpec.IEEE754.Native

private theorem modelSignOfBool_not (s : Bool) :
    modelSignOfBool (!s) = -modelSignOfBool s := by cases s <;> rfl

theorem model64OfStandardFloat_SFopp (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) x = true) :
    model64OfStandardFloat (FaithfulPrimFloat.SFopp x) =
      Float.Model.neg (model64OfStandardFloat x) := by
  unfold Float.Model.neg
  rw [unpack_model64OfStandardFloat x hx]
  cases x <;> simp_all [model64OfStandardFloat, FaithfulPrimFloat.SFopp,
    unpackedOfStandardFloat, Float.Model.UnpackedFloat.neg, modelSignOfBool_not,
    validBinarySingleNaNStandardFloat]

theorem model32OfStandardFloat_SFopp (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 24) (emax := 128) x = true) :
    model32OfStandardFloat (FaithfulPrimFloat.SFopp x) =
      Float32.Model.neg (model32OfStandardFloat x) := by
  unfold Float32.Model.neg
  rw [unpack_model32OfStandardFloat x hx]
  cases x <;> simp_all [model32OfStandardFloat, FaithfulPrimFloat.SFopp,
    unpackedOfStandardFloat, Float.Model.UnpackedFloat.neg, modelSignOfBool_not,
    validBinarySingleNaNStandardFloat]

theorem model64OfStandardFloat_SFabs (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) x = true) :
    model64OfStandardFloat (FaithfulPrimFloat.SFabs x) =
      Float.Model.abs (model64OfStandardFloat x) := by
  unfold Float.Model.abs
  rw [unpack_model64OfStandardFloat x hx]
  cases x <;> simp_all [model64OfStandardFloat, FaithfulPrimFloat.SFabs,
    unpackedOfStandardFloat, Float.Model.UnpackedFloat.abs, modelSignOfBool,
    validBinarySingleNaNStandardFloat]

theorem model32OfStandardFloat_SFabs (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 24) (emax := 128) x = true) :
    model32OfStandardFloat (FaithfulPrimFloat.SFabs x) =
      Float32.Model.abs (model32OfStandardFloat x) := by
  unfold Float32.Model.abs
  rw [unpack_model32OfStandardFloat x hx]
  cases x <;> simp_all [model32OfStandardFloat, FaithfulPrimFloat.SFabs,
    unpackedOfStandardFloat, Float.Model.UnpackedFloat.abs, modelSignOfBool,
    validBinarySingleNaNStandardFloat]

end FloatSpec.IEEE754.Native

namespace FaithfulPrimFloat

namespace PrimitiveFloat

/-- The Lean binary64 logical model of a proof-carrying FLoCq primitive float. -/
def toModel (x : FaithfulPrimFloat.PrimitiveFloat) : Float.Model :=
  FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat (Prim2B x)

/-- The native Lean float represented by a proof-carrying FLoCq primitive float. -/
def toFloat (x : FaithfulPrimFloat.PrimitiveFloat) : Float :=
  Float.ofModel (toModel x)

/-- Decode a Lean binary64 logical model through the FLoCq single-NaN carrier. -/
def ofModel (x : Float.Model) : FaithfulPrimFloat.PrimitiveFloat :=
  SF2Prim (FloatSpec.IEEE754.Native.standardFloatOfModel64 x)

@[simp] theorem prim2SF_ofModel (x : Float.Model) :
    Prim2SF (ofModel x) = FloatSpec.IEEE754.Native.standardFloatOfModel64 x := by
  simp [Prim2SF, ofModel, SF2Prim,
    FloatSpec.IEEE754.Native.validStandardFloatOfModel64]

/-- Decode a native Lean float through its logical model. -/
def ofFloat (x : Float) : FaithfulPrimFloat.PrimitiveFloat :=
  ofModel x.toModel

@[simp] theorem toFloat_toModel (x : FaithfulPrimFloat.PrimitiveFloat) :
    (toFloat x).toModel = toModel x := rfl

@[simp] theorem toModel_ofModel (x : Float.Model) :
    toModel (ofModel x) = x := by
  rw [toModel,
    FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat]
  change FloatSpec.IEEE754.Native.model64OfStandardFloat
    (B2SF (Prim2B (ofModel x))) = x
  rw [B2SF_Prim2B, prim2SF_ofModel,
    FloatSpec.IEEE754.Native.model64OfStandardFloat_standardFloatOfModel64]

@[simp] theorem ofModel_toModel (x : FaithfulPrimFloat.PrimitiveFloat) :
    ofModel (toModel x) = x := by
  apply primitiveFloat_ext
  rw [prim2SF_ofModel, toModel,
    FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat]
  change FloatSpec.IEEE754.Native.standardFloatOfModel64
    (FloatSpec.IEEE754.Native.model64OfStandardFloat (B2SF (Prim2B x))) = Prim2SF x
  rw [FloatSpec.IEEE754.Native.standardFloatOfModel64_model64OfStandardFloat
    (B2SF (Prim2B x)) (B2SF_valid (Prim2B x)), B2SF_Prim2B]

@[simp] theorem toModel_neg (x : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (-x) = Float.Model.neg (toModel x) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat (Prim2B (-x)) =
    Float.Model.neg (FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat (Prim2B x))
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat,
    FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat]
  change FloatSpec.IEEE754.Native.model64OfStandardFloat (B2SF (Prim2B (-x))) =
    Float.Model.neg (FloatSpec.IEEE754.Native.model64OfStandardFloat (B2SF (Prim2B x)))
  rw [B2SF_Prim2B, B2SF_Prim2B]
  exact FloatSpec.IEEE754.Native.model64OfStandardFloat_SFopp
    (Prim2SF x) (Prim2SF_valid x)

@[simp] theorem toModel_abs (x : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (FaithfulPrimFloat.abs x) = Float.Model.abs (toModel x) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat
      (Prim2B (FaithfulPrimFloat.abs x)) =
    Float.Model.abs (FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat (Prim2B x))
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat,
    FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat]
  change FloatSpec.IEEE754.Native.model64OfStandardFloat
      (B2SF (Prim2B (FaithfulPrimFloat.abs x))) =
    Float.Model.abs (FloatSpec.IEEE754.Native.model64OfStandardFloat (B2SF (Prim2B x)))
  rw [B2SF_Prim2B, B2SF_Prim2B]
  exact FloatSpec.IEEE754.Native.model64OfStandardFloat_SFabs
    (Prim2SF x) (Prim2SF_valid x)

private theorem unpack_toModel (x : FaithfulPrimFloat.PrimitiveFloat) :
    (toModel x).unpack =
      FloatSpec.IEEE754.Native.unpackedOfBinarySingleNaNFloat (Prim2B x) := by
  rw [toModel,
    FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat]
  rw [FloatSpec.IEEE754.Native.unpack_model64OfStandardFloat
    (binarySingleNaNFloatToStandardFloat (Prim2B x))
    (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat (Prim2B x))]
  exact FloatSpec.IEEE754.Native.unpackedOfStandardFloat_binarySingleNaNFloatToStandardFloat _

@[simp] theorem toModel_isNaN (x : FaithfulPrimFloat.PrimitiveFloat) :
    Float.Model.isNaN (toModel x) = FaithfulPrimFloat.is_nan x := by
  rw [toModel,
    FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat]
  rw [FloatSpec.IEEE754.Native.model64OfStandardFloat_isNaN
    (binarySingleNaNFloatToStandardFloat (Prim2B x))
    (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat (Prim2B x))]
  change is_nan_SF (B2SF (Prim2B x)) = FaithfulPrimFloat.is_nan x
  rw [B2SF_Prim2B]
  rfl

@[simp] theorem toModel_isFinite (x : FaithfulPrimFloat.PrimitiveFloat) :
    Float.Model.isFinite (toModel x) = FaithfulPrimFloat.is_finite x := by
  rw [toModel,
    FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat]
  rw [FloatSpec.IEEE754.Native.model64OfStandardFloat_isFinite
    (binarySingleNaNFloatToStandardFloat (Prim2B x))
    (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat (Prim2B x))]
  change is_finite_SF (B2SF (Prim2B x)) = FaithfulPrimFloat.is_finite x
  rw [B2SF_Prim2B]
  rfl

private theorem Bmult_eq_binarySingleNaN_Bmult (x y : PrimBinaryFloat) :
    FaithfulPrimFloat.Bmult RoundingMode.RNE x y =
      @BinarySingleNaN.Bmult primPrec primEmax primPrecGt0Witness
        primPrecLtEmaxWitness RoundingMode.RNE x y := by
  cases x <;> cases y <;>
    simp [FaithfulPrimFloat.Bmult, BinarySingleNaN.Bmult, SF2B]

@[simp] theorem toModel_mul (x y : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (x * y) = Float.Model.mul (toModel x) (toModel y) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat (Prim2B (x * y)) = _
  rw [FaithfulPrimFloat.mul_equiv, Bmult_eq_binarySingleNaN_Bmult]
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bmult_RNE]
  unfold Float.Model.mul
  rw [unpack_toModel, unpack_toModel]

private theorem standardFloatToBinarySingleNaNFloat_eq_B2BSN
    (z : StandardFloat)
    (hz₁ hz₂ :
      validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax) z = true)
    (hn : is_nan_SF z = false) :
    standardFloatToBinarySingleNaNFloat z hz₁ =
      binaryFloatToBinarySingleNaNFloat
        (Binary.standardFloatToBinaryFloatOfNotNaN z hz₂ hn) := by
  apply primBinaryFloat_ext_sf
  unfold B2SF
  rw [← B2SF_BSN_binarySingleNaNFloatToB754,
    ← B2SF_BSN_binarySingleNaNFloatToB754,
    binarySingleNaNFloatToB754_standardFloatToBinarySingleNaNFloat,
    Binary.binarySingleNaNFloatToB754_standardFloatToBinaryFloatOfNotNaN]

private theorem Bplus_eq_binarySingleNaN_Bplus (x y : PrimBinaryFloat) :
    FaithfulPrimFloat.Bplus RoundingMode.RNE x y =
      @BinarySingleNaN.Bplus primPrec primEmax primPrecGt0Witness
        primPrecLtEmaxWitness RoundingMode.RNE x y := by
  cases x <;> cases y <;>
    simp [FaithfulPrimFloat.Bplus, BinarySingleNaN.Bplus,
      binary_normalize_bsn, Binary.normalize, Binary.B2BSN, SF2B] <;>
    split_ifs
  all_goals first
    | rfl
    | exact standardFloatToBinarySingleNaNFloat_eq_B2BSN _ _ _ _

@[simp] theorem toModel_add (x y : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (x + y) = Float.Model.add (toModel x) (toModel y) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat (Prim2B (x + y)) = _
  rw [FaithfulPrimFloat.add_equiv, Bplus_eq_binarySingleNaN_Bplus]
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bplus_RNE]
  unfold Float.Model.add
  rw [unpack_toModel, unpack_toModel]

private theorem Bopp_eq_binarySingleNaN_Bopp (x : PrimBinaryFloat) :
    FaithfulPrimFloat.Bopp x = BinarySingleNaN.Bopp x := by
  cases x <;> rfl

private theorem Bminus_eq_binarySingleNaN_Bminus (x y : PrimBinaryFloat) :
    FaithfulPrimFloat.Bminus RoundingMode.RNE x y =
      @BinarySingleNaN.Bminus primPrec primEmax primPrecGt0Witness
        primPrecLtEmaxWitness RoundingMode.RNE x y := by
  rw [show FaithfulPrimFloat.Bminus RoundingMode.RNE x y =
      FaithfulPrimFloat.Bplus RoundingMode.RNE x (FaithfulPrimFloat.Bopp y) from rfl,
    show @BinarySingleNaN.Bminus primPrec primEmax primPrecGt0Witness
        primPrecLtEmaxWitness RoundingMode.RNE x y =
      @BinarySingleNaN.Bplus primPrec primEmax primPrecGt0Witness
        primPrecLtEmaxWitness RoundingMode.RNE x (BinarySingleNaN.Bopp y) from rfl,
    Bopp_eq_binarySingleNaN_Bopp, Bplus_eq_binarySingleNaN_Bplus]

@[simp] theorem toModel_sub (x y : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (x - y) = Float.Model.sub (toModel x) (toModel y) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat (Prim2B (x - y)) = _
  rw [FaithfulPrimFloat.sub_equiv, Bminus_eq_binarySingleNaN_Bminus]
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bminus_RNE]
  unfold Float.Model.sub
  rw [unpack_toModel, unpack_toModel]

private theorem Bdiv_eq_binarySingleNaN_Bdiv (x y : PrimBinaryFloat) :
    FaithfulPrimFloat.Bdiv RoundingMode.RNE x y =
      @BinarySingleNaN.Bdiv primPrec primEmax primPrecGt0Witness
        primPrecLtEmaxWitness RoundingMode.RNE x y := by
  cases x <;> cases y <;>
    simp [FaithfulPrimFloat.Bdiv, BinarySingleNaN.Bdiv,
      BinarySingleNaN.Bdiv_finite, SF2B, binaryPositiveOfNat_spec]

@[simp] theorem toModel_div (x y : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (x / y) = Float.Model.div (toModel x) (toModel y) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat (Prim2B (x / y)) = _
  rw [FaithfulPrimFloat.div_equiv, Bdiv_eq_binarySingleNaN_Bdiv]
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bdiv_RNE]
  unfold Float.Model.div
  rw [unpack_toModel, unpack_toModel]

private theorem Bsqrt_eq_binarySingleNaN_Bsqrt (x : PrimBinaryFloat) :
    FaithfulPrimFloat.Bsqrt RoundingMode.RNE x =
      @BinarySingleNaN.Bsqrt primPrec primEmax primPrecGt0Witness
        primPrecLtEmaxWitness RoundingMode.RNE x := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => cases s <;> rfl
  | B754_nan =>
      simp [FaithfulPrimFloat.Bsqrt, b64_sqrt, BSN2Binary64,
        Binary.Bsqrt, BinarySingleNaN.Bsqrt, unop_nan_pl64, default_nan_pl64,
        binaryFloatToBinarySingleNaNFloat]
  | B754_finite s m e hm hb =>
      cases s
      · simp [FaithfulPrimFloat.Bsqrt, b64_sqrt, BSN2Binary64,
          Binary.Bsqrt, BinarySingleNaN.Bsqrt, binaryPositiveOfNat_spec]
        exact (standardFloatToBinarySingleNaNFloat_eq_B2BSN _ _ _ _).symm
      · simp [FaithfulPrimFloat.Bsqrt, b64_sqrt, BSN2Binary64,
          Binary.Bsqrt, BinarySingleNaN.Bsqrt, unop_nan_pl64, default_nan_pl64,
          binaryFloatToBinarySingleNaNFloat]

@[simp] theorem toModel_sqrt (x : FaithfulPrimFloat.PrimitiveFloat) :
    toModel (FaithfulPrimFloat.sqrt x) = Float.Model.sqrt (toModel x) := by
  change FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat
      (Prim2B (FaithfulPrimFloat.sqrt x)) = _
  rw [FaithfulPrimFloat.sqrt_equiv, Bsqrt_eq_binarySingleNaN_Bsqrt]
  rw [FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat_Bsqrt_RNE]
  unfold Float.Model.sqrt
  rw [unpack_toModel]

end PrimitiveFloat

end FaithfulPrimFloat
