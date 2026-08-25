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

private instance instPrimPrecGt0 : Prec_gt_0 primPrec :=
  ⟨by norm_num [primPrec]⟩

private instance instPrimPrecLtEmax : Prec_lt_emax primPrec primEmax :=
  ⟨by
    norm_num [primPrec, primEmax],
   by
    norm_num [primEmax]⟩

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
  ⟨StandardFloat.S754_finite false 4503599627370496 (-52), by native_decide⟩

def two : PrimitiveFloat :=
  ⟨StandardFloat.S754_finite false 4503599627370496 (-51), by native_decide⟩

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
    one = B2Prim
      (BinarySingleNaNFloat.B754_finite
        (prec := primPrec) (emax := primEmax) false 4503599627370496 (-52)
        (by norm_num) (by native_decide)) := by
  apply primitiveFloat_ext
  rfl

theorem two_equiv :
    two = B2Prim
      (BinarySingleNaNFloat.B754_finite
        (prec := primPrec) (emax := primEmax) false 4503599627370496 (-51)
        (by norm_num) (by native_decide)) := by
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

noncomputable def SFcompare (x y : StandardFloat) : Ordering :=
  if SFltb x y then Ordering.lt
  else if SFltb y x then Ordering.gt
  else Ordering.eq

noncomputable def eqb (x y : PrimitiveFloat) : Bool :=
  SFeqb (Prim2SF x) (Prim2SF y)

noncomputable def ltb (x y : PrimitiveFloat) : Bool :=
  SFltb (Prim2SF x) (Prim2SF y)

noncomputable def leb (x y : PrimitiveFloat) : Bool :=
  SFleb (Prim2SF x) (Prim2SF y)

noncomputable def compare (x y : PrimitiveFloat) : Ordering :=
  SFcompare (Prim2SF x) (Prim2SF y)

noncomputable def Beqb (x y : PrimBinaryFloat) : Bool :=
  SFeqb (B2SF x) (B2SF y)

noncomputable def Bltb (x y : PrimBinaryFloat) : Bool :=
  SFltb (B2SF x) (B2SF y)

noncomputable def Bleb (x y : PrimBinaryFloat) : Bool :=
  SFleb (B2SF x) (B2SF y)

noncomputable def Bcompare (x y : PrimBinaryFloat) : Ordering :=
  SFcompare (B2SF x) (B2SF y)

theorem compare_equiv (x y : PrimitiveFloat) :
    compare x y = Bcompare (Prim2B x) (Prim2B y) := by
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

def to_Z (x : t) : Int :=
  Int.ofNat x.toNat

end Uint63

namespace Z

def of_N (n : Nat) : Int :=
  Int.ofNat n

end Z

def normfr_mantissa (x : PrimitiveFloat) : Uint63.t :=
  ⟨SFnormfr_mantissa primPrec (Prim2SF x)⟩

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
          simpa [SFdiv, px, py, binaryPositiveOfNat_spec] using haux.1

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
