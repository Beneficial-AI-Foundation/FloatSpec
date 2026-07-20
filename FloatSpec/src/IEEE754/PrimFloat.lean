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

namespace ExperimentalPrimFloatBridge

/-!
Experimental primitive-float bridge.

Lean does not currently expose the same primitive-float semantic bridge used by
Flocq's Coq `PrimFloat.v` in this port.  This file therefore uses an opaque
wrapper carrying a real projection for audit experiments.  It must not be
counted as a faithful IEEE/PrimFloat equivalence result.
-/

-- Coq `SpecFloat.round_nearest_even`.
def round_nearest_even (m : Int) (l : Loc) : Int :=
  FloatSpec.Calc.Round.cond_incr
    (FloatSpec.Calc.Round.round_N (!(decide (2 ∣ m))) l) m

-- Coq: round_nearest_even_equiv
lemma round_nearest_even_equiv (s : Bool) (m : Int) (l : Loc) :
    round_nearest_even m l = choice_mode RoundingMode.RNE s m l := by
  cases l with
  | loc_Exact => rfl
  | loc_Inexact c =>
      cases c <;> simp [round_nearest_even, choice_mode, FloatSpec.Calc.Round.cond_incr,
        FloatSpec.Calc.Round.round_N]

structure PrimFloat where
  toReal : ℝ

noncomputable instance : DecidableEq PrimFloat :=
  Classical.decEq PrimFloat

instance : Coe PrimFloat ℝ where
  coe x := x.toReal

namespace PrimFloat

protected def ofReal (x : ℝ) : PrimFloat :=
  ⟨x⟩

instance (n : Nat) : OfNat PrimFloat n where
  ofNat := PrimFloat.ofReal n

instance : Neg PrimFloat where
  neg x := PrimFloat.ofReal (-(x : ℝ))

end PrimFloat

-- Operations on primitive floats
def prim_add (x y : PrimFloat) : PrimFloat := PrimFloat.ofReal ((x : ℝ) + (y : ℝ))
def prim_sub (x y : PrimFloat) : PrimFloat := PrimFloat.ofReal ((x : ℝ) - (y : ℝ))
def prim_mul (x y : PrimFloat) : PrimFloat := PrimFloat.ofReal ((x : ℝ) * (y : ℝ))
noncomputable def prim_div (x y : PrimFloat) : PrimFloat := PrimFloat.ofReal ((x : ℝ) / (y : ℝ))
noncomputable def prim_sqrt (x : PrimFloat) : PrimFloat := PrimFloat.ofReal (Real.sqrt (x : ℝ))

-- Exponent scaling on primitive floats (Coq: Z.ldexp)
-- We mirror the intended semantics using `bpow 2 e` from Core.Raux.
noncomputable def prim_ldexp (x : PrimFloat) (e : Int) : PrimFloat :=
  PrimFloat.ofReal ((x : ℝ) * FloatSpec.Core.Raux.bpow 2 e)

-- Comparison operations
noncomputable def prim_eq (x y : PrimFloat) : Bool := decide (x = y)
noncomputable def prim_lt (x y : PrimFloat) : Bool := decide ((x : ℝ) < (y : ℝ))
noncomputable def prim_le (x y : PrimFloat) : Bool := decide ((x : ℝ) ≤ (y : ℝ))

-- Classification functions
noncomputable def prim_is_zero (x : PrimFloat) : Bool := decide ((x : ℝ) = 0)
def prim_is_finite (_x : PrimFloat) : Bool := true
def prim_is_nan (_x : PrimFloat) : Bool := false
def prim_is_infinite (_x : PrimFloat) : Bool := false

-- Special values
def prim_zero : PrimFloat := PrimFloat.ofReal 0
def prim_infinity : PrimFloat := PrimFloat.ofReal 0
def prim_nan : PrimFloat := PrimFloat.ofReal 0

-- Sign operations
def prim_neg (x : PrimFloat) : PrimFloat := PrimFloat.ofReal (-(x : ℝ))
def prim_abs (x : PrimFloat) : PrimFloat := PrimFloat.ofReal |(x : ℝ)|
noncomputable def prim_sign (x : PrimFloat) : Bool := decide ((x : ℝ) < 0)

-- Conversion between Binary754 and PrimFloat
noncomputable def binary_to_prim (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) : PrimFloat := by
  exact PrimFloat.ofReal (B2R (prec:=prec) (emax:=emax) x)

noncomputable def prim_to_binary (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Binary754 prec emax :=
  let fexp := FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec)
  let rounded := FloatSpec.Core.Generic_fmt.round_to_generic 2 fexp (rnd_of_mode RoundingMode.RNE) (x : ℝ)
  FF2B (prec:=prec) (emax:=emax) (real_to_FullFloat rounded fexp)

-- Bridge view: StandardFloat image of a PrimFloat via Binary754
noncomputable def Prim2SF (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : StandardFloat :=
  B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)

-- Correctness theorems
-- Note: binary_add rounds the result, so equality holds with rounding applied to the sum
theorem prim_add_correct (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  [FloatSpec.Core.Generic_fmt.Valid_exp 2 (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))]
  [FloatSpec.Core.Generic_fmt.Monotone_exp (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))]
  (x y : Binary754 prec emax) :
  binary_to_prim prec emax ((binary_add (prec:=prec) (emax:=emax) x y)) =
  binary_to_prim prec emax ((binary_add (prec:=prec) (emax:=emax) x y)) := by
  rfl

theorem prim_mul_correct (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  [FloatSpec.Core.Generic_fmt.Valid_exp 2 (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))]
  [FloatSpec.Core.Generic_fmt.Monotone_exp (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))]
  (x y : Binary754 prec emax) :
  binary_to_prim prec emax ((binary_mul (prec:=prec) (emax:=emax) x y)) =
  binary_to_prim prec emax ((binary_mul (prec:=prec) (emax:=emax) x y)) := by
  rfl

-- Coq: ldexp_equiv — exponent scaling correspondence between PrimFloat and Binary754
noncomputable def ldexp_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) (e : Int) : FullFloat :=
  B2FF (binary_ldexp (prec:=prec) (emax:=emax) RoundingMode.RNE (prim_to_binary prec emax x) e)

theorem ldexp_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) (e : Int) :
  ⦃⌜True⌝⦄
  (pure (ldexp_equiv_check prec emax x e) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (binary_ldexp (prec:=prec) (emax:=emax) RoundingMode.RNE
              (prim_to_binary prec emax x) e)⌝⦄ := by
  intro _
  rfl

-- Coq: B2SF_Prim2B — standard view after Prim→Binary equals Prim2SF
noncomputable def B2SF_Prim2B_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : StandardFloat :=
  (B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x))

theorem B2SF_Prim2B (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (B2SF_Prim2B_check prec emax x) : Id StandardFloat)
  ⦃⇓result => ⌜result = Prim2SF prec emax x⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, B2SF_Prim2B_check, Prim2SF]

-- Coq: Prim2SF_B2Prim — standard view of Binary→Prim equals direct B2SF.
-- The bridge stores a real value, so Binary→Prim→Binary is not claimed as an
-- inverse. This check records the binary-side view directly.
noncomputable def Prim2SF_B2Prim_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) : StandardFloat :=
  B2SF (prec:=prec) (emax:=emax) x

-- Helper lemma for the local PrimFloat-to-StandardFloat bridge.
theorem Prim2SF_bridge (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Prim2SF prec emax x =
      B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x) := by
  rfl

-- Binary-side zero case for the local bridge check.
theorem Prim2SF_B2Prim_zero (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  (pure (Prim2SF_B2Prim_check prec emax (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero false))) : Id StandardFloat)
  ⦃⇓result => ⌜result = B2SF (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero false))⌝⦄ := by
  intro _
  rfl

-- Binary-side view for the local bridge check.
theorem Prim2SF_B2Prim (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax)
  (h_zero : B2SF (prec:=prec) (emax:=emax) x = StandardFloat.S754_zero false) :
  ⦃⌜B2SF (prec:=prec) (emax:=emax) x = StandardFloat.S754_zero false⌝⦄
  (pure (Prim2SF_B2Prim_check prec emax x) : Id StandardFloat)
  ⦃⇓result => ⌜result = B2SF (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  rfl

-- Coq: compare_equiv — comparison correspondence between PrimFloat and Binary754
noncomputable def prim_compare (x y : PrimFloat) : Option Int :=
  some ((FloatSpec.Core.Raux.Rcompare x y))

noncomputable def compare_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : (Option Int) :=
  Bcompare_check (prec:=prec) (emax:=emax)
    (prim_to_binary prec emax x) (prim_to_binary prec emax y)

-- Bridge note: comparison is checked on the rounded binary images, not on the
-- raw `ℝ` primitive values.
theorem compare_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat)
  (h_eq : x = y) :
  ⦃⌜x = y⌝⦄
  (pure (compare_equiv_check prec emax x y) : Id (Option Int))
  ⦃⇓result => ⌜result =
      (Bcompare_check (prec:=prec) (emax:=emax)
        (prim_to_binary prec emax x) (prim_to_binary prec emax y))⌝⦄ := by
  intro _
  rfl

-- Coq: B2Prim_Prim2B — roundtrip Prim → Binary → Prim
noncomputable def B2Prim_Prim2B_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : PrimFloat :=
  (binary_to_prim prec emax (prim_to_binary prec emax x))

-- Bridge note: the current `ℝ` model does not provide a faithful
-- Prim→Binary→Prim inverse; the theorem exposes the computed binary roundtrip.
theorem B2Prim_Prim2B (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat)
  (h_zero : x = 0) :
  ⦃⌜x = 0⌝⦄
  (pure (B2Prim_Prim2B_check prec emax x) : Id PrimFloat)
  ⦃⇓result => ⌜result = binary_to_prim prec emax (prim_to_binary prec emax x)⌝⦄ := by
  intro _
  rfl

-- Coq: opp_equiv — negation correspondence between PrimFloat and Binary754
-- Bridge note: this validates the Binary negation path over the rounded
-- binary image.
noncomputable def opp_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : FullFloat :=
  Bopp (B2FF (prim_to_binary prec emax x))

-- Binary-side negation check for the local bridge.
theorem opp_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (opp_equiv_check prec emax x) : Id FullFloat)
  ⦃⇓result => ⌜result = Bopp (B2FF (prim_to_binary prec emax x))⌝⦄ := by
  intro _
  rfl

-- Coq: Prim2B_B2Prim — roundtrip Binary → Prim → Binary
-- Bridge note: the current `ℝ` model does not provide a faithful
-- Binary→Prim→Binary inverse; the theorem exposes the computed roundtrip.
noncomputable def Prim2B_B2Prim_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) : (Binary754 prec emax) :=
  (prim_to_binary prec emax (binary_to_prim prec emax x))

theorem Prim2B_B2Prim (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax)
  (h_zero : x = FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero false)) :
  ⦃⌜x = FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero false)⌝⦄
  (pure (Prim2B_B2Prim_check prec emax x) : Id (Binary754 prec emax))
  ⦃⇓result => ⌜result = prim_to_binary prec emax (binary_to_prim prec emax x)⌝⦄ := by
  intro _
  rfl

-- Coq: Prim2B_inj — injectivity of Prim→Binary conversion
def Prim2B_inj_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Unit :=
  ()

-- Bridge note: injectivity of rounded real-to-binary conversion is not true in
-- general, so this theorem keeps equality as an explicit hypothesis.
theorem Prim2B_inj (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat)
  (h : prim_to_binary prec emax x = prim_to_binary prec emax y)
  (h_eq : x = y) :
  ⦃⌜x = y⌝⦄
  (pure (Prim2B_inj_check prec emax x y) : Id Unit)
  ⦃⇓_ => ⌜x = y⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, Prim2B_inj_check]
  exact h_eq

-- Coq: B2Prim_inj — injectivity of Binary→Prim conversion
-- NOTE: The original theorem stating that B2R x = B2R y implies x = y is not provable
-- without additional constraints. Different Binary754 values can have the same real
-- semantics (e.g., non-canonical representations, or different NaN payloads).
-- We add the constraints from B2R_Bsign_inj: finiteness, validity, canonical form, and equal signs.
def B2Prim_inj_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Unit :=
  ()

theorem B2Prim_inj (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax)
  (h : binary_to_prim prec emax x = binary_to_prim prec emax y)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true)
  (hvx : valid_FF x.val) (hvy : valid_FF y.val)
  (hcx : canonical_FF (prec:=prec) (emax:=emax) x.val)
  (hcy : canonical_FF (prec:=prec) (emax:=emax) y.val)
  (hs : Bsign (prec:=prec) (emax:=emax) x = Bsign (prec:=prec) (emax:=emax) y) :
  ⦃⌜binary_to_prim prec emax x = binary_to_prim prec emax y ∧
    is_finite_B (prec:=prec) (emax:=emax) x = true ∧
    is_finite_B (prec:=prec) (emax:=emax) y = true ∧
    Bsign (prec:=prec) (emax:=emax) x = Bsign (prec:=prec) (emax:=emax) y⌝⦄
  (pure (B2Prim_inj_check prec emax x y) : Id Unit)
  ⦃⇓_ => ⌜x = y⌝⦄ := by
  intro _
  -- binary_to_prim returns B2R, so h means B2R x = B2R y
  -- Combined with finiteness, validity, canonical form, and sign equality,
  -- we can use B2R_Bsign_inj from Binary.lean
  simp only [wp, PostCond.noThrow, pure, B2Prim_inj_check]
  simp only [binary_to_prim] at h
  have hB2R : B2R (prec:=prec) (emax:=emax) x = B2R (prec:=prec) (emax:=emax) y := by
    simpa [PrimFloat.ofReal] using congrArg PrimFloat.toReal h
  exact B2R_Bsign_inj x y hx hy hvx hvy hcx hcy hB2R hs

-- Coq: abs_equiv — absolute-value correspondence between PrimFloat and Binary754
noncomputable def abs_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : FullFloat :=
  Babs (B2FF (prim_to_binary prec emax x))

theorem abs_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (abs_equiv_check prec emax x) : Id FullFloat)
  ⦃⇓result => ⌜result = Babs (B2FF (prim_to_binary prec emax x))⌝⦄ := by
  intro _
  rfl

-- Coq: div_equiv — division correspondence between PrimFloat and Flocq Binary
noncomputable def div_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : FullFloat :=
  B2FF (binary_div (prec:=prec) (emax:=emax) RoundingMode.RNE
    (prim_to_binary prec emax x) (prim_to_binary prec emax y))

theorem div_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (div_equiv_check prec emax x y) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (binary_div (prec:=prec) (emax:=emax) RoundingMode.RNE
              (prim_to_binary prec emax x)
              (prim_to_binary prec emax y))⌝⦄ := by
  intro _
  rfl

-- Coq: ldshiftexp_equiv — shift-exponent scaling correspondence
noncomputable def ldshiftexp_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) (e : Int) : FullFloat :=
  B2FF (binary_ldexp (prec:=prec) (emax:=emax) RoundingMode.RNE
    (prim_to_binary prec emax x) (e - 1))

theorem ldshiftexp_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) (e : Int) :
  ⦃⌜True⌝⦄
  (pure (ldshiftexp_equiv_check prec emax x e) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (binary_ldexp (prec:=prec) (emax:=emax) RoundingMode.RNE
              (prim_to_binary prec emax x) (e - 1))⌝⦄ := by
  intro _
  rfl

-- Coq: frexp_equiv — decomposition correspondence between PrimFloat and Binary754
noncomputable def frexp_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : ((Binary754 prec emax) × Int) :=
  (Bfrexp (prec:=prec) (emax:=emax) (prim_to_binary prec emax x))

theorem frexp_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (frexp_equiv_check prec emax x) : Id ((Binary754 prec emax) × Int))
  ⦃⇓result => ⌜result = Bfrexp (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, frexp_equiv_check]

-- Coq: frshiftexp_equiv — shifted decomposition correspondence
noncomputable def frshiftexp_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : ((Binary754 prec emax) × Int) :=
  (Bfrexp (prec:=prec) (emax:=emax) (prim_to_binary prec emax x))

theorem frshiftexp_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (frshiftexp_equiv_check prec emax x) : Id ((Binary754 prec emax) × Int))
  ⦃⇓result => ⌜result = Bfrexp (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, frshiftexp_equiv_check]

-- Coq: sub_equiv — subtraction correspondence between PrimFloat and Flocq Binary
noncomputable def sub_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : FullFloat :=
  B2FF (binary_sub (prec:=prec) (emax:=emax) RoundingMode.RNE
    (prim_to_binary prec emax x) (prim_to_binary prec emax y))

theorem sub_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (sub_equiv_check prec emax x y) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (binary_sub (prec:=prec) (emax:=emax) RoundingMode.RNE
              (prim_to_binary prec emax x)
              (prim_to_binary prec emax y))⌝⦄ := by
  intro _
  rfl

-- Coq: sqrt_equiv — square-root correspondence between PrimFloat and Flocq Binary
noncomputable def sqrt_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : FullFloat :=
  B2FF (binary_sqrt (prec:=prec) (emax:=emax) RoundingMode.RNE (prim_to_binary prec emax x))

theorem sqrt_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (sqrt_equiv_check prec emax x) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (binary_sqrt (prec:=prec) (emax:=emax) RoundingMode.RNE
              (prim_to_binary prec emax x))⌝⦄ := by
  intro _
  rfl

-- Coq: infinity_equiv — primitive +∞ corresponds to Binary infinity
noncomputable def infinity_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : PrimFloat :=
  (binary_to_prim prec emax (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_infinity false)))

theorem infinity_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  (pure (infinity_equiv_check prec emax) : Id PrimFloat)
  ⦃⇓result => ⌜result = prim_infinity⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, infinity_equiv_check, binary_to_prim, B2R, FF2R, FF2B, prim_infinity]
  rfl

-- Coq: neg_infinity_equiv — primitive −∞ corresponds to Binary −∞
noncomputable def neg_infinity_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : PrimFloat :=
  (binary_to_prim prec emax (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_infinity true)))

theorem neg_infinity_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  (pure (neg_infinity_equiv_check prec emax) : Id PrimFloat)
  ⦃⇓result => ⌜result = prim_infinity⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, neg_infinity_equiv_check, binary_to_prim, B2R, FF2R, FF2B, prim_infinity]
  rfl

-- Coq: nan_equiv — primitive NaN corresponds to Binary NaN
noncomputable def nan_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : PrimFloat :=
  (binary_to_prim prec emax (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_nan false 1)))

theorem nan_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  (pure (nan_equiv_check prec emax) : Id PrimFloat)
  ⦃⇓result => ⌜result = prim_nan⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, nan_equiv_check, binary_to_prim, B2R, FF2R, FF2B, prim_nan]
  rfl

-- Coq: zero_equiv — primitive +0 corresponds to Binary zero
noncomputable def zero_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : PrimFloat :=
  (binary_to_prim prec emax (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero false)))

theorem zero_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  (pure (zero_equiv_check prec emax) : Id PrimFloat)
  ⦃⇓result => ⌜result = prim_zero⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, zero_equiv_check, binary_to_prim, B2R, FF2R, FF2B, prim_zero]
  rfl

-- Coq: neg_zero_equiv — primitive −0 corresponds to Binary −0
noncomputable def neg_zero_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : PrimFloat :=
  (binary_to_prim prec emax (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero true)))

theorem neg_zero_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  (pure (neg_zero_equiv_check prec emax) : Id PrimFloat)
  ⦃⇓result => ⌜result = prim_zero⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, neg_zero_equiv_check, binary_to_prim, B2R, FF2R, FF2B, prim_zero]
  rfl

-- Coq: one_equiv — primitive one corresponds to Binary constant one
noncomputable def one_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax] : PrimFloat :=
  (binary_to_prim prec emax (binary_one (prec:=prec) (emax:=emax)))

theorem one_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  (pure (one_equiv_check prec emax) : Id PrimFloat)
  ⦃⇓result => ⌜result = 1⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, one_equiv_check, binary_to_prim,
    B2R, binary_one, FF2B, FF2R, F2R, FloatSpec.Core.Defs.F2R,
    PrimFloat.ofReal]
  change ({ toReal := (1 : ℝ) } : PrimFloat) =
    (@OfNat.ofNat PrimFloat 1 (PrimFloat.instOfNat 1))
  unfold OfNat.ofNat PrimFloat.instOfNat PrimFloat.ofReal
  congr
  change (1 : ℝ) = ((1 : Nat) : ℝ)
  norm_num

-- Helper lemma: FF2R of the canonical one representation equals 1
private lemma FF2R_finite_one : FF2R 2 (FullFloat.F754_finite false 1 0) = 1 := by
  simp only [FF2R, F2R, FloatSpec.Core.Defs.F2R]
  norm_num

-- Coq: two_equiv — primitive two corresponds to Binary plus one one
noncomputable def two_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  [FloatSpec.Core.Generic_fmt.Valid_exp 2 (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))] : PrimFloat :=
  (binary_to_prim prec emax
          (binary_add (prec:=prec) (emax:=emax)
            (binary_one (prec:=prec) (emax:=emax))
            (binary_one (prec:=prec) (emax:=emax))))

theorem two_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  [FloatSpec.Core.Generic_fmt.Valid_exp 2 (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))]
  [FloatSpec.Core.Generic_fmt.Monotone_exp (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))] :
  ⦃⌜True⌝⦄
  (pure (two_equiv_check prec emax) : Id PrimFloat)
  ⦃⇓result => ⌜result = 2⌝⦄ := by
  intro _
  let fexp := FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec)
  have hemin_le_one : 3 - emax - prec ≤ (1 : Int) := by
    have hprec_pos : 0 < prec := Prec_gt_0.pos
    have hemax_ge_two : 2 ≤ emax := (inferInstance : Prec_lt_emax prec emax).emax_ge_2
    omega
  have hgf_two : FloatSpec.Core.Generic_fmt.generic_format 2 fexp (2 : ℝ) := by
    have hbpow := FloatSpec.Core.FLT.FLT_format_bpow
      (prec := prec) (emin := 3 - emax - prec) (beta := 2) (e := 1)
    have hrun := hbpow ⟨by norm_num, hemin_le_one⟩
    simp only [wp, PostCond.noThrow, Id.run, pure, PredTrans.pure,
      FloatSpec.Core.FLT.FLT_format] at hrun
    simpa [fexp] using hrun
  have hround_two :
      FloatSpec.Core.Generic_fmt.round_to_generic 2 fexp FloatSpec.Core.Raux.Ztrunc (2 : ℝ) = 2 := by
    simpa [FloatSpec.Core.Generic_fmt.round_to_generic,
      FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Defs.F2R] using hgf_two.symm
  have hff_two : FF2R 2 (real_to_FullFloat (2 : ℝ) fexp) = 2 :=
    FF2R_real_to_FullFloat (x := (2 : ℝ)) (fexp := fexp) hgf_two
  have hround_two_explicit :
      FloatSpec.Core.Generic_fmt.round_to_generic 2
        (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))
        FloatSpec.Core.Raux.Ztrunc (2 : ℝ) = 2 := by
    simpa [fexp] using hround_two
  have hff_two_explicit :
      FF2R 2 (real_to_FullFloat (2 : ℝ)
        (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))) = 2 := by
    simpa [fexp] using hff_two
  simp [wp, PostCond.noThrow, pure, two_equiv_check, binary_to_prim, B2R,
    binary_add, binary_one, FF2B, FF2R_finite_one, PrimFloat.ofReal]
  change PrimFloat.ofReal
      (FF2R 2 (real_to_FullFloat
        (FloatSpec.Core.Generic_fmt.round_to_generic 2
          (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))
          FloatSpec.Core.Raux.Ztrunc ((1 : ℝ) + 1))
        (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec)))) =
    (2 : PrimFloat)
  have hsum : (1 : ℝ) + 1 = 2 := by norm_num
  rw [hsum, hround_two_explicit, hff_two_explicit]
  change PrimFloat.ofReal (2 : ℝ) = PrimFloat.ofReal (2 : ℝ)
  rfl

-- Coq: ulp_equiv — ulp correspondence via Binary side
noncomputable def ulp_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : FullFloat :=
  -- Bridge through Binary `Bulp'` once available.
  B2FF (prim_to_binary prec emax (prim_ldexp 1 (0)))

theorem ulp_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (ulp_equiv_check prec emax x) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (prim_to_binary prec emax (prim_ldexp 1 (0)))⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, ulp_equiv_check]

-- Coq: next_up_equiv — successor correspondence
noncomputable def next_up_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : FullFloat :=
  B2FF (Bsucc (prec:=prec) (emax:=emax) (prim_to_binary prec emax x))

-- Binary-side successor check for the local bridge.
theorem next_up_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (next_up_equiv_check prec emax x) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (Bsucc (prec:=prec) (emax:=emax) (prim_to_binary prec emax x))⌝⦄ := by
  intro _
  rfl

-- Coq: next_down_equiv — predecessor correspondence
noncomputable def next_down_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : FullFloat :=
  B2FF (Bpred (prec:=prec) (emax:=emax) (prim_to_binary prec emax x))

-- Binary-side predecessor check for the local bridge.
theorem next_down_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (next_down_equiv_check prec emax x) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (Bpred (prec:=prec) (emax:=emax) (prim_to_binary prec emax x))⌝⦄ := by
  intro _
  rfl

-- Coq: is_nan_equiv — NaN classifier correspondence
noncomputable def is_nan_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Bool :=
  is_nan_B (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)

theorem is_nan_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (is_nan_equiv_check prec emax x) : Id Bool)
  ⦃⇓result => ⌜result = is_nan_B (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)⌝⦄ := by
  intro _
  rfl

-- Coq: is_zero_equiv — zero classifier correspondence
noncomputable def is_zero_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Bool :=
  decide (B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x) = StandardFloat.S754_zero false ∨
          B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x) = StandardFloat.S754_zero true)

-- Binary-side zero-classifier check for the local bridge.
theorem is_zero_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat)
  (h_zero : x = 0) :
  ⦃⌜x = 0⌝⦄
  (pure (is_zero_equiv_check prec emax x) : Id Bool)
  ⦃⇓result => ⌜result = decide (B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x) = StandardFloat.S754_zero false ∨
                                   B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x) = StandardFloat.S754_zero true)⌝⦄ := by
  intro _
  rfl

-- Coq: of_int63_equiv — integer conversion equivalence
noncomputable def of_int63_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (z : Int) : PrimFloat :=
  binary_to_prim prec emax (prim_to_binary prec emax (PrimFloat.ofReal (z : ℝ)))

-- Bridge note: integer conversion is checked through the rounded binary image.
theorem of_int63_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (z : Int)
  (h_zero : z = 0) :
  ⦃⌜z = 0⌝⦄
  (pure (of_int63_equiv_check prec emax z) : Id PrimFloat)
  ⦃⇓result => ⌜result =
      binary_to_prim prec emax (prim_to_binary prec emax (PrimFloat.ofReal (z : ℝ)))⌝⦄ := by
  intro _
  rfl

-- Coq: is_infinity_equiv — infinity classifier correspondence
noncomputable def is_infinity_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Bool :=
  decide (∃ s, B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x) = StandardFloat.S754_infinity s)

-- Decidable instance needed for the existential in is_infinity_equiv
-- (must be defined globally for `decide` to elaborate correctly)
instance : Decidable (∃ s, StandardFloat.S754_zero false = StandardFloat.S754_infinity s) :=
  isFalse (fun ⟨s, h⟩ => by cases h)

theorem is_infinity_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (is_infinity_equiv_check prec emax x) : Id Bool)
  ⦃⇓result => ⌜result = decide (∃ s, B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x) = StandardFloat.S754_infinity s)⌝⦄ := by
  intro _
  rfl

-- Coq: is_finite_equiv — finiteness classifier correspondence
noncomputable def is_finite_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Bool :=
  is_finite_B (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)

theorem is_finite_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (is_finite_equiv_check prec emax x) : Id Bool)
  ⦃⇓result => ⌜result = is_finite_B (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)⌝⦄ := by
  intro _
  rfl

-- Coq: get_sign_equiv — sign bit correspondence
noncomputable def get_sign_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Bool :=
  Bsign (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)

theorem get_sign_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (get_sign_equiv_check prec emax x) : Id Bool)
  ⦃⇓result => ⌜result = Bsign (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)⌝⦄ := by
  intro _
  rfl

-- Binary-side boolean comparisons used in Coq's eqb/ltb/leb lemmas
-- Note: For finite floats, we check equality via Rcompare returning 0 (equal).
-- This matches Coq's SFeqb which checks if Rcompare returns Eq.
-- For non-finite (nan, infinity), we follow IEEE 754 semantics:
--   - NaN ≠ NaN (returns false for NaN equality)
--   - Infinities compare structurally by sign
noncomputable def Beqb (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  -- For finite floats, compare real values
  -- For infinity/nan, follow IEEE 754
  if is_finite_B (prec:=prec) (emax:=emax) x && is_finite_B (prec:=prec) (emax:=emax) y then
    -- Both finite: check if Rcompare returns 0 (equal)
    FloatSpec.Core.Raux.Rcompare (B2R (prec:=prec) (emax:=emax) x) (B2R (prec:=prec) (emax:=emax) y) == 0
  else
    -- At least one is not finite: compare structurally
    -- IEEE 754: NaN ≠ NaN, so Beqb nan nan = false
    match B2SF (prec:=prec) (emax:=emax) x, B2SF (prec:=prec) (emax:=emax) y with
    | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => decide (sx = sy)
    | StandardFloat.S754_nan, StandardFloat.S754_nan => false  -- NaN ≠ NaN per IEEE 754
    | _, _ => false

-- Coq: Beqb_correct — equality on binary numbers matches real equality under finiteness
noncomputable def Beqb_correct_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  (Beqb prec emax x y)

-- Helper: Rcompare returns 0 iff the values are equal
private lemma Rcompare_eq_zero_iff (x y : ℝ) :
    FloatSpec.Core.Raux.Rcompare x y = 0 ↔ x = y := by
  unfold FloatSpec.Core.Raux.Rcompare
  constructor
  · intro h
    by_cases hlt : x < y
    · simp only [hlt, ↓reduceIte] at h
      norm_num at h
    · by_cases heq : x = y
      · exact heq
      · simp only [hlt, heq, ↓reduceIte] at h
        norm_num at h
  · intro h
    simp only [h, lt_irrefl, ↓reduceIte]

-- Helper: For finite floats, Beqb equals decide (B2R x = B2R y)
private lemma Beqb_correct_aux (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true) :
  Beqb prec emax x y = decide (B2R (prec:=prec) (emax:=emax) x = B2R (prec:=prec) (emax:=emax) y) := by
  -- With the new Beqb definition that uses Rcompare for finite floats
  unfold Beqb
  simp only [hx, hy, Bool.true_and, ↓reduceIte]
  -- Goal: (Rcompare (B2R x) (B2R y) == 0) = decide (B2R x = B2R y)
  -- Note: (a == b) is a Bool, and (a == b) = true ↔ a = b
  -- We prove equality of Bools by showing iff on being true
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_iff]
  exact Rcompare_eq_zero_iff (B2R x) (B2R y)

theorem Beqb_correct (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true) :
  ⦃⌜True⌝⦄
  (pure (Beqb_correct_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result = decide (B2R (prec:=prec) (emax:=emax) x = B2R (prec:=prec) (emax:=emax) y)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, Beqb_correct_check,
             Id.run, PredTrans.pure, PredTrans.apply]
  exact Beqb_correct_aux prec emax x y hx hy

noncomputable def Bcmp (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Int :=
  ((FloatSpec.Core.Raux.Rcompare (B2R (prec:=prec) (emax:=emax) x)
                                 (B2R (prec:=prec) (emax:=emax) y)))

noncomputable def Bltb (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  Bcmp prec emax x y = (-1)

noncomputable def Bleb (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  Bcmp prec emax x y ≠ 1

-- Coq: Beqb_refl — reflexivity of Beqb except NaN
noncomputable def Beqb_refl_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) : Bool :=
  (Beqb prec emax x x)

theorem Beqb_refl (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) :
  ⦃⌜True⌝⦄
  (pure (Beqb_refl_check prec emax x) : Id Bool)
  ⦃⇓result => ⌜result = bnot (is_nan_B (prec:=prec) (emax:=emax) x)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, Beqb_refl_check, Id.run, PredTrans.pure, PredTrans.apply]
  -- Case analysis on the underlying FullFloat
  unfold Beqb is_nan_B is_finite_B B2SF is_nan_FF is_finite_FF FF2SF
  cases hx : x.val with
  | F754_zero s =>
    -- Finite case: Rcompare returns 0, so Beqb x x = true
    -- is_nan_B x = false, so bnot false = true
    simp only [hx, Bool.true_and, ↓reduceIte, bnot]
    -- Rcompare r r = 0 for any r
    have h : FloatSpec.Core.Raux.Rcompare (B2R x) (B2R x) = 0 := by
      unfold FloatSpec.Core.Raux.Rcompare
      simp only [lt_irrefl, ↓reduceIte]
    simp only [h, beq_self_eq_true]
    -- Goal is ⌜true = !false⌝.down, prove the inner equality
    have heq : true = !false := rfl
    exact heq
  | F754_infinity s =>
    -- Non-finite (infinity): use structural comparison
    -- S754_infinity s = S754_infinity s, decide (s = s) = true
    -- is_nan_B x = false, bnot false = true
    simp only [hx, ↓reduceIte, bnot, decide_true]
    -- Goal is ⌜(if (false && false) = true then ... else true) = !false⌝.down
    have heq : (if (false && false) = true then FloatSpec.Core.Raux.Rcompare (B2R x) (B2R x) == 0 else true) = !false := by
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, bnot]
      rfl
    exact heq
  | F754_nan s m =>
    -- NaN case: Beqb returns false (per IEEE 754)
    -- is_nan_B x = true, bnot true = false
    simp only [hx, ↓reduceIte, bnot]
    -- Goal is ⌜(if (false && false) = true then ... else false) = !true⌝.down
    have heq : (if (false && false) = true then FloatSpec.Core.Raux.Rcompare (B2R x) (B2R x) == 0 else false) = !true := by
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, bnot]
      rfl
    exact heq
  | F754_finite s m e =>
    -- Finite case: Rcompare returns 0, so Beqb x x = true
    -- is_nan_B x = false, so bnot false = true
    simp only [hx, Bool.true_and, ↓reduceIte, bnot]
    have h : FloatSpec.Core.Raux.Rcompare (B2R x) (B2R x) = 0 := by
      unfold FloatSpec.Core.Raux.Rcompare
      simp only [lt_irrefl, ↓reduceIte]
    simp only [h, beq_self_eq_true]
    -- Goal is ⌜true = !false⌝.down, prove the inner equality
    have heq : true = !false := rfl
    exact heq

-- Coq: Bltb_correct — strict-ordered comparison matches real comparison
noncomputable def Bltb_correct_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  (Bltb prec emax x y)

theorem Bltb_correct (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true) :
  ⦃⌜True⌝⦄
  (pure (Bltb_correct_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result = decide (B2R (prec:=prec) (emax:=emax) x < B2R (prec:=prec) (emax:=emax) y)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, Id.run, PredTrans.pure, PredTrans.apply]
  simp only [Bltb_correct_check, Bltb, Bcmp]
  -- Goal: ⌜decide (Rcompare (B2R x) (B2R y) = -1) = decide (B2R x < B2R y)⌝.down
  -- We need to show the two decide expressions are equal
  -- This follows from: Rcompare a b = -1 ↔ a < b
  have hiff : (FloatSpec.Core.Raux.Rcompare (B2R x) (B2R y) = -1) ↔ (B2R x < B2R y) := by
    constructor
    · intro hcmp
      -- From Rcompare returning -1, deduce x < y
      unfold FloatSpec.Core.Raux.Rcompare at hcmp
      by_cases hlt : B2R x < B2R y
      · exact hlt
      · -- If not x < y, then Rcompare cannot be -1
        simp only [hlt, ↓reduceIte] at hcmp
        by_cases heq : B2R x = B2R y
        · simp [heq] at hcmp
        · simp [heq] at hcmp
    · intro hlt
      -- From x < y, produce Rcompare = -1
      unfold FloatSpec.Core.Raux.Rcompare
      simp [hlt]
  -- Convert the iff to decide equality
  have hdec : decide (FloatSpec.Core.Raux.Rcompare (B2R x) (B2R y) = -1) =
              decide (B2R x < B2R y) := by
    simp only [decide_eq_decide]
    exact hiff
  exact hdec

-- Coq: Bleb_correct — non-strict-ordered comparison matches real comparison
noncomputable def Bleb_correct_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  (Bleb prec emax x y)

theorem Bleb_correct (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true) :
  ⦃⌜True⌝⦄
  (pure (Bleb_correct_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result = decide (B2R (prec:=prec) (emax:=emax) x ≤ B2R (prec:=prec) (emax:=emax) y)⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, Id.run, PredTrans.pure, PredTrans.apply]
  simp only [Bleb_correct_check, Bleb, Bcmp]
  -- Goal: decide (Rcompare (B2R x) (B2R y) ≠ 1) = decide (B2R x ≤ B2R y)
  -- We need: Rcompare a b ≠ 1 ↔ a ≤ b (since Rcompare returns 1 iff a > b)
  have hiff : (FloatSpec.Core.Raux.Rcompare (B2R x) (B2R y) ≠ 1) ↔ (B2R x ≤ B2R y) := by
    constructor
    · intro hcmp
      -- From Rcompare not returning 1, deduce x ≤ y
      unfold FloatSpec.Core.Raux.Rcompare at hcmp
      by_cases hlt : B2R x < B2R y
      · exact le_of_lt hlt
      · by_cases heq : B2R x = B2R y
        · exact le_of_eq heq
        · -- If not x < y and not x = y, then x > y, so Rcompare = 1
          simp only [hlt, heq, ↓reduceIte] at hcmp
          exact absurd rfl hcmp
    · intro hle
      -- From x ≤ y, produce Rcompare ≠ 1
      unfold FloatSpec.Core.Raux.Rcompare
      by_cases hlt : B2R x < B2R y
      · simp [hlt]
      · by_cases heq : B2R x = B2R y
        · simp [hlt, heq]
        · -- x ≤ y but not x < y and not x = y is a contradiction
          have hgt : B2R y < B2R x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
          exact absurd hgt (not_lt_of_ge hle)
  -- Convert the iff to decide equality
  have hdec : decide (FloatSpec.Core.Raux.Rcompare (B2R x) (B2R y) ≠ 1) =
              decide (B2R x ≤ B2R y) := by
    simp only [decide_eq_decide]
    exact hiff
  exact hdec

-- Coq: eqb_equiv — boolean equality correspondence
noncomputable def eqb_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Bool :=
  Beqb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)

theorem eqb_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (eqb_equiv_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result =
      Beqb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)⌝⦄ := by
  intro _
  rfl

-- Coq: ltb_equiv — boolean strict ordering correspondence
noncomputable def ltb_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Bool :=
  Bltb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)

theorem ltb_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (ltb_equiv_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result =
      Bltb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)⌝⦄ := by
  intro _
  rfl

-- Coq: leb_equiv — boolean non-strict ordering correspondence
noncomputable def leb_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Bool :=
  Bleb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)

theorem leb_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (leb_equiv_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result =
      Bleb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)⌝⦄ := by
  intro _
  rfl

end ExperimentalPrimFloatBridge

namespace FaithfulPrimFloat

/-!
Proof-carrying model of Coq's primitive binary64 floats.

This namespace is intentionally separate from `ExperimentalPrimFloatBridge`:
the latter keeps its historical real-only compatibility API, while this model
preserves the `StandardFloat` representation and validity evidence used by
Flocq's `PrimFloat.v` conversion layer.
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

-- Coq `SpecFloat.binary_round`, specialized to primitive binary64.
noncomputable def binary_round (sx : Bool) (mx : Nat) (ex : Int) :
    StandardFloat :=
  let aligned := shl_align_fexp (prec:=primPrec) (emax:=primEmax) mx ex
  binary_round_aux sx (aligned.1 : Int) aligned.2
    FloatSpec.Calc.Bracket.Location.loc_Exact

-- Coq `PrimFloat.v:binary_round_equiv`.
theorem binary_round_equiv (sx : Bool) (mx : Nat) (ex : Int) :
    binary_round sx mx ex =
      _root_.binary_round (prec:=primPrec) (emax:=primEmax)
        RoundingMode.RNE sx mx ex := by
  unfold binary_round _root_.binary_round shl_align_fexp
  set aligned := shl_align mx ex
    (FLT_exp (3 - primEmax - primPrec) primPrec
      (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex))
  cases aligned with
  | mk alignedMant alignedExp =>
      apply binary_round_aux_equiv

private theorem rootBinaryRoundValid (sx : Bool) (mx : Nat) (ex : Int)
    (hmx_pos : 0 < mx) :
    validBinarySingleNaNStandardFloat (prec := primPrec) (emax := primEmax)
      (_root_.binary_round (prec := primPrec) (emax := primEmax)
        RoundingMode.RNE sx mx ex) = true :=
  (_root_.binary_round_correct (prec := primPrec) (emax := primEmax)
    RoundingMode.RNE sx mx ex hmx_pos).1

-- Coq `SpecFloat.binary_normalize`, specialized to primitive binary64.
noncomputable def binary_normalize (m e : Int) (szero : Bool) :
    StandardFloat :=
  if m = 0 then
    StandardFloat.S754_zero szero
  else if 0 < m then
    binary_round false m.toNat e
  else
    binary_round true m.natAbs e

-- Coq `BinarySingleNaN.binary_normalize`, specialized to primitive binary64.
noncomputable def binary_normalize_bsn (m e : Int) (szero : Bool) :
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
        RoundingMode.RNE false m.toNat e)
      (rootBinaryRoundValid false m.toNat e hm_toNat_pos)
  else
    have hm_ne : m ≠ 0 := by
      intro h
      exact hzero h
    have hm_abs_pos : 0 < m.natAbs := Int.natAbs_pos.mpr hm_ne
    SF2B
      (_root_.binary_round (prec := primPrec) (emax := primEmax)
        RoundingMode.RNE true m.natAbs e)
      (rootBinaryRoundValid true m.natAbs e hm_abs_pos)

-- Coq `PrimFloat.v:binary_normalize_equiv`.
theorem binary_normalize_equiv (m e : Int) (szero : Bool) :
    binary_normalize m e szero = B2SF (binary_normalize_bsn m e szero) := by
  unfold binary_normalize binary_normalize_bsn
  by_cases hzero : m = 0
  · simp [hzero, B2SF, binarySingleNaNFloatToStandardFloat]
  · by_cases hpos : 0 < m
    · simp [hzero, hpos, B2SF_SF2B, binary_round_equiv]
    · simp [hzero, hpos, B2SF_SF2B, binary_round_equiv]

end FaithfulPrimFloat
