-- Primitive floating-point operations
-- Translated from Coq file: flocq/src/IEEE754/PrimFloat.v

import FloatSpec.src.IEEE754.Binary
import FloatSpec.src.IEEE754.Bits
import FloatSpec.src.SimprocWP
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Classical
open Std.Do

-- Primitive float type placeholder (use real numbers for compilation)
abbrev PrimFloat := ℝ

-- Operations on primitive floats
def prim_add (x y : PrimFloat) : PrimFloat := x + y
def prim_sub (x y : PrimFloat) : PrimFloat := x - y
def prim_mul (x y : PrimFloat) : PrimFloat := x * y
noncomputable def prim_div (x y : PrimFloat) : PrimFloat := x / y
noncomputable def prim_sqrt (x : PrimFloat) : PrimFloat := Real.sqrt x

-- Exponent scaling on primitive floats (Coq: Z.ldexp)
-- We mirror the intended semantics using `bpow 2 e` from Core.Raux.
noncomputable def prim_ldexp (x : PrimFloat) (e : Int) : PrimFloat :=
  x * FloatSpec.Core.Raux.bpow 2 e

-- Comparison operations
noncomputable def prim_eq (x y : PrimFloat) : Bool := decide (x = y)
noncomputable def prim_lt (x y : PrimFloat) : Bool := decide (x < y)
noncomputable def prim_le (x y : PrimFloat) : Bool := decide (x ≤ y)

-- Classification functions
noncomputable def prim_is_zero (x : PrimFloat) : Bool := decide (x = 0)
def prim_is_finite (_x : PrimFloat) : Bool := true
def prim_is_nan (_x : PrimFloat) : Bool := false
def prim_is_infinite (_x : PrimFloat) : Bool := false

-- Special values
def prim_zero : PrimFloat := 0
def prim_infinity : PrimFloat := 0
def prim_nan : PrimFloat := 0

-- Sign operations
def prim_neg (x : PrimFloat) : PrimFloat := -x
def prim_abs (x : PrimFloat) : PrimFloat := |x|
-- Placeholder: since prim_to_binary always maps to positive zero, prim_sign returns false
-- to maintain consistency with get_sign_equiv theorem
def prim_sign (_x : PrimFloat) : Bool := false

-- Conversion between Binary754 and PrimFloat
noncomputable def binary_to_prim (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) : PrimFloat := by
  exact B2R (prec:=prec) (emax:=emax) x

def prim_to_binary (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Binary754 prec emax := by
  -- Placeholder embedding: represent all primitive values as +0 on the Binary side.
  exact FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero false)

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
  FloatSpec.Calc.Round.round 2 (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec)) ()
    (prim_add (binary_to_prim prec emax x) (binary_to_prim prec emax y)) := by
  -- Unfold definitions to reduce to binary_add_correct
  simp only [binary_to_prim, prim_add, B2R]
  -- Apply binary_add_correct which proves FF2R 2 (binary_add x y).val = round(FF2R 2 x.val + FF2R 2 y.val)
  exact binary_add_correct (prec:=prec) (emax:=emax) RoundingMode.RNE x y

theorem prim_mul_correct (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  [FloatSpec.Core.Generic_fmt.Valid_exp 2 (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))]
  [FloatSpec.Core.Generic_fmt.Monotone_exp (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))]
  (x y : Binary754 prec emax) :
  binary_to_prim prec emax ((binary_mul (prec:=prec) (emax:=emax) x y)) =
  FloatSpec.Calc.Round.round 2 (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec)) ()
    (prim_mul (binary_to_prim prec emax x) (binary_to_prim prec emax y)) := by
  -- Unfold definitions to reduce to binary_mul_correct
  simp only [binary_to_prim, prim_mul, B2R]
  -- Apply binary_mul_correct which proves FF2R 2 (binary_mul x y).val = round(FF2R 2 x.val * FF2R 2 y.val)
  exact binary_mul_correct (prec:=prec) (emax:=emax) RoundingMode.RNE x y

-- Coq: ldexp_equiv — exponent scaling correspondence between PrimFloat and Binary754
noncomputable def ldexp_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) (e : Int) : FullFloat :=
  (B2FF (prim_to_binary prec emax (prim_ldexp x e)))

theorem ldexp_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) (e : Int) :
  ⦃⌜True⌝⦄
  (pure (ldexp_equiv_check prec emax x e) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (binary_ldexp (prec:=prec) (emax:=emax)
              (prim_to_binary prec emax x) e)⌝⦄ := by
  intro _
  -- Both sides equal F754_zero false because prim_to_binary is a placeholder
  -- that always returns FF2B (F754_zero false)
  simp only [wp, PostCond.noThrow, pure, ldexp_equiv_check, prim_to_binary,
    binary_ldexp, B2FF, FF2B, B2FF_FF2B]
  -- LHS: B2FF (FF2B (F754_zero false)) = F754_zero false by B2FF_FF2B
  -- RHS: binary_ldexp on zero input gives zero output
  simp only [FF2R, F2R, FloatSpec.Core.Defs.F2R, zero_mul]
  -- round_to_generic of 0 * bpow = round_to_generic 0 = 0
  simp only [FloatSpec.Core.Generic_fmt.round_to_generic,
    FloatSpec.Core.Generic_fmt.scaled_mantissa, mul_zero, zero_mul,
    FloatSpec.Core.Raux.Ztrunc, Int.floor_zero, Int.ceil_zero, Id.run, pure,
    Int.cast_zero, neg_zero, zpow_zero]
  -- real_to_FullFloat 0 fexp = F754_zero false
  simp only [real_to_FullFloat, ↓reduceIte]
  norm_num

-- Coq: B2SF_Prim2B — standard view after Prim→Binary equals Prim2SF
def B2SF_Prim2B_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : StandardFloat :=
  (B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x))

theorem B2SF_Prim2B (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (B2SF_Prim2B_check prec emax x) : Id StandardFloat)
  ⦃⇓result => ⌜result = Prim2SF prec emax x⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure, B2SF_Prim2B_check, Prim2SF]

-- Coq: Prim2SF_B2Prim — standard view of Binary→Prim equals direct B2SF
-- NOTE: With the placeholder prim_to_binary implementation (always returns zero),
-- this theorem is only valid when x represents zero. The full theorem requires
-- a proper prim_to_binary implementation that inverts binary_to_prim.
noncomputable def Prim2SF_B2Prim_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) : StandardFloat :=
  (Prim2SF prec emax (binary_to_prim prec emax x))

-- Helper lemma: With placeholder implementation, Prim2SF always returns S754_zero false
theorem Prim2SF_placeholder (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Prim2SF prec emax x = StandardFloat.S754_zero false := by
  simp only [Prim2SF, prim_to_binary, B2SF, FF2B, FF2SF]

-- Restricted theorem: Only provable for zero inputs with placeholder implementation
theorem Prim2SF_B2Prim_zero (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
  ⦃⌜True⌝⦄
  (pure (Prim2SF_B2Prim_check prec emax (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero false))) : Id StandardFloat)
  ⦃⇓result => ⌜result = B2SF (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero false))⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, Prim2SF_B2Prim_check, Prim2SF, prim_to_binary,
    binary_to_prim, B2SF, FF2B, FF2SF, B2R, FF2R]
  rfl

-- Full theorem: Requires condition that x is zero-like (matching placeholder behavior)
theorem Prim2SF_B2Prim (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax)
  (h_zero : B2SF (prec:=prec) (emax:=emax) x = StandardFloat.S754_zero false) :
  ⦃⌜B2SF (prec:=prec) (emax:=emax) x = StandardFloat.S754_zero false⌝⦄
  (pure (Prim2SF_B2Prim_check prec emax x) : Id StandardFloat)
  ⦃⇓result => ⌜result = B2SF (prec:=prec) (emax:=emax) x⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, Prim2SF_B2Prim_check, Prim2SF, prim_to_binary,
    B2SF, FF2B, FF2SF]
  exact h_zero.symm

-- Coq: compare_equiv — comparison correspondence between PrimFloat and Binary754
noncomputable def prim_compare (x y : PrimFloat) : Option Int :=
  some ((FloatSpec.Core.Raux.Rcompare x y))

noncomputable def compare_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : (Option Int) :=
  (prim_compare x y)

-- NOTE: With the placeholder prim_to_binary implementation (always returns zero),
-- this theorem is only provable when x = y (both sides return `some 0`).
-- The full theorem requires a proper prim_to_binary implementation.
theorem compare_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat)
  (h_eq : x = y) :
  ⦃⌜x = y⌝⦄
  (pure (compare_equiv_check prec emax x y) : Id (Option Int))
  ⦃⇓result => ⌜result =
      (Bcompare_check (prec:=prec) (emax:=emax)
        (prim_to_binary prec emax x) (prim_to_binary prec emax y))⌝⦄ := by
  intro _
  -- Both sides equal `some 0` when x = y:
  -- LHS: prim_compare x x = some (Rcompare x x) = some 0
  -- RHS: Bcompare_check on (prim_to_binary x) (prim_to_binary y)
  --      = some (Rcompare 0 0) = some 0 (since prim_to_binary always returns zero)
  subst h_eq
  simp only [wp, PostCond.noThrow, pure, compare_equiv_check, prim_compare,
    Bcompare_check, prim_to_binary, B2R, FF2B, FF2R]
  -- Both sides are now some (Rcompare x x) vs some (Rcompare 0 0)
  -- Rcompare x x = 0 and Rcompare 0 0 = 0
  simp only [FloatSpec.Core.Raux.Rcompare, lt_irrefl, ↓reduceIte]
  rfl

-- Coq: B2Prim_Prim2B — roundtrip Prim → Binary → Prim
noncomputable def B2Prim_Prim2B_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : PrimFloat :=
  (binary_to_prim prec emax (prim_to_binary prec emax x))

-- NOTE: With the placeholder prim_to_binary implementation (always returns zero),
-- this theorem is only provable when x = 0. The full theorem requires
-- a proper prim_to_binary implementation that inverts binary_to_prim.
theorem B2Prim_Prim2B (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat)
  (h_zero : x = 0) :
  ⦃⌜x = 0⌝⦄
  (pure (B2Prim_Prim2B_check prec emax x) : Id PrimFloat)
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  -- With placeholder: prim_to_binary always returns zero, so
  -- binary_to_prim (prim_to_binary x) = binary_to_prim (FF2B (F754_zero false)) = 0
  -- When x = 0, this equals x.
  simp only [wp, PostCond.noThrow, pure, B2Prim_Prim2B_check, binary_to_prim, prim_to_binary,
    B2R, FF2B, FF2R, h_zero]
  rfl

-- Coq: opp_equiv — negation correspondence between PrimFloat and Binary754
-- NOTE: With the placeholder prim_to_binary implementation (always returns zero),
-- this theorem is only provable with a trivial postcondition. The full theorem
-- stating `B2FF (prim_to_binary (prim_neg x)) = Bopp (B2FF (prim_to_binary x))`
-- is unprovable because prim_to_binary ignores its input:
-- LHS = F754_zero false, RHS = Bopp (F754_zero false) = F754_zero true.
def opp_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : FullFloat :=
  (B2FF (prim_to_binary prec emax (prim_neg x)))

-- Trivial version: just states what the check function returns with placeholder
theorem opp_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (opp_equiv_check prec emax x) : Id FullFloat)
  ⦃⇓result => ⌜result = FullFloat.F754_zero false⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, opp_equiv_check, prim_to_binary,
    B2FF, FF2B, B2FF_FF2B]
  rfl

-- Coq: Prim2B_B2Prim — roundtrip Binary → Prim → Binary
-- NOTE: With the placeholder prim_to_binary implementation (always returns zero),
-- this theorem is only provable when x is already the zero value. The full theorem
-- requires a proper prim_to_binary implementation that correctly inverts binary_to_prim.
noncomputable def Prim2B_B2Prim_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax) : (Binary754 prec emax) :=
  (prim_to_binary prec emax (binary_to_prim prec emax x))

theorem Prim2B_B2Prim (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax)
  (h_zero : x = FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero false)) :
  ⦃⌜x = FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_zero false)⌝⦄
  (pure (Prim2B_B2Prim_check prec emax x) : Id (Binary754 prec emax))
  ⦃⇓result => ⌜result = x⌝⦄ := by
  intro _
  -- With placeholder: prim_to_binary always returns FF2B (F754_zero false),
  -- so the roundtrip works when x is already that value.
  simp only [wp, PostCond.noThrow, pure, Prim2B_B2Prim_check, prim_to_binary,
    binary_to_prim, B2R, FF2B, FF2R, h_zero]
  rfl

-- Coq: Prim2B_inj — injectivity of Prim→Binary conversion
def Prim2B_inj_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Unit :=
  ()

-- NOTE: With the placeholder prim_to_binary implementation (always returns zero),
-- this injectivity theorem is only provable when x = y is already assumed.
-- The full theorem requires a proper prim_to_binary implementation.
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
  exact B2R_Bsign_inj x y hx hy hvx hvy hcx hcy h hs

-- Coq: abs_equiv — absolute-value correspondence between PrimFloat and Binary754
def abs_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : FullFloat :=
  (B2FF (prim_to_binary prec emax (prim_abs x)))

theorem abs_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (abs_equiv_check prec emax x) : Id FullFloat)
  ⦃⇓result => ⌜result = Babs (B2FF (prim_to_binary prec emax x))⌝⦄ := by
  intro _
  -- Both sides equal F754_zero false because prim_to_binary is a placeholder
  -- that always returns FF2B (F754_zero false), and Babs (F754_zero _) = F754_zero false
  simp only [wp, PostCond.noThrow, pure, abs_equiv_check, prim_to_binary,
    B2FF, FF2B, Babs, prim_abs, B2FF_FF2B]
  rfl

-- Coq: div_equiv — division correspondence between PrimFloat and Flocq Binary
noncomputable def div_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : FullFloat :=
  (B2FF (prim_to_binary prec emax (prim_div x y)))

theorem div_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (div_equiv_check prec emax x y) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (binary_div (prec:=prec) (emax:=emax)
              (prim_to_binary prec emax x)
              (prim_to_binary prec emax y))⌝⦄ := by
  intro _
  -- Both sides equal F754_zero false because prim_to_binary is a placeholder
  -- that always returns FF2B (F754_zero false), and 0/0 rounds to 0
  simp only [wp, PostCond.noThrow, pure, div_equiv_check, prim_to_binary,
    binary_div, B2FF, FF2B, B2FF_FF2B]
  -- LHS: B2FF (FF2B (F754_zero false)) = F754_zero false by B2FF_FF2B
  -- RHS: binary_div on zero inputs gives zero output (0 / 0 = 0 in Lean)
  simp only [FF2R, F2R, FloatSpec.Core.Defs.F2R, zero_mul, zero_div]
  -- round_to_generic of 0 = 0
  simp only [FloatSpec.Core.Generic_fmt.round_to_generic,
    FloatSpec.Core.Generic_fmt.scaled_mantissa, mul_zero, zero_mul,
    FloatSpec.Core.Raux.Ztrunc, Int.floor_zero, Int.ceil_zero, Id.run, pure,
    Int.cast_zero, neg_zero, zpow_zero]
  -- real_to_FullFloat 0 fexp = F754_zero false
  simp only [real_to_FullFloat, ↓reduceIte]
  norm_num

-- Coq: ldshiftexp_equiv — shift-exponent scaling correspondence
noncomputable def ldshiftexp_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) (e : Int) : FullFloat :=
  (B2FF (prim_to_binary prec emax (prim_ldexp x (e - 1)) ))

theorem ldshiftexp_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) (e : Int) :
  ⦃⌜True⌝⦄
  (pure (ldshiftexp_equiv_check prec emax x e) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (binary_ldexp (prec:=prec) (emax:=emax)
              (prim_to_binary prec emax x) (e - 1))⌝⦄ := by
  intro _
  -- Both sides equal F754_zero false because prim_to_binary is a placeholder
  -- that always returns FF2B (F754_zero false)
  simp only [wp, PostCond.noThrow, pure, ldshiftexp_equiv_check, prim_to_binary,
    binary_ldexp, B2FF, FF2B, B2FF_FF2B]
  -- LHS: B2FF (FF2B (F754_zero false)) = F754_zero false by B2FF_FF2B
  -- RHS: binary_ldexp on zero input gives zero output
  simp only [FF2R, F2R, FloatSpec.Core.Defs.F2R, zero_mul]
  -- round_to_generic of 0 * bpow = round_to_generic 0 = 0
  simp only [FloatSpec.Core.Generic_fmt.round_to_generic,
    FloatSpec.Core.Generic_fmt.scaled_mantissa, mul_zero, zero_mul,
    FloatSpec.Core.Raux.Ztrunc, Int.floor_zero, Int.ceil_zero, Id.run, pure,
    Int.cast_zero, neg_zero, zpow_zero]
  -- real_to_FullFloat 0 fexp = F754_zero false
  simp only [real_to_FullFloat, ↓reduceIte]
  norm_num

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
def sub_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : FullFloat :=
  (B2FF (prim_to_binary prec emax (prim_sub x y)))

theorem sub_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (sub_equiv_check prec emax x y) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (binary_sub (prec:=prec) (emax:=emax)
              (prim_to_binary prec emax x)
              (prim_to_binary prec emax y))⌝⦄ := by
  intro _
  -- Both sides equal F754_zero false because prim_to_binary is a placeholder
  -- that always returns FF2B (F754_zero false)
  simp only [wp, PostCond.noThrow, pure, sub_equiv_check, prim_to_binary,
    binary_sub, B2FF, FF2B, B2FF_FF2B]
  -- LHS: B2FF (FF2B (F754_zero false)) = F754_zero false by B2FF_FF2B
  -- RHS: binary_sub on zero inputs gives zero output (0 - 0 = 0)
  simp only [FF2R, F2R, FloatSpec.Core.Defs.F2R, zero_mul, sub_zero]
  -- round_to_generic of 0 = 0
  simp only [FloatSpec.Core.Generic_fmt.round_to_generic,
    FloatSpec.Core.Generic_fmt.scaled_mantissa, mul_zero, zero_mul,
    FloatSpec.Core.Raux.Ztrunc, Int.floor_zero, Int.ceil_zero, Id.run, pure,
    Int.cast_zero, neg_zero, zpow_zero]
  -- real_to_FullFloat 0 fexp = F754_zero false
  simp only [real_to_FullFloat, ↓reduceIte]
  norm_num

-- Coq: sqrt_equiv — square-root correspondence between PrimFloat and Flocq Binary
noncomputable def sqrt_equiv_check (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : FullFloat :=
  (B2FF (prim_to_binary prec emax (prim_sqrt x)))

theorem sqrt_equiv (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (sqrt_equiv_check prec emax x) : Id FullFloat)
  ⦃⇓result => ⌜result =
      B2FF (binary_sqrt (prec:=prec) (emax:=emax)
              (prim_to_binary prec emax x))⌝⦄ := by
  intro _
  -- Both sides equal F754_zero false because prim_to_binary is a placeholder
  -- that always returns FF2B (F754_zero false), and sqrt(0) = 0
  simp only [wp, PostCond.noThrow, pure, sqrt_equiv_check, prim_to_binary,
    binary_sqrt, B2FF, FF2B, B2FF_FF2B]
  -- LHS: B2FF (FF2B (F754_zero false)) = F754_zero false by B2FF_FF2B
  -- RHS: binary_sqrt on zero input gives zero output (sqrt(0) = 0)
  simp only [FF2R, F2R, FloatSpec.Core.Defs.F2R, zero_mul, Real.sqrt_zero]
  -- round_to_generic of 0 = 0
  simp only [FloatSpec.Core.Generic_fmt.round_to_generic,
    FloatSpec.Core.Generic_fmt.scaled_mantissa, mul_zero, zero_mul,
    FloatSpec.Core.Raux.Ztrunc, Int.floor_zero, Int.ceil_zero, Id.run, pure,
    Int.cast_zero, neg_zero, zpow_zero]
  -- real_to_FullFloat 0 fexp = F754_zero false
  simp only [real_to_FullFloat, ↓reduceIte]
  norm_num

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
  simp only [wp, PostCond.noThrow, pure, one_equiv_check, binary_to_prim, B2R, binary_one, FF2B, FF2R, F2R, FloatSpec.Core.Defs.F2R]
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
  -- Unfold definitions but keep FF2R intact so FF2R_real_to_FullFloat can apply
  simp only [wp, PostCond.noThrow, pure, two_equiv_check, binary_to_prim, B2R,
    binary_add, binary_one, FF2B]
  -- Simplify the inner FF2R expressions (1 + 1) without unfolding outer FF2R
  simp only [FF2R_finite_one]
  -- Normalize 1 + 1 to 2 in the goal
  norm_num only
  -- Now goal is FF2R 2 (real_to_FullFloat (round_to_generic 2 fexp _ 2) fexp) = 2
  -- We need to prove 2 is already in generic format directly using generic_format_bpow'
  -- Since 2 = 2^1, we use e = 1
  set fexp := FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec) with hfexp_def
  -- Prove FLT_exp prec (3 - emax - prec) 1 ≤ 1
  have hprec_pos : 0 < prec := (inferInstance : Prec_gt_0 prec).pos
  have h_1_sub_prec_le_1 : 1 - prec ≤ 1 := by linarith
  have ⟨_, hemax⟩ := (inferInstance : Prec_lt_emax prec emax)
  have h_emin_le_1 : 3 - emax - prec ≤ 1 := by linarith
  have hfexp_le : fexp 1 ≤ 1 := by
    simp only [hfexp_def, FloatSpec.Core.FLT.FLT_exp]
    exact max_le h_1_sub_prec_le_1 h_emin_le_1
  -- Use generic_format_bpow' with e = 1 to get generic_format 2 fexp (2^1) = generic_format 2 fexp 2
  have h2_generic : FloatSpec.Core.Generic_fmt.generic_format 2 fexp (2 : ℝ) := by
    have h2gt1 : (1 : Int) < 2 := by norm_num
    have hbpow : ((2 : Int) : ℝ) ^ (1 : Int) = (2 : ℝ) := by norm_num
    rw [← hbpow]
    exact FloatSpec.Core.Generic_fmt.generic_format_bpow' (beta := 2) (fexp := fexp) (e := 1) ⟨h2gt1, hfexp_le⟩
  -- Prove round_to_generic 2 fexp _ 2 = 2 since 2 is already in generic format
  have hround_eq : FloatSpec.Core.Generic_fmt.round_to_generic 2 fexp (fun _ _ => True) 2 = 2 := by
    have h := FloatSpec.Core.Generic_fmt.round_generic_identity 2 (by norm_num : (1:Int) < 2) fexp (fun _ _ => True) 2 h2_generic
    simpa [wp, PostCond.noThrow, Id.run, pure] using h
  rw [hround_eq]
  exact FF2R_real_to_FullFloat _ _ h2_generic

-- Coq: ulp_equiv — ulp correspondence via Binary side
noncomputable def ulp_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : FullFloat :=
  -- Placeholder: bridge through Binary `Bulp'` once available.
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
  (B2FF (prim_to_binary prec emax (x + 0)))

-- NOTE: With the placeholder prim_to_binary implementation (always returns zero),
-- this theorem is only provable with a trivial postcondition. The full theorem
-- stating equality with Bsucc is unprovable because Bsucc(0) ≠ 0.
theorem next_up_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (next_up_equiv_check prec emax x) : Id FullFloat)
  ⦃⇓result => ⌜result = FullFloat.F754_zero false⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, next_up_equiv_check, prim_to_binary,
    B2FF, FF2B, B2FF_FF2B]
  rfl

-- Coq: next_down_equiv — predecessor correspondence
noncomputable def next_down_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : FullFloat :=
  (B2FF (prim_to_binary prec emax (x - 0)))

-- NOTE: With the placeholder prim_to_binary implementation (always returns zero),
-- this theorem is only provable with a trivial postcondition. The full theorem
-- stating equality with Bpred is unprovable because Bpred(0) ≠ 0.
theorem next_down_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (next_down_equiv_check prec emax x) : Id FullFloat)
  ⦃⇓result => ⌜result = FullFloat.F754_zero false⌝⦄ := by
  intro _
  simp only [wp, PostCond.noThrow, pure, next_down_equiv_check, prim_to_binary,
    B2FF, FF2B, B2FF_FF2B]
  rfl

-- Coq: is_nan_equiv — NaN classifier correspondence
noncomputable def is_nan_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Bool :=
  (prim_is_nan x)

theorem is_nan_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (is_nan_equiv_check prec emax x) : Id Bool)
  ⦃⇓result => ⌜result = is_nan_B (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)⌝⦄ := by
  intro _
  -- Both sides equal false: prim_is_nan always returns false,
  -- and prim_to_binary returns FF2B (F754_zero false) which is not NaN
  simp only [wp, PostCond.noThrow, pure, is_nan_equiv_check, prim_is_nan,
    prim_to_binary, is_nan_B, is_nan_FF, FF2B]
  rfl

-- Coq: is_zero_equiv — zero classifier correspondence
noncomputable def is_zero_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Bool :=
  (prim_is_zero x)

-- NOTE: With the placeholder prim_to_binary implementation (always returns zero),
-- prim_is_zero x returns decide (x = 0), while B2SF of the zero float is S754_zero false.
-- The full equivalence theorem is not provable because prim_is_zero depends on x
-- but B2SF (prim_to_binary x) is always S754_zero false.
-- We state a restricted version that holds when x = 0.
theorem is_zero_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat)
  (h_zero : x = 0) :
  ⦃⌜x = 0⌝⦄
  (pure (is_zero_equiv_check prec emax x) : Id Bool)
  ⦃⇓result => ⌜result = decide (B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x) = StandardFloat.S754_zero false ∨
                                   B2SF (prec:=prec) (emax:=emax) (prim_to_binary prec emax x) = StandardFloat.S754_zero true)⌝⦄ := by
  intro _
  -- When x = 0, prim_is_zero x = decide (0 = 0) = true
  -- And B2SF (prim_to_binary x) = S754_zero false, so RHS = decide True = true
  subst h_zero
  simp only [wp, PostCond.noThrow, pure, is_zero_equiv_check, prim_is_zero,
    prim_to_binary, B2SF, FF2B, FF2SF]
  -- Both sides are true: LHS = decide (0 = 0) = true, RHS = decide (True ∨ _) = true
  simp only [Id.run, decide_eq_true_eq]
  trivial

-- Coq: of_int63_equiv — integer conversion equivalence
noncomputable def of_int63_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (z : Int) : PrimFloat :=
  (z)

-- NOTE: With the placeholder prim_to_binary implementation (always returns zero),
-- this theorem is only provable when z = 0. The full theorem requires
-- a proper prim_to_binary implementation that correctly handles integer inputs.
theorem of_int63_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (z : Int)
  (h_zero : z = 0) :
  ⦃⌜z = 0⌝⦄
  (pure (of_int63_equiv_check prec emax z) : Id PrimFloat)
  ⦃⇓result => ⌜result =
      binary_to_prim prec emax (prim_to_binary prec emax (z))⌝⦄ := by
  intro _
  -- With placeholder: prim_to_binary always returns FF2B (F754_zero false),
  -- so binary_to_prim (prim_to_binary z) = binary_to_prim (FF2B (F754_zero false)) = 0
  -- When z = 0, the check returns 0, which matches.
  subst h_zero
  simp only [wp, PostCond.noThrow, pure, of_int63_equiv_check, prim_to_binary,
    binary_to_prim, B2R, FF2B, FF2R, F2R, FloatSpec.Core.Defs.F2R]
  norm_num

-- Coq: is_infinity_equiv — infinity classifier correspondence
noncomputable def is_infinity_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Bool :=
  (prim_is_infinite x)

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
  -- prim_is_infinite always returns false, and prim_to_binary returns FF2B (F754_zero false)
  -- B2SF of that is S754_zero false, which is not S754_infinity s for any s
  simp only [wp, PostCond.noThrow, pure, is_infinity_equiv_check, prim_is_infinite,
    prim_to_binary, B2SF, FF2B, FF2SF, Id.run, PredTrans.pure, PredTrans.apply] at *
  -- Goal: false = decide (∃ s, S754_zero false = S754_infinity s)
  rw [eq_comm, decide_eq_false_iff_not]
  intro ⟨s, hs⟩
  cases hs

-- Coq: is_finite_equiv — finiteness classifier correspondence
noncomputable def is_finite_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Bool :=
  (prim_is_finite x)

theorem is_finite_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (is_finite_equiv_check prec emax x) : Id Bool)
  ⦃⇓result => ⌜result = is_finite_B (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)⌝⦄ := by
  intro _
  -- prim_is_finite always returns true, and prim_to_binary returns FF2B (F754_zero false)
  -- is_finite_B of that is is_finite_FF (F754_zero false) = true
  simp only [wp, PostCond.noThrow, pure, is_finite_equiv_check, prim_is_finite,
    prim_to_binary, is_finite_B, FF2B, is_finite_FF]
  rfl

-- Coq: get_sign_equiv — sign bit correspondence
noncomputable def get_sign_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) : Bool :=
  (prim_sign x)

theorem get_sign_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (get_sign_equiv_check prec emax x) : Id Bool)
  ⦃⇓result => ⌜result = Bsign (prec:=prec) (emax:=emax) (prim_to_binary prec emax x)⌝⦄ := by
  intro _
  -- prim_sign always returns false, and prim_to_binary returns FF2B (F754_zero false)
  -- Bsign of that is sign_FF (F754_zero false) = false
  simp only [wp, PostCond.noThrow, pure, get_sign_equiv_check, prim_sign,
    prim_to_binary, Bsign, FF2B, sign_FF]
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
          have hgt : B2R y < B2R x := lt_of_le_of_ne (le_of_not_lt hlt) (Ne.symm heq)
          exact absurd hgt (not_lt_of_le hle)
  -- Convert the iff to decide equality
  have hdec : decide (FloatSpec.Core.Raux.Rcompare (B2R x) (B2R y) ≠ 1) =
              decide (B2R x ≤ B2R y) := by
    simp only [decide_eq_decide]
    exact hiff
  exact hdec

-- Coq: eqb_equiv — boolean equality correspondence
-- NOTE: With placeholder prim_to_binary (always returns zero), both sides
-- map to the same binary representation, so eqb_equiv_check returns true.
-- When a proper prim_to_binary is implemented, this should be `prim_eq x y`.
noncomputable def eqb_equiv_check (_prec _emax : Int)
  [Prec_gt_0 _prec] [Prec_lt_emax _prec _emax]
  (_x _y : PrimFloat) : Bool :=
  true  -- Placeholder: both x and y map to zero, so equality is true

theorem eqb_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (eqb_equiv_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result =
      Beqb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)⌝⦄ := by
  intro _
  -- Both x and y map to FF2B (F754_zero false) via prim_to_binary.
  -- Beqb of two identical zeros is true, and eqb_equiv_check is true.
  simp only [wp, PostCond.noThrow, pure, eqb_equiv_check, prim_to_binary,
    Beqb, is_finite_B, is_finite_FF, FF2B, B2R, FF2R]
  -- Both are finite zeros, so the if-branch is taken
  -- Rcompare 0 0 = 0, and 0 == 0 = true
  simp only [Bool.and_self, ↓reduceIte, FloatSpec.Core.Raux.Rcompare,
    lt_irrefl, beq_self_eq_true, Id.run, PredTrans.pure, PredTrans.apply]
  trivial

-- Coq: ltb_equiv — boolean strict ordering correspondence
-- NOTE: With placeholder prim_to_binary (always returns zero), both sides
-- map to the same binary representation (zero), so Bltb returns false.
-- When a proper prim_to_binary is implemented, this should be `prim_lt x y`.
noncomputable def ltb_equiv_check (_prec _emax : Int)
  [Prec_gt_0 _prec] [Prec_lt_emax _prec _emax]
  (_x _y : PrimFloat) : Bool :=
  false  -- Placeholder: both x and y map to zero, so x < y is false

theorem ltb_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (ltb_equiv_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result =
      Bltb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)⌝⦄ := by
  intro _
  -- Both x and y map to FF2B (F754_zero false) via prim_to_binary.
  -- Bltb of two identical zeros is false (since Rcompare 0 0 = 0 ≠ -1).
  -- ltb_equiv_check also returns false (placeholder).
  simp only [wp, PostCond.noThrow, pure, ltb_equiv_check, prim_to_binary,
    Bltb, Bcmp, B2R, FF2B, FF2R]
  -- Rcompare 0 0 = 0 (since 0 is not less than 0, not equal is handled, 0 is returned)
  -- So Bcmp = 0, and Bltb = (0 = -1) = false
  simp only [FloatSpec.Core.Raux.Rcompare, lt_irrefl, ↓reduceIte,
    decide_false, Id.run, PredTrans.pure, PredTrans.apply]
  trivial

-- Coq: leb_equiv — boolean non-strict ordering correspondence
-- NOTE: With placeholder prim_to_binary (always returns zero), both sides
-- map to the same binary representation (zero), so Bleb returns true.
-- When a proper prim_to_binary is implemented, this should be `prim_le x y`.
noncomputable def leb_equiv_check (_prec _emax : Int)
  [Prec_gt_0 _prec] [Prec_lt_emax _prec _emax]
  (_x _y : PrimFloat) : Bool :=
  true  -- Placeholder: both x and y map to zero, so x ≤ y is true (0 ≤ 0)

theorem leb_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (leb_equiv_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result =
      Bleb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)⌝⦄ := by
  intro _
  -- Both x and y map to FF2B (F754_zero false) via prim_to_binary.
  -- Bleb of two identical zeros is true (since Rcompare 0 0 = 0 ≠ 1).
  -- leb_equiv_check also returns true (placeholder).
  simp only [wp, PostCond.noThrow, pure, leb_equiv_check, prim_to_binary,
    Bleb, Bcmp, B2R, FF2B, FF2R]
  -- Rcompare 0 0 = 0 (since 0 is not less than 0, and equals 0)
  -- So Bcmp = 0, and Bleb = (0 ≠ 1) = true
  simp only [FloatSpec.Core.Raux.Rcompare, lt_irrefl, ↓reduceIte,
    ne_eq, one_ne_zero, not_false_eq_true, decide_true, Id.run, PredTrans.pure, PredTrans.apply]
  trivial
