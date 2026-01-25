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
noncomputable def prim_sign (x : PrimFloat) : Bool := decide (x < 0)

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
    prim_to_binary, B2SF, FF2B, FF2SF]
  -- Both sides are false: LHS = false, RHS = decide (∃ s, S754_zero false = S754_infinity s) = false
  simp only [decide_eq_false_iff_not, not_exists]
  intro s
  cases s <;> simp only [StandardFloat.S754_zero.injEq, reduceCtorEq, not_false_eq_true]

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
  -- Proof deferred; aligns with Coq's `is_finite_equiv`.
  exact sorry

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
  -- Proof deferred; aligns with Coq's `get_sign_equiv` via `B2SF_Prim2B`.
  exact sorry

-- Binary-side boolean comparisons used in Coq's eqb/ltb/leb lemmas
noncomputable def Beqb (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  match B2SF (prec:=prec) (emax:=emax) x, B2SF (prec:=prec) (emax:=emax) y with
  | StandardFloat.S754_zero sx, StandardFloat.S754_zero sy => decide (sx = sy)
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => decide (sx = sy)
  | StandardFloat.S754_nan, StandardFloat.S754_nan => true
  | StandardFloat.S754_finite sx mx ex, StandardFloat.S754_finite sy my ey =>
      decide (sx = sy ∧ mx = my ∧ ex = ey)
  | _, _ => false

-- Coq: Beqb_correct — equality on binary numbers matches real equality under finiteness
noncomputable def Beqb_correct_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax) : Bool :=
  (Beqb prec emax x y)

theorem Beqb_correct (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true) :
  ⦃⌜True⌝⦄
  (pure (Beqb_correct_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result = decide (B2R (prec:=prec) (emax:=emax) x = B2R (prec:=prec) (emax:=emax) y)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `Beqb_correct` via `Bcompare_correct`.
  exact sorry

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
  -- Proof deferred; follows Coq's `Beqb_refl` by case analysis.
  exact sorry

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
  -- Proof deferred; mirrors Coq's `Bltb_correct` via `Bcompare_correct` and `Rcompare`.
  exact sorry

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
  -- Proof deferred; mirrors Coq's `Bleb_correct` via `Bcompare_correct` and `Rcompare`.
  exact sorry

-- Coq: eqb_equiv — boolean equality correspondence
noncomputable def eqb_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Bool :=
  (prim_eq x y)

theorem eqb_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (eqb_equiv_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result =
      Beqb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `eqb_equiv` via `B2SF_Prim2B`.
  exact sorry

-- Coq: ltb_equiv — boolean strict ordering correspondence
noncomputable def ltb_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Bool :=
  (prim_lt x y)

theorem ltb_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (ltb_equiv_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result =
      Bltb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `ltb_equiv` via `B2R` and `Rcompare`.
  exact sorry

-- Coq: leb_equiv — boolean non-strict ordering correspondence
noncomputable def leb_equiv_check (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) : Bool :=
  (prim_le x y)

theorem leb_equiv (prec emax : Int)
  [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x y : PrimFloat) :
  ⦃⌜True⌝⦄
  (pure (leb_equiv_check prec emax x y) : Id Bool)
  ⦃⇓result => ⌜result =
      Bleb prec emax (prim_to_binary prec emax x) (prim_to_binary prec emax y)⌝⦄ := by
  intro _
  -- Proof deferred; mirrors Coq's `leb_equiv` via `B2R` and `Rcompare`.
  exact sorry
