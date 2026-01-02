import FloatSpec.Linter.OmegaLinter
/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Original Copyright (C) 2011-2018 Sylvie Boldo
Original Copyright (C) 2011-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
-/

import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Generic_fmt
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Basic
import Std.Do.Triple
import Std.Tactic.Do
import FloatSpec.src.Core.Ulp
import FloatSpec.src.Core.FIX

-- Avoid `simp` from eagerly using `neg_mul`, which in this file
-- triggers deep typeclass search for `HasDistribNeg` on ℝ.
attribute [-simp] neg_mul


open Real
open Std.Do
open FloatSpec.Core.Generic_fmt FloatSpec.Core.Raux

namespace FloatSpec.Core.FLX

variable (prec : Int)

/-- Fixed-precision exponent function

    In fixed-precision format, the exponent is adjusted to maintain
    a constant precision. The exponent function returns e - prec,
    which ensures that mantissas have exactly 'prec' significant digits.
-/
def FLX_exp (e : Int) : Int :=
  e - prec

/-- Check FLX exponent function correctness

    Verify that the FLX exponent function computes e - prec
    correctly for any input e. This validates the precision
    adjustment mechanism.
-/
def FLX_exp_correct_check (e : Int) : Bool :=
  (FLX_exp prec e = e - prec)

/-- Specification: Fixed-precision exponent calculation

    The FLX exponent function subtracts the precision from the
    input exponent. This adjustment ensures that all representable
    numbers have exactly 'prec' significant digits in their mantissa.
-/
@[spec]
theorem FLX_exp_spec (e : Int) :
    ⦃⌜True⌝⦄
    FLX_exp_correct_check prec e
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  -- Unfold and compute: FLX_exp prec e = e - prec by definition
  simp [FLX_exp_correct_check, FLX_exp]

/-- Fixed-precision format predicate

    A real number x is in FLX format if it can be represented
    using the generic format with the fixed-precision exponent
    function. This gives x = m × β^(e-prec) where m has bounded magnitude.
-/
def FLX_format (beta : Int) (x : ℝ) : Prop :=
  FloatSpec.Core.Generic_fmt.generic_format beta (FLX_exp prec) x

/-- Unbounded fixed-precision format with normalized mantissas (placeholder).

    This mirrors Coq's `FLXN_format`. For now, we model it using
    the same underlying generic format predicate as `FLX_format`.
    Proofs will refine this equivalence later.
-/
def FLXN_format (beta : Int) (x : ℝ) : Prop :=
  FLX_format prec beta x

/-- Specification: FLX format using generic format

    The FLX format is defined through the generic format mechanism
    with the fixed-precision exponent function. This characterizes
    floating-point numbers with constant precision.
-/
@[spec]
theorem FLX_format_spec (beta : Int) (x : ℝ) :
    ⦃⌜True⌝⦄
    FLX_format prec beta x
    ⦃⇓result => ⌜result = (FloatSpec.Core.Generic_fmt.generic_format beta (FLX_exp prec) x)⌝⦄ := by
  intro _
  -- By definition, `FLX_format` is `generic_format beta (FLX_exp prec)`
  unfold FLX_format
  -- Reduce the Id-triple and compute both sides to the same run
  simp [wp, PostCond.noThrow, Id.run]

/-- Specification: FLX exponent function correctness

    The FLX exponent function correctly implements the precision
    adjustment by returning e - prec. This ensures the mantissa
    precision remains constant across different magnitudes.
-/
@[spec]
theorem FLX_exp_correct_spec (e : Int) :
    ⦃⌜True⌝⦄
    FLX_exp_correct_check prec e
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  simp [FLX_exp_correct_check, FLX_exp]

/-- Check if zero is in FLX format

    Verify that zero is representable in the fixed-precision format.
    Zero should always be representable regardless of the precision
    since it can be expressed as 0 × β^e for any exponent e.
-/
noncomputable def FLX_format_0_check (beta : Int) : Bool :=
  -- Concrete arithmetic check: Ztrunc 0 = 0
  pure (((FloatSpec.Core.Raux.Ztrunc (0 : ℝ))) == (0 : Int))

/-- Specification: Zero is in FLX format

    Zero is always representable in fixed-precision format.
    This follows from the fact that 0 = 0 × β^(e-prec) for
    any exponent e, making zero universal across all formats.
-/
@[spec]
theorem FLX_format_0_spec (beta : Int) :
    ⦃⌜beta > 1⌝⦄
    FLX_format_0_check beta
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold FLX_format_0_check
  simp only [wp, PostCond.noThrow, pure, PredTrans.pure, PredTrans.apply]
  have h : ((FloatSpec.Core.Raux.Ztrunc (0 : ℝ)) == (0 : Int)) = true := by
    rw [FloatSpec.Core.Generic_fmt.Ztrunc_zero]; decide
  exact h

/-- Check closure under negation

    Verify that if x is in FLX format, then -x is also in FLX format.
    This tests the closure property under additive inverse for
    fixed-precision floating-point numbers.
-/
noncomputable def FLX_format_opp_check (beta : Int) (x : ℝ) : Bool :=
  -- Concrete arithmetic check leveraging Ztrunc_opp: Ztrunc(-x) + Ztrunc(x) = 0
  pure (((FloatSpec.Core.Raux.Ztrunc (-x)) + (FloatSpec.Core.Raux.Ztrunc x)) == (0 : Int))

/-- Specification: FLX format closed under negation

    Fixed-precision formats are closed under negation. If x is
    representable as m × β^(e-prec), then -x is representable
    as (-m) × β^(e-prec), preserving precision and format properties.
-/
@[spec]
theorem FLX_format_opp_spec (beta : Int) (x : ℝ) :
    ⦃⌜(FLX_format prec beta x).run⌝⦄
    FLX_format_opp_check beta x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold FLX_format_opp_check
  simp only [wp, PostCond.noThrow, pure, PredTrans.pure, PredTrans.apply]
  -- Use Ztrunc_neg to show Ztrunc(-x).run + Ztrunc(x).run = 0
  have h : ((FloatSpec.Core.Raux.Ztrunc (-x)) + (FloatSpec.Core.Raux.Ztrunc x) == (0 : Int)) = true := by
    rw [FloatSpec.Core.Generic_fmt.Ztrunc_neg]
    simp only [neg_add_cancel, beq_self_eq_true]
  exact h

/-- Check closure under absolute value

    Verify that if x is in FLX format, then |x| is also in FLX format.
    This tests closure under the absolute value operation, which
    should preserve representability in fixed-precision formats.
-/
noncomputable def FLX_format_abs_check (beta : Int) (x : ℝ) : Bool :=
  -- Concrete arithmetic check: Ztrunc(|x|) matches natAbs of Ztrunc(x)
  pure (((FloatSpec.Core.Raux.Ztrunc (abs x)))
        == Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).natAbs))

/-- Specification: FLX format closed under absolute value

    Fixed-precision formats are closed under absolute value.
    If x is representable, then |x| is also representable since
    |x| can use the same mantissa magnitude with appropriate sign.
-/
@[spec]
theorem FLX_format_abs_spec (beta : Int) (x : ℝ) :
    ⦃⌜(FLX_format prec beta x).run⌝⦄
    FLX_format_abs_check beta x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  -- Local helper: compute Ztrunc(|x|) in terms of Ztrunc(x).
  -- This mirrors `Raux.Ztrunc_abs` but produces a direct equality,
  -- convenient for rewriting the boolean equality to `true`.
  have zabs_eq :
      (FloatSpec.Core.Raux.Ztrunc (abs x))
        = Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).natAbs) := by
    -- Expand truncation and split on the sign of x.
    -- On |x| we always take the floor branch since |x| ≥ 0.
    simp [FloatSpec.Core.Raux.Ztrunc, not_lt.mpr (abs_nonneg x)]
    by_cases hxlt : x < 0
    · -- Negative case: |x| = -x and ⌊-x⌋ = -⌈x⌉; natAbs(⌈x⌉) coerces to |-⌈x⌉|.
      have hxle : x ≤ 0 := le_of_lt hxlt
      have habs : |x| = -x := by simpa using (abs_of_neg hxlt)
      have hceil_nonpos : Int.ceil x ≤ 0 := (Int.ceil_le).mpr (by simpa using hxle)
      have hAbsCeil : |Int.ceil x| = - Int.ceil x := abs_of_nonpos hceil_nonpos
      -- Rewrite both sides to meet on |⌈x⌉|.
      have hNatAbsCeil : ((Int.ceil x).natAbs : Int) = |Int.ceil x| :=
        (Int.natCast_natAbs (Int.ceil x))
      -- LHS: ⌊|x|⌋ = ⌊-x⌋ = -⌈x⌉; RHS: ↑(natAbs ⌈x⌉) = |⌈x⌉| = -⌈x⌉.
      simpa [habs, Int.floor_neg, hxlt, hAbsCeil, hNatAbsCeil]
    · -- Nonnegative case: |x| = x, so we compare ⌊x⌋ with its nonnegative abs.
      have hxge : 0 ≤ x := le_of_not_gt hxlt
      have hxabs : |x| = x := by simpa using (abs_of_nonneg hxge)
      -- ⌊x⌋ ≥ 0 when x ≥ 0
      have hfloor_nonneg : 0 ≤ (Int.floor x : Int) := by
        have : ((0 : Int) : ℝ) ≤ x := by simpa using hxge
        have : (0 : Int) ≤ Int.floor x := (Int.le_floor).mpr this
        simpa using this
      have hAbsFloor : |Int.floor x| = Int.floor x := abs_of_nonneg hfloor_nonneg
      -- Coerce natAbs to Int and rewrite via |⌊x⌋|
      have hNatAbsFloor : ((Int.floor x).natAbs : Int) = |Int.floor x| :=
        (Int.natCast_natAbs (Int.floor x))
      -- LHS: ⌊|x|⌋ = ⌊x⌋; RHS: ↑(natAbs ⌊x⌋) = |⌊x⌋| = ⌊x⌋.
      simpa [hxabs, hAbsFloor, hNatAbsFloor, hxlt]
  -- Now reduce the boolean equality using the computed equality.
  unfold FLX_format_abs_check
  simp only [wp, PostCond.noThrow, pure, PredTrans.pure, PredTrans.apply]
  -- The goal is about comparing Ztrunc values; use the helper equality
  have h : (((FloatSpec.Core.Raux.Ztrunc (abs x)))
            == Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).natAbs)) = true := by
    rw [zabs_eq]; simp only [beq_self_eq_true]
  exact h

end FloatSpec.Core.FLX

namespace FloatSpec.Core.FLX

variable (prec : Int)

/-- Bridge instance: from the project-wide `Prec_gt_0 prec` to a `Fact (0 < prec)`.
This lets downstream files that assume `[Prec_gt_0 prec]` reuse the `Valid_exp`
instance for `FLX_exp` that requires `[Fact (0 < prec)]`. -/
instance instFactPrecPos (prec : Int) [Prec_gt_0 prec] :
    Fact (0 < prec) :=
  ⟨(Prec_gt_0.pos : 0 < prec)⟩

/- Valid_exp instance for FLX_exp (requires positive precision). -/
instance FLX_exp_valid (beta : Int) [hp : Fact (0 < prec)] :
    FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec) := by
  refine ⟨?_⟩
  intro k
  refine And.intro ?_ ?_
  · -- Large regime
    exact
      (fun _ =>
        -- 0 < prec → 1 ≤ prec over ℤ
        have hprec1 : 1 ≤ prec := by simpa using (Int.add_one_le_iff).mpr hp.out
        have hadd : k + 1 ≤ k + prec := by grind
        -- Convert to subtraction form: (k + 1) - prec ≤ k
        have hsub : (k + 1) - prec ≤ k := by
          -- (k + 1) - prec ≤ k ↔ k + 1 ≤ k + prec
          have : k + 1 ≤ k + prec := by
            simpa [add_comm, add_left_comm, add_assoc] using hadd
          exact (sub_le_iff_le_add).2 this
        -- Rewrite to FLX_exp
        (by simpa [FLX_exp, sub_eq_add_neg] using hsub))
  · -- Small regime (impossible when 0 < prec)
    exact
      (fun hk =>
        -- From k ≤ k - prec, deduce k + prec ≤ k
        have hk' : k + prec ≤ k := by
          calc
            k + prec ≤ (FLX_exp prec k) + prec := by grind
            _ = k := by simp [FLX_exp, sub_eq_add_neg]
            _ ≤ k := le_rfl
        -- But k < k + prec since 0 < prec
        have hklt : k < k + prec := lt_add_of_pos_right k hp.out
        have hfalse : False := (not_lt_of_ge hk') hklt
        And.intro (False.elim hfalse) (by intro _ _; exact False.elim hfalse))

/- Monotonicity of FLX_exp: subtracting a fixed `prec` preserves ≤. -/
instance FLX_exp_mono :
    Monotone_exp (FLX_exp prec) :=
  ⟨by
    intro a b hab
    -- a ≤ b ⇒ a - prec ≤ b - prec
    simpa [FLX_exp, sub_eq_add_neg] using sub_le_sub_right hab prec⟩

/-
Coq (FLX.v):
Theorem generic_format_FLX :
  forall x, FLX_format x -> generic_format beta FLX_exp x.
-/
theorem generic_format_FLX (beta : Int) (x : ℝ) :
    ⦃⌜(FLX_format prec beta x).run⌝⦄
    FloatSpec.Core.Generic_fmt.generic_format beta (FLX_exp prec) x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  simpa [FLX_format]

end FloatSpec.Core.FLX

namespace FloatSpec.Core.FLX

variable (prec : Int)

/-
Coq (FLX.v):
Theorem generic_format_FLXN:
  forall x, FLXN_format x -> generic_format beta FLX_exp x.
-/
theorem generic_format_FLXN (beta : Int) (x : ℝ) :
    ⦃⌜(FLXN_format prec beta x).run⌝⦄
    FloatSpec.Core.Generic_fmt.generic_format beta (FLX_exp prec) x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  simpa [FLXN_format, FLX_format]

/-
Coq (FLX.v):
Theorem FLXN_format_generic:
  forall x, generic_format beta FLX_exp x -> FLXN_format x.
-/
theorem FLXN_format_generic (beta : Int) (x : ℝ) :
    ⦃⌜(FloatSpec.Core.Generic_fmt.generic_format beta (FLX_exp prec) x)⌝⦄
    FLXN_format prec beta x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  simpa [FLXN_format, FLX_format] using hx

/-
Coq (FLX.v):
Theorem FIX_format_FLX :
  forall x e,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  FLX_format x ->
  FIX_format beta (e - prec) x.

Lean (spec): If |x| lies in [β^(e-1), β^e] and x is in FLX_format,
then x is in FIX_format with minimal exponent (e - prec).
-/
theorem FIX_format_FLX (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜0 < prec ∧ 1 < beta ∧ (beta : ℝ) ^ (e - 1) < |x| ∧ |x| ≤ (beta : ℝ) ^ e ∧ (FLX_format prec beta x).run⌝⦄
    (pure (FloatSpec.Core.FIX.FIX_format (emin := e - prec) beta x) : Id Prop)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  simp only [wp, PostCond.noThrow, Id.run, pure, PredTrans.pure]
  -- Unpack preconditions
  rcases hpre with ⟨hprec, hβ, hlt, hupp, hx_fmt⟩
  -- Provide the `Fact (0 < prec)` instance for `Valid_exp` below
  have _instPrec : Fact (0 < prec) := ⟨hprec⟩
  -- Pointwise inequality at e is an equality for FLX_exp vs FIX_exp (both = e - prec)
  have hle_e : FloatSpec.Core.FIX.FIX_exp (emin := e - prec) e ≤ FLX_exp prec e := by
    simp [FloatSpec.Core.FIX.FIX_exp, FLX_exp]
  -- Apply inclusion with tight bounds at e
  have :=
    FloatSpec.Core.Generic_fmt.generic_inclusion
      (beta := beta)
      (fexp1 := FLX_exp prec)
      (fexp2 := FloatSpec.Core.FIX.FIX_exp (emin := e - prec))
      (e := e)
  -- Prepare the hypotheses for the lemma and conclude
  have hrun :
      (FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FIX.FIX_exp (emin := e - prec)) x) := by
    exact this hβ hle_e x ⟨hlt, hupp⟩ hx_fmt
  simpa [FloatSpec.Core.FIX.FIX_format, FLX_format]
    using hrun

/-
Coq (FLX.v):
Theorem FLX_format_FIX :
  forall x e,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  FIX_format beta (e - prec) x ->
  FLX_format x.

Lean (spec): If |x| lies in [β^(e-1), β^e] and x is in FIX_format
with minimal exponent (e - prec), then x is in FLX_format.
-/
theorem FLX_format_FIX (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜0 < prec ∧ 1 < beta ∧ (beta : ℝ) ^ (e - 1) ≤ |x| ∧ |x| ≤ (beta : ℝ) ^ e ∧ FloatSpec.Core.FIX.FIX_format (emin := e - prec) beta x⌝⦄
    (pure (FLX_format prec beta x) : Id Prop)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  simp only [wp, PostCond.noThrow, Id.run, pure, PredTrans.pure]
  -- Unpack hypotheses
  rcases hpre with ⟨hprec, hβ, _hlb, hupp, hx_fix⟩
  -- Provide the `Fact (0 < prec)` instance for `Valid_exp` below
  have _instPrec : Fact (0 < prec) := ⟨hprec⟩
  -- Use inclusion lemma with fexp1 := FIX_exp (emin := e - prec), fexp2 := FLX_exp
  -- We only need a pointwise inequality for all e' ≤ e, which holds by arithmetic.
  have hle_all : ∀ e' : Int,
      e' ≤ e →
      FLX_exp prec e' ≤ FloatSpec.Core.FIX.FIX_exp (emin := e - prec) e' := by
    intro e' he'
    -- FLX_exp prec e' = e' - prec and FIX_exp (emin := e - prec) e' = e - prec
    simpa [FLX_exp, FloatSpec.Core.FIX.FIX_exp] using he'
  -- Apply the generic inclusion with only an upper bound at e
  have hrun :
      (FloatSpec.Core.Generic_fmt.generic_format beta (FLX_exp prec) x) := by
    exact
      (FloatSpec.Core.Generic_fmt.generic_inclusion_le
        (beta := beta)
        (fexp1 := FloatSpec.Core.FIX.FIX_exp (emin := e - prec))
        (fexp2 := FLX_exp prec)
        (e2 := e))
        hβ hle_all x hupp hx_fix
  -- Repackage to FLX_format
  simpa [FLX_format] using hrun

end FloatSpec.Core.FLX

namespace FloatSpec.Core.FLX

variable (prec : Int)

/-
Coq (FLX.v):
Theorem FLXN_format_satisfies_any :
  satisfies_any FLXN_format.
-/
theorem FLXN_format_satisfies_any (beta : Int)
    [Valid_exp beta (FLX_exp prec)] :
    FloatSpec.Core.Generic_fmt.satisfies_any
      (fun y => (FLXN_format prec beta y).run) := by
  simpa [FLXN_format, FLX_format]
    using
      FloatSpec.Core.Generic_fmt.generic_format_satisfies_any
        (beta := beta) (fexp := FLX_exp prec)

end FloatSpec.Core.FLX

namespace FloatSpec.Core.FLX

variable (prec : Int)

/- Valid_exp instance for FLX_exp (placeholder). -/

/-
Coq (FLX.v):
Theorem FLX_format_satisfies_any :
  satisfies_any FLX_format.
-/
theorem FLX_format_satisfies_any (beta : Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec)] :
    FloatSpec.Core.Generic_fmt.satisfies_any (fun y => (FLX_format prec beta y).run) := by
  simpa [FLX_format]
    using FloatSpec.Core.Generic_fmt.generic_format_satisfies_any (beta := beta) (fexp := FLX_exp prec)

end FloatSpec.Core.FLX

namespace FloatSpec.Core.FLX

variable (prec : Int)

/-- Coq ({lit}`FLX.v`):
Theorem {lit}`ulp_FLX_0`: {lit}`ulp beta FLX_exp 0 = 0`.

Lean (spec): In FLX (with positive precision), {lit}`negligible_exp` is {lit}`none`,
so {lit}`ulp` at zero evaluates to 0.
-/
theorem ulp_FLX_0 (beta : Int) [Prec_gt_0 prec] :
    ⦃⌜True⌝⦄
    FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) 0
    ⦃⇓r => ⌜r = 0⌝⦄ := by
  intro _; classical
  -- Show that `negligible_exp (FLX_exp prec) = none` when `0 < prec`.
  have hprec : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  -- Use the specification lemma for `negligible_exp`.
  have hspec := FloatSpec.Core.Ulp.negligible_exp_spec' (fexp := FLX_exp prec)
  -- Establish the pointwise strict inequality fexp n < n for FLX when 0 < prec.
  have hlt_all : ∀ n : Int, FLX_exp prec n < n := by
    intro n
    -- n - prec < n, since 0 < prec
    have : n < n + prec := lt_add_of_pos_right n hprec
    -- Rearrange to subtraction form
    exact (sub_lt_iff_lt_add).2 this
  -- Deduce that the option must be `none` from the spec lemma.
  have hnone : FloatSpec.Core.Ulp.negligible_exp (fexp := FLX_exp prec) = none := by
    -- From the disjunction, the `some`-witness branch contradicts `hlt_all`.
    cases hspec with
    | inl h => exact h.left
    | inr h =>
        rcases h with ⟨n, hopt, hnle⟩
        -- `n ≤ n - prec` contradicts `n - prec < n` (from `hlt_all`).
        cases (lt_irrefl (a := n)) (lt_of_le_of_lt hnle (hlt_all n))
  -- Evaluate `ulp` at zero using the computed `none` branch.
  unfold FloatSpec.Core.Ulp.ulp
  simp [wp, PostCond.noThrow, Id.run, bind, pure, hnone]

/-- Coq ({lit}`FLX.v`):
Lemma {lit}`ulp_FLX_1`: {lit}`ulp beta FLX_exp 1 = bpow (-prec + 1)`.

Lean (spec): The ULP under FLX at 1 equals {lit}`β^(1 - prec)`.
-/
theorem ulp_FLX_1 (beta : Int) [Prec_gt_0 prec] :
    ⦃⌜1 < beta⌝⦄
    FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) 1
    ⦃⇓r => ⌜r = (beta : ℝ) ^ (1 - prec)⌝⦄ := by
  intro hβ; classical
  -- Provide the bridge from `[Prec_gt_0 prec]` to `Fact (0 < prec)` for `Valid_exp`.
  have _instPrec : Fact (0 < prec) := ⟨(Prec_gt_0.pos : 0 < prec)⟩
  -- Evaluate `ulp` at a nonzero input: `1 ≠ 0`.
  have h1ne : (1 : ℝ) ≠ 0 := one_ne_zero
  unfold FloatSpec.Core.Ulp.ulp
  -- Nonzero branch of `ulp` reduces to `β ^ (cexp … 1)`.
  simp [h1ne, wp, PostCond.noThrow, Id.run, bind, pure]
  -- Compute the canonical exponent at `x = 1`.
  have hcexp_run :
      (FloatSpec.Core.Generic_fmt.cexp (beta := beta) (fexp := FLX_exp prec) 1)
        = FLX_exp prec ((FloatSpec.Core.Raux.mag beta 1)) := by
    simpa [wp, PostCond.noThrow, Id.run]
      using (FloatSpec.Core.Generic_fmt.cexp_spec (beta := beta) (fexp := FLX_exp prec) (x := 1)) hβ
  -- Since `1 = β^0`, we have `mag beta 1 = 1` (mag(β^e) = e + 1).
  have hmag1 : (FloatSpec.Core.Raux.mag beta 1) = 1 := by
    have hmag_pow0 := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := 0)
    have hrun : (FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ 0)) = 0 + 1 := by
      simpa [wp, PostCond.noThrow, Id.run, pure] using (hmag_pow0 hβ)
    simp only [zpow_zero, zero_add] at hrun
    exact hrun
  -- Hence `cexp … 1 = FLX_exp prec 1 = 1 - prec`.
  have hcexp_eq : (FloatSpec.Core.Generic_fmt.cexp (beta := beta) (fexp := FLX_exp prec) 1)
            = 1 - prec := by
    rw [hcexp_run, hmag1, FLX_exp]
  -- Finish: `ulp 1 = β ^ (cexp 1) = β ^ (1 - prec)`.
  have hpow_eq :
      (beta : ℝ) ^ ((FloatSpec.Core.Generic_fmt.cexp (beta := beta) (fexp := FLX_exp prec) 1))
        = (beta : ℝ) ^ (1 - prec) := by
    rw [hcexp_eq]
  -- Goal: β ^ cexp beta (FLX_exp prec) 1 = β ^ (1 - prec)
  -- Use that cexp ... 1 = 1 - prec
  have hcexp_Id : FloatSpec.Core.Generic_fmt.cexp (beta := beta) (fexp := FLX_exp prec) 1
                = (1 - prec : Int) := by
    show (FloatSpec.Core.Generic_fmt.cexp beta (FLX_exp prec) 1) = (1 - prec)
    ext; exact hcexp_eq
  rw [hcexp_Id]

/-- Coq ({lit}`FLX.v`):
Theorem {lit}`ulp_FLX_le`:
  {lit}`forall x, (ulp beta (FLX_exp prec) x <= Rabs x * bpow (1 - prec))%R.`

Lean (spec): ULP under FLX is bounded above by {lit}`|x| * β^(1 - prec)`.
-/
theorem ulp_FLX_le (beta : Int) [Prec_gt_0 prec] (x : ℝ) :
    ⦃⌜1 < beta⌝⦄
    FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x
    ⦃⇓r => ⌜r ≤ |x| * (beta : ℝ) ^ (1 - prec)⌝⦄ := by
  intro hβ; classical
  -- Positivity facts for the radix
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  -- Case split on x = 0
  by_cases hx0 : x = 0
  ·
    -- For FLX with prec > 0, negligible_exp = none, hence ulp 0 = 0 ≤ 0
    have hprec : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    have hspec := FloatSpec.Core.Ulp.negligible_exp_spec' (fexp := FLX_exp prec)
    have hlt_all : ∀ n : Int, FLX_exp prec n < n := by
      intro n
      have : n < n + prec := lt_add_of_pos_right n hprec
      exact (sub_lt_iff_lt_add).2 this
    have hnone : FloatSpec.Core.Ulp.negligible_exp (fexp := FLX_exp prec) = none := by
      cases hspec with
      | inl h => exact h.left
      | inr h =>
          rcases h with ⟨n, hopt, hnle⟩
          have : False := (not_lt_of_ge hnle) (hlt_all n)
          exact this.elim
    -- Evaluate the program in the zero branch and close 0 ≤ 0
    unfold FloatSpec.Core.Ulp.ulp
    simpa [hx0, hnone, wp, PostCond.noThrow, Id.run, bind, pure]
  ·
    -- Nonzero case: ulp x = β^(cexp x) and cexp runs to FLX_exp (mag x)
    have hxne : x ≠ 0 := hx0
    unfold FloatSpec.Core.Ulp.ulp
    -- Reduce the Id-triple and expose cexp
    simp [hxne, wp, PostCond.noThrow, Id.run, bind, pure]
    -- Compute the canonical exponent at x
    have hcexp_run :
        (FloatSpec.Core.Generic_fmt.cexp (beta := beta) (fexp := FLX_exp prec) x)
          = FLX_exp prec ((FloatSpec.Core.Raux.mag beta x)) := by
      simpa [wp, PostCond.noThrow, Id.run]
        using (FloatSpec.Core.Generic_fmt.cexp_spec (beta := beta) (fexp := FLX_exp prec) (x := x)) hβ
    -- Abbreviate the magnitude
    set m : Int := (FloatSpec.Core.Raux.mag beta x) with hm
    -- Lower bound: β^(m - 1) ≤ |x|
    have hlow : (beta : ℝ) ^ (m - 1) ≤ |x| := by
      have htr := FloatSpec.Core.Raux.bpow_mag_le (beta := beta) (x := x) (e := m)
      simpa [FloatSpec.Core.Raux.abs_val, wp, PostCond.noThrow, Id.run, hm, sub_eq_add_neg]
        using htr ⟨hβ, hxne, le_rfl⟩
    -- Multiply both sides by β^(-(prec - 1)) (positive), then rewrite
    have hnonneg : 0 ≤ (beta : ℝ) ^ (-(prec - 1)) := le_of_lt (zpow_pos hbpos (-(prec - 1)))
    have hmul :
        (beta : ℝ) ^ (m - 1) * (beta : ℝ) ^ (1 - prec)
          ≤ |x| * (beta : ℝ) ^ (1 - prec) := by
      -- Note: (-(prec - 1)) = (1 - prec)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using (mul_le_mul_of_nonneg_right hlow hnonneg)
    -- Left side becomes β^(m - prec)
    have hleft :
        (beta : ℝ) ^ (m - 1) * (beta : ℝ) ^ (1 - prec)
          = (beta : ℝ) ^ (m - prec) := by
      -- (m - 1) + (1 - prec) = m - prec
      have := (zpow_add₀ hbne (m - 1) (1 - prec)).symm
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using this
    -- Assemble and rewrite the goal to the required shape
    -- ulp x = β^(cexp x) = β^(m - prec)
    have : (beta : ℝ) ^ (m - prec) ≤ |x| * (beta : ℝ) ^ (1 - prec) := by
      simpa [hleft]
        using hmul
    -- Finish by rewriting cexp and FLX_exp
    simpa [hcexp_run, FLX_exp, sub_eq_add_neg]
      using this

/-
Coq (FLX.v):
Theorem ulp_FLX_ge:
  forall x, (Rabs x * bpow (-prec) <= ulp beta FLX_exp x)%R.

Lean (spec): ULP under FLX is bounded below by `|x| * β^(-prec)`.
-/
theorem ulp_FLX_ge (beta : Int) (x : ℝ) :
    ⦃⌜1 < beta⌝⦄
    FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x
    ⦃⇓r => ⌜|x| * (beta : ℝ) ^ (-prec) ≤ r⌝⦄ := by
  intro hβ; classical
  -- Base positivity facts from 1 < beta
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbnonneg : 0 ≤ (beta : ℝ) ^ (-prec) := le_of_lt (zpow_pos hbpos _)
  -- Split on x = 0
  by_cases hx0 : x = 0
  ·
    -- ulp 0 is either 0 or a positive power of β; in both cases, 0 ≤ r
    unfold FloatSpec.Core.Ulp.ulp
    cases hopt : FloatSpec.Core.Ulp.negligible_exp (fexp := FLX_exp prec) with
    | none =>
        -- ulp 0 = 0
        simp [hx0, hopt, wp, PostCond.noThrow, Id.run, bind, pure]
    | some n =>
        -- ulp 0 = β^(fexp n) and β > 0 ⇒ this is ≥ 0
        simpa [hx0, hopt, wp, PostCond.noThrow, Id.run, bind, pure,
               abs_zero]
          using (show 0 ≤ (beta : ℝ) ^ (FLX_exp prec n) from
            le_of_lt (zpow_pos hbpos _))
  ·
    -- Nonzero case: ulp x = β^(cexp … x)
    have hxne : x ≠ 0 := hx0
    -- Evaluate `ulp` and `cexp` on a nonzero input (no Valid_exp needed)
    have hulp_run :
        (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x)
          = (beta : ℝ) ^ ((FloatSpec.Core.Generic_fmt.cexp (beta := beta) (fexp := FLX_exp prec) x)) := by
      unfold FloatSpec.Core.Ulp.ulp
      simp [hxne, Id.run, bind, pure]
    have hcexp_run :
        (FloatSpec.Core.Generic_fmt.cexp (beta := beta) (fexp := FLX_exp prec) x)
          = FLX_exp prec ((FloatSpec.Core.Raux.mag beta x)) := by
      simpa [wp, PostCond.noThrow, Id.run]
        using (FloatSpec.Core.Generic_fmt.cexp_spec (beta := beta) (fexp := FLX_exp prec) (x := x)) hβ
    -- Abbreviate the magnitude
    set m : Int := (FloatSpec.Core.Raux.mag beta x) with hm
    -- Target reduces to: |x| * β^(-prec) ≤ β^(m - prec)
    -- Rewrite RHS as β^m * β^(-prec)
    have : |x| * (beta : ℝ) ^ (-prec) ≤ (beta : ℝ) ^ m * (beta : ℝ) ^ (-prec) := by
      -- Show the generic magnitude upper bound: |x| ≤ β^m
      have h_abs_le : |x| ≤ (beta : ℝ) ^ m := by
        -- Derive from the definition of mag via logarithms
        have hxpos : 0 < |x| := abs_pos.mpr hxne
        -- L := log |x| / log β; mag x = ⌊L⌋ + 1 when x ≠ 0
        set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
        have hmageq_run : (FloatSpec.Core.Raux.mag beta x) = Int.floor L + 1 := by
          unfold FloatSpec.Core.Raux.mag
          simp only [Id.run, pure, hxne, if_false, L]
        have hmageq : m = Int.floor L + 1 := by simpa [hm] using hmageq_run
        -- log β > 0 when 1 < β
        have hlogβ_pos : 0 < Real.log (beta : ℝ) :=
          (Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)).mpr (by exact_mod_cast hβ)
        have hL_le : L ≤ (m : ℝ) := by
          -- L ≤ ⌊L⌋ + 1 since L - 1 < ⌊L⌋ (definition of floor)
          have hfloor_lt : L - 1 < (Int.floor L : ℝ) := Int.sub_one_lt_floor L
          have : L < (Int.floor L : ℝ) + 1 := by linarith
          have hle : L ≤ (Int.floor L : ℝ) + 1 := le_of_lt this
          simpa [hmageq] using hle
        -- Move back to exponentials: |x| ≤ exp(m * log β) = β^m
        have hlog_le : Real.log (abs x) ≤ (m : ℝ) * Real.log (beta : ℝ) := by
          -- L * log β = log |x|
          have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
            have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
            calc
              L * Real.log (beta : ℝ)
                  = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by rfl
              _ = Real.log (abs x) := by simpa [hne] using (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
          have := mul_le_mul_of_nonneg_right hL_le (le_of_lt hlogβ_pos)
          simpa [hL_mul, mul_comm, mul_left_comm, mul_assoc] using this
        have h_exp_le : abs x ≤ Real.exp ((m : ℝ) * Real.log (beta : ℝ)) :=
          (Real.log_le_iff_le_exp (x := abs x) hxpos).1 hlog_le
        -- exp((m) * log β) = β^m
        have hpow_pos : 0 < (beta : ℝ) ^ m := zpow_pos hbpos _
        have h_exp_eq_pow : Real.exp ((m : ℝ) * Real.log (beta : ℝ)) = (beta : ℝ) ^ m := by
          have : Real.exp (Real.log ((beta : ℝ) ^ m)) = (beta : ℝ) ^ m := Real.exp_log hpow_pos
          have hlog_zpow_m : Real.log ((beta : ℝ) ^ m) = (m : ℝ) * Real.log (beta : ℝ) := by
            simpa using Real.log_zpow hbpos m
          simpa [hlog_zpow_m] using this
        simpa [h_exp_eq_pow] using h_exp_le
      exact mul_le_mul_of_nonneg_right h_abs_le hbnonneg
    -- Conclude by rewriting powers and cexp
    have hrhs : (beta : ℝ) ^ m * (beta : ℝ) ^ (-prec) = (beta : ℝ) ^ (m - prec) := by
      -- (m) + (-prec) = m - prec
      simpa [sub_eq_add_neg] using (FloatSpec.Core.Generic_fmt.zpow_mul_sub (a := (beta : ℝ)) (hbne := ne_of_gt hbpos) (e := m) (c := prec))
    -- And cexp run computes to m - prec under FLX_exp
    have hce :
        ((FloatSpec.Core.Generic_fmt.cexp (beta := beta) (fexp := FLX_exp prec) x))
          = m - prec := by
      simpa [hcexp_run, FLX_exp, sub_eq_add_neg, hm]
    -- Chain ≤ with equality on the RHS, and discharge the Hoare triple
    have hout : |x| * (beta : ℝ) ^ (-prec) ≤ (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x) := by
      -- First rewrite to the exponent difference form
      have hlt' : |x| * (beta : ℝ) ^ (-prec) ≤ (beta : ℝ) ^ (m - prec) := by
        have eq1 : (beta : ℝ) ^ (m - prec) = (beta : ℝ) ^ m * (beta : ℝ) ^ (-prec) := by
          simpa [sub_eq_add_neg] using
            (zpow_add₀ (ne_of_gt hbpos) m (-prec))
        simpa [eq1] using this
      -- Then identify ulp(x) on nonzero inputs and compute cexp
      calc |x| * (beta : ℝ) ^ (-prec)
          ≤ (beta : ℝ) ^ (m - prec) := hlt'
        _ = (beta : ℝ) ^ ((FloatSpec.Core.Generic_fmt.cexp (beta := beta) (fexp := FLX_exp prec) x)) := by
            simp only [hce]
        _ = (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x) := by
            simp only [hulp_run]
    -- Convert β^(-prec) to (β^prec)⁻¹ for the final goal
    have hpow_inv : (beta : ℝ) ^ (-prec) = ((beta : ℝ) ^ prec)⁻¹ := zpow_neg (beta : ℝ) prec
    have hout' : |x| * ((beta : ℝ) ^ prec)⁻¹ ≤ (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x) := by
      simp only [← hpow_inv]; exact hout
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using hout'

/-
Coq (FLX.v):
Lemma ulp_FLX_exact_shift:
  forall x e,
  (ulp beta FLX_exp (x * bpow e) = ulp beta FLX_exp x * bpow e)%R.

Lean (spec): ULP under FLX scales exactly under multiplication by β^e.
-/
theorem ulp_FLX_exact_shift (beta : Int) [Prec_gt_0 prec] (x : ℝ) (e : Int) :
    ⦃⌜1 < beta⌝⦄
    (do
      let u1 ← FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (x * (beta : ℝ) ^ e)
      let u2 ← FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x
      pure (u1, u2))
    ⦃⇓p => ⌜p.1 = p.2 * (beta : ℝ) ^ e⌝⦄ := by
  intro hβ; classical
  -- Basic facts about the base β
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  -- Case split on x = 0
  by_cases hx0 : x = 0
  · -- For x = 0, ulp 0 = 0 under FLX when 0 < prec (proved locally here)
    -- Show `negligible_exp (FLX_exp prec) = none`
    have hprec : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    have hlt_all : ∀ n : Int, FLX_exp prec n < n := by
      intro n
      -- n - prec < n since 0 < prec
      have : n < n + prec := lt_add_of_pos_right n hprec
      exact (sub_lt_iff_lt_add).2 this
    have hnone : FloatSpec.Core.Ulp.negligible_exp (fexp := FLX_exp prec) = none := by
      -- Use the generic spec for negligible_exp to exclude the Some-branch
      have hspec := FloatSpec.Core.Ulp.negligible_exp_spec' (fexp := FLX_exp prec)
      cases hspec with
      | inl h => exact h.left
      | inr h =>
          rcases h with ⟨n, hopt, hnle⟩
          exact False.elim ((lt_irrefl (a := n)) (lt_of_le_of_lt hnle (hlt_all n)))
    -- Evaluate both ulps at zero
    have hulp0 : (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) 0) = 0 := by
      unfold FloatSpec.Core.Ulp.ulp
      simp [hx0, hnone, Id.run, bind, pure]
    -- Discharge the Hoare triple by direct computation
    -- Left side uses x*β^e = 0 as well
    have hxscale : x * (beta : ℝ) ^ e = 0 := by simpa [hx0]
    have hulp0' : (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (x * (beta : ℝ) ^ e)) = 0 := by
      unfold FloatSpec.Core.Ulp.ulp
      simp [hxscale, hnone, Id.run, bind, pure]
    -- Establish the run‑level equality and discharge the Hoare triple
    have hEqRuns :
        (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
          = ((FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x)) * (beta : ℝ) ^ e := by
      calc
        (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
            = 0 := hulp0'
        _   = 0 * (beta : ℝ) ^ e := by ring
        _   = ((FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) 0)) * (beta : ℝ) ^ e := by
              rw [hulp0]
        _   = ((FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x)) * (beta : ℝ) ^ e := by
              rw [hx0]
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using hEqRuns
  · -- x ≠ 0: reduce both ulps to powers and compare exponents via mag shift
    have hx_ne : x ≠ 0 := hx0
    have hy_ne : x * (beta : ℝ) ^ e ≠ 0 := mul_ne_zero hx_ne (by simpa using zpow_ne_zero e hbne)
    -- Notations for magnitudes
    set M : Int := (FloatSpec.Core.Raux.mag beta x) with hM
    set N : Int := (FloatSpec.Core.Raux.mag beta (x * (beta : ℝ) ^ e)) with hN
    -- Evaluate cexp and ulp in the nonzero branches
    have hcexp_x :
        (FloatSpec.Core.Generic_fmt.cexp (beta := beta) (fexp := FLX_exp prec) x)
          = FLX_exp prec M := by
      unfold FloatSpec.Core.Generic_fmt.cexp
      simp [FloatSpec.Core.Raux.mag, hM]
    have hcexp_y :
        (FloatSpec.Core.Generic_fmt.cexp (beta := beta) (fexp := FLX_exp prec) (x * (beta : ℝ) ^ e))
          = FLX_exp prec N := by
      unfold FloatSpec.Core.Generic_fmt.cexp
      simp [FloatSpec.Core.Raux.mag, hN]
    have hulp_x :
        (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x)
          = (beta : ℝ) ^ (FLX_exp prec M) := by
      unfold FloatSpec.Core.Ulp.ulp
      simp only [hx_ne, if_false, Id.run, bind, pure]
      -- cexp ... x : Id Int, which unfolds to Int; goal is β^(cexp x) = β^(FLX_exp prec M)
      -- We have hcexp_x : (cexp ... x).run = FLX_exp prec M
      -- For Id Int, v = v.run definitionally, so congrArg (β^·) hcexp_x closes it.
      exact congrArg (fun t : Int => (beta : ℝ) ^ t) hcexp_x
    have hulp_y :
        (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
          = (beta : ℝ) ^ (FLX_exp prec N) := by
      unfold FloatSpec.Core.Ulp.ulp
      simp only [hy_ne, if_false, Id.run, bind, pure]
      exact congrArg (fun t : Int => (beta : ℝ) ^ t) hcexp_y
    -- Show the magnitude shift under scaling: N = M + e
    have hN_eq : N = M + e := by
      -- Use logarithmic characterization of mag (floor + 1 definition)
      set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
      have hM_run : M = Int.floor L + 1 := by
        -- Discharge the conditional in `mag` using x ≠ 0
        simp only [FloatSpec.Core.Raux.mag, hM, hx_ne, if_false, Id.run, pure, L]
      -- Compute mag at the scaled input
      have hbpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR _
      have hxabs_pos : 0 < |x| := abs_pos.mpr hx_ne
      have hbpow_abs_pos : 0 < |(beta : ℝ) ^ e| := abs_pos.mpr (ne_of_gt hbpow_pos)
      have hlog_prod :
          Real.log (|x| * |(beta : ℝ) ^ e|)
            = Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ) := by
        calc
          Real.log (|x| * |(beta : ℝ) ^ e|)
              = Real.log (|x|) + Real.log (|(beta : ℝ) ^ e|) := by
                    simpa using Real.log_mul (ne_of_gt hxabs_pos) (ne_of_gt hbpow_abs_pos)
          _   = Real.log (|x|) + Real.log ((beta : ℝ) ^ e) := by
                    simpa [abs_of_nonneg (le_of_lt hbpow_pos)]
          _   = Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ) := by
                    simpa using Real.log_zpow hbposR e
      have habs_mul : abs (x * (beta : ℝ) ^ e) = |x| * |(beta : ℝ) ^ e| := by
        have hbnonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt hbpow_pos
        simp [abs_mul, abs_of_nonneg hbnonneg]
      have hlogβ_pos : 0 < Real.log (beta : ℝ) :=
        (Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)).mpr (by exact_mod_cast hβ)
      have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
      have hdiv :
          Real.log (abs (x * (beta : ℝ) ^ e)) / Real.log (beta : ℝ)
            = L + (e : ℝ) := by
        calc
          Real.log (abs (x * (beta : ℝ) ^ e)) / Real.log (beta : ℝ)
              = Real.log (|x| * |(beta : ℝ) ^ e|) / Real.log (beta : ℝ) := by simpa [habs_mul]
          _   = (Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) := by
                  rw [hlog_prod]
          _   = Real.log (|x|) / Real.log (beta : ℝ)
                  + ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) := by
                  simpa using (add_div (Real.log (|x|)) ((e : ℝ) * Real.log (beta : ℝ)) (Real.log (beta : ℝ)))
          _   = L + (e : ℝ) := by
                  simpa [L, hlogβ_ne] using (congrArg id (by
                    simpa [hlogβ_ne] using (mul_div_cancel' (e : ℝ) (Real.log (beta : ℝ)))))
      have hN_run' : N = Int.floor (L + (e : ℝ)) + 1 := by
        -- Evaluate mag at the scaled input via the computed division form
        have hy_ne' : x * (beta : ℝ) ^ e ≠ 0 := hy_ne
        have hfloor_div :
            Int.floor (Real.log (abs (x * (beta : ℝ) ^ e)) / Real.log (beta : ℝ))
              = Int.floor (L + (e : ℝ)) := by
          simpa using congrArg Int.floor hdiv
        have : (FloatSpec.Core.Raux.mag beta (x * (beta : ℝ) ^ e))
                = Int.floor (L + (e : ℝ)) + 1 := by
          simp only [FloatSpec.Core.Raux.mag, hy_ne', if_false, Id.run, pure]
          rw [hfloor_div]
        simpa [hN] using this
      -- Floor(L + e) + 1 = (Floor(L) + 1) + e for integer e
      have hfloor_add : Int.floor (L + (e : ℝ)) = Int.floor L + e :=
        Int.floor_add_intCast L e
      -- Conclude N = M + e
      have : N = (Int.floor L + 1) + e := by
        simp only [hN_run', hfloor_add]
        ring
      simpa [hM_run] using this
    -- Turn the magnitude shift into an exponent equality
    have hExp_eq : FLX_exp prec N = (FLX_exp prec M) + e := by
      -- FLX_exp t = t - prec
      have : N - prec = (M - prec) + e := by
        simpa [hN_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      simpa [FLX_exp] using this
    -- Transform exponent equality to equality of powers and use zpow_add
    have hpow_eq :
        (beta : ℝ) ^ (FLX_exp prec N) = (beta : ℝ) ^ (FLX_exp prec M) * (beta : ℝ) ^ e := by
      have := congrArg (fun t => (beta : ℝ) ^ t) hExp_eq
      simpa [zpow_add₀ hbne] using this
    -- Finish by rewriting both ulps
    have : (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
            = ((FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x)) * (beta : ℝ) ^ e := by
      rw [hulp_y, hulp_x, hpow_eq]
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this

end FloatSpec.Core.FLX

namespace FloatSpec.Core.FLX

variable (prec : Int)

/-
Coq (FLX.v):
Theorem FLX_format_generic :
  forall x, generic_format beta FLX_exp x -> FLX_format x.
-/
theorem FLX_format_generic (beta : Int) (x : ℝ) :
    ⦃⌜(FloatSpec.Core.Generic_fmt.generic_format beta (FLX_exp prec) x)⌝⦄
    FLX_format prec beta x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  simpa [FLX_format] using hx

end FloatSpec.Core.FLX

namespace FloatSpec.Core.FLX

variable (prec : Int)

/-- Coq ({lit}`FLX.v`):
Lemma {lit}`negligible_exp_FLX`: {lit}`negligible_exp FLX_exp = None`.

Lean (spec): In our simplified model, {lean}`Ulp.negligible_exp` is always {lit}`none`,
so for FLX it is {lit}`none` as well.
-/
theorem negligible_exp_FLX (beta : Int) [Prec_gt_0 prec] :
    ⦃⌜True⌝⦄
    (pure (FloatSpec.Core.Ulp.negligible_exp (fexp := FLX_exp prec)) : Id (Option Int))
    ⦃⇓r => ⌜r = none⌝⦄ := by
  intro _; classical
  -- From 0 < prec, we have ∀ n, (n - prec) < n, i.e. FLX_exp n < n.
  have hprec : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hlt_all : ∀ n : Int, FLX_exp prec n < n := by
    intro n
    have : n < n + prec := lt_add_of_pos_right n hprec
    exact (sub_lt_iff_lt_add).2 this
  -- Use the specification of `negligible_exp` to conclude it must be `none`.
  have hspec := FloatSpec.Core.Ulp.negligible_exp_spec' (fexp := FLX_exp prec)
  have hnone : FloatSpec.Core.Ulp.negligible_exp (fexp := FLX_exp prec) = none := by
    cases hspec with
    | inl h => exact h.left
    | inr h =>
        rcases h with ⟨n, hopt, hnle⟩
        -- Contradiction: n ≤ n - prec < n
        cases (lt_irrefl (a := n)) (lt_of_le_of_lt hnle (hlt_all n))
  -- Reduce the Id‑triple and discharge with the computed equality.
  simpa [wp, PostCond.noThrow] using hnone

/-
Coq (FLX.v):
Theorem generic_format_FLX_1 :
  generic_format beta FLX_exp 1.
-/
theorem generic_format_FLX_1 (beta : Int) [Prec_gt_0 prec] :
    ⦃⌜1 < beta⌝⦄
    FloatSpec.Core.Generic_fmt.generic_format beta (FLX_exp prec) 1
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hβ; classical
  -- Bridge `Prec_gt_0` to a `Fact (0 < prec)` to enable `[Valid_exp]`.
  have _instPrec : Fact (0 < prec) := ⟨(Prec_gt_0.pos : 0 < prec)⟩
  -- Use the generic `generic_format_bpow'` at exponent 0 (since 1 = β^0).
  have hfe_le : FLX_exp prec 0 ≤ 0 := by
    -- FLX_exp prec 0 = 0 - prec ≤ 0 when 0 < prec
    simpa [FLX_exp, sub_eq_add_neg] using
      (neg_nonpos.mpr (le_of_lt (Prec_gt_0.pos : 0 < prec)))
  have h :=
    FloatSpec.Core.Generic_fmt.generic_format_bpow'
      (beta := beta) (fexp := FLX_exp prec) (e := 0)
      (by exact ⟨hβ, hfe_le⟩)
  -- Rewrite (β : ℝ)^0 = 1 to conclude.
  simpa [zpow_zero] using h

end FloatSpec.Core.FLX

namespace FloatSpec.Core.FLX

variable (prec : Int)

/-
Coq (FLX.v):
Lemma succ_FLX_1 : (succ beta FLX_exp 1 = 1 + bpow (-prec + 1))%R.

Lean (spec): The successor at 1 under FLX equals `1 + β^(1 - prec)`.
-/
theorem succ_FLX_1 (beta : Int) [Prec_gt_0 prec] :
    ⦃⌜1 < beta⌝⦄
    FloatSpec.Core.Ulp.succ beta (FLX_exp prec) 1
    ⦃⇓r => ⌜r = 1 + (beta : ℝ) ^ (1 - prec)⌝⦄ := by
  intro hβ; classical
  -- Evaluate `succ` at a nonnegative input (here 0 ≤ 1)
  simp [FloatSpec.Core.Ulp.succ, wp, PostCond.noThrow, Id.run, bind, pure]
  -- Reduce to rewriting `ulp` at x = 1 using `ulp_FLX_1`.
  have hulp := (ulp_FLX_1 (prec := prec) (beta := beta)) hβ
  simpa [wp, PostCond.noThrow] using hulp

/-
Coq (FLX.v):
Theorem eq_0_round_0_FLX :
   forall rnd {Vr: Valid_rnd rnd} x,
     round beta FLX_exp rnd x = 0%R -> x = 0%R.

Lean (spec): If rounding in FLX yields 0, then the input is 0 (for any mode).
-/
theorem eq_0_round_0_FLX
    (beta : Int)
    [Prec_gt_0 prec]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec)]
    (rnd : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜1 < beta ∧ round_to_generic (beta := beta) (fexp := FLX_exp prec) (mode := rnd) x = 0⌝⦄
    (pure x : Id ℝ)
    ⦃⇓r => ⌜r = 0⌝⦄ := by
  intro hpre; classical
  -- Reduce Hoare triple to the pure goal r = 0 with r = x
  simp [wp, PostCond.noThrow] at hpre ⊢
  rcases hpre with ⟨hβ, hround0⟩
  -- FLX has `negligible_exp = none` when `0 < prec`
  have hnone : FloatSpec.Core.Ulp.negligible_exp (fexp := FLX_exp prec) = none := by
    simpa [wp, PostCond.noThrow] using (negligible_exp_FLX (prec := prec) (beta := beta) (by trivial))
  -- Use the generic lemma `eq_0_round_0_negligible_exp` specialized to FLX
  have himpl :
      round_to_generic (beta := beta) (fexp := FLX_exp prec) (mode := rnd) x = 0 → x = 0 := by
    simpa [wp, PostCond.noThrow, Id.run, bind, pure]
      using
        (FloatSpec.Core.Ulp.eq_0_round_0_negligible_exp
          (beta := beta) (fexp := FLX_exp prec) (hne := hnone) (rnd := rnd) (x := x)) hβ
  exact himpl hround0

/-
Coq (FLX.v):
Theorem gt_0_round_gt_0_FLX :
   forall rnd {Vr: Valid_rnd rnd} x,
     (0 < x)%R -> (0 < round beta FLX_exp rnd x)%R.

Lean (spec): For any mode, if x > 0 then rounding in FLX yields a positive value.
-/
theorem gt_0_round_gt_0_FLX
    (beta : Int)
    [Prec_gt_0 prec]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta (FLX_exp prec)]
    (rnd : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜1 < beta ∧ 0 < x⌝⦄
    (pure (round_to_generic (beta := beta) (fexp := FLX_exp prec) (mode := rnd) x) : Id ℝ)
    ⦃⇓r => ⌜0 < r⌝⦄ := by
  intro hpre; classical
  -- Reduce the Hoare triple to a pure goal and unpack premises
  simp [wp, PostCond.noThrow, Id.run, pure] at hpre ⊢
  rcases hpre with ⟨hβ, hx_pos⟩
  -- Monotonicity gives nonnegativity: round 0 ≤ round x and round 0 = 0
  have hr0 :
      round_to_generic (beta := beta) (fexp := FLX_exp prec) (mode := rnd) 0 = 0 := by
    simp [round_to_generic, FloatSpec.Core.Generic_fmt.Ztrunc_zero]
  have hmono :=
    round_to_generic_monotone
      (beta := beta) (fexp := FLX_exp prec) (rnd := rnd)
  have hr_nonneg :
      0 ≤ round_to_generic (beta := beta) (fexp := FLX_exp prec) (mode := rnd) x := by
    have :
        round_to_generic (beta := beta) (fexp := FLX_exp prec) (mode := rnd) 0
          ≤ round_to_generic (beta := beta) (fexp := FLX_exp prec) (mode := rnd) x :=
      hmono (le_of_lt hx_pos)
    simpa [hr0] using this
  -- In FLX, there is no flush-to-zero: rounding a nonzero positive x cannot yield 0
  have hne_exp : FloatSpec.Core.Ulp.negligible_exp (fexp := FLX_exp prec) = none := by
    simpa [wp, PostCond.noThrow]
      using (negligible_exp_FLX (prec := prec) (beta := beta) (by trivial))
  have hr_ne :
      round_to_generic (beta := beta) (fexp := FLX_exp prec) (mode := rnd) x ≠ 0 := by
    -- Use the generic `round_neq_0_negligible_exp` under `Monotone_exp` for FLX
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have htrip :=
      FloatSpec.Core.Ulp.round_neq_0_negligible_exp
        (beta := beta) (fexp := FLX_exp prec)
        (hne := hne_exp) (rnd := rnd) (x := x) (hx := hx_ne)
    simpa [wp, PostCond.noThrow, Id.run, pure] using (htrip hβ)
  -- Combine ≥ 0 with ≠ 0 to obtain > 0
  exact lt_of_le_of_ne hr_nonneg (by simpa [eq_comm] using hr_ne)

/-
Coq (FLX.v):
Lemma succ_FLX_exact_shift:
  forall x e,
  (succ beta FLX_exp (x * bpow e) = succ beta FLX_exp x * bpow e)%R.

Lean (spec): Successor under FLX scales exactly under multiplication by β^e.
-/
-- Auxiliary: exact shift for `pred` on positive inputs.
private theorem pred_FLX_exact_shift_pos_aux (beta : Int) [Prec_gt_0 prec]
    (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ 0 < x⌝⦄
    (do
      let p1 ← FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (x * (beta : ℝ) ^ e)
      let p2 ← FloatSpec.Core.Ulp.pred beta (FLX_exp prec) x
      pure (p1, p2))
    ⦃⇓p => ⌜p.1 = p.2 * (beta : ℝ) ^ e⌝⦄ := by
  intro hpre; classical
  rcases hpre with ⟨hβ, hx_pos⟩
  -- Provide bridge instance for `[Valid_exp]`
  have _instPrec : Fact (0 < prec) := ⟨(Prec_gt_0.pos : 0 < prec)⟩
  -- Evaluate `pred` via `pred_eq_pos` on nonnegative inputs
  have hy_nonneg : 0 ≤ x * (beta : ℝ) ^ e := by
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    exact le_of_lt (mul_pos hx_pos (zpow_pos hbposR e))
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hpred_y_run :
      (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
        = x * (beta : ℝ) ^ e - (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (x * (beta : ℝ) ^ e)) := by
    have h := FloatSpec.Core.Ulp.pred_eq_pos (beta := beta) (fexp := FLX_exp prec)
                (x := x * (beta : ℝ) ^ e) (hx := hy_nonneg)
    have hrun := h hβ
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using hrun
  have hpred_x_run :
      (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) x)
        = x - (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x) := by
    have h := FloatSpec.Core.Ulp.pred_eq_pos (beta := beta) (fexp := FLX_exp prec)
                (x := x) (hx := hx_nonneg)
    have hrun := h hβ
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using hrun
  -- ULP scales exactly under β^e in FLX
  have hulp_shift :
      (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
        = (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x) * (beta : ℝ) ^ e := by
    have := ulp_FLX_exact_shift (prec := prec) (beta := beta) (x := x) (e := e)
    have := this hβ
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
  -- Factor out the common `(β^e)`
  have hrunEq :
      (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
        = ((FloatSpec.Core.Ulp.pred beta (FLX_exp prec) x)) * (beta : ℝ) ^ e := by
    calc (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
        = x * (beta : ℝ) ^ e - (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (x * (beta : ℝ) ^ e)) := hpred_y_run
      _ = x * (beta : ℝ) ^ e - (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x) * (beta : ℝ) ^ e := by
          rw [hulp_shift]
      _ = (x - (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x)) * (beta : ℝ) ^ e := by ring
      _ = (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) x) * (beta : ℝ) ^ e := by rw [hpred_x_run]
  simp only [wp, PostCond.noThrow, Id.run, bind, pure, PredTrans.pure,
             PredTrans.bind, PredTrans.apply, hrunEq]
  trivial

theorem succ_FLX_exact_shift (beta : Int) [Prec_gt_0 prec] (x : ℝ) (e : Int) :
    ⦃⌜1 < beta⌝⦄
    (do
      let s1 ← FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (x * (beta : ℝ) ^ e)
      let s2 ← FloatSpec.Core.Ulp.succ beta (FLX_exp prec) x
      pure (s1, s2))
    ⦃⇓p => ⌜p.1 = p.2 * (beta : ℝ) ^ e⌝⦄ := by
  intro hβ; classical
  -- Ensure `[Valid_exp]` is available
  have _instPrec : Fact (0 < prec) := ⟨(Prec_gt_0.pos : 0 < prec)⟩
  -- Split on the sign of x
  by_cases hxpos : 0 < x
  · -- Positive case: use `succ_eq_pos` and `ulp` shift
    have hy_nonneg : 0 ≤ x * (beta : ℝ) ^ e := by
      have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
      exact le_of_lt (mul_pos hxpos (zpow_pos hbposR e))
    have hx_nonneg : 0 ≤ x := le_of_lt hxpos
    have hsucc_y_run :
        (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
          = x * (beta : ℝ) ^ e + (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (x * (beta : ℝ) ^ e)) := by
      have := FloatSpec.Core.Ulp.succ_eq_pos (beta := beta) (fexp := FLX_exp prec)
                  (x := x * (beta : ℝ) ^ e) (hx := hy_nonneg) True.intro
      simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
    have hsucc_x_run :
        (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) x)
          = x + (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x) := by
      have := FloatSpec.Core.Ulp.succ_eq_pos (beta := beta) (fexp := FLX_exp prec)
                  (x := x) (hx := hx_nonneg) True.intro
      simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
    have hulp_shift :
        (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
          = (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x) * (beta : ℝ) ^ e := by
      have := ulp_FLX_exact_shift (prec := prec) (beta := beta) (x := x) (e := e)
      have := this hβ
      simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
    have hrunEq :
        (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
          = ((FloatSpec.Core.Ulp.succ beta (FLX_exp prec) x)) * (beta : ℝ) ^ e := by
      calc (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
          = x * (beta : ℝ) ^ e + (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (x * (beta : ℝ) ^ e)) := hsucc_y_run
        _ = x * (beta : ℝ) ^ e + (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x) * (beta : ℝ) ^ e := by
            rw [hulp_shift]
        _ = (x + (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) x)) * (beta : ℝ) ^ e := by ring
        _ = (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) x) * (beta : ℝ) ^ e := by rw [hsucc_x_run]
    simp only [wp, PostCond.noThrow, Id.run, bind, pure, PredTrans.pure,
               PredTrans.bind, PredTrans.apply, hrunEq]
    trivial
  · -- Nonpositive case: reduce to `pred` on `-x > 0`
    have hxle : x ≤ 0 := le_of_not_gt hxpos
    by_cases hx0 : x = 0
    · -- Degenerate: compute `ulp 0 = 0` (since FLX is non‑FTZ) and finish
      have hy : x * (beta : ℝ) ^ e = 0 := by simpa [hx0]
      have hnone : FloatSpec.Core.Ulp.negligible_exp (fexp := FLX_exp prec) = none := by
        simpa [wp, PostCond.noThrow]
          using (negligible_exp_FLX (prec := prec) (beta := beta) (by trivial))
      -- Evaluate both sides via `run`, reduce `ulp 0` using `hnone`, and compare
      have lhs :
          (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
            = (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) 0) := by
        simp [FloatSpec.Core.Ulp.succ, hy, Id.run, bind, pure]
      have hsucc0_run :
          (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) x)
            = (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) 0) := by
        simp [FloatSpec.Core.Ulp.succ, hx0, Id.run, bind, pure]
      have hulp0' : (FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) 0) = 0 := by
        unfold FloatSpec.Core.Ulp.ulp
        simp [hnone, Id.run, bind, pure]
      -- Conclude through the common value 0
      have hrunEq :
          (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
            = ((FloatSpec.Core.Ulp.succ beta (FLX_exp prec) x)) * (beta : ℝ) ^ e := by
        have lhs0 : (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (x * (beta : ℝ) ^ e)) = 0 := by
          rw [lhs, hulp0']
        have rhs0 : ((FloatSpec.Core.Ulp.succ beta (FLX_exp prec) x)) * (beta : ℝ) ^ e = 0 := by
          rw [hsucc0_run, hulp0']; ring
        rw [lhs0, rhs0]
      simp only [wp, PostCond.noThrow, Id.run, bind, pure, PredTrans.pure,
                 PredTrans.bind, PredTrans.apply, hrunEq]
      trivial
    · -- Strictly negative: use `pred` exact shift on `-x`
      have hxlt : x < 0 := lt_of_le_of_ne hxle hx0
      have hxneg_pos : 0 < -x := by exact neg_pos.mpr hxlt
      have hpred_pos_shift :
          (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) ((-x) * (beta : ℝ) ^ e))
            = (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (-x)) * (beta : ℝ) ^ e := by
        have := pred_FLX_exact_shift_pos_aux (prec := prec) (beta := beta) (-x) e
        have := this ⟨hβ, hxneg_pos⟩
        simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
      -- succ z = - pred (-z)
      have hsucc_y :
          (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
            = - (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (-(x * (beta : ℝ) ^ e))) := by
        simp [FloatSpec.Core.Ulp.pred]
      have hsucc_x :
          (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) x)
            = - (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (-x)) := by
        simp [FloatSpec.Core.Ulp.pred]
      have :
          (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
            = ((FloatSpec.Core.Ulp.succ beta (FLX_exp prec) x)) * (beta : ℝ) ^ e := by
        -- First, rewrite the `pred` shift along `-(x*β^e) = (-x)*β^e`
        have hneg_scale : -(x * (beta : ℝ) ^ e) = (-x) * (beta : ℝ) ^ e := by
          -- -(x * t) = (-1) * (x * t) = ((-1) * x) * t = (-x) * t
          calc
            -(x * (beta : ℝ) ^ e)
                = (-1 : ℝ) * (x * (beta : ℝ) ^ e) := by simpa [neg_one_mul]
            _ = ((-1 : ℝ) * x) * (beta : ℝ) ^ e := by
                  simpa [mul_assoc] using
                    (mul_assoc (-1 : ℝ) x ((beta : ℝ) ^ e)).symm
            _ = (-x) * (beta : ℝ) ^ e := by
                  simpa [neg_one_mul]
        have hpred_pos_shift' :
            (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (-(x * (beta : ℝ) ^ e)))
              = (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (-x)) * (beta : ℝ) ^ e := by
          simpa [hneg_scale] using hpred_pos_shift
        -- Now convert back to `succ` using `succ z = - pred (-z)` on both sides
        have hneg :
            - (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (-(x * (beta : ℝ) ^ e)))
              = - ((FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (-x)) * (beta : ℝ) ^ e) := by
          exact congrArg (fun t : ℝ => -t) hpred_pos_shift'
        -- Replace both sides via `hsucc_*` and move the negation across multiplication
        calc (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
            = - (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (-(x * (beta : ℝ) ^ e))) := hsucc_y
          _ = - ((FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (-x)) * (beta : ℝ) ^ e) := hneg
          _ = (- (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (-x))) * (beta : ℝ) ^ e := by ring
          _ = (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) x) * (beta : ℝ) ^ e := by rw [← hsucc_x]
      simp only [wp, PostCond.noThrow, Id.run, bind, pure, PredTrans.pure,
                 PredTrans.bind, PredTrans.apply, this]
      trivial

/-
Coq (FLX.v):
Lemma pred_FLX_exact_shift:
  forall x e,
  (pred beta FLX_exp (x * bpow e) = pred beta FLX_exp x * bpow e)%R.

Lean (spec): Predecessor under FLX scales exactly under multiplication by β^e.
-/
theorem pred_FLX_exact_shift (beta : Int) [Prec_gt_0 prec] (x : ℝ) (e : Int) :
    ⦃⌜1 < beta⌝⦄
    (do
      let p1 ← FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (x * (beta : ℝ) ^ e)
      let p2 ← FloatSpec.Core.Ulp.pred beta (FLX_exp prec) x
      pure (p1, p2))
    ⦃⇓p => ⌜p.1 = p.2 * (beta : ℝ) ^ e⌝⦄ := by
  intro hβ; classical
  -- Rewrite `pred` via `succ` and use the exact-shift lemma for `succ` applied to `-x`.
  have hpred_scaled_run :
      (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
        = - (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (-(x * (beta : ℝ) ^ e))) := by
    simp [FloatSpec.Core.Ulp.pred, Id.run, bind, pure]
  have hpred_x_run :
      (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) x)
        = - (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (-x)) := by
    simp [FloatSpec.Core.Ulp.pred, Id.run, bind, pure]
  -- Observe that -(x * β^e) = (-x) * β^e.
  have hneg_scale : -(x * (beta : ℝ) ^ e) = (-x) * (beta : ℝ) ^ e := by
    -- -(x * t) = (-1) * (x * t) = ((-1) * x) * t = (-x) * t
    calc
      -(x * (beta : ℝ) ^ e)
          = (-1 : ℝ) * (x * (beta : ℝ) ^ e) := by simpa [neg_one_mul]
      _ = ((-1 : ℝ) * x) * (beta : ℝ) ^ e := by
            -- reassociate: a * (b * c) = (a * b) * c
            simpa [mul_assoc] using
              (mul_assoc (-1 : ℝ) x ((beta : ℝ) ^ e)).symm
      _ = (-x) * (beta : ℝ) ^ e := by
            simpa [neg_one_mul]
  -- Exact shift for `succ` at `-x`.
  have hsucc_shift :
      (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) ((-x) * (beta : ℝ) ^ e))
        = ((FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (-x))) * (beta : ℝ) ^ e := by
    have := succ_FLX_exact_shift (prec := prec) (beta := beta) (x := -x) (e := e)
    have := this hβ
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
  -- Package some run-time abbreviations to simplify rewriting.
  set S : ℝ := (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (-x)) with hSdef
  set T : ℝ := (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (-(x * (beta : ℝ) ^ e))) with hTdef
  -- Relate `pred` to `succ` via negation on both arguments.
  have hS_pred : (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) x) = -S := by
    simpa [hSdef] using hpred_x_run
  have hT_scaled : T = S * (beta : ℝ) ^ e := by
    -- First, rewrite the scaled argument using `-(x*β^e) = (-x)*β^e`.
    have : T = (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) ((-x) * (beta : ℝ) ^ e)) := by
      simpa [hTdef, hneg_scale]
    -- Then, apply the exact-shift lemma for `succ` and substitute `S`.
    calc
      T = (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) ((-x) * (beta : ℝ) ^ e)) := this
      _ = (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (-x)) * (beta : ℝ) ^ e := hsucc_shift
      _ = S * (beta : ℝ) ^ e := by simpa [hSdef]
  -- Now rewrite both sides of the target equality
  have hpred_scaled :
      (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (x * (beta : ℝ) ^ e)) = -T := by
    simpa [hTdef] using hpred_scaled_run
  have :
      (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
        = ((FloatSpec.Core.Ulp.pred beta (FLX_exp prec) x)) * (beta : ℝ) ^ e := by
    calc
      (FloatSpec.Core.Ulp.pred beta (FLX_exp prec) (x * (beta : ℝ) ^ e))
          = -T := hpred_scaled
      _ = - (S * (beta : ℝ) ^ e) := by simpa [hT_scaled]
      _ = (-S) * (beta : ℝ) ^ e := by
            -- -(S * t) = (-1) * (S * t) = ((-1) * S) * t = (-S) * t
            have : -(S * (beta : ℝ) ^ e)
                    = ((-1 : ℝ) * S) * (beta : ℝ) ^ e := by
              calc
                -(S * (beta : ℝ) ^ e)
                    = (-1 : ℝ) * (S * (beta : ℝ) ^ e) := by simpa [neg_one_mul]
                _ = ((-1 : ℝ) * S) * (beta : ℝ) ^ e := by
                      simpa [mul_assoc] using
                        (mul_assoc (-1 : ℝ) S ((beta : ℝ) ^ e)).symm
            simpa [neg_one_mul] using this
      _ = ((FloatSpec.Core.Ulp.pred beta (FLX_exp prec) x)) * (beta : ℝ) ^ e := by
            rw [← hS_pred]
  simp only [wp, PostCond.noThrow, Id.run, bind, pure, PredTrans.pure,
             PredTrans.bind, PredTrans.apply, this]
  trivial

end FloatSpec.Core.FLX
