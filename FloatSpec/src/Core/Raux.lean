import FloatSpec.Linter
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

import FloatSpec.src.Core.Zaux
import FloatSpecRoles  -- Register {coq} doc role
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Real.Sqrt
-- import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- import Mathlib.Data.Nat.Find
-- import Mathlib.Tactic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do

namespace FloatSpec.Core.Raux

section Rmissing

/-- Subtraction ordering principle

    If x ≤ y, then the difference y - x is non-negative.
    This is a fundamental property used throughout real analysis.
-/
def Rle_0_minus (x y : ℝ) : ℝ :=
  y - x

/-- Specification: Subtraction ordering principle

    The operation ensures that if x ≤ y, then y - x ≥ 0.
    This captures the relationship between ordering and subtraction.
-/
@[spec]
theorem Rle_0_minus_spec (x y : ℝ) (hxy : x ≤ y) :
    ⦃⌜True⌝⦄
    (pure (Rle_0_minus x y) : Id _)
    ⦃⇓result => ⌜0 ≤ result⌝⦄ := by
  intro _
  unfold Rle_0_minus
  exact sub_nonneg_of_le hxy

-- (moved/alternative specs for exponential monotonicity exist below)

/-- Absolute values equal implies values are equal up to sign

    If |x| = |y|, then either x = y or x = -y.
    This captures the two possible cases for equal magnitudes.
-/
def Rabs_eq_Rabs_case (x y : ℝ) : (ℝ × ℝ) :=
  (x, y)

/-- Specification: Equal absolute values give equality up to sign

    Under the precondition |x| = |y|, the pair (x, y) satisfies
    x = y or x = -y.
-/
@[spec]
theorem Rabs_eq_Rabs_spec (x y : ℝ) (hxy : |x| = |y|) :
    ⦃⌜True⌝⦄
    (pure (Rabs_eq_Rabs_case x y) : Id _)
    ⦃⇓p => ⌜p.1 = p.2 ∨ p.1 = -p.2⌝⦄ := by
  intro _
  unfold Rabs_eq_Rabs_case
  -- Use the standard equivalence |x| = |y| ↔ x = y ∨ x = -y
  simpa using (abs_eq_abs.mp hxy)

/-- Absolute value of difference bounded under simple conditions

    If {lean}`0 ≤ y` and {lean}`y ≤ 2 * x`, then {lean}`|x - y| ≤ x`.
-/
def Rabs_minus_le_val (x y : ℝ) : ℝ :=
  (abs (x - y))

/-- Specification: Bound on {lean}`|x - y|`

    Under {lean}`0 ≤ y` and {lean}`y ≤ 2 * x`, the value {lean}`|x - y|` is bounded by {lean}`x`.
-/
@[spec]
theorem Rabs_minus_le_spec (x y : ℝ) (h : 0 ≤ y ∧ y ≤ 2 * x) :
    ⦃⌜True⌝⦄
    (pure (Rabs_minus_le_val x y) : Id _)
    ⦃⇓r => ⌜r ≤ x⌝⦄ := by
  intro _
  unfold Rabs_minus_le_val
  -- We prove |x - y| ≤ x by showing -x ≤ x - y ≤ x
  -- Upper bound: from 0 ≤ y, we get x - y ≤ x
  have h0y : 0 ≤ y := h.left
  have hx_upper : x - y ≤ x := by
    -- x - y ≤ x ↔ x ≤ x + y, which holds since 0 ≤ y
    have : x ≤ x + y := by exact le_add_of_nonneg_right h0y
    exact (sub_le_iff_le_add).2 this
  -- Lower bound: from y ≤ 2*x, we get -x ≤ x - y
  have hy2x : y ≤ 2 * x := h.right
  have hx_lower : -x ≤ x - y := by
    -- This is equivalent to 0 ≤ (x - y) - (-x) = 2*x - y
    have : 0 ≤ 2 * x - y := sub_nonneg.mpr hy2x
    -- rewrite 2*x - y as (x - y) - (-x)
    have : 0 ≤ (x - y) - (-x) := by
      simpa [sub_eq_add_neg, two_mul, add_comm, add_left_comm, add_assoc] using this
    exact (sub_nonneg.mp this)
  -- Combine bounds via abs_le
  exact (abs_le.mpr ⟨hx_lower, hx_upper⟩)

/-- Lower bound characterization via absolute value

    If y ≤ -x or x ≤ y, then x ≤ |y|.
-/
def Rabs_ge_case (x y : ℝ) : (ℝ × ℝ) :=
  (x, y)

@[spec]
theorem Rabs_ge_spec (x y : ℝ) (h : y ≤ -x ∨ x ≤ y) :
    ⦃⌜True⌝⦄
    (pure (Rabs_ge_case x y) : Id _)
    ⦃⇓p => ⌜p.1 ≤ |p.2|⌝⦄ := by
  intro _
  unfold Rabs_ge_case
  rcases h with h1 | h2
  · -- Case y ≤ -x ⇒ x ≤ |y|
    have hxle : x ≤ -y := by
      have := neg_le_neg h1
      simpa using this
    have h_abs : -y ≤ |y| := by
      simpa using (neg_le_abs y)
    exact hxle.trans h_abs
  · -- Case x ≤ y ⇒ x ≤ |y|
    exact h2.trans (le_abs_self y)

/-- Inverse characterization: x ≤ |y| implies y ≤ -x or x ≤ y. -/
def Rabs_ge_inv_case (x y : ℝ) : (ℝ × ℝ) :=
  (x, y)

@[spec]
theorem Rabs_ge_inv_spec (x y : ℝ) (hx : x ≤ |y|) :
    ⦃⌜True⌝⦄
    (pure (Rabs_ge_inv_case x y) : Id _)
    ⦃⇓p => ⌜p.2 ≤ -p.1 ∨ p.1 ≤ p.2⌝⦄ := by
  intro _
  unfold Rabs_ge_inv_case
  by_cases hy : 0 ≤ y
  · -- If y ≥ 0, then |y| = y and the goal reduces to x ≤ y
    have habs : |y| = y := abs_of_nonneg hy
    have hx' : x ≤ y := by simpa [habs] using hx
    exact Or.inr hx'
  · -- If y ≤ 0, then |y| = -y and from x ≤ -y we get y ≤ -x
    have hy' : y ≤ 0 := le_of_not_ge hy
    have habs : |y| = -y := abs_of_nonpos hy'
    have hx' : x ≤ -y := by simpa [habs] using hx
    have : y ≤ -x := by
      have := neg_le_neg hx'
      simpa using this
    exact Or.inl this

/-- From |x| ≤ y, derive the two-sided bound -y ≤ x ≤ y. -/
def Rabs_le_inv_pair (x y : ℝ) : (ℝ × ℝ) :=
  (x, y)

@[spec]
theorem Rabs_le_inv_spec (x y : ℝ) (h : |x| ≤ y) :
    ⦃⌜True⌝⦄
    (pure (Rabs_le_inv_pair x y) : Id _)
    ⦃⇓p => ⌜-p.2 ≤ p.1 ∧ p.1 ≤ p.2⌝⦄ := by
  intro _
  unfold Rabs_le_inv_pair
  exact (abs_le.mp h)

/-- Multiplication preserves strict inequalities

    For non-negative values, strict inequalities are preserved
    under multiplication. This is essential for scaling arguments
    in floating-point proofs.
-/
def Rmult_lt_compat (r1 r2 r3 r4 : ℝ) : (ℝ × ℝ) :=
  (r1 * r3, r2 * r4)

/-- Specification: Multiplication preserves strict inequalities

    If {lean}`0 ≤ r1`, {lean}`0 ≤ r3`, {lean}`r1 < r2`, and {lean}`r3 < r4`,
    then {lean}`r1 * r3 < r2 * r4`.
    This property is crucial for analyzing products of bounds.
-/
@[spec]
theorem Rmult_lt_compat_spec (r1 r2 r3 r4 : ℝ)
    (h : 0 ≤ r1 ∧ 0 ≤ r3 ∧ r1 < r2 ∧ r3 < r4) :
    ⦃⌜True⌝⦄
    (pure (Rmult_lt_compat r1 r2 r3 r4) : Id _)
    ⦃⇓result => ⌜result.1 < result.2⌝⦄ := by
  intro _
  unfold Rmult_lt_compat
  have ⟨h1, h3, h12, h34⟩ := h
  by_cases hr3 : r3 = 0
  · subst hr3
    simp
    exact mul_pos (h1.trans_lt h12) h34
  · have h3_pos : 0 < r3 := lt_of_le_of_ne h3 (Ne.symm hr3)
    exact mul_lt_mul h12 (le_of_lt h34) h3_pos (le_of_lt (h1.trans_lt h12))

/-- Right multiplication cancellation for inequality

    If products are unequal and the right factor is the same,
    then the left factors must be unequal.
-/
def Rmult_neq_reg_r (_r1 r2 r3 : ℝ) : (ℝ × ℝ) :=
  (r2, r3)

/-- Specification: Right multiplication cancellation

    If {lean}`r2 * r1 ≠ r3 * r1`, then {lean}`r2 ≠ r3`.
    This allows cancellation in multiplication inequalities.
-/
@[spec]
theorem Rmult_neq_reg_r_spec (r1 r2 r3 : ℝ) (h : r2 * r1 ≠ r3 * r1) :
    ⦃⌜True⌝⦄
    (pure (Rmult_neq_reg_r r1 r2 r3) : Id _)
    ⦃⇓result => ⌜result.1 ≠ result.2⌝⦄ := by
  intro _
  unfold Rmult_neq_reg_r
  -- Reduce to showing r2 ≠ r3 from the hypothesis on products
  -- If r2 = r3 then r2 * r1 = r3 * r1, contradicting h
  simpa using
    (fun h_eq : r2 = r3 => by
      apply h
      simpa [h_eq])

/-- Multiplication preserves non-equality

    Multiplying unequal numbers by a non-zero value
    preserves the inequality.
-/
def Rmult_neq_compat_r (r1 r2 r3 : ℝ) : (ℝ × ℝ) :=
  (r2 * r1, r3 * r1)

/-- Specification: Multiplication preserves non-equality

    If {lean}`r1 ≠ 0` and {lean}`r2 ≠ r3`,
    then {lean}`r2 * r1 ≠ r3 * r1`.
-/
@[spec]
theorem Rmult_neq_compat_r_spec (r1 r2 r3 : ℝ) (h : r1 ≠ 0 ∧ r2 ≠ r3) :
    ⦃⌜True⌝⦄
    (pure (Rmult_neq_compat_r r1 r2 r3) : Id _)
    ⦃⇓result => ⌜result.1 ≠ result.2⌝⦄ := by
  intro _
  unfold Rmult_neq_compat_r
  simp
  have ⟨h1_ne, h23_ne⟩ := h
  exact ⟨h23_ne, h1_ne⟩

/-- Right distributivity of minimum over multiplication

    For non-negative multipliers, minimum distributes over
    multiplication from the right.
-/
def Rmult_min_distr_r (x y z : ℝ) : (ℝ × ℝ) :=
  (min (x * z) (y * z), min x y * z)

/-- Specification: Right distributivity of minimum

    If {lean}`0 ≤ z`, then {lean}`min (x * z) (y * z) = min x y * z`.
-/
@[spec]
theorem Rmult_min_distr_r_spec (x y z : ℝ) (h : 0 ≤ z) :
    ⦃⌜True⌝⦄
    (pure (Rmult_min_distr_r x y z) : Id _)
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  intro _
  unfold Rmult_min_distr_r
  -- We need to prove: min (x * z) (y * z) = min x y * z
  rw [min_mul_of_nonneg _ _ h]
  rfl

/-- Left distributivity of minimum over multiplication

    For non-negative multipliers, minimum distributes over
    multiplication from the left.
-/
def Rmult_min_distr_l (x y z : ℝ) : (ℝ × ℝ) :=
  (min (x * y) (x * z), x * min y z)

/-- Specification: Left distributivity of minimum

    If {lean}`0 ≤ x`, then {lean}`min (x * y) (x * z) = x * min y z`.
-/
@[spec]
theorem Rmult_min_distr_l_spec (x y z : ℝ) (h : 0 ≤ x) :
    ⦃⌜True⌝⦄
    (pure (Rmult_min_distr_l x y z) : Id _)
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  intro _
  unfold Rmult_min_distr_l
  -- We need to prove: min (x * y) (x * z) = x * min y z
  rw [mul_min_of_nonneg _ _ h]
  rfl

/-- Minimum of opposites equals negative maximum

    Taking the minimum of negated values is equivalent
    to negating the maximum of the original values.
-/
def Rmin_opp (x y : ℝ) : (ℝ × ℝ) :=
  (min (-x) (-y), -(max x y))

/-- Specification: Minimum of opposites

    min (-x) (-y) = -(max x y).
    This duality between min and max under negation is fundamental.
-/
@[spec]
theorem Rmin_opp_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rmin_opp x y) : Id _)
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  -- Precondition is trivial; name it to avoid parser confusion
  intro hTrue
  unfold Rmin_opp
  -- We need to prove: min (-x) (-y) = -(max x y)
  exact min_neg_neg x y

/-- Maximum of opposites equals negative minimum

    Taking the maximum of negated values is equivalent
    to negating the minimum of the original values.
-/
def Rmax_opp (x y : ℝ) : (ℝ × ℝ) :=
  (max (-x) (-y), -(min x y))

/-- Specification: Maximum of opposites

    max (-x) (-y) = -(min x y).
    This completes the duality between min/max under negation.
-/
@[spec]
theorem Rmax_opp_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rmax_opp x y) : Id _)
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  intro htriv
  unfold Rmax_opp
  -- We need to prove: max (-x) (-y) = -(min x y)
  exact max_neg_neg x y

/-- Monotonicity of the exponential function

    If x ≤ y, then exp x ≤ exp y. This captures the
    strict monotonicity of the real exponential function.
-/
noncomputable def exp_le_check (x _y : ℝ) : ℝ :=
  (Real.exp x)

/-- Specification: Exponential is monotone increasing

    Given x ≤ y, the value exp x is bounded above by exp y.
-/
@[spec]
theorem exp_le_spec (x y : ℝ) (hxy : x ≤ y) :
    ⦃⌜True⌝⦄
    (pure (exp_le_check x y) : Id _)
    ⦃⇓ex => ⌜ex ≤ Real.exp y⌝⦄ := by
  intro _
  unfold exp_le_check
  -- Using monotonicity of exp: exp x ≤ exp y ↔ x ≤ y
  exact (Iff.mpr Real.exp_le_exp hxy)

/-- Coq name compatibility: {lean}`exp_le` -/
theorem exp_le (x y : ℝ) (hxy : x ≤ y) :
    ⦃⌜True⌝⦄
    (pure (exp_le_check x y) : Id _)
    ⦃⇓ex => ⌜ex ≤ Real.exp y⌝⦄ :=
  exp_le_spec x y hxy

end Rmissing

section IZR

/-- Carrier for relating Int order and real order via casting -/
def IZR_le_lt_triple (m n p : Int) : (ℝ × ℝ × ℝ) :=
  ((m : ℝ), (n : ℝ), (p : ℝ))

/-- Coq: {coq}`IZR_le_lt`

    If m ≤ n < p as integers, then (m:ℝ) ≤ (n:ℝ) < (p:ℝ).
-/
@[spec]
theorem IZR_le_lt_spec (m n p : Int) (h : m ≤ n ∧ n < p) :
    ⦃⌜True⌝⦄
    (pure (IZR_le_lt_triple m n p) : Id _)
    ⦃⇓t => ⌜t.1 ≤ t.2.1 ∧ t.2.1 < t.2.2⌝⦄ := by
  intro _
  unfold IZR_le_lt_triple
  rcases h with ⟨hmn, hnp⟩
  exact ⟨(Int.cast_mono hmn), (Int.cast_strictMono hnp)⟩

/-- Carrier for the converse relation from reals back to Ints -/
def le_lt_IZR_triple (m n p : Int) : (Int × Int × Int) :=
  (m, n, p)

/-- If the real casts satisfy m <= n and n < p, then m <= n < p as integers (Coq: le_lt_IZR). -/
@[spec]
theorem le_lt_IZR_spec (m n p : Int) (h : (m : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (p : ℝ)) :
    ⦃⌜True⌝⦄
    (pure (le_lt_IZR_triple m n p) : Id _)
    ⦃⇓t => ⌜t.1 ≤ t.2.1 ∧ t.2.1 < t.2.2⌝⦄ := by
  intro _
  unfold le_lt_IZR_triple
  rcases h with ⟨hmnR, hnpR⟩
  -- Use order-reflecting casts: (m:ℝ) ≤ (n:ℝ) ↔ m ≤ n, and (n:ℝ) < (p:ℝ) ↔ n < p
  exact ⟨(Int.cast_le).1 hmnR, (Int.cast_lt).1 hnpR⟩

/-- Carrier for inequality preservation under casting -/
def neq_IZR_pair (m n : Int) : (Int × Int) :=
  (m, n)

/-  If the real casts of m and n are unequal, then m and n are unequal as
    integers. Provide the Coq-named lemma so documentation cross-references like
    {name}`neq_IZR` resolve. This is the same content as `neq_IZR_spec` below. -/
theorem neq_IZR (m n : Int) (hmnR : (m : ℝ) ≠ (n : ℝ)) :
    ⦃⌜True⌝⦄
    (pure (neq_IZR_pair m n) : Id _)
    ⦃⇓p => ⌜p.1 ≠ p.2⌝⦄ := by
  intro _
  unfold neq_IZR_pair
  -- Reduce the Hoare-style triple on Id to a pure proposition
  simp [wp, PostCond.noThrow, Id.run, PredTrans.pure]
  -- Goal is `m ≠ n`; close it by contraposition using cast injectivity
  exact fun hmn => hmnR (by simpa [hmn])

/-- If the real casts of m and n are unequal, then m and n are unequal as integers (Coq: {lean}`neq_IZR`). -/
@[spec]
theorem neq_IZR_spec (m n : Int) (hmnR : (m : ℝ) ≠ (n : ℝ)) :
    ⦃⌜True⌝⦄
    (pure (neq_IZR_pair m n) : Id _)
    ⦃⇓p => ⌜p.1 ≠ p.2⌝⦄ := by
  intro _
  unfold neq_IZR_pair
  -- Reduce the Hoare-style triple on Id to a pure proposition
  simp [wp, PostCond.noThrow, Id.run, PredTrans.pure]
  -- Goal is `m ≠ n`; close it by contraposition using cast injectivity
  exact fun hmn => hmnR (by simpa [hmn])


end IZR

section Rrecip

/-- Reciprocal comparison on positives: if {lean}`0 < x ∧ x < y` then {lean}`1/y < 1/x` -/
noncomputable def Rinv_lt_check (x y : ℝ) : (ℝ × ℝ) :=
  (1 / y, 1 / x)

/-- Specification: Reciprocal reverses order on positive reals -/
@[spec]
theorem Rinv_lt_spec (x y : ℝ) (h : 0 < x ∧ x < y) :
    ⦃⌜True⌝⦄
    (pure (Rinv_lt_check x y) : Id _)
    ⦃⇓p => ⌜p.1 < p.2⌝⦄ := by
  intro _
  -- Standard property: for 0 < x < y, we have 1/y < 1/x
  unfold Rinv_lt_check
  exact one_div_lt_one_div_of_lt h.left h.right

/-- Reciprocal comparison (≤) on positives: if 0 < x ≤ y then 1/y ≤ 1/x -/
noncomputable def Rinv_le_check (x y : ℝ) : (ℝ × ℝ) :=
  (1 / y, 1 / x)

/-- Specification: Reciprocal is antitone on positive reals (≤ version) -/
@[spec]
theorem Rinv_le_spec (x y : ℝ) (h : 0 < x ∧ x ≤ y) :
    ⦃⌜True⌝⦄
    (pure (Rinv_le_check x y) : Id _)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _
  -- Standard property: for 0 < x ≤ y, we have 1/y ≤ 1/x
  unfold Rinv_le_check
  exact one_div_le_one_div_of_le h.left h.right

end Rrecip

section Sqrt

/-- Nonnegativity of square root

    The square root of a non-negative real number is itself non-negative.
    This captures the standard property of the real square root function.
-/
noncomputable def sqrt_ge_0_check (x : ℝ) : ℝ :=
  Real.sqrt x

/-- Specification: sqrt is non-negative on ℝ≥0

    Given 0 ≤ x, the computed value satisfies 0 ≤ sqrt x.
-/
@[spec]
theorem sqrt_ge_0_spec (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (sqrt_ge_0_check x) : Id _)
    ⦃⇓r => ⌜0 ≤ r⌝⦄ := by
  intro _
  unfold sqrt_ge_0_check
  exact Real.sqrt_nonneg x

/-
  Coq (Raux.v):
  Lemma sqrt_neg : forall x, (x <= 0)%R -> (sqrt x = 0)%R.

  Lean (spec): If x ≤ 0 then sqrt x = 0.
-/
/-- Carrier for {coq}`sqrt_neg`: returns {lean}`Real.sqrt x`. -/
noncomputable def sqrt_neg_check (x : ℝ) : ℝ :=
  Real.sqrt x

@[spec]
theorem sqrt_neg_spec (x : ℝ) (hx : x ≤ 0) :
    ⦃⌜True⌝⦄
    (pure (sqrt_neg_check x) : Id _)
    ⦃⇓r => ⌜r = 0⌝⦄ := by
  intro _
  unfold sqrt_neg_check
  exact Real.sqrt_eq_zero_of_nonpos hx

/-- Coq (Raux.v): Theorem sqrt_ge_0
    For all real x, 0 ≤ sqrt x. We provide a wrapper with
    the exact Coq name around {lean}`sqrt_ge_0_check`.

    Lean (spec): No precondition; sqrt is nonnegative. -/
theorem sqrt_ge_0 (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (sqrt_ge_0_check x) : Id _)
    ⦃⇓r => ⌜0 ≤ r⌝⦄ := by
  intro _
  unfold sqrt_ge_0_check
  -- Standard: sqrt is always nonnegative
  exact Real.sqrt_nonneg x

end Sqrt

section Abs

/-- Check for zero absolute value

    Encodes the predicate |x| = 0 as a boolean value for specification.
-/
noncomputable def Rabs_eq_R0_check (x : ℝ) : Bool :=
  (|x| = 0)

/-- Specification: Absolute value equals zero iff the number is zero

    The absolute value of a real number is zero if and only if the number itself is zero.
-/
@[spec]
theorem Rabs_eq_R0_spec (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rabs_eq_R0_check x) : Id _)
    ⦃⇓b => ⌜b ↔ x = 0⌝⦄ := by
  intro _
  unfold Rabs_eq_R0_check
  -- Standard property: |x| = 0 ↔ x = 0
  simpa using (abs_eq_zero : |x| = 0 ↔ x = 0)

end Abs

section Squares

/-
  Coq (Raux.v):
  Lemma Rsqr_le_abs_0_alt :
    forall x y, (x² <= y² -> x <= Rabs y)%R.

  Lean (spec): From x^2 ≤ y^2, deduce x ≤ |y|.
-/
/-- Carrier for {coq}`Rsqr_le_abs_0_alt`: returns the first argument. -/
noncomputable def Rsqr_le_abs_0_alt_val (x _y : ℝ) : ℝ :=
  x

@[spec]
theorem Rsqr_le_abs_0_alt_spec (x y : ℝ) (hxy : x^2 ≤ y^2) :
    ⦃⌜True⌝⦄
    (pure (Rsqr_le_abs_0_alt_val x y) : Id _)
    ⦃⇓r => ⌜r ≤ |y|⌝⦄ := by
  intro _
  -- r = x by definition
  unfold Rsqr_le_abs_0_alt_val
  -- From x^2 ≤ y^2 we get |x| ≤ |y| via `sq_le_sq`.
  have habs : |x| ≤ |y| := (sq_le_sq).mp hxy
  -- And x ≤ |x| holds for all reals; combine both.
  exact (le_trans (le_abs_self x) habs)

end Squares

section AbsMore

/-- Boolean check for strict inequality on absolute value: |x| < y -/
noncomputable def Rabs_lt_check (x y : ℝ) : Bool :=
  (|x| < y)

/-- Specification: |x| < y iff the boolean returns true -/
@[spec]
theorem Rabs_lt_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rabs_lt_check x y) : Id _)
    ⦃⇓b => ⌜b ↔ |x| < y⌝⦄ := by
  intro _
  unfold Rabs_lt_check
  -- Follows from decidability of (<) on ℝ
  simp [wp, PostCond.noThrow, pure, decide_eq_true_iff]

end AbsMore

section AbsGt

/-- Boolean check for strict lower bound on |x|: y < |x| -/
noncomputable def Rabs_gt_check (x y : ℝ) : Bool :=
  (y < |x|)

/-- Specification: y < |x| iff the boolean returns true -/
@[spec]
theorem Rabs_gt_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rabs_gt_check x y) : Id _)
    ⦃⇓b => ⌜b ↔ y < |x|⌝⦄ := by
  intro _
  unfold Rabs_gt_check
  -- Follows from decidability of (<) on ℝ
  simp [wp, PostCond.noThrow, pure, decide_eq_true_iff]

end AbsGt

section AbsGtInv

/-- Pair carrier for the converse direction: from y < x or y < -x to y < |x| -/
def Rabs_gt_inv_pair (x y : ℝ) : (ℝ × ℝ) :=
  (x, y)

/-- Specification: If y < x or y < -x then y < |x|

    This is the converse direction corresponding to {lean}`Rabs_gt_spec`.
-/
@[spec]
theorem Rabs_gt_inv_spec (x y : ℝ) (h : y < x ∨ y < -x) :
    ⦃⌜True⌝⦄
    (pure (Rabs_gt_inv_pair x y) : Id _)
    ⦃⇓p => ⌜p.2 < |p.1|⌝⦄ := by
  intro _
  unfold Rabs_gt_inv_pair
  -- From y < x or y < -x and x ≤ |x|, -x ≤ |x| we get y < |x|
  rcases h with hxy | hxny
  · exact lt_of_lt_of_le hxy (le_abs_self x)
  · exact lt_of_lt_of_le hxny (by simpa using (neg_le_abs x))

end AbsGtInv

section Rcompare

/-- Three-way comparison for real numbers

    Returns -1 if x < y, 0 if x = y, and 1 if x > y.
    This provides a complete ordering comparison in one operation.
-/
noncomputable def Rcompare (x y : ℝ) : Int :=
  (if x < y then -1
        else if x = y then 0
        else 1)

/-- Coq {coq}`Rcompare_prop`: inductive characterization of {lean}`Rcompare` codes. -/
inductive Rcompare_prop (x y : ℝ) : Int → Prop where
  | Rcompare_Lt_ : x < y → Rcompare_prop x y (-1)
  | Rcompare_Eq_ : x = y → Rcompare_prop x y 0
  | Rcompare_Gt_ : y < x → Rcompare_prop x y 1

export Rcompare_prop (Rcompare_Lt_ Rcompare_Eq_ Rcompare_Gt_)

/-- Coq {coq}`Rcompare_prop_ind` (alias of the recursor). -/
abbrev Rcompare_prop_ind := @Rcompare_prop.rec

/-- Coq {coq}`Rcompare_prop_sind` (alias of the recursor). -/
abbrev Rcompare_prop_sind := @Rcompare_prop.rec

/-- Coq-style spec: {coq}`Rcompare_prop` holds for {lean}`Rcompare`. -/
theorem Rcompare_prop_spec (x y : ℝ) : Rcompare_prop x y (Rcompare x y) := by
  by_cases hxy : x < y
  · simpa [Rcompare, hxy] using (Rcompare_Lt_ (x := x) (y := y) hxy)
  · by_cases hxeq : x = y
    · subst hxeq
      simpa [Rcompare, hxy] using (Rcompare_Eq_ (x := x) (y := x) rfl)
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) (Ne.symm hxeq)
      simpa [Rcompare, hxy, hxeq, hyx] using (Rcompare_Gt_ (x := x) (y := y) hyx)

/-- Specification: Three-way comparison correctness

    The comparison function returns:
    - -1 when x < y
    - 0 when x = y
    - 1 when x > y

    This captures the complete ordering of real numbers.
-/
@[spec]
theorem Rcompare_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare x y) : Id _)
    ⦃⇓result => ⌜(result = -1 ↔ x < y) ∧
                (result = 0 ↔ x = y) ∧
                (result = 1 ↔ y < x)⌝⦄ := by
  intro _
  -- Reduce the Hoare triple to the pure comparison statement.
  simp [wp, PostCond.noThrow, Id.run, Rcompare]
  by_cases hxy : x < y
  · have hne : x ≠ y := ne_of_lt hxy
    have hnotyx : ¬ y < x := not_lt_of_ge (le_of_lt hxy)
    simp [hxy, hne, hnotyx]
  · by_cases hxeq : x = y
    · subst hxeq
      simp [hxy]
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) (Ne.symm hxeq)
      have hnotxy : ¬ x < y := hxy
      simp [hxy, hxeq, hyx, hnotxy]

/-- Rcompare is antisymmetric

    Swapping arguments negates the result, reflecting
    the antisymmetry of the ordering relation.
-/
noncomputable def Rcompare_sym (x y : ℝ) : Int :=
  let c := Rcompare y x; -c

/-- Specification: Comparison antisymmetry

    Rcompare x y = -(Rcompare y x).
    This captures the antisymmetric nature of ordering.
-/
@[spec]
theorem Rcompare_sym_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_sym x y) : Id _)
    ⦃⇓result => ⌜result = -(Rcompare y x)⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, Id.run, Rcompare_sym]

/-- Comparison with opposites reverses order

    Comparing negated values reverses the comparison,
    reflecting that negation reverses order.
-/
noncomputable def Rcompare_opp (x y : ℝ) : Int :=
  Rcompare y x

/-- Specification: Opposite comparison

    Rcompare (-x) (-y) = Rcompare y x.
    Negating both arguments reverses the comparison.
-/
@[spec]
theorem Rcompare_opp_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_opp x y) : Id _)
    ⦃⇓result => ⌜result = (Rcompare y x)⌝⦄ := by
  intro _
  unfold Rcompare_opp
  rfl

/-- Comparison is invariant under translation

    Adding the same value to both arguments doesn't
    change the comparison result.
-/
noncomputable def Rcompare_plus_r (x y _z: ℝ) : Int :=
  Rcompare x y

/-- Specification: Translation invariance

    Rcompare (x + z) (y + z) = Rcompare x y.
    Translation preserves ordering relationships.
-/
@[spec]
theorem Rcompare_plus_r_spec (x y z : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_plus_r x y z) : Id _)
    ⦃⇓result => ⌜result = (Rcompare x y)⌝⦄ := by
  intro _
  unfold Rcompare_plus_r
  rfl

/-- Left addition preserves comparison

    Adding a value on the left preserves the comparison.
-/
noncomputable def Rcompare_plus_l (x y _z : ℝ) : Int :=
  Rcompare x y

/-- Specification: Left translation invariance

    Rcompare (z + x) (z + y) = Rcompare x y.
-/
@[spec]
theorem Rcompare_plus_l_spec (x y z : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_plus_l x y z) : Id _)
    ⦃⇓result => ⌜result = (Rcompare x y)⌝⦄ := by
  intro _
  unfold Rcompare_plus_l
  rfl

/-- Comparison is preserved by positive scaling

    Multiplying by a positive value preserves the comparison.
-/
noncomputable def Rcompare_mult_r (x y _z : ℝ) : Int :=
  Rcompare x y

/-- Specification: Positive scaling preserves comparison

    If {lean}`0<z`, then {lean}`Rcompare (x*z) (y*z) = Rcompare x y`.
-/
@[spec]
theorem Rcompare_mult_r_spec (x y z : ℝ) (_hz : 0 < z) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_mult_r x y z) : Id _)
    ⦃⇓result => ⌜result = (Rcompare x y)⌝⦄ := by
  intro _
  unfold Rcompare_mult_r
  rfl

/-- Left multiplication by positive preserves comparison

    Multiplying on the left by a positive value preserves comparison.
-/
noncomputable def Rcompare_mult_l (x y _z : ℝ) : Int :=
  Rcompare x y

/-- Specification: Left positive scaling preserves comparison

    If {lean}`0<z`, then {lean}`Rcompare (z*x) (z*y) = Rcompare x y`.
-/
@[spec]
theorem Rcompare_mult_l_spec (x y z : ℝ) (_hz : 0 < z) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_mult_l x y z) : Id _)
    ⦃⇓result => ⌜result = (Rcompare x y)⌝⦄ := by
  intro _
  unfold Rcompare_mult_l
  rfl

end Rcompare

section RcompareMore

/-- Return the comparison code; used in specialized specs below -/
/-  Coq names like `Rcompare_Lt` refer to the comparison on reals; we provide a
    tiny wrapper returning the Int code, so cross-references to these names
    type-check in documentation. -/
noncomputable def Rcompare_Lt (x y : ℝ) : Int := Rcompare x y
/-- Carrier for {coq}`Rcompare_Eq`: comparison yielding Eq code. -/
noncomputable def Rcompare_Eq (x y : ℝ) : Int := Rcompare x y
/-- Carrier for {coq}`Rcompare_Gt`: comparison yielding Gt code. -/
noncomputable def Rcompare_Gt (x y : ℝ) : Int := Rcompare x y
/-- Carrier for {coq}`Rcompare_not_Lt`: comparison when not Lt. -/
noncomputable def Rcompare_not_Lt (x y : ℝ) : Int := Rcompare x y
/-- Carrier for {coq}`Rcompare_not_Gt`: comparison when not Gt. -/
noncomputable def Rcompare_not_Gt (x y : ℝ) : Int := Rcompare x y
/-- Carrier for {coq}`Rcompare`: generic comparison. -/
noncomputable def Rcompare_val (x y : ℝ) : Int := Rcompare x y

/-- Coq: {lean}`Rcompare_Lt` — if {lean}`x < y` then the comparison yields the Lt code {lean}`-1`. -/
@[spec]
theorem Rcompare_Lt_spec (x y : ℝ) (hxy : x < y) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r = -1⌝⦄ := by
  intro _
  unfold Rcompare_val Rcompare
  -- Reduce the Hoare triple to the postcondition on the pure result
  simp [wp, PostCond.noThrow, Id.run, PredTrans.pure]
  -- With x < y, the comparison branch yields -1
  have hx : x < y := hxy
  simp [hx, pure]

/-/ Coq-named wrapper (renamed locally to avoid clashing with the def). -/
private theorem Rcompare_Lt_wr (x y : ℝ) (hxy : x < y) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r = -1⌝⦄ := by
  simpa using Rcompare_Lt_spec x y hxy

/-- Coq: Rcompare_Lt_inv - from code Lt (-1) deduce x < y. -/
@[spec]
theorem Rcompare_Lt_inv_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r = -1 → x < y⌝⦄ := by
  intro _
  unfold Rcompare_val Rcompare
  -- Reduce to a pure goal on the returned code
  simp [wp, PostCond.noThrow, Id.run, PredTrans.pure]
  -- Goal after simp: (y ≤ x → (if x = y then 0 else 1) = -1) → x < y
  intro hcode
  by_cases hxlt : x < y
  · exact hxlt
  · -- Not (x < y); the code cannot be -1, derive contradiction
    have hbranch : (if x = y then (0 : Int) else 1) = -1 := hcode (le_of_not_gt hxlt)
    by_cases heq : x = y
    · have h0 : (0 : Int) ≠ (-1 : Int) := by decide
      have : (0 : Int) = (-1 : Int) := by simpa [heq] using hbranch
      exact (False.elim (h0 this))
    · have h1 : (1 : Int) ≠ (-1 : Int) := by decide
      have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxlt) (Ne.symm heq)
      have : (1 : Int) = (-1 : Int) := by simpa [heq, hyx] using hbranch
      exact (False.elim (h1 this))

/-/ Coq: Rcompare_not_Lt - if y ≤ x then comparison is not Lt (-1). -/
@[spec]
theorem Rcompare_not_Lt_spec (x y : ℝ) :
    ⦃⌜y ≤ x⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r ≠ -1⌝⦄ := by
  intro hyx
  unfold Rcompare_val Rcompare
  -- Reduce Hoare triple on Id to a pure goal
  simp [wp, PostCond.noThrow, Id.run, PredTrans.pure]
  -- Under y ≤ x, we have ¬ x < y, so we enter the second branch
  have hnot : ¬ x < y := not_lt.mpr hyx
  -- It remains to show: (if x = y then (0 : Int) else 1) ≠ -1
  by_cases hxy : x = y
  · simpa [hnot, hxy]
  · simpa [hnot, hxy]

/-- Coq-named wrapper. -/
private theorem Rcompare_not_Lt_wr (x y : ℝ) :
    ⦃⌜y ≤ x⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r ≠ -1⌝⦄ := by
  simpa using Rcompare_not_Lt_spec x y

/-- Coq: Rcompare\_not\_Lt\_inv. -/
@[spec]
theorem Rcompare_not_Lt_inv_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r ≠ -1 → y ≤ x⌝⦄ := by
  intro _
  unfold Rcompare_val
  -- Reduce to a pure proposition about the returned comparison code
  unfold Rcompare
  simp [wp, PostCond.noThrow, Id.run, PredTrans.pure]
  -- Goal after simp: y ≤ x → ¬(if x = y then 0 else 1) = -1 → y ≤ x
  intro hle _
  exact hle

/-
  Provide the Coq-named lemma without the `_spec` suffix so documentation
  cross-references like {name}`Rcompare_not_Lt_inv` resolve. The statement
  matches `Rcompare_not_Lt_inv_spec` exactly; we expose it under the Coq name
  as a thin wrapper.
-/
theorem Rcompare_not_Lt_inv (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r ≠ -1 → y ≤ x⌝⦄ := by
  simpa using Rcompare_not_Lt_inv_spec x y

/-/ Coq: {lit}`Rcompare_Eq` — if {lean}`x = y` then comparison yields Eq {lean}`0`. -/
@[spec]
theorem Rcompare_Eq_spec (x y : ℝ) :
    ⦃⌜x = y⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r = 0⌝⦄ := by
  intro hxy
  unfold Rcompare_val
  -- Reduce the Hoare triple to the postcondition on the pure result
  unfold Rcompare
  have hEq : x = y := hxy
  simp [wp, PostCond.noThrow, Id.run, pure, hEq]

/-  Coq-named wrapper to satisfy doc cross-references. -/
private theorem Rcompare_Eq_wr (x y : ℝ) :
    ⦃⌜x = y⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r = 0⌝⦄ := by
  simpa using Rcompare_Eq_spec x y

/-/ Coq: {lean}`Rcompare_Eq_inv` - from code Eq {lean}`0` deduce {lean}`x = y`. -/
@[spec]
theorem Rcompare_Eq_inv_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r = 0 → x = y⌝⦄ := by
  intro _
  unfold Rcompare_val
  -- Reduce to a pure proposition about the returned code
  unfold Rcompare
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Goal: (if x < y then -1 else if x = y then 0 else 1) = 0 → x = y
  intro hcode
  by_cases hlt : x < y
  · -- Then the code is -1, contradiction with = 0
    have : (-1 : Int) ≠ 0 := by decide
    have : False := this (by simpa [hlt] using hcode)
    exact this.elim
  · -- Not (x < y); split on equality
    by_cases heq : x = y
    · -- Then the code is 0, so x = y holds
      exact heq
    · -- Otherwise y < x, code is 1, contradiction with = 0
      have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      have : (1 : Int) ≠ 0 := by decide
      have : False := this (by simpa [hlt, heq, hyx] using hcode)
      exact this.elim

/-- Coq-named wrapper. -/
theorem Rcompare_Eq_inv (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r = 0 → x = y⌝⦄ := by
  simpa using Rcompare_Eq_inv_spec x y

/-/ Coq: {lean}`Rcompare_Gt` — if {lean}`y < x` then comparison yields Gt {lean}`1`. -/
@[spec]
theorem Rcompare_Gt_spec (x y : ℝ) :
    ⦃⌜y < x⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r = 1⌝⦄ := by
  intro hyx
  unfold Rcompare_val
  -- Reduce the Hoare triple to a pure goal about the returned code
  unfold Rcompare
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Under y < x, we have ¬ x < y and x ≠ y, hence the code is 1
  have hnotlt : ¬ x < y := not_lt.mpr (le_of_lt hyx)
  have hneq : x ≠ y := by exact Ne.symm (ne_of_lt hyx)
  simp [hnotlt, hneq]

/-  Coq-named wrapper. -/
private theorem Rcompare_Gt_wr (x y : ℝ) :
    ⦃⌜y < x⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r = 1⌝⦄ := by
  simpa using Rcompare_Gt_spec x y

/-- Coq: Rcompare_Gt_inv — from code Gt 1, deduce y < x. -/
@[spec]
theorem Rcompare_Gt_inv_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r = 1 → y < x⌝⦄ := by
  intro _
  unfold Rcompare_val
  -- Reduce to a pure proposition about the returned comparison code
  unfold Rcompare
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Goal: (if x < y then -1 else if x = y then 0 else 1) = 1 → y < x
  intro hcode
  by_cases hlt : x < y
  · -- Then the code is -1, contradiction with = 1
    have : (-1 : Int) ≠ 1 := by decide
    have : False := this (by simpa [hlt] using hcode)
    exact this.elim
  · -- Not (x < y); split on equality
    by_cases heq : x = y
    · -- Then the code is 0, contradiction with = 1
      have : (0 : Int) ≠ 1 := by decide
      have : False := this (by simpa [hlt, heq] using hcode)
      exact this.elim
    · -- Otherwise y < x, as desired
      exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)

/-  Coq-named wrapper. -/
theorem Rcompare_Gt_inv (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r = 1 → y < x⌝⦄ := by
  simpa using Rcompare_Gt_inv_spec x y

/-/ Coq: {lean}`Rcompare_not_Gt` — if {lean}`x ≤ y` then comparison is not Gt {lean}`1`. -/
@[spec]
theorem Rcompare_not_Gt_spec (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r ≠ 1⌝⦄ := by
  intro hxy
  unfold Rcompare_val Rcompare
  -- Reduce Hoare triple on Id to a pure goal
  simp [wp, PostCond.noThrow, Id.run]
  -- Goal: (if x < y then -1 else if x = y then 0 else 1) ≠ 1
  by_cases hlt : x < y
  · -- In the Lt branch the code is -1
    simp [hlt, pure]
  · -- Not (x < y). Under x ≤ y, this forces x = y
    have hyx : y ≤ x := not_lt.mp hlt
    have hEq : x = y := le_antisymm hxy hyx
    simp [hEq, pure]

/-  Coq-named wrapper. -/
private theorem Rcompare_not_Gt_wr (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r ≠ 1⌝⦄ := by
  simpa using Rcompare_not_Gt_spec x y

/-- Coq theorem Rcompare\_not\_Gt\_inv. -/
@[spec]
theorem Rcompare_not_Gt_inv_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r ≠ 1 → x ≤ y⌝⦄ := by
  intro _
  unfold Rcompare_val
  -- Reduce to a pure proposition about the returned comparison code
  unfold Rcompare
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Goal: (if x < y then -1 else if x = y then 0 else 1) ≠ 1 → x ≤ y
  intro hneq
  by_cases hlt : x < y
  · -- Then x ≤ y holds immediately
    exact le_of_lt hlt
  · -- Not (x < y); split on equality
    by_cases heq : x = y
    · -- Then x ≤ y trivially
      simpa [heq]
    · -- Otherwise, the code would be 1, contradicting hneq; derive x ≤ y by ex falso
      exact (False.elim (hneq (by simpa [hlt, heq])))

/-  Coq-named wrapper. -/
theorem Rcompare_not_Gt_inv (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_val x y) : Id _)
    ⦃⇓r => ⌜r ≠ 1 → x ≤ y⌝⦄ := by
  simpa using Rcompare_not_Gt_inv_spec x y

/-- Integer comparison as an Int code (-1/0/1), mirroring Coq's Z.compare -/
def Zcompare_int (m n : Int) : Int :=
  (if m < n then -1 else if m = n then 0 else 1)

/-- Carrier for {coq}`Rcompare_IZR`: comparing casts of integers matches integer comparison. -/
noncomputable def Rcompare_IZR (m n : Int) : Int := Rcompare (m : ℝ) (n : ℝ)

/-- Coq theorem {name}`Rcompare_IZR`: comparing casts of integers matches integer comparison. -/
@[spec]
theorem Rcompare_IZR_spec (m n : Int) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_IZR m n) : Id _)
    ⦃⇓r => ⌜r = (Zcompare_int m n)⌝⦄ := by
  intro _
  -- Discharge the Hoare triple by computation on both sides
  simp [Zcompare_int, Rcompare_IZR, Rcompare, wp, PostCond.noThrow, Id.run, pure]

/-- Middle-value comparison identity: compare (x - d) vs (u - x) equals comparing x vs (d+u)/2 -/
noncomputable def Rcompare_middle_check (x d u : ℝ) : (Int × Int) :=
  let c := (Rcompare x ((d + u) / 2))
  (c, c)

@[spec]
theorem Rcompare_middle_spec (x d u : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_middle_check x d u) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rcompare_middle_check
  simp [wp, PostCond.noThrow, Id.run]

/-- Halving on left: compare {lean}`x/2` with {lean}`y` equals compare {lean}`x` with {lean}`2*y`. -/
noncomputable def Rcompare_half_l_check (x y : ℝ) : (Int × Int) :=
  ((Rcompare (x / 2) y), (Rcompare x (2 * y)))

@[spec]
theorem Rcompare_half_l_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_half_l_check x y) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rcompare_half_l_check
  -- Reduce the Hoare triple and expand the comparisons
  simp [wp, PostCond.noThrow, Id.run, Rcompare, pure]
  -- Show the two nested-condition expressions are equal by
  -- transporting inequalities/equalities via multiplication by 2 > 0.
  have h2pos : (0 : ℝ) < 2 := by norm_num
  -- Build the equivalence without relying on named div lemmas.
  have hlt : (x / 2 < y) ↔ (x < 2 * y) := by
    constructor
    · intro h
      have := mul_lt_mul_of_pos_right h h2pos
      -- (x/2)*2 = x
      -- y*2 = 2*y
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    · intro h
      have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
      have := mul_lt_mul_of_pos_right h hhalfpos
      -- x*(1/2) = x/2 and (2*y)*(1/2) = y
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have heq : (x / 2 = y) ↔ (x = 2 * y) := by
    -- x/2 = y  ↔  x = y*2  ↔  x = 2*y
    have h2ne : (2 : ℝ) ≠ 0 := by norm_num
    simpa [mul_comm] using (div_eq_iff h2ne : x / 2 = y ↔ x = y * 2)
  -- Case analysis on x < 2*y and x = 2*y to align the branches.
  by_cases hxlt : x < 2 * y
  · have : x / 2 < y := (hlt.mpr hxlt)
    simp [hxlt, this]
  · have hxnotlt : ¬ x < 2 * y := by exact hxlt
    by_cases hxeq : x = 2 * y
    · have : x / 2 = y := (heq.mpr hxeq)
      simp [hxeq]
    ·
      -- From ¬ (x < 2*y), obtain ¬ (x/2 < y) via hlt;
      -- from x ≠ 2*y, obtain x/2 ≠ y via heq.
      have hx2notlt : ¬ x / 2 < y := by
        intro h
        exact hxnotlt (hlt.mp h)
      have hx2neq : x / 2 ≠ y := by
        intro h
        exact hxeq (heq.mp h)
      simp [hxnotlt, hxeq, hx2notlt, hx2neq]

/-- Halving on right: compare {lean}`x` with {lean}`y/2` equals compare {lean}`2*x` with {lean}`y`. -/
noncomputable def Rcompare_half_r_check (x y : ℝ) : (Int × Int) :=
  ((Rcompare x (y / 2)), (Rcompare (2 * x) y))

@[spec]
theorem Rcompare_half_r_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_half_r_check x y) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rcompare_half_r_check
  -- Reduce to equality of the nested-condition expressions
  simp [wp, PostCond.noThrow, Id.run, Rcompare, pure]
  -- Transport comparisons via multiplication by positive constants
  have h2pos : (0 : ℝ) < 2 := by norm_num
  -- Inequality equivalence: x < y/2  ↔  2*x < y
  have hlt : (x < y / 2) ↔ (2 * x < y) := by
    constructor
    · intro h
      have := mul_lt_mul_of_pos_right h h2pos
      -- x*2 < (y/2)*2 = y
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
    · intro h
      have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
      have := mul_lt_mul_of_pos_right h hhalfpos
      -- (2*x)*(1/2) = x and y*(1/2) = y/2
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
  -- Equality equivalence: x = y/2  ↔  2*x = y
  have heq : (x = y / 2) ↔ (2 * x = y) := by
    have h2ne : (2 : ℝ) ≠ 0 := by norm_num
    -- eq_div_iff: x = y/2 ↔ x*2 = y
    simpa [mul_comm] using (eq_div_iff h2ne : x = y / 2 ↔ x * 2 = y)
  -- Case analysis on the right-hand comparison
  by_cases hxlt : 2 * x < y
  · have : x < y / 2 := (hlt.mpr hxlt)
    simp [hxlt, this]
  · have hxnotlt : ¬ 2 * x < y := by exact hxlt
    by_cases hxeq : 2 * x = y
    · have hx_eq : x = y / 2 := (heq.symm.mp hxeq)
      -- First reduce the right side using hxeq
      simp [hxeq]
      -- Then reduce the left side using hx_eq
      simp [hx_eq]
    ·
      -- Transport the negations via the equivalences
      have hx2notlt : ¬ x < y / 2 := by
        intro h
        exact hxnotlt (hlt.mp h)
      have hx2neq : x ≠ y / 2 := by
        intro h
        exact hxeq (heq.mp h)
      simp [hxnotlt, hxeq, hx2notlt, hx2neq]

/-- Square comparison reduces to comparison on absolute values -/
noncomputable def Rcompare_sqr_check (x y : ℝ) : (Int × Int) :=
  ((Rcompare (x * x) (y * y)), (Rcompare |x| |y|))

private theorem Rcompare_sqr_run_eq (x y : ℝ) :
    (Rcompare (x * x) (y * y)) = (Rcompare |x| |y|) := by
  -- Compare using the three cases on |x| and |y|
  rcases lt_trichotomy (|x|) (|y|) with hlt | heq | hgt
  · -- Lt case
    have hx2 : x ^ 2 < y ^ 2 := (sq_lt_sq).2 hlt
    -- Left code is -1, right code is -1
    have hx2' : x * x < y * y := by simpa [pow_two] using hx2
    simp [Rcompare, pure, Id.run, hx2', hlt]
  · -- Eq case
    have hx2eq : x ^ 2 = y ^ 2 := by
      simpa [sq_abs] using congrArg (fun t => t ^ (2 : Nat)) heq
    have hxeq' : x * x = y * y := by simpa [pow_two] using hx2eq
    -- Show the left code is 0 (second branch), and the right code is 0 (equality)
    by_cases hxlt : x * x < y * y
    · -- Contradiction: rewriting by equality gives x*x < x*x
      have hxlt' : x * x < x * x := by simpa [hxeq'] using hxlt
      exact (False.elim ((lt_irrefl _) hxlt'))
    · simp [Rcompare, pure, Id.run, hxeq', heq]
  · -- Gt case
    have hy2 : y ^ 2 < x ^ 2 := (sq_lt_sq).2 hgt
    have hnotlt : ¬ x * x < y * y := by
      have : ¬ x ^ 2 < y ^ 2 := not_lt.mpr (le_of_lt hy2)
      simpa [pow_two] using this
    have hneq : x * x ≠ y * y := by
      have : x ^ 2 ≠ y ^ 2 := by simpa [eq_comm] using (ne_of_gt hy2)
      simpa [pow_two] using this
    -- With ¬(x^2 < y^2) and x^2 ≠ y^2, left code is 1; on the right we are in the Gt branch
    -- Also reduce the right side using ¬(|x| < |y|) and |x| ≠ |y|
    have hnotlt_abs : ¬ |x| < |y| := not_lt_of_ge (le_of_lt hgt)
    have hneq_abs : |x| ≠ |y| := by
      intro hEq
      -- From |y| < |x| and |x| = |y|, derive the contradiction |y| < |y|
      have : |y| < |y| := by simpa [hEq] using hgt
      exact (lt_irrefl _ this)
    simp [Rcompare, pure, Id.run, hnotlt, hneq, hnotlt_abs, hneq_abs]

@[spec]
theorem Rcompare_sqr_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_sqr_check x y) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rcompare_sqr_check
  -- Reduce the Hoare triple on Id to a pure equality, then use the helper lemma
  simp [wp, PostCond.noThrow, Id.run]
  -- Now it's a pure equality of integers
  simpa using (Rcompare_sqr_run_eq x y)

/-- Minimum expressed via comparison code -/
noncomputable def Rmin_compare_check (x y : ℝ) : (ℝ × Int) :=
  (min x y, (Rcompare x y))

@[spec]
theorem Rmin_compare_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rmin_compare_check x y) : Id _)
    ⦃⇓p => ⌜p.1 = (if p.2 = -1 then x else if p.2 = 0 then x else y)⌝⦄ := by
  intro _
  unfold Rmin_compare_check
  -- Reduce to a pure equality and expand the comparison code
  simp [wp, PostCond.noThrow, Id.run, Rcompare, pure]
  -- Goal is now: min x y = if c = -1 then x else if c = 0 then x else y
  -- where c = if x < y then -1 else if x = y then 0 else 1.
  by_cases hlt : x < y
  · have hle : x ≤ y := le_of_lt hlt
    -- Left side: min x y = x; right side reduces to x
    simp [hlt, hle]
  · have hnotlt : ¬ x < y := hlt
    by_cases heq : x = y
    · -- In the equality case, both sides reduce to x
      subst heq
      simp
    · -- Strict greater case: y < x
      have hgt : y < x := lt_of_le_of_ne (le_of_not_gt hnotlt) (Ne.symm heq)
      have hleyx : y ≤ x := le_of_lt hgt
      -- Left side: min x y = y; right side reduces to y
      simp [hnotlt, heq, hleyx]

end RcompareMore

section BooleanComparisons

/-- Boolean less-or-equal test for real numbers

    Tests whether x ≤ y, returning a boolean result.
    This provides a decidable ordering test.
-/
noncomputable def Rle_bool (x y : ℝ) : Bool :=
  (decide (x ≤ y))

/-- Coq {coq}`Rle_bool_prop`: inductive characterization of {lean}`Rle_bool`. -/
inductive Rle_bool_prop (x y : ℝ) : Bool → Prop where
  | Rle_bool_true_ : x ≤ y → Rle_bool_prop x y true
  | Rle_bool_false_ : y < x → Rle_bool_prop x y false

export Rle_bool_prop (Rle_bool_true_ Rle_bool_false_)

/-- Coq {coq}`Rle_bool_prop_ind` (alias of the recursor). -/
abbrev Rle_bool_prop_ind := @Rle_bool_prop.rec

/-- Coq {coq}`Rle_bool_prop_sind` (alias of the recursor). -/
abbrev Rle_bool_prop_sind := @Rle_bool_prop.rec

/-- Coq-style spec: {coq}`Rle_bool_prop` holds for {lean}`Rle_bool`. -/
theorem Rle_bool_prop_spec (x y : ℝ) : Rle_bool_prop x y (Rle_bool x y) := by
  by_cases hxy : x ≤ y
  · have h : Rle_bool_prop x y true := Rle_bool_true_ hxy
    simpa [Rle_bool, hxy] using h
  · have hyx : y < x := lt_of_not_ge hxy
    have h : Rle_bool_prop x y false := Rle_bool_false_ hyx
    simpa [Rle_bool, hxy] using h

/-- Specification: Boolean ordering test

    The boolean less-or-equal test returns true if and only if
    x ≤ y. This provides a computational version of the ordering.
-/
@[spec]
theorem Rle_bool_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rle_bool x y) : Id _)
    ⦃⇓result => ⌜result = true ↔ x ≤ y⌝⦄ := by
  intro _
  unfold Rle_bool
  -- Reduce Hoare triple on Id to a pure proposition about `decide (x ≤ y)`
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- The decidable instance for ℝ gives: decide (x ≤ y) = true ↔ x ≤ y
  -- Goal is solved by simp

/-- Monotone case: if x ≤ y then {lean}`Rle_bool x y = true` -/
theorem Rle_bool_true (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    (pure (Rle_bool x y) : Id _)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hxy
  unfold Rle_bool
  -- Reduce Hoare triple to a pure goal and apply decidability
  simp [wp, PostCond.noThrow, Id.run, pure]
  exact hxy

/-- Antitone case: if y < x then {lean}`Rle_bool x y = false` -/
theorem Rle_bool_false (x y : ℝ) :
    ⦃⌜y < x⌝⦄
    (pure (Rle_bool x y) : Id _)
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro hyx
  unfold Rle_bool
  -- Follows from decidability of (≤) on ℝ and `¬(x ≤ y)` from `y < x`
  simp [wp, PostCond.noThrow, Id.run, pure]
  exact hyx

/-- Boolean strict less-than test for real numbers

    Tests whether x < y, returning a boolean result.
    This provides a decidable strict ordering test.
-/
noncomputable def Rlt_bool (x y : ℝ) : Bool :=
  (x < y)

/-- Coq {coq}`Rlt_bool_prop`: inductive characterization of {lean}`Rlt_bool`. -/
inductive Rlt_bool_prop (x y : ℝ) : Bool → Prop where
  | Rlt_bool_true_ : x < y → Rlt_bool_prop x y true
  | Rlt_bool_false_ : y ≤ x → Rlt_bool_prop x y false

export Rlt_bool_prop (Rlt_bool_true_ Rlt_bool_false_)

/-- Coq {coq}`Rlt_bool_prop_ind` (alias of the recursor). -/
abbrev Rlt_bool_prop_ind := @Rlt_bool_prop.rec

/-- Coq {coq}`Rlt_bool_prop_sind` (alias of the recursor). -/
abbrev Rlt_bool_prop_sind := @Rlt_bool_prop.rec

/-- Coq-style spec: {coq}`Rlt_bool_prop` holds for {lean}`Rlt_bool`. -/
theorem Rlt_bool_prop_spec (x y : ℝ) : Rlt_bool_prop x y (Rlt_bool x y) := by
  by_cases hxy : x < y
  · have h : Rlt_bool_prop x y true := Rlt_bool_true_ hxy
    simpa [Rlt_bool, hxy] using h
  · have hyx : y ≤ x := le_of_not_gt hxy
    have h : Rlt_bool_prop x y false := Rlt_bool_false_ hyx
    simpa [Rlt_bool, hxy] using h

/-- Specification: Boolean strict ordering test

    The boolean less-than test returns true if and only if
    x < y. This provides a computational version of strict ordering.
-/
@[spec]
theorem Rlt_bool_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rlt_bool x y) : Id _)
    ⦃⇓result => ⌜result = true ↔ x < y⌝⦄ := by
  intro _
  unfold Rlt_bool
  -- The decidable instance for ℝ gives us this
  simp [wp, PostCond.noThrow, pure, decide_eq_true_iff]

/-- Monotone case: if x < y then {lean}`Rlt_bool x y = true` -/
theorem Rlt_bool_true (x y : ℝ) :
    ⦃⌜x < y⌝⦄
    (pure (Rlt_bool x y) : Id _)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hlt
  unfold Rlt_bool
  -- Follows from decidability of (<) on ℝ
  simp [wp, PostCond.noThrow, Id.run, pure]
  exact hlt

/-- Antitone case: if y ≤ x then {lean}`Rlt_bool x y = false` -/
theorem Rlt_bool_false (x y : ℝ) :
    ⦃⌜y ≤ x⌝⦄
    (pure (Rlt_bool x y) : Id _)
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro hyx
  unfold Rlt_bool
  -- Follows from decidability of (<) on ℝ and `¬ (x < y)` from `y ≤ x`
  simp [wp, PostCond.noThrow, Id.run, pure, not_lt.mpr hyx]

/-- Negation flips strict-less-than boolean

    Rlt_bool (-x) (-y) = Rlt_bool y x.
    Direct consequence of {coq}`Rcompare_opp` in Coq; mirrors here.
-/
theorem Rlt_bool_opp (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rlt_bool (-x) (-y), Rlt_bool y x) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rlt_bool
  -- Reduce to equality of the underlying boolean tests and use neg_lt_neg_iff
  simp [wp, PostCond.noThrow, Id.run, pure, bind, neg_lt_neg_iff]

/-- Negation of strict less-than is greater-or-equal

    Boolean negation of x < y is equivalent to y ≤ x.
    This captures the duality between < and ≥.
-/
noncomputable def negb_Rlt_bool (x y : ℝ) : Bool :=
  (y ≤ x)

/-- Specification: Negated < equals ≥

    For booleans, not (x < y) ↔ y ≤ x.
    This duality is fundamental for simplifying comparisons.
-/
@[spec]
theorem negb_Rlt_bool_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (negb_Rlt_bool x y) : Id _)
    ⦃⇓result => ⌜result ↔ y ≤ x⌝⦄ := by
  intro _
  unfold negb_Rlt_bool
  -- The decidable instance for ℝ gives us this
  simp [wp, PostCond.noThrow, pure, decide_eq_true_iff]

/-- Negation of less-or-equal is strict greater-than

    Boolean negation of x ≤ y is equivalent to y < x.
    This captures the duality between ≤ and >.
-/
noncomputable def negb_Rle_bool (x y : ℝ) : Bool :=
  (y < x)

/-- Specification: Negated ≤ equals >

    For booleans, {lean}`(¬ (x ≤ y)) ↔ y < x`.
    This completes the duality between orderings.
-/
@[spec]
theorem negb_Rle_bool_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (negb_Rle_bool x y) : Id _)
    ⦃⇓result => ⌜result ↔ y < x⌝⦄ := by
  intro _
  unfold negb_Rle_bool
  -- The decidable instance for ℝ gives us this
  simp [wp, PostCond.noThrow, pure, decide_eq_true_iff]

/-- Boolean equality test for real numbers

    Tests whether two real numbers are equal, returning a boolean.
    This provides a decidable equality test.
-/
noncomputable def Req_bool (x y : ℝ) : Bool :=
  (x = y)

/-- Coq {coq}`Req_bool_prop`: inductive characterization of {lean}`Req_bool`. -/
inductive Req_bool_prop (x y : ℝ) : Bool → Prop where
  | Req_bool_true_ : x = y → Req_bool_prop x y true
  | Req_bool_false_ : x ≠ y → Req_bool_prop x y false

export Req_bool_prop (Req_bool_true_ Req_bool_false_)

/-- Coq {coq}`Req_bool_prop_ind` (alias of the recursor). -/
abbrev Req_bool_prop_ind := @Req_bool_prop.rec

/-- Coq {coq}`Req_bool_prop_sind` (alias of the recursor). -/
abbrev Req_bool_prop_sind := @Req_bool_prop.rec

/-- Coq-style spec: {coq}`Req_bool_prop` holds for {lean}`Req_bool`. -/
theorem Req_bool_prop_spec (x y : ℝ) : Req_bool_prop x y (Req_bool x y) := by
  by_cases hxy : x = y
  · have h : Req_bool_prop x y true := Req_bool_true_ hxy
    simpa [Req_bool, hxy] using h
  · have h : Req_bool_prop x y false := Req_bool_false_ hxy
    simpa [Req_bool, hxy] using h

/-- Specification: Boolean equality test

    The boolean equality test returns true if and only if
    the real numbers are equal. This provides a computational
    version of equality.
-/
@[spec]
theorem Req_bool_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Req_bool x y) : Id _)
    ⦃⇓result => ⌜result = true ↔ x = y⌝⦄ := by
  intro _
  unfold Req_bool
  -- The decidable instance for ℝ gives us this
  simp [wp, PostCond.noThrow, pure, decide_eq_true_iff]

/-- If x = y then {lean}`Req_bool x y = true` -/
theorem Req_bool_true (x y : ℝ) :
    ⦃⌜x = y⌝⦄
    (pure (Req_bool x y) : Id _)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hxy
  unfold Req_bool
  -- Reduce Hoare triple to a pure goal and apply decidability
  simp [wp, PostCond.noThrow, Id.run, pure]
  exact hxy

/-- If x ≠ y then {lean}`Req_bool x y = false` -/
theorem Req_bool_false (x y : ℝ) :
    ⦃⌜x ≠ y⌝⦄
    (pure (Req_bool x y) : Id _)
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro hxy
  unfold Req_bool
  -- Reduce the Hoare triple to a pure boolean equality via wp for Id
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Now it suffices to turn `x = y` into False using `hxy`
  exact hxy

end BooleanComparisons

section BooleanOperations

/-- Boolean equality is symmetric

    The equality test for booleans is symmetric:
    (a == b) = (b == a).
-/
def eqb_sym (a b : Bool) : (Bool × Bool) :=
  ((a == b), (b == a))

/-- Specification: Boolean equality symmetry

    a == b equals b == a for all booleans.
-/
@[spec]
theorem eqb_sym_spec (a b : Bool) :
    ⦃⌜True⌝⦄
    (pure (eqb_sym a b) : Id _)
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  intro _
  unfold eqb_sym
  -- Boolean equality is symmetric
  exact Bool.beq_comm

/-- Boolean equality test wrapper for {coq}`eqb` specs. -/
def eqb_check (a b : Bool) : Bool :=
  (a == b)

/-- If a = b then (a == b) = true -/
@[spec]
theorem eqb_true_spec (a b : Bool) :
    ⦃⌜a = b⌝⦄
    (pure (eqb_check a b) : Id _)
    ⦃⇓r => ⌜r = true⌝⦄ := by
  intro hEq
  unfold eqb_check
  -- Follows from Bool equality
  -- Reduce to the reflexive cases using the hypothesis a = b
  cases hEq
  cases a <;> simp

/-- If a ≠ b then (a == b) = false -/
@[spec]
theorem eqb_false_spec (a b : Bool) :
    ⦃⌜a ≠ b⌝⦄
    (pure (eqb_check a b) : Id _)
    ⦃⇓r => ⌜r = false⌝⦄ := by
  intro hNe
  unfold eqb_check
  -- Follows from Bool disequality
  -- Exhaust over a,b and use the contradiction for equal cases
  cases a <;> cases b <;> simp at *

end BooleanOperations

section ConditionalOpposite

/-- Conditional opposite based on sign

    Returns -m if the condition is true, m otherwise.
    This is used for conditional negation in floating-point
    sign handling.
-/
def cond_Ropp (b : Bool) (m : ℝ) : ℝ :=
  if b then -m else m

/-- Specification: Conditional negation

    The conditional opposite operation returns:
    - -m when b is true
    - m when b is false

    This is fundamental for handling signs in floating-point.
-/
@[spec]
theorem cond_Ropp_spec (b : Bool) (m : ℝ) :
    ⦃⌜True⌝⦄
    (pure (cond_Ropp b m) : Id _)
    ⦃⇓result => ⌜result = if b then -m else m⌝⦄ := by
  intro _
  unfold cond_Ropp
  rfl

/-- Conditional opposite is involutive

    Applying conditional opposite twice with the same
    boolean returns the original value.
-/
def cond_Ropp_involutive (b : Bool) (m : ℝ) : ℝ :=
  let x := cond_Ropp b m
  cond_Ropp b x

/-- Specification: Involutive property

    cond_Ropp b (cond_Ropp b m) = m.
    Double application cancels out.
-/
@[spec]
theorem cond_Ropp_involutive_spec (b : Bool) (m : ℝ) :
    ⦃⌜True⌝⦄
    (pure (cond_Ropp_involutive b m) : Id _)
    ⦃⇓result => ⌜result = m⌝⦄ := by
  intro _
  unfold cond_Ropp_involutive
  simp [cond_Ropp, bind]
  by_cases h : b
  · simp [h]
  · simp [h]

/-- Conditional opposite is injective

    If conditional opposites are equal with the same boolean,
    then the original values must be equal.
-/
def cond_Ropp_inj (_b : Bool) (m1 m2 : ℝ) : (ℝ × ℝ) :=
  (m1, m2)

/-- Specification: Injectivity

    If cond_Ropp b m1 = cond_Ropp b m2, then m1 = m2.
-/
@[spec]
theorem cond_Ropp_inj_spec (b : Bool) (m1 m2 : ℝ) :
    ⦃⌜(cond_Ropp b m1) = (cond_Ropp b m2)⌝⦄
    (pure (cond_Ropp_inj b m1 m2) : Id _)
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  intro h
  unfold cond_Ropp_inj
  -- h states that cond_Ropp b m1 = cond_Ropp b m2
  -- We need to prove m1 = m2
  simp [cond_Ropp, Id.run] at h
  by_cases hb : b
  · simp [hb] at h
    -- h : -m1 = -m2, need to prove m1 = m2
    have : m1 = m2 := by linarith
    exact this
  · simp [hb] at h
    exact h

end ConditionalOpposite

section CondAbsMulAdd

/-- Absolute value is invariant under conditional negation -/
noncomputable def abs_cond_Ropp_check (b : Bool) (x : ℝ) : ℝ :=
  (|cond_Ropp b x|)

@[spec]
theorem abs_cond_Ropp_spec (b : Bool) (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (abs_cond_Ropp_check b x) : Id _)
    ⦃⇓r => ⌜r = |x|⌝⦄ := by
  intro _
  unfold abs_cond_Ropp_check cond_Ropp
  -- |if b then -x else x| = |x|
  by_cases hb : b
  · simp [hb, abs_neg]
  · simp [hb]

/-- Conditional negation distributes over multiplication (left) -/
noncomputable def cond_Ropp_mult_l_check (b : Bool) (x y : ℝ) : ℝ :=
  cond_Ropp b (x * y)

@[spec]
theorem cond_Ropp_mult_l_spec (b : Bool) (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (cond_Ropp_mult_l_check b x y) : Id _)
    ⦃⇓r => ⌜r = (cond_Ropp b x) * y⌝⦄ := by
  intro _
  unfold cond_Ropp_mult_l_check cond_Ropp
  -- Reduce the Hoare triple on Id to a pure goal
  simp [wp, PostCond.noThrow, Id.run, neg_mul]

/-- Conditional negation distributes over multiplication (right) -/
noncomputable def cond_Ropp_mult_r_check (b : Bool) (x y : ℝ) : ℝ :=
  cond_Ropp b (x * y)

@[spec]
theorem cond_Ropp_mult_r_spec (b : Bool) (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (cond_Ropp_mult_r_check b x y) : Id _)
    ⦃⇓r => ⌜r = x * (cond_Ropp b y)⌝⦄ := by
  intro _
  unfold cond_Ropp_mult_r_check cond_Ropp
  -- if b then -(x*y) else (x*y) equals x * (if b then -y else y)
  simp [wp, PostCond.noThrow, Id.run, mul_neg]

/-- Conditional negation distributes over addition -/
noncomputable def cond_Ropp_plus_check (b : Bool) (x y : ℝ) : ℝ :=
  cond_Ropp b (x + y)

@[spec]
theorem cond_Ropp_plus_spec (b : Bool) (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (cond_Ropp_plus_check b x y) : Id _)
    ⦃⇓r => ⌜r = (cond_Ropp b x) + (cond_Ropp b y)⌝⦄ := by
  intro _
  unfold cond_Ropp_plus_check cond_Ropp
  -- if b then -(x+y) else (x+y) equals (if b then -x else x) + (if b then -y else y)
  cases b <;>
    simp [wp, PostCond.noThrow, Id.run, add_comm]

end CondAbsMulAdd

section CondRltBool

/-- Compare after conditional negation on both sides -/
noncomputable def cond_Ropp_Rlt_bool_check (b : Bool) (x y : ℝ) : Bool :=
  let x' := cond_Ropp b x
  let y' := cond_Ropp b y
  Rlt_bool x' y'

@[spec]
theorem cond_Ropp_Rlt_bool_spec (b : Bool) (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (cond_Ropp_Rlt_bool_check b x y) : Id _)
    ⦃⇓r => ⌜r = true ↔ (if b then y < x else x < y)⌝⦄ := by
  intro _
  unfold cond_Ropp_Rlt_bool_check
  -- Negation reverses strict inequality
  -- Reduce the Hoare triple on Id and inline the definitions
  simp [wp, PostCond.noThrow, Id.run, pure, bind, Rlt_bool, cond_Ropp]
  -- Now analyze on the boolean flag and use `neg_lt_neg_iff`
  by_cases hb : b
  · -- When b = true, we compare -x and -y, which flips the inequality
    simp [hb, neg_lt_neg_iff]
  · -- When b = false, the inequality is unchanged
    simp [hb]

/-- Compare after conditional negation on right side -/
noncomputable def Rlt_bool_cond_Ropp_check (b : Bool) (x y : ℝ) : Bool :=
  let y' := cond_Ropp b y
  Rlt_bool x y'

@[spec]
theorem Rlt_bool_cond_Ropp_spec (b : Bool) (x y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rlt_bool_cond_Ropp_check b x y) : Id _)
    ⦃⇓r => ⌜r = true ↔ (if b then x < -y else x < y)⌝⦄ := by
  intro _
  unfold Rlt_bool_cond_Ropp_check cond_Ropp
  -- If b then compare against -y, else against y
  simp [wp, PostCond.noThrow, Id.run, pure, bind, Rlt_bool]
  by_cases hb : b
  · simp [hb]
  · simp [hb]

end CondRltBool

section IZRCond

/-- Conditional opposite commutes with integer-to-real cast -/
noncomputable def IZR_cond_Zopp_check (b : Bool) (m : Int) : ℝ :=
  cond_Ropp b (m : ℝ)

@[spec]
theorem IZR_cond_Zopp_spec (b : Bool) (m : Int) :
    ⦃⌜True⌝⦄
    (pure (IZR_cond_Zopp_check b m) : Id _)
    ⦃⇓r => ⌜r = (if b then -((m : ℝ)) else (m : ℝ))⌝⦄ := by
  intro _
  unfold IZR_cond_Zopp_check cond_Ropp
  rfl

end IZRCond

-- Inverse bounds for strict absolute inequalities
section AbsLtInv

/-- Pair carrier for the inverse strict-abs inequality result: -y < x ∧ x < y -/
noncomputable def Rabs_lt_inv_pair (x y : ℝ) : (ℝ × ℝ) :=
  (x, y)

/-- Specification: From {lit}`|x| < y` derive the two-sided strict bound {lit}`-y < x < y`. -/
@[spec]
theorem Rabs_lt_inv_spec (x y : ℝ) :
    ⦃⌜|x| < y⌝⦄
    (pure (Rabs_lt_inv_pair x y) : Id _)
    ⦃⇓p => ⌜-p.2 < p.1 ∧ p.1 < p.2⌝⦄ := by
  intro h
  unfold Rabs_lt_inv_pair
  -- Standard equivalence for real absolute value
  simpa using (abs_lt.mp h)

end AbsLtInv

-- Integer rounding helpers (floor/ceil/trunc/away) and their properties
section IntRound

/-- Integer floor as an Id-wrapped Int -/
noncomputable def Zfloor (x : ℝ) : Int :=
  ⌊x⌋

/-- Integer ceiling as an Id-wrapped Int -/
noncomputable def Zceil (x : ℝ) : Int :=
  ⌈x⌉

/-- Truncation toward zero: ceil for negatives, floor otherwise -/
noncomputable def Ztrunc (x : ℝ) : Int :=
  (if x < 0 then ⌈x⌉ else ⌊x⌋)

/-- Carrier for Ztrunc_abs_real: casted truncation of |y| as a real. -/
noncomputable def Ztrunc_abs_real_val (y : ℝ) : ℝ :=
  (((Ztrunc (abs y)) : Int) : ℝ)

theorem Ztrunc_abs_real (y : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Ztrunc_abs_real_val y) : Id _)
    ⦃⇓r => ⌜r = abs (((Ztrunc y) : Int) : ℝ)⌝⦄ := by
  -- First, reduce the Hoare-style triple for `pure` to a plain goal.
  -- This turns the specification into `True → r = ...`.
  intro _
  -- Work by cases on the sign of y and unfold Ztrunc.
  unfold Ztrunc_abs_real_val
  by_cases hy : y < 0
  · -- Negative case: compute both sides explicitly and compare
    have hceil_nonpos : Int.ceil y ≤ 0 := (Int.ceil_le).mpr (by simpa using (le_of_lt hy))
    have hceil_nonposR : ((Int.ceil y : Int) : ℝ) ≤ 0 := by exact_mod_cast hceil_nonpos
    -- Left-hand side: Ztrunc (|y|) = ⌊-y⌋ = -⌈y⌉
    have hL : (((Ztrunc (abs y)) : Int) : ℝ) = -(((Int.ceil y : Int) : ℝ)) := by
      have : (Ztrunc (abs y)) = Int.floor (-y) := by
        -- since y < 0, we have |y| = -y and Ztrunc uses floor on nonnegatives
        have : (abs y) = -y := by simpa [abs_of_neg hy]
        -- Ztrunc on nonnegative arguments reduces to floor
        -- because -y > 0 given y < 0
        have hypos : 0 < -y := by exact neg_pos.mpr hy
        -- Now simplify Ztrunc (abs y)
        simp [Ztrunc, this, not_lt.mpr (le_of_lt hypos)]
      -- Cast both sides to ℝ and rewrite floor(-y)
      simpa [Int.floor_neg, Int.cast_neg] using congrArg (fun i : Int => (i : ℝ)) this
    -- Right-hand side: abs (⌈y⌉) = -⌈y⌉ because ⌈y⌉ ≤ 0
    have hR : abs ((((Ztrunc y) : Int) : ℝ)) = -(((Int.ceil y : Int) : ℝ)) := by
      -- Ztrunc y uses ceil when y < 0
      have : (((Ztrunc y) : Int) : ℝ) = ((Int.ceil y : Int) : ℝ) := by
        simp [Ztrunc, hy]
      -- simplify absolute value using nonpositivity of ⌈y⌉
      rw [this, abs_of_nonpos hceil_nonposR]
    -- Conclude by comparing both canonical forms
    simp only [Ztrunc_abs_real_val, wp, PostCond.noThrow, Id.run]
    exact hL.trans hR.symm
  · -- Nonnegative case: |y| = y and both truncations use floor
    have hy0 : 0 ≤ y := le_of_not_gt hy
    have hfloor_nonneg : 0 ≤ (Int.floor y : Int) := (Int.le_floor).mpr (by simpa using hy0)
    have hL : ((((Ztrunc (abs y)) : Int) : ℝ)) = ((Int.floor y : Int) : ℝ) := by
      simp [Ztrunc, abs_of_nonneg hy0, hy]
    have hR : abs ((((Ztrunc y) : Int) : ℝ)) = ((Int.floor y : Int) : ℝ) := by
      have : (((Ztrunc y) : Int) : ℝ) = ((Int.floor y : Int) : ℝ) := by
        simp [Ztrunc, hy]
      rw [this, abs_of_nonneg (by exact_mod_cast hfloor_nonneg)]
    simp only [Ztrunc_abs_real_val, wp, PostCond.noThrow, Id.run]
    exact hL.trans hR.symm

/-- Away-from-zero rounding: floor for negatives, ceil otherwise -/
noncomputable def Zaway (x : ℝ) : Int :=
  (if x < 0 then ⌊x⌋ else ⌈x⌉)

/-- Floor lower bound: ⌊x⌋ ≤ x -/
theorem Zfloor_lb (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Zfloor x) : Id _)
    ⦃⇓z => ⌜(z : ℝ) ≤ x⌝⦄ := by
  intro _
  unfold Zfloor
  -- Standard floor property: (⌊x⌋ : ℝ) ≤ x
  simpa using (Int.floor_le x)

/-- Floor upper bound: x < ⌊x⌋ + 1 -/
theorem Zfloor_ub (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Zfloor x) : Id _)
    ⦃⇓z => ⌜x < (z : ℝ) + 1⌝⦄ := by
  intro _
  unfold Zfloor
  -- Standard floor upper bound: x < (⌊x⌋ : ℝ) + 1
  simpa using (Int.lt_floor_add_one x)

/-- Floor greatest-lower-bound: if m ≤ x then m ≤ ⌊x⌋ -/
theorem Zfloor_lub (x : ℝ) (m : Int) :
    ⦃⌜(m : ℝ) ≤ x⌝⦄
    (pure (Zfloor x) : Id _)
    ⦃⇓z => ⌜m ≤ z⌝⦄ := by
  intro hm
  unfold Zfloor
  -- Greatest lower bound property for floor: m ≤ ⌊x⌋ ↔ (m : ℝ) ≤ x
  exact (Int.le_floor).mpr hm

/-- Characterization: if m ≤ x < m+1 then ⌊x⌋ = m -/
theorem Zfloor_imp (x : ℝ) (m : Int) :
    ⦃⌜(m : ℝ) ≤ x ∧ x < (m : ℝ) + 1⌝⦄
    (pure (Zfloor x) : Id _)
    ⦃⇓z => ⌜z = m⌝⦄ := by
  intro h
  unfold Zfloor
  -- Characterization of floor by the half-open interval [m, m+1)
  simpa using ((Int.floor_eq_iff).2 h)

/-- Floor of an integer equals itself -/
theorem Zfloor_IZR (m : Int) :
    ⦃⌜True⌝⦄
    (pure (Zfloor (m : ℝ)) : Id _)
    ⦃⇓z => ⌜z = m⌝⦄ := by
  intro _
  unfold Zfloor
  -- Floor of an integer casts back to the same integer
  simpa using (Int.floor_intCast m)

/-- Monotonicity of floor: x ≤ y ⇒ ⌊x⌋ ≤ ⌊y⌋ -/
theorem Zfloor_le (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    (pure (Zfloor x, Zfloor y) : Id _)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro hxy
  -- Reduce the Id/do program and expose floors
  simp [Zfloor]  -- goal becomes: ⌊x⌋ ≤ ⌊y⌋
  -- Use the GLB property of floor with m := ⌊x⌋ and r := y
  -- It suffices to show (⌊x⌋ : ℝ) ≤ y
  refine (Int.le_floor).mpr ?_
  exact (Int.floor_le x).trans hxy

end IntRound

section IntCeil

/-- Ceiling upper bound: x ≤ ⌈x⌉ -/
theorem Zceil_ub (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Zceil x) : Id _)
    ⦃⇓z => ⌜x ≤ (z : ℝ)⌝⦄ := by
  intro _
  unfold Zceil
  -- Standard ceiling property: x ≤ (⌈x⌉ : ℝ)
  have hx : x ≤ (Int.ceil x : ℝ) := by
    -- Cast the integer inequality to ℝ
    exact_mod_cast Int.le_ceil x
  simpa using hx

/-- Ceiling lower-neighborhood: ⌈x⌉ - 1 < x -/
theorem Zceil_lb (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Zceil x) : Id _)
    ⦃⇓z => ⌜(z : ℝ) - 1 < x⌝⦄ := by
  intro _
  unfold Zceil
  -- Using the standard ceiling bound: (⌈x⌉ : ℝ) < x + 1
  -- and rewriting a - 1 < b ↔ a < b + 1
  simpa [sub_lt_iff_lt_add, add_comm] using (Int.ceil_lt_add_one x)

/-- Ceiling least-upper-bound: if x ≤ m then ⌈x⌉ ≤ m -/
theorem Zceil_glb (x : ℝ) (m : Int) :
    ⦃⌜x ≤ (m : ℝ)⌝⦄
    (pure (Zceil x) : Id _)
    ⦃⇓z => ⌜z ≤ m⌝⦄ := by
  intro hx
  unfold Zceil
  -- Least upper bound property for ceiling: ⌈x⌉ ≤ m ↔ x ≤ m
  exact (Int.ceil_le).mpr hx

/-- Characterization: if m - 1 < x ≤ m then ⌈x⌉ = m -/
theorem Zceil_imp (x : ℝ) (m : Int) :
    ⦃⌜(m : ℝ) - 1 < x ∧ x ≤ (m : ℝ)⌝⦄
    (pure (Zceil x) : Id _)
    ⦃⇓z => ⌜z = m⌝⦄ := by
  intro h
  unfold Zceil
  -- Characterization of ceiling by the half-open interval (m-1, m]
  simpa using ((Int.ceil_eq_iff).2 h)

/-- Ceiling of an integer equals itself -/
theorem Zceil_IZR (m : Int) :
    ⦃⌜True⌝⦄
    (pure (Zceil (m : ℝ)) : Id _)
    ⦃⇓z => ⌜z = m⌝⦄ := by
  intro _
  unfold Zceil
  -- Ceiling of an integer casts back to the same integer
  simpa using (Int.ceil_intCast m)

/-- Monotonicity of ceiling: x ≤ y ⇒ ⌈x⌉ ≤ ⌈y⌉ -/
theorem Zceil_le (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    (pure (Zceil x, Zceil y) : Id _)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro hxy
  -- Reduce the Id/do program and expose ceilings
  simp [Zceil]
  -- Use the characterization of ceiling via upper bounds:
  -- ⌈x⌉ ≤ m ↔ x ≤ m. Take m := ⌈y⌉ and show x ≤ ⌈y⌉ using x ≤ y ≤ ⌈y⌉.
  refine (Int.ceil_le).mpr ?_
  exact hxy.trans (Int.le_ceil y)

/-- Non-integral case: if ⌊x⌋ ≠ x then ⌈x⌉ = ⌊x⌋ + 1 -/
theorem Zceil_floor_neq (x : ℝ) :
    ⦃⌜((Zfloor x) : ℝ) ≠ x⌝⦄
    (pure (Zceil x, Zfloor x) : Id _)
    ⦃⇓p => ⌜p.1 = p.2 + 1⌝⦄ := by
  intro hne
  -- Expose the pure ceilings/floors
  simp [Zceil, Zfloor] at *
  -- Let f := ⌊x⌋ and c := ⌈x⌉
  set f := Int.floor x
  set c := Int.ceil x
  -- From floor inequality and the hypothesis (⌊x⌋ : ℝ) ≠ x, get strict inequality
  have hfl : (f : ℝ) ≤ x := by simpa [f] using (Int.floor_le x)
  have hflt : (f : ℝ) < x := lt_of_le_of_ne hfl (by simpa [f] using hne)
  -- And x ≤ c by definition of ceiling
  have hxc : x ≤ (c : ℝ) := by simpa [c] using (Int.le_ceil x)
  -- Hence (f : ℝ) < (c : ℝ), so f < c as integers
  have hfcR : (f : ℝ) < (c : ℝ) := lt_of_lt_of_le hflt hxc
  have hfc : f < c := (Int.cast_lt).mp hfcR
  -- Also, from x < (⌊x⌋ : ℝ) + 1, we get ⌈x⌉ ≤ ⌊x⌋ + 1
  have hceil_le : c ≤ f + 1 := by
    refine (Int.ceil_le).mpr ?_
    have hxlt : x < (f : ℝ) + 1 := by
      -- x < (⌊x⌋ : ℝ) + 1
      simpa [f] using (Int.lt_floor_add_one x)
    -- Strengthen to ≤ and rewrite the cast of (f+1 : ℤ)
    have : x ≤ (f : ℝ) + 1 := le_of_lt hxlt
    simpa [Int.cast_add, Int.cast_one] using this
  -- Combine c ≤ f+1 with f < c ↔ f+1 ≤ c
  have hle' : f + 1 ≤ c := (Int.add_one_le_iff.mpr hfc)
  exact le_antisymm hceil_le hle'

end IntCeil

section IntTrunc

/-- Truncation at integers: Ztrunc (m) = m -/
theorem Ztrunc_IZR (m : Int) :
    ⦃⌜True⌝⦄
    (pure (Ztrunc (m : ℝ)) : Id _)
    ⦃⇓z => ⌜z = m⌝⦄ := by
  intro _; unfold Ztrunc; by_cases h : (m : ℝ) < 0 <;> simp [h]

/-- For nonnegatives: Ztrunc x = ⌊x⌋ -/
theorem Ztrunc_floor (x : ℝ) :
    ⦃⌜0 ≤ x⌝⦄
    (pure (Ztrunc x) : Id _)
    ⦃⇓z => ⌜z = (Zfloor x)⌝⦄ := by
  intro hx
  unfold Ztrunc
  -- Under 0 ≤ x, the truncation takes the floor branch
  have hx_nlt : ¬ x < 0 := not_lt.mpr hx
  simp [Zfloor, hx_nlt]

/-- For nonpositives: Ztrunc x = ⌈x⌉ -/
theorem Ztrunc_ceil (x : ℝ) :
    ⦃⌜x ≤ 0⌝⦄
    (pure (Ztrunc x) : Id _)
    ⦃⇓z => ⌜z = (Zceil x)⌝⦄ := by
  intro hxle
  unfold Ztrunc
  by_cases hlt : x < 0
  · -- Negative case: Ztrunc takes the ceiling branch
    simp [Zceil, hlt]
  · -- Nonnegative case with x ≤ 0 ⇒ x = 0, so floor = ceil = 0
    have hx0 : 0 ≤ x := not_lt.mp hlt
    have hxeq : x = 0 := le_antisymm hxle hx0
    simp [Zceil, hxeq]

/-- Monotonicity of truncation: x ≤ y ⇒ Ztrunc x ≤ Ztrunc y -/
theorem Ztrunc_le (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    (pure (Ztrunc x, Ztrunc y) : Id _)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro hxy
  -- Expose the definitions of Ztrunc and split on the signs of x and y
  by_cases hx : x < 0
  · by_cases hy : y < 0
    · -- Both negative: trunc = ceil; use monotonicity of ceiling
      simp [Ztrunc, hx, hy]
      -- Show: ⌈x⌉ ≤ ⌈y⌉ using x ≤ y ≤ ⌈y⌉
      refine (Int.ceil_le).mpr ?_
      exact hxy.trans (Int.le_ceil y)
    · -- x < 0, 0 ≤ y: need ⌈x⌉ ≤ ⌊y⌋ via  ⌈x⌉ ≤ 0 ≤ ⌊y⌋
      have hy0 : 0 ≤ y := le_of_not_gt hy
      have hxle0 : x ≤ (0 : ℝ) := le_of_lt hx
      -- Coerce 0 to an Int-cast real to match lemmas' expected types
      have hxle0' : x ≤ ((0 : Int) : ℝ) := by simpa using hxle0
      have hceil_le0 : Int.ceil x ≤ 0 := (Int.ceil_le).mpr hxle0'
      have hy0' : ((0 : Int) : ℝ) ≤ y := by simpa using hy0
      have h0_le_floor : (0 : Int) ≤ Int.floor y := (Int.le_floor).mpr hy0'
      -- Combine the bounds and rewrite the goal
      have : Int.ceil x ≤ Int.floor y := le_trans hceil_le0 h0_le_floor
      simpa [Ztrunc, hx, hy] using this
  · by_cases hy : y < 0
    · -- 0 ≤ x and y < 0 contradict x ≤ y; derive False and conclude
      have hx0 : 0 ≤ x := le_of_not_gt hx
      have hy0 : 0 ≤ y := hx0.trans hxy
      have : False := (not_lt.mpr hy0) hy
      cases this
    · -- Both nonnegative: trunc = floor; use monotonicity of floor
      simp [Ztrunc, hx, hy]
      -- Show: ⌊x⌋ ≤ ⌊y⌋ via (⌊x⌋ : ℝ) ≤ y
      refine (Int.le_floor).mpr ?_
      exact (Int.floor_le x).trans hxy

/-- Opposite: Ztrunc (-x) = - Ztrunc x -/
theorem Ztrunc_opp (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Ztrunc (-x), Ztrunc x) : Id _)
    ⦃⇓p => ⌜p.1 = -p.2⌝⦄ := by
  intro _
  -- Expose the definitions: Ztrunc t = if t < 0 then ⌈t⌉ else ⌊t⌋
  simp [Ztrunc]
  -- Goal now: (if 0 < x then ⌈-x⌉ else ⌊-x⌋) = -(if x < 0 then ⌈x⌉ else ⌊x⌋)
  by_cases hxpos : 0 < x
  · -- Left takes the ceil branch; right takes the floor branch
    have hnotlt : ¬ x < 0 := not_lt.mpr (le_of_lt hxpos)
    simp [hxpos, hnotlt, Int.ceil_neg]
  · -- Left takes the floor branch; split on whether x < 0 or x = 0
    have hxle : x ≤ 0 := le_of_not_gt hxpos
    by_cases hxlt : x < 0
    · -- Right takes the ceil branch; use floor_neg
      simp [hxpos, hxlt, Int.floor_neg]
    · -- Then x = 0, so both sides are 0
      have : x = 0 := le_antisymm hxle (le_of_not_gt hxlt)
      subst this
      simp

/-- Absolute value: Ztrunc |x| = |Ztrunc x| -/
theorem Ztrunc_abs (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Ztrunc |x|, Ztrunc x) : Id _)
    ⦃⇓p => ⌜p.1 = Int.natAbs p.2⌝⦄ := by
  intro _
  -- Expose both truncations; for |x| we can simplify the sign test
  -- since |x| ≥ 0 always.
  simp [Ztrunc, not_lt.mpr (abs_nonneg x)]
  -- Goal is now: ⌊|x|⌋ = Int.natAbs (if x < 0 then ⌈x⌉ else ⌊x⌋)
  by_cases hxlt : x < 0
  · -- Negative case: |x| = -x and ⌊-x⌋ = -⌈x⌉.
    have hxle : x ≤ 0 := le_of_lt hxlt
    have habs : |x| = -x := by simpa using (abs_of_neg hxlt)
    have hceil_nonpos : Int.ceil x ≤ 0 := (Int.ceil_le).mpr (by simpa using hxle)
    have hnabs : ((Int.natAbs (Int.ceil x) : Int)) = - (Int.ceil x) :=
      Int.ofNat_natAbs_of_nonpos hceil_nonpos
    have habs_cast : |Int.ceil x| = ((Int.natAbs (Int.ceil x) : Int)) := by
      simpa using (Int.natCast_natAbs (Int.ceil x))
    -- Rewrite both sides accordingly
    simpa [habs, Int.floor_neg, hxlt, hnabs, habs_cast]
  · -- Nonnegative case: x ≥ 0, so ⌊|x|⌋ = ⌊x⌋ and natAbs ⌊x⌋ = ⌊x⌋.
    have hxge : 0 ≤ x := le_of_not_gt hxlt
    have hxabs : |x| = x := by simpa using (abs_of_nonneg hxge)
    -- Floor is nonnegative when x is nonnegative, via the GLB property of floor.
    have hfloor_nonneg : 0 ≤ (Int.floor x : Int) := by
      -- Using: m ≤ ⌊x⌋ ↔ (m : ℝ) ≤ x, with m := 0
      have : (0 : Int) ≤ Int.floor x := (Int.le_floor).mpr (by simpa using hxge)
      simpa using this
    -- Show ⌊|x|⌋ = ⌊x⌋ and |if x<0 then ⌈x⌉ else ⌊x⌋| = |⌊x⌋|
    have hL : ⌊|x|⌋ = ⌊x⌋ := by simpa [hxabs]
    have hR : |if x < 0 then ⌈x⌉ else ⌊x⌋| = |⌊x⌋| := by simpa [hxlt]
    -- Since ⌊x⌋ ≥ 0, we have |⌊x⌋| = ⌊x⌋.
    have hAbsFloor : |Int.floor x| = Int.floor x := abs_of_nonneg hfloor_nonneg
    -- Conclude by rewriting both sides.
    simpa [hL, hR, hAbsFloor]

/-- Lower bound via absolute: if n ≤ |x| then n ≤ |Ztrunc x| -/
theorem Ztrunc_lub (n : Int) (x : ℝ) :
    ⦃⌜(n : ℝ) ≤ |x|⌝⦄
    (pure (Ztrunc x) : Id _)
    ⦃⇓z => ⌜n ≤ Int.natAbs z⌝⦄ := by
  intro h
  unfold Ztrunc
  by_cases hxlt : x < 0
  · -- Negative case: z = ⌈x⌉ and |x| = -x
    -- Reduce the Hoare triple on Id to a pure inequality on ⌈x⌉
    simp [wp, PostCond.noThrow, Id.run, hxlt]
    have hxle : x ≤ 0 := le_of_lt hxlt
    have habs : |x| = -x := by simpa using (abs_of_nonpos hxle)
    -- From (n : ℝ) ≤ |x| = -x, deduce x ≤ -n
    have hx_le_negn : x ≤ (-n : ℝ) := by
      have : (n : ℝ) ≤ -x := by simpa [habs] using h
      have := neg_le_neg this
      simpa using this
    -- Hence ⌈x⌉ ≤ -n by the ceil characterization
    have hceil_le : Int.ceil x ≤ -n := (Int.ceil_le).mpr (by simpa using hx_le_negn)
    -- And ⌈x⌉ ≤ 0, since x ≤ 0
    have hceil_nonpos : Int.ceil x ≤ 0 := (Int.ceil_le).mpr (by simpa using hxle)
    -- From ⌈x⌉ ≤ -n, obtain n ≤ -⌈x⌉
    have hn_le : n ≤ - Int.ceil x := by
      have := neg_le_neg hceil_le
      simpa using this
    -- Conclude: n ≤ |⌈x⌉|
    have : n ≤ |Int.ceil x| := by
      simpa [abs_of_nonpos hceil_nonpos] using hn_le
    exact this
  · -- Nonnegative case: z = ⌊x⌋ and |x| = x
    -- Reduce the Hoare triple on Id to a pure inequality on ⌊x⌋
    simp [wp, PostCond.noThrow, Id.run, hxlt]
    have hxge : 0 ≤ x := le_of_not_gt hxlt
    have habs : |x| = x := by simpa using (abs_of_nonneg hxge)
    -- From (n : ℝ) ≤ x derive n ≤ ⌊x⌋, then compare to natAbs ⌊x⌋
    have h_le_floor : n ≤ Int.floor x := by
      have : (n : ℝ) ≤ x := by simpa [habs] using h
      exact (Int.le_floor).mpr this
    -- ⌊x⌋ ≥ 0
    have hfloor_nonneg : 0 ≤ (Int.floor x : Int) := by
      have : (0 : Int) ≤ Int.floor x := (Int.le_floor).mpr (by simpa using hxge)
      simpa using this
    -- Move to |⌊x⌋| using abs_of_nonneg
    have : n ≤ |Int.floor x| := by
      simpa [abs_of_nonneg hfloor_nonneg] using h_le_floor
    exact this

/-- Basic truncation error bound: |Ztrunc x - x| < 1 -/
theorem abs_Ztrunc_sub_lt_one (x : ℝ) : abs (((Ztrunc x) : ℝ) - x) < 1 := by
  unfold Ztrunc
  by_cases h : x < 0
  · -- Negative case: Ztrunc x = ⌈x⌉
    simp [h]
    -- We have x ≤ ⌈x⌉ < x + 1, so 0 ≤ ⌈x⌉ - x < 1
    have h1 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
    have h2 : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
    have pos : 0 ≤ ⌈x⌉ - x := by linarith [h1]
    have lt : ⌈x⌉ - x < 1 := by linarith [h2]
    rw [abs_of_nonneg pos]
    exact lt
  · -- Non-negative case: Ztrunc x = ⌊x⌋
    simp [h]
    -- We have ⌊x⌋ ≤ x < ⌊x⌋ + 1, so 0 ≤ x - ⌊x⌋ < 1
    have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have h2 : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
    have pos : 0 ≤ x - ⌊x⌋ := by linarith [h1]
    have lt : x - ⌊x⌋ < 1 := by linarith [h2]
    rw [abs_sub_comm, abs_of_nonneg pos]
    exact lt

end IntTrunc

section IntAway

/-- Away-from-zero at integers: Zaway (m) = m -/
theorem Zaway_IZR (m : Int) :
    ⦃⌜True⌝⦄
    (pure (Zaway (m : ℝ)) : Id _)
    ⦃⇓z => ⌜z = m⌝⦄ := by
  intro _; unfold Zaway; by_cases h : (m : ℝ) < 0 <;> simp [h]

/-- For nonnegatives: Zaway x = ⌈x⌉ -/
theorem Zaway_ceil (x : ℝ) :
    ⦃⌜0 ≤ x⌝⦄
    (pure (Zaway x) : Id _)
    ⦃⇓z => ⌜z = (Zceil x)⌝⦄ := by
  intro hx
  unfold Zaway
  -- Under 0 ≤ x, we have ¬ x < 0, so Zaway takes the ceil branch
  have hx_nlt : ¬ x < 0 := not_lt.mpr hx
  simp [Zceil, hx_nlt]

/-- For nonpositives: Zaway x = ⌊x⌋ -/
theorem Zaway_floor (x : ℝ) :
    ⦃⌜x ≤ 0⌝⦄
    (pure (Zaway x) : Id _)
    ⦃⇓z => ⌜z = (Zfloor x)⌝⦄ := by
  intro hxle
  unfold Zaway
  by_cases hlt : x < 0
  · -- Negative case: Zaway takes the floor branch
    simp [Zfloor, hlt]
  · -- Nonnegative case with x ≤ 0 ⇒ x = 0, so ceil = floor
    have hx0 : 0 ≤ x := not_lt.mp hlt
    have hxeq : x = 0 := le_antisymm hxle hx0
    simp [Zfloor, hxeq]

/-- Monotonicity of away rounding: x ≤ y ⇒ Zaway x ≤ Zaway y -/
theorem Zaway_le (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    (pure (Zaway x, Zaway y) : Id _)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro hxy
  -- Expose the definitions of Zaway and split on the signs of x and y
  by_cases hx : x < 0
  · by_cases hy : y < 0
    · -- Both negative: away = floor; use monotonicity of floor
      simp [Zaway, hx, hy]
      refine (Int.le_floor).mpr ?_
      exact (Int.floor_le x).trans hxy
    · -- x < 0, 0 ≤ y: need ⌊x⌋ ≤ ⌈y⌉
      have hy0 : 0 ≤ y := le_of_not_gt hy
      simp [Zaway, hx, hy]
      -- Show: (⌊x⌋ : ℝ) ≤ (⌈y⌉ : ℝ), then cast back to Int inequality
      have hR : ((Int.floor x : ℝ) ≤ (Int.ceil y : ℝ)) := by
        exact (Int.floor_le x) |>.trans (hxy.trans (Int.le_ceil y))
      exact (Int.cast_le).1 hR
  · by_cases hy : y < 0
    · -- 0 ≤ x and y < 0 contradict x ≤ y; derive False
      have hx0 : 0 ≤ x := le_of_not_gt hx
      have hy0 : 0 ≤ y := hx0.trans hxy
      have : False := (not_lt.mpr hy0) hy
      cases this
    · -- Both nonnegative: away = ceil; use monotonicity of ceiling
      simp [Zaway, hx, hy]
      refine (Int.ceil_le).mpr ?_
      exact hxy.trans (Int.le_ceil y)

/-- Opposite: Zaway (-x) = - Zaway x -/
theorem Zaway_opp (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Zaway (-x), Zaway x) : Id _)
    ⦃⇓p => ⌜p.1 = -p.2⌝⦄ := by
  intro _
  -- Expose the definitions: Zaway t = if t < 0 then ⌊t⌋ else ⌈t⌉
  -- Target becomes a pure equality of integers
  simp [Zaway]
  -- Goal: (if 0 < x then ⌊-x⌋ else ⌈-x⌉) = - (if x < 0 then ⌊x⌋ else ⌈x⌉)
  by_cases hxpos : 0 < x
  · -- Then (-x) < 0 and x < 0 is false
    have hL : (if 0 < x then ⌊-x⌋ else ⌈-x⌉) = ⌊-x⌋ := by simp [hxpos]
    have hnlt : ¬ x < 0 := not_lt.mpr (le_of_lt hxpos)
    have hR : (if x < 0 then ⌊x⌋ else ⌈x⌉) = ⌈x⌉ := by simp [hnlt]
    have hfloor_neg : ⌊-x⌋ = -⌈x⌉ := by simpa using (Int.floor_neg (a := x))
    calc
      (if 0 < x then ⌊-x⌋ else ⌈-x⌉)
          = ⌊-x⌋ := hL
      _   = -⌈x⌉ := hfloor_neg
      _   = -(if x < 0 then ⌊x⌋ else ⌈x⌉) := by simpa [hR]
  · -- Not (0 < x): hence x ≤ 0; split further on x < 0
    have hxle : x ≤ 0 := le_of_not_gt hxpos
    by_cases hxlt : x < 0
    · -- Negative x: (-x) ≥ 0, so take ceil on the left; right takes floor
      have hL : (if 0 < x then ⌊-x⌋ else ⌈-x⌉) = ⌈-x⌉ := by simp [hxpos]
      have hR : (if x < 0 then ⌊x⌋ else ⌈x⌉) = ⌊x⌋ := by simp [hxlt]
      have hceil_neg : ⌈-x⌉ = -⌊x⌋ := by simpa using (Int.ceil_neg (a := x))
      calc
        (if 0 < x then ⌊-x⌋ else ⌈-x⌉)
            = ⌈-x⌉ := hL
        _   = -⌊x⌋ := hceil_neg
        _   = -(if x < 0 then ⌊x⌋ else ⌈x⌉) := by simpa [hR]
    · -- x = 0: both sides reduce to 0
      have hx0 : x = 0 := le_antisymm hxle (not_lt.mp hxlt)
      subst hx0
      simp

/-- Absolute value: Zaway |x| = |Zaway x| -/
theorem Zaway_abs (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Zaway |x|, Zaway x) : Id _)
    ⦃⇓p => ⌜p.1 = Int.natAbs p.2⌝⦄ := by
  intro _
  -- Expose both roundings; for |x| we can simplify the sign test
  -- since |x| ≥ 0 always.
  simp [Zaway, not_lt.mpr (abs_nonneg x)]
  -- Goal is now: ⌈|x|⌉ = Int.natAbs (if x < 0 then ⌊x⌋ else ⌈x⌉)
  by_cases hxlt : x < 0
  · -- Negative case: |x| = -x and ⌈-x⌉ = -⌊x⌋.
    have hxle : x ≤ 0 := le_of_lt hxlt
    have habs : |x| = -x := by simpa using (abs_of_nonpos hxle)
    -- Show ⌊x⌋ ≤ 0 via monotonicity of floor (x ≤ 0 ⇒ ⌊x⌋ ≤ ⌊0⌋ = 0)
    have hfloor_nonpos : Int.floor x ≤ 0 := by
      simpa using (Int.floor_le_floor (a := x) (b := 0) hxle)
    -- Conclude by rewriting both sides to -⌊x⌋ and |⌊x⌋|
    have hL : ⌈|x|⌉ = -⌊x⌋ := by simpa [habs] using (Int.ceil_neg (a := x))
    have hR : |if x < 0 then ⌊x⌋ else ⌈x⌉| = |⌊x⌋| := by simpa [hxlt]
    have hAbsFloor : |Int.floor x| = -Int.floor x := abs_of_nonpos hfloor_nonpos
    -- Chain the equalities
    calc
      ⌈|x|⌉ = -⌊x⌋ := hL
      _     = |⌊x⌋| := by simpa [hAbsFloor]
      _     = |if x < 0 then ⌊x⌋ else ⌈x⌉| := hR.symm
  · -- Nonnegative case: x ≥ 0, so ⌈|x|⌉ = ⌈x⌉ and |⌈x⌉| = ⌈x⌉.
    have hxge : 0 ≤ x := le_of_not_gt hxlt
    have hxabs : |x| = x := by simpa using (abs_of_nonneg hxge)
    -- ⌈x⌉ is nonnegative when x ≥ 0
    have hceil_nonneg : 0 ≤ (Int.ceil x : Int) := Int.ceil_nonneg (by simpa using hxge)
    -- Conclude by rewriting both sides.
    simpa [hxabs, hxlt, abs_of_nonneg hceil_nonneg]

end IntAway

section IntDiv

/-- Division at floors for integers: floor((x:ℝ)/(y:ℝ)) = x / y when y ≠ 0. -/
theorem Zfloor_div (x y : Int) :
    ⦃⌜0 < y⌝⦄
    (pure (Zfloor ((x : ℝ) / (y : ℝ))) : Id _)
    ⦃⇓z => ⌜z = x / y⌝⦄ := by
  intro hypos
  unfold Zfloor
  -- We prove ⌊(x : ℝ) / (y : ℝ)⌋ = x / y by the floor characterization
  -- using the Euclidean division x = y * (x / y) + x % y and
  -- bounds 0 ≤ x % y < y when 0 < y.
  have hy_pos : 0 < y := hypos
  -- Remainder bounds in ℤ
  have hr_nonnegZ : (0 : Int) ≤ x % y := Int.emod_nonneg _ (ne_of_gt hy_pos)
  have hr_ltZ : x % y < y := Int.emod_lt_of_pos _ hy_pos
  -- Cast to ℝ
  have hr_nonneg : (0 : ℝ) ≤ ((x % y : Int) : ℝ) := by
    simpa using (Int.cast_mono hr_nonnegZ)
  have hr_lt : ((x % y : Int) : ℝ) < (y : ℝ) := by
    simpa using (Int.cast_strictMono hr_ltZ)
  -- Real identity: (x : ℝ) = (y : ℝ) * (x / y) + (x % y)
  have hx_decomp : (y : ℝ) * ((x / y : Int) : ℝ) + ((x % y : Int) : ℝ) = (x : ℝ) := by
    simpa [Int.cast_add, Int.cast_mul] using
      congrArg (fun t : Int => (t : ℝ)) (Int.mul_ediv_add_emod x y)
  -- Lower bound: (x / y : ℝ) ≤ (x : ℝ) / (y : ℝ)
  have h_lower : ((x / y : Int) : ℝ) ≤ (x : ℝ) / (y : ℝ) := by
    -- Multiply both sides by y > 0 and use the decomposition
    have hyR_pos : 0 < (y : ℝ) := by exact_mod_cast hy_pos
    have hmul_le : ((x / y : Int) : ℝ) * (y : ℝ) ≤ (x : ℝ) := by
      -- (q*y) ≤ (q*y + r) when r ≥ 0
      have : ((x / y : Int) : ℝ) * (y : ℝ) ≤ ((x / y : Int) : ℝ) * (y : ℝ) + ((x % y : Int) : ℝ) :=
        by exact le_add_of_nonneg_right hr_nonneg
      simpa [mul_comm, hx_decomp] using this
    -- Using the equivalence a ≤ b / y ↔ a*y ≤ b for y > 0
    exact (le_div_iff₀ hyR_pos).mpr hmul_le
  -- Upper bound: (x : ℝ) / (y : ℝ) < (x / y : ℝ) + 1
  have h_upper : (x : ℝ) / (y : ℝ) < ((x / y : Int) : ℝ) + 1 := by
    -- Equivalent to x < ((x / y) + 1) * y since y > 0
    have hyR_pos : 0 < (y : ℝ) := by exact_mod_cast hy_pos
    -- From the decomposition x = y*q + r and r < y
    have hx_lt : (x : ℝ) < (((x / y : Int) : ℝ) + 1) * (y : ℝ) := by
      -- rewrite x in terms of q and r, then compare r < y
      have h := add_lt_add_left hr_lt ((y : ℝ) * ((x / y : Int) : ℝ))
      simp only at h
      -- rearrange (y*q + y) = ((q + 1) * y)
      linarith [h]
    -- Transport the inequality through division by positive y
    exact (div_lt_iff₀ hyR_pos).mpr hx_lt
  -- Conclude by the floor characterization
  have hfloor : ⌊(x : ℝ) / (y : ℝ)⌋ = x / y := Int.floor_eq_iff.mpr ⟨h_lower, h_upper⟩
  simp only [hfloor]
  rfl

/-- Coq lemma {coq}`Ztrunc_div`: for integers x and y with y ≠ 0, {coq}`Ztrunc` ({coq}`IZR` x / {coq}`IZR` y) equals the integer quotient; in Lean we state it as {lean}`Ztrunc ((x : ℝ) / (y : ℝ)) = Int.tdiv x y`. -/
theorem Ztrunc_div (x y : Int) :
    ⦃⌜0 ≤ x ∧ 0 < y⌝⦄
    (pure (Ztrunc ((x : ℝ) / (y : ℝ))) : Id _)
    ⦃⇓z => ⌜z = Int.tdiv x y⌝⦄ := by
  intro hxy
  have hx_nonneg : 0 ≤ x := hxy.left
  have hy_pos : 0 < y := hxy.right
  unfold Ztrunc
  -- x ≥ 0: Ztrunc takes the floor branch; use floor characterization and tdiv=ediv
  have hxR_nonneg : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx_nonneg
  have hyR_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy_pos
  have hx_nlt : ¬ ((x : ℝ) / (y : ℝ) < 0) := by
    exact not_lt.mpr (div_nonneg hxR_nonneg (le_of_lt hyR_pos))
  -- Show: ⌊(x:ℝ)/(y:ℝ)⌋ = x / y using the floor characterization at positive y
  have hr_nonnegZ : (0 : Int) ≤ x % y := Int.emod_nonneg _ (ne_of_gt hy_pos)
  have hr_ltZ : x % y < y := Int.emod_lt_of_pos _ hy_pos
  have hr_nonneg : (0 : ℝ) ≤ ((x % y : Int) : ℝ) := by simpa using (Int.cast_mono hr_nonnegZ)
  have hr_lt : ((x % y : Int) : ℝ) < (y : ℝ) := by simpa using (Int.cast_strictMono hr_ltZ)
  have hx_decomp : (y : ℝ) * ((x / y : Int) : ℝ) + ((x % y : Int) : ℝ) = (x : ℝ) := by
    simpa [Int.cast_add, Int.cast_mul] using congrArg (fun t : Int => (t : ℝ)) (Int.mul_ediv_add_emod x y)
  have h_lower : ((x / y : Int) : ℝ) ≤ (x : ℝ) / (y : ℝ) := by
    have hmul_le : ((x / y : Int) : ℝ) * (y : ℝ) ≤ (x : ℝ) := by
      have : ((x / y : Int) : ℝ) * (y : ℝ)
                ≤ ((x / y : Int) : ℝ) * (y : ℝ) + ((x % y : Int) : ℝ) :=
        le_add_of_nonneg_right hr_nonneg
      simpa [mul_comm, hx_decomp] using this
    exact (le_div_iff₀ hyR_pos).mpr hmul_le
  have h_upper : (x : ℝ) / (y : ℝ) < ((x / y : Int) : ℝ) + 1 := by
    have hx_lt : (x : ℝ) < (((x / y : Int) : ℝ) + 1) * (y : ℝ) := by
      have h := add_lt_add_left hr_lt ((y : ℝ) * ((x / y : Int) : ℝ))
      simp only at h
      linarith [h]
    exact (div_lt_iff₀ hyR_pos).mpr hx_lt
  have hf : ⌊(x : ℝ) / (y : ℝ)⌋ = x / y := by
    simp only [Int.floor_eq_iff, h_lower, h_upper, and_self]
  have htdiv : Int.tdiv x y = x / y := by
    simpa using (Int.tdiv_eq_ediv_of_nonneg hx_nonneg : Int.tdiv x y = x / y)
  -- Reduce the program and close the goal
  simpa [hx_nlt, hf, htdiv]

end IntDiv

-- Comparisons against floor/ceil bounds
section CompareIntBounds

/-- Floor/Ceil middle comparison identities -/
noncomputable def Rcompare_floor_ceil_middle_check (x : ℝ) : (Int × Int) :=
  let f := Zfloor x
  let c := Zceil x
  ((Rcompare (f : ℝ) x), (Rcompare x (c : ℝ)))

@[spec]
theorem Rcompare_floor_ceil_middle_spec (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_floor_ceil_middle_check x) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  -- Expand the program to equality of the two comparison codes.
  unfold Rcompare_floor_ceil_middle_check
  -- Reduce both sides to simple if-forms using monotonicity of floor/ceil
  have hcodeL : (Rcompare ((Int.floor x : ℝ)) x) = (if x = (Int.floor x : ℝ) then 0 else -1) := by
    unfold Rcompare
    have hle : (Int.floor x : ℝ) ≤ x := Int.floor_le x
    by_cases heq : (Int.floor x : ℝ) = x
    · -- If equality holds, the "<" branch is impossible.
      have hnotlt : ¬ (Int.floor x : ℝ) < x := by
        -- Reduce to ¬ x < x
        simpa [heq] using (lt_irrefl x : ¬ x < x)
      simp [heq]
    · have hlt : (Int.floor x : ℝ) < x := lt_of_le_of_ne hle heq
      -- In the strict case, the comparison code is -1
      have : (Rcompare ((Int.floor x : ℝ)) x) = -1 := by
        simp [Rcompare, hlt]
      -- And the target if-form also reduces to -1 since x ≠ ⌊x⌋
      have : (Rcompare ((Int.floor x : ℝ)) x)
              = (if x = (Int.floor x : ℝ) then 0 else -1) := by
        simpa [this, if_neg (by simpa [eq_comm] using heq)]
      exact this
  have hcodeR : (Rcompare x ((Int.ceil x : ℝ))) = (if x = (Int.ceil x : ℝ) then 0 else -1) := by
    unfold Rcompare
    have hle : x ≤ (Int.ceil x : ℝ) := Int.le_ceil x
    by_cases heq : x = (Int.ceil x : ℝ)
    · -- Equality case: code is 0
      have hnotlt : ¬ x < (Int.ceil x : ℝ) := by
        -- If x = ⌈x⌉, then x < ⌈x⌉ would imply x < x
        intro hxlt
        have : x < x := lt_of_lt_of_eq hxlt heq.symm
        exact (lt_irrefl _) this
      -- Evaluate the nested-ifs directly using rewrites
      have : (if x < (Int.ceil x : ℝ) then (-1 : Int) else if x = (Int.ceil x : ℝ) then 0 else 1) = 0 := by
        rw [if_neg hnotlt, if_pos heq]
      -- Right-hand side also reduces to 0 under heq
      simpa [if_pos heq] using this
    · -- Strict case: code is -1
      have hlt : x < (Int.ceil x : ℝ) := lt_of_le_of_ne hle heq
      have : (if x < (Int.ceil x : ℝ) then (-1 : Int) else if x = (Int.ceil x : ℝ) then 0 else 1) = -1 := by
        simp [hlt]
      simpa [heq] using this
  -- Floor hits x iff ceil hits x; transport the cases
  have hiff : (x = (Int.floor x : ℝ)) ↔ (x = (Int.ceil x : ℝ)) := by
    constructor
    · intro hfx
      have : Int.ceil x = Int.floor x := by
        have h1 : Int.ceil ((Int.floor x : ℝ)) = Int.floor x := Int.ceil_intCast (Int.floor x)
        have h2 : Int.ceil x = Int.ceil ((Int.floor x : ℝ)) := congrArg Int.ceil hfx
        exact h2.trans h1
      exact by
        have : (Int.ceil x : ℝ) = (Int.floor x : ℝ) := congrArg (fun n : Int => (n : ℝ)) this
        simpa [this] using hfx
    · intro hcx
      have : Int.floor x = Int.ceil x := by
        have h1 : Int.floor ((Int.ceil x : ℝ)) = Int.ceil x := Int.floor_intCast (Int.ceil x)
        have h2 : Int.floor x = Int.floor ((Int.ceil x : ℝ)) := congrArg Int.floor hcx
        exact h2.trans h1
      exact by
        have : (Int.floor x : ℝ) = (Int.ceil x : ℝ) := congrArg (fun n : Int => (n : ℝ)) this
        simpa [this] using hcx
  -- Conclude by rewriting both codes with the if-forms and equating conditions
  have : (Rcompare ((Int.floor x : ℝ)) x) = (Rcompare x ((Int.ceil x : ℝ))) := by
    by_cases hx : x = (Int.floor x : ℝ)
    · -- Equality case: both codes evaluate to 0
      have hx' : x = (Int.ceil x : ℝ) := (hiff.mp hx)
      have hL0 : (Rcompare ((Int.floor x : ℝ)) x) = 0 := by
        rw [hcodeL, if_pos hx]
      have hR0 : (Rcompare x ((Int.ceil x : ℝ))) = 0 := by
        rw [hcodeR, if_pos hx']
      rw [hL0, hR0]
    · -- Strict inequalities case: both codes evaluate to -1
      have hx' : x ≠ (Int.ceil x : ℝ) := by
        intro h; exact hx ((hiff.mpr h))
      have hL1 : (Rcompare ((Int.floor x : ℝ)) x) = -1 := by
        -- Using the simplified code form hcodeL and inequality of x ≠ ⌊x⌋
        have hneq : x ≠ (Int.floor x : ℝ) := by simpa [eq_comm] using hx
        rw [hcodeL, if_neg hneq]
      have hR1 : (Rcompare x ((Int.ceil x : ℝ))) = -1 := by
        -- Using the simplified code form hcodeR and inequality of x ≠ ⌈x⌉
        rw [hcodeR, if_neg hx']
      rw [hL1, hR1]
  -- Finish by reducing the wp-goal to this equality.
  simpa [wp, PostCond.noThrow] using this

/-- Carrier for {coq}`Rcompare_ceil_floor_middle`: checks ceiling/floor comparison codes. -/
noncomputable def Rcompare_ceil_floor_middle_check (x : ℝ) : (Int × Int) :=
  let f := Zfloor x
  let c := Zceil x
  ((Rcompare (c : ℝ) x), (Rcompare x (f : ℝ)))

@[spec]
theorem Rcompare_ceil_floor_middle_spec (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Rcompare_ceil_floor_middle_check x) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rcompare_ceil_floor_middle_check
  -- Reduce the Hoare triple on Id to a pure equality of comparison codes.
  -- Avoid inlining `bind` to keep `simp` from looping; use the wp/noThrow form
  -- as elsewhere in this file.
  simp [wp, PostCond.noThrow, Id.run, Rcompare, pure, Zfloor, Zceil]
  -- Show both comparison codes coincide by splitting on whether x hits its ceil/floor.
  -- Compute each code using monotonicity facts: x ≤ ⌈x⌉ and ⌊x⌋ ≤ x.
  have hL : (Rcompare ((Int.ceil x : ℝ)) x) = (if x = (Int.ceil x : ℝ) then (0 : Int) else 1) := by
    unfold Rcompare
    have hnotlt : ¬ (Int.ceil x : ℝ) < x := not_lt.mpr (Int.le_ceil x)
    -- The equality test is commutative; rewrite to match the statement
    simp [hnotlt, eq_comm]
  have hR : (Rcompare x ((Int.floor x : ℝ))) = (if x = (Int.floor x : ℝ) then (0 : Int) else 1) := by
    unfold Rcompare
    have hnotlt : ¬ x < (Int.floor x : ℝ) := not_lt.mpr (Int.floor_le x)
    simp [hnotlt]
  -- Using standard floor/ceil-on-integers facts, the equality tests are equivalent.
  have hiff : (x = (Int.ceil x : ℝ)) ↔ (x = (Int.floor x : ℝ)) := by
    constructor
    · intro hcx
      -- From x = ⌈x⌉, infer ⌊x⌋ = ⌈x⌉, hence x = ⌊x⌋ as reals.
      have h1 : Int.floor x = Int.floor ((Int.ceil x : ℝ)) := by
        exact congrArg Int.floor hcx
      have h2 : Int.floor ((Int.ceil x : ℝ)) = Int.ceil x := Int.floor_intCast (Int.ceil x)
      have hfloor_eq_ceil : Int.floor x = Int.ceil x := by
        exact h1.trans h2
      -- Conclude x = ⌊x⌋ by transporting hcx through hfloor_eq_ceil
      have hcast : (Int.ceil x : ℝ) = (Int.floor x : ℝ) := by
        exact congrArg (fun n : Int => (n : ℝ)) hfloor_eq_ceil.symm
      exact hcx.trans hcast
    · intro hfx
      -- From x = ⌊x⌋, infer ⌈x⌉ = ⌊x⌋, hence x = ⌈x⌉ as reals.
      have h1 : Int.ceil x = Int.ceil ((Int.floor x : ℝ)) := by
        exact congrArg Int.ceil hfx
      have h2 : Int.ceil ((Int.floor x : ℝ)) = Int.floor x := Int.ceil_intCast (Int.floor x)
      have hceil_eq_floor : Int.ceil x = Int.floor x := by
        exact h1.trans h2
      -- Conclude x = ⌈x⌉ by transporting hfx through hceil_eq_floor
      have hcast : (Int.floor x : ℝ) = (Int.ceil x : ℝ) := by
        exact congrArg (fun n : Int => (n : ℝ)) hceil_eq_floor.symm
      exact hfx.trans hcast
  -- Reduce the Hoare-style goal to a pure equality and discharge it by rewriting and cases.
  -- Goal after simp: prove (Rcompare (↑⌈x⌉) x) = (Rcompare x ↑⌊x⌋).
  -- Rewrite both sides with hL and hR, then case on x = ⌈x⌉.
  have : (Rcompare ((Int.ceil x : ℝ)) x) = (Rcompare x ((Int.floor x : ℝ))) := by
    by_cases hx : x = (Int.ceil x : ℝ)
    · -- Then also x = ⌊x⌋, by hiff
      have hx' : x = (Int.floor x : ℝ) := (hiff.mp hx)
      -- Evaluate each code via hL/hR and the equalities
      have hL0 : (Rcompare ((Int.ceil x : ℝ)) x) = 0 := by
        -- Use hL to rewrite, then evaluate the if using hx
        have : (if x = (Int.ceil x : ℝ) then (0 : Int) else 1) = 0 := if_pos hx
        exact hL ▸ this
      have hR0 : (Rcompare x ((Int.floor x : ℝ))) = 0 := by
        -- Use hR to rewrite, then evaluate the if using hx'
        have : (if x = (Int.floor x : ℝ) then (0 : Int) else 1) = 0 := if_pos hx'
        exact hR ▸ this
      rw [hL0, hR0]
    · -- Otherwise, x < ⌈x⌉ and ⌊x⌋ < x, so both codes reduce to 1
      -- Show each side evaluates to 1 explicitly.
      have hneqL : (Int.ceil x : ℝ) ≠ x := by simpa [eq_comm] using hx
      have hnotltL : ¬ (Int.ceil x : ℝ) < x := not_lt.mpr (Int.le_ceil x)
      have hfxne : x ≠ (Int.floor x : ℝ) := by
        -- If x = ⌊x⌋, then by hiff we would have x = ⌈x⌉, contradicting hx
        intro hxfloor; exact hx ((hiff.mpr hxfloor))
      have hnotltR : ¬ x < (Int.floor x : ℝ) := not_lt.mpr (Int.floor_le x)
      have hL1 : (Rcompare ((Int.ceil x : ℝ)) x) = 1 := by
        -- Not less and not equal ⇒ code = 1
        simp [Rcompare, hnotltL, hneqL]
      have hR1 : (Rcompare x ((Int.floor x : ℝ))) = 1 := by
        -- Not less and not equal ⇒ code = 1
        simp [Rcompare, hnotltR, hfxne]
      rw [hL1, hR1]
  -- Finish by reducing the wp-goal to this equality.
  simpa [wp, PostCond.noThrow] using this

end CompareIntBounds

/-
  Basic results on radix and bpow (Coq Raux.v Section pow)
  In this Lean port, we express bpow via real integer powers (zpow).
-/
section PowBasics

/-- Positivity of the radix as a real number (assuming beta > 1). -/
noncomputable def radix_pos_check (beta : Int) : ℝ :=
  (beta : ℝ)

theorem radix_pos (beta : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (radix_pos_check beta) : Id _)
    ⦃⇓r => ⌜0 < r⌝⦄ := by
  intro hβ
  unfold radix_pos_check
  -- From 1 < beta in ℤ, we get (1 : ℝ) < (beta : ℝ) by monotone casting,
  -- hence 0 < (beta : ℝ) by transitivity with 0 < 1.
  have h1β : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have h01 : (0 : ℝ) < (1 : ℝ) := by exact zero_lt_one
  exact lt_trans h01 h1β

/-- Realization of bpow using real integer powers. -/
noncomputable def bpow (beta e : Int) : ℝ :=
  ((beta : ℝ) ^ e)

/-- Bridge lemma: integer power via reals for positive exponent -/
noncomputable def IZR_Zpower_pos_check (n m : Int) : (ℝ × ℝ) :=
  (((n : ℝ) ^ m, (n : ℝ) ^ m))

theorem IZR_Zpower_pos (n m : Int) :
    ⦃⌜0 < m⌝⦄
    (pure (IZR_Zpower_pos_check n m) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold IZR_Zpower_pos_check
  -- Both components are definitionally equal
  rfl

/-- Bridge: our bpow corresponds to integer power on reals -/
noncomputable def bpow_powerRZ_check (beta e : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ e, (beta : ℝ) ^ e))

theorem bpow_powerRZ (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (bpow_powerRZ_check beta e) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold bpow_powerRZ_check
  -- Both sides are definitionally equal
  rfl

/-- Nonnegativity of bpow -/
theorem bpow_ge_0 (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (bpow beta e) : Id _)
    ⦃⇓v => ⌜0 ≤ v⌝⦄ := by
  intro hβ
  unfold bpow
  -- From 1 < beta in ℤ, we get (1 : ℝ) < (beta : ℝ), hence 0 < (beta : ℝ)
  have h1β : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one h1β
  -- Positive base to any integer power is positive, therefore nonnegative
  exact le_of_lt (zpow_pos hbpos e)

/-- Positivity of bpow -/
theorem bpow_gt_0 (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (bpow beta e) : Id _)
    ⦃⇓v => ⌜0 < v⌝⦄ := by
  intro hβ
  unfold bpow
  -- From 1 < beta in ℤ, get (beta : ℝ) > 1, hence positive
  have h1β : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one h1β
  -- Positive base to any integer power stays positive
  exact zpow_pos hbpos e

/-- Addition law for bpow exponents -/
noncomputable def bpow_plus_check (beta e1 e2 : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ (e1 + e2), ((beta : ℝ) ^ e1) * ((beta : ℝ) ^ e2)))

theorem bpow_plus (beta e1 e2 : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (bpow_plus_check beta e1 e2) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro hβ
  -- Reduce the Hoare triple on Id to a pure equality
  unfold bpow_plus_check
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Goal: (beta : ℝ) ^ (e1 + e2) = (beta : ℝ) ^ e1 * (beta : ℝ) ^ e2
  -- This is `zpow_add₀` for a nonzero base
  have h1β : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one h1β
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  simpa using (zpow_add₀ hbne e1 e2)

/-- Value of bpow at 1 -/
noncomputable def bpow_one_check (beta : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ (1 : Int), (beta : ℝ)))

theorem bpow_1 (beta : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (bpow_one_check beta) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold bpow_one_check
  -- Reduce the Hoare triple on Id to a pure equality and use zpow at 1
  simp [wp, PostCond.noThrow, Id.run, pure, zpow_one]

/-- Carrier for Flocq bpow_plus_1. -/
noncomputable def bpow_plus_1_check (beta e : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ (e + 1), (beta : ℝ) * ((beta : ℝ) ^ e)))

theorem bpow_plus_1 (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (bpow_plus_1_check beta e) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold bpow_plus_1_check
  -- zpow addition specialized to 1; use zpow_add₀ for nonzero base
  have h1β : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast ‹1 < beta›
  have hbpos : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one h1β
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  -- Rearrange to match the target `(beta : ℝ) * (beta : ℝ) ^ e`
  simpa [zpow_one, mul_comm] using (zpow_add₀ hbne e (1 : Int))

/-- Opposite exponent law: bpow (-e) = 1 / bpow e -/
noncomputable def bpow_opp_check (beta e : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ (-e), 1 / ((beta : ℝ) ^ e)))

theorem bpow_opp (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (bpow_opp_check beta e) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold bpow_opp_check
  -- Reduce Hoare triple on Id to a pure equality and use zpow_neg
  simp [wp, PostCond.noThrow, Id.run, pure, zpow_neg, one_div]

/-- Strict monotonicity of bpow in the exponent

    If {lean}`1 < beta` and {lean}`e1 < e2`, then {lean}`(beta : ℝ) ^ e1 < (beta : ℝ) ^ e2`.
-/
noncomputable def bpow_lt_check (beta e1 e2 : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ e1, (beta : ℝ) ^ e2))

theorem bpow_lt (beta e1 e2 : Int) :
    ⦃⌜1 < beta ∧ e1 < e2⌝⦄
    (pure (bpow_lt_check beta e1 e2) : Id _)
    ⦃⇓p => ⌜p.1 < p.2⌝⦄ := by
  intro h
  unfold bpow_lt_check
  rcases h with ⟨hβ, hlt⟩
  -- Transport base inequality to ℝ and apply strict monotonicity of zpow in the exponent
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  exact (zpow_lt_zpow_right₀ hβR hlt)

/-- Converse monotonicity: compare exponents via bpow values

    If {lean}`1 < beta` and {lean}`(beta : ℝ) ^ e1 < (beta : ℝ) ^ e2`, then {lean}`e1 < e2`.
-/
noncomputable def lt_bpow_check (beta e1 e2 : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ e1, (beta : ℝ) ^ e2))

theorem lt_bpow (beta e1 e2 : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ e1) < ((beta : ℝ) ^ e2)⌝⦄
    (pure (lt_bpow_check beta e1 e2) : Id _)
    ⦃⇓_ => ⌜e1 < e2⌝⦄ := by
  intro hlt
  unfold lt_bpow_check
  -- Reduce Hoare triple on Id to a pure goal about the inputs
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Use strict monotonicity of zpow in the exponent for bases > 1
  -- to transport the inequality back to the exponents.
  -- Split the precondition
  rcases hlt with ⟨hβ, hbpowlt⟩
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- Strict monotonicity gives: (beta:ℝ)^e1 < (beta:ℝ)^e2 ↔ e1 < e2
  exact ((zpow_right_strictMono₀ hβR).lt_iff_lt).1 hbpowlt

/-- Monotonicity (≤) of bpow in the exponent -/
noncomputable def bpow_le_check (beta e1 e2 : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ e1, (beta : ℝ) ^ e2))

theorem bpow_le (beta e1 e2 : Int) :
    ⦃⌜1 < beta ∧ e1 ≤ e2⌝⦄
    (pure (bpow_le_check beta e1 e2) : Id _)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro h
  unfold bpow_le_check
  rcases h with ⟨hβ, hle⟩
  -- Transport base inequality to ℝ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- Strict monotonicity in the exponent for bases > 1 yields monotonicity (≤)
  exact ((zpow_right_strictMono₀ hβR).monotone hle)

/-- Converse (≤) direction via bpow values -/
noncomputable def le_bpow_check (beta e1 e2 : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ e1, (beta : ℝ) ^ e2))

theorem le_bpow (beta e1 e2 : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ e1) ≤ ((beta : ℝ) ^ e2)⌝⦄
    (pure (le_bpow_check beta e1 e2) : Id _)
    ⦃⇓_ => ⌜e1 ≤ e2⌝⦄ := by
  intro h
  unfold le_bpow_check
  -- Reduce the Hoare triple on Id to a pure goal
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Split the precondition
  rcases h with ⟨hβ, hle_pow⟩
  -- Transport 1 < beta to ℝ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- Prove by contradiction: assume ¬ e1 ≤ e2, i.e. e2 < e1
  by_contra hle
  have hlt_e : e2 < e1 := lt_of_not_ge hle
  -- Strict monotonicity of zpow in the exponent for bases > 1
  have hlt_pow : (beta : ℝ) ^ e2 < (beta : ℝ) ^ e1 :=
    zpow_lt_zpow_right₀ hβR hlt_e
  -- This contradicts (beta^e1) ≤ (beta^e2)
  have : (beta : ℝ) ^ e2 < (beta : ℝ) ^ e2 := lt_of_lt_of_le hlt_pow hle_pow
  exact (lt_irrefl _ this)

/-- Injectivity of bpow on the exponent -/
noncomputable def bpow_inj_check (beta e1 e2 : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ e1, (beta : ℝ) ^ e2))

theorem bpow_inj (beta e1 e2 : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ e1) = ((beta : ℝ) ^ e2)⌝⦄
    (pure (bpow_inj_check beta e1 e2) : Id _)
    ⦃⇓_ => ⌜e1 = e2⌝⦄ := by
  intro h
  unfold bpow_inj_check
  -- Reduce to a pure goal about the inputs
  simp [wp, PostCond.noThrow, Id.run, pure]
  rcases h with ⟨hβ, heq⟩
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- Strict monotonicity in the exponent implies injectivity
  exact (zpow_right_strictMono₀ hβR).injective heq

/-- Exponential form of bpow via Real.exp and Real.log -/
noncomputable def bpow_exp_check (beta e : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ e, Real.exp ((e : ℝ) * Real.log (beta : ℝ))))

theorem bpow_exp (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (bpow_exp_check beta e) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro hβ
  unfold bpow_exp_check
  -- From 1 < beta (as an integer), we get positivity on ℝ
  have hbposℤ : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  -- Hence every zpow is positive, in particular (beta : ℝ) ^ e > 0
  have hpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR _
  -- Logarithm of a positive zpow scales the exponent
  have hlog_zpow : Real.log ((beta : ℝ) ^ e) = (e : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbposR e
  -- Conclude by exp∘log and the log_zpow identity
  -- (beta : ℝ) ^ e = exp (log ((beta : ℝ) ^ e)) = exp ((e : ℝ) * log beta)
  calc
    (beta : ℝ) ^ e
        = Real.exp (Real.log ((beta : ℝ) ^ e)) := (Real.exp_log hpow_pos).symm
    _ = Real.exp ((e : ℝ) * Real.log (beta : ℝ)) := by simpa [hlog_zpow]

/-- From bpow (e1 - 1) < bpow e2, deduce e1 ≤ e2 -/
noncomputable def bpow_lt_bpow_pair (_beta e1 e2 : Int) : (Int × Int) :=
  (e1, e2)

theorem bpow_lt_bpow (beta e1 e2 : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ (e1 - 1) < (beta : ℝ) ^ e2)⌝⦄
    (pure (bpow_lt_bpow_pair beta e1 e2) : Id _)
    ⦃⇓_ => ⌜e1 ≤ e2⌝⦄ := by
  intro h
  unfold bpow_lt_bpow_pair
  -- Reduce Hoare triple on Id to a pure goal about the inputs
  simp [wp, PostCond.noThrow, Id.run]
  -- From the strict inequality on powers, get a strict inequality on exponents
  rcases h with ⟨hβ, hpowlt⟩
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hlt_exp : e1 - 1 < e2 := ((zpow_right_strictMono₀ hβR).lt_iff_lt).1 hpowlt
  -- Add 1 to both sides and use Int.lt_add_one_iff
  have hlt_add1 : e1 < e2 + 1 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (add_lt_add_right hlt_exp 1)
  exact (Int.lt_add_one_iff).1 hlt_add1

/-- Uniqueness of the integer exponent bounding an absolute value by bpow -/
noncomputable def bpow_unique_pair (_beta : Int) (_x : ℝ) (e1 e2 : Int) : (Int × Int) :=
  (e1, e2)

theorem bpow_unique (beta : Int) (x : ℝ) (e1 e2 : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ (e1 - 1) ≤ |x| ∧ |x| < (beta : ℝ) ^ e1) ∧
               ((beta : ℝ) ^ (e2 - 1) ≤ |x| ∧ |x| < (beta : ℝ) ^ e2)⌝⦄
    (pure (bpow_unique_pair beta x e1 e2) : Id _)
    ⦃⇓_ => ⌜e1 = e2⌝⦄ := by
  intro h
  unfold bpow_unique_pair
  -- Reduce Hoare triple on Id to a pure goal about the inputs
  simp [wp, PostCond.noThrow, Id.run]
  -- Split hypotheses
  rcases h with ⟨hβ, h1, h2⟩
  rcases h1 with ⟨hle1, hlt1⟩
  rcases h2 with ⟨hle2, hlt2⟩
  -- Transport base inequality to ℝ and use strict monotonicity of zpow in the exponent
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- From hle2 ≤ |x| and |x| < bpow e1, deduce bpow (e2-1) < bpow e1 ⇒ e2 ≤ e1
  have hlt21 : (beta : ℝ) ^ (e2 - 1) < (beta : ℝ) ^ e1 := lt_of_le_of_lt hle2 hlt1
  have hlt_exp21 : e2 - 1 < e1 := ((zpow_right_strictMono₀ hβR).lt_iff_lt).1 hlt21
  have hle21 : e2 ≤ e1 := by
    -- e2 - 1 < e1 ⇒ e2 < e1 + 1 ⇒ e2 ≤ e1
    have : e2 < e1 + 1 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (add_lt_add_right hlt_exp21 1)
    exact (Int.lt_add_one_iff.mp this)
  -- Symmetrically, from hle1 ≤ |x| and |x| < bpow e2, deduce e1 ≤ e2
  have hlt12 : (beta : ℝ) ^ (e1 - 1) < (beta : ℝ) ^ e2 := lt_of_le_of_lt hle1 hlt2
  have hlt_exp12 : e1 - 1 < e2 := ((zpow_right_strictMono₀ hβR).lt_iff_lt).1 hlt12
  have hle12 : e1 ≤ e2 := by
    have : e1 < e2 + 1 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (add_lt_add_right hlt_exp12 1)
    exact (Int.lt_add_one_iff.mp this)
  -- Antisymmetry yields equality of exponents
  exact le_antisymm hle12 hle21

/-- Carrier for {coq}`sqrt_bpow`: square-root law on even exponents. -/
noncomputable def sqrt_bpow_check (beta e : Int) : (ℝ × ℝ) :=
  ((Real.sqrt ((beta : ℝ) ^ (2 * e)), (beta : ℝ) ^ e))

/-- Square-root law for even exponents: {lean}`Real.sqrt ((beta : ℝ) ^ (2 * e)) = (beta : ℝ) ^ e` -/
theorem sqrt_bpow (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (sqrt_bpow_check beta e) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold sqrt_bpow_check
  -- From 1 < beta we get (beta : ℝ) > 0 hence nonzero
  have hbposℤ : (0 : Int) < beta := lt_trans (by decide) ‹1 < beta›
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  -- Rewrite the exponent 2*e as e+e and expand using zpow_add₀
  have : Real.sqrt ((beta : ℝ) ^ (2 * e))
      = Real.sqrt (((beta : ℝ) ^ e) * ((beta : ℝ) ^ e)) := by
    simpa [two_mul, zpow_add₀ hbne]
  -- Now use √(x*x) = |x| and that (beta : ℝ) ^ e ≥ 0
  have hnonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt (zpow_pos hbposR e)
  have : Real.sqrt ((beta : ℝ) ^ (2 * e)) = |(beta : ℝ) ^ e| := by
    simpa [this]
      using (Real.sqrt_mul_self_eq_abs ((beta : ℝ) ^ e))
  -- Since (beta : ℝ) ^ e > 0, its absolute value is itself
  simpa [this, abs_of_nonneg hnonneg]

/-- Lower bound: bpow (e/2) ≤ sqrt (bpow e) -/
noncomputable def sqrt_bpow_ge_check (beta e : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ (e / 2), Real.sqrt ((beta : ℝ) ^ e)))

theorem sqrt_bpow_ge (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (sqrt_bpow_ge_check beta e) : Id _)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _
  unfold sqrt_bpow_ge_check
  -- Goal: (beta : ℝ)^(e/2) ≤ √((beta : ℝ)^e)
  -- From 1 < beta we get (beta : ℝ) > 0 hence nonzero
  have hbposℤ : (0 : Int) < beta := lt_trans (by decide) ‹1 < beta›
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  -- Both sides are nonnegative
  have hx_nonneg : 0 ≤ (beta : ℝ) ^ (e / 2) := le_of_lt (zpow_pos hbposR (e / 2))
  have hy_nonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt (zpow_pos hbposR e)
  -- It suffices to show (beta^(e/2))^2 ≤ (beta^e)
  refine (Real.le_sqrt hx_nonneg hy_nonneg).2 ?_;
  -- Rewrite the right-hand side using the division algorithm: e = 2*(e/2) + e % 2
  have hdecomp : 2 * (e / 2) + e % 2 = e := by
    simpa using (Int.mul_ediv_add_emod e 2)
  -- Show: (beta^(e/2))^2 = (beta)^(2*(e/2))
  have hx_sq : ((beta : ℝ) ^ (e / 2)) ^ 2 = (beta : ℝ) ^ (2 * (e / 2)) := by
    -- x^2 = x*x and a^(m+n) = a^m * a^n (for a ≠ 0)
    -- so (beta^(e/2))^2 = beta^(e/2) * beta^(e/2) = beta^(2*(e/2))
    have hx_prod_exp :
        (beta : ℝ) ^ (e / 2) * (beta : ℝ) ^ (e / 2)
          = (beta : ℝ) ^ ((e / 2) + (e / 2)) := by
      simpa using (zpow_add₀ hbne (e / 2) (e / 2)).symm
    simpa [pow_two, two_mul] using hx_prod_exp
  -- Using the decomposition of e, rewrite (beta^e) as (beta)^(2*(e/2)) * (beta)^(e%2)
  have hy_fact : (beta : ℝ) ^ e
      = (beta : ℝ) ^ (2 * (e / 2)) * (beta : ℝ) ^ (e % 2) := by
    calc
      (beta : ℝ) ^ e
          = (beta : ℝ) ^ (2 * (e / 2) + e % 2) := by simpa [hdecomp]
      _ = (beta : ℝ) ^ (2 * (e / 2)) * (beta : ℝ) ^ (e % 2) := by
            simpa [zpow_add₀ hbne]
  -- Since (beta : ℝ) ^ (e % 2) ≥ 1 (as e%2 ∈ {0,1} and beta ≥ 1), we have the desired inequality
  have h_beta_ge_one : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (le_of_lt ‹1 < beta›)
  -- For the remainder r = e % 2 ∈ {0,1}, we have 1 ≤ beta^r
  have honele : (1 : ℝ) ≤ (beta : ℝ) ^ (e % 2) := by
    -- For r = e % 2 ∈ {0,1}
    rcases (Int.emod_two_eq_zero_or_one e) with hr0 | hr1
    · simpa [hr0]
    · simpa [hr1] using h_beta_ge_one
  -- Put everything together: x^2 ≤ x^2 * beta^r = (beta^e)
  have hx2_le : ((beta : ℝ) ^ (e / 2)) ^ 2 ≤ (beta : ℝ) ^ e := by
    have hA_nonneg : 0 ≤ (beta : ℝ) ^ (2 * (e / 2)) := le_of_lt (zpow_pos hbposR _)
    calc
      ((beta : ℝ) ^ (e / 2)) ^ 2
          = (beta : ℝ) ^ (2 * (e / 2)) := hx_sq
      _ ≤ (beta : ℝ) ^ (2 * (e / 2)) * (beta : ℝ) ^ (e % 2) := by
            exact le_mul_of_one_le_right hA_nonneg honele
      _ = (beta : ℝ) ^ e := by simpa [hy_fact]
  exact hx2_le

/-- Bridge: natural-power form equals bpow at Z.ofNat e -/
noncomputable def IZR_Zpower_nat_check (beta : Int) (e : Nat) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ (Int.ofNat e), (beta : ℝ) ^ (Int.ofNat e)))

theorem IZR_Zpower_nat (beta : Int) (e : Nat) :
    ⦃⌜1 < beta⌝⦄
    (pure (IZR_Zpower_nat_check beta e) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold IZR_Zpower_nat_check
  -- The two components are definitionally equal
  rfl

/-- Bridge: for nonnegative exponents, Zpower equals bpow -/
noncomputable def IZR_Zpower_check (beta e : Int) : (ℝ × ℝ) :=
  (((beta : ℝ) ^ e, (beta : ℝ) ^ e))

theorem IZR_Zpower (beta e : Int) :
    ⦃⌜0 ≤ e⌝⦄
    (pure (IZR_Zpower_check beta e) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold IZR_Zpower_check
  -- Both components are definitionally equal
  rfl

end PowBasics

/-
  Limited Principle of Omniscience (LPO) style results from Coquelicot
  (ported from Coq Raux.v). We encode the computational content as
  Id-wrapped options that select a witness when it exists.
 -/
/-!  LPO (limited principle of omniscience) corner -/
section LPO

/-- Carrier for {coq}`LPO_min`: either {given -show}`n : Nat` wrapped in {lean}`some n` with a minimal witness, or {lean}`none` if none exists. -/
noncomputable def LPO_min_choice (P : Nat → Prop) : (Option Nat) :=
  by
    classical
    -- Choose the least witness when it exists
    exact
      if h : ∃ n, P n then
        some (Nat.find h)
      else
        none

/-- Coq (Raux.v) {coq}`LPO_min`. Lean spec uses {lean}`Option` {lean}`Nat` to encode the sum. -/
theorem LPO_min (P : Nat → Prop) :
    ⦃⌜∀ n : Nat, P n ∨ ¬ P n⌝⦄
    (pure (LPO_min_choice P) : Id _)
    ⦃⇓r => ⌜match r with | some n => P n ∧ ∀ i, i < n → ¬ P i | none => ∀ n : Nat, ¬ P n⌝⦄ := by
  intro _
  unfold LPO_min_choice
  classical
  -- Reduce the Hoare triple on Id to a pure goal
  simp [wp, PostCond.noThrow, Id.run]
  -- Split on existence of a witness
  by_cases h : ∃ n, P n
  · -- some witness exists: return the least one via Nat.find
    simp [h]
    refine And.intro ?hP ?hmin
    · -- P (Nat.find h)
      exact Nat.find_spec h
    · -- minimality in the `simp`-rewritten form
      intro i hi
      -- `Nat.lt_find_iff` rewrites `i < Nat.find h` to `∀ m ≤ i, ¬ P m`.
      -- So we can instantiate it at `m = i`.
      exact hi i le_rfl
  · -- no witness exists: return none and prove ∀ n, ¬ P n
    -- From ¬∃ n, P n, derive ∀ n, ¬ P n
    simpa [h] using (not_exists.mp h)

/-- Carrier for {coq}`LPO`: either {given -show}`n : Nat` wrapped in {lean}`some n` with a witness, or {lean}`none` if none exists. -/
noncomputable def LPO_choice (P : Nat → Prop) : (Option Nat) :=
  by
    classical
    -- Choose a witness when it exists (take the least one), otherwise none
    exact
      if h : ∃ n, P n then
        some (Nat.find h)
      else
        none

/-- Coq (Raux.v) {coq}`LPO`. Lean spec: {given -show}`n : Nat` in {lean}`some n` indicates a witness satisfying the predicate; {lean}`none` indicates universal negation. -/
theorem LPO (P : Nat → Prop) :
    ⦃⌜∀ n : Nat, P n ∨ ¬ P n⌝⦄
    (pure (LPO_choice P) : Id _)
    ⦃⇓r => ⌜match r with | some n => P n | none => ∀ n : Nat, ¬ P n⌝⦄ := by
  intro _
  unfold LPO_choice
  classical
  -- Reduce the Hoare triple on Id to a pure goal
  simp [wp, PostCond.noThrow, Id.run]
  -- Split on existence of a witness
  by_cases h : ∃ n, P n
  · -- some witness exists: return the least one via Nat.find
    simp [h]
    -- We must show P (Nat.find h)
    exact Nat.find_spec h
  · -- no witness exists: return none and prove ∀ n, ¬ P n
    -- From ¬∃ n, P n, derive ∀ n, ¬ P n
    simpa [h] using (not_exists.mp h)

/-- Carrier for {coq}`LPO` over integers: either {given -show}`n : Int` in {lean}`some n` with a witness, or {lean}`none`. -/
noncomputable def LPO_Z_choice (P : Int → Prop) : (Option Int) :=
  by
    classical
    -- Choose a witness when it exists (using classical choice), otherwise none
    exact
      if h : ∃ n, P n then
        some (Classical.choose h)
      else
        none

/-- Coq (Raux.v) lemma {coq}`LPO_Z`: for any predicate on integers with decidability, either {given -show}`n : Int` satisfies it or no integer does; the Lean spec encodes this as an option meaning {lean}`some n` indicates satisfaction and {lean}`none` indicates no witness exists. -/
theorem LPO_Z (P : Int → Prop) :
    ⦃⌜∀ n : Int, P n ∨ ¬ P n⌝⦄
    (pure (LPO_Z_choice P) : Id _)
    ⦃⇓r => ⌜match r with | some n => P n | none => ∀ n : Int, ¬ P n⌝⦄ := by
  intro _
  unfold LPO_Z_choice
  classical
  -- Reduce the Hoare triple on Id to a pure goal
  simp [wp, PostCond.noThrow, Id.run]
  -- Split on existence of a witness
  by_cases h : ∃ n, P n
  · -- some witness exists: return one via classical choice
    simp [h]
    -- We must show P (Classical.choose h)
    exact Classical.choose_spec h
  · -- no witness exists: return none and prove ∀ n, ¬ P n
    -- From ¬∃ n, P n, derive ∀ n, ¬ P n
    simpa [h] using (not_exists.mp h)

end LPO

/-
  Magnitude function and related lemmas (Coq Raux.v Section pow)
  We parameterize by an integer base `beta` (≥ 2), analogous to Coq's `radix`.
-/
section Mag

/-- Coq {coq}`mag_prop`: witness record for a magnitude exponent. -/
structure mag_prop (beta : Int) (x : ℝ) : Type where
  /-- The exponent witnessing the magnitude bound. -/
  mag_val : Int
  /-- Coq bound: if x ≠ 0 then β^(e-1) ≤ |x| < β^e. -/
  mag_spec : x ≠ 0 → bpow beta (mag_val - 1) ≤ |x| ∧ |x| < bpow beta mag_val

/-- Coq {coq}`mag_val` projection. -/
abbrev mag_val {beta : Int} {x : ℝ} (m : mag_prop beta x) : Int := m.mag_val

/-- Coq {coq}`Build_mag_prop` constructor alias. -/
abbrev Build_mag_prop {beta : Int} {x : ℝ} (e : Int)
    (h : x ≠ 0 → bpow beta (e - 1) ≤ |x| ∧ |x| < bpow beta e) : mag_prop beta x :=
  { mag_val := e, mag_spec := h }


/-- Magnitude of a real number with respect to base {lit}`beta`.

    In Coq, {coq}`mag` is characterized by {coq}`bpow` bounds: for nonzero {lit}`x`,
    {lit}`bpow (e - 1) ≤ |x| < bpow e`, where {lit}`e = mag x`.
    We model it as a pure computation and wrap it in {lean}`Id` only in specs.

    **IMPORTANT**: We use `⌊log|x|/log β⌋ + 1` (floor + 1) to match Coq's semantics.
    This ensures `mag(β^e) = e + 1`, giving the strict upper bound {lit}`|x| < β^(mag x)`.
    The previous ceiling-based definition gave `mag(β^e) = e`, which created
    boundary cases where {lit}`|x| = β^(mag x)` that don't exist in Coq.
-/
noncomputable def mag (beta : Int) (x : ℝ) : Int :=
  -- Use floor + 1 to match Coq's strict upper bound semantics.
  if x = 0 then 0 else ⌊Real.log (abs x) / Real.log (beta : ℝ)⌋ + 1

/-- Uniqueness of magnitude from bpow bounds.
    With Coq semantics: β^(e-1) ≤ |x| < β^e implies mag(x) = e.
    Note: non-strict lower bound, strict upper bound. -/
theorem mag_unique (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ (e - 1) ≤ |x| ∧ |x| < (beta : ℝ) ^ e)⌝⦄
    (pure (mag beta x) : Id _)
    ⦃⇓m => ⌜m = e⌝⦄ := by
  intro h
  unfold mag
  -- Split hypotheses
  rcases h with ⟨hβ, ⟨hlow, hupp⟩⟩
  -- From 1 < beta (as ℤ), get positivity on ℝ
  have hbposℤ : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hb_gt1R : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- |x| is strictly positive since β^(e-1) > 0 and |x| ≥ β^(e-1)
  have hxpos : 0 < |x| := lt_of_lt_of_le (zpow_pos hbposR (e - 1)) hlow
  have hx0 : x ≠ 0 := abs_pos.mp hxpos
  -- Set L := log |x| / log β to simplify the algebra
  set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hLdef
  -- log β is positive (since β > 1)
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)
    exact this.mpr hb_gt1R
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
    calc
      L * Real.log (beta : ℝ)
          = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by
              simpa [hLdef]
      _   = Real.log (abs x) * Real.log (beta : ℝ) / Real.log (beta : ℝ) := by
              simpa [div_mul_eq_mul_div]
      _   = Real.log (abs x) := by
              simpa [hlogβ_ne] using
                (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
  -- Upper bound: |x| < β^e implies L < e
  have hlog_lt : Real.log (abs x) < Real.log ((beta : ℝ) ^ e) :=
    Real.log_lt_log hxpos hupp
  have hlog_zpow_e : Real.log ((beta : ℝ) ^ e) = (e : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbposR e
  have hL_lt_e : L < (e : ℝ) := by
    have hmul_lt : L * Real.log (beta : ℝ) < (e : ℝ) * Real.log (beta : ℝ) := by
      simpa [hL_mul, hlog_zpow_e] using hlog_lt
    exact (lt_of_mul_lt_mul_right hmul_lt (le_of_lt hlogβ_pos))
  -- From L < e, floor(L) < e, so floor(L) ≤ e - 1
  have hfloor_lt : Int.floor L < e := Int.floor_lt.mpr hL_lt_e
  have hfloor_le_em1 : Int.floor L ≤ e - 1 := by grind
  -- Lower bound: β^(e-1) ≤ |x| implies (e-1) ≤ L
  have hlog_le : Real.log ((beta : ℝ) ^ (e - 1)) ≤ Real.log (abs x) :=
    Real.log_le_log (zpow_pos hbposR (e - 1)) hlow
  have hlog_zpow_em1 : Real.log ((beta : ℝ) ^ (e - 1))
      = (e - 1 : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbposR (e - 1)
  have hexm1_le_L : (e - 1 : ℝ) ≤ L := by
    have hmul_le : (e - 1 : ℝ) * Real.log (beta : ℝ) ≤ L * Real.log (beta : ℝ) := by
      simpa [hL_mul, hlog_zpow_em1] using hlog_le
    exact (le_of_mul_le_mul_right hmul_le hlogβ_pos)
  -- From (e-1) ≤ L, we have e - 1 ≤ floor(L)
  have h_em1_le_floor : e - 1 ≤ Int.floor L := by
    have h : ((e - 1 : Int) : ℝ) ≤ L := by simpa using hexm1_le_L
    exact Int.le_floor.mpr h
  -- Combining: e - 1 ≤ floor(L) ≤ e - 1, so floor(L) = e - 1
  have hfloor_eq : Int.floor L = e - 1 := le_antisymm hfloor_le_em1 h_em1_le_floor
  -- Therefore floor(L) + 1 = e
  have hfloor_add1_eq : Int.floor L + 1 = e := by grind
  -- Finalize: discharge the conditional (x ≠ 0)
  simp only [hx0, ite_false, wp, PostCond.noThrow, Id.run, bind, pure]
  exact hfloor_add1_eq

/-- Opposite preserves magnitude: mag (-x) = mag x -/
theorem mag_opp (beta : Int) (x : ℝ) :
    ⦃⌜1 < beta⌝⦄
    (pure (mag beta (-x), mag beta x) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  simp [mag]

/-- Absolute value preserves magnitude: mag |x| = mag x -/
theorem mag_abs (beta : Int) (x : ℝ) :
    ⦃⌜1 < beta⌝⦄
    (pure (mag beta |x|, mag beta x) : Id _)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  simp [mag]

/-- Uniqueness under positivity: for {given -show}`β`, {given -show}`x : ℝ`, {given -show}`e : ℤ`, if {lean}`0 < x` and `β^(e-1) ≤ x < β^e`, then {lean}`mag β x = e`.

    Note: with Coq semantics (floor+1), bounds are: non-strict lower, strict upper.
-/
theorem mag_unique_pos (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ 0 < x ∧ ((beta : ℝ) ^ (e - 1) ≤ x ∧ x < (beta : ℝ) ^ e)⌝⦄
    (pure (mag beta x) : Id _)
    ⦃⇓m => ⌜m = e⌝⦄ := by
  intro h
  -- Reduce to `mag_unique` by rewriting |x| to x using positivity
  rcases h with ⟨hβ, hxpos, ⟨hlow, hupp⟩⟩
  have hxabs : |x| = x := abs_of_pos hxpos
  -- Assemble the hypothesis required by `mag_unique` (Coq bounds: non-strict lower, strict upper)
  have h' : 1 < beta ∧ ((beta : ℝ) ^ (e - 1) ≤ |x| ∧ |x| < (beta : ℝ) ^ e) := by
    refine ⟨hβ, ?_⟩
    simpa [hxabs] using And.intro hlow hupp
  -- Apply the previously proven uniqueness lemma
  exact (mag_unique beta x e) h'

/-- Bounding |x| by bpow bounds magnitude from above -/
theorem mag_le_abs (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ x ≠ 0 ∧ |x| < (beta : ℝ) ^ e⌝⦄
    (pure (mag beta x) : Id _)
    ⦃⇓m => ⌜m ≤ e⌝⦄ := by
  intro h
  unfold mag
  -- Split hypotheses
  rcases h with ⟨hβ, hx_ne, hx_lt⟩
  -- Base > 1 on ℝ and hence positive
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one hβR
  -- Positivity of |x| from x ≠ 0
  have hx_pos : 0 < |x| := by
    simpa using (abs_pos.mpr hx_ne)
  -- Take logs (strictly increasing on ℝ>0)
  have hlog_lt : Real.log (abs x) < Real.log ((beta : ℝ) ^ e) :=
    Real.log_lt_log hx_pos hx_lt
  -- Express log of the power
  have hlog_pow : Real.log ((beta : ℝ) ^ e) = (e : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbposR e
  -- Denominator log β is positive since β > 1
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    -- Use the specialized equivalence 0 < log β ↔ 1 < β (for β > 0)
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)
    exact this.mpr hβR
  -- Let L := log|x| / log β
  set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hLdef
  -- From log|x| < e * log β and log β > 0, deduce L < e
  have hL_lt : L < e := by
    have : Real.log (abs x) < (e : ℝ) * Real.log (beta : ℝ) := by simpa [hlog_pow] using hlog_lt
    -- a/c < b  ↔  a < b*c for c>0
    have := (div_lt_iff₀ hlogβ_pos).mpr this
    simpa [hLdef] using this
  -- floor L + 1 ≤ e from L < e (since floor L < e implies floor L + 1 ≤ e)
  have hfloor_lt : Int.floor L < e := Int.floor_lt.mpr hL_lt
  have hfloor_add1_le : Int.floor L + 1 ≤ e := Int.lt_iff_add_one_le.mp hfloor_lt
  -- Evaluate the `Id` program and close the goal
  -- Under x ≠ 0 the program returns ⌊L⌋ + 1, so it suffices to use hfloor_add1_le
  simpa [wp, PostCond.noThrow, Id.run, pure, mag, hLdef, hx_ne] using hfloor_add1_le

/-- Monotonicity: if x ≠ 0 and |x| ≤ |y| then mag x ≤ mag y

    Note: with our definition {lean}`mag 0 = 0`, the claim with x = 0 is false in general
    (e.g. for 1 < beta and 0 < |y| < 1, we have mag 0 = 0 > mag y). We therefore
    assume x ≠ 0; this also forces y ≠ 0 under |x| ≤ |y|.
-/
theorem mag_le (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta ∧ x ≠ 0 ∧ |x| ≤ |y|⌝⦄
    (pure (mag beta x, mag beta y) : Id _)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro h
  -- Unpack hypotheses and derive basic positivity facts
  rcases h with ⟨hβ, hx_ne, hxy_abs⟩
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hx_pos : 0 < |x| := by simpa using (abs_pos.mpr hx_ne)
  have hy_pos : 0 < |y| := lt_of_lt_of_le hx_pos hxy_abs
  have hy_ne : y ≠ 0 := by exact (abs_pos.mp hy_pos)
  -- Reduce the program to a pure inequality between ceilings
  -- using the nonzero facts to discharge the conditionals.
  simp [mag, hx_ne, hy_ne, wp, PostCond.noThrow, Id.run]
  -- Normalize the goal to use |x| and |y| explicitly
   -- logβ > 0, so dividing preserves ≤
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
    exact this.mpr hβR

  -- Lx, Ly as shorthands
  set Lx : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hLx
  set Ly : ℝ := Real.log (abs y) / Real.log (beta : ℝ) with hLy

  -- log is monotone on (0, ∞), so log|x| ≤ log|y|
  have hlog_le : Real.log (abs x) ≤ Real.log (abs y) :=
    Real.log_le_log hx_pos hxy_abs

  -- Multiply by logβ and cancel (positive), to get Lx ≤ Ly
  have hLx_mul : Lx * Real.log (beta : ℝ) = Real.log (abs x) := by
    have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    calc
      Lx * Real.log (beta : ℝ)
          = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLx]
      _ = Real.log (abs x) := by
          simpa [hne, div_mul_eq_mul_div] using
            (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
  have hLy_mul : Ly * Real.log (beta : ℝ) = Real.log (abs y) := by
    have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    calc
      Ly * Real.log (beta : ℝ)
          = (Real.log (abs y) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLy]
      _ = Real.log (abs y) := by
          simpa [hne, div_mul_eq_mul_div] using
            (mul_div_cancel' (Real.log (abs y)) (Real.log (beta : ℝ)))

  have hmul_le : Lx * Real.log (beta : ℝ) ≤ Ly * Real.log (beta : ℝ) := by
    simpa [hLx_mul, hLy_mul] using hlog_le
  have hLx_le_Ly : Lx ≤ Ly := (le_of_mul_le_mul_right hmul_le hlogβ_pos)

  -- Floor is monotone, so floor+1 is also monotone
  have hfloor : Int.floor Lx ≤ Int.floor Ly := Int.floor_mono hLx_le_Ly
  have hfloor_add1 : Int.floor Lx + 1 ≤ Int.floor Ly + 1 := by grind

  -- Now collapse the pair produced by `pure` and its projections.
  -- This makes the goal defeq to `⌊Lx⌋ + 1 ≤ ⌊Ly⌋ + 1`.
  simpa [mag, hx_ne, hy_ne, wp, PostCond.noThrow, Id.run, hLx, hLy, pure]
    using hfloor_add1

/-- If {lit}`0 < |x| < bpow e` then {lit}`mag x ≤ e`

    Since {coq}`mag` is defined via {lean}`Int.ceil (log |x| / log beta)`, the bound
    {lit}`|x| < (beta : ℝ) ^ e` implies {lit}`log_beta |x| < e`, hence {lit}`mag x ≤ e`.
    This corrects the direction compared to an earlier draft. -/
theorem lt_mag (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ 0 < |x| ∧ |x| < (beta : ℝ) ^ e⌝⦄
    (pure (mag beta x) : Id _)
    ⦃⇓m => ⌜m ≤ e⌝⦄ := by
  intro h
  -- Strengthen 0 < |x| to x ≠ 0 and reuse `mag_le_abs`.
  have hβ : 1 < beta := h.left
  have hxpos : 0 < |x| := h.right.left
  have hx_ne : x ≠ 0 := by
    intro hx; simpa [hx] using hxpos
  have hxlt : |x| < (beta : ℝ) ^ e := h.right.right
  exact (mag_le_abs beta x e) ⟨hβ, hx_ne, hxlt⟩

/-- Magnitude of bpow e is e + 1 (Coq semantics).
    With floor+1 definition: mag(β^e) = ⌊log(β^e)/log β⌋ + 1 = ⌊e⌋ + 1 = e + 1.
    This matches Coq: β^e ≤ β^e < β^(e+1), so mag(β^e) = e + 1. -/
theorem mag_bpow (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (mag beta ((beta : ℝ) ^ e)) : Id _)
    ⦃⇓m => ⌜m = e + 1⌝⦄ := by
  intro hβ
  -- Reduce the Hoare triple on `Id` to a pure equality
  -- and compute `mag` on the specific input `(β : ℝ)^e`.
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one hβR
  -- Positivity implies non-zeroness for zpow
  have hx_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR e
  have hx_ne : ((beta : ℝ) ^ e) ≠ 0 := ne_of_gt hx_pos
  -- Compute the logarithm of the power
  have hlog_pow : Real.log ((beta : ℝ) ^ e) = (e : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbposR e
  -- log β is positive hence nonzero (since β > 1)
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)
    exact this.mpr hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  -- Quotient simplifies to `e` since `log (β) ≠ 0`
  have hquot : ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) = (e : ℝ) := by
    simpa [hlogβ_ne] using (mul_div_cancel' (e : ℝ) (Real.log (beta : ℝ)))
  -- Now discharge the conditional `x = 0` and apply floor+1
  -- `⌊(e : ℝ)⌋ + 1 = e + 1` for any integer `e`.
  have hfloor_eq : Int.floor (e : ℝ) = e := Int.floor_intCast e
  -- With floor+1 definition, mag(β^e) = ⌊e⌋ + 1 = e + 1
  simp only [wp, PostCond.noThrow, Id.run, pure, mag, hx_ne, ite_false,
         abs_of_nonneg (le_of_lt hx_pos), hlog_pow, hquot, hfloor_eq]
  -- The goal should be e + 1 = e + 1
  rfl

/-- Scaling by bpow shifts magnitude additively -/
theorem mag_mult_bpow (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (mag beta (x * (beta : ℝ) ^ e)) : Id _)
    ⦃⇓m => ⌜∃ k, m = k + e⌝⦄ := by
  intro _
  -- Reduce Hoare triple on Id to a pure existence over the returned value
  simp [wp, PostCond.noThrow, Id.run, pure, mag]
  -- We need to show: ∃ k, (if x * (beta : ℝ) ^ e = 0 then 0
  --                      else ⌈Real.log (|x * (beta : ℝ) ^ e|) / Real.log (beta : ℝ)⌉)
  --                    = k + e
  by_cases hx : x = 0
  · -- If x = 0, the result is 0; pick k = -e
    simp [hx]
    exact ⟨-e, by simp⟩
  · -- If x ≠ 0, rewrite the logarithm and use translation invariance of ceil
    have hx_ne : x ≠ 0 := hx
    -- From 1 < beta, the base is positive, hence its zpow is positive and nonzero
    have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast ‹1 < beta›
    have hbpos : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one hβR
    have hbpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbpos _
    have hbpow_ne : (beta : ℝ) ^ e ≠ 0 := ne_of_gt hbpow_pos
    -- Therefore x * (beta : ℝ) ^ e ≠ 0, so we are in the nonzero branch
    have hxmul_ne : x * (beta : ℝ) ^ e ≠ 0 := mul_ne_zero hx_ne hbpow_ne
    -- The condition (x = 0 ∨ (β : ℝ)^e = 0) is false in this branch
    simp [hx, hbpow_ne]
    -- Rewrite the argument of the ceiling as L + e, where L := log |x| / log β
    set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
    have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
      have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
        Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
      exact this.mpr hβR
    have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    -- |(β : ℝ) ^ e| = (β : ℝ) ^ e since it is positive
    have habs_bpow : |(beta : ℝ) ^ e| = (beta : ℝ) ^ e := by
      simpa using (abs_of_nonneg (le_of_lt hbpow_pos))
    -- log (|x| * |β^e|) = log |x| + e * log β (since |x| > 0 and β^e > 0)
    have hxabs_pos : 0 < |x| := abs_pos.mpr hx_ne
    have hlog_abs_bpow : Real.log (|(beta : ℝ) ^ e|) = Real.log ((beta : ℝ) ^ e) := by
      simpa [abs_of_nonneg (le_of_lt hbpow_pos)]
    have hlog_prod :
        Real.log (|x| * |(beta : ℝ) ^ e|)
          = Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ) := by
      have habs_bpow_pos : 0 < |(beta : ℝ) ^ e| := abs_pos.mpr hbpow_ne
      calc
        Real.log (|x| * |(beta : ℝ) ^ e|)
            = Real.log (|x|) + Real.log (|(beta : ℝ) ^ e|) := by
                simpa using Real.log_mul (ne_of_gt hxabs_pos) (ne_of_gt habs_bpow_pos)
        _ = Real.log (|x|) + Real.log ((beta : ℝ) ^ e) := by
                simpa [hlog_abs_bpow]
        _ = Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ) := by
                simpa using Real.log_zpow hbpos e
    -- Divide by log β and simplify to L + e
    have hdiv :
        Real.log (|x| * |(beta : ℝ) ^ e|) / Real.log (beta : ℝ)
          = L + (e : ℝ) := by
      have hmul_div : ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) = (e : ℝ) := by
        simpa [hlogβ_ne] using (mul_div_cancel' (e : ℝ) (Real.log (beta : ℝ)))
      calc
        _ = (Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) := by
              simp only [hlog_prod]
        _ = Real.log (|x|) / Real.log (beta : ℝ)
              + ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) := by
              ring
        _ = L + (e : ℝ) := by
              simp only [L, hmul_div]
    -- Now use translation invariance of floor by integers
    refine ⟨Int.floor L + 1, ?_⟩
    -- Since beta > 0, |beta| = beta and |beta^e| = beta^e = |beta|^e
    have habs_beta : |(beta : ℝ)| = (beta : ℝ) := abs_of_pos hbpos
    have habs_beta_pow : |(beta : ℝ)| ^ e = |(beta : ℝ) ^ e| := by
      rw [habs_beta, habs_bpow]
    have hfloor_eq : Int.floor
              (Real.log (|x| * |(beta : ℝ) ^ e|) / Real.log (beta : ℝ))
              = Int.floor (L + (e : ℝ)) := by
      simp only [hdiv]
    -- Apply Int.floor_add_intCast: ⌊L + e⌋ = ⌊L⌋ + e
    simp only [habs_beta_pow, hfloor_eq, Int.floor_add_intCast]
    ring

/-- Upper bound: if x ≠ 0 and |x| < bpow e then mag x ≤ e -/
theorem mag_le_bpow (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ x ≠ 0 ∧ |x| < (beta : ℝ) ^ e⌝⦄
    (pure (mag beta x) : Id _)
    ⦃⇓m => ⌜m ≤ e⌝⦄ := by
  -- This is exactly `mag_le_abs`.
  intro h
  exact (mag_le_abs beta x e) h

/-- Lower bound: if bpow (e - 1) ≤ |x| then e ≤ mag x -/
theorem mag_gt_bpow (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ (beta : ℝ) ^ (e - 1) < |x|⌝⦄
    (pure (mag beta x) : Id _)
    ⦃⇓m => ⌜e ≤ m⌝⦄ := by
  intro h
  -- Unpack hypotheses and derive basic positivity facts
  rcases h with ⟨hβ, hlt⟩
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one hβR
  -- From strict lower bound, |x| is positive hence x ≠ 0
  have hx_pos : 0 < |x| := lt_trans (zpow_pos hbpos (e - 1)) hlt
  have hx_ne : x ≠ 0 := by
    exact (abs_pos.mp hx_pos)
  -- Reduce the Hoare triple on Id to a pure inequality about ceilings
  simp [mag, hx_ne, wp, PostCond.noThrow, Id.run]
  -- Let L := log |x| / log β
  set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
  -- log β is positive since β > 1
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
    exact this.mpr hβR
  -- Take logs (strictly increasing on ℝ>0) on the strict lower bound
  have hlog_lt :
      Real.log ((beta : ℝ) ^ (e - 1)) < Real.log (abs x) :=
    Real.log_lt_log (zpow_pos hbpos (e - 1)) hlt
  -- Rewrite log of the power and divide by positive log β to get (e-1) < L
  have hpow_log :
      Real.log ((beta : ℝ) ^ (e - 1))
        = (e - 1 : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbpos (e - 1)
  have hlt_L : (e - 1 : ℝ) < L := by
    have := (lt_div_iff₀ hlogβ_pos).mpr (by simpa [hpow_log] using hlog_lt)
    simpa [L] using this
  -- Use floor property: (e - 1 : ℝ) < L implies e - 1 < floor(L) + 1, i.e., e ≤ floor(L) + 1
  -- Since (e - 1) < L, we have e - 1 ≤ floor(L) (because floor(L) ≥ e-1 when L > e-1)
  have h_em1_le_floor : e - 1 ≤ Int.floor L := by
    have h : ((e - 1 : Int) : ℝ) < L := by simpa using hlt_L
    exact Int.le_floor.mpr (le_of_lt h)
  -- Therefore e ≤ floor(L) + 1
  have hfinal : e ≤ Int.floor L + 1 := by grind
  simpa [wp, PostCond.noThrow, Id.run, pure, mag, hx_ne, L] using hfinal

/-- Combined lower bound: if bpow (e - 1) < |x| then e ≤ mag x -/
theorem mag_ge_bpow (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ (beta : ℝ) ^ (e - 1) < |x|⌝⦄
    (pure (mag beta x) : Id _)
    ⦃⇓m => ⌜e ≤ m⌝⦄ := by
  -- This is exactly `mag_gt_bpow`.
  exact mag_gt_bpow beta x e

/-- If mag x < e then |x| < bpow e -/
noncomputable def abs_val (x : ℝ) : ℝ :=
  |x|

theorem bpow_mag_gt (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ (mag beta x) < e⌝⦄
    (pure (abs_val x) : Id _)
    ⦃⇓v => ⌜v < (beta : ℝ) ^ e⌝⦄ := by
  intro h
  unfold abs_val
  rcases h with ⟨hβ, hlt⟩
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  by_cases hx0 : x = 0
  ·
    -- |x| = 0 and β^e > 0 when β > 0
    have : 0 < (beta : ℝ) ^ e := zpow_pos hbpos e
    simpa [hx0, abs_zero] using this
  ·
    -- Nonzero case
    have hx_pos : 0 < |x| := abs_pos.mpr hx0
    -- L := log|x| / logβ and mag = ⌊L⌋ + 1 (Coq semantics)
    set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hL
    have hmag_run : (mag beta x) = Int.floor L + 1 := by
      simp [mag, hx0, hL]
    have hfloor_add1_lt : Int.floor L + 1 < e := hmag_run ▸ hlt

    -- From ⌊L⌋ + 1 < e get L < e (since L < ⌊L⌋ + 1 by floor property)
    have hL_lt : L < (e : ℝ) := by
      have hL_lt_floor_add1 : L < Int.floor L + 1 := Int.lt_floor_add_one L
      calc L < Int.floor L + 1 := hL_lt_floor_add1
        _ < e := by exact_mod_cast hfloor_add1_lt

    -- log β > 0
    have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
      have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
        Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
      exact this.mpr hβR
    have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos

    -- L * log β = log |x|
    have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
      calc
        L * Real.log (beta : ℝ)
            = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by
                simpa [hL]
        _ = Real.log (abs x) * Real.log (beta : ℝ) / Real.log (beta : ℝ) := by
                simpa [div_mul_eq_mul_div]
        _ = Real.log (abs x) := by
                simpa [hlogβ_ne] using
                  (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))

    -- Turn L < e into log|x| < e * log β
    have hlog_lt : Real.log (abs x) < (e : ℝ) * Real.log (beta : ℝ) := by
      have := mul_lt_mul_of_pos_right hL_lt hlogβ_pos
      simpa [hL_mul, mul_comm, mul_left_comm, mul_assoc] using this

    -- Exponentiate: |x| < exp(e * log β)
    have h_abs_lt : |x| < Real.exp ((e : ℝ) * Real.log (beta : ℝ)) :=
      (Real.log_lt_iff_lt_exp (x := |x|) hx_pos).1 hlog_lt

    -- exp(e * log β) = β^e  (NO `simp/simpa`, just `rw`)
    have h_exp_eq : Real.exp ((e : ℝ) * Real.log (beta : ℝ)) = (beta : ℝ) ^ e := by
      have hlog : (e : ℝ) * Real.log (beta : ℝ) = Real.log ((beta : ℝ) ^ e) := by
        -- log(β^e) = e * log β
        simpa using (Real.log_zpow hbpos e).symm
      have hbpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbpos e
      -- rewrite then close with exp_log
      rw [hlog, Real.exp_log hbpow_pos]

    -- Conclude
    simpa [h_exp_eq] using h_abs_lt

/-- If e ≤ mag x then bpow (e - 1) ≤ |x|

    Note: this requires {lean}`x ≠ 0`. For {lean}`x = 0`, we have {lean}`(mag beta 0) = 0`
    while {lean}`(beta : ℝ) ^ (e - 1) > 0` for all integers {lean}`e` when {lean}`1 < beta`,
    so the statement would be false for {lean}`e ≤ 0`.
-/
theorem bpow_mag_le (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ x ≠ 0 ∧ e ≤ (mag beta x)⌝⦄
    (pure (abs_val x) : Id _)
    ⦃⇓v => ⌜(beta : ℝ) ^ (e - 1) ≤ v⌝⦄ := by
  intro h
  unfold abs_val
  -- Unpack hypotheses and basic facts
  rcases h with ⟨hβ, hx_ne, he_le⟩
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hx_pos : 0 < |x| := abs_pos.mpr hx_ne
  -- Abbreviation L := log |x| / log β
  set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
  -- Evaluate `(mag beta x)` under `x ≠ 0` (Coq semantics: floor+1)
  have hmag_run : (mag beta x) = Int.floor L + 1 := by
    simp [mag, hx_ne, L]
  -- log β > 0
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
    exact this.mpr hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  -- From e ≤ ⌊L⌋ + 1, deduce (e - 1) ≤ ⌊L⌋, hence (e - 1 : ℝ) ≤ L
  have h_em1_le_L : (e - 1 : ℝ) ≤ L := by
    have hstep : e - 1 ≤ Int.floor L := by
      have : e ≤ Int.floor L + 1 := hmag_run ▸ he_le
      grind
    have hfloor_le_L : (Int.floor L : ℝ) ≤ L := Int.floor_le L
    calc (e - 1 : ℝ) ≤ Int.floor L := by exact_mod_cast hstep
      _ ≤ L := hfloor_le_L
  -- Multiply by log β > 0 to obtain a bound on log |x|
  have hlog_le : (e - 1 : ℝ) * Real.log (beta : ℝ) ≤ Real.log (abs x) := by
    have := mul_le_mul_of_nonneg_right h_em1_le_L (le_of_lt hlogβ_pos)
    -- L * log β = log |x|
    have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
      calc
        L * Real.log (beta : ℝ)
            = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by
                simpa [L]
        _ = Real.log (abs x) * Real.log (beta : ℝ) / Real.log (beta : ℝ) := by
                simpa [div_mul_eq_mul_div]
        _ = Real.log (abs x) := by
                simpa [hlogβ_ne] using
                  (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
    simpa [hL_mul, mul_comm] using this
  -- Exponentiate: exp((e-1) * log β) ≤ |x|, and exp/log correspondence gives β^(e-1)
  have h_exp_eq : Real.exp ((e - 1 : ℝ) * Real.log (beta : ℝ)) = (beta : ℝ) ^ (e - 1) := by
    have hbpow_pos : 0 < (beta : ℝ) ^ (e - 1) := zpow_pos hbpos (e - 1)
    have hlog : Real.log ((beta : ℝ) ^ (e - 1)) = ((e - 1 : ℝ) * Real.log (beta : ℝ)) := by
      simpa using (Real.log_zpow hbpos (e - 1))
    have : Real.exp (Real.log ((beta : ℝ) ^ (e - 1))) = (beta : ℝ) ^ (e - 1) :=
      Real.exp_log hbpow_pos
    simpa [hlog] using this
  have hpow_le : (beta : ℝ) ^ (e - 1) ≤ |x| := by
    -- Compare exponentials and then rewrite each side
    have hexp_le :
        Real.exp ((e - 1 : ℝ) * Real.log (beta : ℝ))
          ≤ Real.exp (Real.log (abs x)) := Real.exp_le_exp.mpr hlog_le
    have hleft : Real.exp ((e - 1 : ℝ) * Real.log (beta : ℝ)) ≤ |x| := by
      simpa only [Real.exp_log hx_pos] using hexp_le
    have hleftrw : (beta : ℝ) ^ (e - 1) = Real.exp ((e - 1 : ℝ) * Real.log (beta : ℝ)) :=
      h_exp_eq.symm
    simpa [hleftrw] using hleft
  exact hpow_le

/-- Direct lower bound: for x ≠ 0, beta^(mag x - 1) ≤ |x|.
    This is a corollary of {lean}`bpow_mag_le` with e = mag x. -/
theorem mag_lower_bound (beta : Int) (x : ℝ) :
    ⦃⌜1 < beta ∧ x ≠ 0⌝⦄
    (pure (abs_val x) : Id _)
    ⦃⇓v => ⌜(beta : ℝ) ^ ((mag beta x) - 1) ≤ v⌝⦄ := by
  intro h
  rcases h with ⟨hβ, hx_ne⟩
  -- Apply bpow_mag_le with e = (mag beta x)
  have hpre : 1 < beta ∧ x ≠ 0 ∧ (mag beta x) ≤ (mag beta x) := ⟨hβ, hx_ne, le_refl _⟩
  exact (bpow_mag_le beta x (mag beta x)) hpre

/-- Direct upper bound: for x ≠ 0, |x| < beta^(mag x).
    Note: This is now STRICT (<) with Coq semantics (floor+1 definition).
    This follows from the floor property: L < ⌊L⌋ + 1. -/
theorem mag_upper_bound (beta : Int) (x : ℝ) :
    ⦃⌜1 < beta ∧ x ≠ 0⌝⦄
    (pure (abs_val x) : Id _)
    ⦃⇓v => ⌜v < (beta : ℝ) ^ (mag beta x)⌝⦄ := by
  intro h
  unfold abs_val
  rcases h with ⟨hβ, hx_ne⟩
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hx_pos : 0 < |x| := abs_pos.mpr hx_ne
  -- Abbreviation L := log |x| / log β
  set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
  -- Evaluate `(mag beta x)` under `x ≠ 0` (Coq semantics: floor+1)
  have hmag_run : (mag beta x) = Int.floor L + 1 := by simp [mag, hx_ne, L]
  -- log β > 0
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
    exact this.mpr hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  -- From floor property: L < ⌊L⌋ + 1 (STRICT)
  have hL_lt_floor_add1 : L < Int.floor L + 1 := Int.lt_floor_add_one L
  -- Multiply by log β > 0: L * log β < (⌊L⌋ + 1) * log β
  have hmul : L * Real.log (beta : ℝ) < (Int.floor L + 1 : ℝ) * Real.log (beta : ℝ) :=
    mul_lt_mul_of_pos_right hL_lt_floor_add1 hlogβ_pos
  -- L * log β = log |x|
  have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
    calc L * Real.log (beta : ℝ)
        = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simp [L]
      _ = Real.log (abs x) := by field_simp
  -- log |x| < (⌊L⌋ + 1) * log β
  have hlog_lt : Real.log (abs x) < (Int.floor L + 1 : ℝ) * Real.log (beta : ℝ) := by
    simpa [hL_mul] using hmul
  -- (⌊L⌋ + 1) * log β = log (β^(⌊L⌋ + 1))
  have hlog_pow : (Int.floor L + 1 : ℝ) * Real.log (beta : ℝ) =
      Real.log ((beta : ℝ) ^ (Int.floor L + 1)) := by
    have h := Real.log_zpow (beta : ℝ) (Int.floor L + 1)
    -- h : log (β ^ (⌊L⌋ + 1)) = (⌊L⌋ + 1) * log β
    calc (Int.floor L + 1 : ℝ) * Real.log (beta : ℝ)
        = (↑(Int.floor L + 1) : ℝ) * Real.log (beta : ℝ) := by simp
      _ = Real.log ((beta : ℝ) ^ (Int.floor L + 1)) := h.symm
  -- log |x| < log (β^(⌊L⌋ + 1))
  have hlog_lt' : Real.log (abs x) < Real.log ((beta : ℝ) ^ (Int.floor L + 1)) := by
    calc Real.log (abs x) < (Int.floor L + 1 : ℝ) * Real.log (beta : ℝ) := hlog_lt
      _ = Real.log ((beta : ℝ) ^ (Int.floor L + 1)) := hlog_pow
  -- Exponentiate: |x| < β^(⌊L⌋ + 1)
  have hpow_pos : 0 < (beta : ℝ) ^ (Int.floor L + 1) := zpow_pos hbpos _
  have habs_lt : |x| < (beta : ℝ) ^ (Int.floor L + 1) :=
    (Real.log_lt_log_iff hx_pos hpow_pos).mp hlog_lt'
  -- Conclude: (mag beta x) = Int.floor L + 1
  simp only [wp, PostCond.noThrow, Id.run, pure, PredTrans.pure]
  have hmag : mag beta x = Int.floor L + 1 := hmag_run
  simp_rw [hmag]
  exact habs_lt

/-- If {lit}`1 < beta`, {lit}`0 ≤ e`, and {lit}`|x| < (beta : ℝ)^e`, then {lit}`mag beta x ≤ e`. -/
theorem mag_le_Zpower (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ 0 ≤ e ∧ |x| < ((beta : ℝ) ^ e)⌝⦄
    (pure (mag beta x) : Id _)
    ⦃⇓m => ⌜m ≤ e⌝⦄ := by
  intro h
  rcases h with ⟨hβ, he_nonneg, hlt⟩
  by_cases hx0 : x = 0
  · -- If x = 0, then mag returns 0; conclude 0 ≤ e from the hypothesis
    -- Reduce Hoare triple to a pure inequality
    simp [mag, hx0, wp, PostCond.noThrow, Id.run] at *
    exact he_nonneg
  · -- If x ≠ 0, this is exactly `mag_le_bpow`
    have : (1 < beta ∧ x ≠ 0 ∧ |x| < (beta : ℝ) ^ e) := ⟨hβ, by exact hx0, hlt⟩
    exact (mag_le_bpow beta x e) this

/-- If {lean}`1 < beta` and {lean}`(beta : ℝ)^(e-1) < |x|`, then {lean}`e ≤ mag beta x`. -/
theorem mag_gt_Zpower (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ (e - 1)) < |x|⌝⦄
    (pure (mag beta x) : Id _)
    ⦃⇓m => ⌜e ≤ m⌝⦄ := by
  intro h
  -- This matches `mag_ge_bpow` exactly.
  exact (mag_ge_bpow beta x e) h

/-- Magnitude of a product versus sum of magnitudes -/
theorem mag_mult (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta ∧ x ≠ 0 ∧ y ≠ 0⌝⦄
    (pure (mag beta (x * y), mag beta x, mag beta y) : Id _)
    ⦃⇓t => ⌜t.1 ≤ t.2.1 + t.2.2 ∧ t.2.1 + t.2.2 - 1 ≤ t.1⌝⦄ := by
  intro h
  -- Unpack hypotheses and basic positivity facts
  rcases h with ⟨hβ, hx_ne, hy_ne⟩
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hxy_ne : x * y ≠ 0 := mul_ne_zero hx_ne hy_ne
  have hx_pos : 0 < |x| := abs_pos.mpr hx_ne
  have hy_pos : 0 < |y| := abs_pos.mpr hy_ne
  -- Reduce the `Id` program
  simp [wp, PostCond.noThrow, Id.run, pure, mag, hxy_ne, hx_ne, hy_ne]
  -- Shorthands for logarithmic magnitudes
  set Lx : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hLx
  set Ly : ℝ := Real.log (abs y) / Real.log (beta : ℝ) with hLy
  set Lxy : ℝ := Real.log (abs (x * y)) / Real.log (beta : ℝ) with hLxy
  have hLx' : Lx = Real.log x / Real.log (beta : ℝ) := by
    simpa [log_abs] using hLx
  have hLy' : Ly = Real.log y / Real.log (beta : ℝ) := by
    simpa [log_abs] using hLy
  -- Relation between the logs: log |xy| = log |x| + log |y|
  have habs_mul : abs (x * y) = abs x * abs y := abs_mul x y
  have hLxy_eq : Lxy = Lx + Ly := by
    calc
      Lxy = Real.log (abs (x * y)) / Real.log (beta : ℝ) := rfl
      _ = Real.log (abs x * abs y) / Real.log (beta : ℝ) := by rw [habs_mul]
      _ = (Real.log (abs x) + Real.log (abs y)) / Real.log (beta : ℝ) := by
            have hx_ne' : (abs x) ≠ 0 := ne_of_gt hx_pos
            have hy_ne' : (abs y) ≠ 0 := ne_of_gt hy_pos
            rw [Real.log_mul hx_ne' hy_ne']
      _ = Lx + Ly := by rw [add_div, hLx, hLy]
  have hLxy_abs : Real.log (abs x * abs y) / Real.log (beta : ℝ) = Lxy := by
    simpa [habs_mul] using hLxy.symm
  have hlog_mul_abs : Real.log (abs x * abs y) / Real.log (beta : ℝ) = Lx + Ly := by
    simpa [hLxy_eq] using hLxy_abs
  -- Prove the inequality in terms of Lx/Ly, then rewrite back.
  have h_goal :
      (Int.floor (Lx + Ly) + 1 ≤ Int.floor Lx + 1 + (Int.floor Ly + 1)) ∧
        (Int.floor Lx + 1 + (Int.floor Ly + 1) - 1 ≤ Int.floor (Lx + Ly) + 1) := by
    constructor
    · have h_floor_add : Int.floor (Lx + Ly) ≤ Int.floor Lx + Int.floor Ly + 1 := by
        have := Int.le_floor_add_floor Lx Ly
        linarith
      linarith
    · have h_add_floor : Int.floor Lx + Int.floor Ly ≤ Int.floor (Lx + Ly) :=
        Int.le_floor_add Lx Ly
      linarith
  simpa [hlog_mul_abs, hLx', hLy', add_assoc, add_left_comm, add_comm]
    using h_goal

/-- Magnitude of a sum under positivity and ordering

    Coq (Flocq) version: if 0 < y ≤ x then
      mag x ≤ mag (x + y) ≤ mag x + 1.
-/
theorem mag_plus (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta ∧ 0 < y ∧ y ≤ x⌝⦄
    (pure (mag beta (x + y), mag beta x, mag beta y) : Id _)
    ⦃⇓t => ⌜t.2.1 ≤ t.1 ∧ t.1 ≤ t.2.1 + 1⌝⦄ := by
  intro h
  rcases h with ⟨hβ, hy_pos, hylex⟩
  -- Basic positivity facts
  have hx_pos : 0 < x := lt_of_lt_of_le hy_pos hylex
  have hxy_pos : 0 < x + y := add_pos hx_pos hy_pos
  have hbposR : 0 < (beta : ℝ) := by
    have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
    exact lt_trans zero_lt_one hβR
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    -- 0 < log β ↔ 1 < β (for β > 0)
    have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt (lt_trans zero_lt_one hβR))
    exact this.mpr hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos

  -- Evaluate the Id program: all arguments are positive hence nonzero
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hxy_ne : x + y ≠ 0 := ne_of_gt hxy_pos
  simp [mag, hx_ne, hy_ne, hxy_ne, wp, PostCond.noThrow, Id.run, pure]

  -- Shorthands for logarithmic magnitudes
  set Lx : ℝ := Real.log x / Real.log (beta : ℝ) with hLx
  set Lxy : ℝ := Real.log (x + y) / Real.log (beta : ℝ) with hLxy

  -- Show Lx ≤ Lxy using monotonicity of log and x ≤ x + y
  have hxle : x ≤ x + y := by
    have : 0 ≤ y := le_of_lt hy_pos
    simpa [add_comm] using add_le_add_left this x
  have hlog_le : Real.log x ≤ Real.log (x + y) := Real.log_le_log hx_pos hxle
  have hLx_mul : Lx * Real.log (beta : ℝ) = Real.log x := by
    calc
      Lx * Real.log (beta : ℝ)
          = (Real.log x / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLx]
      _ = Real.log x := by
          simpa [hlogβ_ne, div_mul_eq_mul_div]
            using (mul_div_cancel' (Real.log x) (Real.log (beta : ℝ)))
  have hLxy_mul : Lxy * Real.log (beta : ℝ) = Real.log (x + y) := by
    calc
      Lxy * Real.log (beta : ℝ)
          = (Real.log (x + y) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLxy]
      _ = Real.log (x + y) := by
          simpa [hlogβ_ne, div_mul_eq_mul_div]
            using (mul_div_cancel' (Real.log (x + y)) (Real.log (beta : ℝ)))
  have hLx_le_Lxy : Lx ≤ Lxy := by
    have : Lx * Real.log (beta : ℝ) ≤ Lxy * Real.log (beta : ℝ) := by
      simpa [hLx_mul, hLxy_mul] using hlog_le
    exact (le_of_mul_le_mul_right this hlogβ_pos)

  -- Show Lxy ≤ Lx + 1 via x + y ≤ β * x (since y ≤ x and β ≥ 2)
  have hβ_ge2ℤ : (2 : Int) ≤ beta := by
    -- From 1 < beta we obtain 2 ≤ beta using `add_one_le_iff` on integers
    simpa using (Int.add_one_le_iff.mpr hβ)
  have hβ_ge2 : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hβ_ge2ℤ
  have hxle2 : x + y ≤ 2 * x := by
    have : y ≤ x := hylex
    -- x + y ≤ x + x = 2*x
    simpa [two_mul] using add_le_add_left this x
  have h2x_le_bx : (2 : ℝ) * x ≤ (beta : ℝ) * x := by
    exact mul_le_mul_of_nonneg_right hβ_ge2 (le_of_lt hx_pos)
  have hxy_le_bx : x + y ≤ (beta : ℝ) * x := le_trans hxle2 h2x_le_bx
  have hbx_pos : 0 < (beta : ℝ) * x := mul_pos hbposR hx_pos
  have hlog_le2 : Real.log (x + y) ≤ Real.log ((beta : ℝ) * x) :=
    Real.log_le_log hxy_pos hxy_le_bx
  -- Rewrite both sides and compare after multiplying by log β > 0
  have hlog_prod : Real.log ((beta : ℝ) * x) = Real.log (beta : ℝ) + Real.log x := by
    simpa using Real.log_mul (ne_of_gt hbposR) (ne_of_gt hx_pos)
  have hmul_right : (Lx + 1) * Real.log (beta : ℝ) = Real.log (beta : ℝ) + Real.log x := by
    calc
      (Lx + 1) * Real.log (beta : ℝ)
          = (Real.log x / Real.log (beta : ℝ) + 1) * Real.log (beta : ℝ) := by
              simpa [hLx]
      _ = (Real.log x / Real.log (beta : ℝ)) * Real.log (beta : ℝ)
            + 1 * Real.log (beta : ℝ) := by
              ring
      _ = Real.log (beta : ℝ) + Real.log x := by
            have : (Real.log x / Real.log (beta : ℝ)) * Real.log (beta : ℝ) = Real.log x := by
              simpa [div_mul_eq_mul_div, hlogβ_ne]
                using (mul_div_cancel' (Real.log x) (Real.log (beta : ℝ)))
            simpa [this] using (by simp [add_comm])
  have hmul_le2 : Lxy * Real.log (beta : ℝ) ≤ (Lx + 1) * Real.log (beta : ℝ) := by
    -- Chain with explicit rewrites
    have hx' : Real.log (x + y) ≤ Real.log (beta : ℝ) + Real.log x := by
      simpa [hlog_prod] using hlog_le2
    calc
      Lxy * Real.log (beta : ℝ)
          = Real.log (x + y) := by simpa [hLxy]
                using hLxy_mul
      _ ≤ Real.log (beta : ℝ) + Real.log x := hx'
      _ = (Lx + 1) * Real.log (beta : ℝ) := by
            -- rearrange using `hmul_right` (use the symmetric direction)
            have hsymm : Real.log (beta : ℝ) + Real.log x
                = (Lx + 1) * Real.log (beta : ℝ) := hmul_right.symm
            simpa [hLx] using hsymm
  have hLxy_le : Lxy ≤ Lx + 1 :=
    (le_of_mul_le_mul_right hmul_le2 hlogβ_pos)

  -- Turn inequalities on reals into inequalities on ceilings
  have hceil_lb : Int.ceil Lx ≤ Int.ceil Lxy :=
    (Int.ceil_le).mpr (hLx_le_Lxy.trans (Int.le_ceil _))
  have hceil_ub : Int.ceil Lxy ≤ Int.ceil (Lx + 1) :=
    Int.ceil_mono hLxy_le
  have hceil_add : Int.ceil (Lx + 1 : ℝ) = Int.ceil Lx + 1 := by
    simpa using Int.ceil_add_intCast (a := Lx) (z := 1)

  -- Package the result for the Hoare-style goal on the returned triple
  -- Use floor properties: Lx ≤ Lxy → ⌊Lx⌋ ≤ ⌊Lxy⌋, and Lxy ≤ Lx + 1 → ⌊Lxy⌋ ≤ ⌊Lx⌋ + 1
  constructor
  · -- Lower bound: ⌊Lx⌋ ≤ ⌊Lxy⌋
    exact Int.floor_mono hLx_le_Lxy
  · -- Upper bound: ⌊Lxy⌋ ≤ ⌊Lx⌋ + 1
    have hfloor_add : Int.floor (Lx + 1 : ℝ) = Int.floor Lx + 1 :=
      Int.floor_add_one Lx
    calc Int.floor Lxy ≤ Int.floor (Lx + 1) := Int.floor_mono hLxy_le
      _ = Int.floor Lx + 1 := hfloor_add

/-- Magnitude of a difference under positivity and strict ordering

    Coq (Flocq) version: if 0 < y < x then mag (x − y) ≤ mag x.
-/
theorem mag_minus (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta ∧ 0 < y ∧ y < x⌝⦄
    (pure (mag beta (x - y), mag beta x, mag beta y) : Id _)
    ⦃⇓t => ⌜t.1 ≤ t.2.1⌝⦄ := by
  intro h
  rcases h with ⟨hβ, hy_pos, hyx⟩
  -- Basic positivity facts
  have hx_pos : 0 < x := lt_trans hy_pos hyx
  have hxy_pos : 0 < x - y := sub_pos.mpr hyx
  -- Discharge `Id` / conditionals
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hxy_ne : x - y ≠ 0 := ne_of_gt hxy_pos
  simp [mag, hx_ne, hy_ne, hxy_ne, wp, PostCond.noThrow, Id.run, pure]
  -- Compare via logarithms
  set Lx : ℝ := Real.log x / Real.log (beta : ℝ) with hLx
  set Lxy : ℝ := Real.log (x - y) / Real.log (beta : ℝ) with hLxy
  -- log β > 0 from 1 < β
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt (lt_trans zero_lt_one hβR))
    exact this.mpr hβR
  -- log monotone on (0, ∞): x - y ≤ x ⇒ log (x - y) ≤ log x
  have hle : x - y ≤ x := by
    have : 0 ≤ y := le_of_lt hy_pos
    simpa using sub_le_self x this
  have hlog_le : Real.log (x - y) ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hxy_pos) hle
  -- Cancel the positive factor log β
  have hmul_Lxy : Lxy * Real.log (beta : ℝ) = Real.log (x - y) := by
    have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    calc
      Lxy * Real.log (beta : ℝ)
          = (Real.log (x - y) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLxy]
      _ = Real.log (x - y) := by
            simpa [hne, div_mul_eq_mul_div]
              using (mul_div_cancel' (Real.log (x - y)) (Real.log (beta : ℝ)))
  have hmul_Lx : Lx * Real.log (beta : ℝ) = Real.log x := by
    have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    calc
      Lx * Real.log (beta : ℝ)
          = (Real.log x / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLx]
      _ = Real.log x := by
            simpa [hne, div_mul_eq_mul_div]
              using (mul_div_cancel' (Real.log x) (Real.log (beta : ℝ)))
  have hLxy_le_Lx : Lxy ≤ Lx := by
    have : Lxy * Real.log (beta : ℝ) ≤ Lx * Real.log (beta : ℝ) := by
      simpa [hmul_Lxy, hmul_Lx] using hlog_le
    exact (le_of_mul_le_mul_right this hlogβ_pos)
  -- Floor monotonicity: Lxy ≤ Lx → ⌊Lxy⌋ ≤ ⌊Lx⌋
  exact Int.floor_mono hLxy_le_Lx

/-- Lower bound variant for magnitude of difference (Coq style)

    If 0 < x, 0 < y and mag y ≤ mag x − 2, then mag x − 1 ≤ mag (x − y).
-/
theorem mag_minus_lb (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta ∧ 0 < x ∧ 0 < y ∧ (mag beta y) ≤ (mag beta x) - 2⌝⦄
    (pure (mag beta (x - y), mag beta x, mag beta y) : Id _)
    ⦃⇓t => ⌜t.2.1 - 1 ≤ t.1⌝⦄ := by
  intro h
  rcases h with ⟨hβ, hx_pos, hy_pos, hmy_le⟩
  -- Basic positivity facts and non-zeroness
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
    exact this.mpr hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos

  -- Rewrite the hypothesis on magnitudes using the definition by ceilings
  set Lx : ℝ := Real.log x / Real.log (beta : ℝ) with hLx
  set Ly : ℝ := Real.log y / Real.log (beta : ℝ) with hLy
  -- From hmy_le: ⌊Ly⌋ + 1 ≤ (⌊Lx⌋ + 1) - 2, i.e., ⌊Ly⌋ ≤ ⌊Lx⌋ - 2
  have hfloor_le : Int.floor Ly ≤ Int.floor Lx - 2 := by
    simp only [mag, hx_ne, hy_ne, abs_of_pos hx_pos, abs_of_pos hy_pos, ite_false,
      Id.run, pure, hLx, hLy] at hmy_le
    linarith
  -- Use floor bounds instead of ceiling bounds (avoids issues when Lx is an integer)
  -- From ⌊Ly⌋ ≤ ⌊Lx⌋ - 2, we get ⌈Ly⌉ ≤ ⌊Ly⌋ + 1 ≤ ⌊Lx⌋ - 1
  have hceil_le_floor : Int.ceil Ly ≤ Int.floor Lx - 1 := by
    have h1 : Int.ceil Ly ≤ Int.floor Ly + 1 := Int.ceil_le_floor_add_one Ly
    -- From hfloor_le: ⌊Ly⌋ ≤ ⌊Lx⌋ - 2, so ⌊Ly⌋ + 1 ≤ ⌊Lx⌋ - 1
    linarith

  -- Upper bound on y: y ≤ (beta : ℝ) ^ (Int.ceil Ly)
  have hLy_mul : Ly * Real.log (beta : ℝ) = Real.log y := by
    calc
      Ly * Real.log (beta : ℝ)
          = (Real.log y / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLy]
      _ = Real.log y := by
            simpa [hlogβ_ne, div_mul_eq_mul_div]
              using (mul_div_cancel' (Real.log y) (Real.log (beta : ℝ)))
  have hlogy_le :
    Real.log y ≤ (Int.ceil Ly : ℝ) * Real.log (beta : ℝ) := by
    -- from Ly ≤ ceil Ly, multiply both sides by log β > 0
    have h' :
        Ly * Real.log (beta : ℝ)
          ≤ (Int.ceil Ly : ℝ) * Real.log (beta : ℝ) :=
      mul_le_mul_of_nonneg_right (Int.le_ceil Ly) (le_of_lt hlogβ_pos)
    -- now turn the left side into log y
    simpa [hLy_mul] using h'
  have hy_le_pow_ceil : y ≤ (beta : ℝ) ^ (Int.ceil Ly) := by
    -- Compare logs then exponentiate, and rewrite the RHS
    have hlog_rhs : Real.log ((beta : ℝ) ^ (Int.ceil Ly))
                      = (Int.ceil Ly : ℝ) * Real.log (beta : ℝ) := by
      simpa using (Real.log_zpow hbpos (Int.ceil Ly))
    have hlexp :
        Real.exp (Real.log y)
          ≤ Real.exp ((Int.ceil Ly : ℝ) * Real.log (beta : ℝ)) := by
      exact Real.exp_le_exp.mpr hlogy_le
    have hy_exp : y ≤ Real.exp ((Int.ceil Ly : ℝ) * Real.log (beta : ℝ)) := by
      -- Rewrite exp (log y) to y on the left-hand side
      have hyExpEq : Real.exp (Real.log y) = y := Real.exp_log hy_pos
      simpa [hyExpEq] using hlexp
    have hbpow_pos' : 0 < (beta : ℝ) ^ (Int.ceil Ly) := zpow_pos hbpos _
    have hexp_eq : Real.exp ((Int.ceil Ly : ℝ) * Real.log (beta : ℝ))
                      = (beta : ℝ) ^ (Int.ceil Ly) := by
      simpa [hlog_rhs] using (Real.exp_log hbpow_pos')
    simpa [hexp_eq] using hy_exp

  -- From Int.ceil Ly ≤ Int.floor Lx - 1, obtain y ≤ (beta : ℝ) ^ (Int.floor Lx - 1)
  have hy_le_pow_shift : y ≤ (beta : ℝ) ^ (Int.floor Lx - 1) := by
    have hmono : (beta : ℝ) ^ (Int.ceil Ly) ≤ (beta : ℝ) ^ (Int.floor Lx - 1) := by
      -- Monotonicity of zpow in the exponent for bases > 1
      exact ((zpow_right_strictMono₀ hβR).monotone hceil_le_floor)
    exact le_trans hy_le_pow_ceil hmono

  -- Now reduce the Hoare-style goal to an inequality on ceilings
  simp [mag, hLx, hLy, abs_of_pos hx_pos, abs_of_pos hy_pos]
  -- Goal (after simp): Int.ceil Lx - 1 ≤ Int.ceil ((Real.log (x - y)) / Real.log β)
  -- It suffices to show Lx - 1 ≤ Lxy and use monotonicity of ceil
  set Lxy : ℝ := Real.log (x - y) / Real.log (beta : ℝ) with hLxy

  -- Show x/β ≤ x - y, which implies log(x) - log(β) ≤ log(x - y)
  -- Also record: Lx * log β = log x (used later)
  have hLx_mul : Lx * Real.log (beta : ℝ) = Real.log x := by
    calc
      Lx * Real.log (beta : ℝ)
          = (Real.log x / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLx]
      _ = Real.log x := by
            simpa [hlogβ_ne, div_mul_eq_mul_div]
              using (mul_div_cancel' (Real.log x) (Real.log (beta : ℝ)))
  -- From (⌈Lx⌉ : ℝ) - 1 ≤ Lx and log β > 0, derive β^(⌈Lx⌉ - 1) ≤ x
  have hx_lb : (beta : ℝ) ^ (Int.ceil Lx - 1) ≤ x := by
    have hceil_le_Lx : (Int.ceil Lx : ℝ) - 1 ≤ Lx := by
      have : (Int.ceil Lx : ℝ) - 1 < Lx := by
        have h := Int.ceil_lt_add_one (a := Lx)
        simpa [sub_lt_iff_lt_add, add_comm] using h
      exact le_of_lt this
    have hlog_le' : ((Int.ceil Lx : ℝ) - 1) * Real.log (beta : ℝ) ≤ Real.log x := by
      have := mul_le_mul_of_nonneg_right hceil_le_Lx (le_of_lt hlogβ_pos)
      simpa [hLx_mul] using this
    have hbpow_pos'' : 0 < (beta : ℝ) ^ (Int.ceil Lx - 1) := zpow_pos hbpos _
    have hexp_le :
        Real.exp (((Int.ceil Lx : ℝ) - 1) * Real.log (beta : ℝ))
          ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hlog_le'
    have hleft :
        Real.exp (((Int.ceil Lx : ℝ) - 1) * Real.log (beta : ℝ))
          = (beta : ℝ) ^ (Int.ceil Lx - 1) := by
      have hlog_eq :
          ((Int.ceil Lx : ℝ) - 1) * Real.log (beta : ℝ)
            = Real.log ((beta : ℝ) ^ (Int.ceil Lx - 1)) := by
        simpa using (Real.log_zpow hbpos (Int.ceil Lx - 1))
      have hstep :
          Real.exp (((Int.ceil Lx : ℝ) - 1) * Real.log (beta : ℝ))
            = Real.exp (Real.log ((beta : ℝ) ^ (Int.ceil Lx - 1))) := by
        exact congrArg Real.exp hlog_eq
      calc
        Real.exp (((Int.ceil Lx : ℝ) - 1) * Real.log (beta : ℝ))
            = Real.exp (Real.log ((beta : ℝ) ^ (Int.ceil Lx - 1))) := hstep
        _ = (beta : ℝ) ^ (Int.ceil Lx - 1) := by
            simpa using (Real.exp_log hbpow_pos'')
    have hright : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    simpa [hleft, hright] using hexp_le

  -- Use floor-based lower bound: β^⌊Lx⌋ ≤ x
  have hx_lb_floor : (beta : ℝ) ^ Int.floor Lx ≤ x := by
    have hfloor_le_Lx : (Int.floor Lx : ℝ) ≤ Lx := Int.floor_le Lx
    have hlog_le' : (Int.floor Lx : ℝ) * Real.log (beta : ℝ) ≤ Real.log x := by
      have := mul_le_mul_of_nonneg_right hfloor_le_Lx (le_of_lt hlogβ_pos)
      simpa [hLx_mul] using this
    have hbpow_pos'' : 0 < (beta : ℝ) ^ Int.floor Lx := zpow_pos hbpos _
    have hexp_le :
        Real.exp ((Int.floor Lx : ℝ) * Real.log (beta : ℝ))
          ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hlog_le'
    have hleft : Real.exp ((Int.floor Lx : ℝ) * Real.log (beta : ℝ)) = (beta : ℝ) ^ Int.floor Lx := by
      have hlog_eq : (Int.floor Lx : ℝ) * Real.log (beta : ℝ) = Real.log ((beta : ℝ) ^ Int.floor Lx) := by
        simpa using (Real.log_zpow hbpos (Int.floor Lx))
      calc
        Real.exp ((Int.floor Lx : ℝ) * Real.log (beta : ℝ))
            = Real.exp (Real.log ((beta : ℝ) ^ Int.floor Lx)) := by rw [hlog_eq]
        _ = (beta : ℝ) ^ Int.floor Lx := Real.exp_log hbpow_pos''
    have hright : Real.exp (Real.log x) = x := Real.exp_log hx_pos
    simpa [hleft, hright] using hexp_le

  have hy_le_x_over_beta : y ≤ x / (beta : ℝ) := by
    -- From y ≤ β^(⌊Lx⌋ - 1) and x ≥ β^⌊Lx⌋, derive x/β ≥ β^(⌊Lx⌋-1) ≥ y
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
    have hx_div_ge : x / (beta : ℝ) ≥ (beta : ℝ) ^ (Int.floor Lx - 1) := by
      -- From x ≥ β^⌊Lx⌋ = β * β^(⌊Lx⌋-1), divide by β
      have hpow_split : (beta : ℝ) ^ Int.floor Lx = (beta : ℝ) * (beta : ℝ) ^ (Int.floor Lx - 1) := by
        have heq : Int.floor Lx = 1 + (Int.floor Lx - 1) := by ring
        conv_lhs => rw [heq, zpow_add₀ hbne, zpow_one]
      have hgoal : (beta : ℝ) ^ (Int.floor Lx - 1) * (beta : ℝ) ≤ x := by
        rw [mul_comm, hpow_split.symm]
        exact hx_lb_floor
      exact (le_div_iff₀ hbpos).mpr hgoal
    -- Combine y ≤ β^(⌊Lx⌋-1) ≤ x/β
    exact le_trans hy_le_pow_shift hx_div_ge

  have hlog_lb : Real.log (x / (beta : ℝ)) ≤ Real.log (x - y) := by
    -- We show x/β ≤ x - y by two steps:
    -- (i) x/β ≤ x - x/β using β ≥ 2 and x > 0;
    -- (ii) x - x/β ≤ x - y since y ≤ x/β.
    have hbge2Z : (2 : Int) ≤ beta := by
      -- from 1 < beta ⇒ 2 ≤ beta
      exact (Int.add_one_le_iff.mpr hβ)
    have hbge2R : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hbge2Z
    have hx_div_nonneg : 0 ≤ x / (beta : ℝ) := div_nonneg (le_of_lt hx_pos) (le_of_lt hbpos)
    have hxdiv_two_le : (2 : ℝ) * (x / (beta : ℝ)) ≤ (beta : ℝ) * (x / (beta : ℝ)) :=
      mul_le_mul_of_nonneg_right hbge2R hx_div_nonneg
    have hxdiv_le : x / (beta : ℝ) ≤ x - x / (beta : ℝ) := by
      -- Show (x/β) + (x/β) ≤ x by comparing x*(2/β) ≤ x
      have hbge2R : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hβ)
      have hfrac_le_one : (2 : ℝ) / (beta : ℝ) ≤ 1 :=
        (div_le_iff₀ hbpos).mpr (by simpa using hbge2R)
      have hmul_le : x * ((2 : ℝ) / (beta : ℝ)) ≤ x * 1 :=
        mul_le_mul_of_nonneg_left hfrac_le_one (le_of_lt hx_pos)
      have htwo_mul_le : (2 : ℝ) * (x / (beta : ℝ)) ≤ x := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, one_mul]
          using hmul_le
      have hxdiv_sum_le : x / (beta : ℝ) + x / (beta : ℝ) ≤ x := by
        simpa [two_mul] using htwo_mul_le
      exact (le_sub_iff_add_le).mpr hxdiv_sum_le
    have hx_sub_mono : x - x / (beta : ℝ) ≤ x - y := by
      -- From y ≤ x/β, subtract from x on both sides
      exact sub_le_sub_left hy_le_x_over_beta x
    have hchain : x / (beta : ℝ) ≤ x - y := le_trans hxdiv_le hx_sub_mono
    have hx_div_pos : 0 < x / (beta : ℝ) := by exact div_pos hx_pos hbpos
    exact Real.log_le_log hx_div_pos hchain

  -- From x/β ≤ x - y and x/β > 0, deduce x - y > 0 for later rewrites
  have hxy_pos : 0 < x - y := by
    -- Since 1 < β and 0 < x, we have x/β < x
    have hx_div_lt : x / (beta : ℝ) < x := by
      have hx_mul_lt : x < (beta : ℝ) * x := by
        have := mul_lt_mul_of_pos_left hβR hx_pos
        simpa [one_mul, mul_comm] using this
      -- Need the RHS as x * β for `div_lt_iff₀`; rewrite with commutativity
      have hx_mul_lt' : x < x * (beta : ℝ) := by simpa [mul_comm] using hx_mul_lt
      exact (div_lt_iff₀ hbpos).mpr hx_mul_lt'
    -- And y ≤ x/β, so y < x; hence 0 < x - y
    have hy_lt_x : y < x := lt_of_le_of_lt hy_le_x_over_beta hx_div_lt
    exact sub_pos.mpr hy_lt_x
  have hxy_ne : x - y ≠ 0 := ne_of_gt hxy_pos

  -- Now reduce the Hoare-style goal to an inequality on ceilings
  simp [mag, hx_ne, hy_ne, hxy_ne, hLx, hLy, abs_of_pos hx_pos, abs_of_pos hy_pos]

  -- Translate to Lx - 1 ≤ Lxy
  have hLx_sub_le : Lx - 1 ≤ Lxy := by
    -- Multiply both sides by log β > 0 and use algebra
    -- Lx * logβ = log x, Lxy * logβ = log (x - y)
    have hlog_ineq : Real.log x - Real.log (beta : ℝ)
                      ≤ Real.log (x - y) := by
      -- log(x) - log(β) = log(x/β)
      have hlog_div : Real.log (x / (beta : ℝ))
                        = Real.log x - Real.log (beta : ℝ) := by
        have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
        simpa using Real.log_div (ne_of_gt hx_pos) hbne
      simpa [hlog_div] using hlog_lb
    -- Compute Lxy * log β = log (x - y)
    have hLxy_mul : Lxy * Real.log (beta : ℝ) = Real.log (x - y) := by
      have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
      calc
        Lxy * Real.log (beta : ℝ)
            = (Real.log (x - y) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by
                simpa [hLxy]
        _ = Real.log (x - y) := by
                simpa [hne, div_mul_eq_mul_div]
                  using (mul_div_cancel' (Real.log (x - y)) (Real.log (beta : ℝ)))
    have hmul_le : (Lx - 1) * Real.log (beta : ℝ) ≤ Lxy * Real.log (beta : ℝ) := by
      have hleft : (Lx - 1) * Real.log (beta : ℝ)
                      = Real.log x - Real.log (beta : ℝ) := by
        calc
          (Lx - 1) * Real.log (beta : ℝ)
              = Lx * Real.log (beta : ℝ) - 1 * Real.log (beta : ℝ) := by ring
          _   = Real.log x - Real.log (beta : ℝ) := by
                simpa [hLx_mul, one_mul]
      have hright : Lxy * Real.log (beta : ℝ) = Real.log (x - y) := hLxy_mul
      simpa [hleft, hright] using hlog_ineq
    exact (le_of_mul_le_mul_right hmul_le hlogβ_pos)

  -- From Lx - 1 ≤ Lxy, we get Lx ≤ Lxy + 1, hence ⌊Lx⌋ ≤ ⌊Lxy + 1⌋ = ⌊Lxy⌋ + 1
  have hLx_le : Lx ≤ Lxy + 1 := by linarith
  have hfloor_le' : Int.floor Lx ≤ Int.floor (Lxy + 1) := Int.floor_mono hLx_le
  have hfloor_add : Int.floor (Lxy + 1) = Int.floor Lxy + 1 := Int.floor_add_one Lxy
  simp only [hLx, hfloor_add] at hfloor_le' ⊢
  exact hfloor_le'

/-- Lower bound on the magnitude of a sum

    Coq (Flocq) version: if x ≠ 0 and mag y ≤ mag x − 2, then
    mag x − 1 ≤ mag (x + y).
-/
theorem mag_plus_ge (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta ∧ x ≠ 0 ∧ (mag beta y) ≤ (mag beta x) - 2⌝⦄
    (pure (mag beta (x + y)) : Id _)
    ⦃⇓m => ⌜(mag beta x) - 1 ≤ m⌝⦄ := by
  intro h
  rcases h with ⟨hβ, hx_ne, hmy_le⟩
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hβR_ge : (1 : ℝ) ≤ (beta : ℝ) := le_of_lt hβR
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := Real.log_pos hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos

  -- Case split on y = 0
  by_cases hy_zero : y = 0
  · -- If y = 0, then x + y = x and result is trivial
    simp only [hy_zero, add_zero, wp, PostCond.noThrow, PredTrans.pure, mag, hx_ne, ite_false,
      Id.run, pure]
    show (Int.floor (Real.log |x| / Real.log ↑beta) + 1 - 1 ≤
        Int.floor (Real.log |x| / Real.log ↑beta) + 1)
    grind

  -- y ≠ 0 case
  have hx_abs_pos : 0 < |x| := abs_pos.mpr hx_ne
  have hy_abs_pos : 0 < |y| := abs_pos.mpr hy_zero

  -- Set up log expressions early
  set mx := Int.floor (Real.log |x| / Real.log (beta : ℝ)) + 1 with hmx_def
  set my := Int.floor (Real.log |y| / Real.log (beta : ℝ)) + 1 with hmy_def

  -- mag x = mx, mag y = my
  have hmag_x_eq : (mag beta x) = mx := by
    simp only [mag, hx_ne, ite_false, Id.run, pure, hmx_def]
  have hmag_y_eq : (mag beta y) = my := by
    simp only [mag, hy_zero, ite_false, Id.run, pure, hmy_def]

  -- From hypothesis: my ≤ mx - 2
  have hmy_le' : my ≤ mx - 2 := by
    simp only [hmag_x_eq, hmag_y_eq] at hmy_le
    exact hmy_le

  -- Direct bound: β^(mx - 1) ≤ |x| (from floor property)
  have hx_lb : (beta : ℝ) ^ (mx - 1) ≤ |x| := by
    have hfloor_le : (Int.floor (Real.log |x| / Real.log (beta : ℝ)) : ℝ) ≤
        Real.log |x| / Real.log (beta : ℝ) := Int.floor_le _
    have hmul : (mx - 1 : ℤ) = Int.floor (Real.log |x| / Real.log (beta : ℝ)) := by grind
    have hlog_ge : (mx - 1 : ℤ) * Real.log (beta : ℝ) ≤ Real.log |x| := by
      rw [hmul]
      have := mul_le_mul_of_nonneg_right hfloor_le (le_of_lt hlogβ_pos)
      field_simp at this ⊢
      exact this
    have hpow_log : Real.log ((beta : ℝ) ^ (mx - 1)) = (mx - 1 : ℤ) * Real.log (beta : ℝ) := by
      rw [Real.log_zpow]
    rw [← hpow_log] at hlog_ge
    have hpow_pos : 0 < (beta : ℝ) ^ (mx - 1) := zpow_pos hbpos _
    rw [← Real.log_le_log_iff hpow_pos hx_abs_pos]
    exact hlog_ge

  -- Direct bound: |y| < β^my (from floor property)
  have hy_ub_my : |y| < (beta : ℝ) ^ my := by
    have hfloor_lt : Real.log |y| / Real.log (beta : ℝ) <
        Int.floor (Real.log |y| / Real.log (beta : ℝ)) + 1 := Int.lt_floor_add_one _
    have hdiv_lt : Real.log |y| < (Int.floor (Real.log |y| / Real.log (beta : ℝ)) + 1) *
        Real.log (beta : ℝ) := by
      have := mul_lt_mul_of_pos_right hfloor_lt hlogβ_pos
      field_simp at this
      rw [mul_comm] at this
      exact this
    have hlog_lt : Real.log |y| < my * Real.log (beta : ℝ) := by
      convert hdiv_lt using 2
      simp only [hmy_def, Int.cast_add, Int.cast_one]
    have hpow_log : Real.log ((beta : ℝ) ^ my) = my * Real.log (beta : ℝ) := by
      rw [Real.log_zpow]
    rw [← hpow_log] at hlog_lt
    have hpow_pos : 0 < (beta : ℝ) ^ my := zpow_pos hbpos _
    rw [← Real.log_lt_log_iff hy_abs_pos hpow_pos]
    exact hlog_lt

  -- From my ≤ mx - 2: |y| < β^(mx - 2)
  have hy_lt_pow : |y| < (beta : ℝ) ^ (mx - 2) := by
    have hpow_le : (beta : ℝ) ^ my ≤ (beta : ℝ) ^ (mx - 2) := zpow_le_zpow_right₀ hβR_ge hmy_le'
    exact lt_of_lt_of_le hy_ub_my hpow_le

  -- |y| < |x| since β^(mx-2) < β^(mx-1) ≤ |x|
  have hy_lt_x : |y| < |x| := by
    have hpow_lt : (beta : ℝ) ^ (mx - 2) < (beta : ℝ) ^ (mx - 1) := by
      have hlt : mx - 2 < mx - 1 := by grind
      exact zpow_lt_zpow_right₀ hβR hlt
    calc |y| < (beta : ℝ) ^ (mx - 2) := hy_lt_pow
      _ < (beta : ℝ) ^ (mx - 1) := hpow_lt
      _ ≤ |x| := hx_lb

  -- x + y ≠ 0 (since |y| < |x|)
  have hxy_ne : x + y ≠ 0 := by
    intro h
    have : x = -y := by linarith
    rw [this] at hy_lt_x
    simp only [abs_neg] at hy_lt_x
    exact (lt_irrefl _) hy_lt_x

  -- Key bound: |x + y| ≥ |x| - |y| (reversed triangle inequality)
  have htri : |x| - |y| ≤ |x + y| := by
    have h_diff_pos : 0 ≤ |x| - |y| := by linarith
    have h_abs_diff : |x| - |y| = abs (|x| - |y|) := (abs_of_nonneg h_diff_pos).symm
    rw [h_abs_diff]
    have := abs_abs_sub_abs_le_abs_sub x (-y)
    simp only [abs_neg, sub_neg_eq_add] at this
    exact this

  -- |x| - |y| > β^(mx-1) - β^(mx-2) = β^(mx-2)(β - 1) ≥ β^(mx-2)
  have hdiff_lb : |x| - |y| > (beta : ℝ) ^ (mx - 2) := by
    have hdiff_ge : |x| - |y| > (beta : ℝ) ^ (mx - 1) - (beta : ℝ) ^ (mx - 2) := by
      linarith
    have hfactor : (beta : ℝ) ^ (mx - 1) - (beta : ℝ) ^ (mx - 2) =
        (beta : ℝ) ^ (mx - 2) * ((beta : ℝ) - 1) := by
      have heq : (mx - 1 : ℤ) = (mx - 2) + 1 := by ring
      rw [heq, zpow_add₀ hbne, zpow_one]
      ring
    rw [hfactor] at hdiff_ge
    -- beta ≥ 2 as integer, so (beta : ℝ) - 1 ≥ 1
    have hbeta_ge_two : (2 : ℤ) ≤ beta := hβ
    have hbeta_ge : (beta : ℝ) - 1 ≥ 1 := by
      have : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hbeta_ge_two
      linarith
    have hpow_pos : 0 < (beta : ℝ) ^ (mx - 2) := zpow_pos hbpos _
    have hpow_nonneg : 0 ≤ (beta : ℝ) ^ (mx - 2) := le_of_lt hpow_pos
    have hone_le : (1 : ℝ) ≤ (beta : ℝ) - 1 := hbeta_ge
    have hmul_ineq : (beta : ℝ) ^ (mx - 2) * 1 ≤ (beta : ℝ) ^ (mx - 2) * ((beta : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hone_le hpow_nonneg
    have hpow_eq : (beta : ℝ) ^ (mx - 2) * 1 = (beta : ℝ) ^ (mx - 2) := mul_one _
    rw [hpow_eq] at hmul_ineq
    linarith

  -- |x + y| ≥ β^(mx-2)
  have hxy_lb : (beta : ℝ) ^ (mx - 2) ≤ |x + y| := by
    have hlt : (beta : ℝ) ^ (mx - 2) < |x + y| := lt_of_lt_of_le hdiff_lb htri
    exact le_of_lt hlt

  -- Set up mxy
  set mxy := Int.floor (Real.log |x + y| / Real.log (beta : ℝ)) + 1 with hmxy_def

  -- From |x + y| ≥ β^(mx-2), we get mxy ≥ mx - 1
  have hmxy_ge : mxy ≥ mx - 1 := by
    have hxy_abs_pos : 0 < |x + y| := abs_pos.mpr hxy_ne
    have hlog_lb : Real.log |x + y| ≥ (mx - 2 : ℤ) * Real.log (beta : ℝ) := by
      have hlog_pow : Real.log ((beta : ℝ) ^ (mx - 2)) = (mx - 2 : ℤ) * Real.log (beta : ℝ) := by
        rw [Real.log_zpow]
      rw [← hlog_pow]
      exact Real.log_le_log (zpow_pos hbpos _) hxy_lb
    have hdiv_lb : Real.log |x + y| / Real.log (beta : ℝ) ≥ (mx - 2 : ℤ) := by
      rw [ge_iff_le, le_div_iff₀ hlogβ_pos]
      exact hlog_lb
    have hfloor_lb : Int.floor (Real.log |x + y| / Real.log (beta : ℝ)) ≥ mx - 2 := by
      exact Int.le_floor.mpr hdiv_lb
    simp only [hmxy_def]
    grind

  -- Prove the WP goal
  simp only [wp, PostCond.noThrow, PredTrans.pure, mag, hxy_ne, ite_false, Id.run, pure,
    hx_ne, hmxy_def, hmx_def]
  exact hmxy_ge

/-- Bounds on magnitude under division -/
theorem mag_div (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta ∧ x ≠ 0 ∧ y ≠ 0⌝⦄
    (pure (mag beta (x / y), mag beta x, mag beta y) : Id _)
    ⦃⇓t => ⌜t.2.1 - t.2.2 ≤ t.1 ∧ t.1 ≤ t.2.1 - t.2.2 + 1⌝⦄ := by
  intro h
  rcases h with ⟨hβ, hx_ne, hy_ne⟩
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := Real.log_pos hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos

  -- x/y ≠ 0
  have hxy_ne : x / y ≠ 0 := div_ne_zero hx_ne hy_ne
  have hx_abs_pos : 0 < |x| := abs_pos.mpr hx_ne
  have hy_abs_pos : 0 < |y| := abs_pos.mpr hy_ne

  -- Reduce to floor expressions
  simp [wp, PostCond.noThrow, Id.run, pure, mag, hx_ne, hy_ne, hxy_ne]

  -- Set up the log expressions
  set Lx := Real.log |x| / Real.log (beta : ℝ) with hLx
  set Ly := Real.log |y| / Real.log (beta : ℝ) with hLy
  set Lxy := Real.log |x / y| / Real.log (beta : ℝ) with hLxy_def
  have hLx' : Lx = Real.log x / Real.log (beta : ℝ) := by
    simpa [log_abs] using hLx
  have hLy' : Ly = Real.log y / Real.log (beta : ℝ) := by
    simpa [log_abs] using hLy
  have hLxy' : Lxy = Real.log (x / y) / Real.log (beta : ℝ) := by
    simpa [log_abs] using hLxy_def

  -- Key: log|x/y| = log|x| - log|y|
  have habs_div : |x / y| = |x| / |y| := abs_div x y
  have hlog_div : Real.log |x / y| = Real.log |x| - Real.log |y| := by
    rw [habs_div]
    exact Real.log_div (ne_of_gt hx_abs_pos) (ne_of_gt hy_abs_pos)

  -- Therefore Lxy = Lx - Ly
  have hLxy_eq : Lxy = Lx - Ly := by
    simp [hLxy_def, hLx, hLy, hlog_div]
    field_simp [hlogβ_ne]

  -- Floor bounds: ⌊Lx - Ly⌋ is between ⌊Lx⌋ - ⌊Ly⌋ - 1 and ⌊Lx⌋ - ⌊Ly⌋
  have hfloor_sub_lb : Int.floor Lx - Int.floor Ly - 1 ≤ Int.floor (Lx - Ly) := by
    have hlt : ((Int.floor Lx - Int.floor Ly - 1 : ℤ) : ℝ) < Lx - Ly := by
      have h1 : (Int.floor Lx : ℝ) ≤ Lx := Int.floor_le Lx
      have h2 : Ly < Int.floor Ly + 1 := Int.lt_floor_add_one Ly
      push_cast; linarith
    exact Int.le_floor.mpr (le_of_lt hlt)

  have hfloor_sub_ub : Int.floor (Lx - Ly) ≤ Int.floor Lx - Int.floor Ly := by
    have h1 : Lx < Int.floor Lx + 1 := Int.lt_floor_add_one Lx
    have h2 : (Int.floor Ly : ℝ) ≤ Ly := Int.floor_le Ly
    have hcast : Lx - Ly < ((Int.floor Lx - Int.floor Ly + 1 : ℤ) : ℝ) := by
      simp only [Int.cast_sub, Int.cast_add, Int.cast_one]
      linarith
    have := Int.floor_le_sub_one_iff.mpr hcast
    linarith

  -- Prove the inequality in terms of Lx/Ly, then rewrite back.
  have h_goal :
      (Int.floor Lx + 1 - (Int.floor Ly + 1) ≤ Int.floor (Lx - Ly) + 1) ∧
        (Int.floor (Lx - Ly) + 1 ≤ Int.floor Lx + 1 - (Int.floor Ly + 1) + 1) := by
    constructor
    · linarith [hfloor_sub_lb]
    · linarith [hfloor_sub_ub]
  have hlog_div_abs : Real.log (x / y) / Real.log (beta : ℝ) = Lx - Ly := by
    simpa [hLxy_eq] using hLxy'.symm
  simpa [hlog_div_abs, hLx', hLy', add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
    using h_goal

/-- Magnitude of square root

    With floor+1 semantics: mag(√x) = ⌊log(√x)/log β⌋ + 1
-/
theorem mag_sqrt (beta : Int) (x : ℝ) :
    ⦃⌜1 < beta ∧ 0 < x⌝⦄
    (pure (mag beta (Real.sqrt x), mag beta x) : Id _)
    ⦃⇓p => ⌜p.1 = Int.floor ((Real.log x / Real.log (beta : ℝ)) / 2) + 1⌝⦄ := by
  intro h
  rcases h with ⟨hβ, hx_pos⟩
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := Real.log_pos hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  -- sqrt x > 0 and sqrt x ≠ 0
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hsqrt_ne : Real.sqrt x ≠ 0 := ne_of_gt hsqrt_pos
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  -- Reduce the monad
  simp only [wp, PostCond.noThrow, Id.run, pure, bind, mag]
  simp only [hsqrt_ne, hx_ne, ite_false]
  -- The key: log(sqrt x) = (1/2) * log x
  have hlog_sqrt : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx_nonneg
  -- Hence log(sqrt x) / log β = (log x / log β) / 2
  have heq : Real.log |Real.sqrt x| / Real.log (beta : ℝ)
           = (Real.log x / Real.log (beta : ℝ)) / 2 := by
    rw [abs_of_pos hsqrt_pos, hlog_sqrt]
    field_simp
  simp only [heq, wp, PostCond.noThrow, PredTrans.pure]
  trivial

/-- Magnitude at 1

    With floor+1 semantics: mag(1) = ⌊0⌋ + 1 = 1
    This corresponds to 1 being in the interval from β^0 to β^1 (including left, excluding right).
-/
theorem mag_1 (beta : Int) :
    ⦃⌜1 < beta⌝⦄
    (pure (mag beta (1 : ℝ)) : Id _)
    ⦃⇓m => ⌜m = 1⌝⦄ := by
  intro _
  -- Direct computation from the definition of `mag`:
  -- |1| = 1 and log 1 = 0, hence floor(0 / log β) + 1 = 0 + 1 = 1.
  simp [wp, PostCond.noThrow, Id.run, pure, mag, abs_one, Real.log_one]

end Mag

end FloatSpec.Core.Raux
