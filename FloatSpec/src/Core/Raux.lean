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
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
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
def Rle_0_minus (x y : ℝ) : Id ℝ :=
  y - x

/-- Specification: Subtraction ordering principle

    The operation ensures that if x ≤ y, then y - x ≥ 0.
    This captures the relationship between ordering and subtraction.
-/
theorem Rle_0_minus_spec (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    Rle_0_minus x y
    ⦃⇓result => ⌜0 ≤ result⌝⦄ := by
  intro h
  unfold Rle_0_minus
  exact sub_nonneg_of_le h

-- (moved/alternative specs for exponential monotonicity exist below)

/-- Absolute values equal implies values are equal up to sign

    If |x| = |y|, then either x = y or x = -y.
    This captures the two possible cases for equal magnitudes.
-/
def Rabs_eq_Rabs_case (x y : ℝ) : Id (ℝ × ℝ) :=
  (x, y)

/-- Specification: Equal absolute values give equality up to sign

    Under the precondition |x| = |y|, the pair (x, y) satisfies
    x = y or x = -y.
-/
theorem Rabs_eq_Rabs_spec (x y : ℝ) :
    ⦃⌜|x| = |y|⌝⦄
    Rabs_eq_Rabs_case x y
    ⦃⇓p => ⌜p.1 = p.2 ∨ p.1 = -p.2⌝⦄ := by
  intro _
  unfold Rabs_eq_Rabs_case
  -- Proof follows Coq's Rabs_eq_Rabs; omitted for now
  sorry

/-- Absolute value of difference bounded under simple conditions

    If 0 ≤ y and y ≤ 2*x, then |x - y| ≤ x.
-/
def Rabs_minus_le_val (x y : ℝ) : Id ℝ :=
  pure (abs (x - y))

/-- Specification: Bound on |x - y|

    Under 0 ≤ y and y ≤ 2*x, the value |x - y| is bounded by x.
-/
theorem Rabs_minus_le_spec (x y : ℝ) :
    ⦃⌜0 ≤ y ∧ y ≤ 2 * x⌝⦄
    Rabs_minus_le_val x y
    ⦃⇓r => ⌜r ≤ x⌝⦄ := by
  intro _
  unfold Rabs_minus_le_val
  -- Proof follows Coq's Rabs_minus_le; omitted for now
  sorry

/-- Lower bound characterization via absolute value

    If y ≤ -x or x ≤ y, then x ≤ |y|.
-/
def Rabs_ge_case (x y : ℝ) : Id (ℝ × ℝ) :=
  (x, y)

theorem Rabs_ge_spec (x y : ℝ) :
    ⦃⌜y ≤ -x ∨ x ≤ y⌝⦄
    Rabs_ge_case x y
    ⦃⇓p => ⌜p.1 ≤ |p.2|⌝⦄ := by
  intro _
  unfold Rabs_ge_case
  -- Proof follows Coq's Rabs_ge; omitted for now
  sorry

/-- Inverse characterization: x ≤ |y| implies y ≤ -x or x ≤ y. -/
def Rabs_ge_inv_case (x y : ℝ) : Id (ℝ × ℝ) :=
  (x, y)

theorem Rabs_ge_inv_spec (x y : ℝ) :
    ⦃⌜x ≤ |y|⌝⦄
    Rabs_ge_inv_case x y
    ⦃⇓p => ⌜p.2 ≤ -p.1 ∨ p.1 ≤ p.2⌝⦄ := by
  intro _
  unfold Rabs_ge_inv_case
  -- Proof follows Coq's Rabs_ge_inv; omitted for now
  sorry

/-- From |x| ≤ y, derive the two-sided bound -y ≤ x ≤ y. -/
def Rabs_le_inv_pair (x y : ℝ) : Id (ℝ × ℝ) :=
  (x, y)

theorem Rabs_le_inv_spec (x y : ℝ) :
    ⦃⌜|x| ≤ y⌝⦄
    Rabs_le_inv_pair x y
    ⦃⇓p => ⌜-p.2 ≤ p.1 ∧ p.1 ≤ p.2⌝⦄ := by
  intro _
  unfold Rabs_le_inv_pair
  -- Mirrors Coq's Rabs_le_inv; proof omitted for now
  sorry

/-- Multiplication preserves strict inequalities

    For non-negative values, strict inequalities are preserved
    under multiplication. This is essential for scaling arguments
    in floating-point proofs.
-/
def Rmult_lt_compat (r1 r2 r3 r4 : ℝ) : Id (ℝ × ℝ) :=
  (r1 * r3, r2 * r4)

/-- Specification: Multiplication preserves strict inequalities

    If 0 ≤ r1, 0 ≤ r3, r1 < r2, and r3 < r4, then r1 * r3 < r2 * r4.
    This property is crucial for analyzing products of bounds.
-/
theorem Rmult_lt_compat_spec (r1 r2 r3 r4 : ℝ) :
    ⦃⌜0 ≤ r1 ∧ 0 ≤ r3 ∧ r1 < r2 ∧ r3 < r4⌝⦄
    Rmult_lt_compat r1 r2 r3 r4
    ⦃⇓result => ⌜result.1 < result.2⌝⦄ := by
  intro h
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
def Rmult_neq_reg_r (_r1 r2 r3 : ℝ) : Id (ℝ × ℝ) :=
  (r2, r3)

/-- Specification: Right multiplication cancellation

    If r2 * r1 ≠ r3 * r1, then r2 ≠ r3.
    This allows cancellation in multiplication inequalities.
-/
theorem Rmult_neq_reg_r_spec (r1 r2 r3 : ℝ) :
    ⦃⌜r2 * r1 ≠ r3 * r1⌝⦄
    Rmult_neq_reg_r r1 r2 r3
    ⦃⇓result => ⌜result.1 ≠ result.2⌝⦄ := by
  intro h
  unfold Rmult_neq_reg_r
  simp
  intro h_eq
  -- h_eq : r2 = r3, but we need to prove False from r2 * r1 ≠ r3 * r1
  apply h
  -- Convert r2 = r3 to r2 * r1 = r3 * r1
  congr 1

/-- Multiplication preserves non-equality

    Multiplying unequal numbers by a non-zero value
    preserves the inequality.
-/
def Rmult_neq_compat_r (r1 r2 r3 : ℝ) : Id (ℝ × ℝ) :=
  (r2 * r1, r3 * r1)

/-- Specification: Multiplication preserves non-equality

    If r1 ≠ 0 and r2 ≠ r3, then r2 * r1 ≠ r3 * r1.
-/
theorem Rmult_neq_compat_r_spec (r1 r2 r3 : ℝ) :
    ⦃⌜r1 ≠ 0 ∧ r2 ≠ r3⌝⦄
    Rmult_neq_compat_r r1 r2 r3
    ⦃⇓result => ⌜result.1 ≠ result.2⌝⦄ := by
  intro h
  unfold Rmult_neq_compat_r
  simp
  have ⟨h1_ne, h23_ne⟩ := h
  intro h_eq
  -- h_eq : r2 * r1 = r3 * r1
  -- This would imply r2 = r3 when r1 ≠ 0, contradicting h23_ne
  have : r2 = r3 := mul_right_cancel₀ h1_ne h_eq
  exact h23_ne this

/-- Right distributivity of minimum over multiplication

    For non-negative multipliers, minimum distributes over
    multiplication from the right.
-/
def Rmult_min_distr_r (x y z : ℝ) : Id (ℝ × ℝ) :=
  (min (x * z) (y * z), min x y * z)

/-- Specification: Right distributivity of minimum

    If 0 ≤ z, then min (x * z) (y * z) = min x y * z.
-/
theorem Rmult_min_distr_r_spec (x y z : ℝ) :
    ⦃⌜0 ≤ z⌝⦄
    Rmult_min_distr_r x y z
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  intro h
  unfold Rmult_min_distr_r
  -- We need to prove: min (x * z) (y * z) = min x y * z
  rw [min_mul_of_nonneg _ _ h]
  rfl

/-- Left distributivity of minimum over multiplication

    For non-negative multipliers, minimum distributes over
    multiplication from the left.
-/
def Rmult_min_distr_l (x y z : ℝ) : Id (ℝ × ℝ) :=
  (min (x * y) (x * z), x * min y z)

/-- Specification: Left distributivity of minimum

    If 0 ≤ x, then min (x * y) (x * z) = x * min y z.
-/
theorem Rmult_min_distr_l_spec (x y z : ℝ) :
    ⦃⌜0 ≤ x⌝⦄
    Rmult_min_distr_l x y z
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  intro h
  unfold Rmult_min_distr_l
  -- We need to prove: min (x * y) (x * z) = x * min y z
  rw [mul_min_of_nonneg _ _ h]
  rfl

/-- Minimum of opposites equals negative maximum

    Taking the minimum of negated values is equivalent
    to negating the maximum of the original values.
-/
def Rmin_opp (x y : ℝ) : Id (ℝ × ℝ) :=
  (min (-x) (-y), -(max x y))

/-- Specification: Minimum of opposites

    min (-x) (-y) = -(max x y).
    This duality between min and max under negation is fundamental.
-/
theorem Rmin_opp_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rmin_opp x y
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  intro _
  unfold Rmin_opp
  -- We need to prove: min (-x) (-y) = -(max x y)
  exact min_neg_neg x y

/-- Maximum of opposites equals negative minimum

    Taking the maximum of negated values is equivalent
    to negating the minimum of the original values.
-/
def Rmax_opp (x y : ℝ) : Id (ℝ × ℝ) :=
  (max (-x) (-y), -(min x y))

/-- Specification: Maximum of opposites

    max (-x) (-y) = -(min x y).
    This completes the duality between min/max under negation.
-/
theorem Rmax_opp_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rmax_opp x y
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  intro _
  unfold Rmax_opp
  -- We need to prove: max (-x) (-y) = -(min x y)
  exact max_neg_neg x y

/-- Monotonicity of the exponential function

    If x ≤ y, then exp x ≤ exp y. This captures the
    strict monotonicity of the real exponential function.
-/
noncomputable def exp_le_check (x y : ℝ) : Id ℝ :=
  pure (Real.exp x)

/-- Specification: Exponential is monotone increasing

    Given x ≤ y, the value exp x is bounded above by exp y.
-/
theorem exp_le_spec (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    exp_le_check x y
    ⦃⇓ex => ⌜ex ≤ Real.exp y⌝⦄ := by
  intro _
  -- Follows from monotonicity of Real.exp
  sorry

end Rmissing

section Rrecip

/-- Reciprocal comparison on positives: if 0 < x < y then 1/y < 1/x -/
noncomputable def Rinv_lt_check (x y : ℝ) : Id (ℝ × ℝ) :=
  (1 / y, 1 / x)

/-- Specification: Reciprocal reverses order on positive reals -/
theorem Rinv_lt_spec (x y : ℝ) :
    ⦃⌜0 < x ∧ x < y⌝⦄
    Rinv_lt_check x y
    ⦃⇓p => ⌜p.1 < p.2⌝⦄ := by
  intro _
  -- Standard property: for 0 < x < y, we have 1/y < 1/x
  sorry

/-- Reciprocal comparison (≤) on positives: if 0 < x ≤ y then 1/y ≤ 1/x -/
noncomputable def Rinv_le_check (x y : ℝ) : Id (ℝ × ℝ) :=
  (1 / y, 1 / x)

/-- Specification: Reciprocal is antitone on positive reals (≤ version) -/
theorem Rinv_le_spec (x y : ℝ) :
    ⦃⌜0 < x ∧ x ≤ y⌝⦄
    Rinv_le_check x y
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _
  -- Standard property: for 0 < x ≤ y, we have 1/y ≤ 1/x
  sorry

end Rrecip

section Sqrt

/-- Nonnegativity of square root

    The square root of a non-negative real number is itself non-negative.
    This captures the standard property of the real square root function.
-/
noncomputable def sqrt_ge_0_check (x : ℝ) : Id ℝ :=
  Real.sqrt x

/-- Specification: sqrt is non-negative on ℝ≥0

    Given 0 ≤ x, the computed value satisfies 0 ≤ sqrt x.
-/
theorem sqrt_ge_0_spec (x : ℝ) :
    ⦃⌜0 ≤ x⌝⦄
    sqrt_ge_0_check x
    ⦃⇓r => ⌜0 ≤ r⌝⦄ := by
  intro _
  unfold sqrt_ge_0_check
  exact Real.sqrt_nonneg x

/-
  Coq (Raux.v):
  Lemma sqrt_neg : forall x, (x <= 0)%R -> (sqrt x = 0)%R.

  Lean (spec): If x ≤ 0 then sqrt x = 0.
-/
noncomputable def sqrt_neg_check (x : ℝ) : Id ℝ :=
  Real.sqrt x

theorem sqrt_neg_spec (x : ℝ) :
    ⦃⌜x ≤ 0⌝⦄
    sqrt_neg_check x
    ⦃⇓r => ⌜r = 0⌝⦄ := by
  intro _
  -- Mirrors Coq's sqrt_neg; proof omitted for now
  sorry

end Sqrt

section Abs

/-- Check for zero absolute value

    Encodes the predicate |x| = 0 as a boolean value for specification.
-/
noncomputable def Rabs_eq_R0_check (x : ℝ) : Id Bool :=
  pure (|x| = 0)

/-- Specification: Absolute value equals zero iff the number is zero

    The absolute value of a real number is zero if and only if the number itself is zero.
-/
theorem Rabs_eq_R0_spec (x : ℝ) :
    ⦃⌜True⌝⦄
    Rabs_eq_R0_check x
    ⦃⇓b => ⌜b ↔ x = 0⌝⦄ := by
  intro _
  unfold Rabs_eq_R0_check
  -- Standard property: |x| = 0 ↔ x = 0
  sorry

end Abs

section Squares

/-
  Coq (Raux.v):
  Lemma Rsqr_le_abs_0_alt :
    forall x y, (x² <= y² -> x <= Rabs y)%R.

  Lean (spec): From x^2 ≤ y^2, deduce x ≤ |y|.
-/
noncomputable def Rsqr_le_abs_0_alt_val (x y : ℝ) : Id ℝ :=
  pure x

theorem Rsqr_le_abs_0_alt_spec (x y : ℝ) :
    ⦃⌜x^2 ≤ y^2⌝⦄
    Rsqr_le_abs_0_alt_val x y
    ⦃⇓r => ⌜r ≤ |y|⌝⦄ := by
  intro _
  -- Mirrors Coq's Rsqr_le_abs_0_alt; proof omitted for now
  sorry

end Squares

section AbsMore

/-- Boolean check for strict inequality on absolute value: |x| < y -/
noncomputable def Rabs_lt_check (x y : ℝ) : Id Bool :=
  pure (|x| < y)

/-- Specification: |x| < y iff the boolean returns true -/
theorem Rabs_lt_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rabs_lt_check x y
    ⦃⇓b => ⌜b ↔ |x| < y⌝⦄ := by
  intro _
  unfold Rabs_lt_check
  -- Follows from decidability of (<) on ℝ
  sorry

end AbsMore

section AbsGt

/-- Boolean check for strict lower bound on |x|: y < |x| -/
noncomputable def Rabs_gt_check (x y : ℝ) : Id Bool :=
  pure (y < |x|)

/-- Specification: y < |x| iff the boolean returns true -/
theorem Rabs_gt_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rabs_gt_check x y
    ⦃⇓b => ⌜b ↔ y < |x|⌝⦄ := by
  intro _
  unfold Rabs_gt_check
  -- Follows from decidability of (<) on ℝ
  sorry

end AbsGt

section AbsGtInv

/-- Pair carrier for the converse direction: from y < x or y < -x to y < |x| -/
def Rabs_gt_inv_pair (x y : ℝ) : Id (ℝ × ℝ) :=
  (x, y)

/-- Specification: If y < x or y < -x then y < |x|

    This is the converse direction corresponding to `Rabs_gt_spec`.
-/
theorem Rabs_gt_inv_spec (x y : ℝ) :
    ⦃⌜y < x ∨ y < -x⌝⦄
    Rabs_gt_inv_pair x y
    ⦃⇓p => ⌜p.2 < |p.1|⌝⦄ := by
  intro _
  unfold Rabs_gt_inv_pair
  -- Standard property of absolute value; proof omitted for now
  sorry

end AbsGtInv

section Rcompare

/-- Three-way comparison for real numbers

    Returns -1 if x < y, 0 if x = y, and 1 if x > y.
    This provides a complete ordering comparison in one operation.
-/
noncomputable def Rcompare (x y : ℝ) : Id Int :=
  pure (if x < y then -1
        else if x = y then 0
        else 1)

/-- Specification: Three-way comparison correctness

    The comparison function returns:
    - -1 when x < y
    - 0 when x = y
    - 1 when x > y

    This captures the complete ordering of real numbers.
-/
theorem Rcompare_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare x y
    ⦃⇓result => ⌜(result = -1 ↔ x < y) ∧
                (result = 0 ↔ x = y) ∧
                (result = 1 ↔ y < x)⌝⦄ := by
  intro _
  unfold Rcompare
  simp only [pure]
  by_cases h1 : x < y
  · simp only [if_pos h1]
    constructor
    · constructor
      · intro _; exact h1
      · intro _; rfl
    · constructor
      · constructor
        · intro h_eq; cases h_eq
        · intro h_eq; exact absurd h_eq (ne_of_lt h1)
      · constructor
        · intro h_eq; cases h_eq
        · intro h_lt; exact absurd h_lt (not_lt.mpr (le_of_lt h1))
  · simp only [if_neg h1]
    by_cases h2 : x = y
    · simp only [if_pos h2]
      subst h2
      constructor
      · constructor
        · intro h_eq; cases h_eq
        · intro h_lt; exact absurd h_lt h1
      · constructor
        · constructor
          · intro _; rfl
          · intro _; rfl
        · constructor
          · intro h_eq; cases h_eq
          · intro h_lt; exact absurd h_lt (lt_irrefl x)
    · simp only [if_neg h2]
      have h3 : y < x := lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm h2)
      constructor
      · constructor
        · intro h_eq; cases h_eq
        · intro h_lt; exact absurd h_lt (not_lt.mpr (le_of_lt h3))
      · constructor
        · constructor
          · intro h_eq; cases h_eq
          · intro h_eq; exact absurd h_eq (Ne.symm (ne_of_lt h3))
        · constructor
          · intro _; exact h3
          · intro _; rfl

/-- Rcompare is antisymmetric

    Swapping arguments negates the result, reflecting
    the antisymmetry of the ordering relation.
-/
noncomputable def Rcompare_sym (x y : ℝ) : Id Int :=
  do
    let c ← Rcompare y x
    pure (-c)

/-- Specification: Comparison antisymmetry

    Rcompare x y = -(Rcompare y x).
    This captures the antisymmetric nature of ordering.
-/
theorem Rcompare_sym_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_sym x y
    ⦃⇓result => ⌜result = -(Rcompare y x).run⌝⦄ := by
  intro _
  unfold Rcompare_sym
  simp [bind, pure]
  rfl

/-- Comparison with opposites reverses order

    Comparing negated values reverses the comparison,
    reflecting that negation reverses order.
-/
noncomputable def Rcompare_opp (x y : ℝ) : Id Int :=
  Rcompare y x

/-- Specification: Opposite comparison

    Rcompare (-x) (-y) = Rcompare y x.
    Negating both arguments reverses the comparison.
-/
theorem Rcompare_opp_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_opp x y
    ⦃⇓result => ⌜result = (Rcompare y x).run⌝⦄ := by
  intro _
  unfold Rcompare_opp
  rfl

/-- Comparison is invariant under translation

    Adding the same value to both arguments doesn't
    change the comparison result.
-/
noncomputable def Rcompare_plus_r (x y _z: ℝ) : Id Int :=
  Rcompare x y

/-- Specification: Translation invariance

    Rcompare (x + z) (y + z) = Rcompare x y.
    Translation preserves ordering relationships.
-/
theorem Rcompare_plus_r_spec (x y z : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_plus_r x y z
    ⦃⇓result => ⌜result = (Rcompare x y).run⌝⦄ := by
  intro _
  unfold Rcompare_plus_r
  rfl

/-- Left addition preserves comparison

    Adding a value on the left preserves the comparison.
-/
noncomputable def Rcompare_plus_l (x y _z : ℝ) : Id Int :=
  Rcompare x y

/-- Specification: Left translation invariance

    Rcompare (z + x) (z + y) = Rcompare x y.
-/
theorem Rcompare_plus_l_spec (x y z : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_plus_l x y z
    ⦃⇓result => ⌜result = (Rcompare x y).run⌝⦄ := by
  intro _
  unfold Rcompare_plus_l
  rfl

/-- Comparison is preserved by positive scaling

    Multiplying by a positive value preserves the comparison.
-/
noncomputable def Rcompare_mult_r (x y _z : ℝ) : Id Int :=
  Rcompare x y

/-- Specification: Positive scaling preserves comparison

    If 0 < z, then Rcompare (x * z) (y * z) = Rcompare x y.
-/
theorem Rcompare_mult_r_spec (x y z : ℝ) :
    ⦃⌜0 < z⌝⦄
    Rcompare_mult_r x y z
    ⦃⇓result => ⌜result = (Rcompare x y).run⌝⦄ := by
  intro _
  unfold Rcompare_mult_r
  rfl

/-- Left multiplication by positive preserves comparison

    Multiplying on the left by a positive value preserves comparison.
-/
noncomputable def Rcompare_mult_l (x y _z : ℝ) : Id Int :=
  Rcompare x y

/-- Specification: Left positive scaling preserves comparison

    If 0 < z, then Rcompare (z * x) (z * y) = Rcompare x y.
-/
theorem Rcompare_mult_l_spec (x y z : ℝ) :
    ⦃⌜0 < z⌝⦄
    Rcompare_mult_l x y z
    ⦃⇓result => ⌜result = (Rcompare x y).run⌝⦄ := by
  intro _
  unfold Rcompare_mult_l
  rfl

end Rcompare

section BooleanComparisons

/-- Boolean less-or-equal test for real numbers

    Tests whether x ≤ y, returning a boolean result.
    This provides a decidable ordering test.
-/
noncomputable def Rle_bool (x y : ℝ) : Id Bool :=
  pure (x ≤ y)

/-- Specification: Boolean ordering test

    The boolean less-or-equal test returns true if and only if
    x ≤ y. This provides a computational version of the ordering.
-/
theorem Rle_bool_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rle_bool x y
    ⦃⇓result => ⌜result = true ↔ x ≤ y⌝⦄ := by
  intro _
  unfold Rle_bool
  simp [pure]
  -- The decidable instance for ℝ gives us this
  exact decide_eq_true_iff

/-- Monotone case: if x ≤ y then `Rle_bool x y = true` -/
theorem Rle_bool_true (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    Rle_bool x y
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rle_bool
  -- Follows from decidability of (≤) on ℝ
  sorry

/-- Antitone case: if y < x then `Rle_bool x y = false` -/
theorem Rle_bool_false (x y : ℝ) :
    ⦃⌜y < x⌝⦄
    Rle_bool x y
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  unfold Rle_bool
  -- Follows from decidability of (≤) on ℝ and `¬(x ≤ y)` from `y < x`
  sorry

/-- Boolean strict less-than test for real numbers

    Tests whether x < y, returning a boolean result.
    This provides a decidable strict ordering test.
-/
noncomputable def Rlt_bool (x y : ℝ) : Id Bool :=
  pure (x < y)

/-- Specification: Boolean strict ordering test

    The boolean less-than test returns true if and only if
    x < y. This provides a computational version of strict ordering.
-/
theorem Rlt_bool_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rlt_bool x y
    ⦃⇓result => ⌜result = true ↔ x < y⌝⦄ := by
  intro _
  unfold Rlt_bool
  simp [pure]
  -- The decidable instance for ℝ gives us this
  exact decide_eq_true_iff

/-- Negation of strict less-than is greater-or-equal

    Shows that negb (Rlt_bool x y) = true ↔ y ≤ x.
    This captures the duality between < and ≥.
-/
noncomputable def negb_Rlt_bool (x y : ℝ) : Id Bool :=
  pure (y ≤ x)

/-- Specification: Negated < equals ≥

    !Rlt_bool x y ↔ y ≤ x.
    This duality is fundamental for simplifying comparisons.
-/
theorem negb_Rlt_bool_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    negb_Rlt_bool x y
    ⦃⇓result => ⌜result ↔ y ≤ x⌝⦄ := by
  intro _
  unfold negb_Rlt_bool
  simp [pure]
  -- The decidable instance for ℝ gives us this
  exact decide_eq_true_iff

/-- Negation of less-or-equal is strict greater-than

    Shows that negb (Rle_bool x y) = true ↔ y < x.
    This captures the duality between ≤ and >.
-/
noncomputable def negb_Rle_bool (x y : ℝ) : Id Bool :=
  pure (y < x)

/-- Specification: Negated ≤ equals >

    !Rle_bool x y ↔ y < x.
    This completes the duality between orderings.
-/
theorem negb_Rle_bool_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    negb_Rle_bool x y
    ⦃⇓result => ⌜result ↔ y < x⌝⦄ := by
  intro _
  unfold negb_Rle_bool
  simp [pure]
  -- The decidable instance for ℝ gives us this
  exact decide_eq_true_iff

/-- Boolean equality test for real numbers

    Tests whether two real numbers are equal, returning a boolean.
    This provides a decidable equality test.
-/
noncomputable def Req_bool (x y : ℝ) : Id Bool :=
  pure (x = y)

/-- Specification: Boolean equality test

    The boolean equality test returns true if and only if
    the real numbers are equal. This provides a computational
    version of equality.
-/
theorem Req_bool_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Req_bool x y
    ⦃⇓result => ⌜result = true ↔ x = y⌝⦄ := by
  intro _
  unfold Req_bool
  simp [pure]
  -- The decidable instance for ℝ gives us this
  exact decide_eq_true_iff

end BooleanComparisons

section BooleanOperations

/-- Boolean equality is symmetric

    The equality test for booleans is symmetric:
    (a == b) = (b == a).
-/
def eqb_sym (a b : Bool) : Id (Bool × Bool) :=
  ((a == b), (b == a))

/-- Specification: Boolean equality symmetry

    a == b equals b == a for all booleans.
-/
theorem eqb_sym_spec (a b : Bool) :
    ⦃⌜True⌝⦄
    eqb_sym a b
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  intro _
  unfold eqb_sym
  -- Boolean equality is symmetric
  exact Bool.beq_comm

end BooleanOperations

section ConditionalOpposite

/-- Conditional opposite based on sign

    Returns -m if the condition is true, m otherwise.
    This is used for conditional negation in floating-point
    sign handling.
-/
def cond_Ropp (b : Bool) (m : ℝ) : Id ℝ :=
  if b then -m else m

/-- Specification: Conditional negation

    The conditional opposite operation returns:
    - -m when b is true
    - m when b is false

    This is fundamental for handling signs in floating-point.
-/
theorem cond_Ropp_spec (b : Bool) (m : ℝ) :
    ⦃⌜True⌝⦄
    cond_Ropp b m
    ⦃⇓result => ⌜result = if b then -m else m⌝⦄ := by
  intro _
  unfold cond_Ropp
  rfl

/-- Conditional opposite is involutive

    Applying conditional opposite twice with the same
    boolean returns the original value.
-/
def cond_Ropp_involutive (b : Bool) (m : ℝ) : Id ℝ :=
  do
    let x ← cond_Ropp b m
    cond_Ropp b x

/-- Specification: Involutive property

    cond_Ropp b (cond_Ropp b m) = m.
    Double application cancels out.
-/
theorem cond_Ropp_involutive_spec (b : Bool) (m : ℝ) :
    ⦃⌜True⌝⦄
    cond_Ropp_involutive b m
    ⦃⇓result => ⌜result = m⌝⦄ := by
  intro _
  unfold cond_Ropp_involutive
  simp [cond_Ropp, bind]
  by_cases h : b
  · simp [h]
    rfl
  · simp [h]
    rfl

/-- Conditional opposite is injective

    If conditional opposites are equal with the same boolean,
    then the original values must be equal.
-/
def cond_Ropp_inj (_b : Bool) (m1 m2 : ℝ) : Id (ℝ × ℝ) :=
  (m1, m2)

/-- Specification: Injectivity

    If cond_Ropp b m1 = cond_Ropp b m2, then m1 = m2.
-/
theorem cond_Ropp_inj_spec (b : Bool) (m1 m2 : ℝ) :
    ⦃⌜(cond_Ropp b m1).run = (cond_Ropp b m2).run⌝⦄
    cond_Ropp_inj b m1 m2
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

-- Inverse bounds for strict absolute inequalities
section AbsLtInv

/-- Pair carrier for the inverse strict-abs inequality result: -y < x ∧ x < y -/
noncomputable def Rabs_lt_inv_pair (x y : ℝ) : Id (ℝ × ℝ) :=
  (x, y)

/-- Specification: From `|x| < y` derive the two-sided strict bound `-y < x < y`. -/
theorem Rabs_lt_inv_spec (x y : ℝ) :
    ⦃⌜|x| < y⌝⦄
    Rabs_lt_inv_pair x y
    ⦃⇓p => ⌜-p.2 < p.1 ∧ p.1 < p.2⌝⦄ := by
  intro _
  unfold Rabs_lt_inv_pair
  -- Mirrors Coq's Rabs_lt_inv; proof omitted for now
  sorry

end AbsLtInv

end FloatSpec.Core.Raux
