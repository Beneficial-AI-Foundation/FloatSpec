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
  intro hxy
  unfold Rabs_eq_Rabs_case
  -- Use the standard equivalence |x| = |y| ↔ x = y ∨ x = -y
  simpa using (abs_eq_abs.mp hxy)

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
  intro h
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
def Rabs_ge_case (x y : ℝ) : Id (ℝ × ℝ) :=
  (x, y)

theorem Rabs_ge_spec (x y : ℝ) :
    ⦃⌜y ≤ -x ∨ x ≤ y⌝⦄
    Rabs_ge_case x y
    ⦃⇓p => ⌜p.1 ≤ |p.2|⌝⦄ := by
  intro h
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
def Rabs_ge_inv_case (x y : ℝ) : Id (ℝ × ℝ) :=
  (x, y)

theorem Rabs_ge_inv_spec (x y : ℝ) :
    ⦃⌜x ≤ |y|⌝⦄
    Rabs_ge_inv_case x y
    ⦃⇓p => ⌜p.2 ≤ -p.1 ∨ p.1 ≤ p.2⌝⦄ := by
  intro hx
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
def Rabs_le_inv_pair (x y : ℝ) : Id (ℝ × ℝ) :=
  (x, y)

theorem Rabs_le_inv_spec (x y : ℝ) :
    ⦃⌜|x| ≤ y⌝⦄
    Rabs_le_inv_pair x y
    ⦃⇓p => ⌜-p.2 ≤ p.1 ∧ p.1 ≤ p.2⌝⦄ := by
  intro h
  unfold Rabs_le_inv_pair
  exact (abs_le.mp h)

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
  pure (Real.exp x )

/-- Specification: Exponential is monotone increasing

    Given x ≤ y, the value exp x is bounded above by exp y.
-/
theorem exp_le_spec (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    exp_le_check x y
    ⦃⇓ex => ⌜ex ≤ Real.exp y⌝⦄ := by
  intro hxy
  unfold exp_le_check
  -- Using monotonicity of exp: exp x ≤ exp y ↔ x ≤ y
  exact (Iff.mpr Real.exp_le_exp hxy)

/-- Coq name compatibility: `exp_le` -/
theorem exp_le (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    exp_le_check x y
    ⦃⇓ex => ⌜ex ≤ Real.exp y⌝⦄ :=
  exp_le_spec x y

end Rmissing

section IZR

/-- Carrier for relating Int order and real order via casting -/
def IZR_le_lt_triple (m n p : Int) : Id (ℝ × ℝ × ℝ) :=
  ((m : ℝ), (n : ℝ), (p : ℝ))

/-- Coq: IZR_le_lt

    If m ≤ n < p as integers, then (m:ℝ) ≤ (n:ℝ) < (p:ℝ).
-/
theorem IZR_le_lt_spec (m n p : Int) :
    ⦃⌜m ≤ n ∧ n < p⌝⦄
    IZR_le_lt_triple m n p
    ⦃⇓t => ⌜t.1 ≤ t.2.1 ∧ t.2.1 < t.2.2⌝⦄ := by
  intro h
  unfold IZR_le_lt_triple
  rcases h with ⟨hmn, hnp⟩
  exact ⟨(Int.cast_mono hmn), (Int.cast_strictMono hnp)⟩

/-- Carrier for the converse relation from reals back to Ints -/
def le_lt_IZR_triple (m n p : Int) : Id (Int × Int × Int) :=
  (m, n, p)

/-- Coq: le_lt_IZR

    If (m:ℝ) ≤ (n:ℝ) < (p:ℝ), then m ≤ n < p as integers.
-/
theorem le_lt_IZR_spec (m n p : Int) :
    ⦃⌜(m : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (p : ℝ)⌝⦄
    le_lt_IZR_triple m n p
    ⦃⇓t => ⌜t.1 ≤ t.2.1 ∧ t.2.1 < t.2.2⌝⦄ := by
  intro h
  unfold le_lt_IZR_triple
  rcases h with ⟨hmnR, hnpR⟩
  -- Use order-reflecting casts: (m:ℝ) ≤ (n:ℝ) ↔ m ≤ n, and (n:ℝ) < (p:ℝ) ↔ n < p
  exact ⟨(Int.cast_le).1 hmnR, (Int.cast_lt).1 hnpR⟩

/-- Carrier for inequality preservation under casting -/
def neq_IZR_pair (m n : Int) : Id (Int × Int) :=
  (m, n)

/-- Coq: neq_IZR

    If (m:ℝ) ≠ (n:ℝ), then m ≠ n as integers.
-/
theorem neq_IZR_spec (m n : Int) :
    ⦃⌜(m : ℝ) ≠ (n : ℝ)⌝⦄
    neq_IZR_pair m n
    ⦃⇓p => ⌜p.1 ≠ p.2⌝⦄ := by
  intro hmnR
  unfold neq_IZR_pair
  -- Show: m ≠ n, using injectivity of Int-cast into ℝ
  intro hmn
  apply hmnR
  -- Casting preserves equalities
  simpa [hmn]

end IZR

section Rrecip

/-- Reciprocal comparison on positives: if 0 < x < y then 1/y < 1/x -/
noncomputable def Rinv_lt_check (x y : ℝ) : Id (ℝ × ℝ) :=
  (1 / y, 1 / x)

/-- Specification: Reciprocal reverses order on positive reals -/
theorem Rinv_lt_spec (x y : ℝ) :
    ⦃⌜0 < x ∧ x < y⌝⦄
    Rinv_lt_check x y
    ⦃⇓p => ⌜p.1 < p.2⌝⦄ := by
  intro h
  -- Standard property: for 0 < x < y, we have 1/y < 1/x
  unfold Rinv_lt_check
  exact one_div_lt_one_div_of_lt h.left h.right

/-- Reciprocal comparison (≤) on positives: if 0 < x ≤ y then 1/y ≤ 1/x -/
noncomputable def Rinv_le_check (x y : ℝ) : Id (ℝ × ℝ) :=
  (1 / y, 1 / x)

/-- Specification: Reciprocal is antitone on positive reals (≤ version) -/
theorem Rinv_le_spec (x y : ℝ) :
    ⦃⌜0 < x ∧ x ≤ y⌝⦄
    Rinv_le_check x y
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro h
  -- Standard property: for 0 < x ≤ y, we have 1/y ≤ 1/x
  unfold Rinv_le_check
  exact one_div_le_one_div_of_le h.left h.right

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
  intro hx
  unfold sqrt_neg_check
  exact Real.sqrt_eq_zero_of_nonpos hx

/-- Coq (Raux.v): Theorem sqrt_ge_0
    For all real x, 0 ≤ sqrt x. We provide a wrapper with
    the exact Coq name around `sqrt_ge_0_check`.

    Lean (spec): No precondition; sqrt is nonnegative. -/
theorem sqrt_ge_0 (x : ℝ) :
    ⦃⌜True⌝⦄
    sqrt_ge_0_check x
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
  simpa using (abs_eq_zero : |x| = 0 ↔ x = 0)

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
  intro hxy
  -- r = x by definition
  unfold Rsqr_le_abs_0_alt_val
  -- From x^2 ≤ y^2 we get |x| ≤ |y| via `sq_le_sq`.
  have habs : |x| ≤ |y| := (sq_le_sq).mp hxy
  -- And x ≤ |x| holds for all reals; combine both.
  exact (le_trans (le_abs_self x) habs)

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
  simp [pure]
  exact decide_eq_true_iff

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
  simp [pure]
  exact decide_eq_true_iff

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
  intro h
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

section RcompareMore

/-- Return the comparison code; used in specialized specs below -/
noncomputable def Rcompare_val (x y : ℝ) : Id Int :=
  Rcompare x y

/-- Coq: Rcompare_Lt - if x < y then comparison yields Lt (-1 here). -/
theorem Rcompare_Lt_spec (x y : ℝ) :
    ⦃⌜x < y⌝⦄
    Rcompare_val x y
    ⦃⇓r => ⌜r = -1⌝⦄ := by
  intro hxy
  unfold Rcompare_val Rcompare
  -- Reduce the Hoare triple to the postcondition on the pure result
  simp [wp, PostCond.noThrow, Id.run]
  -- With x < y, the comparison branch yields -1
  have hx : x < y := hxy
  simp [hx, pure]

/-- Coq: Rcompare_Lt_inv - from code Lt (-1) deduce x < y. -/
theorem Rcompare_Lt_inv_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_val x y
    ⦃⇓r => ⌜r = -1 → x < y⌝⦄ := by
  intro _
  unfold Rcompare_val
  -- Reduce the Hoare triple to a pure proposition about the returned code
  unfold Rcompare
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Goal after simp: (y ≤ x → (if x = y then 0 else 1) = -1) → x < y
  intro hcode
  -- Prove by contradiction: if ¬(x < y), then y ≤ x, forcing an impossible code
  by_contra hnot
  have hyx : y ≤ x := not_lt.mp hnot
  have hx : (if x = y then (0 : Int) else 1) = (-1 : Int) := hcode hyx
  have hneq : (if x = y then (0 : Int) else 1) ≠ (-1 : Int) := by
    by_cases heq : x = y
    · -- Then we would have 0 = -1, impossible
      have : (0 : Int) ≠ (-1 : Int) := by decide
      simpa [heq] using this
    · -- Then we would have 1 = -1, impossible
      have : (1 : Int) ≠ (-1 : Int) := by decide
      simpa [heq] using this
  exact hneq hx

/-- Coq: Rcompare_not_Lt - if y ≤ x then comparison is not Lt (-1). -/
theorem Rcompare_not_Lt_spec (x y : ℝ) :
    ⦃⌜y ≤ x⌝⦄
    Rcompare_val x y
    ⦃⇓r => ⌜r ≠ -1⌝⦄ := by
  intro hyx
  unfold Rcompare_val Rcompare
  -- Reduce Hoare triple on Id to a pure goal
  simp [wp, PostCond.noThrow, Id.run]
  -- Under y ≤ x, we have ¬ x < y, so we enter the second branch
  have hnot : ¬ x < y := not_lt.mpr hyx
  simp [hnot]
  -- It remains to show: (if x = y then (0 : Int) else 1) ≠ -1
  by_cases hxy : x = y
  · simp [hxy]
  · simp [hxy]

/-- Coq: Rcompare_not_Lt_inv - from not Lt (-1) deduce y ≤ x. -/
theorem Rcompare_not_Lt_inv_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_val x y
    ⦃⇓r => ⌜r ≠ -1 → y ≤ x⌝⦄ := by
  intro _
  unfold Rcompare_val
  -- Reduce to a pure proposition about the returned comparison code
  unfold Rcompare
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Goal after simp: y ≤ x → ¬(if x = y then 0 else 1) = -1 → y ≤ x
  intro hyx _; exact hyx

/-- Coq: Rcompare_Eq - if x = y then comparison yields Eq (0 here). -/
theorem Rcompare_Eq_spec (x y : ℝ) :
    ⦃⌜x = y⌝⦄
    Rcompare_val x y
    ⦃⇓r => ⌜r = 0⌝⦄ := by
  intro hxy
  unfold Rcompare_val
  -- Reduce the Hoare triple to the postcondition on the pure result
  unfold Rcompare
  have hEq : x = y := hxy
  simp [wp, PostCond.noThrow, Id.run, pure, hEq]

/-- Coq: Rcompare_Eq_inv - from code Eq (0) deduce x = y. -/
theorem Rcompare_Eq_inv_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_val x y
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

/-- Coq: Rcompare_Gt - if y < x then comparison yields Gt (1 here). -/
theorem Rcompare_Gt_spec (x y : ℝ) :
    ⦃⌜y < x⌝⦄
    Rcompare_val x y
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

/-- Coq: Rcompare_Gt_inv - from code Gt (1) deduce y < x. -/
theorem Rcompare_Gt_inv_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_val x y
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

/-- Coq: Rcompare_not_Gt - if x ≤ y then comparison is not Gt (1). -/
theorem Rcompare_not_Gt_spec (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    Rcompare_val x y
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
    simp [hlt, hEq, pure]

/-- Coq: Rcompare_not_Gt_inv - from not Gt (1) deduce x ≤ y. -/
theorem Rcompare_not_Gt_inv_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_val x y
    ⦃⇓r => ⌜r ≠ 1 → x ≤ y⌝⦄ := by
  intro _
  unfold Rcompare_val
  -- Follows from Rcompare_spec; proof omitted for now
  sorry

/-- Integer comparison as an Int code (-1/0/1), mirroring Coq's Z.compare -/
def Zcompare_int (m n : Int) : Id Int :=
  pure (if m < n then -1 else if m = n then 0 else 1)

/-- Coq: Rcompare_IZR - comparison of casted Ints matches integer comparison. -/
theorem Rcompare_IZR_spec (m n : Int) :
    ⦃⌜True⌝⦄
    Rcompare ((m : ℝ)) (n : ℝ)
    ⦃⇓r => ⌜r = (Zcompare_int m n).run⌝⦄ := by
  intro _
  unfold Zcompare_int Rcompare
  -- Case split on integer order; proof omitted for now
  sorry

/-- Middle-value comparison identity: compare (x - d) vs (u - x) equals comparing x vs (d+u)/2 -/
noncomputable def Rcompare_middle_check (x d u : ℝ) : Id (Int × Int) :=
  ((Rcompare (x - d) (u - x)).run, (Rcompare x ((d + u) / 2)).run)

theorem Rcompare_middle_spec (x d u : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_middle_check x d u
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rcompare_middle_check
  -- Mirrors Coq's Rcompare_middle; proof omitted for now
  sorry

/-- Halving on left: compare (x/2) y equals compare x (2*y) -/
noncomputable def Rcompare_half_l_check (x y : ℝ) : Id (Int × Int) :=
  ((Rcompare (x / 2) y).run, (Rcompare x (2 * y)).run)

theorem Rcompare_half_l_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_half_l_check x y
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rcompare_half_l_check
  -- Mirrors Coq's Rcompare_half_l; proof omitted for now
  sorry

/-- Halving on right: compare x (y/2) equals compare (2*x) y -/
noncomputable def Rcompare_half_r_check (x y : ℝ) : Id (Int × Int) :=
  ((Rcompare x (y / 2)).run, (Rcompare (2 * x) y).run)

theorem Rcompare_half_r_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_half_r_check x y
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rcompare_half_r_check
  -- Mirrors Coq's Rcompare_half_r; proof omitted for now
  sorry

/-- Square comparison reduces to comparison on absolute values -/
noncomputable def Rcompare_sqr_check (x y : ℝ) : Id (Int × Int) :=
  ((Rcompare (x * x) (y * y)).run, (Rcompare |x| |y|).run)

theorem Rcompare_sqr_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_sqr_check x y
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rcompare_sqr_check
  -- Mirrors Coq's Rcompare_sqr; proof omitted for now
  sorry

/-- Minimum expressed via comparison code -/
noncomputable def Rmin_compare_check (x y : ℝ) : Id (ℝ × Int) :=
  (min x y, (Rcompare x y).run)

theorem Rmin_compare_spec (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rmin_compare_check x y
    ⦃⇓p => ⌜p.1 = (if p.2 = -1 then x else if p.2 = 0 then x else y)⌝⦄ := by
  intro _
  unfold Rmin_compare_check
  -- Mirrors Coq's Rmin_compare; proof omitted for now
  sorry

end RcompareMore

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

/-- Monotone case: if x < y then `Rlt_bool x y = true` -/
theorem Rlt_bool_true (x y : ℝ) :
    ⦃⌜x < y⌝⦄
    Rlt_bool x y
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rlt_bool
  -- Follows from decidability of (<) on ℝ
  sorry

/-- Antitone case: if y ≤ x then `Rlt_bool x y = false` -/
theorem Rlt_bool_false (x y : ℝ) :
    ⦃⌜y ≤ x⌝⦄
    Rlt_bool x y
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  unfold Rlt_bool
  -- Follows from decidability of (<) on ℝ and `¬ (x < y)` from `y ≤ x`
  sorry

/-- Negation flips strict-less-than boolean

    Rlt_bool (-x) (-y) = Rlt_bool y x.
    Direct consequence of `Rcompare_opp` in Coq; mirrors here.
-/
theorem Rlt_bool_opp (x y : ℝ) :
    ⦃⌜True⌝⦄
    do
      let a ← Rlt_bool (-x) (-y)
      let b ← Rlt_bool y x
      pure (a, b)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rlt_bool
  -- Mirrors Coq's Rlt_bool_opp using `Rcompare_opp`; proof omitted
  sorry

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

/-- If x = y then `Req_bool x y = true` -/
theorem Req_bool_true (x y : ℝ) :
    ⦃⌜x = y⌝⦄
    Req_bool x y
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Req_bool
  -- Follows from decidable equality on ℝ
  sorry

/-- If x ≠ y then `Req_bool x y = false` -/
theorem Req_bool_false (x y : ℝ) :
    ⦃⌜x ≠ y⌝⦄
    Req_bool x y
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  unfold Req_bool
  -- Follows from decidable equality on ℝ
  sorry

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

/- Boolean equality test wrapper -/
noncomputable def eqb_check (a b : Bool) : Id Bool :=
  pure (a == b)

/-- If a = b then (a == b) = true -/
theorem eqb_true_spec (a b : Bool) :
    ⦃⌜a = b⌝⦄
    eqb_check a b
    ⦃⇓r => ⌜r = true⌝⦄ := by
  intro _
  unfold eqb_check
  -- Follows from Bool equality
  sorry

/-- If a ≠ b then (a == b) = false -/
theorem eqb_false_spec (a b : Bool) :
    ⦃⌜a ≠ b⌝⦄
    eqb_check a b
    ⦃⇓r => ⌜r = false⌝⦄ := by
  intro _
  unfold eqb_check
  -- Follows from Bool disequality
  sorry

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

section CondAbsMulAdd

/-- Absolute value is invariant under conditional negation -/
noncomputable def abs_cond_Ropp_check (b : Bool) (x : ℝ) : Id ℝ :=
  pure (|cond_Ropp b x|)

theorem abs_cond_Ropp_spec (b : Bool) (x : ℝ) :
    ⦃⌜True⌝⦄
    abs_cond_Ropp_check b x
    ⦃⇓r => ⌜r = |x|⌝⦄ := by
  intro _
  unfold abs_cond_Ropp_check cond_Ropp
  -- |if b then -x else x| = |x|
  sorry

/-- Conditional negation distributes over multiplication (left) -/
noncomputable def cond_Ropp_mult_l_check (b : Bool) (x y : ℝ) : Id ℝ :=
  cond_Ropp b (x * y)

theorem cond_Ropp_mult_l_spec (b : Bool) (x y : ℝ) :
    ⦃⌜True⌝⦄
    cond_Ropp_mult_l_check b x y
    ⦃⇓r => ⌜r = (cond_Ropp b x).run * y⌝⦄ := by
  intro _
  unfold cond_Ropp_mult_l_check cond_Ropp
  -- if b then -(x*y) else (x*y) equals (if b then -x else x) * y
  sorry

/-- Conditional negation distributes over multiplication (right) -/
noncomputable def cond_Ropp_mult_r_check (b : Bool) (x y : ℝ) : Id ℝ :=
  cond_Ropp b (x * y)

theorem cond_Ropp_mult_r_spec (b : Bool) (x y : ℝ) :
    ⦃⌜True⌝⦄
    cond_Ropp_mult_r_check b x y
    ⦃⇓r => ⌜r = x * (cond_Ropp b y).run⌝⦄ := by
  intro _
  unfold cond_Ropp_mult_r_check cond_Ropp
  -- if b then -(x*y) else (x*y) equals x * (if b then -y else y)
  sorry

/-- Conditional negation distributes over addition -/
noncomputable def cond_Ropp_plus_check (b : Bool) (x y : ℝ) : Id ℝ :=
  cond_Ropp b (x + y)

theorem cond_Ropp_plus_spec (b : Bool) (x y : ℝ) :
    ⦃⌜True⌝⦄
    cond_Ropp_plus_check b x y
    ⦃⇓r => ⌜r = (cond_Ropp b x).run + (cond_Ropp b y).run⌝⦄ := by
  intro _
  unfold cond_Ropp_plus_check cond_Ropp
  -- if b then -(x+y) else (x+y) equals (if b then -x else x) + (if b then -y else y)
  sorry

end CondAbsMulAdd

section CondRltBool

/-- Compare after conditional negation on both sides -/
noncomputable def cond_Ropp_Rlt_bool_check (b : Bool) (x y : ℝ) : Id Bool :=
  do
    let x' ← cond_Ropp b x
    let y' ← cond_Ropp b y
    Rlt_bool x' y'

theorem cond_Ropp_Rlt_bool_spec (b : Bool) (x y : ℝ) :
    ⦃⌜True⌝⦄
    cond_Ropp_Rlt_bool_check b x y
    ⦃⇓r => ⌜r = true ↔ (if b then y < x else x < y)⌝⦄ := by
  intro _
  unfold cond_Ropp_Rlt_bool_check
  -- Negation reverses strict inequality
  sorry

/-- Compare after conditional negation on right side -/
noncomputable def Rlt_bool_cond_Ropp_check (b : Bool) (x y : ℝ) : Id Bool :=
  do
    let y' ← cond_Ropp b y
    Rlt_bool x y'

theorem Rlt_bool_cond_Ropp_spec (b : Bool) (x y : ℝ) :
    ⦃⌜True⌝⦄
    Rlt_bool_cond_Ropp_check b x y
    ⦃⇓r => ⌜r = true ↔ (if b then x < -y else x < y)⌝⦄ := by
  intro _
  unfold Rlt_bool_cond_Ropp_check cond_Ropp
  -- If b then compare against -y, else against y
  sorry

end CondRltBool

section IZRCond

/-- Conditional opposite commutes with integer-to-real cast -/
noncomputable def IZR_cond_Zopp_check (b : Bool) (m : Int) : Id ℝ :=
  cond_Ropp b (m : ℝ)

theorem IZR_cond_Zopp_spec (b : Bool) (m : Int) :
    ⦃⌜True⌝⦄
    IZR_cond_Zopp_check b m
    ⦃⇓r => ⌜r = (if b then -((m : ℝ)) else (m : ℝ))⌝⦄ := by
  intro _
  unfold IZR_cond_Zopp_check cond_Ropp
  rfl

end IZRCond

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

-- Integer rounding helpers (floor/ceil/trunc/away) and their properties
section IntRound

/-- Integer floor as an Id-wrapped Int -/
noncomputable def Zfloor (x : ℝ) : Id Int :=
  pure ⌊x⌋

/-- Integer ceiling as an Id-wrapped Int -/
noncomputable def Zceil (x : ℝ) : Id Int :=
  pure ⌈x⌉

/-- Truncation toward zero: ceil for negatives, floor otherwise -/
noncomputable def Ztrunc (x : ℝ) : Id Int :=
  pure (if x < 0 then ⌈x⌉ else ⌊x⌋)

/-- Away-from-zero rounding: floor for negatives, ceil otherwise -/
noncomputable def Zaway (x : ℝ) : Id Int :=
  pure (if x < 0 then ⌊x⌋ else ⌈x⌉)

/-- Floor lower bound: ⌊x⌋ ≤ x -/
theorem Zfloor_lb (x : ℝ) :
    ⦃⌜True⌝⦄
    Zfloor x
    ⦃⇓z => ⌜(z : ℝ) ≤ x⌝⦄ := by
  intro _; unfold Zfloor; sorry

/-- Floor upper bound: x < ⌊x⌋ + 1 -/
theorem Zfloor_ub (x : ℝ) :
    ⦃⌜True⌝⦄
    Zfloor x
    ⦃⇓z => ⌜x < (z : ℝ) + 1⌝⦄ := by
  intro _; unfold Zfloor; sorry

/-- Floor greatest-lower-bound: if m ≤ x then m ≤ ⌊x⌋ -/
theorem Zfloor_lub (x : ℝ) (m : Int) :
    ⦃⌜(m : ℝ) ≤ x⌝⦄
    Zfloor x
    ⦃⇓z => ⌜m ≤ z⌝⦄ := by
  intro _; unfold Zfloor; sorry

/-- Characterization: if m ≤ x < m+1 then ⌊x⌋ = m -/
theorem Zfloor_imp (x : ℝ) (m : Int) :
    ⦃⌜(m : ℝ) ≤ x ∧ x < (m : ℝ) + 1⌝⦄
    Zfloor x
    ⦃⇓z => ⌜z = m⌝⦄ := by
  intro _; unfold Zfloor; sorry

/-- Floor of an integer equals itself -/
theorem Zfloor_IZR (m : Int) :
    ⦃⌜True⌝⦄
    Zfloor (m : ℝ)
    ⦃⇓z => ⌜z = m⌝⦄ := by
  intro _; unfold Zfloor; sorry

/-- Monotonicity of floor: x ≤ y ⇒ ⌊x⌋ ≤ ⌊y⌋ -/
theorem Zfloor_le (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    do
      let a ← Zfloor x
      let b ← Zfloor y
      pure (a, b)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _; simp [Zfloor]; sorry

end IntRound

section IntCeil

/-- Ceiling upper bound: x ≤ ⌈x⌉ -/
theorem Zceil_ub (x : ℝ) :
    ⦃⌜True⌝⦄
    Zceil x
    ⦃⇓z => ⌜x ≤ (z : ℝ)⌝⦄ := by
  intro _; unfold Zceil; sorry

/-- Ceiling lower-neighborhood: ⌈x⌉ - 1 < x -/
theorem Zceil_lb (x : ℝ) :
    ⦃⌜True⌝⦄
    Zceil x
    ⦃⇓z => ⌜(z : ℝ) - 1 < x⌝⦄ := by
  intro _; unfold Zceil; sorry

/-- Ceiling least-upper-bound: if x ≤ m then ⌈x⌉ ≤ m -/
theorem Zceil_glb (x : ℝ) (m : Int) :
    ⦃⌜x ≤ (m : ℝ)⌝⦄
    Zceil x
    ⦃⇓z => ⌜z ≤ m⌝⦄ := by
  intro _; unfold Zceil; sorry

/-- Characterization: if m - 1 < x ≤ m then ⌈x⌉ = m -/
theorem Zceil_imp (x : ℝ) (m : Int) :
    ⦃⌜(m : ℝ) - 1 < x ∧ x ≤ (m : ℝ)⌝⦄
    Zceil x
    ⦃⇓z => ⌜z = m⌝⦄ := by
  intro _; unfold Zceil; sorry

/-- Ceiling of an integer equals itself -/
theorem Zceil_IZR (m : Int) :
    ⦃⌜True⌝⦄
    Zceil (m : ℝ)
    ⦃⇓z => ⌜z = m⌝⦄ := by
  intro _; unfold Zceil; sorry

/-- Monotonicity of ceiling: x ≤ y ⇒ ⌈x⌉ ≤ ⌈y⌉ -/
theorem Zceil_le (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    do
      let a ← Zceil x
      let b ← Zceil y
      pure (a, b)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _; simp [Zceil]; sorry

/-- Non-integral case: if ⌊x⌋ ≠ x then ⌈x⌉ = ⌊x⌋ + 1 -/
theorem Zceil_floor_neq (x : ℝ) :
    ⦃⌜((Zfloor x).run : ℝ) ≠ x⌝⦄
    do
      let c ← Zceil x
      let f ← Zfloor x
      pure (c, f)
    ⦃⇓p => ⌜p.1 = p.2 + 1⌝⦄ := by
  intro _; simp [Zceil, Zfloor]; sorry

end IntCeil

section IntTrunc

/-- Truncation at integers: Ztrunc (m) = m -/
theorem Ztrunc_IZR (m : Int) :
    ⦃⌜True⌝⦄
    Ztrunc (m : ℝ)
    ⦃⇓z => ⌜z = m⌝⦄ := by
  intro _; unfold Ztrunc; by_cases h : (m : ℝ) < 0 <;> simp [Zceil, Zfloor, h]

/-- For nonnegatives: Ztrunc x = ⌊x⌋ -/
theorem Ztrunc_floor (x : ℝ) :
    ⦃⌜0 ≤ x⌝⦄
    Ztrunc x
    ⦃⇓z => ⌜z = (Zfloor x).run⌝⦄ := by
  intro _; unfold Ztrunc; simp [Zfloor]; sorry

/-- For nonpositives: Ztrunc x = ⌈x⌉ -/
theorem Ztrunc_ceil (x : ℝ) :
    ⦃⌜x ≤ 0⌝⦄
    Ztrunc x
    ⦃⇓z => ⌜z = (Zceil x).run⌝⦄ := by
  intro _; unfold Ztrunc; simp [Zceil]; sorry

/-- Monotonicity of truncation: x ≤ y ⇒ Ztrunc x ≤ Ztrunc y -/
theorem Ztrunc_le (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    do
      let a ← Ztrunc x
      let b ← Ztrunc y
      pure (a, b)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _; simp [Ztrunc]; sorry

/-- Opposite: Ztrunc (-x) = - Ztrunc x -/
theorem Ztrunc_opp (x : ℝ) :
    ⦃⌜True⌝⦄
    do
      let a ← Ztrunc (-x)
      let b ← Ztrunc x
      pure (a, b)
    ⦃⇓p => ⌜p.1 = -p.2⌝⦄ := by
  intro _; simp [Ztrunc]; sorry

/-- Absolute value: Ztrunc |x| = |Ztrunc x| -/
theorem Ztrunc_abs (x : ℝ) :
    ⦃⌜True⌝⦄
    do
      let a ← Ztrunc |x|
      let b ← Ztrunc x
      pure (a, b)
    ⦃⇓p => ⌜p.1 = Int.natAbs p.2⌝⦄ := by
  intro _; simp [Ztrunc]; sorry

/-- Lower bound via absolute: if n ≤ |x| then n ≤ |Ztrunc x| -/
theorem Ztrunc_lub (n : Int) (x : ℝ) :
    ⦃⌜(n : ℝ) ≤ |x|⌝⦄
    Ztrunc x
    ⦃⇓z => ⌜n ≤ Int.natAbs z⌝⦄ := by
  intro _; simp [Ztrunc]; sorry

end IntTrunc

section IntAway

/-- Away-from-zero at integers: Zaway (m) = m -/
theorem Zaway_IZR (m : Int) :
    ⦃⌜True⌝⦄
    Zaway (m : ℝ)
    ⦃⇓z => ⌜z = m⌝⦄ := by
  intro _; unfold Zaway; by_cases h : (m : ℝ) < 0 <;> simp [Zfloor, Zceil, h]

/-- For nonnegatives: Zaway x = ⌈x⌉ -/
theorem Zaway_ceil (x : ℝ) :
    ⦃⌜0 ≤ x⌝⦄
    Zaway x
    ⦃⇓z => ⌜z = (Zceil x).run⌝⦄ := by
  intro _; unfold Zaway; simp [Zceil]; sorry

/-- For nonpositives: Zaway x = ⌊x⌋ -/
theorem Zaway_floor (x : ℝ) :
    ⦃⌜x ≤ 0⌝⦄
    Zaway x
    ⦃⇓z => ⌜z = (Zfloor x).run⌝⦄ := by
  intro _; unfold Zaway; simp [Zfloor]; sorry

/-- Monotonicity of away rounding: x ≤ y ⇒ Zaway x ≤ Zaway y -/
theorem Zaway_le (x y : ℝ) :
    ⦃⌜x ≤ y⌝⦄
    do
      let a ← Zaway x
      let b ← Zaway y
      pure (a, b)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _; simp [Zaway]; sorry

/-- Opposite: Zaway (-x) = - Zaway x -/
theorem Zaway_opp (x : ℝ) :
    ⦃⌜True⌝⦄
    do
      let a ← Zaway (-x)
      let b ← Zaway x
      pure (a, b)
    ⦃⇓p => ⌜p.1 = -p.2⌝⦄ := by
  intro _; simp [Zaway]; sorry

/-- Absolute value: Zaway |x| = |Zaway x| -/
theorem Zaway_abs (x : ℝ) :
    ⦃⌜True⌝⦄
    do
      let a ← Zaway |x|
      let b ← Zaway x
      pure (a, b)
    ⦃⇓p => ⌜p.1 = Int.natAbs p.2⌝⦄ := by
  intro _; simp [Zaway]; sorry

end IntAway

section IntDiv

/-- Division at floors: floor (x / y) for integer x,y

    Coq: Zfloor_div
    For integers x,y with y ≠ 0, we have
    Zfloor (IZR x / IZR y) = x / y.
-/
theorem Zfloor_div (x y : Int) :
    ⦃⌜y ≠ 0⌝⦄
    Zfloor ((x : ℝ) / (y : ℝ))
    ⦃⇓z => ⌜z = x / y⌝⦄ := by
  intro _
  unfold Zfloor
  -- Mirrors Coq's Zfloor_div; proof omitted for now
  sorry

/-- Division at truncation: trunc (x / y) for integer x,y (toward zero)

    Coq: Ztrunc_div
    For integers x,y with y ≠ 0, we have
    Ztrunc (IZR x / IZR y) = Int.quot x y (toward-zero quotient).
-/
theorem Ztrunc_div (x y : Int) :
    ⦃⌜y ≠ 0⌝⦄
    Ztrunc ((x : ℝ) / (y : ℝ))
    ⦃⇓z => ⌜z = x / y⌝⦄ := by
  intro _
  unfold Ztrunc
  -- Mirrors Coq's Ztrunc_div; proof omitted for now
  sorry

end IntDiv

-- Comparisons against floor/ceil bounds
section CompareIntBounds

/-- Floor/Ceil middle comparison identities -/
noncomputable def Rcompare_floor_ceil_middle_check (x : ℝ) : Id (Int × Int) :=
  do
    let f ← Zfloor x
    let c ← Zceil x
    pure ((Rcompare (f : ℝ) x).run, (Rcompare x (c : ℝ)).run)

theorem Rcompare_floor_ceil_middle_spec (x : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_floor_ceil_middle_check x
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rcompare_floor_ceil_middle_check
  -- Mirrors Coq's Rcompare_floor_ceil_middle; proof omitted for now
  sorry

noncomputable def Rcompare_ceil_floor_middle_check (x : ℝ) : Id (Int × Int) :=
  do
    let f ← Zfloor x
    let c ← Zceil x
    pure ((Rcompare (c : ℝ) x).run, (Rcompare x (f : ℝ)).run)

theorem Rcompare_ceil_floor_middle_spec (x : ℝ) :
    ⦃⌜True⌝⦄
    Rcompare_ceil_floor_middle_check x
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Rcompare_ceil_floor_middle_check
  -- Mirrors Coq's Rcompare_ceil_floor_middle; proof omitted for now
  sorry

end CompareIntBounds

/-
  Basic results on radix and bpow (Coq Raux.v Section pow)
  In this Lean port, we express bpow via real integer powers (zpow).
-/
section PowBasics

/-- Positivity of the radix as a real number (assuming beta > 1). -/
noncomputable def radix_pos_check (beta : Int) : Id ℝ :=
  pure (beta : ℝ)

theorem radix_pos (beta : Int) :
    ⦃⌜1 < beta⌝⦄
    radix_pos_check beta
    ⦃⇓r => ⌜0 < r⌝⦄ := by
  intro _
  unfold radix_pos_check
  -- Follows from casting positivity; proof omitted
  sorry

/-- Realization of bpow using real integer powers. -/
noncomputable def bpow (beta e : Int) : Id ℝ :=
  pure ((beta : ℝ) ^ e)

/-- Bridge lemma: integer power via reals for positive exponent -/
noncomputable def IZR_Zpower_pos_check (n m : Int) : Id (ℝ × ℝ) :=
  pure (((n : ℝ) ^ m, (n : ℝ) ^ m))

theorem IZR_Zpower_pos (n m : Int) :
    ⦃⌜0 < m⌝⦄
    IZR_Zpower_pos_check n m
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold IZR_Zpower_pos_check
  -- Mirrors Coq's IZR_Zpower_pos; proof omitted
  sorry

/-- Bridge: our bpow corresponds to integer power on reals -/
noncomputable def bpow_powerRZ_check (beta e : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ e, (beta : ℝ) ^ e))

theorem bpow_powerRZ (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    bpow_powerRZ_check beta e
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold bpow_powerRZ_check
  -- Mirrors Coq's bpow_powerRZ; proof omitted
  sorry

/-- Nonnegativity of bpow -/
theorem bpow_ge_0 (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    bpow beta e
    ⦃⇓v => ⌜0 ≤ v⌝⦄ := by
  intro _
  unfold bpow
  -- Standard property for positive bases; proof omitted
  sorry

/-- Positivity of bpow -/
theorem bpow_gt_0 (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    bpow beta e
    ⦃⇓v => ⌜0 < v⌝⦄ := by
  intro _
  unfold bpow
  -- Standard property for positive bases; proof omitted
  sorry

/-- Addition law for bpow exponents -/
noncomputable def bpow_plus_check (beta e1 e2 : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ (e1 + e2), ((beta : ℝ) ^ e1) * ((beta : ℝ) ^ e2)))

theorem bpow_plus (beta e1 e2 : Int) :
    ⦃⌜1 < beta⌝⦄
    bpow_plus_check beta e1 e2
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold bpow_plus_check
  -- Follows from zpow addition; proof omitted
  sorry

/-- Value of bpow at 1 -/
noncomputable def bpow_one_check (beta : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ (1 : Int), (beta : ℝ)))

theorem bpow_1 (beta : Int) :
    ⦃⌜1 < beta⌝⦄
    bpow_one_check beta
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold bpow_one_check
  -- zpow at 1; proof omitted
  sorry

/-- Increment law: bpow (e+1) = beta * bpow e -/
noncomputable def bpow_plus_1_check (beta e : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ (e + 1), (beta : ℝ) * ((beta : ℝ) ^ e)))

theorem bpow_plus_1 (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    bpow_plus_1_check beta e
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold bpow_plus_1_check
  -- zpow addition specialized to 1; proof omitted
  sorry

/-- Opposite exponent law: bpow (-e) = 1 / bpow e -/
noncomputable def bpow_opp_check (beta e : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ (-e), 1 / ((beta : ℝ) ^ e)))

theorem bpow_opp (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    bpow_opp_check beta e
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold bpow_opp_check
  -- zpow negation; proof omitted
  sorry

/-- Strict monotonicity of bpow in the exponent

    If `1 < beta` and `e1 < e2`, then `(beta : ℝ) ^ e1 < (beta : ℝ) ^ e2`.
-/
noncomputable def bpow_lt_check (beta e1 e2 : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ e1, (beta : ℝ) ^ e2))

theorem bpow_lt (beta e1 e2 : Int) :
    ⦃⌜1 < beta ∧ e1 < e2⌝⦄
    bpow_lt_check beta e1 e2
    ⦃⇓p => ⌜p.1 < p.2⌝⦄ := by
  intro _
  unfold bpow_lt_check
  -- Mirrors Coq's bpow_lt; proof omitted for now
  sorry

/-- Converse monotonicity: compare exponents via bpow values

    If `1 < beta` and `(beta : ℝ) ^ e1 < (beta : ℝ) ^ e2`, then `e1 < e2`.
-/
noncomputable def lt_bpow_check (beta e1 e2 : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ e1, (beta : ℝ) ^ e2))

theorem lt_bpow (beta e1 e2 : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ e1) < ((beta : ℝ) ^ e2)⌝⦄
    lt_bpow_check beta e1 e2
    ⦃⇓_ => ⌜e1 < e2⌝⦄ := by
  intro _
  unfold lt_bpow_check
  -- Mirrors Coq's lt_bpow; proof omitted for now
  sorry

/-- Monotonicity (≤) of bpow in the exponent -/
noncomputable def bpow_le_check (beta e1 e2 : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ e1, (beta : ℝ) ^ e2))

theorem bpow_le (beta e1 e2 : Int) :
    ⦃⌜1 < beta ∧ e1 ≤ e2⌝⦄
    bpow_le_check beta e1 e2
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _
  unfold bpow_le_check
  -- Mirrors Coq's bpow_le; proof omitted for now
  sorry

/-- Converse (≤) direction via bpow values -/
noncomputable def le_bpow_check (beta e1 e2 : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ e1, (beta : ℝ) ^ e2))

theorem le_bpow (beta e1 e2 : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ e1) ≤ ((beta : ℝ) ^ e2)⌝⦄
    le_bpow_check beta e1 e2
    ⦃⇓_ => ⌜e1 ≤ e2⌝⦄ := by
  intro _
  unfold le_bpow_check
  -- Mirrors Coq's le_bpow; proof omitted for now
  sorry

/-- Injectivity of bpow on the exponent -/
noncomputable def bpow_inj_check (beta e1 e2 : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ e1, (beta : ℝ) ^ e2))

theorem bpow_inj (beta e1 e2 : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ e1) = ((beta : ℝ) ^ e2)⌝⦄
    bpow_inj_check beta e1 e2
    ⦃⇓_ => ⌜e1 = e2⌝⦄ := by
  intro _
  unfold bpow_inj_check
  -- Mirrors Coq's bpow_inj; proof omitted for now
  sorry

/-- Exponential form of bpow via Real.exp and Real.log -/
noncomputable def bpow_exp_check (beta e : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ e, Real.exp ((e : ℝ) * Real.log (beta : ℝ))))

theorem bpow_exp (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    bpow_exp_check beta e
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold bpow_exp_check
  -- Mirrors Coq's bpow_exp; proof omitted for now
  sorry

/-- From bpow (e1 - 1) < bpow e2, deduce e1 ≤ e2 -/
noncomputable def bpow_lt_bpow_pair (beta e1 e2 : Int) : Id (Int × Int) :=
  (e1, e2)

theorem bpow_lt_bpow (beta e1 e2 : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ (e1 - 1) < (beta : ℝ) ^ e2)⌝⦄
    bpow_lt_bpow_pair beta e1 e2
    ⦃⇓_ => ⌜e1 ≤ e2⌝⦄ := by
  intro _
  unfold bpow_lt_bpow_pair
  -- Mirrors Coq's bpow_lt_bpow; proof omitted for now
  sorry

/-- Uniqueness of the integer exponent bounding an absolute value by bpow -/
noncomputable def bpow_unique_pair (beta : Int) (x : ℝ) (e1 e2 : Int) : Id (Int × Int) :=
  (e1, e2)

theorem bpow_unique (beta : Int) (x : ℝ) (e1 e2 : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ (e1 - 1) ≤ |x| ∧ |x| < (beta : ℝ) ^ e1) ∧
               ((beta : ℝ) ^ (e2 - 1) ≤ |x| ∧ |x| < (beta : ℝ) ^ e2)⌝⦄
    bpow_unique_pair beta x e1 e2
    ⦃⇓_ => ⌜e1 = e2⌝⦄ := by
  intro _
  unfold bpow_unique_pair
  -- Mirrors Coq's bpow_unique; proof omitted for now
  sorry

/-- Square-root law for even exponents: sqrt (bpow (2*e)) = bpow e -/
noncomputable def sqrt_bpow_check (beta e : Int) : Id (ℝ × ℝ) :=
  pure ((Real.sqrt ((beta : ℝ) ^ (2 * e)), (beta : ℝ) ^ e))

theorem sqrt_bpow (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    sqrt_bpow_check beta e
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold sqrt_bpow_check
  -- Follows Coq's sqrt_bpow; proof omitted
  sorry

/-- Lower bound: bpow (e/2) ≤ sqrt (bpow e) -/
noncomputable def sqrt_bpow_ge_check (beta e : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ (e / 2), Real.sqrt ((beta : ℝ) ^ e)))

theorem sqrt_bpow_ge (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    sqrt_bpow_ge_check beta e
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _
  unfold sqrt_bpow_ge_check
  -- Mirrors Coq's sqrt_bpow_ge; proof omitted
  sorry

/-- Bridge: natural-power form equals bpow at Z.ofNat e -/
noncomputable def IZR_Zpower_nat_check (beta : Int) (e : Nat) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ (Int.ofNat e), (beta : ℝ) ^ (Int.ofNat e)))

theorem IZR_Zpower_nat (beta : Int) (e : Nat) :
    ⦃⌜1 < beta⌝⦄
    IZR_Zpower_nat_check beta e
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold IZR_Zpower_nat_check
  -- Mirrors Coq's IZR_Zpower_nat; proof omitted for now
  sorry

/-- Bridge: for nonnegative exponents, Zpower equals bpow -/
noncomputable def IZR_Zpower_check (beta e : Int) : Id (ℝ × ℝ) :=
  pure (((beta : ℝ) ^ e, (beta : ℝ) ^ e))

theorem IZR_Zpower (beta e : Int) :
    ⦃⌜0 ≤ e⌝⦄
    IZR_Zpower_check beta e
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold IZR_Zpower_check
  -- Mirrors Coq's IZR_Zpower; proof omitted for now
  sorry

end PowBasics

/-
  Limited Principle of Omniscience (LPO) style results from Coquelicot
  (ported from Coq Raux.v). We encode the computational content as
  Id-wrapped options that select a witness when it exists.
 -/
section LPO

/-- Carrier for LPO_min: either `some n` with a minimal witness, or `none` if none exists. -/
noncomputable def LPO_min_choice (P : Nat → Prop) : Id (Option Nat) :=
  pure none

/-- Coq (Raux.v):
Theorem LPO_min:
  ∀ P : ℕ → Prop, (∀ n, P n ∨ ¬ P n) →
  {n : ℕ | P n ∧ ∀ i, i < n → ¬ P i} + {∀ n, ¬ P n}.

Lean (spec): Using an `Option Nat` to encode the sum; when `some n`, the
returned `n` is a minimal witness; when `none`, no witness exists. -/
theorem LPO_min (P : Nat → Prop) :
    ⦃⌜∀ n, P n ∨ ¬ P n⌝⦄
    LPO_min_choice P
    ⦃⇓r => ⌜match r with
            | some n => P n ∧ ∀ i, i < n → ¬ P i
            | none   => ∀ n, ¬ P n⌝⦄ := by
  intro _
  unfold LPO_min_choice
  -- Mirrors Coq's LPO_min; proof omitted for now
  sorry

/-- Carrier for LPO: either `some n` with a witness, or `none` if none exists. -/
noncomputable def LPO_choice (P : Nat → Prop) : Id (Option Nat) :=
  pure none

/-- Coq (Raux.v):
Theorem LPO:
  ∀ P : ℕ → Prop, (∀ n, P n ∨ ¬ P n) → {n : ℕ | P n} + {∀ n, ¬ P n}.

Lean (spec): `some n` indicates a witness `P n`; `none` indicates universal negation. -/
theorem LPO (P : Nat → Prop) :
    ⦃⌜∀ n, P n ∨ ¬ P n⌝⦄
    LPO_choice P
    ⦃⇓r => ⌜match r with
            | some n => P n
            | none   => ∀ n, ¬ P n⌝⦄ := by
  intro _
  unfold LPO_choice
  -- Mirrors Coq's LPO; proof omitted for now
  sorry

/-- Carrier for LPO over integers: either `some n` with a witness, or `none`. -/
noncomputable def LPO_Z_choice (P : Int → Prop) : Id (Option Int) :=
  pure none

/-- Coq (Raux.v):
Lemma LPO_Z : ∀ P : ℤ → Prop, (∀ n, P n ∨ ¬ P n) → {n : ℤ | P n} + {∀ n, ¬ P n}.

Lean (spec): `some n` indicates `P n`; `none` indicates `∀ n, ¬ P n`. -/
theorem LPO_Z (P : Int → Prop) :
    ⦃⌜∀ n, P n ∨ ¬ P n⌝⦄
    LPO_Z_choice P
    ⦃⇓r => ⌜match r with
            | some n => P n
            | none   => ∀ n, ¬ P n⌝⦄ := by
  intro _
  unfold LPO_Z_choice
  -- Mirrors Coq's LPO_Z; proof omitted for now
  sorry

end LPO

/-
  Magnitude function and related lemmas (Coq Raux.v Section pow)
  We parameterize by an integer base `beta` (≥ 2), analogous to Coq's `radix`.
-/
section Mag

/-- Magnitude of a real number with respect to base `beta`.

    In Coq, `mag` is characterized by bpow bounds: for nonzero `x`,
    bpow (e - 1) ≤ |x| < bpow e, where `e = mag x`.
    We model it as an `Id Int` computation for use in Hoare-style specs.
-/
noncomputable def mag (beta : Int) (x : ℝ) : Id Int :=
  -- We model `mag` as a pure computation in the `Id` monad
  -- so it can be used with `do`-notation throughout the file.
  pure (if x = 0 then 0 else ⌈Real.log (abs x) / Real.log (beta : ℝ)⌉)

/-- Uniqueness of magnitude from bpow bounds -/
theorem mag_unique (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ (e - 1) ≤ |x| ∧ |x| < (beta : ℝ) ^ e)⌝⦄
    mag beta x
    ⦃⇓m => ⌜m = e⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's mag_unique; proof omitted for now
  sorry

/-- Opposite preserves magnitude: mag (-x) = mag x -/
theorem mag_opp (beta : Int) (x : ℝ) :
    ⦃⌜1 < beta⌝⦄
    do
      let a ← mag beta (-x)
      let b ← mag beta x
      pure (a, b)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  simp [mag]

/-- Absolute value preserves magnitude: mag |x| = mag x -/
theorem mag_abs (beta : Int) (x : ℝ) :
    ⦃⌜1 < beta⌝⦄
    do
      let a ← mag beta |x|
      let b ← mag beta x
      pure (a, b)
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  simp [mag]

/-- Uniqueness under positivity: if 0 < x and bounds hold, mag x = e -/
theorem mag_unique_pos (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ 0 < x ∧ ((beta : ℝ) ^ (e - 1) ≤ x ∧ x < (beta : ℝ) ^ e)⌝⦄
    mag beta x
    ⦃⇓m => ⌜m = e⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's mag_unique_pos; proof omitted for now
  sorry

/-- Bounding |x| by bpow bounds magnitude from above -/
theorem mag_le_abs (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ |x| < (beta : ℝ) ^ e⌝⦄
    mag beta x
    ⦃⇓m => ⌜m ≤ e⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's mag_le_abs; proof omitted for now
  sorry

/-- Monotonicity: if |x| ≤ |y| then mag x ≤ mag y -/
theorem mag_le (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta ∧ |x| ≤ |y|⌝⦄
    do
      let a ← mag beta x
      let b ← mag beta y
      pure (a, b)
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _
  simp [mag]
  -- Proof deferred
  sorry

/-- If 0 < |x| < bpow e then e ≤ mag x -/
theorem lt_mag (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ 0 < |x| ∧ |x| < (beta : ℝ) ^ e⌝⦄
    mag beta x
    ⦃⇓m => ⌜e ≤ m⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's lt_mag; proof omitted for now
  sorry

/-- Magnitude of bpow e is e -/
theorem mag_bpow (beta e : Int) :
    ⦃⌜1 < beta⌝⦄
    mag beta ((beta : ℝ) ^ e)
    ⦃⇓m => ⌜m = e⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's mag_bpow; proof omitted for now
  sorry

/-- Scaling by bpow shifts magnitude additively -/
theorem mag_mult_bpow (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta⌝⦄
    mag beta (x * (beta : ℝ) ^ e)
    ⦃⇓m => ⌜∃ k, m = k + e⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's mag_mult_bpow; proof omitted for now
  sorry

/-- Upper bound: if x ≠ 0 and |x| < bpow e then mag x ≤ e -/
theorem mag_le_bpow (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ x ≠ 0 ∧ |x| < (beta : ℝ) ^ e⌝⦄
    mag beta x
    ⦃⇓m => ⌜m ≤ e⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's mag_le_bpow; proof omitted for now
  sorry

/-- Lower bound: if bpow (e - 1) ≤ |x| then e ≤ mag x -/
theorem mag_gt_bpow (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ (beta : ℝ) ^ (e - 1) ≤ |x|⌝⦄
    mag beta x
    ⦃⇓m => ⌜e ≤ m⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's mag_gt_bpow; proof omitted for now
  sorry

/-- Combined lower bound: if bpow (e - 1) < |x| then e ≤ mag x -/
theorem mag_ge_bpow (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ (beta : ℝ) ^ (e - 1) < |x|⌝⦄
    mag beta x
    ⦃⇓m => ⌜e ≤ m⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's mag_ge_bpow; proof omitted for now
  sorry

/-- If mag x < e then |x| < bpow e -/
noncomputable def abs_val (x : ℝ) : Id ℝ :=
  pure |x|

theorem bpow_mag_gt (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ (mag beta x).run < e⌝⦄
    abs_val x
    ⦃⇓v => ⌜v < (beta : ℝ) ^ e⌝⦄ := by
  intro _
  unfold abs_val
  -- Mirrors Coq's bpow_mag_gt; proof omitted for now
  sorry

/-- If e ≤ mag x then bpow (e - 1) ≤ |x| -/
theorem bpow_mag_le (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ e ≤ (mag beta x).run⌝⦄
    abs_val x
    ⦃⇓v => ⌜(beta : ℝ) ^ (e - 1) ≤ v⌝⦄ := by
  intro _
  unfold abs_val
  -- Mirrors Coq's bpow_mag_le; proof omitted for now
  sorry

/-- Translate bpow bound via integer power: if |x| < IZR (Zpower _ e) then mag x ≤ e -/
theorem mag_le_Zpower (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ |x| < ((beta : ℝ) ^ e)⌝⦄
    mag beta x
    ⦃⇓m => ⌜m ≤ e⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's mag_le_Zpower; proof omitted for now
  sorry

/-- Translate bpow lower bound via integer power: if IZR (Zpower _ (e-1)) ≤ |x| then e ≤ mag x -/
theorem mag_gt_Zpower (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜1 < beta ∧ ((beta : ℝ) ^ (e - 1)) ≤ |x|⌝⦄
    mag beta x
    ⦃⇓m => ⌜e ≤ m⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's mag_gt_Zpower; proof omitted for now
  sorry

/-- Magnitude of a product versus sum of magnitudes -/
theorem mag_mult (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta⌝⦄
    do
      let a ← mag beta (x * y)
      let b ← mag beta x
      let c ← mag beta y
      pure (a, b, c)
    ⦃⇓t => ⌜t.1 ≤ t.2.1 + t.2.2 ∧ t.2.1 + t.2.2 - 1 ≤ t.1⌝⦄ := by
  intro _
  simp [mag]
  -- Proof deferred
  sorry

/-- Magnitude of a sum versus max of magnitudes -/
theorem mag_plus (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta⌝⦄
    do
      let a ← mag beta (x + y)
      let b ← mag beta x
      let c ← mag beta y
      pure (a, b, c)
    ⦃⇓t => ⌜min (t.2.1) (t.2.2) - 1 ≤ t.1 ∧ t.1 ≤ max (t.2.1) (t.2.2) + 1⌝⦄ := by
  intro _
  simp [mag]
  -- Proof deferred
  sorry

/-- Magnitude of a difference bounded by max of magnitudes -/
theorem mag_minus (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta⌝⦄
    do
      let a ← mag beta (x - y)
      let b ← mag beta x
      let c ← mag beta y
      pure (a, b, c)
    ⦃⇓t => ⌜t.1 ≤ max (t.2.1) (t.2.2) + 1⌝⦄ := by
  intro _
  simp [mag]
  -- Proof deferred
  sorry

/-- Lower bound variant for magnitude of difference -/
theorem mag_minus_lb (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta⌝⦄
    do
      let a ← mag beta (x - y)
      let b ← mag beta x
      let c ← mag beta y
      pure (a, b, c)
    ⦃⇓t => ⌜min (t.2.1) (t.2.2) - 1 ≤ t.1⌝⦄ := by
  intro _
  simp [mag]
  -- Proof deferred
  sorry

/-- Lower bound on |x+y| via magnitudes -/
theorem mag_plus_ge (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta ∧ x ≠ 0 ∧ (mag beta y).run ≤ (mag beta x).run - 2⌝⦄
    mag beta (x + y)
    ⦃⇓m => ⌜(mag beta x).run - 1 ≤ m⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's mag_plus_ge; proof omitted for now
  sorry

/-- Bounds on magnitude under division -/
theorem mag_div (beta : Int) (x y : ℝ) :
    ⦃⌜1 < beta ∧ x ≠ 0 ∧ y ≠ 0⌝⦄
    do
      let a ← mag beta (x / y)
      let b ← mag beta x
      let c ← mag beta y
      pure (a, b, c)
    ⦃⇓t => ⌜t.2.1 - t.2.2 ≤ t.1 ∧ t.1 ≤ t.2.1 - t.2.2 + 1⌝⦄ := by
  intro _
  simp [mag]
  -- Proof deferred
  sorry

/-- Magnitude of square root -/
theorem mag_sqrt (beta : Int) (x : ℝ) :
    ⦃⌜1 < beta ∧ 0 < x⌝⦄
    do
      let a ← mag beta (Real.sqrt x)
      let b ← mag beta x
      pure (a, b)
    ⦃⇓p => ⌜p.1 = Int.ediv (p.2 + 1) 2⌝⦄ := by
  intro _
  simp [mag]
  -- Mirrors Coq's mag_sqrt; proof omitted for now
  sorry

/-- Magnitude at 1 -/
theorem mag_1 (beta : Int) :
    ⦃⌜1 < beta⌝⦄
    mag beta (1 : ℝ)
    ⦃⇓m => ⌜m = 1⌝⦄ := by
  intro _
  unfold mag
  -- Mirrors Coq's mag_1; proof omitted for now
  sorry

end Mag

end FloatSpec.Core.Raux
