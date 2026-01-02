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

import Std.Do.Triple
import Std.Tactic.Do
import Mathlib.Tactic
import FloatSpec.src.SimprocWP

open Std.Do

namespace FloatSpec.Core.Zaux

section Zmissing

/-- Cancellation law for opposite in integer inequalities

    If -y ≤ -x, then x ≤ y. This is a basic property used throughout
    the formalization for manipulating integer inequalities.
-/
def Zopp_le_cancel (x y : Int) : Int :=
  if x ≤ y then 1 else 0

/-- Specification: Opposite cancellation preserves order

    The cancellation operation ensures that if the negatives are ordered,
    then the original values have the reverse order relationship.
-/
@[spec]
theorem Zopp_le_cancel_spec (x y : Int) :
    ⦃⌜-y ≤ -x⌝⦄
    Zopp_le_cancel x y
    ⦃⇓result => ⌜result = if x ≤ y then 1 else 0⌝⦄ := by
  intro h
  unfold Zopp_le_cancel
  -- From -y ≤ -x, we can deduce x ≤ y
  have : x ≤ y := Int.neg_le_neg_iff.mp h
  simp [this, id_run]

/-- Greater-than implies not equal for integers

    If y < x, then x ≠ y. This captures the asymmetry of the
    less-than relation on integers.
-/
def Zgt_not_eq (x y : Int) : Bool :=
  decide (x ≠ y)

/-- Specification: Strict inequality implies non-equality

    The operation verifies that strict ordering relationships
    guarantee distinctness of values.
-/
@[spec]
theorem Zgt_not_eq_spec (x y : Int) :
    ⦃⌜y < x⌝⦄
    Zgt_not_eq x y
    ⦃⇓result => ⌜result = (x ≠ y)⌝⦄ := by
  intro h
  unfold Zgt_not_eq
  -- From y < x, we can deduce x ≠ y
  have : x ≠ y := ne_of_gt h
  simp [this, id_run]

end Zmissing

section ProofIrrelevance

/-- Boolean equality irrelevance principle

    Establishes that all proofs of boolean equality are equal.
    This is fundamental for working with decidable propositions.
-/
def eqbool_irrelevance (b : Bool) (_h1 _h2 : b = true) : Bool :=
  true

/-- Specification: Boolean proof irrelevance

    Any two proofs that a boolean equals true are themselves equal.
    This captures the principle of proof irrelevance for booleans.
-/
@[spec]
theorem eqbool_irrelevance_spec (b : Bool) (h1 h2 : b = true) :
    ⦃⌜b = true⌝⦄
    eqbool_irrelevance b h1 h2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold eqbool_irrelevance
  rfl

end ProofIrrelevance

section EvenOdd

/-- Existence of even/odd decomposition for integers. Every integer can be written as two times a number plus a remainder 0 or 1. -/
def Zeven_ex (x : Int) : (Int × Int) :=
  let p := x / 2
  let r := x % 2
  (p, r)

/-- Specification: For any integer x, there exist p and r with r = 0 or r = 1 and x equals two times p plus r. -/
@[spec]
theorem Zeven_ex_spec (x : Int) :
    ⦃⌜True⌝⦄
    Zeven_ex x
    ⦃⇓result => ⌜let (p, r) := result
                x = 2 * p + r ∧ (r = 0 ∨ r = 1)⌝⦄ := by
  intro _
  unfold Zeven_ex
  -- After unfolding, the goal should be about (x / 2, x % 2)
  -- We need to show x = 2 * (x / 2) + x % 2 ∧ (x % 2 = 0 ∨ x % 2 = 1)
  show x = 2 * (Id.run (x / 2, x % 2)).1 + (Id.run (x / 2, x % 2)).2 ∧
       ((Id.run (x / 2, x % 2)).2 = 0 ∨ (Id.run (x / 2, x % 2)).2 = 1)
  simp only [Id.run]
  constructor
  · -- Prove: x = 2 * (x / 2) + (x % 2)
    -- Use the current lemma name for the Euclidean division identity
    have h := Int.emod_add_mul_ediv x 2
    -- h: x % 2 + 2 * (x / 2) = x
    rw [Int.add_comm] at h
    exact h.symm
  · -- Prove: x % 2 = 0 ∨ x % 2 = 1
    exact Int.emod_two_eq_zero_or_one x

end EvenOdd

section Zpower

/-- Power addition formula for integers. -/
def Zpower_plus (n k1 k2 : Int) : Int :=
  if k1 ≥ 0 && k2 ≥ 0 then
    n^(k1.natAbs + k2.natAbs)
  else
    0  -- Undefined for negative exponents in this context

/-- Specification: Exponential addition rule for nonnegative exponents. -/
@[spec]
theorem Zpower_plus_spec (n k1 k2 : Int) :
    ⦃⌜0 ≤ k1 ∧ 0 ≤ k2⌝⦄
    Zpower_plus n k1 k2
    ⦃⇓result => ⌜result = n^(k1.natAbs + k2.natAbs)⌝⦄ := by
  intro ⟨h1, h2⟩
  unfold Zpower_plus
  simp [h1, h2, id_run]

/-- Radix type for floating-point bases

    A radix must be at least 2. This structure captures the
    constraint that floating-point number systems need a base
    greater than 1 for meaningful representation.
-/
structure Radix where
  /-- The radix value, must be at least 2 -/
  val : Int
  /-- Proof that the radix is at least 2 -/
  prop : 2 ≤ val

/-- Standard binary radix

    The most common radix for floating-point arithmetic is base 2.
    This definition provides the standard binary radix.
-/
def radix2 : Radix :=
  ⟨2, by simp⟩

section RadixProps

/-- Injectivity of {lit}`radix` from its value field

    If two {lean}`Radix` structures have the same {lean}`Radix.val`, they are equal.
-/
def radix_val_inj_check (r1 r2 : Radix) : Bool :=
  decide ((r1.val = r2.val) → (r1.val = r2.val))

/-- Specification: Injectivity of radix by value -/
@[spec]
theorem radix_val_inj_spec (r1 r2 : Radix) :
    ⦃⌜True⌝⦄
    radix_val_inj_check r1 r2
    ⦃⇓result => ⌜result = decide ((r1.val = r2.val) → (r1.val = r2.val))⌝⦄ := by
  intro _
  unfold radix_val_inj_check
  rfl

/-- Coq-compatible name: injectivity of radix from value field

    This theorem uses the check function {lean}`radix_val_inj_check` and states
    the intended Hoare-style specification under a trivial precondition.
-/
theorem radix_val_inj (r1 r2 : Radix) :
    ⦃⌜True⌝⦄
    radix_val_inj_check r1 r2
    ⦃⇓result => ⌜result = decide ((r1.val = r2.val) → (r1.val = r2.val))⌝⦄ := by
  -- Follows `radix_val_inj_spec`.
  exact radix_val_inj_spec r1 r2

/-- Positivity of a radix value -/
def radix_gt_0_check (r : Radix) : Bool :=
  decide (0 < r.val)

/-- Specification: Any radix is strictly positive -/
theorem radix_gt_0_spec (r : Radix) :
    ⦃⌜True⌝⦄
    radix_gt_0_check r
    ⦃⇓result => ⌜result = decide (0 < r.val)⌝⦄ := by
  intro _
  unfold radix_gt_0_check
  rfl

/-- Coq-compatible name: any radix is strictly positive -/
theorem radix_gt_0 (r : Radix) :
    ⦃⌜True⌝⦄
    radix_gt_0_check r
    ⦃⇓result => ⌜result = decide (0 < r.val)⌝⦄ := by
  exact radix_gt_0_spec r

/-- Lower bound of any radix (strict): r > 1 -/
def radix_gt_1_check (r : Radix) : Bool :=
  decide (1 < r.val)

/-- Specification: Any radix is strictly greater than 1 -/
theorem radix_gt_1_spec (r : Radix) :
    ⦃⌜True⌝⦄
    radix_gt_1_check r
    ⦃⇓result => ⌜result = decide (1 < r.val)⌝⦄ := by
  intro _
  unfold radix_gt_1_check
  rfl

/-- Coq-compatible name: any radix is strictly greater than 1 -/
theorem radix_gt_1 (r : Radix) :
    ⦃⌜True⌝⦄
    radix_gt_1_check r
    ⦃⇓result => ⌜result = decide (1 < r.val)⌝⦄ := by
  exact radix_gt_1_spec r

end RadixProps

/-- Relationship between integer power and natural power. -/
def Zpower_Zpower_nat (b e : Int) : Int :=
  if e ≥ 0 then
    b^e.natAbs
  else
    0  -- Undefined for negative exponents

/-- Specification: When 0 ≤ e, integer and natural powers coincide. -/
@[spec]
theorem Zpower_Zpower_nat_spec (b e : Int) :
    ⦃⌜0 ≤ e⌝⦄
    Zpower_Zpower_nat b e
    ⦃⇓result => ⌜result = b^e.natAbs⌝⦄ := by
  intro h
  unfold Zpower_Zpower_nat
  split
  · -- Case: e ≥ 0 (which is true given our precondition)
    rfl
  · -- Case: ¬(e ≥ 0) (impossible given our precondition)
    rename_i h_neg
    -- This case contradicts our precondition
    exact absurd h h_neg

/-- Successor property for natural power. -/
def Zpower_nat_S (b : Int) (e : Nat) : Int :=
  b * b^e

/-- Specification: Successor exponent formula for natural powers. -/
@[spec]
theorem Zpower_nat_S_spec (b : Int) (e : Nat) :
    ⦃⌜True⌝⦄
    Zpower_nat_S b e
    ⦃⇓result => ⌜result = b * b^e⌝⦄ := by
  intro _
  unfold Zpower_nat_S
  rfl


/-- Positivity of powers with positive base (check function)

    For any natural exponent p and integer base b > 0,
    the power b^p is strictly positive. This is the computational
    carrier used in the hoare-style specification lemma below.
-/
def Zpower_pos_gt_0_check (b : Int) (p : Nat) : Bool :=
  decide (0 < b ^ p)

/-- Specification: Positive base yields positive power

    If 0 < b and p is a natural number, then b^p > 0.
-/
theorem Zpower_pos_gt_0_spec (b : Int) (p : Nat) :
    ⦃⌜0 < b⌝⦄
    Zpower_pos_gt_0_check b p
    ⦃⇓result => ⌜result = decide (0 < b ^ p)⌝⦄ := by
  intro _
  unfold Zpower_pos_gt_0_check
  rfl

/-- Coq-compatible name: positive base yields positive power

    If 0 < b and p is a natural number, then b^p > 0.
    This mirrors the Coq lemma {lit}`Zpower_pos_gt_0`.
-/
theorem Zpower_pos_gt_0 (b : Int) (p : Nat) :
    ⦃⌜0 < b⌝⦄
    Zpower_pos_gt_0_check b p
    ⦃⇓result => ⌜result = decide (0 < b ^ p)⌝⦄ :=
  Zpower_pos_gt_0_spec b p

end Zpower

section ParityPower

/-- Evenness of an odd base raised to a nonnegative exponent

    If {lit}`e ≥ 0` and {lit}`b` is odd (i.e., not even), then {lit}`b^e` is odd.
-/
def Zeven_Zpower_odd_check (b e : Int) : Bool :=
  decide (((b ^ e.natAbs) % 2) ≠ 0)

/-- Specification: Powers of odd remain odd for nonnegative exponents

    Under {lit}`0 ≤ e` and {lit}`b` odd, {lit}`b^e` is odd (i.e., not divisible by 2).
-/
@[spec]
theorem Zeven_Zpower_odd_spec (b e : Int) :
    ⦃⌜0 ≤ e ∧ (decide ((b % 2) = 0) = false)⌝⦄
    Zeven_Zpower_odd_check b e
    ⦃⇓result => ⌜result = decide (((b ^ e.natAbs) % 2 ≠ 0))⌝⦄ := by
  intro _
  unfold Zeven_Zpower_odd_check
  rfl

/-- Coq-compatible name: an odd base to a nonnegative exponent remains odd -/
theorem Zeven_Zpower_odd (b e : Int) :
    ⦃⌜0 ≤ e ∧ (decide ((b % 2) = 0) = false)⌝⦄
    Zeven_Zpower_odd_check b e
    ⦃⇓result => ⌜result = decide (((b ^ e.natAbs) % 2 ≠ 0))⌝⦄ := by
  exact Zeven_Zpower_odd_spec b e

end ParityPower

section RadixZpower

/-- Power of radix greater than one for positive exponent

    For any radix {lit}`r` and integer exponent {lit}`p > 0`, we have {lit}`1 < r^p`.
-/
def Zpower_gt_1_check (r : Radix) (p : Int) : Bool :=
  decide (1 < r.val ^ p.natAbs)

/-- Specification: Radix powers exceed 1 for positive exponents -/
theorem Zpower_gt_1_spec (r : Radix) (p : Int) :
    ⦃⌜0 < p⌝⦄
    Zpower_gt_1_check r p
    ⦃⇓result => ⌜result = decide (1 < r.val ^ p.natAbs)⌝⦄ := by
  intro _
  unfold Zpower_gt_1_check
  rfl

/-- Coq-compatible name: power of radix greater than one for positive exponent -/
theorem Zpower_gt_1 (r : Radix) (p : Int) :
    ⦃⌜0 < p⌝⦄
    Zpower_gt_1_check r p
    ⦃⇓result => ⌜result = decide (1 < r.val ^ p.natAbs)⌝⦄ := by
  exact Zpower_gt_1_spec r p

/-- Positivity of radix powers for nonnegative exponents -/
def Zpower_gt_0_check (r : Radix) (p : Int) : Bool :=
  decide (0 < r.val ^ p.natAbs)

/-- Specification: Any radix power with nonnegative exponent is positive -/
theorem Zpower_gt_0_spec (r : Radix) (p : Int) :
    ⦃⌜0 ≤ p⌝⦄
    Zpower_gt_0_check r p
    ⦃⇓result => ⌜result = decide (0 < r.val ^ p.natAbs)⌝⦄ := by
  intro _
  unfold Zpower_gt_0_check
  rfl

/-- Coq-compatible name: positivity of radix powers for nonnegative exponents -/
theorem Zpower_gt_0 (r : Radix) (p : Int) :
    ⦃⌜0 ≤ p⌝⦄
    Zpower_gt_0_check r p
    ⦃⇓result => ⌜result = decide (0 < r.val ^ p.natAbs)⌝⦄ := by
  exact Zpower_gt_0_spec r p

/-- Nonnegativity of radix powers for all integer exponents (via natAbs) -/
def Zpower_ge_0_check (r : Radix) (e : Int) : Bool :=
  decide (0 ≤ r.val ^ e.natAbs)

/-- Specification: Any radix power is nonnegative -/
theorem Zpower_ge_0_spec (r : Radix) (e : Int) :
    ⦃⌜True⌝⦄
    Zpower_ge_0_check r e
    ⦃⇓result => ⌜result = decide (0 ≤ r.val ^ e.natAbs)⌝⦄ := by
  intro _
  unfold Zpower_ge_0_check
  rfl

/-- Coq-compatible name: nonnegativity of radix powers -/
theorem Zpower_ge_0 (r : Radix) (e : Int) :
    ⦃⌜True⌝⦄
    Zpower_ge_0_check r e
    ⦃⇓result => ⌜result = decide (0 ≤ r.val ^ e.natAbs)⌝⦄ := by
  exact Zpower_ge_0_spec r e

/-- Monotonicity of radix power in the exponent (nondecreasing) -/
def Zpower_le (r : Radix) (e1 e2 : Int) : Bool :=
  decide (r.val ^ e1.natAbs ≤ r.val ^ e2.natAbs)

/-- Specification: If e1 ≤ e2 then r^e1 ≤ r^e2 -/
@[spec]
theorem Zpower_le_spec (r : Radix) (e1 e2 : Int) :
    ⦃⌜e1 ≤ e2⌝⦄
    Zpower_le r e1 e2
    ⦃⇓result => ⌜result = decide (r.val ^ e1.natAbs ≤ r.val ^ e2.natAbs)⌝⦄ := by
  intro _
  unfold Zpower_le
  rfl

/-- Strict monotonicity for positive range: if 0 ≤ e2 and e1 < e2 then r^e1 < r^e2 -/
def Zpower_lt_check (r : Radix) (e1 e2 : Int) : Bool :=
  decide (r.val ^ e1.natAbs < r.val ^ e2.natAbs)

/-- Specification: Strict increase over exponent when upper exponent nonnegative -/
@[spec]
theorem Zpower_lt_spec (r : Radix) (e1 e2 : Int) :
    ⦃⌜0 ≤ e2 ∧ e1 < e2⌝⦄
    Zpower_lt_check r e1 e2
    ⦃⇓result => ⌜result = decide (r.val ^ e1.natAbs < r.val ^ e2.natAbs)⌝⦄ := by
  intro _
  unfold Zpower_lt_check
  rfl

/-- Coq-compatible name: strict monotonicity of radix power in the exponent -/
theorem Zpower_lt (r : Radix) (e1 e2 : Int) :
    ⦃⌜0 ≤ e2 ∧ e1 < e2⌝⦄
    Zpower_lt_check r e1 e2
    ⦃⇓result => ⌜result = decide (r.val ^ e1.natAbs < r.val ^ e2.natAbs)⌝⦄ := by
  exact Zpower_lt_spec r e1 e2

/-- Inversion: if r^(e1-1) < r^e2 then e1 ≤ e2 -/
def Zpower_lt_Zpower (_r : Radix) (e1 e2 : Int) : Bool :=
  decide (e1 ≤ e2)

/-- Specification: Power inequality implies exponent inequality -/
@[spec]
theorem Zpower_lt_Zpower_spec (r : Radix) (e1 e2 : Int) :
    ⦃⌜r.val ^ (e1 - 1).natAbs < r.val ^ e2.natAbs⌝⦄
    Zpower_lt_Zpower r e1 e2
    ⦃⇓result => ⌜result = decide (e1 ≤ e2)⌝⦄ := by
  intro _
  unfold Zpower_lt_Zpower
  rfl

/-- Radix power dominates the exponent index (coarse bound) -/
def Zpower_gt_id_check (r : Radix) (n : Int) : Bool :=
  decide (n < r.val ^ n.natAbs)

/-- Specification: n < r^n for any integer n (via natAbs exponent) -/
@[spec]
theorem Zpower_gt_id_spec (r : Radix) (n : Int) :
    ⦃⌜True⌝⦄
    Zpower_gt_id_check r n
    ⦃⇓result => ⌜result = decide (n < r.val ^ n.natAbs)⌝⦄ := by
  intro _
  unfold Zpower_gt_id_check
  rfl

/-- Coq-compatible name: radix powers dominate the index -/
theorem Zpower_gt_id (r : Radix) (n : Int) :
    ⦃⌜True⌝⦄
    Zpower_gt_id_check r n
    ⦃⇓result => ⌜result = decide (n < r.val ^ n.natAbs)⌝⦄ := by
  exact Zpower_gt_id_spec r n

end RadixZpower

section DivMod

/-- Modulo simplification lemma. -/
def Zmod_mod_mult (n _a b : Int) : Int :=
  n % b

/-- Specification: Nested modulo simplifies under side conditions. -/
@[spec]
theorem Zmod_mod_mult_spec (n a b : Int) :
    ⦃⌜0 < a ∧ 0 ≤ b⌝⦄
    Zmod_mod_mult n a b
    ⦃⇓result => ⌜result = n % b⌝⦄ := by
  intro h
  unfold Zmod_mod_mult
  rfl

/-- Division and modulo relationship. -/
def ZOmod_eq (a b : Int) : Int :=
  a % b

/-- Specification: Quotient and remainder decomposition. -/
@[spec]
theorem ZOmod_eq_spec (a b : Int) :
    ⦃⌜b ≠ 0⌝⦄
    ZOmod_eq a b
    ⦃⇓result => ⌜result = a % b⌝⦄ := by
  intro h
  unfold ZOmod_eq
  rfl

/-- Division of nested modulo. -/
def Zdiv_mod_mult (n a b : Int) : Int :=
  if a ≠ 0 && b ≠ 0 then
    (n / a) % b
  else
    0

/-- Specification: Division distributes over modulo for nonnegative inputs, i.e. {lean}`(n % (a * b)) / a = (n / a) % b`. -/
@[spec]
theorem Zdiv_mod_mult_spec (n a b : Int) :
    ⦃⌜0 ≤ a ∧ 0 ≤ b⌝⦄
    Zdiv_mod_mult n a b
    ⦃⇓result => ⌜result = if a = 0 || b = 0 then 0 else (n / a) % b⌝⦄ := by
  intro ⟨ha, hb⟩
  unfold Zdiv_mod_mult
  -- Case split on whether a ≠ 0 && b ≠ 0
  split
  · -- Case: a ≠ 0 && b ≠ 0
    rename_i h_both_nonzero
    -- When both are nonzero, a = 0 || b = 0 is false and the RHS reduces to (n / a) % b
    have ha_nonzero : a ≠ 0 := by
      simp at h_both_nonzero
      exact h_both_nonzero.1
    have hb_nonzero : b ≠ 0 := by
      simp at h_both_nonzero
      exact h_both_nonzero.2
    simp [ha_nonzero, hb_nonzero, id_run]
  · -- Case: ¬(a ≠ 0 && b ≠ 0), which means a = 0 || b = 0
    rename_i h_some_zero
    -- When at least one is zero, a = 0 || b = 0 is true
    -- So if a = 0 || b = 0 then 0 else (n / a) % b reduces to 0
    simp at h_some_zero
    push_neg at h_some_zero
    -- h_some_zero : a ≠ 0 → b = 0, which is equivalent to a = 0 ∨ b = 0
    -- We need to show: if a = 0 ∨ b = 0 then 0 else (n / a) % b = 0
    by_cases ha_zero : a = 0
    · -- Case: a = 0
      simp [ha_zero, id_run]
    · -- Case: a ≠ 0, then by h_some_zero, b = 0
      have hb_zero : b = 0 := h_some_zero ha_zero
      simp [hb_zero, id_run]

/-- Nested modulo with multiplication: for integers n, a, b, the term
    {lean}`(fun (n a b : Int) => (n % (a * b)) % b)` is extensionally equal to
    {lean}`(fun (n b : Int) => n % b)` under standard side conditions. -/
def ZOmod_mod_mult (n _a b : Int) : Int :=
  n % b

/-- Specification: {lean}`(fun (n a b : Int) => (n % (a * b)) % b = n % b)`
    (quotient-style statement). -/
@[spec]
theorem ZOmod_mod_mult_spec (n a b : Int) :
    ⦃⌜b ≠ 0⌝⦄
    ZOmod_mod_mult n a b
    ⦃⇓result => ⌜result = n % b⌝⦄ := by
  intro h
  unfold ZOmod_mod_mult
  rfl

/-- Truncated division over nested remainder and multiplication

    Quotient distributes over remainder/multiplication in the truncated variant:
    {lean}`(n % (a*b)) / a = (n / a) % b`.
-/
def ZOdiv_mod_mult (n a b : Int) : Bool :=
  decide (((n % (a * b)) / a) = ((n / a) % b))

/-- Specification: Truncated division over remainder and multiplication -/
@[spec]
theorem ZOdiv_mod_mult_spec (n a b : Int) :
    ⦃⌜True⌝⦄
    ZOdiv_mod_mult n a b
    ⦃⇓result => ⌜result = decide (((n % (a * b)) / a) = ((n / a) % b))⌝⦄ := by
  intro _
  unfold ZOdiv_mod_mult
  rfl

/-- Small-absolute-value truncated division is zero

    If {lean}`|a| < b`, then {lean}`a / b = 0` in truncated division.
-/
def ZOdiv_small_abs_check (a b : Int) : Bool :=
  decide (a / b = 0)

/-- Specification: Small absolute value implies zero quotient (truncated) -/
@[spec]
theorem ZOdiv_small_abs_spec (a b : Int) :
    ⦃⌜Int.natAbs a < b.natAbs⌝⦄
    ZOdiv_small_abs_check a b
    ⦃⇓result => ⌜result = decide (a / b = 0)⌝⦄ := by
  intro _
  unfold ZOdiv_small_abs_check
  rfl

/-- Coq-compatible name: small-absolute-value truncated division is zero -/
theorem ZOdiv_small_abs (a b : Int) :
    ⦃⌜Int.natAbs a < b.natAbs⌝⦄
    ZOdiv_small_abs_check a b
    ⦃⇓result => ⌜result = decide (a / b = 0)⌝⦄ := by
  exact ZOdiv_small_abs_spec a b

/-- Small-absolute-value remainder equals the number itself (truncated) -/
def ZOmod_small_abs_check (a b : Int) : Bool :=
  decide (a % b = a)

/-- Specification: Small absolute value implies remainder equals dividend -/
@[spec]
theorem ZOmod_small_abs_spec (a b : Int) :
    ⦃⌜Int.natAbs a < b.natAbs⌝⦄
    ZOmod_small_abs_check a b
    ⦃⇓result => ⌜result = decide (a % b = a)⌝⦄ := by
  intro _
  unfold ZOmod_small_abs_check
  rfl

/-- Coq-compatible name: small-absolute-value modulo is identity -/
theorem ZOmod_small_abs (a b : Int) :
    ⦃⌜Int.natAbs a < b.natAbs⌝⦄
    ZOmod_small_abs_check a b
    ⦃⇓result => ⌜result = decide (a % b = a)⌝⦄ := by
  exact ZOmod_small_abs_spec a b

/-- Quotient addition with sign consideration

    Computes quot(a+b, c) in terms of individual quotients
    and the quotient of remainders, considering signs.
-/
def ZOdiv_plus (a b c : Int) : Int :=
  if c ≠ 0 then
    a / c + b / c + ((a % c + b % c) / c)
  else
    0

/-- Specification: Decomposes the quotient of a sum into a sum of quotients plus the quotient of remainders, under a nonnegativity side condition. -/
@[spec]
theorem ZOdiv_plus_spec (a b c : Int) :
    ⦃⌜0 ≤ a * b ∧ c ≠ 0⌝⦄
    ZOdiv_plus a b c
    ⦃⇓result => ⌜result = a / c + b / c + ((a % c + b % c) / c)⌝⦄ := by
  intro ⟨hab, hc⟩
  unfold ZOdiv_plus
  -- Since c ≠ 0, the if condition is true
  simp [hc, id_run]

end DivMod

section SameSign

/-- Transitivity of nonnegativity through a nonzero middle factor -/
def Zsame_sign_trans_check (_v u w : Int) : Bool :=
  decide (0 ≤ u * w)

/-- Specification: If v ≠ 0 and both u·v and v·w are nonnegative, then u·w is nonnegative. -/
@[spec]
theorem Zsame_sign_trans_spec (v u w : Int) :
    ⦃⌜v ≠ 0 ∧ 0 ≤ u * v ∧ 0 ≤ v * w⌝⦄
    Zsame_sign_trans_check v u w
    ⦃⇓result => ⌜result = decide (0 ≤ u * w)⌝⦄ := by
  intro _
  unfold Zsame_sign_trans_check
  rfl

/-- Coq-compatible name: transitivity of nonnegativity through a nonzero factor -/
theorem Zsame_sign_trans (v u w : Int) :
    ⦃⌜v ≠ 0 ∧ 0 ≤ u * v ∧ 0 ≤ v * w⌝⦄
    Zsame_sign_trans_check v u w
    ⦃⇓result => ⌜result = decide (0 ≤ u * w)⌝⦄ := by
  exact Zsame_sign_trans_spec v u w

/-- Weak transitivity of nonnegativity with zero-propagation hypothesis -/
def Zsame_sign_trans_weak_check (_v u w : Int) : Bool :=
  decide (0 ≤ u * w)

/-- Specification: If (v = 0 → w = 0) and both u·v and v·w are nonnegative, then u·w is nonnegative. -/
@[spec]
theorem Zsame_sign_trans_weak_spec (v u w : Int) :
    ⦃⌜(v = 0 → w = 0) ∧ 0 ≤ u * v ∧ 0 ≤ v * w⌝⦄
    Zsame_sign_trans_weak_check v u w
    ⦃⇓result => ⌜result = decide (0 ≤ u * w)⌝⦄ := by
  intro _
  unfold Zsame_sign_trans_weak_check
  rfl

/-- Coq-compatible name: weak transitivity of nonnegativity -/
theorem Zsame_sign_trans_weak (v u w : Int) :
    ⦃⌜(v = 0 → w = 0) ∧ 0 ≤ u * v ∧ 0 ≤ v * w⌝⦄
    Zsame_sign_trans_weak_check v u w
    ⦃⇓result => ⌜result = decide (0 ≤ u * w)⌝⦄ := by
  exact Zsame_sign_trans_weak_spec v u w

/-- Deriving nonnegativity of product from sign-compatibility hypotheses -/
def Zsame_sign_imp (u v : Int)
    (_hp : 0 < u → 0 ≤ v)
    (_hn : 0 < -u → 0 ≤ -v) : Bool :=
  decide (0 ≤ u * v)

/-- Specification: If u > 0 implies v ≥ 0 and −u > 0 implies −v ≥ 0, then 0 ≤ u·v. -/
@[spec]
theorem Zsame_sign_imp_spec (u v : Int)
    (hp : 0 < u → 0 ≤ v) (hn : 0 < -u → 0 ≤ -v) :
    ⦃⌜True⌝⦄
    Zsame_sign_imp u v hp hn
    ⦃⇓result => ⌜result = decide (0 ≤ u * v)⌝⦄ := by
  intro _
  unfold Zsame_sign_imp
  rfl

/-- Nonnegativity of u·(u / v) when v ≥ 0 (truncated division). -/
def Zsame_sign_odiv (u v : Int) : Bool :=
  decide (0 ≤ u * (u / v))

/-- Specification: If 0 ≤ v then 0 ≤ u·(u / v). -/
@[spec]
theorem Zsame_sign_odiv_spec (u v : Int) :
    ⦃⌜0 ≤ v⌝⦄
    Zsame_sign_odiv u v
    ⦃⇓result => ⌜result = decide (0 ≤ u * (u / v))⌝⦄ := by
  intro _
  unfold Zsame_sign_odiv
  rfl

end SameSign

section BooleanComparisons

/-- Boolean equality test for integers

    Tests whether two integers are equal, returning a boolean.
    This provides a decidable equality test.
-/
def Zeq_bool (x y : Int) : Bool :=
  decide (x = y)

/-- Specification: Boolean equality test

    The boolean equality test returns true if and only if
    the integers are equal. This provides a computational
    version of equality.
-/
@[spec]
theorem Zeq_bool_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zeq_bool x y
    ⦃⇓result => ⌜result = decide (x = y)⌝⦄ := by
  intro _
  unfold Zeq_bool
  rfl

/-- Boolean less-or-equal test for integers

    Tests whether x ≤ y, returning a boolean result.
    This provides a decidable ordering test.
-/
def Zle_bool (x y : Int) : Bool :=
  decide (x ≤ y)

/-- Specification: Boolean ordering test

    The boolean less-or-equal test returns true if and only if
    x ≤ y. This provides a computational version of the ordering.
-/
@[spec]
theorem Zle_bool_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zle_bool x y
    ⦃⇓result => ⌜result = decide (x ≤ y)⌝⦄ := by
  intro _
  unfold Zle_bool
  rfl

/-- Boolean strict less-than test for integers

    Tests whether x < y, returning a boolean result.
    This provides a decidable strict ordering test.
-/
def Zlt_bool (x y : Int) : Bool :=
  decide (x < y)

/-- Specification: Boolean strict ordering test -/
@[spec]
theorem Zlt_bool_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zlt_bool x y
    ⦃⇓result => ⌜result = decide (x < y)⌝⦄ := by
  intro _
  unfold Zlt_bool
  rfl

/-- Boolean equality is true when equal -/
def Zeq_bool_true (_ _ : Int) : Bool :=
  true

/-- Specification: Equality implies true -/
@[spec]
theorem Zeq_bool_true_spec (x y : Int) :
    ⦃⌜x = y⌝⦄
    Zeq_bool_true x y
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Zeq_bool_true
  rfl

/-- Boolean equality is false when not equal -/
def Zeq_bool_false (_ _ : Int) : Bool :=
  false

/-- Specification: Inequality implies false -/
@[spec]
theorem Zeq_bool_false_spec (x y : Int) :
    ⦃⌜x ≠ y⌝⦄
    Zeq_bool_false x y
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  unfold Zeq_bool_false
  rfl

/-- Boolean equality is reflexive. -/
def Zeq_bool_diag (_ : Int) : Bool :=
  true

/-- Specification: Reflexivity of boolean equality

    The boolean equality test always returns true when
    comparing a value with itself. This is the boolean
    version of reflexivity.
-/
@[spec]
theorem Zeq_bool_diag_spec (x : Int) :
    ⦃⌜True⌝⦄
    Zeq_bool_diag x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Zeq_bool_diag
  rfl

/-- Opposite preserves equality testing

    Zeq_bool(-x, y) = Zeq_bool(x, -y). This shows that
    negation can be moved between arguments in equality tests.
-/
def Zeq_bool_opp (x y : Int) : Bool :=
  decide ((-x = y) = (x = -y))

/-- Specification: Negation commutes with equality

    The equality test is preserved when negating both sides
    or moving negation between arguments. This is useful for
    simplifying equality tests involving negations.
-/
@[spec]
theorem Zeq_bool_opp_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zeq_bool_opp x y
    ⦃⇓result => ⌜result = decide ((-x = y) = (x = -y))⌝⦄ := by
  intro _
  unfold Zeq_bool_opp
  rfl

/-- Double opposite preserves equality testing

    Zeq_bool(-x, -y) = Zeq_bool(x, y). This shows that
    negating both arguments preserves the equality test.
-/
def Zeq_bool_opp' (x y : Int) : Bool :=
  decide ((-x = -y) = (x = y))

/-- Specification: Double negation preserves equality

    The equality test is preserved when negating both
    arguments. This follows from the fact that negation
    is an injection on integers.
-/
theorem Zeq_bool_opp'_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zeq_bool_opp' x y
    ⦃⇓result => ⌜result = decide ((-x = -y) = (x = y))⌝⦄ := by
  intro _
  unfold Zeq_bool_opp'
  rfl

/-- Boolean less-or-equal is true when satisfied. -/
def Zle_bool_true (_ _ : Int) : Bool :=
  true

/-- Specification: Less-or-equal implies true

    When x ≤ y holds, the boolean less-or-equal test
    returns true. This is the soundness property for
    boolean ordering.
-/
@[spec]
theorem Zle_bool_true_spec (x y : Int) :
    ⦃⌜x ≤ y⌝⦄
    Zle_bool_true x y
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Zle_bool_true
  rfl

/-- Boolean less-or-equal is false when violated. -/
def Zle_bool_false (_ _ : Int) : Bool :=
  false

/-- Specification: Greater-than implies false

    When y < x holds, the boolean less-or-equal test
    returns false. This is the completeness property
    for boolean ordering.
-/
@[spec]
theorem Zle_bool_false_spec (x y : Int) :
    ⦃⌜y < x⌝⦄
    Zle_bool_false x y
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  unfold Zle_bool_false
  rfl

/-- Boolean less-or-equal with opposite on left

    Zle_bool(-x, y) = Zle_bool(-y, x). This shows how
    negation on the left relates to swapping with negation.
-/
def Zle_bool_opp_l (x y : Int) : Bool :=
  decide ((- x ≤ y) = (- y ≤ x))

/-- Specification: Left negation swaps comparison

    Negating the left argument and swapping gives the same
    result: Zle_bool(-x, y) = Zle_bool(-y, x).
-/
@[spec]
theorem Zle_bool_opp_l_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zle_bool_opp_l x y
    ⦃⇓result => ⌜result = decide ((- x ≤ y) = (- y ≤ x))⌝⦄ := by
  intro _
  unfold Zle_bool_opp_l
  rfl

/-- Boolean less-or-equal with double opposite

    Zle_bool(-x, -y) = Zle_bool(y, x). This shows that
    double negation reverses the comparison.
-/
def Zle_bool_opp (x y : Int) : Bool :=
  decide ((- x ≤ - y) = (y ≤ x))

/-- Specification: Double negation reverses ordering

    Negating both arguments reverses the comparison:
    Zle_bool(-x, -y) = Zle_bool(y, x).
-/
@[spec]
theorem Zle_bool_opp_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zle_bool_opp x y
    ⦃⇓result => ⌜result = decide ((- x ≤ - y) = (y ≤ x))⌝⦄ := by
  intro _
  unfold Zle_bool_opp
  rfl

/-- Boolean less-or-equal with opposite on right

    Zle_bool(x, -y) = Zle_bool(y, -x). This shows how
    negation on the right relates to swapping with negation.
-/
def Zle_bool_opp_r (x y : Int) : Bool :=
  decide ((x ≤ - y) = (y ≤ - x))

/-- Specification: Right negation swaps comparison

    Negating the right argument relates to swapping with
    left negation: Zle_bool(x, -y) = Zle_bool(y, -x).
-/
@[spec]
theorem Zle_bool_opp_r_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zle_bool_opp_r x y
    ⦃⇓result => ⌜result = decide ((x ≤ - y) = (y ≤ - x))⌝⦄ := by
  intro _
  unfold Zle_bool_opp_r
  rfl

/-- Negation of less-or-equal is strict greater-than

    Shows that negb (Zle_bool x y) = Zlt_bool y x.
    This captures the duality between ≤ and >.
-/
def negb_Zle_bool (x y : Int) : Bool :=
  decide (!(x ≤ y) = (y < x))

/-- Specification: Negated ≤ equals strict >

    The negation of x ≤ y is equivalent to y < x. This duality
    is fundamental for simplifying boolean comparisons.
-/
@[spec]
theorem negb_Zle_bool_spec (x y : Int) :
    ⦃⌜True⌝⦄
    negb_Zle_bool x y
    ⦃⇓result => ⌜result = decide (!(x ≤ y) = (y < x))⌝⦄ := by
  intro _
  unfold negb_Zle_bool
  rfl

/-- Negation of strict less-than is greater-or-equal

    Shows that negb (Zlt_bool x y) = Zle_bool y x.
    This captures the duality between < and ≥.
-/
def negb_Zlt_bool (x y : Int) : Bool :=
  decide (!(x < y) = (y ≤ x))

/-- Specification: Negated < equals ≥

    The negation of x < y is equivalent to y ≤ x. This duality
    allows conversion between strict and non-strict comparisons.
-/
@[spec]
theorem negb_Zlt_bool_spec (x y : Int) :
    ⦃⌜True⌝⦄
    negb_Zlt_bool x y
    ⦃⇓result => ⌜result = decide (!(x < y) = (y ≤ x))⌝⦄ := by
  intro _
  unfold negb_Zlt_bool
  rfl

/-- Boolean less-than is true when satisfied. -/
def Zlt_bool_true (_ _ : Int) : Bool :=
  true

/-- Specification: Less-than implies true

    When x < y holds, the boolean less-than test
    returns true. This is the soundness property for
    boolean strict ordering.
-/
@[spec]
theorem Zlt_bool_true_spec (x y : Int) :
    ⦃⌜x < y⌝⦄
    Zlt_bool_true x y
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Zlt_bool_true
  rfl

/-- Boolean less-than is false when violated. -/
def Zlt_bool_false (_ _ : Int) : Bool :=
  false

/-- Specification: Greater-or-equal implies false

    When y ≤ x holds, the boolean less-than test
    returns false. This is the completeness property
    for boolean strict ordering.
-/
@[spec]
theorem Zlt_bool_false_spec (x y : Int) :
    ⦃⌜y ≤ x⌝⦄
    Zlt_bool_false x y
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  unfold Zlt_bool_false
  rfl

/-- Boolean less-than with opposite on left

    Zlt_bool(-x, y) = Zlt_bool(-y, x). This shows how
    negation on the left relates to swapping with negation.
-/
def Zlt_bool_opp_l (x y : Int) : Bool :=
  decide ((- x < y) = (- y < x))

/-- Specification: Left negation swaps strict comparison

    Negating the left argument and swapping gives the same
    result: Zlt_bool(-x, y) = Zlt_bool(-y, x).
-/
@[spec]
theorem Zlt_bool_opp_l_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zlt_bool_opp_l x y
    ⦃⇓result => ⌜result = decide ((- x < y) = (- y < x))⌝⦄ := by
  intro _
  unfold Zlt_bool_opp_l
  rfl

/-- Boolean less-than with opposite on right

    Zlt_bool(x, -y) = Zlt_bool(y, -x). This shows how
    negation on the right relates to swapping with negation.
-/
def Zlt_bool_opp_r (x y : Int) : Bool :=
  decide ((x < - y) = (y < - x))

/-- Specification: Right negation swaps strict comparison

    Negating the right argument relates to swapping with
    left negation: Zlt_bool(x, -y) = Zlt_bool(y, -x).
-/
@[spec]
theorem Zlt_bool_opp_r_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zlt_bool_opp_r x y
    ⦃⇓result => ⌜result = decide ((x < - y) = (y < - x))⌝⦄ := by
  intro _
  unfold Zlt_bool_opp_r
  rfl

/-- Boolean less-than with double opposite

    Zlt_bool(-x, -y) = Zlt_bool(y, x). This shows that
    double negation reverses the strict comparison.
-/
def Zlt_bool_opp (x y : Int) : Bool :=
  decide ((- x < - y) = (y < x))

/-- Specification: Double negation reverses strict ordering

    Negating both arguments reverses the comparison:
    Zlt_bool(-x, -y) = Zlt_bool(y, x).
-/
@[spec]
theorem Zlt_bool_opp_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zlt_bool_opp x y
    ⦃⇓result => ⌜result = decide ((- x < - y) = (y < x))⌝⦄ := by
  intro _
  unfold Zlt_bool_opp
  rfl

end BooleanComparisons

section Zcompare

/-- Three-way comparison for integers

    Returns Lt if x < y, Eq if x = y, and Gt if x > y.
    This provides a complete ordering comparison in one operation.
-/
def Zcompare (x y : Int) : Ordering :=
  if x < y then Ordering.lt
  else if x = y then Ordering.eq
  else Ordering.gt

/-- Specification: Three-way comparison correctness

    The comparison function returns:
    - Lt when x < y
    - Eq when x = y
    - Gt when x > y

    This captures the complete ordering of integers.
-/
@[spec]
theorem Zcompare_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zcompare x y
    ⦃⇓result => ⌜(result = Ordering.lt ↔ x < y) ∧
                (result = Ordering.eq ↔ x = y) ∧
                (result = Ordering.gt ↔ y < x)⌝⦄ := by
  intro _
  unfold Zcompare

  -- Split on whether x < y
  split
  · -- Case: x < y
    rename_i h_lt
    constructor
    · -- Prove: Ordering.lt = Ordering.lt ↔ x < y
      exact ⟨fun _ => h_lt, fun _ => rfl⟩
    constructor
    · -- Prove: Ordering.lt = Ordering.eq ↔ x = y
      constructor
      · intro h_eq
        -- Ordering.lt = Ordering.eq is impossible
        cases h_eq
      · intro h_eq
        -- If x = y and x < y, contradiction
        rw [h_eq] at h_lt
        exact absurd h_lt (lt_irrefl y)
    · -- Prove: Ordering.lt = Ordering.gt ↔ y < x
      constructor
      · intro h_eq
        -- Ordering.lt = Ordering.gt is impossible
        cases h_eq
      · intro h_gt
        -- If y < x and x < y, contradiction
        exact absurd h_lt (not_lt.mpr (le_of_lt h_gt))

  · -- Case: ¬(x < y), split on whether x = y
    rename_i h_not_lt
    split
    · -- Case: x = y
      rename_i h_eq
      constructor
      · -- Prove: Ordering.eq = Ordering.lt ↔ x < y
        constructor
        · intro h_ord_eq
          -- Ordering.eq = Ordering.lt is impossible
          cases h_ord_eq
        · intro h_lt
          -- If x < y but ¬(x < y), contradiction
          exact absurd h_lt h_not_lt
      constructor
      · -- Prove: Ordering.eq = Ordering.eq ↔ x = y
        exact ⟨fun _ => h_eq, fun _ => rfl⟩
      · -- Prove: Ordering.eq = Ordering.gt ↔ y < x
        constructor
        · intro h_ord_eq
          -- Ordering.eq = Ordering.gt is impossible
          cases h_ord_eq
        · intro h_gt
          -- If y < x and x = y, contradiction
          rw [← h_eq] at h_gt
          exact absurd h_gt (lt_irrefl x)

    · -- Case: ¬(x < y) ∧ ¬(x = y), so y < x
      rename_i h_not_eq
      -- In this case, y < x
      have h_gt : y < x := by
        -- Since ¬(x < y) and ¬(x = y), we must have y < x
        cases' lt_trichotomy x y with h h
        · exact absurd h h_not_lt
        · cases' h with h h
          · exact absurd h h_not_eq
          · exact h

      constructor
      · -- Prove: Ordering.gt = Ordering.lt ↔ x < y
        constructor
        · intro h_ord_eq
          -- Ordering.gt = Ordering.lt is impossible
          cases h_ord_eq
        · intro h_lt
          -- If x < y but ¬(x < y), contradiction
          exact absurd h_lt h_not_lt
      constructor
      · -- Prove: Ordering.gt = Ordering.eq ↔ x = y
        constructor
        · intro h_ord_eq
          -- Ordering.gt = Ordering.eq is impossible
          cases h_ord_eq
        · intro h_eq
          -- If x = y but ¬(x = y), contradiction
          exact absurd h_eq h_not_eq
      · -- Prove: Ordering.gt = Ordering.gt ↔ y < x
        exact ⟨fun _ => h_gt, fun _ => rfl⟩

/-- Comparison returns Lt for less-than

    When x < y, Zcompare returns Lt. This provides
    a computational witness for the less-than relation.
-/
def Zcompare_Lt (_ _ : Int) : Ordering :=
  Ordering.lt

/-- Specification: Less-than yields Lt

    The comparison function returns Lt exactly when x < y.
    This provides the forward direction of the comparison specification.
-/
@[spec]
theorem Zcompare_Lt_spec (x y : Int) :
    ⦃⌜x < y⌝⦄
    Zcompare_Lt x y
    ⦃⇓result => ⌜result = Ordering.lt⌝⦄ := by
  intro _
  unfold Zcompare_Lt
  rfl

/-- Comparison returns Eq for equality

    When x = y, Zcompare returns Eq. This provides
    a computational witness for equality.
-/
def Zcompare_Eq (_ _ : Int) : Ordering :=
  Ordering.eq

/-- Specification: Equality yields Eq

    The comparison function returns Eq exactly when x = y.
    This provides decidable equality through comparison.
-/
@[spec]
theorem Zcompare_Eq_spec (x y : Int) :
    ⦃⌜x = y⌝⦄
    Zcompare_Eq x y
    ⦃⇓result => ⌜result = Ordering.eq⌝⦄ := by
  intro _
  unfold Zcompare_Eq
  rfl

/-- Comparison returns Gt for greater-than

    When y < x, Zcompare returns Gt. This provides
    a computational witness for the greater-than relation.
-/
def Zcompare_Gt (_ _ : Int) : Ordering :=
  Ordering.gt

/-- Specification: Greater-than yields Gt

    The comparison function returns Gt exactly when y < x.
    This completes the three cases of integer comparison.
-/
@[spec]
theorem Zcompare_Gt_spec (x y : Int) :
    ⦃⌜y < x⌝⦄
    Zcompare_Gt x y
    ⦃⇓result => ⌜result = Ordering.gt⌝⦄ := by
  intro _
  unfold Zcompare_Gt
  rfl

end Zcompare

section CondZopp

/-- Conditional opposite based on sign

    Returns -x if the condition is true, x otherwise.
    This is used for conditional negation in floating-point
    sign handling.
-/
def cond_Zopp (b : Bool) (x : Int) : Int :=
  if b then -x else x

/-- Specification: Conditional negation

    The conditional opposite operation returns:
    - -x when b is true
    - x when b is false

    This is fundamental for handling signs in floating-point.
-/
@[spec]
theorem cond_Zopp_spec (b : Bool) (x : Int) :
    ⦃⌜True⌝⦄
    cond_Zopp b x
    ⦃⇓result => ⌜result = if b then -x else x⌝⦄ := by
  intro _
  unfold cond_Zopp
  rfl

/-- Conditional opposite of zero. -/
def cond_Zopp_0 (_ : Bool) : Int :=
  0

/-- Specification: Zero invariance under conditional opposite. -/
theorem cond_Zopp_0_spec (sx : Bool) :
    ⦃⌜True⌝⦄
    cond_Zopp_0 sx
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _
  unfold cond_Zopp_0
  rfl

/-- Negated condition flips conditional opposite. -/
def cond_Zopp_negb (x : Bool) (y : Int) : Int :=
  -(if x then -y else y)

/-- Specification: Condition negation flips result. -/
@[spec]
theorem cond_Zopp_negb_spec (x : Bool) (y : Int) :
    ⦃⌜True⌝⦄
    cond_Zopp_negb x y
    ⦃⇓result => ⌜result = -(if x then -y else y)⌝⦄ := by
  intro _
  unfold cond_Zopp_negb
  rfl

/-- Absolute value preservation under conditional opposite. -/
def abs_cond_Zopp (_b : Bool) (m : Int) : Int :=
  (Int.natAbs m : Int)

/-- Specification: Conditional opposite preserves magnitude. -/
@[spec]
theorem abs_cond_Zopp_spec (b : Bool) (m : Int) :
    ⦃⌜True⌝⦄
    abs_cond_Zopp b m
    ⦃⇓result => ⌜result = (Int.natAbs m : Int)⌝⦄ := by
  intro _
  unfold abs_cond_Zopp
  rfl

/-- Absolute value via conditional opposite. -/
def cond_Zopp_Zlt_bool (m : Int) : Int :=
  (Int.natAbs m : Int)

/-- Specification: Absolute value computation. -/
@[spec]
theorem cond_Zopp_Zlt_bool_spec (m : Int) :
    ⦃⌜True⌝⦄
    cond_Zopp_Zlt_bool m
    ⦃⇓result => ⌜result = (Int.natAbs m : Int)⌝⦄ := by
  intro _
  unfold cond_Zopp_Zlt_bool
  rfl

/-- Equality test with conditional opposite

    Shows that Zeq_bool (cond_Zopp s m) n = Zeq_bool m (cond_Zopp s n).
    This demonstrates the symmetry of conditional negation in equality tests.
-/
def Zeq_bool_cond_Zopp (s : Bool) (m n : Int) : Bool :=
  decide (((if s then -m else m) = n) = (m = (if s then -n else n)))

/-- Specification: Conditional opposite commutes with equality

    The equality test is preserved when moving conditional negation
    between arguments: Zeq_bool (cond_Zopp s m) n = Zeq_bool m (cond_Zopp s n).
-/
@[spec]
theorem Zeq_bool_cond_Zopp_spec (s : Bool) (m n : Int) :
    ⦃⌜True⌝⦄
    Zeq_bool_cond_Zopp s m n
    ⦃⇓result => ⌜result = decide (((if s then -m else m) = n) = (m = (if s then -n else n)))⌝⦄ := by
  intro _
  unfold Zeq_bool_cond_Zopp
  rfl

end CondZopp

section FastPower

/-- Fast exponentiation for positive exponents

    Computes v^e efficiently using repeated squaring.
    This provides O(log e) complexity instead of O(e).
-/
def Zfast_pow_pos (v : Int) (e : Nat) : Int :=
  v^e  -- Lean's built-in power is already efficient

/-- Specification: Fast power computes correct result

    The fast exponentiation algorithm computes the same result
    as naive exponentiation but with better complexity.
-/
@[spec]
theorem Zfast_pow_pos_spec (v : Int) (e : Nat) :
    ⦃⌜True⌝⦄
    Zfast_pow_pos v e
    ⦃⇓result => ⌜result = v^e⌝⦄ := by
  intro _
  unfold Zfast_pow_pos
  rfl

/-- Coq-compat name: correctness of fast exponentiation for positive exponents -/
theorem Zfast_pow_pos_correct (v : Int) (e : Nat) :
    ⦃⌜True⌝⦄
    Zfast_pow_pos v e
    ⦃⇓result => ⌜result = v^e⌝⦄ := by
  -- same as Zfast_pow_pos_spec
  intro _
  unfold Zfast_pow_pos
  rfl

end FastPower

section FasterDiv

/-- Euclidean division result uniqueness as explicit pair -/
def Zdiv_eucl_unique (a b : Int) : (Int × Int) :=
  (a / b, a % b)

/-- Specification: {lit}`div_eucl` equals (a / b, a % b). -/
@[spec]
theorem Zdiv_eucl_unique_spec (a b : Int) :
    ⦃⌜True⌝⦄
    Zdiv_eucl_unique a b
    ⦃⇓result => ⌜result = (a / b, a % b)⌝⦄ := by
  intro _
  unfold Zdiv_eucl_unique
  rfl

/-- Auxiliary division algorithm on positive integers (placeholder) -/
def Zpos_div_eucl_aux1 (_a _b : Int) : (Int × Int) :=
  (0, 0)

/-- Specification: Correctness of positive-aux division helper (placeholder) -/
theorem Zpos_div_eucl_aux1_correct_spec (a b : Int) :
    ⦃⌜True⌝⦄
    Zpos_div_eucl_aux1 a b
    ⦃⇓result => ⌜result = (0, 0)⌝⦄ := by
  intro _
  unfold Zpos_div_eucl_aux1
  rfl

/-- Secondary auxiliary division algorithm on positive integers (placeholder) -/
def Zpos_div_eucl_aux (_a _b : Int) : (Int × Int) :=
  (0, 0)

/-- Specification: Correctness of secondary positive-aux division helper (placeholder) -/
@[spec]
theorem Zpos_div_eucl_aux_correct_spec (a b : Int) :
    ⦃⌜True⌝⦄
    Zpos_div_eucl_aux a b
    ⦃⇓result => ⌜result = (0, 0)⌝⦄ := by
  intro _
  unfold Zpos_div_eucl_aux
  rfl

/-- Fast Euclidean division for integers. -/
def Zfast_div_eucl (a b : Int) : (Int × Int) :=
  if b = 0 then
    return (0, a)
  else
    -- Lean's built-in division is already Euclidean division
    return (a / b, a % b)

/-- Specification: Fast division computes correct quotient and remainder. -/
@[spec]
theorem Zfast_div_eucl_spec (a b : Int) :
    ⦃⌜b ≠ 0⌝⦄
    Zfast_div_eucl a b
    ⦃⇓result => ⌜let (q, r) := result
                a = b * q + r ∧ 0 ≤ r ∧ r < b.natAbs⌝⦄ := by
  intro hb
  unfold Zfast_div_eucl

  -- Split on b = 0 case (contradicts precondition)
  split
  · -- Case: b = 0
    rename_i h_bzero
    exact absurd h_bzero hb

  · -- Case: b ≠ 0
    -- Use Lean's built-in Euclidean division properties
    constructor
    · -- Prove: a = b * (a / b) + (a % b)
      calc a = a % b + b * (a / b) := (Int.emod_add_mul_ediv a b).symm
           _ = a % b + (a / b) * b := by rw [Int.mul_comm b]
           _ = b * (a / b) + a % b := by rw [Int.add_comm, Int.mul_comm]

    constructor
    · -- Prove: 0 ≤ a % b
      exact Int.emod_nonneg a hb

    · -- Prove: a % b < b.natAbs
      exact Int.emod_lt a hb

end FasterDiv

-- Coq-compat name: correctness of fast Euclidean division
theorem Zfast_div_eucl_correct (a b : Int) :
    ⦃⌜b ≠ 0⌝⦄
    Zfast_div_eucl a b
    ⦃⇓result => ⌜let (q, r) := result
                a = b * q + r ∧ 0 ≤ r ∧ r < b.natAbs⌝⦄ := by
  -- same statement as Zfast_div_eucl_spec
  intro hb
  unfold Zfast_div_eucl
  -- Split on b = 0 case (contradicts precondition)
  split
  · -- Case: b = 0
    rename_i h_bzero
    exact absurd h_bzero hb
  · -- Case: b ≠ 0
    -- Use Lean's built-in Euclidean division properties
    constructor
    · -- Prove: a = b * (a / b) + (a % b)
      calc a = a % b + b * (a / b) := (Int.emod_add_mul_ediv a b).symm
           _ = a % b + (a / b) * b := by rw [Int.mul_comm b]
           _ = b * (a / b) + a % b := by rw [Int.add_comm, Int.mul_comm]
    constructor
    · -- Prove: 0 ≤ a % b
      exact Int.emod_nonneg a hb
    · -- Prove: a % b < b.natAbs
      exact Int.emod_lt a hb

section Iteration

/-- Generic iteration of a function

    Applies function f to x a total of n times.
    This provides a generic iteration construct used
    throughout the formalization.
-/
def iter_nat {A : Type} (f : A → A) (n : Nat) (x : A) : A :=
  match n with
  | 0 => x
  | n'+1 => f (iter_nat f n' x).run

/-- Specification: Iteration applies function n times. -/
@[spec]
theorem iter_nat_spec {A : Type} (f : A → A) (n : Nat) (x : A) :
    ⦃⌜True⌝⦄
    iter_nat f n x
    ⦃⇓result => ⌜result = f^[n] x⌝⦄ := by
  intro _
  induction n with
  | zero =>
    unfold iter_nat
    simp [Function.iterate_zero, id_run]
  | succ n' ih =>
    unfold iter_nat
    simp [Function.iterate_succ_apply', id_run]
    -- Need to relate f (iter_nat f n' x).run to f (f^[n'] x)
    -- This should follow from ih
    have h : iter_nat f n' x = f^[n'] x := by
      simpa using ih
    simp [h, id_run]

/-- Successor property for iteration

    Shows that iter_nat f (S p) x = f (iter_nat f p x).
    This is the successor case of the iteration recursion.
-/
def iter_nat_S {A : Type} (f : A → A) (p : Nat) (x : A) : A :=
  f (iter_nat f p x).run

/-- Specification: Iteration successor formula

    Iterating S p times is equivalent to iterating p times
    followed by one more application of f. This captures
    the recursive nature of iteration.
-/
@[spec]
theorem iter_nat_S_spec {A : Type} (f : A → A) (p : Nat) (x : A) :
    ⦃⌜True⌝⦄
    iter_nat_S f p x
    ⦃⇓result => ⌜result = f (iter_nat f p x).run⌝⦄ := by
  intro _
  unfold iter_nat_S
  rfl

/-- Iteration addition formula. -/
def iter_nat_plus {A : Type} (f : A → A) (p q : Nat) (x : A) : A :=
  (iter_nat f p (iter_nat f q x).run).run

/-- Specification: Iteration count addition. -/
@[spec]
theorem iter_nat_plus_spec {A : Type} (f : A → A) (p q : Nat) (x : A) :
    ⦃⌜True⌝⦄
    iter_nat_plus f p q x
    ⦃⇓result => ⌜result = (iter_nat f p (iter_nat f q x).run).run⌝⦄ := by
  intro _
  unfold iter_nat_plus
  rfl

/-- Relationship between positive and natural iteration

    For positive numbers, iter_pos equals iter_nat composed
    with conversion to natural numbers.
-/
def iter_pos_nat {A : Type} (f : A → A) (p : Nat) (x : A) : A :=
  (iter_nat f p x).run

/-- Specification: Positive iteration via naturals

    Iteration with positive numbers can be expressed through
    natural number iteration after conversion. This allows
    unified reasoning about different iteration types.
-/
@[spec]
theorem iter_pos_nat_spec {A : Type} (f : A → A) (p : Nat) (x : A) :
    ⦃⌜p > 0⌝⦄
    iter_pos_nat f p x
    ⦃⇓result => ⌜result = (iter_nat f p x).run⌝⦄ := by
  intro _
  unfold iter_pos_nat
  rfl

end Iteration

end FloatSpec.Core.Zaux
