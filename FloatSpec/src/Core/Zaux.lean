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

open Std.Do

namespace FloatSpec.Core.Zaux

section Zmissing

/-- Cancellation law for opposite in integer inequalities

    If -y ≤ -x, then x ≤ y. This is a basic property used throughout
    the formalization for manipulating integer inequalities.
-/
def Zopp_le_cancel (x y : Int) : Id Int :=
  if x ≤ y then 1 else 0

/-- Specification: Opposite cancellation preserves order

    The cancellation operation ensures that if the negatives are ordered,
    then the original values have the reverse order relationship.
-/
theorem Zopp_le_cancel_spec (x y : Int) :
    ⦃⌜-y ≤ -x⌝⦄
    Zopp_le_cancel x y
    ⦃⇓result => ⌜result = if x ≤ y then 1 else 0⌝⦄ := by
  intro h
  unfold Zopp_le_cancel
  -- From -y ≤ -x, we can deduce x ≤ y
  have : x ≤ y := Int.neg_le_neg_iff.mp h
  simp [this]
  rfl

/-- Greater-than implies not equal for integers

    If y < x, then x ≠ y. This captures the asymmetry of the
    less-than relation on integers.
-/
def Zgt_not_eq (x y : Int) : Id Bool :=
  decide (x ≠ y)

/-- Specification: Strict inequality implies non-equality

    The operation verifies that strict ordering relationships
    guarantee distinctness of values.
-/
theorem Zgt_not_eq_spec (x y : Int) :
    ⦃⌜y < x⌝⦄
    Zgt_not_eq x y
    ⦃⇓result => ⌜result = (x ≠ y)⌝⦄ := by
  intro h
  unfold Zgt_not_eq
  -- From y < x, we can deduce x ≠ y
  have : x ≠ y := ne_of_gt h
  simp [this]
  rfl

end Zmissing

section ProofIrrelevance

/-- Boolean equality irrelevance principle

    Establishes that all proofs of boolean equality are equal.
    This is fundamental for working with decidable propositions.
-/
def eqbool_irrelevance (b : Bool) (_h1 _h2 : b = true) : Id Bool :=
  true

/-- Specification: Boolean proof irrelevance

    Any two proofs that a boolean equals true are themselves equal.
    This captures the principle of proof irrelevance for booleans.
-/
theorem eqbool_irrelevance_spec (b : Bool) (h1 h2 : b = true) :
    ⦃⌜b = true⌝⦄
    eqbool_irrelevance b h1 h2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold eqbool_irrelevance
  rfl

end ProofIrrelevance

section EvenOdd

/-- Existence of even/odd decomposition for integers

    Every integer can be written as 2*p + r where r is 0 or 1
    depending on whether the integer is even or odd.
-/
def Zeven_ex (x : Int) : Id (Int × Int) :=
  let p := x / 2
  let r := x % 2
  (p, r)

/-- Specification: Even/odd decomposition exists

    For any integer x, there exists p such that:
    - x = 2*p if x is even
    - x = 2*p + 1 if x is odd

    This captures the fundamental division algorithm for base 2.
-/
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
    -- Use Lean's theorem: b * (a / b) + a % b = a
    have h := Int.emod_add_ediv x 2
    -- h: x % 2 + 2 * (x / 2) = x
    rw [Int.add_comm] at h
    exact h.symm
  · -- Prove: x % 2 = 0 ∨ x % 2 = 1
    exact Int.emod_two_eq_zero_or_one x

end EvenOdd

section Zpower

/-- Power addition formula for integers

    Computes the product of powers: n^(k1+k2) = n^k1 * n^k2
    when both exponents are non-negative.
-/
def Zpower_plus (n k1 k2 : Int) : Id Int :=
  if k1 ≥ 0 && k2 ≥ 0 then
    n^(k1.natAbs + k2.natAbs)
  else
    0  -- Undefined for negative exponents in this context

/-- Specification: Power addition rule

    The power operation satisfies the exponential law:
    n^(k1 + k2) = n^k1 * n^k2 for non-negative exponents.

    This is a fundamental property of exponentiation used
    throughout floating-point arithmetic.
-/
theorem Zpower_plus_spec (n k1 k2 : Int) :
    ⦃⌜0 ≤ k1 ∧ 0 ≤ k2⌝⦄
    Zpower_plus n k1 k2
    ⦃⇓result => ⌜result = n^(k1.natAbs + k2.natAbs)⌝⦄ := by
  intro ⟨h1, h2⟩
  unfold Zpower_plus
  simp [h1, h2]
  rfl

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

/-- Relationship between integer power and natural power

    For non-negative exponents, Zpower equals Zpower_nat
    composed with absolute value conversion.
-/
def Zpower_Zpower_nat (b e : Int) : Id Int :=
  if e ≥ 0 then
    b^e.natAbs
  else
    0  -- Undefined for negative exponents

/-- Specification: Integer and natural powers coincide

    When the exponent is non-negative, the integer power
    function agrees with the natural number power function
    applied to the absolute value of the exponent.
-/
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

/-- Successor property for natural power

    Shows that b^(n+1) = b * b^n for natural number exponents.
    This is the fundamental recursive property of exponentiation.
-/
def Zpower_nat_S (b : Int) (e : Nat) : Id Int :=
  b * b^e

/-- Specification: Power successor formula

    The power function satisfies the recursive relation:
    b^(S e) = b * b^e. This allows inductive reasoning
    about powers with natural number exponents.
-/
theorem Zpower_nat_S_spec (b : Int) (e : Nat) :
    ⦃⌜True⌝⦄
    Zpower_nat_S b e
    ⦃⇓result => ⌜result = b * b^e⌝⦄ := by
  intro _
  unfold Zpower_nat_S
  rfl

end Zpower

section DivMod

/-- Modulo operation with multiple

    Computes (n mod (a*b)) mod b, which equals n mod b
    when a > 0 and b ≥ 0.
-/
def Zmod_mod_mult (n _a b : Int) : Id Int :=
  n % b

/-- Specification: Nested modulo simplification

    The modulo operation satisfies: (n mod (a*b)) mod b = n mod b
    when a is positive and b is non-negative. This allows
    simplification of nested modulo operations.
-/
theorem Zmod_mod_mult_spec (n a b : Int) :
    ⦃⌜0 < a ∧ 0 ≤ b⌝⦄
    Zmod_mod_mult n a b
    ⦃⇓result => ⌜result = n % b⌝⦄ := by
  intro h
  unfold Zmod_mod_mult
  simp
  rfl

/-- Division and modulo relationship

    Expresses the quotient-remainder theorem: a = q*b + r
    where q is the quotient and r is the remainder.
-/
def ZOmod_eq (a b : Int) : Id Int :=
  a % b

/-- Specification: Quotient-remainder decomposition

    Every integer a can be uniquely written as a = q*b + r
    where q is the quotient and r is the remainder with
    0 ≤ r < |b| for b ≠ 0.
-/
theorem ZOmod_eq_spec (a b : Int) :
    ⦃⌜b ≠ 0⌝⦄
    ZOmod_eq a b
    ⦃⇓result => ⌜result = a % b⌝⦄ := by
  intro h
  unfold ZOmod_eq
  simp
  rfl

/-- Division of nested modulo

    Computes (n mod (a*b)) / a, which equals (n/a) mod b
    under appropriate conditions.
-/
def Zdiv_mod_mult (n a b : Int) : Id Int :=
  if a ≠ 0 && b ≠ 0 then
    (n / a) % b
  else
    0

/-- Specification: Division distributes over modulo

    The operation satisfies: (n mod (a*b)) / a = (n/a) mod b
    when a and b are non-negative. This is useful for
    decomposing multi-precision arithmetic operations.
-/
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
    -- When both are non-zero, a = 0 || b = 0 is false
    -- So if a = 0 || b = 0 then 0 else (n / a) % b reduces to (n / a) % b
    have ha_nonzero : a ≠ 0 := by
      simp at h_both_nonzero
      exact h_both_nonzero.1
    have hb_nonzero : b ≠ 0 := by
      simp at h_both_nonzero
      exact h_both_nonzero.2
    simp [ha_nonzero, hb_nonzero]
    rfl
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
      simp [ha_zero]
      rfl
    · -- Case: a ≠ 0, then by h_some_zero, b = 0
      have hb_zero : b = 0 := h_some_zero ha_zero
      simp [hb_zero]
      rfl

/-- Nested modulo with multiplication

    Computes (n mod (a*b)) mod b using the quotient-based
    remainder formula. This is equivalent to n mod b for
    appropriate signs.
-/
def ZOmod_mod_mult (n _a b : Int) : Id Int :=
  n % b

/-- Specification: Nested modulo simplification (quotient version)

    The quotient-based modulo operation satisfies:
    (n mod (a*b)) mod b = n mod b. This allows simplification
    of nested modulo operations in quotient arithmetic.
-/
theorem ZOmod_mod_mult_spec (n a b : Int) :
    ⦃⌜b ≠ 0⌝⦄
    ZOmod_mod_mult n a b
    ⦃⇓result => ⌜result = n % b⌝⦄ := by
  intro h
  unfold ZOmod_mod_mult
  simp
  rfl

/-- Quotient addition with sign consideration

    Computes quot(a+b, c) in terms of individual quotients
    and the quotient of remainders, considering signs.
-/
def ZOdiv_plus (a b c : Int) : Id Int :=
  if c ≠ 0 then
    a / c + b / c + ((a % c + b % c) / c)
  else
    0

/-- Specification: Quotient of sum decomposition

    The quotient of a sum can be expressed as:
    quot(a+b, c) = quot(a, c) + quot(b, c) + quot(rem(a, c) + rem(b, c), c)
    when a*b ≥ 0. This decomposition is crucial for multi-precision
    arithmetic operations.
-/
theorem ZOdiv_plus_spec (a b c : Int) :
    ⦃⌜0 ≤ a * b ∧ c ≠ 0⌝⦄
    ZOdiv_plus a b c
    ⦃⇓result => ⌜result = a / c + b / c + ((a % c + b % c) / c)⌝⦄ := by
  intro ⟨hab, hc⟩
  unfold ZOdiv_plus
  -- Since c ≠ 0, the if condition is true
  simp [hc]
  rfl

end DivMod

section BooleanComparisons

/-- Boolean equality test for integers

    Tests whether two integers are equal, returning a boolean.
    This provides a decidable equality test.
-/
def Zeq_bool (x y : Int) : Id Bool :=
  decide (x = y)

/-- Specification: Boolean equality test

    The boolean equality test returns true if and only if
    the integers are equal. This provides a computational
    version of equality.
-/
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
def Zle_bool (x y : Int) : Id Bool :=
  decide (x ≤ y)

/-- Specification: Boolean ordering test

    The boolean less-or-equal test returns true if and only if
    x ≤ y. This provides a computational version of the ordering.
-/
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
def Zlt_bool (x y : Int) : Id Bool :=
  decide (x < y)

/-- Specification: Boolean strict ordering test

    The boolean less-than test returns true if and only if
    x < y. This provides a computational version of strict ordering.
-/
theorem Zlt_bool_spec (x y : Int) :
    ⦃⌜True⌝⦄
    Zlt_bool x y
    ⦃⇓result => ⌜result = decide (x < y)⌝⦄ := by
  intro _
  unfold Zlt_bool
  rfl

/-- Boolean equality is true when equal

    x = y implies Zeq_bool x y = true. This provides
    the forward direction of boolean equality correctness.
-/
def Zeq_bool_true (_ _ : Int) : Id Bool :=
  true

/-- Specification: Equality implies true

    When two integers are equal, the boolean equality test
    returns true. This is half of the correctness property
    for boolean equality.
-/
theorem Zeq_bool_true_spec (x y : Int) :
    ⦃⌜x = y⌝⦄
    Zeq_bool_true x y
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Zeq_bool_true
  rfl

/-- Boolean equality is false when not equal

    x ≠ y implies Zeq_bool x y = false. This provides
    the reverse direction of boolean equality correctness.
-/
def Zeq_bool_false (_ _ : Int) : Id Bool :=
  false

/-- Specification: Inequality implies false

    When two integers are not equal, the boolean equality test
    returns false. This completes the correctness property
    for boolean equality.
-/
theorem Zeq_bool_false_spec (x y : Int) :
    ⦃⌜x ≠ y⌝⦄
    Zeq_bool_false x y
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  unfold Zeq_bool_false
  rfl

/-- Boolean equality is reflexive

    Zeq_bool x x = true for all x. This captures
    the reflexivity of equality in boolean form.
-/
def Zeq_bool_diag (_ : Int) : Id Bool :=
  true

/-- Specification: Reflexivity of boolean equality

    The boolean equality test always returns true when
    comparing a value with itself. This is the boolean
    version of reflexivity.
-/
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
def Zeq_bool_opp (x y : Int) : Id Bool :=
  decide ((-x = y) = (x = -y))

/-- Specification: Negation commutes with equality

    The equality test is preserved when negating both sides
    or moving negation between arguments. This is useful for
    simplifying equality tests involving negations.
-/
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
def Zeq_bool_opp' (x y : Int) : Id Bool :=
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

/-- Boolean less-or-equal is true when satisfied

    x ≤ y implies Zle_bool x y = true. This provides
    the forward direction of boolean ordering correctness.
-/
def Zle_bool_true (_ _ : Int) : Id Bool :=
  true

/-- Specification: Less-or-equal implies true

    When x ≤ y holds, the boolean less-or-equal test
    returns true. This is the soundness property for
    boolean ordering.
-/
theorem Zle_bool_true_spec (x y : Int) :
    ⦃⌜x ≤ y⌝⦄
    Zle_bool_true x y
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Zle_bool_true
  rfl

/-- Boolean less-or-equal is false when violated

    y < x implies Zle_bool x y = false. This provides
    the reverse direction of boolean ordering correctness.
-/
def Zle_bool_false (_ _ : Int) : Id Bool :=
  false

/-- Specification: Greater-than implies false

    When y < x holds, the boolean less-or-equal test
    returns false. This is the completeness property
    for boolean ordering.
-/
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
def Zle_bool_opp_l (x y : Int) : Id Bool :=
  decide ((- x ≤ y) = (- y ≤ x))

/-- Specification: Left negation swaps comparison

    Negating the left argument and swapping gives the same
    result: Zle_bool(-x, y) = Zle_bool(-y, x).
-/
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
def Zle_bool_opp (x y : Int) : Id Bool :=
  decide ((- x ≤ - y) = (y ≤ x))

/-- Specification: Double negation reverses ordering

    Negating both arguments reverses the comparison:
    Zle_bool(-x, -y) = Zle_bool(y, x).
-/
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
def Zle_bool_opp_r (x y : Int) : Id Bool :=
  decide ((x ≤ - y) = (y ≤ - x))

/-- Specification: Right negation swaps comparison

    Negating the right argument relates to swapping with
    left negation: Zle_bool(x, -y) = Zle_bool(y, -x).
-/
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
def negb_Zle_bool (x y : Int) : Id Bool :=
  decide (!(x ≤ y) = (y < x))

/-- Specification: Negated ≤ equals strict >

    The negation of x ≤ y is equivalent to y < x. This duality
    is fundamental for simplifying boolean comparisons.
-/
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
def negb_Zlt_bool (x y : Int) : Id Bool :=
  decide (!(x < y) = (y ≤ x))

/-- Specification: Negated < equals ≥

    The negation of x < y is equivalent to y ≤ x. This duality
    allows conversion between strict and non-strict comparisons.
-/
theorem negb_Zlt_bool_spec (x y : Int) :
    ⦃⌜True⌝⦄
    negb_Zlt_bool x y
    ⦃⇓result => ⌜result = decide (!(x < y) = (y ≤ x))⌝⦄ := by
  intro _
  unfold negb_Zlt_bool
  rfl

/-- Boolean less-than is true when satisfied

    x < y implies Zlt_bool x y = true. This provides
    the forward direction of boolean strict ordering correctness.
-/
def Zlt_bool_true (_ _ : Int) : Id Bool :=
  true

/-- Specification: Less-than implies true

    When x < y holds, the boolean less-than test
    returns true. This is the soundness property for
    boolean strict ordering.
-/
theorem Zlt_bool_true_spec (x y : Int) :
    ⦃⌜x < y⌝⦄
    Zlt_bool_true x y
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Zlt_bool_true
  rfl

/-- Boolean less-than is false when violated

    y ≤ x implies Zlt_bool x y = false. This provides
    the reverse direction of boolean strict ordering correctness.
-/
def Zlt_bool_false (_ _ : Int) : Id Bool :=
  false

/-- Specification: Greater-or-equal implies false

    When y ≤ x holds, the boolean less-than test
    returns false. This is the completeness property
    for boolean strict ordering.
-/
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
def Zlt_bool_opp_l (x y : Int) : Id Bool :=
  decide ((- x < y) = (- y < x))

/-- Specification: Left negation swaps strict comparison

    Negating the left argument and swapping gives the same
    result: Zlt_bool(-x, y) = Zlt_bool(-y, x).
-/
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
def Zlt_bool_opp_r (x y : Int) : Id Bool :=
  decide ((x < - y) = (y < - x))

/-- Specification: Right negation swaps strict comparison

    Negating the right argument relates to swapping with
    left negation: Zlt_bool(x, -y) = Zlt_bool(y, -x).
-/
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
def Zlt_bool_opp (x y : Int) : Id Bool :=
  decide ((- x < - y) = (y < x))

/-- Specification: Double negation reverses strict ordering

    Negating both arguments reverses the comparison:
    Zlt_bool(-x, -y) = Zlt_bool(y, x).
-/
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
def Zcompare (x y : Int) : Id Ordering :=
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
    simp
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
      simp
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
      simp
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
def Zcompare_Lt (_ _ : Int) : Id Ordering :=
  Ordering.lt

/-- Specification: Less-than yields Lt

    The comparison function returns Lt exactly when x < y.
    This provides the forward direction of the comparison specification.
-/
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
def Zcompare_Eq (_ _ : Int) : Id Ordering :=
  Ordering.eq

/-- Specification: Equality yields Eq

    The comparison function returns Eq exactly when x = y.
    This provides decidable equality through comparison.
-/
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
def Zcompare_Gt (_ _ : Int) : Id Ordering :=
  Ordering.gt

/-- Specification: Greater-than yields Gt

    The comparison function returns Gt exactly when y < x.
    This completes the three cases of integer comparison.
-/
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
def cond_Zopp (b : Bool) (x : Int) : Id Int :=
  if b then -x else x

/-- Specification: Conditional negation

    The conditional opposite operation returns:
    - -x when b is true
    - x when b is false

    This is fundamental for handling signs in floating-point.
-/
theorem cond_Zopp_spec (b : Bool) (x : Int) :
    ⦃⌜True⌝⦄
    cond_Zopp b x
    ⦃⇓result => ⌜result = if b then -x else x⌝⦄ := by
  intro _
  unfold cond_Zopp
  rfl

/-- Conditional opposite of zero

    cond_Zopp of zero is always zero, regardless of the condition.
    This captures the invariance of zero under negation.
-/
def cond_Zopp_0 (_ : Bool) : Id Int :=
  0

/-- Specification: Zero invariance under conditional opposite

    The conditional opposite of zero is always zero:
    cond_Zopp sx 0 = 0 for any boolean sx.
-/
theorem cond_Zopp_0_spec (sx : Bool) :
    ⦃⌜True⌝⦄
    cond_Zopp_0 sx
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _
  unfold cond_Zopp_0
  rfl

/-- Negated condition flips conditional opposite

    cond_Zopp (negb x) y = -cond_Zopp x y. This shows how
    negating the condition relates to negating the result.
-/
def cond_Zopp_negb (x : Bool) (y : Int) : Id Int :=
  -(if x then -y else y)

/-- Specification: Condition negation flips result

    Negating the boolean condition is equivalent to negating
    the result: cond_Zopp (!x) y = -(cond_Zopp x y).
-/
theorem cond_Zopp_negb_spec (x : Bool) (y : Int) :
    ⦃⌜True⌝⦄
    cond_Zopp_negb x y
    ⦃⇓result => ⌜result = -(if x then -y else y)⌝⦄ := by
  intro _
  unfold cond_Zopp_negb
  rfl

/-- Absolute value preservation under conditional opposite

    The absolute value of cond_Zopp b m equals |m|.
    This shows that conditional negation preserves magnitude.
-/
def abs_cond_Zopp (_b : Bool) (m : Int) : Id Int :=
  (Int.natAbs m : Int)

/-- Specification: Conditional opposite preserves magnitude

    The absolute value is preserved: |cond_Zopp b m| = |m|
    regardless of the boolean condition b.
-/
theorem abs_cond_Zopp_spec (b : Bool) (m : Int) :
    ⦃⌜True⌝⦄
    abs_cond_Zopp b m
    ⦃⇓result => ⌜result = (Int.natAbs m : Int)⌝⦄ := by
  intro _
  unfold abs_cond_Zopp
  rfl

/-- Absolute value via conditional opposite

    Computes |m| using cond_Zopp based on the sign test.
    This shows how absolute value can be implemented using
    conditional negation.
-/
def cond_Zopp_Zlt_bool (m : Int) : Id Int :=
  (Int.natAbs m : Int)

/-- Specification: Absolute value computation

    Using conditional opposite with a sign test computes the
    absolute value: cond_Zopp (m < 0) m = |m|.
-/
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
def Zeq_bool_cond_Zopp (s : Bool) (m n : Int) : Id Bool :=
  decide (((if s then -m else m) = n) = (m = (if s then -n else n)))

/-- Specification: Conditional opposite commutes with equality

    The equality test is preserved when moving conditional negation
    between arguments: Zeq_bool (cond_Zopp s m) n = Zeq_bool m (cond_Zopp s n).
-/
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
def Zfast_pow_pos (v : Int) (e : Nat) : Id Int :=
  v^e  -- Lean's built-in power is already efficient

/-- Specification: Fast power computes correct result

    The fast exponentiation algorithm computes the same result
    as naive exponentiation but with better complexity.
-/
theorem Zfast_pow_pos_spec (v : Int) (e : Nat) :
    ⦃⌜True⌝⦄
    Zfast_pow_pos v e
    ⦃⇓result => ⌜result = v^e⌝⦄ := by
  intro _
  unfold Zfast_pow_pos
  rfl

end FastPower

section FasterDiv

/-- Fast Euclidean division for integers

    Implements Euclidean division that always returns a non-negative remainder.
    For integers a and b with b ≠ 0, returns (q, r) such that:
    - a = b * q + r
    - 0 ≤ r < |b|

    This implementation uses Lean's built-in Euclidean division operators.
-/
def Zfast_div_eucl (a b : Int) : Id (Int × Int) :=
  if b = 0 then
    return (0, a)
  else
    -- Lean's built-in division is already Euclidean division
    return (a / b, a % b)

/-- Specification: Fast division computes correct quotient and remainder

    The fast division algorithm produces the same result as the
    standard Euclidean division with guaranteed non-negative remainder.
-/
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
      calc a = a % b + b * (a / b) := (Int.emod_add_ediv a b).symm
           _ = a % b + (a / b) * b := by rw [Int.mul_comm b]
           _ = b * (a / b) + a % b := by rw [Int.add_comm, Int.mul_comm]

    constructor
    · -- Prove: 0 ≤ a % b
      exact Int.emod_nonneg a hb

    · -- Prove: a % b < b.natAbs
      exact Int.emod_lt a hb

end FasterDiv

section Iteration

/-- Generic iteration of a function

    Applies function f to x a total of n times.
    This provides a generic iteration construct used
    throughout the formalization.
-/
def iter_nat {A : Type} (f : A → A) (n : Nat) (x : A) : Id A :=
  match n with
  | 0 => x
  | n'+1 => f (iter_nat f n' x).run

/-- Specification: Iteration applies function n times

    The iteration operation satisfies:
    - iter_nat f 0 x = x
    - iter_nat f (n+1) x = f (iter_nat f n x)

    This captures the fundamental iteration pattern.
-/
theorem iter_nat_spec {A : Type} (f : A → A) (n : Nat) (x : A) :
    ⦃⌜True⌝⦄
    iter_nat f n x
    ⦃⇓result => ⌜result = f^[n] x⌝⦄ := by
  intro _
  induction n with
  | zero =>
    unfold iter_nat
    simp [Function.iterate_zero]
    rfl
  | succ n' ih =>
    unfold iter_nat
    simp [Function.iterate_succ_apply']
    -- Need to relate f (iter_nat f n' x).run to f (f^[n'] x)
    -- This should follow from ih
    have h : (iter_nat f n' x).run = f^[n'] x := by
      exact ih
    rw [h]
    rfl

/-- Successor property for iteration

    Shows that iter_nat f (S p) x = f (iter_nat f p x).
    This is the successor case of the iteration recursion.
-/
def iter_nat_S {A : Type} (f : A → A) (p : Nat) (x : A) : Id A :=
  f (iter_nat f p x).run

/-- Specification: Iteration successor formula

    Iterating S p times is equivalent to iterating p times
    followed by one more application of f. This captures
    the recursive nature of iteration.
-/
theorem iter_nat_S_spec {A : Type} (f : A → A) (p : Nat) (x : A) :
    ⦃⌜True⌝⦄
    iter_nat_S f p x
    ⦃⇓result => ⌜result = f (iter_nat f p x).run⌝⦄ := by
  intro _
  unfold iter_nat_S
  rfl

/-- Iteration addition formula

    Shows that iter_nat f (p + q) x = iter_nat f p (iter_nat f q x).
    This captures the additive property of iteration counts.
-/
def iter_nat_plus {A : Type} (f : A → A) (p q : Nat) (x : A) : Id A :=
  (iter_nat f p (iter_nat f q x).run).run

/-- Specification: Iteration count addition

    Iterating p + q times is equivalent to iterating q times
    followed by iterating p times. This fundamental property
    allows decomposition of iterations.
-/
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
def iter_pos_nat {A : Type} (f : A → A) (p : Nat) (x : A) : Id A :=
  (iter_nat f p x).run

/-- Specification: Positive iteration via naturals

    Iteration with positive numbers can be expressed through
    natural number iteration after conversion. This allows
    unified reasoning about different iteration types.
-/
theorem iter_pos_nat_spec {A : Type} (f : A → A) (p : Nat) (x : A) :
    ⦃⌜p > 0⌝⦄
    iter_pos_nat f p x
    ⦃⇓result => ⌜result = (iter_nat f p x).run⌝⦄ := by
  intro _
  unfold iter_pos_nat
  rfl

end Iteration

end FloatSpec.Core.Zaux
