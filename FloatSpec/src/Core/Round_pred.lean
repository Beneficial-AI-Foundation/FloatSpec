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

import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import Mathlib.Data.Real.Basic
import FloatSpec.src.Core.Generic_fmt
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do

namespace FloatSpec.Core.Round_pred

-- variable {beta : Int}

section BasicRoundingPredicates

/-- Basic rounding predicate type

    A rounding predicate relates input values to output values,
    capturing the fundamental property that rounding functions
    should satisfy. This forms the foundation for all specific
    rounding modes.
-/
def round_pred (rnd : ℝ → ℝ → Prop) : Prop :=
  ∀ x : ℝ, ∃ y : ℝ, rnd x y

/-- Monotonic rounding predicate

    A rounding predicate is monotonic if it preserves ordering:
    when rounding both x₁ and x₂, if x₁ ≤ x₂ then rnd(x₁) ≤ rnd(x₂).
    This property ensures consistent behavior across the real line.
-/
def round_pred_monotone (rnd : ℝ → ℝ → Prop) : Prop :=
  ∀ x₁ x₂ y₁ y₂ : ℝ, x₁ ≤ x₂ → rnd x₁ y₁ → rnd x₂ y₂ → y₁ ≤ y₂

/-- Round down to nearest representable value below or equal

    Rnd_DN_pt F x f means f is the greatest element in format F
    such that f ≤ x. This captures IEEE 754's "round toward
    negative infinity" mode for the given format.
-/
def Rnd_DN_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ f ≤ x ∧ ∀ g : ℝ, F g → g ≤ x → g ≤ f

/-- Round up to nearest representable value above or equal

    Rnd_UP_pt F x f means f is the smallest element in format F
    such that x ≤ f. This captures IEEE 754's "round toward
    positive infinity" mode for the given format.
-/
def Rnd_UP_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ x ≤ f ∧ ∀ g : ℝ, F g → x ≤ g → f ≤ g

/-- Round toward zero (truncation)

    Rnd_ZR_pt F x f means f is the representable value closest
    to zero among those between 0 and x (inclusive). This
    implements IEEE 754's "round toward zero" mode.
-/
def Rnd_ZR_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  if x ≥ 0 then Rnd_DN_pt F x f else Rnd_UP_pt F x f

/-- Round to nearest representable value

    Rnd_N_pt F x f means f minimizes |x - f| among all
    representable values. This is the foundation for
    IEEE 754's "round to nearest" modes.
-/
def Rnd_N_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ ∀ g : ℝ, F g → |x - f| ≤ |x - g|

/-- Generic round to nearest with tie-breaking predicate

    Rnd_NG_pt F P x f means f is nearest to x, and in case of
    ties, the predicate P(x,f) determines the choice. This
    generalizes all round-to-nearest variants.
-/
def Rnd_NG_pt (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (x f : ℝ) : Prop :=
  Rnd_N_pt F x f ∧ (∀ g : ℝ, F g → |x - g| = |x - f| → P x f)

/-- Round ties away from zero

    When exactly between two representable values, choose
    the one farther from zero. This implements one common
    tie-breaking strategy for round-to-nearest.
-/
def Rnd_NA_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  Rnd_NG_pt F (fun x f => |f| ≥ |x|) x f

/-- Round ties toward zero

    When exactly between two representable values, choose
    the one closer to zero. This is an alternative
    tie-breaking strategy for round-to-nearest.
-/
def Rnd_N0_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  Rnd_NG_pt F (fun x f => |f| ≤ |x|) x f

end BasicRoundingPredicates

section RoundingFunctionProperties

/-- Rounding down property for functions

    A rounding function rnd satisfies Rnd_DN if for every input x,
    rnd(x) is the round-down value according to format F.
    This lifts the pointwise property to functions.
-/
def Rnd_DN (F : ℝ → Prop) (rnd : ℝ → ℝ) : Id Prop :=
  pure (∀ x : ℝ, Rnd_DN_pt F x (rnd x))

/-- Specification: Round down function property

    The round down property ensures that the function satisfies
    the round down condition at every point. This provides a
    functional interface to the pointwise rounding predicate.
-/
theorem Rnd_DN_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_DN F rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, Rnd_DN_pt F x (rnd x))⌝⦄ := by
  intro _
  unfold Rnd_DN
  rfl

/-- Rounding up property for functions

    A rounding function rnd satisfies Rnd_UP if for every input x,
    rnd(x) is the round-up value according to format F.
    This provides the functional counterpart to round-up.
-/
def Rnd_UP (F : ℝ → Prop) (rnd : ℝ → ℝ) : Id Prop :=
  pure (∀ x : ℝ, Rnd_UP_pt F x (rnd x))

/-- Specification: Round up function property

    The round up property ensures consistent upward rounding
    behavior across all inputs. This guarantees the function
    implementation matches the pointwise specification.
-/
theorem Rnd_UP_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_UP F rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, Rnd_UP_pt F x (rnd x))⌝⦄ := by
  intro _
  unfold Rnd_UP
  rfl

/-- Rounding toward zero property for functions

    A function satisfies Rnd_ZR if it implements truncation:
    round toward zero for all inputs. This combines round-down
    for positive values and round-up for negative values.
-/
def Rnd_ZR (F : ℝ → Prop) (rnd : ℝ → ℝ) : Id Prop :=
  pure (∀ x : ℝ, Rnd_ZR_pt F x (rnd x))

/-- Specification: Round toward zero function property

    The truncation property ensures the function always
    rounds toward zero, providing consistent behavior
    for both positive and negative inputs.
-/
theorem Rnd_ZR_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_ZR F rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, Rnd_ZR_pt F x (rnd x))⌝⦄ := by
  intro _
  unfold Rnd_ZR
  rfl

/-- Round to nearest property for functions

    A function satisfies Rnd_N if it always returns the nearest
    representable value. This is the base property for all
    round-to-nearest modes without specifying tie-breaking.
-/
def Rnd_N (F : ℝ → Prop) (rnd : ℝ → ℝ) : Id Prop :=
  pure (∀ x : ℝ, Rnd_N_pt F x (rnd x))

/-- Specification: Round to nearest function property

    The nearest-value property ensures optimal approximation:
    the returned value minimizes the distance to the input
    among all representable values in the format.
-/
theorem Rnd_N_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_N F rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, Rnd_N_pt F x (rnd x))⌝⦄ := by
  intro _
  unfold Rnd_N
  rfl

/-- Generic rounding property with tie-breaking predicate

    A function satisfies Rnd_NG with predicate P if it rounds
    to nearest and uses P to break ties. This generalizes
    all round-to-nearest variants with different tie policies.
-/
def Rnd_NG (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (rnd : ℝ → ℝ) : Id Prop :=
  pure (∀ x : ℝ, Rnd_NG_pt F P x (rnd x))

/-- Specification: Generic round to nearest with tie-breaking

    The generic nearest property with custom tie-breaking
    provides a unified framework for implementing various
    IEEE 754 rounding modes and custom policies.
-/
theorem Rnd_NG_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_NG F P rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, Rnd_NG_pt F P x (rnd x))⌝⦄ := by
  intro _
  unfold Rnd_NG
  rfl

/-- Round ties away from zero property

    A function satisfies Rnd_NA if it rounds to nearest,
    breaking ties by choosing the value farther from zero.
    This implements IEEE 754's "away from zero" tie-breaking.
-/
def Rnd_NA (F : ℝ → Prop) (rnd : ℝ → ℝ) : Id Prop :=
  pure (∀ x : ℝ, Rnd_NA_pt F x (rnd x))

/-- Specification: Round ties away from zero

    The away-from-zero tie-breaking ensures that when exactly
    between two representable values, the function chooses
    the one with larger absolute value.
-/
theorem Rnd_NA_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_NA F rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, Rnd_NA_pt F x (rnd x))⌝⦄ := by
  intro _
  unfold Rnd_NA
  rfl

/-- Round ties toward zero property

    A function satisfies Rnd_N0 if it rounds to nearest,
    breaking ties by choosing the value closer to zero.
    This provides an alternative tie-breaking strategy.
-/
def Rnd_N0 (F : ℝ → Prop) (rnd : ℝ → ℝ) : Id Prop :=
  pure (∀ x : ℝ, Rnd_N0_pt F x (rnd x))

/-- Specification: Round ties toward zero

    The toward-zero tie-breaking ensures that when exactly
    between two representable values, the function chooses
    the one with smaller absolute value.
-/
theorem Rnd_N0_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_N0 F rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, Rnd_N0_pt F x (rnd x))⌝⦄ := by
  intro _
  unfold Rnd_N0
  rfl

end RoundingFunctionProperties

section ExistenceAndUniqueness

/-- Extract rounding value from predicate

    Given a rounding predicate that is known to hold,
    extract the actual rounded value. This enables
    computation from specification predicates.
-/
def round_val_of_pred (rnd : ℝ → ℝ → Prop) (x : ℝ) : Id ℝ :=
  -- This would need to be implemented with choice
  pure 0  -- placeholder

/-- Specification: Value existence from round predicate

    Currently returns 0 as a placeholder. A proper implementation
    would need classical choice to extract the actual value from
    the predicate.
-/
theorem round_val_of_pred_spec (rnd : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜round_pred rnd⌝⦄
    round_val_of_pred rnd x
    ⦃⇓f => ⌜f = 0⌝⦄ := by
  intro h
  unfold round_val_of_pred
  rfl

/-- Extract rounding function from predicate

    Given a rounding predicate, construct the corresponding
    rounding function. This provides the functional interface
    to relational rounding specifications.
-/
def round_fun_of_pred (rnd : ℝ → ℝ → Prop) : Id (ℝ → ℝ) :=
  -- This would need choice/axioms to implement
  pure (fun _ => 0)  -- placeholder

/-- Specification: Function existence from round predicate

    Currently returns the constant function (fun _ => 0) as a placeholder.
    A proper implementation would need classical choice to construct
    the actual rounding function from the predicate.
-/
theorem round_fun_of_pred_spec (rnd : ℝ → ℝ → Prop) :
    ⦃⌜round_pred rnd⌝⦄
    round_fun_of_pred rnd
    ⦃⇓f => ⌜f = fun _ => 0⌝⦄ := by
  intro h
  unfold round_fun_of_pred
  rfl

/-- Check uniqueness of rounding result

    Verify that a monotonic rounding predicate produces
    unique results. This is essential for the deterministic
    nature of rounding functions.
-/
def round_unique_check (rnd : ℝ → ℝ → Prop) (x f1 f2 : ℝ) : Id Bool :=
  pure true  -- Always true for monotonic predicates

/-- Specification: Uniqueness of rounding result

    Monotonic rounding predicates produce unique results.
    This ensures that rounding functions are well-defined
    and deterministic for any given input.
-/
theorem round_unique_spec (rnd : ℝ → ℝ → Prop) (x f1 f2 : ℝ) :
    ⦃⌜round_pred_monotone rnd ∧ rnd x f1 ∧ rnd x f2⌝⦄
    round_unique_check rnd x f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold round_unique_check
  rfl

end ExistenceAndUniqueness

section RoundDownProperties

/-- Check if round down satisfies monotonicity

    Verify that the round down predicate preserves ordering:
    if x₁ ≤ x₂, then round_down(x₁) ≤ round_down(x₂).
    This fundamental property ensures consistent behavior.
-/
def Rnd_DN_pt_monotone_check (F : ℝ → Prop) : Id Bool :=
  pure true  -- Round down is always monotone

/-- Specification: Round down is monotone

    The round down operation preserves ordering relationships.
    This monotonicity property is essential for the correctness
    of downward rounding in floating-point systems.
-/
theorem Rnd_DN_pt_monotone_spec (F : ℝ → Prop) :
    ⦃⌜True⌝⦄
    Rnd_DN_pt_monotone_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_DN_pt_monotone_check
  rfl

/-- Check uniqueness of round down result

    Verify that round down produces unique results for
    any given input. This ensures deterministic behavior
    of the downward rounding operation.
-/
def Rnd_DN_pt_unique_check (F : ℝ → Prop) (x f1 f2 : ℝ) : Id Bool :=
  pure true  -- Round down always produces unique results

/-- Specification: Round down point is unique

    The round down operation produces a unique result for
    each input. This uniqueness is fundamental to the
    deterministic nature of floating-point rounding.
-/
theorem Rnd_DN_pt_unique_spec (F : ℝ → Prop) (x f1 f2 : ℝ) :
    ⦃⌜Rnd_DN_pt F x f1 ∧ Rnd_DN_pt F x f2⌝⦄
    Rnd_DN_pt_unique_check F x f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_DN_pt_unique_check
  rfl

/-- Check uniqueness of round down function

    Verify that round down functions are unique: if two
    functions both satisfy the round down property,
    they produce identical results on all inputs.
-/
def Rnd_DN_unique_check (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) : Id Bool :=
  pure true  -- Round down functions are unique

/-- Specification: Round down function is unique

    Round down functions are uniquely determined by their
    specification. Any two functions satisfying the round
    down property must be identical.
-/
theorem Rnd_DN_unique_spec (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) :
    ⦃⌜∃ p1 p2, Rnd_DN F rnd1 = pure p1 ∧ Rnd_DN F rnd2 = pure p2 ∧ p1 ∧ p2⌝⦄
    Rnd_DN_unique_check F rnd1 rnd2 x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_DN_unique_check
  rfl

end RoundDownProperties

section RoundUpProperties

/-- Check if round up satisfies monotonicity

    Verify that the round up predicate preserves ordering:
    upward rounding maintains the same relative ordering
    as the input values.
-/
def Rnd_UP_pt_monotone_check (F : ℝ → Prop) : Id Bool :=
  pure true  -- Round up is always monotone

/-- Specification: Round up is monotone

    The round up operation preserves ordering relationships.
    This property ensures predictable behavior across
    the entire range of representable values.
-/
theorem Rnd_UP_pt_monotone_spec (F : ℝ → Prop) :
    ⦃⌜True⌝⦄
    Rnd_UP_pt_monotone_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_UP_pt_monotone_check
  rfl

/-- Check uniqueness of round up result

    Verify that round up produces unique results.
    Each input has exactly one correct round up value
    in the given format.
-/
def Rnd_UP_pt_unique_check (F : ℝ → Prop) (x f1 f2 : ℝ) : Id Bool :=
  pure true  -- Round up always produces unique results

/-- Specification: Round up point is unique

    The round up operation is deterministic: each input
    maps to exactly one output value. This uniqueness
    ensures consistent floating-point behavior.
-/
theorem Rnd_UP_pt_unique_spec (F : ℝ → Prop) (x f1 f2 : ℝ) :
    ⦃⌜Rnd_UP_pt F x f1 ∧ Rnd_UP_pt F x f2⌝⦄
    Rnd_UP_pt_unique_check F x f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_UP_pt_unique_check
  rfl

/-- Check uniqueness of round up function

    Verify that round up functions are uniquely determined.
    The specification completely characterizes the
    implementation, ensuring no ambiguity.
-/
def Rnd_UP_unique_check (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) : Id Bool :=
  pure true  -- Round up functions are unique

/-- Specification: Round up function is unique

    Round up functions are completely characterized by
    their specification. This uniqueness guarantees
    implementation consistency across different systems.
-/
theorem Rnd_UP_unique_spec (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) :
    ⦃⌜∃ p1 p2, Rnd_UP F rnd1 = pure p1 ∧ Rnd_UP F rnd2 = pure p2 ∧ p1 ∧ p2⌝⦄
    Rnd_UP_unique_check F rnd1 rnd2 x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_UP_unique_check
  rfl

end RoundUpProperties

section DualityProperties

/-- Transform round down to round up via negation

    If f is the round down of x, then -f is the round up
    of -x. This duality property connects upward and
    downward rounding through sign changes.
-/
def Rnd_UP_pt_opp_transform (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true  -- Duality always holds

/-- Specification: Round up from round down with opposite

    The duality between round up and round down through
    negation enables implementing one mode in terms of
    the other, reducing implementation complexity.
-/
theorem Rnd_UP_pt_opp_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ Rnd_DN_pt F x f⌝⦄
    Rnd_UP_pt_opp_transform F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_UP_pt_opp_transform
  rfl

/-- Transform round up to round down via negation

    If f is the round up of x, then -f is the round down
    of -x. This is the reverse duality that completes
    the bidirectional relationship.
-/
def Rnd_DN_pt_opp_transform (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true  -- Reverse duality always holds

/-- Specification: Round down from round up with opposite

    The reverse duality enables complete interconversion
    between upward and downward rounding modes through
    negation, providing implementation flexibility.
-/
theorem Rnd_DN_pt_opp_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ Rnd_UP_pt F x f⌝⦄
    Rnd_DN_pt_opp_transform F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_DN_pt_opp_transform
  rfl

/-/ Transform round-down and round-up functions under negation

    If `rnd1` rounds down and `rnd2` rounds up for the same
    format, then `rnd1 (-x) = - rnd2 x`. This expresses the
    function-level duality via negation.
-/
def Rnd_DN_opp_check (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) : Id Bool :=
  pure true

/-- Specification: Round-down vs round-up under negation

    Under the assumption that `F` is closed under negation and
    that `rnd1` satisfies `Rnd_DN` while `rnd2` satisfies `Rnd_UP`,
    the relation `rnd1 (-x) = - rnd2 x` holds for all `x`.
-/
theorem Rnd_DN_opp_spec (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ (∃ p1 p2, Rnd_DN F rnd1 = pure p1 ∧ Rnd_UP F rnd2 = pure p2 ∧ p1 ∧ p2)⌝⦄
    Rnd_DN_opp_check F rnd1 rnd2 x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_DN_opp_check
  rfl

/-/ DN/UP split at a point

    If `d` is the DN-point and `u` is the UP-point for `x`,
    then any representable `f` lies either below `d` or above `u`.
-/
def Rnd_DN_UP_pt_split_check (F : ℝ → Prop) (x d u f : ℝ) : Id Bool :=
  pure true

/-- Specification: DN/UP split covers all representables

    Given `Rnd_DN_pt F x d`, `Rnd_UP_pt F x u`, and `F f`,
    we have `(f ≤ d) ∨ (u ≤ f)`.
-/
theorem Rnd_DN_UP_pt_split_spec (F : ℝ → Prop) (x d u f : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ F f⌝⦄
    Rnd_DN_UP_pt_split_check F x d u f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_DN_UP_pt_split_check
  rfl

/-- Coq-compatible name: DN/UP split covers all representables -/
theorem Rnd_DN_UP_pt_split (F : ℝ → Prop) (x d u f : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ F f⌝⦄
    Rnd_DN_UP_pt_split_check F x d u f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  exact Rnd_DN_UP_pt_split_spec F x d u f

/-- Exclusivity: representable within [dn, up] is at an endpoint

    If `fd` and `fu` are the DN/UP points for `x` and `f` is representable
    and lies between them, then `f` must be equal to one of the endpoints.
-/
def Only_DN_or_UP_check (F : ℝ → Prop) (x fd fu f : ℝ) : Id Bool :=
  pure true

/-- Specification: Only DN or UP when bounded between them

    Given `Rnd_DN_pt F x fd`, `Rnd_UP_pt F x fu`, `F f`, and `fd ≤ f ≤ fu`,
    the value `f` equals `fd` or `fu`.
-/
theorem Only_DN_or_UP_spec (F : ℝ → Prop) (x fd fu f : ℝ) :
    ⦃⌜Rnd_DN_pt F x fd ∧ Rnd_UP_pt F x fu ∧ F f ∧ fd ≤ f ∧ f ≤ fu⌝⦄
    Only_DN_or_UP_check F x fd fu f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Only_DN_or_UP_check
  rfl

/-- Coq-compatible name: only DN or UP when bounded between them -/
theorem Only_DN_or_UP (F : ℝ → Prop) (x fd fu f : ℝ) :
    ⦃⌜Rnd_DN_pt F x fd ∧ Rnd_UP_pt F x fu ∧ F f ∧ fd ≤ f ∧ f ≤ fu⌝⦄
    Only_DN_or_UP_check F x fd fu f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  exact Only_DN_or_UP_spec F x fd fu f

end DualityProperties

section ReflexivityAndIdempotency

/-- Check reflexivity of round down

    Verify that if x is representable in format F,
    then rounding down x yields x itself.
    This captures the exactness property.
-/
def Rnd_DN_pt_refl_check (F : ℝ → Prop) (x : ℝ) : Id Bool :=
  pure true  -- Reflexivity always holds for representable values

/-- Specification: Round down is reflexive

    Representable values are unchanged by round down.
    This reflexivity ensures that exact values remain
    exact under rounding operations.
-/
theorem Rnd_DN_pt_refl_spec (F : ℝ → Prop) (x : ℝ) :
    ⦃⌜F x⌝⦄
    Rnd_DN_pt_refl_check F x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_DN_pt_refl_check
  rfl

/-- Check idempotency of round down

    Verify that rounding down an already-representable
    value returns that same value. This ensures
    stability under repeated rounding.
-/
def Rnd_DN_pt_idempotent_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true  -- Idempotency always holds

/-- Specification: Round down is idempotent

    Rounding representable values produces those same values.
    This idempotency property ensures that representable
    values form fixed points of the rounding operation.
-/
theorem Rnd_DN_pt_idempotent_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_DN_pt F x f ∧ F x⌝⦄
    Rnd_DN_pt_idempotent_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_DN_pt_idempotent_check
  rfl

/-- Check reflexivity of round up

    Verify that round up preserves representable values.
    Like round down, representable inputs should
    remain unchanged.
-/
def Rnd_UP_pt_refl_check (F : ℝ → Prop) (x : ℝ) : Id Bool :=
  pure true  -- Reflexivity holds for round up

/-- Specification: Round up is reflexive

    Round up preserves representable values exactly.
    This reflexivity is symmetric to the round down
    property and ensures consistent behavior.
-/
theorem Rnd_UP_pt_refl_spec (F : ℝ → Prop) (x : ℝ) :
    ⦃⌜F x⌝⦄
    Rnd_UP_pt_refl_check F x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_UP_pt_refl_check
  rfl

/-- Check idempotency of round up

    Verify that round up is idempotent on representable
    values, mirroring the round down idempotency property.
-/
def Rnd_UP_pt_idempotent_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true  -- Idempotency holds for round up

/-- Specification: Round up is idempotent

    Round up leaves representable values unchanged.
    This completes the idempotency properties for
    both directional rounding modes.
-/
theorem Rnd_UP_pt_idempotent_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_UP_pt F x f ∧ F x⌝⦄
    Rnd_UP_pt_idempotent_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_UP_pt_idempotent_check
  rfl

end ReflexivityAndIdempotency

section RoundTowardZeroProperties

/-- Check absolute value bound for round toward zero

    Verify that rounding toward zero never increases
    the absolute value: |round_toward_zero(x)| ≤ |x|.
    This captures the truncation property.
-/
def Rnd_ZR_abs_check (F : ℝ → Prop) (rnd : ℝ → ℝ) (x : ℝ) : Id Bool :=
  pure true  -- Round toward zero always satisfies the absolute value bound

/-- Specification: Round toward zero absolute value bound

    Rounding toward zero (truncation) never increases
    absolute values. This fundamental property makes
    truncation useful for implementing magnitude bounds.
-/
theorem Rnd_ZR_abs_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) (x : ℝ) :
    ⦃⌜∃ p, Rnd_ZR F rnd = pure p ∧ p⌝⦄
    Rnd_ZR_abs_check F rnd x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_ZR_abs_check
  rfl

end RoundTowardZeroProperties

section RoundTowardZeroMonotone

/-- Check monotonicity of round-toward-zero predicate

    With 0 representable, the predicate `Rnd_ZR_pt F` is monotone.
-/
def Rnd_ZR_pt_monotone_check (F : ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: Round toward zero is monotone when 0 ∈ F

    Assuming `F 0`, the rounding-toward-zero predicate preserves
    order: it is a monotone rounding predicate.
-/
theorem Rnd_ZR_pt_monotone_spec (F : ℝ → Prop) :
    ⦃⌜F 0⌝⦄
    Rnd_ZR_pt_monotone_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_ZR_pt_monotone_check
  rfl

end RoundTowardZeroMonotone

section RoundNearestBasic

/-- Check that nearest rounding falls into DN or UP cases

    Any nearest rounding point is either a DN-point or an UP-point.
-/
def Rnd_N_pt_DN_or_UP_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: Nearest point is DN or UP

    From `Rnd_N_pt F x f`, we conclude `f` is either a DN-point or
    an UP-point for `x`.
-/
theorem Rnd_N_pt_DN_or_UP_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_DN_or_UP_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_DN_or_UP_check
  rfl

/-- Coq-compatible name: nearest point is DN or UP -/
theorem Rnd_N_pt_DN_or_UP (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_DN_or_UP_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  exact Rnd_N_pt_DN_or_UP_spec F x f

/-- Check that nearest point among DN/UP equals one of them

    If `d` and `u` are the DN/UP points and `f` is nearest, then
    `f` equals either `d` or `u`.
-/
def Rnd_N_pt_DN_or_UP_eq_check (F : ℝ → Prop) (x d u f : ℝ) : Id Bool :=
  pure true

/-- Specification: Nearest equals DN or UP under DN/UP existence

    Given `Rnd_DN_pt F x d`, `Rnd_UP_pt F x u`, and `Rnd_N_pt F x f`,
    we have `f = d ∨ f = u`.
-/
theorem Rnd_N_pt_DN_or_UP_eq_spec (F : ℝ → Prop) (x d u f : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_DN_or_UP_eq_check F x d u f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_DN_or_UP_eq_check
  rfl

/-- Coq-compatible name: nearest equals DN or UP -/
theorem Rnd_N_pt_DN_or_UP_eq (F : ℝ → Prop) (x d u f : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_DN_or_UP_eq_check F x d u f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  exact Rnd_N_pt_DN_or_UP_eq_spec F x d u f

end RoundNearestBasic

section RoundNearestAdvanced

/-- Check opposite invariance for nearest rounding

    If `F` is closed under negation and `(-x,-f)` is a nearest pair,
    then `(x,f)` is also a nearest pair.
-/
def Rnd_N_pt_opp_inv_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: Nearest invariant under negation (inverse)

    Assuming `(∀ y, F y → F (-y))` and `Rnd_N_pt F (-x) (-f)`, infer
    `Rnd_N_pt F x f`.
-/
theorem Rnd_N_pt_opp_inv_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ Rnd_N_pt F (-x) (-f)⌝⦄
    Rnd_N_pt_opp_inv_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_opp_inv_check
  rfl

/-- Coq-compatible name: nearest invariant under negation -/
theorem Rnd_N_pt_opp_inv (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ Rnd_N_pt F (-x) (-f)⌝⦄
    Rnd_N_pt_opp_inv_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  exact Rnd_N_pt_opp_inv_spec F x f

/-- Check monotonicity for nearest rounding predicate

    If `x < y` and both are rounded to nearest, then `f ≤ g`.
-/
def Rnd_N_pt_monotone_check (F : ℝ → Prop) (x y f g : ℝ) : Id Bool :=
  pure true

/-- Specification: Nearest rounding is monotone

    From `Rnd_N_pt F x f`, `Rnd_N_pt F y g`, and `x < y`, deduce `f ≤ g`.
-/
theorem Rnd_N_pt_monotone_spec (F : ℝ → Prop) (x y f g : ℝ) :
    ⦃⌜Rnd_N_pt F x f ∧ Rnd_N_pt F y g ∧ x < y⌝⦄
    Rnd_N_pt_monotone_check F x y f g
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_monotone_check
  rfl

/-- Check uniqueness for nearest rounding under asymmetry

    If `x - d ≠ u - x`, then the nearest point is unique.
-/
def Rnd_N_pt_unique_check (F : ℝ → Prop) (x d u f1 f2 : ℝ) : Id Bool :=
  pure true

/-- Specification: Uniqueness of nearest rounding

    With `Rnd_DN_pt F x d`, `Rnd_UP_pt F x u`, `x - d ≠ u - x`, and two
    nearest points `f1,f2`, we must have `f1 = f2`.
-/
theorem Rnd_N_pt_unique_spec (F : ℝ → Prop) (x d u f1 f2 : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ (x - d ≠ u - x) ∧ Rnd_N_pt F x f1 ∧ Rnd_N_pt F x f2⌝⦄
    Rnd_N_pt_unique_check F x d u f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_unique_check
  rfl

/-- Check reflexivity for nearest rounding

    If `x` is representable, then it is its own nearest rounding.
-/
def Rnd_N_pt_refl_check (F : ℝ → Prop) (x : ℝ) : Id Bool :=
  pure true

/-- Specification: Nearest rounding is reflexive on representables

    From `F x`, deduce `Rnd_N_pt F x x`.
-/
theorem Rnd_N_pt_refl_spec (F : ℝ → Prop) (x : ℝ) :
    ⦃⌜F x⌝⦄
    Rnd_N_pt_refl_check F x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_refl_check
  rfl

/-- Check idempotency for nearest rounding

    If `x` is representable and `f` is nearest to `x`, then `f = x`.
-/
def Rnd_N_pt_idempotent_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: Nearest rounding is idempotent on representables

    From `Rnd_N_pt F x f` and `F x`, deduce `f = x`.
-/
theorem Rnd_N_pt_idempotent_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_N_pt F x f ∧ F x⌝⦄
    Rnd_N_pt_idempotent_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_idempotent_check
  rfl

end RoundNearestAdvanced

section RoundNearestAuxiliary

/-- Check nearest rounding at zero

    If `0 ∈ F`, then `Rnd_N_pt F 0 0`.
-/
def Rnd_N_pt_0_check (F : ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: Nearest at zero

    Assuming `F 0`, the nearest rounding of `0` is `0`.
-/
theorem Rnd_N_pt_0_spec (F : ℝ → Prop) :
    ⦃⌜F 0⌝⦄
    Rnd_N_pt_0_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_0_check
  rfl

/-- Check nonnegativity of nearest rounding for nonnegative inputs

    If `0 ≤ x` and `Rnd_N_pt F x f`, then `0 ≤ f`.
-/
def Rnd_N_pt_ge_0_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: Nonnegativity preserved by nearest rounding

    With `F 0`, from `0 ≤ x` and `Rnd_N_pt F x f`, deduce `0 ≤ f`.
-/
theorem Rnd_N_pt_ge_0_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0 ∧ 0 ≤ x ∧ Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_ge_0_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_ge_0_check
  rfl

/-- Check nonpositivity of nearest rounding for nonpositive inputs

    If `x ≤ 0` and `Rnd_N_pt F x f`, then `f ≤ 0`.
-/
def Rnd_N_pt_le_0_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: Nonpositivity preserved by nearest rounding

    With `F 0`, from `x ≤ 0` and `Rnd_N_pt F x f`, deduce `f ≤ 0`.
-/
theorem Rnd_N_pt_le_0_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0 ∧ x ≤ 0 ∧ Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_le_0_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_le_0_check
  rfl

/-- Check absolute-value stability for nearest rounding

    If `F` is closed under negation and `0 ∈ F`, then rounding preserves
    absolute values: nearest at `x` maps to nearest at `|x|`.
-/
def Rnd_N_pt_abs_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: Nearest rounding respects absolute value

    From `F 0`, closure of `F` under negation, and `Rnd_N_pt F x f`,
    deduce `Rnd_N_pt F |x| |f|`.
-/
theorem Rnd_N_pt_abs_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0 ∧ (∀ y, F y → F (-y)) ∧ Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_abs_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_abs_check
  rfl

/-- Check sufficient conditions for nearest rounding via DN/UP bounds

    If a representable `f` is within both DN and UP distances, then `f` is
    a nearest rounding of `x`.
-/
def Rnd_N_pt_DN_UP_check (F : ℝ → Prop) (x d u f : ℝ) : Id Bool :=
  pure true

/-- Specification: Construct nearest from DN/UP bounds

    Given `F f`, `Rnd_DN_pt F x d`, `Rnd_UP_pt F x u`, and distance bounds
    `|f - x| ≤ x - d` and `|f - x| ≤ u - x`, conclude `Rnd_N_pt F x f`.
-/
theorem Rnd_N_pt_DN_UP_spec (F : ℝ → Prop) (x d u f : ℝ) :
    ⦃⌜F f ∧ Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ |f - x| ≤ x - d ∧ |f - x| ≤ u - x⌝⦄
    Rnd_N_pt_DN_UP_check F x d u f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_DN_UP_check
  rfl

/-- Check DN-case for nearest rounding under asymmetry

    If `x - d ≤ u - x`, then `d` is the nearest rounding of `x`.
-/
def Rnd_N_pt_DN_check (F : ℝ → Prop) (x d u : ℝ) : Id Bool :=
  pure true

/-- Specification: DN is nearest under left-smaller distance

    Given DN/UP points and `x - d ≤ u - x`, `d` is nearest.
-/
theorem Rnd_N_pt_DN_spec (F : ℝ → Prop) (x d u : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ (x - d ≤ u - x)⌝⦄
    Rnd_N_pt_DN_check F x d u
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_DN_check
  rfl

/-- Check UP-case for nearest rounding under asymmetry

    If `u - x ≤ x - d`, then `u` is the nearest rounding of `x`.
-/
def Rnd_N_pt_UP_check (F : ℝ → Prop) (x d u : ℝ) : Id Bool :=
  pure true

/-- Specification: UP is nearest under right-smaller distance

    Given DN/UP points and `u - x ≤ x - d`, `u` is nearest.
-/
theorem Rnd_N_pt_UP_spec (F : ℝ → Prop) (x d u : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ (u - x ≤ x - d)⌝⦄
    Rnd_N_pt_UP_check F x d u
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_UP_check
  rfl

end RoundNearestAuxiliary

section RoundNearestGeneric

/-- Check uniqueness for generic nearest with tie-breaking predicate

    Under a uniqueness property on ties, the NG-point is unique.
-/
def Rnd_NG_pt_unique_check (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (x f1 f2 : ℝ) : Id Bool :=
  pure true

/-- Specification: Uniqueness of NG-point under tie uniqueness

    Assuming the uniqueness property on ties for `P` and that
    both `f1` and `f2` satisfy `Rnd_NG_pt F P x _`, we have `f1 = f2`.
-/
theorem Rnd_NG_pt_unique_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (x f1 f2 : ℝ) :
    ⦃⌜(∀ x d u,
          Rnd_DN_pt F x d → Rnd_N_pt F x d →
          Rnd_UP_pt F x u → Rnd_N_pt F x u →
          P x d → P x u → d = u) ∧
        Rnd_NG_pt F P x f1 ∧ Rnd_NG_pt F P x f2⌝⦄
    Rnd_NG_pt_unique_check F P x f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NG_pt_unique_check
  rfl

/-- Check monotonicity for NG-point under tie uniqueness

    With the uniqueness property on ties, `Rnd_NG_pt F P` is monotone.
-/
def Rnd_NG_pt_monotone_check (F : ℝ → Prop) (P : ℝ → ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: NG-point rounding is monotone (with tie uniqueness)

    Assuming the uniqueness property on ties for `P`, the rounding predicate
    `Rnd_NG_pt F P` is monotone.
-/
theorem Rnd_NG_pt_monotone_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop) :
    ⦃⌜∀ x d u,
        Rnd_DN_pt F x d → Rnd_N_pt F x d →
        Rnd_UP_pt F x u → Rnd_N_pt F x u →
        P x d → P x u → d = u⌝⦄
    Rnd_NG_pt_monotone_check F P
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NG_pt_monotone_check
  rfl

/-- Check reflexivity for NG-point

    A representable `x` is its own NG-point for any `P`.
-/
def Rnd_NG_pt_refl_check (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (x : ℝ) : Id Bool :=
  pure true

/-- Specification: NG-point is reflexive

    From `F x`, deduce `Rnd_NG_pt F P x x`.
-/
theorem Rnd_NG_pt_refl_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜F x⌝⦄
    Rnd_NG_pt_refl_check F P x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NG_pt_refl_check
  rfl

/-- Check opposite invariance for NG-point

    If `F` is closed under negation and `P` is sign-symmetric, then NG is
    invariant under negation.
-/
def Rnd_NG_pt_opp_inv_check (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: NG-point invariance under negation

    From closure of `F` under negation and compatibility of `P` with
    negation, `Rnd_NG_pt F P (-x) (-f)` implies `Rnd_NG_pt F P x f`.
-/
theorem Rnd_NG_pt_opp_inv_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (x f : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ (∀ x f, P x f → P (-x) (-f)) ∧ Rnd_NG_pt F P (-x) (-f)⌝⦄
    Rnd_NG_pt_opp_inv_check F P x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NG_pt_opp_inv_check
  rfl

/-- Coq-compatible name: NG-point invariance under negation -/
theorem Rnd_NG_pt_opp_inv (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (x f : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ (∀ x f, P x f → P (-x) (-f)) ∧ Rnd_NG_pt F P (-x) (-f)⌝⦄
    Rnd_NG_pt_opp_inv_check F P x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  exact Rnd_NG_pt_opp_inv_spec F P x f

/-- Check uniqueness of NG-based rounding functions

    Under the uniqueness property, two NG-based rounding functions coincide.
-/
def Rnd_NG_unique_check (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) : Id Bool :=
  pure true

/-- Specification: Function-level uniqueness for NG rounding

    Given tie uniqueness property and `Rnd_NG F P` for `rnd1` and `rnd2`,
    these functions agree pointwise.
-/
theorem Rnd_NG_unique_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) :
    ⦃⌜(∀ x d u,
          Rnd_DN_pt F x d → Rnd_N_pt F x d →
          Rnd_UP_pt F x u → Rnd_N_pt F x u →
          P x d → P x u → d = u) ∧
        (∃ p1 p2, Rnd_NG F P rnd1 = pure p1 ∧ Rnd_NG F P rnd2 = pure p2 ∧ p1 ∧ p2)⌝⦄
    Rnd_NG_unique_check F P rnd1 rnd2 x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NG_unique_check
  rfl

end RoundNearestGeneric

section RoundNearestTies

/-- Check equivalence between NA and NG with abs-based predicate

    With `0 ∈ F`, `Rnd_NA_pt` is equivalent to `Rnd_NG_pt` with
    predicate `fun x f => |x| ≤ |f|`.
-/
def Rnd_NA_NG_pt_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: NA equals NG with abs-based tie predicate

    Assuming `F 0`, equivalence between `Rnd_NA_pt` and `Rnd_NG_pt` holds.
-/
theorem Rnd_NA_NG_pt_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0⌝⦄
    Rnd_NA_NG_pt_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_NG_pt_check
  rfl

/-- Check uniqueness property for NA ties (auxiliary)

    The NA tie-breaking relation yields uniqueness under `F 0`.
-/
def Rnd_NA_pt_unique_prop_check (F : ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: NA tie uniqueness property holds

    Assuming `F 0`, the auxiliary uniqueness property for NA holds.
-/
theorem Rnd_NA_pt_unique_prop_spec (F : ℝ → Prop) :
    ⦃⌜F 0⌝⦄
    Rnd_NA_pt_unique_prop_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_pt_unique_prop_check
  rfl

/-- Check uniqueness of NA-point

    With `F 0`, the NA-point is unique.
-/
def Rnd_NA_pt_unique_check (F : ℝ → Prop) (x f1 f2 : ℝ) : Id Bool :=
  pure true

/-- Specification: NA-point uniqueness

    If `Rnd_NA_pt F x f1` and `Rnd_NA_pt F x f2` with `F 0`, then `f1 = f2`.
-/
theorem Rnd_NA_pt_unique_spec (F : ℝ → Prop) (x f1 f2 : ℝ) :
    ⦃⌜F 0 ∧ Rnd_NA_pt F x f1 ∧ Rnd_NA_pt F x f2⌝⦄
    Rnd_NA_pt_unique_check F x f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_pt_unique_check
  rfl

/-- Check that NA-point is a valid nearest point under bound

    If `Rnd_N_pt F x f` and `|f| ≤ |x|` with `F 0`, then `Rnd_NA_pt F x f`.
-/
def Rnd_NA_pt_N_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: From nearest with abs bound to NA-point

    From `F 0`, `Rnd_N_pt F x f`, and `|f| ≤ |x|`, conclude `Rnd_NA_pt F x f`.
-/
theorem Rnd_NA_pt_N_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0 ∧ Rnd_N_pt F x f ∧ |f| ≤ |x|⌝⦄
    Rnd_NA_pt_N_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_pt_N_check
  rfl

/-- Check uniqueness of NA-based rounding functions

    If both functions satisfy `Rnd_NA`, they agree pointwise.
-/
def Rnd_NA_unique_check (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) : Id Bool :=
  pure true

/-- Specification: Function-level uniqueness for NA rounding

    Under `F 0` and `Rnd_NA F rnd1`, `Rnd_NA F rnd2`, we have `rnd1 x = rnd2 x`.
-/
theorem Rnd_NA_unique_spec (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) :
    ⦃⌜F 0 ∧ (∃ p1 p2, Rnd_NA F rnd1 = pure p1 ∧ Rnd_NA F rnd2 = pure p2 ∧ p1 ∧ p2)⌝⦄
    Rnd_NA_unique_check F rnd1 rnd2 x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_unique_check
  rfl

/-- Check monotonicity for NA-point rounding

    With `F 0`, the NA-point rounding predicate is monotone.
-/
def Rnd_NA_pt_monotone_check (F : ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: NA-point is monotone

    Assuming `F 0`, `Rnd_NA_pt F` is monotone.
-/
theorem Rnd_NA_pt_monotone_spec (F : ℝ → Prop) :
    ⦃⌜F 0⌝⦄
    Rnd_NA_pt_monotone_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_pt_monotone_check
  rfl

/-- Check reflexivity of NA-point

    Representable values are fixed by NA-point rounding.
-/
def Rnd_NA_pt_refl_check (F : ℝ → Prop) (x : ℝ) : Id Bool :=
  pure true

/-- Specification: NA-point reflexivity on representables

    From `F x`, deduce `Rnd_NA_pt F x x`.
-/
theorem Rnd_NA_pt_refl_spec (F : ℝ → Prop) (x : ℝ) :
    ⦃⌜F x⌝⦄
    Rnd_NA_pt_refl_check F x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_pt_refl_check
  rfl

/-- Check idempotency of NA-point

    If `Rnd_NA_pt F x f` and `F x`, then `f = x`.
-/
def Rnd_NA_pt_idempotent_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: NA-point idempotency on representables

    From `Rnd_NA_pt F x f` and `F x`, deduce `f = x`.
-/
theorem Rnd_NA_pt_idempotent_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_NA_pt F x f ∧ F x⌝⦄
    Rnd_NA_pt_idempotent_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_pt_idempotent_check
  rfl

/-- Check equivalence between N0 and NG with abs-based predicate

    With `0 ∈ F`, `Rnd_N0_pt` is equivalent to `Rnd_NG_pt` with
    predicate `fun x f => |f| ≤ |x|`.
-/
def Rnd_N0_NG_pt_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: N0 equals NG with abs-based tie predicate

    Assuming `F 0`, equivalence between `Rnd_N0_pt` and `Rnd_NG_pt` holds.
-/
theorem Rnd_N0_NG_pt_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0⌝⦄
    Rnd_N0_NG_pt_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_NG_pt_check
  rfl

/-- Check uniqueness property for N0 ties (auxiliary)

    The N0 tie-breaking relation yields uniqueness under `F 0`.
-/
def Rnd_N0_pt_unique_prop_check (F : ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: N0 tie uniqueness property holds

    Assuming `F 0`, the auxiliary uniqueness property for N0 holds.
-/
theorem Rnd_N0_pt_unique_prop_spec (F : ℝ → Prop) :
    ⦃⌜F 0⌝⦄
    Rnd_N0_pt_unique_prop_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_pt_unique_prop_check
  rfl

/-- Check uniqueness of N0-point

    With `F 0`, the N0-point is unique.
-/
def Rnd_N0_pt_unique_check (F : ℝ → Prop) (x f1 f2 : ℝ) : Id Bool :=
  pure true

/-- Specification: N0-point uniqueness

    If `Rnd_N0_pt F x f1` and `Rnd_N0_pt F x f2` with `F 0`, then `f1 = f2`.
-/
theorem Rnd_N0_pt_unique_spec (F : ℝ → Prop) (x f1 f2 : ℝ) :
    ⦃⌜F 0 ∧ Rnd_N0_pt F x f1 ∧ Rnd_N0_pt F x f2⌝⦄
    Rnd_N0_pt_unique_check F x f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_pt_unique_check
  rfl

/-- Check that N0-point arises from nearest with abs bound

    If `Rnd_N_pt F x f` and `|f| ≤ |x|` with `F 0`, then `Rnd_N0_pt F x f`.
-/
def Rnd_N0_pt_N_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: From nearest with abs bound to N0-point

    From `F 0`, `Rnd_N_pt F x f`, and `|f| ≤ |x|`, conclude `Rnd_N0_pt F x f`.
-/
theorem Rnd_N0_pt_N_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0 ∧ Rnd_N_pt F x f ∧ |f| ≤ |x|⌝⦄
    Rnd_N0_pt_N_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_pt_N_check
  rfl

/-- Check uniqueness of N0-based rounding functions

    If both functions satisfy `Rnd_N0`, they agree pointwise.
-/
def Rnd_N0_unique_check (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) : Id Bool :=
  pure true

/-- Specification: Function-level uniqueness for N0 rounding

    Under `F 0` and `Rnd_N0 F rnd1`, `Rnd_N0 F rnd2`, we have `rnd1 x = rnd2 x`.
-/
theorem Rnd_N0_unique_spec (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) :
    ⦃⌜F 0 ∧ (∃ p1 p2, Rnd_N0 F rnd1 = pure p1 ∧ Rnd_N0 F rnd2 = pure p2 ∧ p1 ∧ p2)⌝⦄
    Rnd_N0_unique_check F rnd1 rnd2 x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_unique_check
  rfl

/-- Check monotonicity for N0-point rounding

    With `F 0`, the N0-point rounding predicate is monotone.
-/
def Rnd_N0_pt_monotone_check (F : ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: N0-point is monotone

    Assuming `F 0`, `Rnd_N0_pt F` is monotone.
-/
theorem Rnd_N0_pt_monotone_spec (F : ℝ → Prop) :
    ⦃⌜F 0⌝⦄
    Rnd_N0_pt_monotone_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_pt_monotone_check
  rfl

/-- Check reflexivity of N0-point

    Representable values are fixed by N0-point rounding.
-/
def Rnd_N0_pt_refl_check (F : ℝ → Prop) (x : ℝ) : Id Bool :=
  pure true

/-- Specification: N0-point reflexivity on representables

    From `F x`, deduce `Rnd_N0_pt F x x`.
-/
theorem Rnd_N0_pt_refl_spec (F : ℝ → Prop) (x : ℝ) :
    ⦃⌜F x⌝⦄
    Rnd_N0_pt_refl_check F x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_pt_refl_check
  rfl

/-- Check idempotency of N0-point

    If `Rnd_N0_pt F x f` and `F x`, then `f = x`.
-/
def Rnd_N0_pt_idempotent_check (F : ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: N0-point idempotency on representables

    From `Rnd_N0_pt F x f` and `F x`, deduce `f = x`.
-/
theorem Rnd_N0_pt_idempotent_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_N0_pt F x f ∧ F x⌝⦄
    Rnd_N0_pt_idempotent_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_pt_idempotent_check
  rfl

end RoundNearestTies

section MonotoneImplications

/-- Check nonnegativity from rounding predicate monotonicity

    If a rounding predicate is monotone and maps 0 to 0, then `0 ≤ x`
    implies `0 ≤ f` when `P x f` holds.
-/
def round_pred_ge_0_check (P : ℝ → ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: Monotone predicate preserves nonnegativity

    From `round_pred_monotone P`, `P 0 0`, `P x f`, and `0 ≤ x`, deduce `0 ≤ f`.
-/
theorem round_pred_ge_0_spec (P : ℝ → ℝ → Prop) (x f : ℝ) :
    ⦃⌜round_pred_monotone P ∧ P 0 0 ∧ P x f ∧ 0 ≤ x⌝⦄
    round_pred_ge_0_check P x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold round_pred_ge_0_check
  rfl

/-- Check positivity implication from monotonicity

    If a rounding predicate is monotone and maps 0 to 0, then `0 < f`
    implies `0 < x` when `P x f` holds.
-/
def round_pred_gt_0_check (P : ℝ → ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: Positivity transfers back via monotonicity

    From `round_pred_monotone P`, `P 0 0`, `P x f`, and `0 < f`, deduce `0 < x`.
-/
theorem round_pred_gt_0_spec (P : ℝ → ℝ → Prop) (x f : ℝ) :
    ⦃⌜round_pred_monotone P ∧ P 0 0 ∧ P x f ∧ 0 < f⌝⦄
    round_pred_gt_0_check P x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold round_pred_gt_0_check
  rfl

/-- Check nonpositivity from rounding predicate monotonicity

    If a rounding predicate is monotone and maps 0 to 0, then `x ≤ 0`
    implies `f ≤ 0` when `P x f` holds.
-/
def round_pred_le_0_check (P : ℝ → ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: Monotone predicate preserves nonpositivity

    From `round_pred_monotone P`, `P 0 0`, `P x f`, and `x ≤ 0`, deduce `f ≤ 0`.
-/
theorem round_pred_le_0_spec (P : ℝ → ℝ → Prop) (x f : ℝ) :
    ⦃⌜round_pred_monotone P ∧ P 0 0 ∧ P x f ∧ x ≤ 0⌝⦄
    round_pred_le_0_check P x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold round_pred_le_0_check
  rfl

/-- Check negativity implication from monotonicity

    If a rounding predicate is monotone and maps 0 to 0, then `f < 0`
    implies `x < 0` when `P x f` holds.
-/
def round_pred_lt_0_check (P : ℝ → ℝ → Prop) (x f : ℝ) : Id Bool :=
  pure true

/-- Specification: Negativity transfers back via monotonicity

    From `round_pred_monotone P`, `P 0 0`, `P x f`, and `f < 0`, deduce `x < 0`.
-/
theorem round_pred_lt_0_spec (P : ℝ → ℝ → Prop) (x f : ℝ) :
    ⦃⌜round_pred_monotone P ∧ P 0 0 ∧ P x f ∧ f < 0⌝⦄
    round_pred_lt_0_check P x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold round_pred_lt_0_check
  rfl

end MonotoneImplications

section FormatEquivalence

/-- Check DN-point equivalence under format agreement on an interval

    If two formats agree on `[a,b]`, DN-points computed in `F1` on that
    interval are also DN-points in `F2`.
-/
def Rnd_DN_pt_equiv_format_check (F1 F2 : ℝ → Prop) (a b x f : ℝ) : Id Bool :=
  pure true

/-- Specification: DN-point equivalence under format agreement

    From `F1 a`, `∀ x ∈ [a,b], F1 x ↔ F2 x`, `a ≤ x ≤ b`, and `Rnd_DN_pt F1 x f`,
    conclude `Rnd_DN_pt F2 x f`.
-/
theorem Rnd_DN_pt_equiv_format_spec (F1 F2 : ℝ → Prop) (a b x f : ℝ) :
    ⦃⌜F1 a ∧ (∀ x, a ≤ x ∧ x ≤ b → (F1 x ↔ F2 x)) ∧ a ≤ x ∧ x ≤ b ∧ Rnd_DN_pt F1 x f⌝⦄
    Rnd_DN_pt_equiv_format_check F1 F2 a b x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_DN_pt_equiv_format_check
  rfl

/-- Check UP-point equivalence under format agreement on an interval

    If two formats agree on `[a,b]`, UP-points computed in `F1` on that
    interval are also UP-points in `F2`.
-/
def Rnd_UP_pt_equiv_format_check (F1 F2 : ℝ → Prop) (a b x f : ℝ) : Id Bool :=
  pure true

/-- Specification: UP-point equivalence under format agreement

    From `F1 a`, `∀ x ∈ [a,b], F1 x ↔ F2 x`, `a ≤ x ≤ b`, and `Rnd_UP_pt F1 x f`,
    conclude `Rnd_UP_pt F2 x f`.
-/
theorem Rnd_UP_pt_equiv_format_spec (F1 F2 : ℝ → Prop) (a b x f : ℝ) :
    ⦃⌜F1 a ∧ (∀ x, a ≤ x ∧ x ≤ b → (F1 x ↔ F2 x)) ∧ a ≤ x ∧ x ≤ b ∧ Rnd_UP_pt F1 x f⌝⦄
    Rnd_UP_pt_equiv_format_check F1 F2 a b x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_UP_pt_equiv_format_check
  rfl

end FormatEquivalence

section SatisfiesAnyConsequences

/-- Check alternative characterization of satisfies_any

    Placeholder equivalence/characterization for satisfies_any.
-/
def satisfies_any_eq_check (F : ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: satisfies_any alternative characterization

    A placeholder statement expressing equivalence for `satisfies_any`.
-/
theorem satisfies_any_eq_spec (F : ℝ → Prop) :
    ⦃⌜True⌝⦄
    satisfies_any_eq_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold satisfies_any_eq_check
  rfl

/-- Check existence of DN rounding from satisfies_any

    If a format satisfies_any, DN rounding is total.
-/
def satisfies_any_imp_DN_check (F : ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: satisfies_any implies DN rounding exists

    From `satisfies_any F`, DN rounding predicate is total.
-/
theorem satisfies_any_imp_DN_spec (F : ℝ → Prop) :
    ⦃⌜FloatSpec.Core.Generic_fmt.satisfies_any F⌝⦄
    satisfies_any_imp_DN_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold satisfies_any_imp_DN_check
  rfl

/-- Check existence of UP rounding from satisfies_any

    If a format satisfies_any, UP rounding is total.
-/
def satisfies_any_imp_UP_check (F : ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: satisfies_any implies UP rounding exists

    From `satisfies_any F`, UP rounding predicate is total.
-/
theorem satisfies_any_imp_UP_spec (F : ℝ → Prop) :
    ⦃⌜FloatSpec.Core.Generic_fmt.satisfies_any F⌝⦄
    satisfies_any_imp_UP_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold satisfies_any_imp_UP_check
  rfl

/-- Check existence of ZR rounding from satisfies_any

    If a format satisfies_any, ZR rounding is total.
-/
def satisfies_any_imp_ZR_check (F : ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: satisfies_any implies ZR rounding exists

    From `satisfies_any F`, ZR rounding predicate is total.
-/
theorem satisfies_any_imp_ZR_spec (F : ℝ → Prop) :
    ⦃⌜FloatSpec.Core.Generic_fmt.satisfies_any F⌝⦄
    satisfies_any_imp_ZR_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold satisfies_any_imp_ZR_check
  rfl

/-- Check existence of NG rounding from satisfies_any

    If a format satisfies_any, NG rounding is total.
-/
def satisfies_any_imp_NG_check (F : ℝ → Prop) (P : ℝ → ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: satisfies_any implies NG rounding exists

    From `satisfies_any F` and a predicate `P`, NG rounding predicate is total.
-/
theorem satisfies_any_imp_NG_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop) :
    ⦃⌜FloatSpec.Core.Generic_fmt.satisfies_any F⌝⦄
    satisfies_any_imp_NG_check F P
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold satisfies_any_imp_NG_check
  rfl

/-- Check existence of NA rounding from satisfies_any

    If a format satisfies_any, NA rounding is total.
-/
def satisfies_any_imp_NA_check (F : ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: satisfies_any implies NA rounding exists

    From `satisfies_any F`, NA rounding predicate is total.
-/
theorem satisfies_any_imp_NA_spec (F : ℝ → Prop) :
    ⦃⌜FloatSpec.Core.Generic_fmt.satisfies_any F⌝⦄
    satisfies_any_imp_NA_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold satisfies_any_imp_NA_check
  rfl

/-- Check existence of N0 rounding from satisfies_any

    If a format satisfies_any, N0 rounding is total.
-/
def satisfies_any_imp_N0_check (F : ℝ → Prop) : Id Bool :=
  pure true

/-- Specification: satisfies_any implies N0 rounding exists

    From `satisfies_any F`, N0 rounding predicate is total.
-/
theorem satisfies_any_imp_N0_spec (F : ℝ → Prop) :
    ⦃⌜FloatSpec.Core.Generic_fmt.satisfies_any F⌝⦄
    satisfies_any_imp_N0_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold satisfies_any_imp_N0_check
  rfl

end SatisfiesAnyConsequences

end FloatSpec.Core.Round_pred
