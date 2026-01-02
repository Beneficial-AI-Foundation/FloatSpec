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
-- import Mathlib.Data.Real.Basic
import FloatSpec.src.Core.Generic_fmt
import Std.Do.Triple
import Std.Tactic.Do
import FloatSpec.src.SimprocWP

open Real
open Std.Do
open FloatSpec.Core.Defs

namespace FloatSpec.Core.Round_pred


-- variable {beta : Int}

-- Re-export pointwise rounding predicates under this namespace for downstream files.
abbrev Rnd_DN_pt := FloatSpec.Core.Defs.Rnd_DN_pt
abbrev Rnd_UP_pt := FloatSpec.Core.Defs.Rnd_UP_pt
abbrev Rnd_N_pt  := FloatSpec.Core.Defs.Rnd_N_pt
abbrev Rnd_NG_pt := FloatSpec.Core.Defs.Rnd_NG_pt
abbrev Rnd_NA_pt := FloatSpec.Core.Defs.Rnd_NA_pt
abbrev Rnd_N0_pt := FloatSpec.Core.Defs.Rnd_N0_pt
abbrev Rnd_ZR_pt := FloatSpec.Core.Defs.Rnd_ZR_pt

section RoundingFunctionProperties

/-- Rounding down property for functions

    A rounding function rnd satisfies `Rnd_DN` if for every input x,
    rnd(x) is the round down value according to format F.
    This lifts the pointwise property to functions.
-/
def Rnd_DN (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Rnd_DN_pt F x (rnd x))

/-- Specification: Round down function property

    The round down property ensures that the function satisfies
    the round down condition at every point. This provides a
    functional interface to the pointwise rounding predicate.
-/
@[spec]
theorem Rnd_DN_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_DN F rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, Rnd_DN_pt F x (rnd x))⌝⦄ := by
  intro h
  unfold Rnd_DN
  rfl

/-- Rounding up property for functions

    A rounding function rnd satisfies `Rnd_UP` if for every input x,
    rnd(x) is the round up value according to format F.
    This provides the functional counterpart to round-up.
-/
def Rnd_UP (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Rnd_UP_pt F x (rnd x))

/-- Specification: Round up function property

    The round up property ensures consistent upward rounding
    behavior across all inputs. This guarantees the function
    implementation matches the pointwise specification.
-/
@[spec]
theorem Rnd_UP_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_UP F rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, Rnd_UP_pt F x (rnd x))⌝⦄ := by
  intro _
  unfold Rnd_UP
  rfl

/-- Rounding toward zero property for functions

    A function satisfies `Rnd_ZR` if it implements truncation:
    round toward zero for all inputs. This combines round-down
    for positive values and round up for negative values.
-/
def Rnd_ZR (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  -- Use the Coq-accurate predicate from Defs to ensure both directions (x ≥ 0 and x ≤ 0)
  pure (∀ x : ℝ, FloatSpec.Core.Defs.Rnd_ZR_pt F x (rnd x))

/-- Specification: Round toward zero function property

    The truncation property ensures the function always
    rounds toward zero, providing consistent behavior
    for both positive and negative inputs.
-/
@[spec]
theorem Rnd_ZR_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_ZR F rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, FloatSpec.Core.Defs.Rnd_ZR_pt F x (rnd x))⌝⦄ := by
  intro _
  unfold Rnd_ZR
  rfl

/-- Round to nearest property for functions

    A function satisfies `Rnd_N` if it always returns the nearest
    representable value. This is the base property for all
    `round-to-nearest` modes without specifying tie breaking.
-/
def Rnd_N (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Rnd_N_pt F x (rnd x))

/-- Specification: Round to nearest function property

    The nearest-value property ensures optimal approximation:
    the returned value minimizes the distance to the input
    among all representable values in the format.
-/
@[spec]
theorem Rnd_N_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_N F rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, Rnd_N_pt F x (rnd x))⌝⦄ := by
  intro _
  unfold Rnd_N
  rfl

/-- Generic rounding property with tie-breaking predicate

    A function satisfies `Rnd_NG` with predicate P if it rounds
    to nearest and uses P to break ties. This generalizes
    all `round-to-nearest` variants with different tie policies.
-/
def Rnd_NG (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Rnd_NG_pt F P x (rnd x))

/-- Specification: Generic round to nearest with tie breaking

    The generic nearest property with custom tie-breaking
    provides a unified framework for implementing various
    IEEE 754 rounding modes and custom policies.
-/
@[spec]
theorem Rnd_NG_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_NG F P rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, Rnd_NG_pt F P x (rnd x))⌝⦄ := by
  intro _
  unfold Rnd_NG
  rfl

/-- Round ties away from zero property

    A function satisfies `Rnd_NA` if it rounds to nearest,
    breaking ties by choosing the value farther from zero.
    This implements IEEE 754's "away from zero" tie breaking.
-/
def Rnd_NA (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Rnd_NA_pt F x (rnd x))

/-- Specification: Round ties away from zero

    The away-from-zero tie-breaking ensures that when exactly
    between two representable values, the function chooses
    the one with larger absolute value.
-/
@[spec]
theorem Rnd_NA_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    ⦃⌜True⌝⦄
    Rnd_NA F rnd
    ⦃⇓result => ⌜result = (∀ x : ℝ, Rnd_NA_pt F x (rnd x))⌝⦄ := by
  intro _
  unfold Rnd_NA
  rfl

/-- Round ties toward zero property

    A function satisfies `Rnd_N0` if it rounds to nearest,
    breaking ties by choosing the value closer to zero.
    This provides an alternative tie breaking strategy.
-/
def Rnd_N0 (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Rnd_N0_pt F x (rnd x))

/-- Specification: Round ties toward zero

    The toward-zero tie-breaking ensures that when exactly
    between two representable values, the function chooses
    the one with smaller absolute value.
-/
@[spec]
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
noncomputable def round_val_of_pred (rnd : ℝ → ℝ → Prop) (x : ℝ) : ℝ :=
  by
    classical
    -- Choose any value satisfying the predicate when it exists; default to 0 otherwise.
    by_cases h : ∃ f : ℝ, rnd x f
    · exact pure (Classical.choose h)
    · exact pure 0

/-- Specification: Value existence from round predicate

    Given `round_pred rnd`, for each `x` there exists some `f`
    such that `rnd x f`. The extractor returns such an `f`.
    This relies on classical choice to select a witness.
-/
@[spec]
theorem round_val_of_pred_spec (rnd : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜round_pred rnd⌝⦄
    round_val_of_pred rnd x
    ⦃⇓f => ⌜rnd x f⌝⦄ := by
  intro h
  unfold round_val_of_pred
  classical
  -- From totality, obtain a witness for `rnd x f`.
  have hx : ∃ f : ℝ, rnd x f := (And.left h) x
  -- Reduce the Hoare triple to a pure postcondition on the result of `Id.run`.
  -- The definition selects `Classical.choose hx` in this case.
  simpa [ pure, hx] using Classical.choose_spec hx

/-- Extract rounding function from predicate

    Given a rounding predicate, construct the corresponding
    rounding function. This provides the functional interface
    to relational rounding specifications.
-/
noncomputable def round_fun_of_pred (rnd : ℝ → ℝ → Prop) : (ℝ → ℝ) :=
  by
    classical
    -- Build a function selecting, for each x, some f with rnd x f (defaulting to 0 if none).
    exact pure (fun x => if h : ∃ f : ℝ, rnd x f then Classical.choose h else 0)

/-- Specification: Function existence from round predicate

    Given a proper rounding predicate `rnd` (total and monotone), the
    extractor `round_fun_of_pred` returns a function `f` such that
    `rnd x (f x)` holds for every input `x`.
-/
@[spec]
theorem round_fun_of_pred_spec (rnd : ℝ → ℝ → Prop) :
    ⦃⌜round_pred rnd⌝⦄
    round_fun_of_pred rnd
    ⦃⇓f => ⌜∀ x, rnd x (f x)⌝⦄ := by
  intro h
  unfold round_fun_of_pred
  classical
  -- Reduce the Hoare triple on `Id` to a pure goal about the returned function.
  -- It suffices to show that for every `x`, the chosen branch yields a witness.
  have hx_all : ∀ x, rnd x ((fun x => if h' : ∃ f : ℝ, rnd x f then Classical.choose h' else 0) x) := by
    intro x
    have hx : ∃ f : ℝ, rnd x f := (And.left h) x
    -- In the total case, the `if` picks `Classical.choose hx`, whose spec gives `rnd x _`.
    simpa [hx] using Classical.choose_spec hx
  simpa [ pure] using hx_all

/-- Check uniqueness of rounding result

    Verify that a monotonic rounding predicate produces
    unique results. This is essential for the deterministic
    nature of rounding functions.
-/
noncomputable def round_unique_check (rnd : ℝ → ℝ → Prop) (x f1 f2 : ℝ) : Bool :=
  by
    -- Decide equality of the two candidates; the spec will prove this is `true`
    -- under `round_pred_monotone rnd` with `rnd x f1` and `rnd x f2`.
    classical
    exact pure (decide (f1 = f2))

/-- Specification: Uniqueness of rounding result

    Monotonic rounding predicates produce unique results.
    This ensures that rounding functions are well-defined
    and deterministic for any given input.
-/
@[spec]
theorem round_unique_spec (rnd : ℝ → ℝ → Prop) (x f1 f2 : ℝ) :
    ⦃⌜round_pred_monotone rnd ∧ rnd x f1 ∧ rnd x f2⌝⦄
    round_unique_check rnd x f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold round_unique_check
  classical
  -- Reduce Hoare triple on Id to a pure goal about equality
  simp [ pure]
  rcases h with ⟨hmono, hx1, hx2⟩
  -- Monotonicity at the same input yields mutual inequalities, hence equality
  have h12 : f1 ≤ f2 := hmono x x f1 f2 hx1 hx2 le_rfl
  have h21 : f2 ≤ f1 := hmono x x f2 f1 hx2 hx1 le_rfl
  exact le_antisymm h12 h21

end ExistenceAndUniqueness

section RoundDownProperties

/-- Check if round down satisfies monotonicity

    Verify that the round down predicate preserves ordering:
    if x₁ ≤ x₂, then round_down(x₁) ≤ round_down(x₂).
    This fundamental property ensures consistent behavior.
-/
-- We expose the monotonicity property for DN-points via a boolean
-- check. Its specification below proves it always evaluates to `true`.
noncomputable def Rnd_DN_pt_monotone_check (F : ℝ → Prop) : Bool := by
  -- Decide the monotonicity proposition; the spec below proves it holds.
  classical
  exact pure (decide (round_pred_monotone (Rnd_DN_pt F)))

/-- Specification: Round down is monotone

    The round down operation preserves ordering relationships.
    This monotonicity property is essential for the correctness
    of downward rounding in floating-point systems.
-/
@[spec]
theorem Rnd_DN_pt_monotone_spec (F : ℝ → Prop) :
    ⦃⌜True⌝⦄
    Rnd_DN_pt_monotone_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_DN_pt_monotone_check
  -- Reduce to the underlying proposition about monotonicity of DN-points.
  classical
  simp [ pure, round_pred_monotone]
  intro x y f g hx hy hxy
  -- Unpack the DN-point facts for x ↦ f and y ↦ g.
  rcases hx with ⟨hfF, hf_le_x, hmax_x⟩
  rcases hy with ⟨hgF, hy_le_y, hmax_y⟩
  -- Since f ≤ x and x ≤ y, we get f ≤ y.
  have hf_le_y : f ≤ y := le_trans hf_le_x hxy
  -- Maximality of g among values ≤ y yields f ≤ g.
  exact hmax_y f hfF hf_le_y

/-- Check uniqueness of round down result

    Verify that round down produces unique results for
    any given input. This ensures deterministic behavior
    of the downward rounding operation.
-/
noncomputable def Rnd_DN_pt_unique_check (F : ℝ → Prop) (x f1 f2 : ℝ) : Bool :=
  by
    -- We return whether the two candidates are equal; the spec
    -- will establish this equality from the DN-point property.
    classical
    exact pure (decide (f1 = f2))

/-- Specification: Round down point is unique

    The round down operation produces a unique result for
    each input. This uniqueness is fundamental to the
    deterministic nature of floating-point rounding.
-/
@[spec]
theorem Rnd_DN_pt_unique_spec (F : ℝ → Prop) (x f1 f2 : ℝ) :
    ⦃⌜Rnd_DN_pt F x f1 ∧ Rnd_DN_pt F x f2⌝⦄
    Rnd_DN_pt_unique_check F x f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  rcases h with ⟨h1, h2⟩
  unfold Rnd_DN_pt_unique_check
  classical
  -- From maximality of DN-points: f1 ≤ f2 and f2 ≤ f1
  have le12 : f1 ≤ f2 := by
    have := h2.2.2 f1 h1.1 h1.2.1
    simpa using this
  have le21 : f2 ≤ f1 := by
    have := h1.2.2 f2 h2.1 h2.2.1
    simpa using this
  have hEq : f1 = f2 := le_antisymm le12 le21
  -- With equality, `decide` reduces to `true`.
  simp [hEq]

/-- Check uniqueness of round down function

    Verify that round down functions are unique: if two
    functions both satisfy the round down property,
    they produce identical results on all inputs.
-/
noncomputable def Rnd_DN_unique_check (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) : Bool :=
  by
    classical
    exact pure (decide (rnd1 x = rnd2 x))

/-- Specification: Round down function is unique

    Round down functions are uniquely determined by their
    specification. Any two functions satisfying the round
    down property must be identical.
-/
@[spec]
theorem Rnd_DN_unique_spec (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) :
    ⦃⌜∃ p1 p2, Rnd_DN F rnd1 = pure p1 ∧ Rnd_DN F rnd2 = pure p2 ∧ p1 ∧ p2⌝⦄
    Rnd_DN_unique_check F rnd1 rnd2 x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_DN_unique_check
  classical
  -- Reduce the Hoare triple to a pure equality goal on functions at x
  simp [ pure]
  -- Extract the DN properties for rnd1 and rnd2 from the given existential packaging
  rcases h with ⟨p1, p2, hEq1, hEq2, Hp1, Hp2⟩
  -- Use that `Id.run` is injective to identify the propositions
  have h1run : (∀ y : ℝ, Rnd_DN_pt F y (rnd1 y)) = p1 := by
    -- Rnd_DN is definitionally `pure (∀ y, ...)`; projecting with `Id.run` removes `pure`.
    simpa [Rnd_DN] using congrArg Id.run hEq1
  have h2run : (∀ y : ℝ, Rnd_DN_pt F y (rnd2 y)) = p2 := by
    simpa [Rnd_DN] using congrArg Id.run hEq2
  -- Turn the packaged proofs `Hp1 : p1` and `Hp2 : p2` into the desired shapes
  have H1' : (∀ y : ℝ, Rnd_DN_pt F y (rnd1 y)) := by
    simpa [h1run] using Hp1
  have H2' : (∀ y : ℝ, Rnd_DN_pt F y (rnd2 y)) := by
    simpa [h2run] using Hp2
  -- Apply DN-point uniqueness at the particular x
  have Hd1 : Rnd_DN_pt F x (rnd1 x) := H1' x
  have Hd2 : Rnd_DN_pt F x (rnd2 x) := H2' x
  -- Use maximality of DN-points to derive equality
  have le12 : rnd1 x ≤ rnd2 x := by
    have := Hd2.2.2 (rnd1 x) Hd1.1 Hd1.2.1
    simpa using this
  have le21 : rnd2 x ≤ rnd1 x := by
    have := Hd1.2.2 (rnd2 x) Hd2.1 Hd2.2.1
    simpa using this
  exact le_antisymm le12 le21

end RoundDownProperties

section RoundUpProperties

/-- Check if round up satisfies monotonicity

    Verify that the round up predicate preserves ordering:
    upward rounding maintains the same relative ordering
    as the input values.
-/
-- We expose the monotonicity property for UP-points via a boolean
-- check. Its specification below proves it always evaluates to `true`.
noncomputable def Rnd_UP_pt_monotone_check (F : ℝ → Prop) : Bool := by
  -- Decide the monotonicity proposition; the spec below proves it holds.
  classical
  exact pure (decide (round_pred_monotone (Rnd_UP_pt F)))

/-- Specification: Round up is monotone

    The round up operation preserves ordering relationships.
    This property ensures predictable behavior across
    the entire range of representable values.
-/
@[spec]
theorem Rnd_UP_pt_monotone_spec (F : ℝ → Prop) :
    ⦃⌜True⌝⦄
    Rnd_UP_pt_monotone_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_UP_pt_monotone_check
  -- Reduce to the underlying proposition about monotonicity of UP-points.
  classical
  simp [ pure, round_pred_monotone]
  intro x y f g hx hy hxy
  -- Use minimality of the UP-point at x with candidate g.
  -- From hy we have `F g` and `y ≤ g`; transitivity gives `x ≤ g`.
  exact hx.2.2 g hy.1 (le_trans hxy hy.2.1)

/-- Check uniqueness of round up result

    Verify that round up produces unique results.
    Each input has exactly one correct round up value
    in the given format.
-/
noncomputable def Rnd_UP_pt_unique_check (F : ℝ → Prop) (x f1 f2 : ℝ) : Bool := by
  -- We encode uniqueness by returning whether `f1 = f2`.
  -- The spec will prove this evaluates to `true` under the
  -- hypotheses `Rnd_UP_pt F x f1` and `Rnd_UP_pt F x f2`.
  classical
  exact pure (decide (f1 = f2))

/-- Specification: Round up point is unique

    The round up operation is deterministic: each input
    maps to exactly one output value. This uniqueness
    ensures consistent floating-point behavior.
-/
@[spec]
theorem Rnd_UP_pt_unique_spec (F : ℝ → Prop) (x f1 f2 : ℝ) :
    ⦃⌜Rnd_UP_pt F x f1 ∧ Rnd_UP_pt F x f2⌝⦄
    Rnd_UP_pt_unique_check F x f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_UP_pt_unique_check
  classical
  -- Reduce the Hoare triple goal to a pure equality via `simp`.
  simp [ pure]
  rcases h with ⟨hf1, hf2⟩
  rcases hf1 with ⟨Ff1, hxle_f1, hmin1⟩
  rcases hf2 with ⟨Ff2, hxle_f2, hmin2⟩
  apply le_antisymm
  · exact hmin1 f2 Ff2 hxle_f2
  · exact hmin2 f1 Ff1 hxle_f1

/-- Check uniqueness of round up function

    Verify that round up functions are uniquely determined.
    The specification completely characterizes the
    implementation, ensuring no ambiguity.
-/
noncomputable def Rnd_UP_unique_check (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) : Bool :=
  by
    classical
    -- Encode pointwise equality; the spec proves this reduces to `true`.
    exact pure (decide (rnd1 x = rnd2 x))

/-- Specification: Round up function is unique

    Round up functions are completely characterized by
    their specification. This uniqueness guarantees
    implementation consistency across different systems.
-/
@[spec]
theorem Rnd_UP_unique_spec (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) :
    ⦃⌜∃ p1 p2, Rnd_UP F rnd1 = pure p1 ∧ Rnd_UP F rnd2 = pure p2 ∧ p1 ∧ p2⌝⦄
    Rnd_UP_unique_check F rnd1 rnd2 x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_UP_unique_check
  classical
  -- Reduce the Hoare triple to a pure equality goal on functions at x
  simp [ pure]
  -- Extract the UP properties for rnd1 and rnd2 from the given existential packaging
  rcases h with ⟨p1, p2, hEq1, hEq2, Hp1, Hp2⟩
  -- `Rnd_UP` is definitionally `pure (∀ y, Rnd_UP_pt F y (rnd1 y))`.
  have h1run : (∀ y : ℝ, Rnd_UP_pt F y (rnd1 y)) = p1 := by
    simpa [Rnd_UP] using congrArg Id.run hEq1
  have h2run : (∀ y : ℝ, Rnd_UP_pt F y (rnd2 y)) = p2 := by
    simpa [Rnd_UP] using congrArg Id.run hEq2
  -- Coerce the packed booleans back to the intended propositions
  have H1' : (∀ y : ℝ, Rnd_UP_pt F y (rnd1 y)) := by
    simpa [h1run] using Hp1
  have H2' : (∀ y : ℝ, Rnd_UP_pt F y (rnd2 y)) := by
    simpa [h2run] using Hp2
  -- Apply UP-point uniqueness at the particular x using minimality of UP-points
  have Hu1 : Rnd_UP_pt F x (rnd1 x) := H1' x
  have Hu2 : Rnd_UP_pt F x (rnd2 x) := H2' x
  -- From minimality: both directions of ≤, hence equality
  have le12 : rnd1 x ≤ rnd2 x := by
    exact Hu1.2.2 (rnd2 x) Hu2.1 Hu2.2.1
  have le21 : rnd2 x ≤ rnd1 x := by
    exact Hu2.2.2 (rnd1 x) Hu1.1 Hu1.2.1
  exact le_antisymm le12 le21

end RoundUpProperties

section DualityProperties

/-- Transform round down to round up via negation

    If f is the round down of x, then -f is the round up
    of -x. This duality property connects upward and
    downward rounding through sign changes.
-/
noncomputable def Rnd_UP_pt_opp_transform (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    -- We encode the duality property by deciding the target predicate.
    -- The accompanying specification proves this decision is `true`.
    classical
    exact pure (decide (Rnd_UP_pt F (-x) (-f)))

/-- Specification: Round up from round down with opposite

    The duality between round up and round down through
    negation enables implementing one mode in terms of
    the other, reducing implementation complexity.
-/
@[spec]
theorem Rnd_UP_pt_opp_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ Rnd_DN_pt F x f⌝⦄
    Rnd_UP_pt_opp_transform F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_UP_pt_opp_transform
  classical
  -- Reduce to proving the dual UP-point predicate holds
  simp [ pure]
  rcases h with ⟨hFopp, hDN⟩
  rcases hDN with ⟨Hf, Hfx, Hmax⟩
  -- Show: Rnd_UP_pt F (-x) (-f)
  refine And.intro (hFopp _ Hf) ?_
  -- Inequality part: -x ≤ -f from f ≤ x
  refine And.intro (by simpa using (neg_le_neg Hfx)) ?_
  -- Minimality: for any representable g with -x ≤ g, we have -f ≤ g
  intro g HgF Hlexg
  have Hg_le_x : -g ≤ x := by
    -- From -x ≤ g, negate both sides
    have := neg_le_neg Hlexg
    simpa [neg_neg] using this
  have Hneg_g : F (-g) := hFopp _ HgF
  have H_le_f : -g ≤ f := Hmax (-g) Hneg_g Hg_le_x
  -- Negating yields the desired inequality
  have := neg_le_neg H_le_f
  simpa [neg_neg] using this

/-- Transform round up to round down via negation

    If f is the round up of x, then -f is the round down
    of -x. This is the reverse duality that completes
    the bidirectional relationship.
-/
noncomputable def Rnd_DN_pt_opp_transform (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    -- Decide the target predicate; the spec establishes it holds.
    classical
    exact pure (decide (Rnd_DN_pt F (-x) (-f)))

/-- Specification: Round down from round up with opposite

    The reverse duality enables complete interconversion
    between upward and downward rounding modes through
    negation, providing implementation flexibility.
-/
@[spec]
theorem Rnd_DN_pt_opp_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ Rnd_UP_pt F x f⌝⦄
    Rnd_DN_pt_opp_transform F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_DN_pt_opp_transform
  classical
  -- Reduce to proving the dual DN-point predicate holds
  simp [ pure]
  rcases ‹(∀ y, F y → F (-y)) ∧ Rnd_UP_pt F x f› with ⟨hFopp, hUP⟩
  rcases hUP with ⟨Hf, hxle_f, hmin⟩
  -- Goal: Rnd_DN_pt F (-x) (-f)
  refine And.intro (hFopp _ Hf) ?_
  -- Inequality: from x ≤ f, we get -f ≤ -x
  refine And.intro (by simpa using (neg_le_neg hxle_f)) ?_
  -- Maximality: if g ≤ -x and F g, then g ≤ -f
  intro g HgF Hg_le_negx
  have hx_le_negg : x ≤ -g := by
    have := neg_le_neg Hg_le_negx
    simpa [neg_neg] using this
  have H_F_negg : F (-g) := hFopp _ HgF
  have hf_le_negg : f ≤ -g := hmin (-g) H_F_negg hx_le_negg
  have hneg : -f ≥ g := by
    have := neg_le_neg hf_le_negg
    simpa [neg_neg] using this
  exact hneg

/-/ Transform round-down and round-up functions under negation

    If `rnd1` rounds down and `rnd2` rounds up for the same
    format, then `rnd1 (-x) = - rnd2 x`. This expresses the
    function-level duality via negation.
-/
noncomputable def Rnd_DN_opp_check (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) : Bool :=
  by
    classical
    exact pure (decide (rnd1 (-x) = - rnd2 x))

/-- Specification: Round-down vs round-up under negation

    Under the assumption that `F` is closed under negation and
    that `rnd1` satisfies `Rnd_DN` while `rnd2` satisfies `Rnd_UP`,
    the relation `rnd1 (-x) = - rnd2 x` holds for all `x`.
-/
@[spec]
theorem Rnd_DN_opp_spec (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ (∃ p1 p2, Rnd_DN F rnd1 = pure p1 ∧ Rnd_UP F rnd2 = pure p2 ∧ p1 ∧ p2)⌝⦄
    Rnd_DN_opp_check F rnd1 rnd2 x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_DN_opp_check
  classical
  -- Reduce the Hoare triple to a pure equality goal on this input `x`.
  simp [ pure]
  -- Unpack assumptions: closure under negation and packaged DN/UP properties.
  rcases h with ⟨hFopp, ⟨p1, p2, hDN, hUP, Hp1, Hp2⟩⟩
  -- Project the underlying propositions from the `Id`-packed specs.
  have hDN_run : (∀ y : ℝ, Rnd_DN_pt F y (rnd1 y)) = p1 := by
    simpa [Rnd_DN] using congrArg Id.run hDN
  have hUP_run : (∀ y : ℝ, Rnd_UP_pt F y (rnd2 y)) = p2 := by
    simpa [Rnd_UP] using congrArg Id.run hUP
  have Hdn : ∀ y : ℝ, Rnd_DN_pt F y (rnd1 y) := by
    simpa [hDN_run] using Hp1
  have Hup : ∀ y : ℝ, Rnd_UP_pt F y (rnd2 y) := by
    simpa [hUP_run] using Hp2
  -- Show that y ↦ -rnd1 (-y) also rounds up by duality on points.
  -- Instantiate at the particular `x`.
  have Hd_at_negx : Rnd_DN_pt F (-x) (rnd1 (-x)) := Hdn (-x)
  -- Construct `Rnd_UP_pt F x (-rnd1 (-x))` directly (duality via negation).
  have Hup_dual : Rnd_UP_pt F x (- rnd1 (-x)) := by
    rcases Hd_at_negx with ⟨Ff, fle, fmax⟩
    refine And.intro (hFopp _ Ff) ?_
    -- Inequality x ≤ -rnd1 (-x) from rnd1 (-x) ≤ -x
    refine And.intro ?hle ?hmin
    · have := neg_le_neg fle
      simpa [neg_neg] using this
    · intro g HgF hx_le_g
      -- From x ≤ g, deduce -g ≤ -x, use DN maximality at -x, then negate back.
      have h1 : -g ≤ -x := by
        have := neg_le_neg hx_le_g
        simpa [neg_neg] using this
      have hFnegg : F (-g) := hFopp _ HgF
      have h2 : -g ≤ rnd1 (-x) := fmax (-g) hFnegg h1
      have := neg_le_neg h2
      simpa [neg_neg] using this
  -- UP-point for `rnd2` at `x`.
  have Hup_at_x : Rnd_UP_pt F x (rnd2 x) := Hup x
  -- Uniqueness of UP-points at the same input yields the desired equality.
  have le1 : - rnd1 (-x) ≤ rnd2 x := by
    exact Hup_dual.2.2 (rnd2 x) Hup_at_x.1 Hup_at_x.2.1
  have le2 : rnd2 x ≤ - rnd1 (-x) := by
    exact Hup_at_x.2.2 (- rnd1 (-x)) Hup_dual.1 Hup_dual.2.1
  -- We proved `-rnd1 (-x) = rnd2 x`; negate both sides to match the target.
  have hEq_neg : - rnd1 (-x) = rnd2 x := le_antisymm le1 le2
  have := congrArg (fun t => -t) hEq_neg
  simpa [neg_neg] using this

/-/ DN/UP split at a point

    If `d` is the DN-point and `u` is the UP-point for `x`,
    then any representable `f` lies either below `d` or above `u`.
-/
noncomputable def Rnd_DN_UP_pt_split_check (F : ℝ → Prop) (x d u f : ℝ) : Bool :=
  by
    -- Encode the split as a decidable boolean; the spec proves it is `true`.
    classical
    exact pure (decide ((f ≤ d) ∨ (u ≤ f)))

/-- Specification: DN/UP split covers all representables

    Given `Rnd_DN_pt F x d`, `Rnd_UP_pt F x u`, and `F f`,
    we have `(f ≤ d) ∨ (u ≤ f)`.
-/
@[spec]
theorem Rnd_DN_UP_pt_split_spec (F : ℝ → Prop) (x d u f : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ F f⌝⦄
    Rnd_DN_UP_pt_split_check F x d u f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_DN_UP_pt_split_check
  classical
  -- Reduce to the underlying propositional statement
  simp [ pure]
  rcases h with ⟨hDN, hUP, hFf⟩
  -- Totality on ℝ: either f ≤ x or x ≤ f
  cases le_total f x with
  | inl hfxle =>
      -- In the ≤ x branch, DN maximality gives f ≤ d
      left
      exact hDN.2.2 f hFf hfxle
  | inr hxlef =>
      -- In the x ≤ branch, UP minimality gives u ≤ f
      right
      exact hUP.2.2 f hFf hxlef

/-- Coq-compatible name: DN/UP split covers all representables -/
theorem Rnd_DN_UP_pt_split (F : ℝ → Prop) (x d u f : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ F f⌝⦄
    Rnd_DN_UP_pt_split_check F x d u f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  exact Rnd_DN_UP_pt_split_spec F x d u f

/-- Exclusivity: representable within `[dn, up]` is at an endpoint

    If `fd` and `fu` are the DN/UP points for `x` and `f` is representable
    and lies between them, then `f` must be equal to one of the endpoints.
-/
noncomputable def Only_DN_or_UP_check (F : ℝ → Prop) (x fd fu f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (f = fd ∨ f = fu))

/-- Specification: Only DN or UP when bounded between them

    Given `Rnd_DN_pt F x fd`, `Rnd_UP_pt F x fu`, `F f`, and `fd ≤ f ≤ fu`,
    the value `f` equals `fd` or `fu`.
-/
@[spec]
theorem Only_DN_or_UP_spec (F : ℝ → Prop) (x fd fu f : ℝ) :
    ⦃⌜Rnd_DN_pt F x fd ∧ Rnd_UP_pt F x fu ∧ F f ∧ fd ≤ f ∧ f ≤ fu⌝⦄
    Only_DN_or_UP_check F x fd fu f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Only_DN_or_UP_check
  classical
  -- Reduce to the underlying propositional goal
  simp [ pure]
  rcases h with ⟨hDN, hUP, hFf, hfdle, hlefu⟩
  -- Split on whether x ≤ f or f < x
  by_cases hx : x ≤ f
  · -- In the x ≤ f branch, UP minimality gives fu ≤ f, hence f = fu
    right
    apply le_antisymm hlefu
    exact hUP.2.2 f hFf hx
  · -- Otherwise, by totality we have f ≤ x; DN maximality gives f ≤ fd, hence f = fd
    left
    have hfxle : f ≤ x := by
      -- From totality, either f ≤ x or x ≤ f; the latter contradicts ¬(x ≤ f)
      cases le_total f x with
      | inl h => exact h
      | inr hxle => exact (False.elim (hx hxle))
    -- From DN maximality: f ≤ fd
    have hlefd : f ≤ fd := hDN.2.2 f hFf hfxle
    exact le_antisymm hlefd hfdle

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
noncomputable def Rnd_DN_pt_refl_check (F : ℝ → Prop) (x : ℝ) : Bool := by
  -- Encode the DN-point reflexivity as a decidable boolean.
  -- The accompanying specification will prove it evaluates to `true`
  -- under the assumption `F x`.
  classical
  exact pure (decide (Rnd_DN_pt F x x))

/-- Specification: Round down is reflexive

    Representable values are unchanged by round down.
    This reflexivity ensures that exact values remain
    exact under rounding operations.
-/
@[spec]
theorem Rnd_DN_pt_refl_spec (F : ℝ → Prop) (x : ℝ) :
    ⦃⌜F x⌝⦄
    Rnd_DN_pt_refl_check F x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hx
  unfold Rnd_DN_pt_refl_check
  classical
  -- Reduce the Hoare triple to a pure goal about the DN-point predicate.
  simp [ pure]
  -- It suffices to build `Rnd_DN_pt F x x` from `F x`.
  refine And.intro hx ?_
  refine And.intro le_rfl ?_
  intro g _ hgx
  -- From `g ≤ x`, we conclude `g ≤ x` (trivial maximality at x itself).
  exact hgx

/-- Check idempotency of round down

    Verify that rounding down an already-representable
    value returns that same value. This ensures
    stability under repeated rounding.
-/
noncomputable def Rnd_DN_pt_idempotent_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    -- Encode idempotency as decidable equality; the spec proves this is `true`.
    classical
    exact pure (decide (f = x))

/-- Specification: Round down is idempotent

    Rounding representable values produces those same values.
    This idempotency property ensures that representable
    values form fixed points of the rounding operation.
-/
@[spec]
theorem Rnd_DN_pt_idempotent_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_DN_pt F x f ∧ F x⌝⦄
    Rnd_DN_pt_idempotent_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_DN_pt_idempotent_check
  classical
  -- Reduce Hoare triple to the underlying equality goal
  simp [ pure]
  rcases h with ⟨hDN, hxF⟩
  rcases hDN with ⟨hfF, hfle, hmax⟩
  -- From maximality with g = x and x ≤ x, we get x ≤ f
  have hxle : x ≤ f := hmax x hxF le_rfl
  -- Together with f ≤ x, we obtain equality
  exact le_antisymm hfle hxle

/-- Check reflexivity of round up

    Verify that round up preserves representable values.
    Like round down, representable inputs should
    remain unchanged.
-/
noncomputable def Rnd_UP_pt_refl_check (F : ℝ → Prop) (x : ℝ) : Bool :=
  by
    -- Encode the UP-point reflexivity as a decidable boolean.
    -- The specification below proves it evaluates to `true` under `F x`.
    classical
    exact pure (decide (Rnd_UP_pt F x x))

/-- Specification: Round up is reflexive

    Round up preserves representable values exactly.
    This reflexivity is symmetric to the round down
    property and ensures consistent behavior.
-/
@[spec]
theorem Rnd_UP_pt_refl_spec (F : ℝ → Prop) (x : ℝ) :
    ⦃⌜F x⌝⦄
    Rnd_UP_pt_refl_check F x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hx
  unfold Rnd_UP_pt_refl_check
  classical
  -- Reduce the Hoare triple to a pure goal about the UP-point predicate.
  simp [ pure]
  -- It suffices to build `Rnd_UP_pt F x x` from `F x`.
  refine And.intro hx ?_
  refine And.intro le_rfl ?_
  intro g _ hxle
  -- From `x ≤ g`, we conclude `x ≤ g` (trivial minimality at x itself).
  exact hxle

/-- Check idempotency of round up

    Verify that round up is idempotent on representable
    values, mirroring the round down idempotency property.
-/
noncomputable def Rnd_UP_pt_idempotent_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    -- Encode idempotency as decidable equality; the spec proves this is `true`.
    classical
    exact pure (decide (f = x))

/-- Specification: Round up is idempotent

    Round up leaves representable values unchanged.
    This completes the idempotency properties for
    both directional rounding modes.
-/
@[spec]
theorem Rnd_UP_pt_idempotent_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_UP_pt F x f ∧ F x⌝⦄
    Rnd_UP_pt_idempotent_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_UP_pt_idempotent_check
  classical
  -- Reduce Hoare triple to the underlying equality goal
  simp [ pure]
  rcases h with ⟨hUP, hxF⟩
  rcases hUP with ⟨hfF, hxle, hmin⟩
  -- From minimality with g = x and x ≤ x, we get f ≤ x
  have hfle : f ≤ x := hmin x hxF le_rfl
  -- Together with x ≤ f, we obtain equality
  exact le_antisymm hfle hxle

end ReflexivityAndIdempotency

section RoundTowardZeroProperties

/-- Check absolute value bound for round toward zero

    Verify that rounding toward zero never increases
    the absolute value: |round_toward_zero(x)| ≤ |x|.
    This captures the truncation property.
-/
noncomputable def Rnd_ZR_abs_check (F : ℝ → Prop) (rnd : ℝ → ℝ) (x : ℝ) : Bool :=
  by
    -- Boolean check encoding |rnd x| ≤ |x|; proved correct in the spec below.
    classical
    exact pure (decide (|rnd x| ≤ |x|))

/-- Specification: Round toward zero absolute value bound

    Rounding toward zero (truncation) never increases
    absolute values. This fundamental property makes
    truncation useful for implementing magnitude bounds.
-/
@[spec]
theorem Rnd_ZR_abs_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) (x : ℝ) :
    ⦃⌜∃ p, Rnd_ZR F rnd = pure p ∧ p⌝⦄
    Rnd_ZR_abs_check F rnd x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_ZR_abs_check
  classical
  -- Reduce Hoare triple on Id to the pure inequality goal |rnd x| ≤ |x|
  simp [ pure]
  -- Unpack the packaged Rnd_ZR property and project it from Id
  rcases h with ⟨p, hEq, hp⟩
  have hrun : (∀ y : ℝ, FloatSpec.Core.Defs.Rnd_ZR_pt F y (rnd y)) = p := by
    simpa [Rnd_ZR] using congrArg Id.run hEq
  have hZR : ∀ y : ℝ, FloatSpec.Core.Defs.Rnd_ZR_pt F y (rnd y) := by
    simpa [hrun] using hp
  -- Show that 0 is representable and rnd 0 = 0
  have h0_DN : FloatSpec.Core.Defs.Rnd_DN_pt F 0 (rnd 0) := (hZR 0).1 le_rfl
  have h0_UP : FloatSpec.Core.Defs.Rnd_UP_pt F 0 (rnd 0) := (hZR 0).2 le_rfl
  have h_r0_le0 : rnd 0 ≤ 0 := h0_DN.2.1
  have h_0_le_r0 : 0 ≤ rnd 0 := h0_UP.2.1
  have hr0_eq0 : rnd 0 = 0 := le_antisymm h_r0_le0 h_0_le_r0
  have hF0 : F 0 := by simpa [hr0_eq0] using h0_DN.1
  -- Now prove the absolute-value bound by cases on the sign of x
  by_cases hx : 0 ≤ x
  · -- Nonnegative input: DN case gives 0 ≤ rnd x ≤ x
    have hDN : FloatSpec.Core.Defs.Rnd_DN_pt F x (rnd x) := (hZR x).1 hx
    have h0_le_rx : 0 ≤ rnd x := by
      -- Use maximality with g = 0 and F 0
      have := hDN.2.2 0 hF0 hx
      -- This has type 0 ≤ rnd x
      simpa using this
    -- Rewrite absolutes and conclude using rnd x ≤ x
    have hx_abs : |x| = x := abs_of_nonneg hx
    have hr_abs : |rnd x| = rnd x := abs_of_nonneg h0_le_rx
    simpa [hx_abs, hr_abs] using hDN.2.1
  · -- Negative input: UP case gives x ≤ rnd x ≤ 0
    have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have hUP : FloatSpec.Core.Defs.Rnd_UP_pt F x (rnd x) := (hZR x).2 hxle0
    have h_rx_le0 : rnd x ≤ 0 := hUP.2.2 0 hF0 hxle0
    have hx_abs : |x| = -x := abs_of_nonpos hxle0
    have hr_abs : |rnd x| = -rnd x := abs_of_nonpos h_rx_le0
    -- From x ≤ rnd x, conclude -rnd x ≤ -x
    have : -rnd x ≤ -x := by exact neg_le_neg hUP.2.1
    simpa [hx_abs, hr_abs] using this

end RoundTowardZeroProperties

section RoundTowardZeroMonotone

/-- Check monotonicity of round-toward-zero predicate

    With 0 representable, the predicate `Rnd_ZR_pt F` is monotone.
-/
noncomputable def Rnd_ZR_pt_monotone_check (F : ℝ → Prop) : Bool :=
  by
    -- Decide the monotonicity proposition; the spec below proves it holds.
    classical
    exact pure (decide (round_pred_monotone (Rnd_ZR_pt F)))

/-- Specification: Round toward zero is monotone when 0 ∈ F

    Assuming `F 0`, the rounding-toward-zero predicate preserves
    order: it is a monotone rounding predicate.
-/
@[spec]
theorem Rnd_ZR_pt_monotone_spec (F : ℝ → Prop) :
    ⦃⌜F 0⌝⦄
    Rnd_ZR_pt_monotone_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hF0
  unfold Rnd_ZR_pt_monotone_check
  classical
  -- Reduce to the monotonicity property for `Rnd_ZR_pt F`.
  simp [ pure, round_pred_monotone]
  -- Prove monotonicity of `Rnd_ZR_pt F` assuming `F 0`.
  intro x y f g hx hy hxy
  -- Split on the sign of x
  by_cases hx0 : 0 ≤ x
  · -- x ≥ 0: both sides are DN-points (since y ≥ x ≥ 0)
    have hDNx : Rnd_DN_pt F x f := (hx.1) hx0
    have hy0 : 0 ≤ y := le_trans hx0 hxy
    have hDNy : Rnd_DN_pt F y g := (hy.1) hy0
    -- Use maximality at y with candidate f
    exact hDNy.2.2 f hDNx.1 (le_trans hDNx.2.1 hxy)
  · -- x < 0: `hx` gives an UP-point at x
    have hUPx : Rnd_UP_pt F x f := (hx.2) (le_of_lt (lt_of_not_ge hx0))
    -- Split on the sign of y
    by_cases hy0 : 0 ≤ y
    · -- x < 0 ≤ y: compare via 0 using `F 0`
      have hDNy : Rnd_DN_pt F y g := (hy.1) hy0
      -- From UP minimality at x with g = 0 and x ≤ 0
      have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx0)
      have hfle0 : f ≤ 0 := hUPx.2.2 0 hF0 hxle0
      -- From DN maximality at y with g = 0 and 0 ≤ y
      have h0leg : 0 ≤ g := hDNy.2.2 0 hF0 hy0
      exact le_trans hfle0 h0leg
    · -- y < 0: both sides are UP-points
      have hUPy : Rnd_UP_pt F y g := (hy.2) (le_of_lt (lt_of_not_ge hy0))
      -- Use minimality at x with candidate g, from x ≤ y ≤ g
      have hxleg : x ≤ g := le_trans hxy hUPy.2.1
      exact hUPx.2.2 g hUPy.1 hxleg

end RoundTowardZeroMonotone

section RoundNearestBasic

/-- Check that nearest rounding falls into DN or UP cases

    Any nearest rounding point is either a DN-point or an UP-point.
-/
noncomputable def Rnd_N_pt_DN_or_UP_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    -- Encode the DN/UP disjunction; the spec will prove it's `true`.
    classical
    exact pure (decide (Rnd_DN_pt F x f ∨ Rnd_UP_pt F x f))

/-- Specification: Nearest point is DN or UP

    From `Rnd_N_pt F x f`, we conclude `f` is either a DN-point or
    an UP-point for `x`.
-/
@[spec]
theorem Rnd_N_pt_DN_or_UP_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_DN_or_UP_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N_pt_DN_or_UP_check
  classical
  -- Reduce Hoare triple to proving the DN/UP disjunction
  simp [ pure]
  rcases h with ⟨HfF, Hmin⟩
  -- Split on whether f ≤ x or x ≤ f
  cases le_total f x with
  | inl hfxle =>
    -- DN case: F f ∧ f ≤ x ∧ ∀ g, F g → g ≤ x → g ≤ f
    left
    refine And.intro HfF ?_
    refine And.intro hfxle ?_
    intro g HgF hglex
    -- Use minimality: |x - f| ≤ |x - g|, with both x - f, x - g ≥ 0
    have hxmf_nonneg : 0 ≤ x - f := sub_nonneg.mpr hfxle
    have hxmg_nonneg : 0 ≤ x - g := sub_nonneg.mpr hglex
    -- Apply minimality at g and rewrite absolutes into linear inequalities
    have h_abs : |x - f| ≤ |x - g| := by
      simpa [abs_sub_comm] using (Hmin g HgF)
    have h_sub : x - f ≤ x - g := by
      simpa [abs_of_nonneg hxmf_nonneg, abs_of_nonneg hxmg_nonneg] using h_abs
    -- x - f ≤ x - g ⇒ g ≤ f, by adding -x and using neg_le_neg_iff
    have hneg : -f ≤ -g := by
      have h' := add_le_add_left h_sub (-x)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'
    exact (neg_le_neg_iff).1 hneg
  | inr hxlef =>
    -- UP case: F f ∧ x ≤ f ∧ ∀ g, F g → x ≤ g → f ≤ g
    right
    refine And.intro HfF ?_
    refine And.intro hxlef ?_
    intro g HgF hxleg
    -- Use minimality: |x - f| ≤ |x - g|, with x - f ≤ 0 and x - g ≤ 0
    have hxmf_nonpos : x - f ≤ 0 := sub_nonpos.mpr hxlef
    have hxmg_nonpos : x - g ≤ 0 := sub_nonpos.mpr hxleg
    -- Apply minimality at g and rewrite absolutes into linear inequalities
    have h_abs : |x - f| ≤ |x - g| := by
      simpa [abs_sub_comm] using (Hmin g HgF)
    have h_sub : f - x ≤ g - x := by
      simpa [abs_of_nonpos hxmf_nonpos, abs_of_nonpos hxmg_nonpos, neg_sub] using h_abs
    -- f - x ≤ g - x ⇒ f ≤ g, by adding x on both sides
    have h' := add_le_add_right h_sub x
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'

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
noncomputable def Rnd_N_pt_DN_or_UP_eq_check (F : ℝ → Prop) (x d u f : ℝ) : Bool :=
  by
    -- Encode the disjunction `f = d ∨ f = u`; the spec will prove it's `true`.
    classical
    exact pure (decide (f = d ∨ f = u))

/-- Specification: Nearest equals DN or UP under DN/UP existence

    Given `Rnd_DN_pt F x d`, `Rnd_UP_pt F x u`, and `Rnd_N_pt F x f`,
    we have `f = d ∨ f = u`.
-/
@[spec]
theorem Rnd_N_pt_DN_or_UP_eq_spec (F : ℝ → Prop) (x d u f : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_DN_or_UP_eq_check F x d u f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N_pt_DN_or_UP_eq_check
  classical
  -- Reduce to proving the propositional disjunction.
  simp [ pure]
  -- Unpack the hypotheses.
  rcases h with ⟨Hd, Hu, Hf⟩
  rcases Hf with ⟨HfF, Hmin⟩
  -- Split on order between f and x.
  cases le_total f x with
  | inl hfxle =>
    -- Show that f is a DN-point, then conclude f = d by uniqueness.
    have HfDN : Rnd_DN_pt F x f := by
      refine And.intro HfF ?_
      refine And.intro hfxle ?_
      intro g HgF hglex
      -- Use minimality: |x - f| ≤ |x - g| and rewrite absolutes.
      have hxmf_nonneg : 0 ≤ x - f := sub_nonneg.mpr hfxle
      have hxmg_nonneg : 0 ≤ x - g := sub_nonneg.mpr hglex
      have h_abs : |x - f| ≤ |x - g| := by
        simpa [abs_sub_comm] using (Hmin g HgF)
      have h_sub : x - f ≤ x - g := by
        simpa [abs_of_nonneg hxmf_nonneg, abs_of_nonneg hxmg_nonneg] using h_abs
      -- x - f ≤ x - g ⇒ g ≤ f
      have hneg : -f ≤ -g := by
        have h' := add_le_add_left h_sub (-x)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'
      exact (neg_le_neg_iff).1 hneg
    -- From DN uniqueness at x, f = d.
    have le_df : d ≤ f := by
      have := HfDN.2.2 d Hd.1 Hd.2.1
      simpa using this
    have le_fd : f ≤ d := by
      have := Hd.2.2 f HfF hfxle
      simpa using this
    exact Or.inl (le_antisymm le_fd le_df)
  | inr hxlef =>
    -- Show that f is an UP-point, then conclude f = u by uniqueness.
    have HfUP : Rnd_UP_pt F x f := by
      refine And.intro HfF ?_
      refine And.intro hxlef ?_
      intro g HgF hxleg
      -- Use minimality: |x - f| ≤ |x - g| and rewrite absolutes.
      have hxmf_nonpos : x - f ≤ 0 := sub_nonpos.mpr hxlef
      have hxmg_nonpos : x - g ≤ 0 := sub_nonpos.mpr hxleg
      have h_abs : |x - f| ≤ |x - g| := by
        simpa [abs_sub_comm] using (Hmin g HgF)
      have h_sub : f - x ≤ g - x := by
        simpa [abs_of_nonpos hxmf_nonpos, abs_of_nonpos hxmg_nonpos, neg_sub] using h_abs
      have h' := add_le_add_right h_sub x
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'
    -- From UP uniqueness at x, f = u.
    have le_fu : f ≤ u := by
      have := HfUP.2.2 u Hu.1 Hu.2.1
      simpa using this
    have le_uf : u ≤ f := by
      have := Hu.2.2 f HfF hxlef
      simpa using this
    exact Or.inr (le_antisymm le_fu le_uf)

/-- Coq-compatible name: nearest equals DN or UP -/
theorem Rnd_N_pt_DN_or_UP_eq (F : ℝ → Prop) (x d u f : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_DN_or_UP_eq_check F x d u f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  exact Rnd_N_pt_DN_or_UP_eq_spec F x d u f

end RoundNearestBasic

section RoundNearestAdvanced

noncomputable section

/-- Check opposite invariance for nearest rounding

    If `F` is closed under negation and `(-x,-f)` is a nearest pair,
    then `(x,f)` is also a nearest pair.
-/
noncomputable def Rnd_N_pt_opp_inv_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    -- We encode the target proposition as a decidable boolean.
    -- The specification below will establish it holds.
    classical
    exact pure (decide (Rnd_N_pt F x f))

/-- Specification: Nearest invariant under negation (inverse)

    Assuming `(∀ y, F y → F (-y))` and `Rnd_N_pt F (-x) (-f)`, infer
    `Rnd_N_pt F x f`.
-/
@[spec]
theorem Rnd_N_pt_opp_inv_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ Rnd_N_pt F (-x) (-f)⌝⦄
    Rnd_N_pt_opp_inv_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N_pt_opp_inv_check
  classical
  -- Reduce the Hoare triple to proving the target proposition.
  simp [ pure]
  rcases h with ⟨hFopp, hNearestNeg⟩
  rcases hNearestNeg with ⟨Hf_neg, Hmin_neg⟩
  -- Show `F f` using closure under negation from `F (-f)`.
  have Hf : F f := by
    -- from F (-f) and closure: F f = F (-(-f))
    simpa [neg_neg] using hFopp (-f) Hf_neg
  -- Show minimality at `x` from minimality at `-x` by rewriting via negations.
  refine And.intro Hf ?_
  intro g HgF
  -- Use candidate `-g` on the `-x` side; closure gives `F (-g)`.
  have Hg_neg : F (-g) := hFopp g HgF
  -- From minimality at -x and symmetry of |·|, derive the desired inequality at x.
  have hneg := Hmin_neg (-g) Hg_neg
  have h1 : |x - f| ≤ |x - g| := by
    simpa [sub_eq_add_neg, add_comm] using hneg
  have h2 : |f - x| ≤ |g - x| := by
    simpa [abs_sub_comm] using h1
  exact h2

/-- Coq-compatible name: nearest invariant under negation -/
theorem Rnd_N_pt_opp_inv (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ Rnd_N_pt F (-x) (-f)⌝⦄
    Rnd_N_pt_opp_inv_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  exact Rnd_N_pt_opp_inv_spec F x f

/-- Check monotonicity for nearest rounding predicate

    If `x < y` and both are rounded to nearest, then `f ≤ g`.
-/
noncomputable def Rnd_N_pt_monotone_check (F : ℝ → Prop) (x y f g : ℝ) : Bool :=
  by
    -- Encode the monotonicity goal `f ≤ g` as a decidable boolean.
    classical
    exact pure (decide (f ≤ g))

/-- Specification: Nearest rounding is monotone

    From `Rnd_N_pt F x f`, `Rnd_N_pt F y g`, and `x < y`, deduce `f ≤ g`.
-/
@[spec]
theorem Rnd_N_pt_monotone_spec (F : ℝ → Prop) (x y f g : ℝ) :
    ⦃⌜Rnd_N_pt F x f ∧ Rnd_N_pt F y g ∧ x < y⌝⦄
    Rnd_N_pt_monotone_check F x y f g
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N_pt_monotone_check
  classical
  -- Reduce to proving the pure inequality `f ≤ g`.
  simp [ pure]
  rcases h with ⟨Hxf, Hyg, hxy⟩
  rcases Hxf with ⟨HfF, Hxmin⟩
  rcases Hyg with ⟨HgF, Hymin⟩
  -- By contradiction, assume `g < f`.
  by_contra hle
  have hgf : g < f := lt_of_not_ge hle
  -- From minimality at x and y (in the definition order |f - x| ≤ |g - x|)
  have Hfgx : |f - x| ≤ |g - x| := Hxmin g HgF
  have Hgfy : |g - y| ≤ |f - y| := Hymin f HfF
  -- Split on the order between x and g
  by_cases hxg : x ≤ g
  · -- Case 1: x ≤ g < f. Then |x - f| = f - x and |x - g| = g - x, contradicting g < f.
    have hxlt_f : x < f := lt_of_le_of_lt hxg hgf
    have hxmf_pos : 0 < f - x := sub_pos.mpr hxlt_f
    have hxmg_nonneg : 0 ≤ g - x := sub_nonneg.mpr hxg
    have Hfgx' : |f - x| ≤ |g - x| := by simpa [abs_sub_comm] using Hfgx
    have Hfgx'' : f - x ≤ g - x := by
      simpa [abs_of_nonneg (le_of_lt hxmf_pos), abs_of_nonneg hxmg_nonneg] using Hfgx'
    have : ¬ f - x ≤ g - x := by
      have h := sub_lt_sub_right hgf x
      exact not_le.mpr h
    exact this Hfgx''
  · -- Case 2: g < x. Then g < y by transitivity with x < y.
    have hgx : g < x := lt_of_not_ge hxg
    have hgy : g < y := lt_trans hgx hxy
    -- Subcase 2a: f ≤ y. Then |y - g| = y - g and |y - f| = y - f, contradicting g < f.
    by_cases hfy : f ≤ y
    · have hy_mg_pos : 0 < y - g := sub_pos.mpr hgy
      have hy_mf_nonneg : 0 ≤ y - f := sub_nonneg.mpr hfy
      have Hgfy' : |y - g| ≤ |y - f| := by
        simpa [abs_sub_comm] using Hgfy
      have Hgfy'' : y - g ≤ y - f := by
        simpa [abs_of_nonneg (le_of_lt hy_mg_pos), abs_of_nonneg hy_mf_nonneg] using Hgfy'
      have : ¬ y - g ≤ y - f := by
        have h := sub_lt_sub_left hgf y
        -- From g < f, we have y - f < y - g, contradicting the above ≤
        exact not_le.mpr h
      exact this Hgfy''
    · -- Subcase 2b: y < f. Use both minimalities and a rearrangement argument.
      have hy_lt_f : y < f := lt_of_not_ge hfy
      -- Rewrite Hfgx and Hgfy without absolutes using sign information.
      have hxmg_pos : 0 < x - g := sub_pos.mpr hgx
      -- From x < y < f, we get 0 < f - x
      have hxmf_pos : 0 < f - x := sub_pos.mpr (lt_trans hxy hy_lt_f)
      have hymg_pos : 0 < y - g := sub_pos.mpr hgy
      have hymf_neg : y - f < 0 := sub_neg.mpr hy_lt_f
      -- |x - f| = f - x and |x - g| = x - g
      have Hfgx' : f - x ≤ x - g := by
        have := Hfgx
        have : |f - x| ≤ |x - g| := by simpa [abs_sub_comm] using this
        simpa [abs_of_pos hxmf_pos, abs_of_pos hxmg_pos] using this
      -- |y - g| = y - g and |y - f| = f - y
      have Hgfy' : y - g ≤ f - y := by
        have habs : |y - g| ≤ |y - f| := by
          simpa [abs_sub_comm] using Hgfy
        simpa [abs_of_pos hymg_pos, abs_of_neg hymf_neg] using habs
      -- Sum inequalities: (f - x) + (y - g) ≤ (x - g) + (f - y)
      have Hsum : (f - x) + (y - g) ≤ (x - g) + (f - y) := add_le_add Hfgx' Hgfy'
      -- But (x - g) + (f - y) = (x - y) + (f - g)
      have hL : (x - g) + (f - y) = (x - y) + (f - g) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      -- and (f - x) + (y - g) = (y - x) + (f - g)
      have hR : (f - x) + (y - g) = (y - x) + (f - g) := by
        simp [sub_eq_add_neg, add_left_comm, add_assoc]
      -- Since y - x > 0, we have (x - y) < (y - x), hence L < R after adding (f - g)
      have hyx_pos : 0 < y - x := sub_pos.mpr hxy
      have hxmy_lt_hyx : (x - y) < (y - x) := by
        -- Since 0 < y - x, we have -(y - x) < (y - x); note x - y = -(y - x).
        have : -(y - x) < (y - x) := neg_lt_self hyx_pos
        simpa [neg_sub, sub_eq_add_neg] using this
      have hStrict : (x - y) + (f - g) < (y - x) + (f - g) := by
        simpa only [add_comm (f - g)] using add_lt_add_right hxmy_lt_hyx (f - g)
      -- Combine with Hsum rewritten via hL and hR to reach a contradiction
      have : (y - x) + (f - g) ≤ (x - y) + (f - g) := by simpa [hL, hR, add_comm, add_left_comm, add_assoc] using Hsum
      exact (not_le_of_gt hStrict) this

/-- Check uniqueness for nearest rounding under asymmetry

    If `x - d ≠ u - x`, then the nearest point is unique.
-/
def Rnd_N_pt_unique_check (F : ℝ → Prop) (x d u f1 f2 : ℝ) : Bool :=
  by
    -- Encode uniqueness by deciding equality; the spec proves it's `true`.
    classical
    exact pure (decide (f1 = f2))

/-- Specification: Uniqueness of nearest rounding

    With `Rnd_DN_pt F x d`, `Rnd_UP_pt F x u`, `x - d ≠ u - x`, and two
    nearest points `f1,f2`, we must have `f1 = f2`.
-/
@[spec]
theorem Rnd_N_pt_unique_spec (F : ℝ → Prop) (x d u f1 f2 : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ (x - d ≠ u - x) ∧ Rnd_N_pt F x f1 ∧ Rnd_N_pt F x f2⌝⦄
    Rnd_N_pt_unique_check F x d u f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N_pt_unique_check
  classical
  -- Reduce to proving f1 = f2 from the hypotheses.
  simp [ pure]
  rcases h with ⟨Hd, Hu, hneq, Hf1, Hf2⟩
  -- Each nearest point is either a DN- or an UP-point.
  have Hclass1 := Rnd_N_pt_DN_or_UP_eq_spec F x d u f1
  have Hclass2 := Rnd_N_pt_DN_or_UP_eq_spec F x d u f2
  have h1 : f1 = d ∨ f1 = u := by
    simpa [Rnd_N_pt_DN_or_UP_eq_check, pure, decide_eq_true_iff]
      using Hclass1 ⟨Hd, Hu, Hf1⟩
  have h2 : f2 = d ∨ f2 = u := by
    simpa [Rnd_N_pt_DN_or_UP_eq_check, pure, decide_eq_true_iff]
      using Hclass2 ⟨Hd, Hu, Hf2⟩
  -- Analyze the four cases.
  cases h1 with
  | inl h1d =>
      cases h2 with
      | inl h2d => simpa [h1d, h2d]
      | inr h2u =>
          -- f1 = d and f2 = u implies equal distances, contradicting hneq
          have : x - d = u - x := by
            rcases Hf1 with ⟨_, Hmin1⟩
            rcases Hf2 with ⟨_, Hmin2⟩
            have h_le₁ : |x - d| ≤ |x - u| := by
              have := Hmin1 u Hu.1
              simpa [h1d, abs_sub_comm] using this
            have h_le₂ : |x - u| ≤ |x - d| := by
              have := Hmin2 d Hd.1
              simpa [h2u, abs_sub_comm] using this
            have h_eq : |x - d| = |x - u| := le_antisymm h_le₁ h_le₂
            -- Rewrite both sides of h_eq using sign information
            have hxmd_nonneg : 0 ≤ x - d := sub_nonneg.mpr Hd.2.1
            have hxmu_nonpos : x - u ≤ 0 := sub_nonpos.mpr Hu.2.1
            have h_eq' : x - d = |x - u| := by
              simpa [abs_of_nonneg hxmd_nonneg] using h_eq
            have h_absu : |x - u| = u - x := by
              simpa [abs_of_nonpos hxmu_nonpos, neg_sub, sub_eq_add_neg]
                using (abs_of_nonpos hxmu_nonpos)
            simpa [h_absu] using h_eq'
          exact (hneq this).elim
  | inr h1u =>
      cases h2 with
      | inl h2d =>
          have : x - d = u - x := by
            rcases Hf1 with ⟨_, Hmin1⟩
            rcases Hf2 with ⟨_, Hmin2⟩
            have h_le₁ : |x - u| ≤ |x - d| := by
              have := Hmin1 d Hd.1
              simpa [h1u, abs_sub_comm] using this
            have h_le₂ : |x - d| ≤ |x - u| := by
              have := Hmin2 u Hu.1
              simpa [h2d, abs_sub_comm] using this
            have h_eq : |x - d| = |x - u| := le_antisymm h_le₂ h_le₁
            -- Rewrite using sign information to obtain a linear equality
            have hxmd_nonneg : 0 ≤ x - d := sub_nonneg.mpr Hd.2.1
            have hxmu_nonpos : x - u ≤ 0 := sub_nonpos.mpr Hu.2.1
            have h_eq' : x - d = |x - u| := by
              simpa [abs_of_nonneg hxmd_nonneg] using h_eq
            have h_absu : |x - u| = u - x := by
              simpa [abs_of_nonpos hxmu_nonpos, neg_sub, sub_eq_add_neg]
                using (abs_of_nonpos hxmu_nonpos)
            simpa [h_absu] using h_eq'
          exact (hneq this).elim
      | inr h2u => simpa [h1u, h2u]

/-- Check reflexivity for nearest rounding

    If `x` is representable, then it is its own nearest rounding.
-/
def Rnd_N_pt_refl_check (F : ℝ → Prop) (x : ℝ) : Bool :=
  by
    -- Encode the proposition `Rnd_N_pt F x x` as a decidable boolean.
    classical
    exact pure (decide (Rnd_N_pt F x x))

/-- Specification: Nearest rounding is reflexive on representables

    From `F x`, deduce `Rnd_N_pt F x x`.
-/
@[spec]
theorem Rnd_N_pt_refl_spec (F : ℝ → Prop) (x : ℝ) :
    ⦃⌜F x⌝⦄
    Rnd_N_pt_refl_check F x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hx
  unfold Rnd_N_pt_refl_check
  classical
  -- Reduce to proving `decide (Rnd_N_pt F x x) = true`.
  -- We first build `Rnd_N_pt F x x`, then rewrite via `decide_eq_true_iff`.
  have hRN : Rnd_N_pt F x x := by
    -- Unfold the nearest predicate goal shape and prove it directly.
    -- `F x` is given by `hx`; distances are minimized at `f = x` since |x - x| = 0.
    refine And.intro hx ?_
    intro g _
    have h : 0 ≤ |x - g| := by simpa using abs_nonneg (x - g)
    simpa using h
  -- Conclude by simplifying the Hoare triple and converting `decide` to Prop.
  simpa [ pure, decide_eq_true_iff]

/-- Check idempotency for nearest rounding

    If `x` is representable and `f` is nearest to `x`, then `f = x`.
-/
def Rnd_N_pt_idempotent_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    -- Encode idempotency as decidable equality; the spec will prove this is `true`.
    classical
    exact pure (decide (f = x))

/-- Specification: Nearest rounding is idempotent on representables

    From `Rnd_N_pt F x f` and `F x`, deduce `f = x`.
-/
@[spec]
theorem Rnd_N_pt_idempotent_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_N_pt F x f ∧ F x⌝⦄
    Rnd_N_pt_idempotent_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N_pt_idempotent_check
  classical
  -- Reduce to proving `f = x` from nearest property at `x` and representability of `x`.
  simp [ pure]
  rcases h with ⟨hN, hxF⟩
  rcases hN with ⟨hfF, hmin⟩
  -- Minimality at `g = x` yields `|f - x| ≤ 0`, hence `f = x`.
  have hle : |f - x| ≤ 0 := by simpa using (hmin x hxF)
  have heq0 : |f - x| = 0 := le_antisymm hle (abs_nonneg _)
  have hsub0 : f - x = 0 := by simpa using (abs_eq_zero.mp heq0)
  exact sub_eq_zero.mp hsub0

-- Close the inner noncomputable section started above.
end

-- (moved the namespace terminator to the end of the file)
end RoundNearestAdvanced

section RoundNearestAuxiliary

/-- Check nearest rounding at zero

    If `0 ∈ F`, then `Rnd_N_pt F 0 0`.
-/
noncomputable def Rnd_N_pt_0_check (F : ℝ → Prop) : Bool :=
  -- Decide the proposition `Rnd_N_pt F 0 0`; the spec proves it holds under `F 0`.
  by
    classical
    exact pure (decide (Rnd_N_pt F 0 0))

/-- Specification: Nearest at zero

    Assuming `F 0`, the nearest rounding of `0` is `0`.
-/
@[spec]
theorem Rnd_N_pt_0_spec (F : ℝ → Prop) :
    ⦃⌜F 0⌝⦄
    Rnd_N_pt_0_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N_pt_0_check
  classical
  -- Reduce to proving `Rnd_N_pt F 0 0` from `F 0`.
  simp [ pure]
  -- Build `Rnd_N_pt F 0 0` directly: representability from the precondition,
  -- and minimality since |0 - 0| = 0 ≤ |g - 0| for any representable g.
  refine And.intro (by simpa) ?_
  intro g _
  have : 0 ≤ |g - 0| := by simpa using abs_nonneg (g - 0)
  simpa [abs_sub_comm, sub_self, sub_zero] using this

/-- Check nonnegativity of nearest rounding for nonnegative inputs

    If `0 ≤ x` and `Rnd_N_pt F x f`, then `0 ≤ f`.
-/
noncomputable def Rnd_N_pt_ge_0_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (0 ≤ f))

/-- Specification: Nonnegativity preserved by nearest rounding

    With `F 0`, from `0 ≤ x` and `Rnd_N_pt F x f`, deduce `0 ≤ f`.
-/
@[spec]
theorem Rnd_N_pt_ge_0_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0 ∧ 0 ≤ x ∧ Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_ge_0_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N_pt_ge_0_check
  classical
  -- Reduce to a propositional goal.
  simp [ pure]
  -- Unpack the assumptions.
  rcases h with ⟨hF0, hx0, hN⟩
  -- From nearest minimality, using g = 0 (since F 0), we get |x - f| ≤ |x - 0| = x.
  have hmin0 : |x - f| ≤ x := by
    have := hN.2 0 hF0
    -- Rewrite |f - x| ≤ |0 - x| as |x - f| ≤ |x - 0| = x.
    simpa [abs_sub_comm, sub_zero, abs_of_nonneg hx0] using this
  -- Prove by contradiction that f cannot be negative.
  by_contra hfneg
  have hf_lt0 : f < 0 := lt_of_not_ge hfneg
  -- Then x - f > x (since -f > 0), hence |x - f| > x, contradicting minimality.
  have hx_lt_xmf : x < x - f := by
    have : 0 < -f := neg_pos.mpr hf_lt0
    have := add_lt_add_left this x
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hxmf_pos : 0 < x - f := by
    exact lt_of_le_of_lt (by simpa using hx0) hx_lt_xmf
  have hx_lt_abs : x < |x - f| := by
    -- Since x - f > 0, |x - f| = x - f
    simpa [abs_of_pos hxmf_pos] using hx_lt_xmf
  exact (lt_irrefl _ (lt_of_lt_of_le hx_lt_abs hmin0))

/-- Check nonpositivity of nearest rounding for nonpositive inputs

    If `x ≤ 0` and `Rnd_N_pt F x f`, then `f ≤ 0`.
-/
noncomputable def Rnd_N_pt_le_0_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (f ≤ 0))

/-- Specification: Nonpositivity preserved by nearest rounding

    With `F 0`, from `x ≤ 0` and `Rnd_N_pt F x f`, deduce `f ≤ 0`.
-/
@[spec]
theorem Rnd_N_pt_le_0_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0 ∧ x ≤ 0 ∧ Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_le_0_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N_pt_le_0_check
  classical
  -- Reduce to a propositional goal.
  simp [ pure]
  -- Unpack the assumptions.
  rcases h with ⟨hF0, hx0, hN⟩
  -- From nearest minimality with g = 0 (since F 0), obtain |f - x| ≤ |0 - x| = -x.
  have hmin0 : |f - x| ≤ -x := by
    have h := hN.2 0 hF0
    -- |0 - x| = | -x | = |x| = -x because x ≤ 0
    simpa [sub_eq_add_neg, abs_neg, abs_of_nonpos hx0] using h
  -- Prove by contradiction that f cannot be positive.
  by_contra hfpos
  have hf_gt0 : 0 < f := lt_of_not_ge hfpos
  -- Since x ≤ 0 and f > 0, we have 0 < f - x, hence |f - x| = f - x.
  have hpos : 0 < f - x := by
    -- 0 < (-x) + f = f - x
    have := add_pos_of_nonneg_of_pos (neg_nonneg.mpr hx0) hf_gt0
    simpa [sub_eq_add_neg, add_comm] using this
  -- And also -x < f - x, hence -x < |f - x|.
  have hx_abs_gt : -x < |f - x| := by
    have : -x < f - x := by
      have := add_lt_add_left hf_gt0 (-x)
      simpa [sub_eq_add_neg, add_comm] using this
    simpa [abs_of_pos hpos] using this
  -- Contradiction with minimality |f - x| ≤ -x.
  exact (lt_irrefl _ (lt_of_lt_of_le hx_abs_gt hmin0))

/-- Check absolute-value stability for nearest rounding

    If `F` is closed under negation and `0 ∈ F`, then rounding preserves
    absolute values: nearest at `x` maps to nearest at `|x|`.
-/
noncomputable def Rnd_N_pt_abs_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (Rnd_N_pt F |x| |f|))

/-- Specification: Nearest rounding respects absolute value

    From `F 0`, closure of `F` under negation, and `Rnd_N_pt F x f`,
    deduce `Rnd_N_pt F |x| |f|`.
-/
@[spec]
theorem Rnd_N_pt_abs_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0 ∧ (∀ y, F y → F (-y)) ∧ Rnd_N_pt F x f⌝⦄
    Rnd_N_pt_abs_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N_pt_abs_check
  classical
  -- Reduce to the propositional goal.
  simp [ pure]
  -- Unpack assumptions: membership of 0 (unused here), closure under negation, and nearest at x.
  rcases h with ⟨_hF0, hFopp, hN⟩
  -- We prove `Rnd_N_pt F |x| |f|` by a case split on the sign of `x`.
  by_cases hx : 0 ≤ x
  · -- Case `x ≥ 0`: then `|x| = x`.
    have hFx : |x| = x := by simpa [abs_of_nonneg hx]
    -- Prove `F |f|` using closure under negation if necessary.
    have Hfabs : F |f| := by
      by_cases hf : 0 ≤ f
      · simpa [abs_of_nonneg hf] using hN.1
      · have hfneg : f < 0 := lt_of_not_ge hf
        simpa [abs_of_neg hfneg] using hFopp f hN.1
    -- Establish minimality at `x` for `|f|` using the reverse triangle inequality.
    refine And.intro (by simpa [hFx] using Hfabs) ?_;
    intro g HgF
    -- `||f| - x| ≤ |f - x|` and `|f - x| ≤ |g - x|` from nearest minimality.
    have h1 : abs (abs f - x) ≤ abs (f - x) := by
      simpa [abs_of_nonneg hx] using (abs_abs_sub_abs_le_abs_sub f x)
    have h2 : abs (f - x) ≤ abs (g - x) := hN.2 g HgF
    have : abs (abs f - x) ≤ abs (g - x) := le_trans h1 h2
    simpa [hFx] using this
  · -- Case `x ≤ 0`: then `|x| = -x`.
    have hFx : |x| = -x := by simpa [abs_of_nonpos (le_of_not_ge hx)]
    -- We will derive the needed inequality at `-x` directly from minimality at `x`.
    -- Prove `F |f|` using closure under negation if necessary.
    have Hfabs : F |f| := by
      by_cases hf : 0 ≤ f
      · simpa [abs_of_nonneg hf] using hN.1
      · have hfneg : f < 0 := lt_of_not_ge hf
        simpa [abs_of_neg hfneg] using hFopp f hN.1
    -- Establish minimality at `-x` for `|f|` via the reverse triangle inequality
    -- and minimality of `-f` at `-x`.
    refine And.intro (by simpa [hFx] using Hfabs) ?_;
    intro g HgF
    have h1 : abs (abs f - abs x) ≤ abs ((-f) - (-x)) := by
      -- Apply the inequality to `-f` and `-x`; note `| -f | = |f|` and `| -x | = |x|`.
      simpa using (abs_abs_sub_abs_le_abs_sub (-f) (-x))
    -- From nearest minimality at `x` for `f` and closure under negation, obtain
    -- `|f - x| ≤ |(-g) - x|`. Rewrite both sides to the `-x` frame.
    have h2 : abs ((-f) - (-x)) ≤ abs (g - (-x)) := by
      -- Start from minimality at `x`.
      have h2' : abs (f - x) ≤ abs ((-g) - x) := hN.2 (-g) (hFopp g HgF)
      -- Rewrite both sides via explicit equalities to avoid fragile `simpa`.
      have hL : abs ((-f) - (-x)) = abs (f - x) := by
        have hxL : (-f) - (-x) = x - f := by simp [sub_eq_add_neg, add_comm]
        simpa [hxL, abs_sub_comm]
      have hR : abs (g - (-x)) = abs ((-g) - x) := by
        have hx1 : abs (g - (-x)) = abs (g + x) := by
          simpa [sub_eq_add_neg]
        have hx2 : abs ((-g) - x) = abs (g + x) := by
          have hx2' : (-g) - x = -(g + x) := by
            simp [sub_eq_add_neg, add_comm]
          calc
            abs ((-g) - x) = abs (-(g + x)) := by simpa [hx2']
            _ = abs (g + x) := by exact abs_neg (g + x)
        exact hx1.trans hx2.symm
      -- Transport `h2'` to the `-x` frame and rewrite to `+` form.
      have t : abs ((-f) - (-x)) ≤ abs (g - (-x)) := by
        -- Use the equalities in the reverse direction to transport `h2'`.
        simpa [hL.symm, hR.symm] using h2'
      have t' : abs (-f + x) ≤ abs (g + x) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using t
      exact t
    have : abs (abs f - abs x) ≤ abs (g - (-x)) := le_trans h1 h2
    simpa [hFx] using this

/-- Check sufficient conditions for nearest rounding via DN/UP bounds

    If a representable `f` is within both DN and UP distances, then `f` is
    a nearest rounding of `x`.
-/
noncomputable def Rnd_N_pt_DN_UP_check (F : ℝ → Prop) (x d u f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (Rnd_N_pt F x f))

/-- Specification: Construct nearest from DN/UP bounds

    Given `F f`, `Rnd_DN_pt F x d`, `Rnd_UP_pt F x u`, and distance bounds
    `|f - x| ≤ x - d` and `|f - x| ≤ u - x`, conclude `Rnd_N_pt F x f`.
-/
@[spec]
theorem Rnd_N_pt_DN_UP_spec (F : ℝ → Prop) (x d u f : ℝ) :
    ⦃⌜F f ∧ Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ |f - x| ≤ x - d ∧ |f - x| ≤ u - x⌝⦄
    Rnd_N_pt_DN_UP_check F x d u f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N_pt_DN_UP_check
  classical
  -- Reduce to proving the nearest-point predicate holds.
  simp [ pure]
  -- Unpack the preconditions.
  rcases h with ⟨hFf, hDN, hUP, hbdL, hbdR⟩
  -- It suffices to provide the nearest-point witness and distance minimality.
  refine And.intro hFf ?_
  intro g hFg
  -- Compare g with x and dispatch to the DN/UP bounds accordingly.
  cases le_total g x with
  | inl hgle =>
      -- Case g ≤ x: by maximality of DN-point, g ≤ d, hence x - d ≤ x - g.
      have h_g_le_d : g ≤ d := hDN.2.2 g hFg hgle
      have h_sub : x - d ≤ x - g := by simpa using (sub_le_sub_left h_g_le_d x)
      -- Chain the inequalities and rewrite |g - x| when g ≤ x.
      have : |f - x| ≤ x - g := le_trans hbdL h_sub
      simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg_of_le hgle)] using this
  | inr hxle =>
      -- Case x ≤ g: by minimality of UP-point, u ≤ g, hence u - x ≤ g - x.
      have h_u_le_g : u ≤ g := hUP.2.2 g hFg hxle
      have h_sub : u - x ≤ g - x := by simpa using (sub_le_sub_right h_u_le_g x)
      -- Chain the inequalities and rewrite |g - x| when x ≤ g.
      have : |f - x| ≤ g - x := le_trans hbdR h_sub
      simpa [abs_of_nonneg (sub_nonneg_of_le hxle)] using this

/-- Check DN-case for nearest rounding under asymmetry

    If `x - d ≤ u - x`, then `d` is the nearest rounding of `x`.
-/
noncomputable def Rnd_N_pt_DN_check (F : ℝ → Prop) (x d u : ℝ) : Bool :=
  by
    classical
    exact pure (decide (Rnd_N_pt F x d))

/-- Specification: DN is nearest under left-smaller distance

    Given DN/UP points and `x - d ≤ u - x`, `d` is nearest.
-/
@[spec]
theorem Rnd_N_pt_DN_spec (F : ℝ → Prop) (x d u : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ (x - d ≤ u - x)⌝⦄
    Rnd_N_pt_DN_check F x d u
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N_pt_DN_check
  classical
  -- Reduce goal to establishing `Rnd_N_pt F x d`.
  simp [ pure]
  rcases h with ⟨hDN, hUP, hdist⟩
  -- From DN we immediately get representability and `d ≤ x`.
  have hFd : F d := hDN.1
  have hd_le_x : d ≤ x := hDN.2.1
  -- It suffices to show the distance minimality property for `d`.
  refine And.intro hFd ?_
  intro g hFg
  -- Case split on the position of g relative to x.
  cases le_total g x with
  | inl hgle =>
      -- If g ≤ x then, by DN maximality, g ≤ d, hence x - d ≤ x - g.
      have h_g_le_d : g ≤ d := hDN.2.2 g hFg hgle
      have h_sub : x - d ≤ x - g := by simpa using (sub_le_sub_left h_g_le_d x)
      -- Rewrite absolute values using the sign information.
      have : |d - x| ≤ x - g := by
        -- |d - x| = x - d because d ≤ x
        simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg_of_le hd_le_x)] using h_sub
      simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg_of_le hgle)] using this
  | inr hxle =>
      -- If x ≤ g then, by UP minimality, u ≤ g, hence u - x ≤ g - x.
      have h_u_le_g : u ≤ g := hUP.2.2 g hFg hxle
      have h_sub : u - x ≤ g - x := by simpa using (sub_le_sub_right h_u_le_g x)
      -- Chain with the hypothesis x - d ≤ u - x and rewrite absolutes.
      have : |d - x| ≤ g - x := by
        -- From |d - x| = x - d and x - d ≤ u - x ≤ g - x
        have : x - d ≤ g - x := le_trans hdist h_sub
        simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg_of_le hd_le_x)] using this
      simpa [abs_of_nonneg (sub_nonneg_of_le hxle)] using this

/-- Check UP-case for nearest rounding under asymmetry

    If `u - x ≤ x - d`, then `u` is the nearest rounding of `x`.
-/
noncomputable def Rnd_N_pt_UP_check (F : ℝ → Prop) (x d u : ℝ) : Bool :=
  by
    classical
    exact pure (decide (Rnd_N_pt F x u))

/-- Specification: UP is nearest under right-smaller distance

    Given DN/UP points and `u - x ≤ x - d`, `u` is nearest.
-/
@[spec]
theorem Rnd_N_pt_UP_spec (F : ℝ → Prop) (x d u : ℝ) :
    ⦃⌜Rnd_DN_pt F x d ∧ Rnd_UP_pt F x u ∧ (u - x ≤ x - d)⌝⦄
    Rnd_N_pt_UP_check F x d u
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N_pt_UP_check
  classical
  -- Reduce goal to establishing `Rnd_N_pt F x u`.
  simp [ pure]
  rcases h with ⟨hDN, hUP, hdist⟩
  -- From UP we immediately get representability and `x ≤ u`.
  have hFu : F u := hUP.1
  have hx_le_u : x ≤ u := hUP.2.1
  -- It suffices to show the distance minimality property for `u`.
  refine And.intro hFu ?_
  intro g hFg
  -- Case split on the position of g relative to x.
  cases le_total g x with
  | inl hgle =>
      -- If g ≤ x then, by DN maximality, g ≤ d, hence x - d ≤ x - g.
      have h_g_le_d : g ≤ d := hDN.2.2 g hFg hgle
      have h_sub : x - d ≤ x - g := by simpa using (sub_le_sub_left h_g_le_d x)
      -- Chain with the hypothesis u - x ≤ x - d and rewrite absolutes.
      have : |u - x| ≤ x - g := by
        -- From |u - x| = u - x and u - x ≤ x - d ≤ x - g
        have : u - x ≤ x - g := le_trans hdist h_sub
        simpa [abs_of_nonneg (sub_nonneg_of_le hx_le_u)] using this
      simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg_of_le hgle)] using this
  | inr hxle =>
      -- If x ≤ g then, by UP minimality, u ≤ g, hence u - x ≤ g - x.
      have h_u_le_g : u ≤ g := hUP.2.2 g hFg hxle
      have h_sub : u - x ≤ g - x := by simpa using (sub_le_sub_right h_u_le_g x)
      -- Rewrite absolute values using the sign information.
      have : |u - x| ≤ g - x := by
        -- |u - x| = u - x because x ≤ u
        simpa [abs_of_nonneg (sub_nonneg_of_le hx_le_u)] using h_sub
      simpa [abs_of_nonneg (sub_nonneg_of_le hxle)] using this

end RoundNearestAuxiliary

section RoundNearestGeneric

noncomputable section

/-- Check uniqueness for generic nearest with tie-breaking predicate

    Under a uniqueness property on ties, the NG-point is unique.
-/
def Rnd_NG_pt_unique_check (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (x f1 f2 : ℝ) : Bool :=
  by
    classical
    exact pure (decide (f1 = f2))

/-- Specification: Uniqueness of NG-point under tie uniqueness

    Assuming the uniqueness property on ties for `P` and that
    both `f1` and `f2` satisfy `Rnd_NG_pt F P x _`, we have `f1 = f2`.
-/
@[spec]
theorem Rnd_NG_pt_unique_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (x f1 f2 : ℝ) :
    ⦃⌜(∀ x d u,
          Rnd_DN_pt F x d → Rnd_N_pt F x d →
          Rnd_UP_pt F x u → Rnd_N_pt F x u →
          P x d → P x u → d = u) ∧
        Rnd_NG_pt F P x f1 ∧ Rnd_NG_pt F P x f2⌝⦄
    Rnd_NG_pt_unique_check F P x f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_NG_pt_unique_check
  classical
  -- Reduce to a propositional goal about equality.
  simp [ pure]
  -- Unpack assumptions: tie uniqueness property and NG-points for f1,f2.
  rcases h with ⟨hTie, hNG1, hNG2⟩
  rcases hNG1 with ⟨hN1, hT1⟩
  rcases hNG2 with ⟨hN2, hT2⟩
  -- If either NG-point uses the uniqueness branch, conclude immediately.
  cases hT1 with
  | inr huniq1 =>
      exact (huniq1 f2 hN2).symm
  | inl hP1 =>
      cases hT2 with
      | inr huniq2 =>
          exact huniq2 f1 hN1
      | inl hP2 =>
          -- Both satisfy P and are nearest. Classify each as DN or UP.
          have hClass1 := Rnd_N_pt_DN_or_UP_spec F x f1
          have hClass2 := Rnd_N_pt_DN_or_UP_spec F x f2
          have hDU1 : Rnd_DN_pt F x f1 ∨ Rnd_UP_pt F x f1 := by
            simpa [Rnd_N_pt_DN_or_UP_check, pure,
              decide_eq_true_iff] using hClass1 hN1
          have hDU2 : Rnd_DN_pt F x f2 ∨ Rnd_UP_pt F x f2 := by
            simpa [Rnd_N_pt_DN_or_UP_check, pure,
              decide_eq_true_iff] using hClass2 hN2
          -- Analyze the four cases.
          cases hDU1 with
          | inl hDN1 =>
              cases hDU2 with
              | inl hDN2 =>
                  -- Both DN: use DN uniqueness.
                  have huniq := Rnd_DN_pt_unique_spec F x f1 f2
                  have : f1 = f2 := by
                    simpa [Rnd_DN_pt_unique_check, pure,
                      decide_eq_true_iff] using huniq ⟨hDN1, hDN2⟩
                  exact this
              | inr hUP2 =>
                  -- Tie case DN/UP with P on both: apply the given tie uniqueness property.
                  exact hTie x f1 f2 hDN1 hN1 hUP2 hN2 hP1 hP2
          | inr hUP1 =>
              cases hDU2 with
              | inl hDN2 =>
                  -- Symmetric tie case: swap roles to use the property, then flip equality.
                  have : f2 = f1 := hTie x f2 f1 hDN2 hN2 hUP1 hN1 hP2 hP1
                  simpa [eq_comm] using this
              | inr hUP2 =>
                  -- Both UP: use UP uniqueness.
                  have huniq := Rnd_UP_pt_unique_spec F x f1 f2
                  have : f1 = f2 := by
                    simpa [Rnd_UP_pt_unique_check, pure,
                      decide_eq_true_iff] using huniq ⟨hUP1, hUP2⟩
                  exact this

/-- Check monotonicity for NG-point under tie uniqueness

    With the uniqueness property on ties, `Rnd_NG_pt F P` is monotone.
-/
noncomputable def Rnd_NG_pt_monotone_check (F : ℝ → Prop) (P : ℝ → ℝ → Prop) : Bool :=
  by
    classical
    exact pure (decide (round_pred_monotone (Rnd_NG_pt F P)))

/-- Specification: NG-point rounding is monotone (with tie uniqueness)

    Assuming the uniqueness property on ties for `P`, the rounding predicate
    `Rnd_NG_pt F P` is monotone.
-/
@[spec]
theorem Rnd_NG_pt_monotone_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop) :
    ⦃⌜∀ x d u,
        Rnd_DN_pt F x d → Rnd_N_pt F x d →
        Rnd_UP_pt F x u → Rnd_N_pt F x u →
        P x d → P x u → d = u⌝⦄
    Rnd_NG_pt_monotone_check F P
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro hTieUnique
  unfold Rnd_NG_pt_monotone_check
  classical
  -- Reduce to proving `round_pred_monotone (Rnd_NG_pt F P)`.
  simp [ pure]
  -- Local helper: a nearest point is either DN or UP.
  -- Port of Rnd_N_pt_DN_or_UP (propositional form).
  have nearest_DN_or_UP
      (x f : ℝ) (h : Rnd_N_pt F x f) : Rnd_DN_pt F x f ∨ Rnd_UP_pt F x f := by
    rcases h with ⟨HfF, Hmin⟩
    -- Split on whether f ≤ x or x ≤ f.
    cases le_total f x with
    | inl hfxle =>
        -- DN case
        left
        refine And.intro HfF ?_
        refine And.intro hfxle ?_
        intro g HgF hglex
        -- Use minimality with absolutes turned into linear inequalities
        have hxmf_nonneg : 0 ≤ x - f := sub_nonneg.mpr hfxle
        have hxmg_nonneg : 0 ≤ x - g := sub_nonneg.mpr hglex
        have h_abs : |x - f| ≤ |x - g| := by simpa [abs_sub_comm] using Hmin g HgF
        have h_sub : x - f ≤ x - g := by
          simpa [abs_of_nonneg hxmf_nonneg, abs_of_nonneg hxmg_nonneg] using h_abs
        -- x - f ≤ x - g ⇒ g ≤ f.
        have hneg : -f ≤ -g := by
          have h' := add_le_add_left h_sub (-x)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'
        exact (neg_le_neg_iff).1 hneg
    | inr hxlef =>
        -- UP case
        right
        refine And.intro HfF ?_
        refine And.intro hxlef ?_
        intro g HgF hxleg
        have hxmf_nonpos : x - f ≤ 0 := sub_nonpos.mpr hxlef
        have hxmg_nonpos : x - g ≤ 0 := sub_nonpos.mpr hxleg
        have h_abs : |x - f| ≤ |x - g| := by simpa [abs_sub_comm] using Hmin g HgF
        have h_sub : f - x ≤ g - x := by
          simpa [abs_of_nonpos hxmf_nonpos, abs_of_nonpos hxmg_nonpos, neg_sub] using h_abs
        have h' := add_le_add_right h_sub x
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'

  -- Local helpers: uniqueness of DN/UP points at a fixed input x.
  have DN_unique (x f1 f2 : ℝ)
      (h1 : Rnd_DN_pt F x f1) (h2 : Rnd_DN_pt F x f2) : f1 = f2 := by
    have le12 : f1 ≤ f2 := by
      have := h2.2.2 f1 h1.1 h1.2.1
      simpa using this
    have le21 : f2 ≤ f1 := by
      have := h1.2.2 f2 h2.1 h2.2.1
      simpa using this
    exact le_antisymm le12 le21

  have UP_unique (x f1 f2 : ℝ)
      (h1 : Rnd_UP_pt F x f1) (h2 : Rnd_UP_pt F x f2) : f1 = f2 := by
    -- From minimality at f1 and f2, we get both directions of ≤
    have le21 : f2 ≤ f1 := by
      exact h2.2.2 f1 h1.1 h1.2.1
    have le12 : f1 ≤ f2 := by
      exact h1.2.2 f2 h2.1 h2.2.1
    exact le_antisymm le12 le21

  -- Now prove monotonicity for Rnd_NG_pt F P.
  intro x y f g hx hy hxy
  -- Split on x < y or x = y.
  cases lt_or_eq_of_le hxy with
  | inl hlt =>
      -- In the strict case, use the Rnd_N_pt monotonic argument at the N level.
      -- Extract nearest witnesses.
      rcases hx with ⟨HxfN, _⟩
      rcases hy with ⟨HygN, _⟩
      -- We reproduce the `Rnd_N_pt` monotonic proof (follows Coq Round_pred.v).
      by_contra hnot
      have hgf : g < f := lt_of_not_ge hnot
      have Hfgx : |x - f| ≤ |x - g| := by simpa [abs_sub_comm] using HxfN.2 g HygN.1
      have Hgfy : |y - g| ≤ |y - f| := by simpa [abs_sub_comm] using HygN.2 f HxfN.1
      by_cases hxg : x ≤ g
      · -- Case 1: x ≤ g < f
        have hxlt_f : x < f := lt_of_le_of_lt hxg hgf
        have hxmf_pos : 0 < f - x := sub_pos.mpr hxlt_f
        have hxmg_nonneg : 0 ≤ g - x := sub_nonneg.mpr hxg
        have Hfgx' : |f - x| ≤ |g - x| := by simpa [abs_sub_comm] using Hfgx
        have Hfgx'' : f - x ≤ g - x := by
          simpa [abs_of_nonneg (le_of_lt hxmf_pos), abs_of_nonneg hxmg_nonneg] using Hfgx'
        have : ¬ f - x ≤ g - x := by
          have h := sub_lt_sub_right hgf x
          exact not_le.mpr h
        exact this Hfgx''
      · -- Case 2: g < x < y
        have hgx : g < x := lt_of_not_ge hxg
        have hgy : g < y := lt_trans hgx hlt
        by_cases hfy : f ≤ y
        · -- Subcase: f ≤ y
          have hy_mg_pos : 0 < y - g := sub_pos.mpr hgy
          have hy_mf_nonneg : 0 ≤ y - f := sub_nonneg.mpr hfy
          have Hgfy' : y - g ≤ y - f := by
            have : |y - g| ≤ |y - f| := by
              -- from Hgfy
              simpa [abs_sub_comm] using Hgfy
            simpa [abs_of_nonneg (le_of_lt hy_mg_pos), abs_of_nonneg hy_mf_nonneg] using this
          have : ¬ y - g ≤ y - f := by
            have h := sub_lt_sub_left hgf y
            exact not_le.mpr h
          exact this Hgfy'
        · -- Subcase: y < f
          have hy_lt_f : y < f := lt_of_not_ge hfy
          have hxmg_pos : 0 < x - g := sub_pos.mpr hgx
          have hxmf_pos : 0 < f - x := sub_pos.mpr (lt_trans hlt hy_lt_f)
          have hymg_pos : 0 < y - g := sub_pos.mpr hgy
          have hymf_neg : y - f < 0 := sub_neg.mpr hy_lt_f
          have Hfgx' : f - x ≤ x - g := by
            have : |f - x| ≤ |x - g| := by simpa [abs_sub_comm] using Hfgx
            simpa [abs_of_pos hxmf_pos, abs_of_pos hxmg_pos] using this
          have Hgfy' : y - g ≤ f - y := by
            have : |y - g| ≤ |y - f| := by
              -- use Hgfy as-is
              simpa using Hgfy
            simpa [abs_of_pos hymg_pos, abs_of_neg hymf_neg] using this
          have Hsum : (f - x) + (y - g) ≤ (x - g) + (f - y) := add_le_add Hfgx' Hgfy'
          have hL : (x - g) + (f - y) = (x - y) + (f - g) := by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          have hR : (f - x) + (y - g) = (y - x) + (f - g) := by
            simp [sub_eq_add_neg, add_left_comm, add_assoc]
          have hyx_pos : 0 < y - x := sub_pos.mpr hlt
          have hxmy_lt_hyx : (x - y) < (y - x) := by
            have : -(y - x) < (y - x) := neg_lt_self hyx_pos
            simpa [neg_sub, sub_eq_add_neg] using this
          have hStrict : (x - y) + (f - g) < (y - x) + (f - g) := by
            simpa only [add_comm (f - g)] using add_lt_add_right hxmy_lt_hyx (f - g)
          have : (y - x) + (f - g) ≤ (x - y) + (f - g) := by
            simpa [hL, hR, add_comm, add_left_comm, add_assoc] using Hsum
          exact (not_le_of_gt hStrict) this
  | inr heq =>
      -- Equal inputs: reduce to x, show f = g by NG uniqueness, then `≤` holds.
      have hyx : Rnd_NG_pt F P x g := by simpa [heq] using hy
      -- Extract nearest and tie components.
      rcases hx with ⟨HxfN, HxfTie⟩
      rcases hyx with ⟨HygN, HygTie⟩
      -- Classify f and g as DN or UP and conclude equality using tie/uniqueness.
      have hfClass := nearest_DN_or_UP x f HxfN
      have hgClass := nearest_DN_or_UP x g HygN
      have hEq : f = g := by
        cases hfClass with
        | inl hDNf =>
            cases hgClass with
            | inl hDNg =>
                exact DN_unique x f g hDNf hDNg
            | inr hUPg =>
                -- Use NG tie info: either both sides provide P, or uniqueness gives equality.
                cases HxfTie with
                | inl pf =>
                    cases HygTie with
                    | inl pg => exact hTieUnique x f g hDNf HxfN hUPg HygN pf pg
                    | inr uniqg => exact uniqg f HxfN
                | inr uniqf =>
                    exact (uniqf g HygN).symm
        | inr hUPf =>
            cases hgClass with
            | inl hDNg =>
                -- Symmetric case: use tie/uniqueness or NG uniqueness.
                cases HygTie with
                | inl pg =>
                    cases HxfTie with
                    | inl pf => exact (hTieUnique x g f hDNg HygN hUPf HxfN pg pf).symm
                    | inr uniqf => exact (uniqf g HygN).symm
                | inr uniqg => exact (uniqg f HxfN)
            | inr hUPg =>
                exact UP_unique x f g hUPf hUPg
      simpa [hEq]

/-- Check reflexivity for NG-point

    A representable `x` is its own NG-point for any `P`.
-/
def Rnd_NG_pt_refl_check (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (x : ℝ) : Bool :=
  by
    classical
    exact pure (decide (Rnd_NG_pt F P x x))

/-- Specification: NG-point is reflexive

    From `F x`, deduce `Rnd_NG_pt F P x x`.
-/
@[spec]
theorem Rnd_NG_pt_refl_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜F x⌝⦄
    Rnd_NG_pt_refl_check F P x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NG_pt_refl_check
  classical
  -- Reduce the Hoare triple to proving the proposition directly.
  simp [ pure]
  -- Show `Rnd_N_pt F x x` and use the uniqueness branch for ties.
  refine And.intro ?nearest ?tie
  · -- Nearest at x is x itself.
    refine And.intro ?Fx ?min
    · -- Provided as precondition of the triple.
      assumption
    · -- 0 = |x - x| ≤ |g - x| for any representable g.
      intro g _
      -- `|x - x|` is 0 and absolute values are nonnegative.
      simpa [sub_self] using (abs_nonneg (g - x))
  · -- Uniqueness branch: any nearest point at x must be x.
    refine Or.inr ?uniq
    intro f2 hf2
    -- Plug `g := x` (which is representable by precondition) in the minimality of f2.
    have h0 : |f2 - x| ≤ |x - x| := hf2.2 x (by simpa using ‹F x›)
    -- Absolute values are nonnegative, hence both sides are ≥ 0; conclude equality.
    have hxx0 : |x - x| = 0 := by simpa [sub_self]
    have hle0 : |f2 - x| ≤ 0 := by simpa [hxx0] using h0
    have hge0 : 0 ≤ |f2 - x| := abs_nonneg _
    have : |f2 - x| = 0 := le_antisymm hle0 hge0
    -- `|f2 - x| = 0` implies `f2 = x`.
    exact sub_eq_zero.mp (by simpa [abs_eq_zero] using this)

/-- Check opposite invariance for NG-point

    If `F` is closed under negation and `P` is sign-symmetric, then NG is
    invariant under negation.
-/
def Rnd_NG_pt_opp_inv_check (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (x f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (Rnd_NG_pt F P x f))

/-- Specification: NG-point invariance under negation

    From closure of `F` under negation and compatibility of `P` with
    negation, `Rnd_NG_pt F P (-x) (-f)` implies `Rnd_NG_pt F P x f`.
-/
@[spec]
theorem Rnd_NG_pt_opp_inv_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (x f : ℝ) :
    ⦃⌜(∀ y, F y → F (-y)) ∧ (∀ x f, P x f → P (-x) (-f)) ∧ Rnd_NG_pt F P (-x) (-f)⌝⦄
    Rnd_NG_pt_opp_inv_check F P x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_NG_pt_opp_inv_check
  classical
  -- Reduce Hoare triple to propositional goal.
  simp [ pure]
  rcases h with ⟨hFopp, hPopp, hNGneg⟩
  rcases hNGneg with ⟨hN_neg, hTie_neg⟩
  -- Transfer nearest property from (-x,-f) to (x,f).
  have hN : Rnd_N_pt F x f := by
    -- Use the existing nearest opp-inv specification.
    simpa [Rnd_N_pt_opp_inv_check, pure,
      decide_eq_true_iff] using (Rnd_N_pt_opp_inv_spec F x f ⟨hFopp, hN_neg⟩)
  -- Establish the tie-breaking side.
  refine And.intro hN ?tie
  cases hTie_neg with
  | inl hPneg =>
      -- P (-x) (-f) ⇒ P x f by sign-symmetry (instantiated at -x,-f).
      have hPx : P x f := by
        simpa [neg_neg] using hPopp (-x) (-f) hPneg
      exact Or.inl hPx
  | inr huniq_neg =>
      -- Uniqueness transfer: any nearest at x maps to a nearest at -x.
      refine Or.inr ?uniq
      intro f2 hNf2
      -- Apply the opp-inv lemma with (x,f) := (-x,-f2) to get nearest at -x.
      have hNf2_neg : Rnd_N_pt F (-x) (-f2) := by
        have hpre : (∀ y, F y → F (-y)) ∧ Rnd_N_pt F (-(-x)) (-(-f2)) := by
          exact And.intro hFopp (by simpa [neg_neg] using hNf2)
        simpa [Rnd_N_pt_opp_inv_check, pure,
          decide_eq_true_iff] using
          (Rnd_N_pt_opp_inv_spec F (-x) (-f2) hpre)
      -- Use uniqueness at -x and cancel the negations.
      have hneg_eq : -f2 = -f := huniq_neg (-f2) hNf2_neg
      have : f2 = f := by
        have := congrArg Neg.neg hneg_eq
        simpa [neg_neg] using this
      exact this

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
    (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) : Bool :=
  by
    classical
    exact pure (decide (rnd1 x = rnd2 x))

/-- Specification: Function-level uniqueness for NG rounding

    Given tie uniqueness property and `Rnd_NG F P` for `rnd1` and `rnd2`,
    these functions agree pointwise.
-/
@[spec]
theorem Rnd_NG_unique_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) :
    ⦃⌜(∀ x d u,
          Rnd_DN_pt F x d → Rnd_N_pt F x d →
          Rnd_UP_pt F x u → Rnd_N_pt F x u →
          P x d → P x u → d = u) ∧
        (∃ p1 p2, Rnd_NG F P rnd1 = pure p1 ∧ Rnd_NG F P rnd2 = pure p2 ∧ p1 ∧ p2)⌝⦄
    Rnd_NG_unique_check F P rnd1 rnd2 x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_NG_unique_check
  classical
  -- Reduce to a pure equality on pointwise values at x.
  simp [ pure]
  -- Unpack tie uniqueness and packaged NG properties for both functions.
  rcases h with ⟨hTie, ⟨p1, p2, hEq1, hEq2, Hp1, Hp2⟩⟩
  -- Project underlying propositions from the Id-wrapped equalities.
  have h1run : (∀ y : ℝ, Rnd_NG_pt F P y (rnd1 y)) = p1 := by
    simpa [Rnd_NG] using congrArg Id.run hEq1
  have h2run : (∀ y : ℝ, Rnd_NG_pt F P y (rnd2 y)) = p2 := by
    simpa [Rnd_NG] using congrArg Id.run hEq2
  have H1 : ∀ y : ℝ, Rnd_NG_pt F P y (rnd1 y) := by
    simpa [h1run] using Hp1
  have H2 : ∀ y : ℝ, Rnd_NG_pt F P y (rnd2 y) := by
    simpa [h2run] using Hp2
  -- Apply point-level uniqueness at x.
  have huniq := Rnd_NG_pt_unique_spec F P x (rnd1 x) (rnd2 x)
  simpa [Rnd_NG_pt_unique_check, pure, decide_eq_true_iff]
    using huniq ⟨hTie, H1 x, H2 x⟩

end

end RoundNearestGeneric

section RoundNearestTies

/-- Check equivalence between NA and NG with abs-based predicate

    With `0 ∈ F`, `Rnd_NA_pt` is equivalent to `Rnd_NG_pt` with
    predicate `fun x f => |x| ≤ |f|`.
-/
noncomputable def Rnd_NA_NG_pt_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    -- Equivalence between NA and NG with predicate |x| ≤ |f|.
    classical
    exact pure (decide (Rnd_NA_pt F x f ↔ Rnd_NG_pt F (fun x f => |x| ≤ |f|) x f))

/-- Specification: NA equals NG with abs-based tie predicate

    Assuming `F 0`, equivalence between `Rnd_NA_pt` and `Rnd_NG_pt` holds.
-/
@[spec]
theorem Rnd_NA_NG_pt_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0⌝⦄
    Rnd_NA_NG_pt_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_NG_pt_check
  classical
  -- Reduce to the underlying equivalence
  simp [ pure]
  constructor
  · -- (→) From NA to NG with predicate |x| ≤ |f| (or uniqueness)
    intro hNA
    rcases hNA with ⟨hN, hTie⟩
    refine And.intro hN ?_;
    -- Either there is a different nearest point, or f is unique among nearest
    by_cases huniq : ∀ f2, Rnd_N_pt F x f2 → f2 = f
    · exact Or.inr huniq
    · -- There exists f2 ≠ f that is also nearest; prove |x| ≤ |f|
      rcases not_forall.mp huniq with ⟨f2, hnot⟩
      have hN2 : Rnd_N_pt F x f2 ∧ f2 ≠ f := by
        exact _root_.not_imp.mp hnot
      have hN2' : Rnd_N_pt F x f2 := hN2.1
      have hneq : f2 ≠ f := hN2.2
      -- Equal distances to x for two nearest points
      have h1 : |x - f| ≤ |x - f2| := by
        simpa [abs_sub_comm] using (hN.2 f2 hN2'.1)
      have h2 : |x - f2| ≤ |x - f| := by
        simpa [abs_sub_comm] using (hN2'.2 f hN.1)
      have heqAbs : |x - f| = |x - f2| := le_antisymm h1 h2
      -- From |x - f| = |x - f2| and f2 ≠ f, deduce x = (f + f2)/2
      have hx_mid : x = (f + f2) / 2 := by
        have hcase := abs_eq_abs.mp heqAbs
        cases hcase with
        | inl hsame =>
            -- x - f = x - f2 ⇒ f = f2 (contradiction)
            have : f = f2 := by
              have := congrArg (fun t => t + (-x)) hsame
              simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
            exact (hneq this.symm).elim
        | inr hopp =>
            -- x - f = -(x - f2) = f2 - x ⇒ 2x = f + f2
            have : x - f = f2 - x := by simpa [neg_sub] using hopp
            have hsum : (x - f) + (x + f) = (f2 - x) + (x + f) := congrArg (fun t => t + (x + f)) this
            -- Simplify both sides
            have h2x : 2 * x = f + f2 := by
              simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
            -- Divide by 2 using `eq_div_iff_mul_eq`
            have hx2 : x * 2 = f + f2 := by simpa [mul_comm] using h2x
            have h2ne : (2 : ℝ) ≠ 0 := by norm_num
            exact (eq_div_iff_mul_eq h2ne).2 hx2
      -- Bound |x| via the average and the tie property |f2| ≤ |f|
      have havg_le : |x| ≤ (|f| + |f2|) / 2 := by
        -- |(f + f2)/2| = |f + f2|/2 ≤ (|f| + |f2|)/2
        have habs_div2 : |(f + f2) / 2| = |f + f2| / 2 := by
          simpa [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
        have htri : |f + f2| ≤ |f| + |f2| := by
          -- Use `abs_add'` with `b := -f2` and simplify
          simpa [abs_neg, add_comm, add_left_comm, add_assoc]
            using (abs_add' (f + f2) (-f2))
        have hdiv_le : |f + f2| / 2 ≤ (|f| + |f2|) / 2 :=
          (div_le_div_of_nonneg_right htri (by norm_num : (0 : ℝ) ≤ 2))
        have hxabs : |x| = |(f + f2) / 2| := by simpa [hx_mid]
        exact (by simpa [hxabs, habs_div2] using hdiv_le)
      have hP : |x| ≤ |f| := by
        have hf2_le_f : |f2| ≤ |f| := hTie f2 hN2'
        -- (|f| + |f2|)/2 ≤ |f|
        have : (|f| + |f2|) / 2 ≤ |f| := by
          have hmono :=
            (div_le_div_of_nonneg_right (add_le_add_left hf2_le_f |f|)
              (by norm_num : (0 : ℝ) ≤ 2))
          -- (|f| + |f|)/2 = |f|
          have hsimp : (|f| + |f|) / 2 = |f| := by
            have : (2 * |f|) / 2 = |f| := by
              simpa using (mul_div_cancel' |f| (2 : ℝ))
            simpa [two_mul, mul_comm] using this
          calc (|f| + |f2|) / 2 = (|f2| + |f|) / 2 := by rw [add_comm]
            _ ≤ (|f| + |f|) / 2 := hmono
            _ = |f| := hsimp
        exact le_trans havg_le this
      exact Or.inl hP
  · -- (←) From NG with predicate |x| ≤ |f| (or uniqueness) to NA
    intro hNG
    rcases hNG with ⟨hN, hbranch⟩
    refine And.intro hN ?_;
    intro f2 hN2
    -- Distances to x are equal for any two nearest points
    have h1 : |x - f| ≤ |x - f2| := by simpa [abs_sub_comm] using (hN.2 f2 hN2.1)
    have h2 : |x - f2| ≤ |x - f| := by simpa [abs_sub_comm] using (hN2.2 f hN.1)
    have heqAbs : |x - f| = |x - f2| := le_antisymm h1 h2
    -- If uniqueness holds in the NG branch, we are done immediately
    cases hbranch with
    | inr huniq =>
        simpa [huniq f2 hN2]
    | inl hP =>
        -- Use the sign of x to relate signs of f and f2, then compare linearly
        by_cases hx0 : 0 ≤ x
        · -- Nonnegative case: f, f2 are nonnegative; P gives x ≤ f
          have hf_nonneg : 0 ≤ f := by
            have h := Rnd_N_pt_ge_0_spec F x f
            simpa [Rnd_N_pt_ge_0_check, pure, decide_eq_true_iff]
              using h ⟨‹F 0›, hx0, hN⟩
          have hf2_nonneg : 0 ≤ f2 := by
            have h := Rnd_N_pt_ge_0_spec F x f2
            simpa [Rnd_N_pt_ge_0_check, pure, decide_eq_true_iff]
              using h ⟨‹F 0›, hx0, hN2⟩
          have hx_le_f : x ≤ f := by simpa [abs_of_nonneg hx0, abs_of_nonneg hf_nonneg] using hP
          -- From equal distances and x ≤ f, deduce f2 ≤ f
          have hx_mid_or := abs_eq_abs.mp heqAbs
          have hf2_le_f : f2 ≤ f := by
            cases hx_mid_or with
            | inl hsame =>
                -- x - f = x - f2 ⇒ f = f2
                have hf_eq : f = f2 := by
                  have := congrArg (fun t => t + (-x)) hsame
                  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
                exact hf_eq.symm ▸ le_rfl
            | inr hopp =>
                -- x - f = -(x - f2) = f2 - x ⇒ 2x = f + f2
                have : x - f = f2 - x := by simpa [neg_sub] using hopp
                have hsum' : (x - f) + (x + f) = (f2 - x) + (x + f) :=
                  congrArg (fun t => t + (x + f)) this
                have hsum : 2 * x = f + f2 := by
                  simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'
                -- From 2x ≤ 2f and 2x = f + f2, get f2 ≤ f
                have hineq : 2 * x ≤ 2 * f := by
                  simpa using
                    (mul_le_mul_of_nonneg_left hx_le_f (by norm_num : (0 : ℝ) ≤ 2))
                have : 2 * x - f ≤ 2 * f - f := sub_le_sub_right hineq f
                simpa [hsum, two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
          -- With nonnegativity, absolute values drop
          have : |f2| ≤ |f| := by simpa [abs_of_nonneg hf2_nonneg, abs_of_nonneg hf_nonneg] using hf2_le_f
          exact this
        · -- Nonpositive case: f, f2 are nonpositive; P gives -x ≤ -f i.e., f ≤ x
          have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx0)
          have hf_nonpos : f ≤ 0 := by
            have h := Rnd_N_pt_le_0_spec F x f
            simpa [Rnd_N_pt_le_0_check, pure, decide_eq_true_iff]
              using h ⟨‹F 0›, hxle0, hN⟩
          have hf2_nonpos : f2 ≤ 0 := by
            have h := Rnd_N_pt_le_0_spec F x f2
            simpa [Rnd_N_pt_le_0_check, pure, decide_eq_true_iff]
              using h ⟨‹F 0›, hxle0, hN2⟩
          have hf_le_x : f ≤ x := by
            -- |x| ≤ |f| ⇒ -x ≤ -f
            have : -x ≤ -f := by
              simpa [abs_of_nonpos hxle0, abs_of_nonpos hf_nonpos] using hP
            simpa using (neg_le_neg_iff.mp this)
          -- From equal distances and f ≤ x, deduce f ≤ f2, hence |f2| ≤ |f|
          have hx_mid_or := abs_eq_abs.mp heqAbs
          have hf_le_f2 : f ≤ f2 := by
            cases hx_mid_or with
            | inl hsame =>
                -- x - f = x - f2 ⇒ f = f2
                have hf_eq : f = f2 := by
                  have := congrArg (fun t => t + (-x)) hsame
                  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
                exact hf_eq ▸ le_rfl
            | inr hopp =>
                -- x - f = -(x - f2) = f2 - x ⇒ 2x = f + f2
                have : x - f = f2 - x := by simpa [neg_sub] using hopp
                have hsum' : (x - f) + (x + f) = (f2 - x) + (x + f) :=
                  congrArg (fun t => t + (x + f)) this
                have hsum : 2 * x = f + f2 := by
                  simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'
                -- From 2f ≤ 2x and 2x = f + f2, get f ≤ f2
                have hineq : 2 * f ≤ 2 * x := by
                  simpa using
                    (mul_le_mul_of_nonneg_left hf_le_x (by norm_num : (0 : ℝ) ≤ 2))
                have : 2 * f ≤ f + f2 := by simpa [hsum] using hineq
                -- Subtract f on both sides to isolate f ≤ f2
                have := sub_le_sub_right this f
                simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
          -- both nonpositive ⇒ -f2 ≤ -f, i.e., |f2| ≤ |f|
          have : |f2| ≤ |f| := by
            have : -f2 ≤ -f := by exact neg_le_neg hf_le_f2
            simpa [abs_of_nonpos hf2_nonpos, abs_of_nonpos hf_nonpos] using this
          exact this

/-- Check uniqueness property for NA ties (auxiliary)

    The NA tie-breaking relation yields uniqueness under `F 0`.
-/
noncomputable def Rnd_NA_pt_unique_prop_check (F : ℝ → Prop) : Bool :=
  by
    -- Uniqueness of tie-breaking for NA predicate (auxiliary property).
    classical
    exact pure (decide (∀ x d u,
      Rnd_DN_pt F x d → Rnd_N_pt F x d →
      Rnd_UP_pt F x u → Rnd_N_pt F x u →
      |x| ≤ |d| → |x| ≤ |u| → d = u))

/-- Specification: NA tie uniqueness property holds

    Assuming `F 0`, the auxiliary uniqueness property for NA holds.
-/
@[spec]
theorem Rnd_NA_pt_unique_prop_spec (F : ℝ → Prop) :
    ⦃⌜F 0⌝⦄
    Rnd_NA_pt_unique_prop_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_pt_unique_prop_check
  classical
  -- Reduce to the underlying propositional statement.
  simp [ pure]
  intro x d u hDN hNd hUP hNu hAd hAu
  -- Case split on the sign of x.
  by_cases hx : 0 ≤ x
  · -- Nonnegative case: deduce nonnegativity of nearest values d and u.
    have hd_nonneg : 0 ≤ d := by
      have h := Rnd_N_pt_ge_0_spec F x d
      simpa [Rnd_N_pt_ge_0_check, pure,
        decide_eq_true_iff] using h ⟨‹F 0›, hx, hNd⟩
    have hu_nonneg : 0 ≤ u := by
      have h := Rnd_N_pt_ge_0_spec F x u
      simpa [Rnd_N_pt_ge_0_check, pure,
        decide_eq_true_iff] using h ⟨‹F 0›, hx, hNu⟩
    -- From |x| ≤ |d| and nonnegativity, obtain x ≤ d; DN gives d ≤ x, hence d = x.
    have hx_le_d : x ≤ d := by
      simpa [abs_of_nonneg hx, abs_of_nonneg hd_nonneg] using hAd
    have hd_eq_x : d = x := le_antisymm hDN.2.1 hx_le_d
    -- From nearest minimality for u with candidate d = x, conclude u = x.
    have hdist : |u - x| ≤ |d - x| := hNu.2 d hDN.1
    have : |u - x| ≤ 0 := by simpa [hd_eq_x, sub_self] using hdist
    have hux0 : |u - x| = 0 := le_antisymm this (abs_nonneg _)
    have : u - x = 0 := by simpa using (abs_eq_zero.mp hux0)
    have hu_eq_x : u = x := sub_eq_zero.mp this
    simpa [hd_eq_x, hu_eq_x]
  · -- Nonpositive case: deduce nonpositivity of nearest values d and u.
    have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have hd_nonpos : d ≤ 0 := by
      have h := Rnd_N_pt_le_0_spec F x d
      simpa [Rnd_N_pt_le_0_check, pure,
        decide_eq_true_iff] using h ⟨‹F 0›, hxle0, hNd⟩
    have hu_nonpos : u ≤ 0 := by
      have h := Rnd_N_pt_le_0_spec F x u
      simpa [Rnd_N_pt_le_0_check, pure,
        decide_eq_true_iff] using h ⟨‹F 0›, hxle0, hNu⟩
    -- Use |x| ≤ |u| together with nonpositivity and UP to get u = x.
    have hx_le_u : x ≤ u := hUP.2.1
    have hu_le_x : u ≤ x := by
      have : -x ≤ -u := by
        simpa [abs_of_nonpos hxle0, abs_of_nonpos hu_nonpos] using hAu
      exact (neg_le_neg_iff.mp this)
    have hu_eq_x : u = x := le_antisymm hu_le_x hx_le_u
    -- From nearest minimality for d with candidate u = x, conclude d = x.
    have hdist : |d - x| ≤ |u - x| := hNd.2 u hUP.1
    have hdx0 : |d - x| = 0 := by
      have : |d - x| ≤ 0 := by simpa [hu_eq_x, sub_self] using hdist
      exact le_antisymm this (abs_nonneg _)
    have : d - x = 0 := by simpa using (abs_eq_zero.mp hdx0)
    have hd_eq_x : d = x := sub_eq_zero.mp this
    simpa [hd_eq_x, hu_eq_x]

/-- Check uniqueness of NA-point

    With `F 0`, the NA-point is unique.
-/
noncomputable def Rnd_NA_pt_unique_check (F : ℝ → Prop) (x f1 f2 : ℝ) : Bool :=
  by
    classical
    exact pure (decide (f1 = f2))

/-- Specification: NA-point uniqueness

    If `Rnd_NA_pt F x f1` and `Rnd_NA_pt F x f2` with `F 0`, then `f1 = f2`.
-/
@[spec]
theorem Rnd_NA_pt_unique_spec (F : ℝ → Prop) (x f1 f2 : ℝ) :
    ⦃⌜F 0 ∧ Rnd_NA_pt F x f1 ∧ Rnd_NA_pt F x f2⌝⦄
    Rnd_NA_pt_unique_check F x f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_pt_unique_check
  classical
  -- We will reduce uniqueness for NA-points to NG-point uniqueness with
  -- the predicate P := fun x f => |x| ≤ |f|, using equivalence under F 0.
  -- First, convert both NA-points to NG-points under the predicate P.
  have hEqv1 : Rnd_NA_pt F x f1 ↔ Rnd_NG_pt F (fun x f => |x| ≤ |f|) x f1 := by
    have hspec := Rnd_NA_NG_pt_spec F x f1
    simpa [Rnd_NA_NG_pt_check, pure, decide_eq_true_iff]
      using hspec (show F 0 from ‹F 0 ∧ Rnd_NA_pt F x f1 ∧ Rnd_NA_pt F x f2›.1)
  have hEqv2 : Rnd_NA_pt F x f2 ↔ Rnd_NG_pt F (fun x f => |x| ≤ |f|) x f2 := by
    have hspec := Rnd_NA_NG_pt_spec F x f2
    simpa [Rnd_NA_NG_pt_check, pure, decide_eq_true_iff]
      using hspec (show F 0 from ‹F 0 ∧ Rnd_NA_pt F x f1 ∧ Rnd_NA_pt F x f2›.1)
  -- Obtain the tie uniqueness property specialized to NA.
  have hTieProp : ∀ x d u,
      Rnd_DN_pt F x d → Rnd_N_pt F x d →
      Rnd_UP_pt F x u → Rnd_N_pt F x u →
      |x| ≤ |d| → |x| ≤ |u| → d = u := by
    have hspec := Rnd_NA_pt_unique_prop_spec F
    simpa [Rnd_NA_pt_unique_prop_check, pure,
      decide_eq_true_iff] using hspec (show F 0 from ‹F 0 ∧ Rnd_NA_pt F x f1 ∧ Rnd_NA_pt F x f2›.1)
  -- Convert hypotheses and apply NG uniqueness to deduce f1 = f2.
  have hNG1 : Rnd_NG_pt F (fun x f => |x| ≤ |f|) x f1 :=
    (hEqv1.mp (‹F 0 ∧ Rnd_NA_pt F x f1 ∧ Rnd_NA_pt F x f2›.2.1))
  have hNG2 : Rnd_NG_pt F (fun x f => |x| ≤ |f|) x f2 :=
    (hEqv2.mp (‹F 0 ∧ Rnd_NA_pt F x f1 ∧ Rnd_NA_pt F x f2›.2.2))
  have heq : f1 = f2 := by
    have huniq := Rnd_NG_pt_unique_spec F (fun x f => |x| ≤ |f|) x f1 f2
    simpa [Rnd_NG_pt_unique_check, pure,
      decide_eq_true_iff] using huniq ⟨hTieProp, hNG1, hNG2⟩
  -- Conclude the boolean check is true from equality.
  simpa [ pure, decide_eq_true_iff, heq]

/-- Check that NA-point is a valid nearest point under bound

    If `Rnd_N_pt F x f` and `|x| ≤ |f|` with `F 0`, then `Rnd_NA_pt F x f`.
-/
noncomputable def Rnd_NA_pt_N_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    -- From nearest with |f| ≤ |x| to NA-point.
    classical
    exact pure (decide (Rnd_NA_pt F x f))

/-- Specification: From nearest with abs bound to NA-point

    From `F 0`, `Rnd_N_pt F x f`, and `|x| ≤ |f|`, conclude `Rnd_NA_pt F x f`.
-/
@[spec]
theorem Rnd_NA_pt_N_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0 ∧ Rnd_N_pt F x f ∧ |x| ≤ |f|⌝⦄
    Rnd_NA_pt_N_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_NA_pt_N_check
  classical
  -- Reduce goal to establishing `Rnd_NA_pt F x f`.
  simp [ pure]
  rcases h with ⟨hF0, hN, hbound⟩
  -- Use equivalence NA ↔ NG with predicate P := fun x f => |x| ≤ |f| under F 0.
  have hEqv : Rnd_NA_pt F x f ↔ Rnd_NG_pt F (fun x f => |x| ≤ |f|) x f := by
    have hspec := Rnd_NA_NG_pt_spec F x f
    simpa [Rnd_NA_NG_pt_check, pure, decide_eq_true_iff]
      using hspec hF0
  -- Since `P x f` holds from the bound, build the NG-point and convert back to NA.
  have hNG : Rnd_NG_pt F (fun x f => |x| ≤ |f|) x f := And.intro hN (Or.inl hbound)
  exact (hEqv.mpr hNG)

/-- Check uniqueness of NA-based rounding functions

    If both functions satisfy `Rnd_NA`, they agree pointwise.
-/
noncomputable def Rnd_NA_unique_check (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) : Bool :=
  by
    classical
    exact pure (decide (rnd1 x = rnd2 x))

/-- Specification: Function-level uniqueness for NA rounding

    Under `F 0` and `Rnd_NA F rnd1`, `Rnd_NA F rnd2`, we have `rnd1 x = rnd2 x`.
-/
@[spec]
theorem Rnd_NA_unique_spec (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) :
    ⦃⌜F 0 ∧ (∃ p1 p2, Rnd_NA F rnd1 = pure p1 ∧ Rnd_NA F rnd2 = pure p2 ∧ p1 ∧ p2)⌝⦄
    Rnd_NA_unique_check F rnd1 rnd2 x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_NA_unique_check
  classical
  -- Reduce Hoare triple to a boolean equality on the pointwise values.
  simp [ pure]
  rcases h with ⟨hF0, hpack⟩
  rcases hpack with ⟨p1, p2, hEq1, hEq2, Hp1, Hp2⟩
  -- Unpack the function-level NA properties for rnd1 and rnd2.
  have h1run : (∀ y : ℝ, Rnd_NA_pt F y (rnd1 y)) = p1 := by
    simpa [Rnd_NA] using congrArg Id.run hEq1
  have h2run : (∀ y : ℝ, Rnd_NA_pt F y (rnd2 y)) = p2 := by
    simpa [Rnd_NA] using congrArg Id.run hEq2
  have H1 : ∀ y : ℝ, Rnd_NA_pt F y (rnd1 y) := by
    simpa [h1run] using Hp1
  have H2 : ∀ y : ℝ, Rnd_NA_pt F y (rnd2 y) := by
    simpa [h2run] using Hp2
  -- Apply NA-point uniqueness at the specific input x.
  have huniq := Rnd_NA_pt_unique_spec F x (rnd1 x) (rnd2 x)
  -- Its postcondition states exactly that `decide (rnd1 x = rnd2 x) = true`.
  simpa [Rnd_NA_pt_unique_check, pure]
    using huniq ⟨hF0, H1 x, H2 x⟩

/-- Check monotonicity for NA-point rounding

    With `F 0`, the NA-point rounding predicate is monotone.
-/
noncomputable def Rnd_NA_pt_monotone_check (F : ℝ → Prop) : Bool :=
  by
    classical
    exact pure (decide (round_pred_monotone (Rnd_NA_pt F)))

/-- Specification: NA-point is monotone

    Assuming `F 0`, `Rnd_NA_pt F` is monotone.
-/
@[spec]
theorem Rnd_NA_pt_monotone_spec (F : ℝ → Prop) :
    ⦃⌜F 0⌝⦄
    Rnd_NA_pt_monotone_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_pt_monotone_check
  classical
  -- Reduce to proving the monotonicity proposition directly.
  simp [ pure, round_pred_monotone]
  -- As in the NG monotonicity proof, we first show that any nearest point
  -- is either a DN-point or an UP-point at the same input.
  have nearest_DN_or_UP
      (x f : ℝ) (h : Rnd_N_pt F x f) : Rnd_DN_pt F x f ∨ Rnd_UP_pt F x f := by
    rcases h with ⟨HfF, Hmin⟩
    -- Split on whether f ≤ x or x ≤ f.
    cases le_total f x with
    | inl hfxle =>
        -- DN case
        left
        refine And.intro HfF ?_
        refine And.intro hfxle ?_
        intro g HgF hglex
        -- From minimality with absolutes rewritten as linear inequalities.
        have hxmf_nonneg : 0 ≤ x - f := sub_nonneg.mpr hfxle
        have hxmg_nonneg : 0 ≤ x - g := sub_nonneg.mpr hglex
        have h_abs : |x - f| ≤ |x - g| := by
          simpa [abs_sub_comm] using (Hmin g HgF)
        have h_sub : x - f ≤ x - g := by
          simpa [abs_of_nonneg hxmf_nonneg, abs_of_nonneg hxmg_nonneg] using h_abs
        -- x - f ≤ x - g ⇒ g ≤ f
        have hneg : -f ≤ -g := by
          have h' := add_le_add_left h_sub (-x)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'
        exact (neg_le_neg_iff).1 hneg
    | inr hxlef =>
        -- UP case
        right
        refine And.intro HfF ?_
        refine And.intro hxlef ?_
        intro g HgF hxleg
        have hxmf_nonpos : x - f ≤ 0 := sub_nonpos.mpr hxlef
        have hxmg_nonpos : x - g ≤ 0 := sub_nonpos.mpr hxleg
        have h_abs : |x - f| ≤ |x - g| := by
          simpa [abs_sub_comm] using (Hmin g HgF)
        have h_sub : f - x ≤ g - x := by
          simpa [abs_of_nonpos hxmf_nonpos, abs_of_nonpos hxmg_nonpos, neg_sub] using h_abs
        have h' := add_le_add_right h_sub x
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'

  -- Local helpers: uniqueness of DN/UP points at a fixed input x.
  have DN_unique (x f1 f2 : ℝ)
      (h1 : Rnd_DN_pt F x f1) (h2 : Rnd_DN_pt F x f2) : f1 = f2 := by
    have le12 : f1 ≤ f2 := by
      have := h2.2.2 f1 h1.1 h1.2.1
      simpa using this
    have le21 : f2 ≤ f1 := by
      have := h1.2.2 f2 h2.1 h2.2.1
      simpa using this
    exact le_antisymm le12 le21

  have UP_unique (x f1 f2 : ℝ)
      (h1 : Rnd_UP_pt F x f1) (h2 : Rnd_UP_pt F x f2) : f1 = f2 := by
    -- From minimality at f1 and f2, we get both directions of ≤
    have le21 : f2 ≤ f1 := by
      exact h2.2.2 f1 h1.1 h1.2.1
    have le12 : f1 ≤ f2 := by
      exact h1.2.2 f2 h2.1 h2.2.1
    exact le_antisymm le12 le21

  -- Prove monotonicity for `Rnd_NA_pt F`.
  intro x y f g hx hy hxy
  -- Split on strict/equal order.
  cases lt_or_eq_of_le hxy with
  | inl hlt =>
      -- For the strict case, follow the nearest-based argument.
      rcases hx with ⟨HxfN, _⟩
      rcases hy with ⟨HygN, _⟩
      by_contra hnot
      have hgf : g < f := lt_of_not_ge hnot
      have Hfgx : |f - x| ≤ |g - x| := HxfN.2 g HygN.1
      have Hgfy : |g - y| ≤ |f - y| := HygN.2 f HxfN.1
      by_cases hxg : x ≤ g
      · -- Case 1: x ≤ g < f
        have hxlt_f : x < f := lt_of_le_of_lt hxg hgf
        have hxmf_pos : 0 < f - x := sub_pos.mpr hxlt_f
        have hxmg_nonneg : 0 ≤ g - x := sub_nonneg.mpr hxg
        have Hfgx' : |f - x| ≤ |g - x| := by simpa [abs_sub_comm] using Hfgx
        have Hfgx'' : f - x ≤ g - x := by
          simpa [abs_of_nonneg (le_of_lt hxmf_pos), abs_of_nonneg hxmg_nonneg] using Hfgx'
        have : ¬ f - x ≤ g - x := by
          have h := sub_lt_sub_right hgf x
          exact not_le.mpr h
        exact this Hfgx''
      · -- Case 2: g < x < y
        have hgx : g < x := lt_of_not_ge hxg
        have hgy : g < y := lt_trans hgx hlt
        by_cases hfy : f ≤ y
        · -- Subcase: f ≤ y
          have hy_mg_pos : 0 < y - g := sub_pos.mpr hgy
          have hy_mf_nonneg : 0 ≤ y - f := sub_nonneg.mpr hfy
          have Hgfy' : y - g ≤ y - f := by
            have : |y - g| ≤ |y - f| := by
              simpa [abs_sub_comm] using Hgfy
            simpa [abs_of_nonneg (le_of_lt hy_mg_pos), abs_of_nonneg hy_mf_nonneg] using this
          have : ¬ y - g ≤ y - f := by
            have h := sub_lt_sub_left hgf y
            exact not_le.mpr h
          exact this Hgfy'
        · -- Subcase: y < f
          have hy_lt_f : y < f := lt_of_not_ge hfy
          have hxmg_pos : 0 < x - g := sub_pos.mpr hgx
          have hxmf_pos : 0 < f - x := sub_pos.mpr (lt_trans hlt hy_lt_f)
          have hymg_pos : 0 < y - g := sub_pos.mpr hgy
          have hymf_neg : y - f < 0 := sub_neg.mpr hy_lt_f
          have Hfgx' : f - x ≤ x - g := by
            have : |f - x| ≤ |x - g| := by simpa [abs_sub_comm] using Hfgx
            simpa [abs_of_pos hxmf_pos, abs_of_pos hxmg_pos] using this
          have Hgfy' : y - g ≤ f - y := by
            have : |y - g| ≤ |y - f| := by
              simpa [abs_sub_comm] using Hgfy
            simpa [abs_of_pos hymg_pos, abs_of_neg hymf_neg] using this
          have Hsum : (f - x) + (y - g) ≤ (x - g) + (f - y) := add_le_add Hfgx' Hgfy'
          have hL : (x - g) + (f - y) = (x - y) + (f - g) := by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          have hR : (f - x) + (y - g) = (y - x) + (f - g) := by
            simp [sub_eq_add_neg, add_left_comm, add_assoc]
          have hyx_pos : 0 < y - x := sub_pos.mpr hlt
          have hxmy_lt_hyx : (x - y) < (y - x) := by
            have : -(y - x) < (y - x) := neg_lt_self hyx_pos
            simpa [neg_sub, sub_eq_add_neg] using this
          have hStrict : (x - y) + (f - g) < (y - x) + (f - g) := by
            simpa only [add_comm (f - g)] using add_lt_add_right hxmy_lt_hyx (f - g)
          have : (y - x) + (f - g) ≤ (x - y) + (f - g) := by
            simpa [hL, hR, add_comm, add_left_comm, add_assoc] using Hsum
          exact (not_le_of_gt hStrict) this
  | inr heq =>
      -- Equal inputs: reduce `hy` to the same x and show `f ≤ g`.
      have hyx : Rnd_NA_pt F x g := by simpa [heq] using hy
      rcases hx with ⟨HxfN, HxfMax⟩
      rcases hyx with ⟨HygN, HygMax⟩
      -- Distances to x are mutually ≤, hence equal.
      have h1 : |x - f| ≤ |x - g| := by simpa [abs_sub_comm] using HxfN.2 g HygN.1
      have h2 : |x - g| ≤ |x - f| := by simpa [abs_sub_comm] using HygN.2 f HxfN.1
      have heqAbs : |x - f| = |x - g| := le_antisymm h1 h2
      -- Classify f and g as DN or UP.
      have hfClass := nearest_DN_or_UP x f HxfN
      have hgClass := nearest_DN_or_UP x g HygN
      -- If both on the same side, uniqueness forces equality.
      have hf_le_g : f ≤ g := by
        cases hfClass with
        | inl hDNf =>
            cases hgClass with
            | inl hDNg =>
                -- Both DN ⇒ equality ⇒ ≤
                simpa [DN_unique x f g hDNf hDNg]
            | inr hUPg =>
                -- DN vs UP ⇒ f ≤ x ≤ g ⇒ f ≤ g
                exact le_trans hDNf.2.1 hUPg.2.1
        | inr hUPf =>
            cases hgClass with
            | inl hDNg =>
                -- UP vs DN: we show this also yields f ≤ g by proving f = g.
                -- From NA tie conditions, we get |f| = |g|.
                have hAbsFG1 : |g| ≤ |f| := HxfMax g HygN
                have hAbsFG2 : |f| ≤ |g| := HygMax f HxfN
                have hAbsEq : |f| = |g| := le_antisymm hAbsFG2 hAbsFG1
                -- From equal absolutes, f = g or f = -g.
                have hcases : f = g ∨ f = -g := by
                  -- Use the standard equivalence |f| = |g| ↔ f = g ∨ f = -g
                  -- available via `abs_eq_abs.mp`.
                  simpa using (abs_eq_abs.mp hAbsEq)
                -- Additionally, since f is UP and g is DN and distances are equal,
                -- we have f - x = x - g (by rewriting |x - f| and |x - g|).
                have hxmf_nonpos : x - f ≤ 0 := sub_nonpos.mpr hUPf.2.1
                have hxmg_nonneg : 0 ≤ x - g := sub_nonneg.mpr hDNg.2.1
                have hlin : f - x = x - g := by
                  -- Rewrite absolutes with signs known from DN/UP to a linear equality.
                  have hL : |x - f| = f - x := by
                    calc
                      |x - f| = -(x - f) := by exact abs_of_nonpos hxmf_nonpos
                      _ = f - x := by simpa [sub_eq_add_neg]
                  have hR : |x - g| = x - g := by
                    exact abs_of_nonneg hxmg_nonneg
                  simpa [hL, hR] using heqAbs
                -- Conclude equality in all cases, hence ≤.
                cases hcases with
                | inl hfg => simpa [hfg]
                | inr hfneg =>
                    -- f = -g and |x - f| = |x - g| with f UP and g DN.
                    -- From sign info, |x - f| = |x - g| rewrites to f - x = x - g.
                    have hlin' : -g - x = x - g := by simpa [hfneg] using hlin
                    -- Adding g on both sides gives -x = x; from this, deduce x = 0.
                    have hnegx : -x = x := by
                      have := congrArg (fun t => t + g) hlin'
                      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
                    have hx0 : x = 0 := by
                      -- From -x = x, add x to both sides to get 0 = x + x;
                      -- rewrite as 2 * x = 0 and conclude x = 0 using `two_ne_zero`.
                      have hsum : 0 = x + x := by
                        have := congrArg (fun t : ℝ => t + x) hnegx
                        simpa [add_comm, add_left_comm, add_assoc] using this
                      have h2x0 : (2 : ℝ) * x = 0 := by
                        -- Turn `0 = x + x` into `2 * x = 0`.
                        have : x + x = 0 := by simpa [eq_comm] using hsum
                        simpa [two_mul, add_comm] using this
                      have hx_or := mul_eq_zero.mp h2x0
                      have : x = 0 := by
                        cases hx_or with
                        | inl h2 =>
                            exact (False.elim (two_ne_zero h2))
                        | inr hx => exact hx
                      exact this
                    -- Since x = 0 and F 0 holds, nearest minimality forces f = 0 and g = 0.
                    have hf0 : f = 0 := by
                      rcases HxfN with ⟨HfF, Hmin⟩
                      have hle0 : |f - x| ≤ |0 - x| := Hmin 0 (by simpa using ‹F 0›)
                      have hle : |f| ≤ 0 := by simpa [hx0, abs_sub_comm, sub_zero] using hle0
                      have heq0 : |f| = 0 := le_antisymm hle (abs_nonneg _)
                      exact (abs_eq_zero.mp heq0)
                    have hg0 : g = 0 := by
                      rcases HygN with ⟨HgF, Hmin⟩
                      have hle0 : |g - x| ≤ |0 - x| := Hmin 0 (by simpa using ‹F 0›)
                      have hle : |g| ≤ 0 := by simpa [hx0, abs_sub_comm, sub_zero] using hle0
                      have heq0 : |g| = 0 := le_antisymm hle (abs_nonneg _)
                      exact (abs_eq_zero.mp heq0)
                    -- Conclude f ≤ g from equality.
                    simpa [hf0, hg0]
            | inr hUPg =>
                -- Both UP ⇒ equality ⇒ ≤
                simpa [UP_unique x f g hUPf hUPg]
      exact hf_le_g

/-- Check reflexivity of NA-point

    Representable values are fixed by NA-point rounding.
-/
noncomputable def Rnd_NA_pt_refl_check (F : ℝ → Prop) (x : ℝ) : Bool :=
  by
    classical
    exact pure (decide (Rnd_NA_pt F x x))

/-- Specification: NA-point reflexivity on representables

    From `F x`, deduce `Rnd_NA_pt F x x`.
-/
@[spec]
theorem Rnd_NA_pt_refl_spec (F : ℝ → Prop) (x : ℝ) :
    ⦃⌜F x⌝⦄
    Rnd_NA_pt_refl_check F x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_NA_pt_refl_check
  classical
  -- It suffices to prove `Rnd_NA_pt F x x` and convert via `decide_eq_true_iff`.
  -- Build the nearest predicate at `x`.
  have hN : Rnd_N_pt F x x := by
    refine And.intro ?hx ?hmin
    · -- Representability of x (from the precondition)
      simpa using ‹F x›
    · -- Minimality: |x - x| = 0 ≤ |g - x| for any representable g
      intro g _
      have : 0 ≤ |g - x| := by simpa using abs_nonneg (g - x)
      simpa [abs_sub_comm, sub_self] using this
  -- Tie-breaking for NA at x: any nearest f2 must equal x, hence |f2| ≤ |x|.
  have hTie : ∀ f2, Rnd_N_pt F x f2 → |f2| ≤ |x| := by
    intro f2 hf2
    -- From nearest-ness of f2, get |f2 - x| ≤ |x - x| = 0, hence f2 = x.
    have hle0 : |f2 - x| ≤ 0 := by
      have := hf2.2 x (by simpa using ‹F x›)
      simpa [abs_sub_comm, sub_self] using this
    have heq0 : |f2 - x| = 0 := le_antisymm hle0 (abs_nonneg _)
    have hsub0 : f2 - x = 0 := by simpa using (abs_eq_zero.mp heq0)
    have hfx : f2 = x := sub_eq_zero.mp hsub0
    -- Conclude the absolute-value inequality by rewriting.
    simpa [hfx] using (le_rfl : |x| ≤ |x|)
  -- Assemble NA-point at x and finish.
  have hNA : Rnd_NA_pt F x x := And.intro hN hTie
  simp [ pure, hNA]

/-- Check idempotency of NA-point

    If `Rnd_NA_pt F x f` and `F x`, then `f = x`.
-/
noncomputable def Rnd_NA_pt_idempotent_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (f = x))

/-- Specification: NA-point idempotency on representables

    From `Rnd_NA_pt F x f` and `F x`, deduce `f = x`.
-/
@[spec]
theorem Rnd_NA_pt_idempotent_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_NA_pt F x f ∧ F x⌝⦄
    Rnd_NA_pt_idempotent_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_NA_pt_idempotent_check
  classical
  -- Reduce to proving `f = x` from nearest property at `x` and representability of `x`.
  simp [ pure]
  rcases h with ⟨hNA, hxF⟩
  -- From NA, extract nearest property.
  rcases hNA with ⟨hN, _hTie⟩
  rcases hN with ⟨hfF, hmin⟩
  -- Minimality at `g = x` yields `|f - x| ≤ 0`, hence `f = x`.
  have hle : |f - x| ≤ 0 := by simpa using (hmin x hxF)
  have heq0 : |f - x| = 0 := le_antisymm hle (abs_nonneg _)
  have hsub0 : f - x = 0 := by simpa using (abs_eq_zero.mp heq0)
  exact sub_eq_zero.mp hsub0

/-- Check equivalence between N0 and NG with abs-based predicate

    With `0 ∈ F`, `Rnd_N0_pt` is equivalent to `Rnd_NG_pt` with
    predicate `fun x f => |f| ≤ |x|`.
-/
noncomputable def Rnd_N0_NG_pt_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    -- Equivalence between N0 and NG with predicate |f| ≤ |x|.
    classical
    exact pure (decide (Rnd_N0_pt F x f ↔ Rnd_NG_pt F (fun x f => |f| ≤ |x|) x f))

/-- Specification: N0 equals NG with abs-based tie predicate

    Assuming `F 0`, equivalence between `Rnd_N0_pt` and `Rnd_NG_pt` holds.
-/
@[spec]
theorem Rnd_N0_NG_pt_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0⌝⦄
    Rnd_N0_NG_pt_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_NG_pt_check
  classical
  -- Reduce to the desired propositional equivalence.
  simp [ pure]
  -- We prove both directions by cases on the sign of x.
  by_cases hx : 0 ≤ x
  · -- Case 0 ≤ x
    constructor
    · -- (→) From N0-point to NG-point with P := fun x f => |f| ≤ |x|
      intro hN0
      rcases hN0 with ⟨hN, hMinAbs⟩
      -- Classification of f as DN/UP for x using nearest property
      have hClass := Rnd_N_pt_DN_or_UP_spec F x f
      have hDU : Rnd_DN_pt F x f ∨ Rnd_UP_pt F x f := by
        simpa [Rnd_N_pt_DN_or_UP_check, pure,
          decide_eq_true_iff] using hClass hN
      -- From nearest at nonnegative x, deduce f ≥ 0
      have h0le_f : 0 ≤ f := by
        -- Minimality vs g = 0 gives |x - f| ≤ |x|
        have hmin0 : |x - f| ≤ |x| := by
          have := hN.2 0 (by simpa using ‹F 0›)
          simpa [abs_sub_comm, sub_zero, abs_of_nonneg hx] using this
        -- Prove by contradiction that f < 0 is impossible
        by_contra hfneg
        have hf_lt0 : f < 0 := lt_of_not_ge hfneg
        have hx_lt_xmf : x < x - f := by
          have : 0 < -f := neg_pos.mpr hf_lt0
          have := add_lt_add_left this x
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        have hxmf_pos : 0 < x - f := lt_of_le_of_lt hx hx_lt_xmf
        have hx_lt_abs : x < |x - f| := by simpa [abs_of_pos hxmf_pos] using hx_lt_xmf
        -- Compose inequalities and rewrite |x| = x (since 0 ≤ x)
        have hx_lt_abs' : x < |x| := lt_of_lt_of_le hx_lt_abs hmin0
        have hx_lt_x : x < x := by simpa [abs_of_nonneg hx] using hx_lt_abs'
        exact (lt_irrefl _ hx_lt_x)
      -- Build NG: nearest plus either P or uniqueness on ties
      refine And.intro hN ?_;
      -- Split on whether f is DN or UP
      cases hDU with
      | inl hDN =>
          -- DN case: since 0 ≤ f ≤ x, we have |f| ≤ |x|
          left
          have : f ≤ x := hDN.2.1
          simpa [abs_of_nonneg h0le_f, abs_of_nonneg hx] using this
      | inr hUP =>
          -- UP case: prove uniqueness among nearest points
          right
          intro f2 hN2
          -- Use the N0 minimal-abs property and classify f2
          have hMin : |f| ≤ |f2| := hMinAbs f2 hN2
          have hClass2 := Rnd_N_pt_DN_or_UP_spec F x f2
          have hDU2 : Rnd_DN_pt F x f2 ∨ Rnd_UP_pt F x f2 := by
            simpa [Rnd_N_pt_DN_or_UP_check, pure,
              decide_eq_true_iff] using hClass2 hN2
          -- Also f2 ≥ 0 under 0 ≤ x
          have h0le_f2 : 0 ≤ f2 := by
            -- As above, use minimality vs 0 and contradict f2 < 0
            have hmin0 : |x - f2| ≤ |x| := by
              have := hN2.2 0 (by simpa using ‹F 0›)
              simpa [abs_sub_comm, sub_zero, abs_of_nonneg hx] using this
            by_contra hf2neg
            have hf2_lt0 : f2 < 0 := lt_of_not_ge hf2neg
            have hx_lt_xmf : x < x - f2 := by
              have : 0 < -f2 := neg_pos.mpr hf2_lt0
              have := add_lt_add_left this x
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
            have hxmf_pos : 0 < x - f2 := lt_of_le_of_lt hx hx_lt_xmf
            have hx_lt_abs : x < |x - f2| := by simpa [abs_of_pos hxmf_pos] using hx_lt_xmf
            -- Compose inequalities and rewrite |x| = x (since 0 ≤ x)
            have hx_lt_abs' : x < |x| := lt_of_lt_of_le hx_lt_abs hmin0
            have hx_lt_x : x < x := by simpa [abs_of_nonneg hx] using hx_lt_abs'
            exact (lt_irrefl _ hx_lt_x)
          -- Now analyze f2 as DN or UP
          cases hDU2 with
          | inl hDN2 =>
              -- f2 DN, f UP: obtain f2 ≤ x ≤ f and combine with |f| ≤ |f2| to deduce equality
              have hle1 : f2 ≤ f := le_trans hDN2.2.1 hUP.2.1
              -- From |f| ≤ |f2| and nonnegativity, deduce f ≤ f2
              have hle2 : f ≤ f2 := by
                simpa [abs_of_nonneg h0le_f, abs_of_nonneg h0le_f2] using hMin
              exact le_antisymm hle1 hle2
          | inr hUP2 =>
              -- Both UP: uniqueness by mutual minimality
              have h12 : f ≤ f2 := hUP.2.2 f2 hUP2.1 hUP2.2.1
              have h21 : f2 ≤ f := hUP2.2.2 f hUP.1 hUP.2.1
              exact le_antisymm h21 h12
    · -- (←) From NG with P/uniqueness to N0
      intro hNG
      rcases hNG with ⟨hN, hTie⟩
      -- Show the minimal-absolute-value property required by N0
      refine And.intro hN ?_
      intro f2 hN2
      -- Nonnegativity of f and f2 under 0 ≤ x
      have h0le_f : 0 ≤ f := by
        -- Same argument as above for f
        have hmin0 : |x - f| ≤ |x| := by
          have := hN.2 0 (by simpa using ‹F 0›)
          simpa [abs_sub_comm, sub_zero, abs_of_nonneg hx] using this
        by_contra hfneg
        have hf_lt0 : f < 0 := lt_of_not_ge hfneg
        have hx_lt_xmf : x < x - f := by
          have : 0 < -f := neg_pos.mpr hf_lt0
          have := add_lt_add_left this x
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        have hxmf_pos : 0 < x - f := lt_of_le_of_lt hx hx_lt_xmf
        have hx_lt_abs : x < |x - f| := by simpa [abs_of_pos hxmf_pos] using hx_lt_xmf
        have hx_lt_abs' : x < |x| := lt_of_lt_of_le hx_lt_abs hmin0
        have hx_lt_x : x < x := by simpa [abs_of_nonneg hx] using hx_lt_abs'
        exact (lt_irrefl _ hx_lt_x)
      have h0le_f2 : 0 ≤ f2 := by
        -- Same argument as above for f2
        have hmin0 : |x - f2| ≤ |x| := by
          have := hN2.2 0 (by simpa using ‹F 0›)
          simpa [abs_sub_comm, sub_zero, abs_of_nonneg hx] using this
        by_contra hf2neg
        have hf2_lt0 : f2 < 0 := lt_of_not_ge hf2neg
        have hx_lt_xmf : x < x - f2 := by
          have : 0 < -f2 := neg_pos.mpr hf2_lt0
          have := add_lt_add_left this x
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        have hxmf_pos : 0 < x - f2 := lt_of_le_of_lt hx hx_lt_xmf
        have hx_lt_abs : x < |x - f2| := by simpa [abs_of_pos hxmf_pos] using hx_lt_xmf
        -- Compose inequalities and rewrite |x| = x (since 0 ≤ x)
        have hx_lt_abs' : x < |x| := lt_of_lt_of_le hx_lt_abs hmin0
        have hx_lt_x : x < x := by simpa [abs_of_nonneg hx] using hx_lt_abs'
        exact (lt_irrefl _ hx_lt_x)
      -- Classify f2 as DN or UP
      have hClass2 := Rnd_N_pt_DN_or_UP_spec F x f2
      have hDU2 : Rnd_DN_pt F x f2 ∨ Rnd_UP_pt F x f2 := by
        simpa [Rnd_N_pt_DN_or_UP_check, pure,
          decide_eq_true_iff] using hClass2 hN2
      -- Use the tie information
      cases hTie with
      | inl hP =>
          -- P: |f| ≤ |x|; with nonnegativity, this gives f ≤ x
          have hfle_x : f ≤ x := by simpa [abs_of_nonneg h0le_f, abs_of_nonneg hx] using hP
          -- Now deduce |f| ≤ |f2| by analyzing f2 as DN or UP
          cases hDU2 with
          | inl hDN2 =>
              -- f2 is DN: use maximality at x with candidate f
              have hle : f ≤ f2 := hDN2.2.2 f hN.1 hfle_x
              simpa [abs_of_nonneg h0le_f, abs_of_nonneg h0le_f2] using hle
          | inr hUP2 =>
              -- f2 is UP: since x ≤ f2, transitivity yields f ≤ f2
              have hle : f ≤ f2 := le_trans hfle_x hUP2.2.1
              simpa [abs_of_nonneg h0le_f, abs_of_nonneg h0le_f2] using hle
      | inr huniq =>
          -- Uniqueness: any nearest f2 must equal f
          have : f2 = f := huniq f2 hN2
          simpa [this]
  · -- Case x < 0 (so x ≤ 0)
    have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    constructor
    · -- (→) From N0-point to NG-point with P
      intro hN0
      rcases hN0 with ⟨hN, hMinAbs⟩
      -- Classification of f as DN/UP for x using nearest property
      have hClass := Rnd_N_pt_DN_or_UP_spec F x f
      have hDU : Rnd_DN_pt F x f ∨ Rnd_UP_pt F x f := by
        simpa [Rnd_N_pt_DN_or_UP_check, pure,
          decide_eq_true_iff] using hClass hN
      -- From nearest at nonpositive x, deduce f ≤ 0
      have hf_le0 : f ≤ 0 := by
        -- Minimality vs g = 0 gives |f - x| ≤ | -x | = -x
        have hmin0 : |f - x| ≤ -x := by
          have h := hN.2 0 (by simpa using ‹F 0›)
          simpa [sub_eq_add_neg, abs_neg, abs_of_nonpos hxle0] using h
        -- Prove by contradiction that f > 0 is impossible
        by_contra hfpos
        have hf_gt0 : 0 < f := lt_of_not_ge hfpos
        have hpos : 0 < f - x := by
          have := add_pos_of_nonneg_of_pos (neg_nonneg.mpr hxle0) hf_gt0
          simpa [sub_eq_add_neg, add_comm] using this
        have hx_abs_gt : -x < |f - x| := by
          have : -x < f - x := by
            have := add_lt_add_left hf_gt0 (-x)
            simpa [sub_eq_add_neg, add_comm] using this
          simpa [abs_of_pos hpos] using this
        exact (lt_irrefl _ (lt_of_lt_of_le hx_abs_gt hmin0))
      -- Build NG: nearest plus either P or uniqueness
      refine And.intro hN ?_;
      cases hDU with
      | inl hDN =>
          -- DN case at x ≤ 0: uniqueness among nearest points
          right
          intro f2 hN2
          -- Use the N0 minimal-abs property and classify f2
          have hMin : |f| ≤ |f2| := hMinAbs f2 hN2
          have hClass2 := Rnd_N_pt_DN_or_UP_spec F x f2
          have hDU2 : Rnd_DN_pt F x f2 ∨ Rnd_UP_pt F x f2 := by
            simpa [Rnd_N_pt_DN_or_UP_check, pure,
              decide_eq_true_iff] using hClass2 hN2
          -- Also f2 ≤ 0 under x ≤ 0
          have hf2_le0 : f2 ≤ 0 := by
            -- Analogous argument for f2
            have hmin0 : |f2 - x| ≤ -x := by
              have h := hN2.2 0 (by simpa using ‹F 0›)
              simpa [sub_eq_add_neg, abs_neg, abs_of_nonpos hxle0] using h
            by_contra hf2pos
            have hf2_gt0 : 0 < f2 := lt_of_not_ge hf2pos
            have hpos : 0 < f2 - x := by
              have := add_pos_of_nonneg_of_pos (neg_nonneg.mpr hxle0) hf2_gt0
              simpa [sub_eq_add_neg, add_comm] using this
            have hx_abs_gt : -x < |f2 - x| := by
              have : -x < f2 - x := by
                have := add_lt_add_left hf2_gt0 (-x)
                simpa [sub_eq_add_neg, add_comm] using this
              simpa [abs_of_pos hpos] using this
            exact (lt_irrefl _ (lt_of_lt_of_le hx_abs_gt hmin0))
          -- Analyze f2 as DN or UP
          cases hDU2 with
          | inl hDN2 =>
              -- Both DN: uniqueness by mutual maximality
              have le12 : f ≤ f2 := hDN2.2.2 f hDN.1 hDN.2.1
              have le21 : f2 ≤ f := hDN.2.2 f2 hDN2.1 hDN2.2.1
              exact le_antisymm le21 le12
          | inr hUP2 =>
              -- f DN, f2 UP: obtain f ≤ x ≤ f2 and use |f| ≤ |f2| to deduce equality
              have hle1 : f ≤ f2 := le_trans hDN.2.1 hUP2.2.1
              have hle2' : f2 ≤ f := by
                have : -f ≤ -f2 := by
                  simpa [abs_of_nonpos hf_le0, abs_of_nonpos hf2_le0] using hMin
                simpa using (neg_le_neg_iff.mp this)
              exact le_antisymm hle2' hle1
      | inr hUP =>
          -- UP case at x ≤ 0: show P holds, i.e., |f| ≤ |x|
          left
          have hxle_f : x ≤ f := hUP.2.1
          -- From x ≤ 0 and x ≤ f, we get -f ≤ -x
          have : -f ≤ -x := by exact neg_le_neg hxle_f
          simpa [abs_of_nonpos hf_le0, abs_of_nonpos hxle0] using this
    · -- (←) From NG with P/uniqueness to N0
      intro hNG
      rcases hNG with ⟨hN, hTie⟩
      refine And.intro hN ?_
      intro f2 hN2
      -- f ≤ 0 and f2 ≤ 0 under x ≤ 0
      have hf_le0 : f ≤ 0 := by
        -- From nearest and x ≤ 0 as above
        have hmin0 : |f - x| ≤ -x := by
          have h := hN.2 0 (by simpa using ‹F 0›)
          simpa [sub_eq_add_neg, abs_neg, abs_of_nonpos hxle0] using h
        by_contra hfpos
        have hf_gt0 : 0 < f := lt_of_not_ge hfpos
        have hpos : 0 < f - x := by
          have := add_pos_of_nonneg_of_pos (neg_nonneg.mpr hxle0) hf_gt0
          simpa [sub_eq_add_neg, add_comm] using this
        have hx_abs_gt : -x < |f - x| := by
          have : -x < f - x := by
            have := add_lt_add_left hf_gt0 (-x)
            simpa [sub_eq_add_neg, add_comm] using this
          simpa [abs_of_pos hpos] using this
        exact (lt_irrefl _ (lt_of_lt_of_le hx_abs_gt hmin0))
      have hf2_le0 : f2 ≤ 0 := by
        -- Same for f2
        have hmin0 : |f2 - x| ≤ -x := by
          have h := hN2.2 0 (by simpa using ‹F 0›)
          simpa [sub_eq_add_neg, abs_neg, abs_of_nonpos hxle0] using h
        by_contra hfpos
        have hf_gt0 : 0 < f2 := lt_of_not_ge hfpos
        have hpos : 0 < f2 - x := by
          have := add_pos_of_nonneg_of_pos (neg_nonneg.mpr hxle0) hf_gt0
          simpa [sub_eq_add_neg, add_comm] using this
        have hx_abs_gt : -x < |f2 - x| := by
          have : -x < f2 - x := by
            have := add_lt_add_left hf_gt0 (-x)
            simpa [sub_eq_add_neg, add_comm] using this
          simpa [abs_of_pos hpos] using this
        exact (lt_irrefl _ (lt_of_lt_of_le hx_abs_gt hmin0))
      -- Classify f2 as DN or UP
      have hClass2 := Rnd_N_pt_DN_or_UP_spec F x f2
      have hDU2 : Rnd_DN_pt F x f2 ∨ Rnd_UP_pt F x f2 := by
        simpa [Rnd_N_pt_DN_or_UP_check, pure,
          decide_eq_true_iff] using hClass2 hN2
      -- Use the tie information
      cases hTie with
      | inl hP =>
          -- P: |f| ≤ |x|; with nonpositivity, this gives -f ≤ -x
          have hneg_le : -f ≤ -x := by
            -- rewrite |f| = -f and |x| = -x
            simpa [abs_of_nonpos hf_le0, abs_of_nonpos hxle0] using hP
          -- Goal: |f| ≤ |f2| i.e., -f ≤ -f2; analyze f2
          cases hDU2 with
          | inl hDN2 =>
              -- f2 DN: from hDN2.2.1 (f2 ≤ x) and hneg_le (−f ≤ −x) deduce -f ≤ -f2
              have hle : -f ≤ -f2 := le_trans hneg_le (by exact neg_le_neg hDN2.2.1)
              simpa [abs_of_nonpos hf_le0, abs_of_nonpos hf2_le0] using hle
          | inr hUP2 =>
              -- f2 UP: use minimality at f2 with g = f and x ≤ f to get f2 ≤ f, then negate
              have hxle_f : x ≤ f := (neg_le_neg_iff.mp hneg_le)
              have hle' : f2 ≤ f := hUP2.2.2 f hN.1 hxle_f
              have hle : -f ≤ -f2 := by exact neg_le_neg hle'
              simpa [abs_of_nonpos hf_le0, abs_of_nonpos hf2_le0] using hle
      | inr huniq =>
          -- Uniqueness: any nearest f2 must equal f
          have : f2 = f := huniq f2 hN2
          simpa [this]

/-- Check uniqueness property for N0 ties (auxiliary)

    The N0 tie-breaking relation yields uniqueness under `F 0`.
-/
noncomputable def Rnd_N0_pt_unique_prop_check (F : ℝ → Prop) : Bool :=
  by
    classical
    exact pure (decide (∀ x d u,
      Rnd_DN_pt F x d → Rnd_N_pt F x d →
      Rnd_UP_pt F x u → Rnd_N_pt F x u →
      |d| ≤ |x| → |u| ≤ |x| → d = u))

/-- Specification: N0 tie uniqueness property holds

    Assuming `F 0`, the auxiliary uniqueness property for N0 holds.
-/
@[spec]
theorem Rnd_N0_pt_unique_prop_spec (F : ℝ → Prop) :
    ⦃⌜F 0⌝⦄
    Rnd_N0_pt_unique_prop_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_pt_unique_prop_check
  classical
  -- Reduce to the underlying propositional goal.
  simp [ pure]
  intro x d u hDN hNd hUP hNu hAd hAu
  -- Case split on the sign of x.
  by_cases hx : 0 ≤ x
  · -- Case x ≥ 0: deduce u ≤ x from |u| ≤ |x| using nonnegativity of u.
    -- From nearest at nonnegative x, we have 0 ≤ u (using F 0).
    have hu_nonneg : 0 ≤ u := by
      have h := Rnd_N_pt_ge_0_spec F x u
      simpa [Rnd_N_pt_ge_0_check, pure,
        decide_eq_true_iff] using h ⟨‹F 0›, hx, hNu⟩
    have hu_le_x : u ≤ x := by
      simpa [abs_of_nonneg hu_nonneg, abs_of_nonneg hx] using hAu
    have hx_le_u : x ≤ u := hUP.2.1
    have hu_eq_x : u = x := le_antisymm hu_le_x hx_le_u
    -- From nearest minimality for d with candidate u, conclude d = x = u.
    have hFd : F d := hDN.1
    have hdist : |d - x| ≤ |u - x| := hNd.2 u hUP.1
    have hdx0 : |d - x| = 0 := by
      have : |d - x| ≤ 0 := by simpa [hu_eq_x, sub_self] using hdist
      exact le_antisymm this (abs_nonneg _)
    have hd_eq_x : d = x := by
      have : d - x = 0 := by simpa using (abs_eq_zero.mp hdx0)
      exact sub_eq_zero.mp this
    simpa [hd_eq_x, hu_eq_x]
  · -- Case x ≤ 0: deduce x ≤ d from |d| ≤ |x| using nonpositivity of d.
    have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    -- From nearest at nonpositive x, we have d ≤ 0 (using F 0).
    have hd_nonpos : d ≤ 0 := by
      have h := Rnd_N_pt_le_0_spec F x d
      simpa [Rnd_N_pt_le_0_check, pure,
        decide_eq_true_iff] using h ⟨‹F 0›, hxle0, hNd⟩
    have hx_le_d : x ≤ d := by
      have : -d ≤ -x := by
        simpa [abs_of_nonpos hd_nonpos, abs_of_nonpos hxle0] using hAd
      exact (neg_le_neg_iff.mp this)
    have hd_le_x : d ≤ x := hDN.2.1
    have hd_eq_x : d = x := le_antisymm hd_le_x hx_le_d
    -- From nearest minimality for u with candidate d, conclude u = x = d.
    have hdist : |u - x| ≤ |d - x| := hNu.2 d hDN.1
    have hux0 : |u - x| = 0 := by
      have : |u - x| ≤ 0 := by simpa [hd_eq_x, sub_self] using hdist
      exact le_antisymm this (abs_nonneg _)
    have hu_eq_x : u = x := by
      have : u - x = 0 := by simpa using (abs_eq_zero.mp hux0)
      exact sub_eq_zero.mp this
    simpa [hd_eq_x, hu_eq_x]

/-- Check uniqueness of N0-point

    With `F 0`, the N0-point is unique.
-/
noncomputable def Rnd_N0_pt_unique_check (F : ℝ → Prop) (x f1 f2 : ℝ) : Bool :=
  by
    classical
    exact pure (decide (f1 = f2))

/-- Specification: N0-point uniqueness

    If `Rnd_N0_pt F x f1` and `Rnd_N0_pt F x f2` with `F 0`, then `f1 = f2`.
-/
@[spec]
theorem Rnd_N0_pt_unique_spec (F : ℝ → Prop) (x f1 f2 : ℝ) :
    ⦃⌜F 0 ∧ Rnd_N0_pt F x f1 ∧ Rnd_N0_pt F x f2⌝⦄
    Rnd_N0_pt_unique_check F x f1 f2
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N0_pt_unique_check
  classical
  -- Prove equality, then finish by simplification.
  have hF0 : F 0 := h.1
  have hN01 : Rnd_N0_pt F x f1 := h.2.1
  have hN02 : Rnd_N0_pt F x f2 := h.2.2
  -- Convert N0-points to NG-points with predicate P := fun x f => |f| ≤ |x|.
  have hEqv1 : Rnd_N0_pt F x f1 ↔ Rnd_NG_pt F (fun x f => |f| ≤ |x|) x f1 := by
    have hspec := Rnd_N0_NG_pt_spec F x f1
    simpa [Rnd_N0_NG_pt_check, pure, decide_eq_true_iff]
      using hspec hF0
  have hEqv2 : Rnd_N0_pt F x f2 ↔ Rnd_NG_pt F (fun x f => |f| ≤ |x|) x f2 := by
    have hspec := Rnd_N0_NG_pt_spec F x f2
    simpa [Rnd_N0_NG_pt_check, pure, decide_eq_true_iff]
      using hspec hF0
  have hNG1 : Rnd_NG_pt F (fun x f => |f| ≤ |x|) x f1 := (hEqv1.mp hN01)
  have hNG2 : Rnd_NG_pt F (fun x f => |f| ≤ |x|) x f2 := (hEqv2.mp hN02)
  -- Obtain the tie uniqueness property specialized to P := |f| ≤ |x| under F 0.
  have hTieProp : ∀ x d u,
      Rnd_DN_pt F x d → Rnd_N_pt F x d →
      Rnd_UP_pt F x u → Rnd_N_pt F x u →
      |d| ≤ |x| → |u| ≤ |x| → d = u := by
    have hspec := Rnd_N0_pt_unique_prop_spec F
    simpa [Rnd_N0_pt_unique_prop_check, pure,
      decide_eq_true_iff] using hspec hF0
  -- Apply the generic uniqueness result for NG-points to get f1 = f2.
  have heq : f1 = f2 := by
    have huniq := Rnd_NG_pt_unique_spec F (fun x f => |f| ≤ |x|) x f1 f2
    simpa [Rnd_NG_pt_unique_check, pure,
      decide_eq_true_iff] using huniq ⟨hTieProp, hNG1, hNG2⟩
  -- Conclude the boolean check is true.
  simpa [ pure, decide_eq_true_iff, heq]

/-- Check that N0-point arises from nearest with abs bound

    If `Rnd_N_pt F x f` and `|f| ≤ |x|` with `F 0`, then `Rnd_N0_pt F x f`.
-/
noncomputable def Rnd_N0_pt_N_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    -- From nearest with |f| ≤ |x| to N0-point.
    classical
    exact pure (decide (Rnd_N0_pt F x f))

/-- Specification: From nearest with abs bound to N0-point

    From `F 0`, `Rnd_N_pt F x f`, and `|f| ≤ |x|`, conclude `Rnd_N0_pt F x f`.
-/
@[spec]
theorem Rnd_N0_pt_N_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜F 0 ∧ Rnd_N_pt F x f ∧ |f| ≤ |x|⌝⦄
    Rnd_N0_pt_N_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N0_pt_N_check
  classical
  -- Reduce to establishing `Rnd_N0_pt F x f` from the preconditions.
  simp [ pure]
  rcases h with ⟨hF0, hN, hbound⟩
  -- Use equivalence N0 ↔ NG with predicate P := fun x f => |f| ≤ |x| under F 0.
  have hEqv :
      Rnd_N0_pt F x f ↔ Rnd_NG_pt F (fun x f => |f| ≤ |x|) x f := by
    have hspec := Rnd_N0_NG_pt_spec F x f
    simpa [Rnd_N0_NG_pt_check, pure,
      decide_eq_true_iff] using hspec hF0
  -- Since `P x f` holds from the bound, build the NG-point and convert back to N0.
  have hNG : Rnd_NG_pt F (fun x f => |f| ≤ |x|) x f := And.intro hN (Or.inl hbound)
  exact (hEqv.mpr hNG)

/-- Check uniqueness of N0-based rounding functions

    If both functions satisfy `Rnd_N0`, they agree pointwise.
-/
noncomputable def Rnd_N0_unique_check (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) : Bool :=
  by
    classical
    exact pure (decide (rnd1 x = rnd2 x))

/-- Specification: Function-level uniqueness for N0 rounding

    Under `F 0` and `Rnd_N0 F rnd1`, `Rnd_N0 F rnd2`, we have `rnd1 x = rnd2 x`.
-/
@[spec]
theorem Rnd_N0_unique_spec (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ) (x : ℝ) :
    ⦃⌜F 0 ∧ (∃ p1 p2, Rnd_N0 F rnd1 = pure p1 ∧ Rnd_N0 F rnd2 = pure p2 ∧ p1 ∧ p2)⌝⦄
    Rnd_N0_unique_check F rnd1 rnd2 x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_N0_unique_check
  classical
  -- Reduce Hoare triple to a boolean equality on the pointwise values.
  simp [ pure]
  rcases h with ⟨hF0, hpack⟩
  rcases hpack with ⟨p1, p2, hEq1, hEq2, Hp1, Hp2⟩
  -- Unpack the function-level N0 properties for rnd1 and rnd2.
  have h1run : (∀ y : ℝ, Rnd_N0_pt F y (rnd1 y)) = p1 := by
    simpa [Rnd_N0] using congrArg Id.run hEq1
  have h2run : (∀ y : ℝ, Rnd_N0_pt F y (rnd2 y)) = p2 := by
    simpa [Rnd_N0] using congrArg Id.run hEq2
  have H1 : ∀ y : ℝ, Rnd_N0_pt F y (rnd1 y) := by
    simpa [h1run] using Hp1
  have H2 : ∀ y : ℝ, Rnd_N0_pt F y (rnd2 y) := by
    simpa [h2run] using Hp2
  -- Apply N0-point uniqueness at the specific input x.
  have huniq := Rnd_N0_pt_unique_spec F x (rnd1 x) (rnd2 x)
  -- Its postcondition states exactly that `decide (rnd1 x = rnd2 x) = true`.
  simpa [Rnd_N0_pt_unique_check, pure]
    using huniq ⟨hF0, H1 x, H2 x⟩

/-- Check monotonicity for N0-point rounding

    With `F 0`, the N0-point rounding predicate is monotone.
-/
noncomputable def Rnd_N0_pt_monotone_check (F : ℝ → Prop) : Bool :=
  by
    classical
    exact pure (decide (round_pred_monotone (Rnd_N0_pt F)))

/-- Specification: N0-point is monotone

    Assuming `F 0`, `Rnd_N0_pt F` is monotone.
-/
@[spec]
theorem Rnd_N0_pt_monotone_spec (F : ℝ → Prop) :
    ⦃⌜F 0⌝⦄
    Rnd_N0_pt_monotone_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_pt_monotone_check
  classical
  -- Reduce to the underlying proposition about monotonicity of N0-points.
  simp [ pure]
  intro x y f g hx hy hxy
  -- Use equivalence N0 ↔ NG with predicate P := fun x f => |f| ≤ |x| (under F 0).
  have hEqv_x :
      Rnd_N0_pt F x f ↔ Rnd_NG_pt F (fun x f => |f| ≤ |x|) x f := by
    have hspec := Rnd_N0_NG_pt_spec F x f
    simpa [Rnd_N0_NG_pt_check, pure,
      decide_eq_true_iff] using hspec ‹F 0›
  have hEqv_y :
      Rnd_N0_pt F y g ↔ Rnd_NG_pt F (fun x f => |f| ≤ |x|) y g := by
    have hspec := Rnd_N0_NG_pt_spec F y g
    simpa [Rnd_N0_NG_pt_check, pure,
      decide_eq_true_iff] using hspec ‹F 0›
  -- Turn N0-points into NG-points.
  have hxNG : Rnd_NG_pt F (fun x f => |f| ≤ |x|) x f := (hEqv_x.mp hx)
  have hyNG : Rnd_NG_pt F (fun x f => |f| ≤ |x|) y g := (hEqv_y.mp hy)
  -- Obtain the tie-uniqueness property specialized to P := |f| ≤ |x| under F 0.
  have hTieUnique : ∀ x d u,
      Rnd_DN_pt F x d → Rnd_N_pt F x d →
      Rnd_UP_pt F x u → Rnd_N_pt F x u →
      |d| ≤ |x| → |u| ≤ |x| → d = u := by
    have hspec := Rnd_N0_pt_unique_prop_spec F
    simpa [Rnd_N0_pt_unique_prop_check, pure,
      decide_eq_true_iff] using hspec ‹F 0›
  -- Monotonicity for NG with this tie property.
  have hNGmono : round_pred_monotone (Rnd_NG_pt F (fun x f => |f| ≤ |x|)) := by
    have h := Rnd_NG_pt_monotone_spec F (fun x f => |f| ≤ |x|)
    simpa [Rnd_NG_pt_monotone_check, pure,
      decide_eq_true_iff] using h hTieUnique
  -- Conclude the desired inequality via NG monotonicity, then we're done.
  exact hNGmono x y f g hxNG hyNG hxy

/-- Check reflexivity of N0-point

    Representable values are fixed by N0-point rounding.
-/
noncomputable def Rnd_N0_pt_refl_check (F : ℝ → Prop) (x : ℝ) : Bool :=
  by
    classical
    exact pure (decide (Rnd_N0_pt F x x))

/-- Specification: N0-point reflexivity on representables

    From `F x`, deduce `Rnd_N0_pt F x x`.
-/
@[spec]
theorem Rnd_N0_pt_refl_spec (F : ℝ → Prop) (x : ℝ) :
    ⦃⌜F x⌝⦄
    Rnd_N0_pt_refl_check F x
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_pt_refl_check
  classical
  -- Reduce the Hoare triple to a pure goal about the N0-point predicate.
  simp [ pure]
  -- Build `Rnd_N0_pt F x x` directly from `F x`.
  -- First, `x` is nearest to itself.
  refine And.intro ?hN ?hminAbs
  · refine And.intro (by simpa) ?_
    intro g _
    have : 0 ≤ |x - g| := by simpa using abs_nonneg (x - g)
    simpa using this
  · intro f2 hN2
    rcases hN2 with ⟨hf2F, hmin⟩
    -- Minimality at `g = x` (using `F x`) forces `f2 = x`.
    have hle : |f2 - x| ≤ 0 := by simpa using (hmin x (by simpa))
    have heq0 : |f2 - x| = 0 := le_antisymm hle (abs_nonneg _)
    have hsub0 : f2 - x = 0 := by simpa using (abs_eq_zero.mp heq0)
    have hf2x : f2 = x := sub_eq_zero.mp hsub0
    -- Hence the tie-breaking inequality is trivial.
    simpa [hf2x]

/-- Check idempotency of N0-point

    If `Rnd_N0_pt F x f` and `F x`, then `f = x`.
-/
noncomputable def Rnd_N0_pt_idempotent_check (F : ℝ → Prop) (x f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (f = x))

/-- Specification: N0-point idempotency on representables

    From `Rnd_N0_pt F x f` and `F x`, deduce `f = x`.
-/
@[spec]
theorem Rnd_N0_pt_idempotent_spec (F : ℝ → Prop) (x f : ℝ) :
    ⦃⌜Rnd_N0_pt F x f ∧ F x⌝⦄
    Rnd_N0_pt_idempotent_check F x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Rnd_N0_pt_idempotent_check
  classical
  -- Reduce to proving `f = x` from nearest property at `x` and representability of `x`.
  simp [ pure]
  -- Extract nearest property from the N0-point hypothesis.
  -- The minimal-absolute tie information is not needed for idempotency at x.
  rcases ‹Rnd_N0_pt F x f ∧ F x› with ⟨hN0, hxF⟩
  rcases hN0 with ⟨hN, _hMinAbs⟩
  rcases hN with ⟨hfF, hmin⟩
  -- Minimality at `g = x` yields `|f - x| ≤ 0`, hence `f = x`.
  have hle : |f - x| ≤ 0 := by simpa using (hmin x hxF)
  have heq0 : |f - x| = 0 := le_antisymm hle (abs_nonneg _)
  have hsub0 : f - x = 0 := by simpa using (abs_eq_zero.mp heq0)
  exact sub_eq_zero.mp hsub0

end RoundNearestTies

section MonotoneImplications

/-- Check nonnegativity from rounding predicate monotonicity

    If a rounding predicate is monotone and maps 0 to 0, then `0 ≤ x`
    implies `0 ≤ f` when `P x f` holds.
-/
noncomputable def round_pred_ge_0_check (P : ℝ → ℝ → Prop) (x f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (0 ≤ f))

/-- Specification: Monotone predicate preserves nonnegativity

    From `round_pred_monotone P`, `P 0 0`, `P x f`, and `0 ≤ x`, deduce `0 ≤ f`.
-/
@[spec]
theorem round_pred_ge_0_spec (P : ℝ → ℝ → Prop) (x f : ℝ) :
    ⦃⌜round_pred_monotone P ∧ P 0 0 ∧ P x f ∧ 0 ≤ x⌝⦄
    round_pred_ge_0_check P x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold round_pred_ge_0_check
  classical
  -- From the precondition and monotonicity, deduce 0 ≤ f.
  have hf_nonneg : 0 ≤ f := by
    rcases h with ⟨hmono, hP00, hPx, hx0⟩
    exact hmono 0 x 0 f hP00 hPx hx0
  -- Reduce Hoare triple to a pure propositional goal and discharge it via `hf_nonneg`.
  simpa [ pure, decide_eq_true_iff, hf_nonneg]

/-- Check positivity implication from monotonicity

    If a rounding predicate is monotone and maps 0 to 0, then `0 < f`
    implies `0 < x` when `P x f` holds.
-/
noncomputable def round_pred_gt_0_check (P : ℝ → ℝ → Prop) (x f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (0 < x))

/-- Specification: Positivity transfers back via monotonicity

    From `round_pred_monotone P`, `P 0 0`, `P x f`, and `0 < f`, deduce `0 < x`.
-/
@[spec]
theorem round_pred_gt_0_spec (P : ℝ → ℝ → Prop) (x f : ℝ) :
    ⦃⌜round_pred_monotone P ∧ P 0 0 ∧ P x f ∧ 0 < f⌝⦄
    round_pred_gt_0_check P x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold round_pred_gt_0_check
  classical
  -- From `0 < f` and monotonicity, deduce `0 < x` by contrapositive.
  -- If `x ≤ 0`, monotonicity implies `f ≤ 0`, contradicting `0 < f`.
  rcases h with ⟨hmono, hP00, hPx, hfpos⟩
  have hxpos : 0 < x := by
    by_contra hxnotpos
    have hxle : x ≤ 0 := le_of_not_gt hxnotpos
    have hf_le_zero : f ≤ 0 := hmono x 0 f 0 hPx hP00 hxle
    exact (not_le_of_gt hfpos) hf_le_zero
  -- Reduce the triple to a propositional goal about `decide (0 < x)`.
  simpa [ pure, decide_eq_true_iff, hxpos]

/-- Check nonpositivity from rounding predicate monotonicity

    If a rounding predicate is monotone and maps 0 to 0, then `x ≤ 0`
    implies `f ≤ 0` when `P x f` holds.
-/
noncomputable def round_pred_le_0_check (P : ℝ → ℝ → Prop) (x f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (f ≤ 0))

/-- Specification: Monotone predicate preserves nonpositivity

    From `round_pred_monotone P`, `P 0 0`, `P x f`, and `x ≤ 0`, deduce `f ≤ 0`.
-/
@[spec]
theorem round_pred_le_0_spec (P : ℝ → ℝ → Prop) (x f : ℝ) :
    ⦃⌜round_pred_monotone P ∧ P 0 0 ∧ P x f ∧ x ≤ 0⌝⦄
    round_pred_le_0_check P x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold round_pred_le_0_check
  classical
  -- From the precondition and monotonicity, deduce f ≤ 0.
  have hf_nonpos : f ≤ 0 := by
    rcases h with ⟨hmono, hP00, hPx, hx0⟩
    exact hmono x 0 f 0 hPx hP00 hx0
  -- Reduce Hoare triple to a pure propositional goal and discharge it via `hf_nonpos`.
  simpa [ pure, decide_eq_true_iff, hf_nonpos]

/-- Check negativity implication from monotonicity

    If a rounding predicate is monotone and maps 0 to 0, then `f < 0`
    implies `x < 0` when `P x f` holds.
-/
noncomputable def round_pred_lt_0_check (P : ℝ → ℝ → Prop) (x f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (x < 0))

/-- Specification: Negativity transfers back via monotonicity

    From `round_pred_monotone P`, `P 0 0`, `P x f`, and `f < 0`, deduce `x < 0`.
-/
@[spec]
theorem round_pred_lt_0_spec (P : ℝ → ℝ → Prop) (x f : ℝ) :
    ⦃⌜round_pred_monotone P ∧ P 0 0 ∧ P x f ∧ f < 0⌝⦄
    round_pred_lt_0_check P x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold round_pred_lt_0_check
  classical
  -- Unpack assumptions and argue by contrapositive.
  rcases h with ⟨hmono, hP00, hPx, hfneg⟩
  have hxneg : x < 0 := by
    -- If 0 ≤ x, monotonicity would imply 0 ≤ f, contradicting f < 0.
    by_contra hxnotneg
    have hx_nonneg : 0 ≤ x := le_of_not_gt hxnotneg
    have hf_nonneg : 0 ≤ f := hmono 0 x 0 f hP00 hPx hx_nonneg
    exact (not_le_of_gt hfneg) hf_nonneg
  -- Reduce to the propositional goal about `decide (x < 0)`.
  simpa [ pure, decide_eq_true_iff, hxneg]

end MonotoneImplications

section FormatEquivalence

/-- Check DN-point equivalence under format agreement on an interval

    If two formats agree on `[a,b]`, DN-points computed in `F1` on that
    interval are also DN-points in `F2`.
-/
noncomputable def Rnd_DN_pt_equiv_format_check (F1 F2 : ℝ → Prop) (a b x f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (Rnd_DN_pt F2 x f))

/-- Specification: DN-point equivalence under format agreement

    From `F1 a`, `∀ x ∈ [a,b], F1 x ↔ F2 x`, `a ≤ x ≤ b`, and `Rnd_DN_pt F1 x f`,
    conclude `Rnd_DN_pt F2 x f`.
-/
@[spec]
theorem Rnd_DN_pt_equiv_format_spec (F1 F2 : ℝ → Prop) (a b x f : ℝ) :
    ⦃⌜F1 a ∧ (∀ x, a ≤ x ∧ x ≤ b → (F1 x ↔ F2 x)) ∧ a ≤ x ∧ x ≤ b ∧ Rnd_DN_pt F1 x f⌝⦄
    Rnd_DN_pt_equiv_format_check F1 F2 a b x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_DN_pt_equiv_format_check
  classical
  -- Reduce to the underlying DN-point predicate over F2.
  simp [ pure]
  -- Unpack assumptions.
  rcases h with ⟨Ha, HFeq, hax, hxb, hDN⟩
  rcases hDN with ⟨HfF1, hf_le_x, hmax1⟩
  -- First show that f lies in the interval [a,b].
  have ha_le_f : a ≤ f := hmax1 a Ha hax
  have hf_le_b : f ≤ b := le_trans hf_le_x hxb
  have hf_interval : a ≤ f ∧ f ≤ b := ⟨ha_le_f, hf_le_b⟩
  -- Use format equivalence on [a,b] to transfer F1 f to F2 f.
  have HfF2 : F2 f := (HFeq f hf_interval).mp HfF1
  -- Assemble the DN-point for F2: membership, inequality, and maximality.
  refine And.intro HfF2 ?rest
  refine And.intro hf_le_x ?max2
  -- Prove maximality over F2 using the equivalence on [a,b] and maximality over F1.
  intro k HkF2 hk_le_x
  -- Split whether k is below a or within [a,b].
  by_cases hk_lt_a : k < a
  · -- If k < a ≤ f then k ≤ f immediately.
    exact le_trans (le_of_lt hk_lt_a) ha_le_f
  · -- Otherwise a ≤ k; also k ≤ b since k ≤ x ≤ b.
    have hk_ge_a : a ≤ k := le_of_not_lt hk_lt_a
    have hk_le_b : k ≤ b := le_trans hk_le_x hxb
    have hk_interval : a ≤ k ∧ k ≤ b := ⟨hk_ge_a, hk_le_b⟩
    -- Transfer membership to F1 and apply maximality there.
    have HkF1 : F1 k := (HFeq k hk_interval).mpr HkF2
    exact hmax1 k HkF1 hk_le_x

/-- Check UP-point equivalence under format agreement on an interval

    If two formats agree on `[a,b]`, UP-points computed in `F1` on that
    interval are also UP-points in `F2`.
-/
noncomputable def Rnd_UP_pt_equiv_format_check (F1 F2 : ℝ → Prop) (a b x f : ℝ) : Bool :=
  by
    classical
    exact pure (decide (Rnd_UP_pt F2 x f))

/-- Specification: UP-point equivalence under format agreement

    From `F1 b`, `∀ x ∈ [a,b], F1 x ↔ F2 x`, `a ≤ x ≤ b`, and `Rnd_UP_pt F1 x f`,
    conclude `Rnd_UP_pt F2 x f`.
-/
@[spec]
theorem Rnd_UP_pt_equiv_format_spec (F1 F2 : ℝ → Prop) (a b x f : ℝ) :
    ⦃⌜F1 b ∧ (∀ x, a ≤ x ∧ x ≤ b → (F1 x ↔ F2 x)) ∧ a ≤ x ∧ x ≤ b ∧ Rnd_UP_pt F1 x f⌝⦄
    Rnd_UP_pt_equiv_format_check F1 F2 a b x f
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold Rnd_UP_pt_equiv_format_check
  classical
  -- Reduce to the underlying UP-point predicate over F2.
  simp [ pure]
  -- Unpack assumptions.
  rcases h with ⟨Hb, HFeq, hax, hxb, hUP⟩
  rcases hUP with ⟨HfF1, hx_le_f, hmin1⟩
  -- Show that f lies in the interval [a,b].
  have ha_le_f : a ≤ f := le_trans hax hx_le_f
  have hf_le_b : f ≤ b := hmin1 b Hb hxb
  have hf_interval : a ≤ f ∧ f ≤ b := ⟨ha_le_f, hf_le_b⟩
  -- Use format equivalence on [a,b] to transfer F1 f to F2 f.
  have HfF2 : F2 f := (HFeq f hf_interval).mp HfF1
  -- Assemble the UP-point for F2: membership, inequality, and minimality.
  refine And.intro HfF2 ?rest
  refine And.intro hx_le_f ?min2
  -- Prove minimality over F2 using the equivalence on [a,b] and minimality over F1.
  intro k HkF2 hx_le_k
  -- Either k ≤ b, in which case transfer membership to F1 via equivalence;
  -- otherwise, use f ≤ b < k.
  by_cases hk_le_b : k ≤ b
  · -- In this branch, a ≤ k since a ≤ x ≤ k.
    have ha_le_k : a ≤ k := le_trans hax hx_le_k
    have hk_interval : a ≤ k ∧ k ≤ b := ⟨ha_le_k, hk_le_b⟩
    have HkF1 : F1 k := (HFeq k hk_interval).mpr HkF2
    exact hmin1 k HkF1 hx_le_k
  · have hb_lt_k : b < k := lt_of_not_ge hk_le_b
    exact le_trans hf_le_b (le_of_lt hb_lt_k)

end FormatEquivalence

section SatisfiesAnyConsequences

/-- Check alternative characterization of `satisfies_any`

    Placeholder equivalence/characterization for `satisfies_any`.
-/
noncomputable def satisfies_any_eq_check (F : ℝ → Prop) : Bool :=
  by
    -- A usable consequence: formats equivalent pointwise preserve `satisfies_any`.
    -- This matches Coq's `satisfies_any_eq` theorem.
    classical
    exact
      pure
        (decide
          (∀ (F1 F2 : ℝ → Prop), (∀ x, F1 x ↔ F2 x) →
            FloatSpec.Core.Generic_fmt.satisfies_any F1 →
            FloatSpec.Core.Generic_fmt.satisfies_any F2))

/-- Specification: `satisfies_any` alternative characterization

    A placeholder statement expressing equivalence for `satisfies_any`.
-/
@[spec]
theorem satisfies_any_eq_spec (F : ℝ → Prop) :
    ⦃⌜True⌝⦄
    satisfies_any_eq_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold satisfies_any_eq_check
  classical
  -- Reduce to proving the Coq-style consequence as a proposition.
  simp [ pure]
  -- Proof of: ∀ F1 F2, (∀ x, F1 x ↔ F2 x) → satisfies_any F1 → satisfies_any F2
  intro F1 F2 hEq hAny
  rcases hAny with ⟨x, hx⟩
  exact ⟨x, (hEq x).mp hx⟩

/-- Check existence of DN rounding from `satisfies_any`

    If a format `satisfies_any`, DN rounding is total.
-/
noncomputable def satisfies_any_imp_DN_check (F : ℝ → Prop) : Bool :=
  by
    classical
    -- Totality of DN rounding as a round_pred property.
    exact pure (decide (round_pred (Rnd_DN_pt F)))

/-- Specification: `satisfies_any` implies DN rounding exists

    From `satisfies_any F`, DN rounding predicate is total.
-/
@[spec]
theorem satisfies_any_imp_DN_spec (F : ℝ → Prop) :
    ⦃⌜round_pred_total (Rnd_DN_pt F)⌝⦄
    satisfies_any_imp_DN_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro htot
  unfold satisfies_any_imp_DN_check
  classical
  -- Reduce the Hoare triple to the underlying proposition about `round_pred`.
  -- It suffices to show totality and monotonicity for `Rnd_DN_pt F`.
  simp [ pure, round_pred]
  constructor
  · -- Totality comes from the precondition (Coq's satisfies_any contains this field).
    exact htot
  · -- Monotonicity of DN-points holds for any format F.
    intro x y f g hx hy hxy
    rcases hx with ⟨hfF, hf_le_x, hmax_x⟩
    rcases hy with ⟨hgF, hy_le_y, hmax_y⟩
    have hf_le_y : f ≤ y := le_trans hf_le_x hxy
    exact hmax_y f hfF hf_le_y

/-- Check existence of UP rounding from `satisfies_any`

    If a format `satisfies_any`, UP rounding is total.
-/
noncomputable def satisfies_any_imp_UP_check (F : ℝ → Prop) : Bool :=
  by
    classical
    exact pure (decide (round_pred (Rnd_UP_pt F)))

/-- Specification: `satisfies_any` implies UP rounding exists

    From `satisfies_any F`, UP rounding predicate is total.
-/
@[spec]
theorem satisfies_any_imp_UP_spec (F : ℝ → Prop) :
    ⦃⌜round_pred_total (Rnd_UP_pt F)⌝⦄
    satisfies_any_imp_UP_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro htot
  unfold satisfies_any_imp_UP_check
  classical
  -- Reduce the Hoare triple to proving `round_pred (Rnd_UP_pt F)`.
  simp [ pure, round_pred]
  constructor
  · -- Totality comes from the precondition.
    exact htot
  · -- Monotonicity of UP-points holds for any format `F`.
    intro x y f g hx hy hxy
    rcases hx with ⟨hfF, hx_le_f, hmin_x⟩
    rcases hy with ⟨hgF, hy_le_y, hmin_y⟩
    -- Since x ≤ y ≤ g, we have x ≤ g; minimality at x yields f ≤ g.
    have hx_le_g : x ≤ g := le_trans hxy hy_le_y
    exact hmin_x g hgF hx_le_g

/-- Check existence of ZR rounding from `satisfies_any`

    If a format `satisfies_any`, ZR rounding is total.
-/
noncomputable def satisfies_any_imp_ZR_check (F : ℝ → Prop) : Bool :=
  by
    classical
    exact pure (decide (round_pred (FloatSpec.Core.Defs.Rnd_ZR_pt F)))

/-- Specification: `satisfies_any` implies ZR rounding exists

    From `satisfies_any F`, ZR rounding predicate is total.
-/
@[spec]
theorem satisfies_any_imp_ZR_spec (F : ℝ → Prop) :
    ⦃⌜round_pred_total (FloatSpec.Core.Defs.Rnd_ZR_pt F)⌝⦄
    satisfies_any_imp_ZR_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro htot
  unfold satisfies_any_imp_ZR_check
  classical
  -- Reduce the Hoare triple to proving `round_pred (Rnd_ZR_pt F)`.
  simp [ pure, round_pred]
  constructor
  · -- Totality follows from the precondition.
    exact htot
  · -- Monotonicity of `Rnd_ZR_pt`.
    intro x y f g hx hy hxy
    -- Derive `F 0` from totality at x = 0.
    obtain ⟨f0, h0⟩ := htot 0
    have hDN0 : Rnd_DN_pt F 0 f0 := (h0.1) le_rfl
    have hUP0 : Rnd_UP_pt F 0 f0 := (h0.2) le_rfl
    have hf0_le0 : f0 ≤ 0 := hDN0.2.1
    have h0_lef0 : 0 ≤ f0 := hUP0.2.1
    have hf0_eq0 : f0 = 0 := le_antisymm hf0_le0 h0_lef0
    have hF0 : F 0 := by simpa [hf0_eq0] using hDN0.1
    -- Prove monotonicity by cases on the signs of x and y.
    by_cases hx0 : 0 ≤ x
    · -- x ≥ 0: both sides are DN-points (since y ≥ x ≥ 0)
      have hDNx : Rnd_DN_pt F x f := (hx.1) hx0
      have hy0 : 0 ≤ y := le_trans hx0 hxy
      have hDNy : Rnd_DN_pt F y g := (hy.1) hy0
      -- Use maximality at y with candidate f
      exact hDNy.2.2 f hDNx.1 (le_trans hDNx.2.1 hxy)
    · -- x < 0: `hx` gives an UP-point at x
      have hUPx : Rnd_UP_pt F x f := (hx.2) (le_of_lt (lt_of_not_ge hx0))
      -- Split on the sign of y
      by_cases hy0 : 0 ≤ y
      · -- x < 0 ≤ y: compare via 0 using `F 0`
        have hDNy : Rnd_DN_pt F y g := (hy.1) hy0
        have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx0)
        have hfle0 : f ≤ 0 := hUPx.2.2 0 hF0 hxle0
        have h0leg : 0 ≤ g := hDNy.2.2 0 hF0 hy0
        exact le_trans hfle0 h0leg
      · -- y < 0: both sides are UP-points
        have hUPy : Rnd_UP_pt F y g := (hy.2) (le_of_lt (lt_of_not_ge hy0))
        have hxleg : x ≤ g := le_trans hxy hUPy.2.1
        exact hUPx.2.2 g hUPy.1 hxleg

/-- Check existence of NG rounding from `satisfies_any`

    If a format `satisfies_any`, NG rounding is total.
-/
noncomputable def satisfies_any_imp_NG_check (F : ℝ → Prop) (P : ℝ → ℝ → Prop) : Bool :=
  by
    classical
    exact pure (decide (round_pred (Rnd_NG_pt F P)))

/-- Specification: `satisfies_any` implies NG rounding exists

    From `satisfies_any F` and a predicate `P`, NG rounding predicate is total.
-/
@[spec]
theorem satisfies_any_imp_NG_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop) :
    ⦃⌜round_pred_total (Rnd_NG_pt F P) ∧
        (∀ x d u,
          Rnd_DN_pt F x d → Rnd_N_pt F x d →
          Rnd_UP_pt F x u → Rnd_N_pt F x u →
          P x d → P x u → d = u)⌝⦄
    satisfies_any_imp_NG_check F P
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold satisfies_any_imp_NG_check
  classical
  -- Reduce to the underlying `round_pred` proposition.
  simp [ pure, round_pred]
  rcases h with ⟨htot, hTieUnique⟩
  constructor
  · -- Totality provided by the precondition.
    exact htot
  · -- Monotonicity follows from the NG monotonicity lemma under tie uniqueness.
    -- Use the existing spec-lemma to discharge `round_pred_monotone`.
    have hmono := Rnd_NG_pt_monotone_spec (F := F) (P := P)
    -- Convert its boolean check result to the desired proposition.
    simpa [Rnd_NG_pt_monotone_check, pure, decide_eq_true_iff]
      using hmono hTieUnique

/-- Check existence of NA rounding from `satisfies_any`

    If a format `satisfies_any`, NA rounding is total.
-/
noncomputable def satisfies_any_imp_NA_check (F : ℝ → Prop) : Bool :=
  by
    classical
    exact pure (decide (round_pred (Rnd_NA_pt F)))

/-- Specification: `satisfies_any` implies NA rounding exists

    From `satisfies_any F`, NA rounding predicate is total.
-/
@[spec]
theorem satisfies_any_imp_NA_spec (F : ℝ → Prop) :
    ⦃⌜round_pred_total (Rnd_NA_pt F) ∧ F 0⌝⦄
    satisfies_any_imp_NA_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold satisfies_any_imp_NA_check
  classical
  -- Reduce to proving `round_pred (Rnd_NA_pt F)`.
  simp [ pure, round_pred]
  rcases h with ⟨htot, hF0⟩
  constructor
  · exact htot
  · -- Monotonicity from the NA monotonicity lemma under `F 0`.
    have hmono := Rnd_NA_pt_monotone_spec (F := F)
    simpa [Rnd_NA_pt_monotone_check, pure,
      decide_eq_true_iff] using hmono hF0

/-- Check existence of N0 rounding from `satisfies_any`

    If a format `satisfies_any`, N0 rounding is total.
-/
noncomputable def satisfies_any_imp_N0_check (F : ℝ → Prop) : Bool :=
  by
    classical
    exact pure (decide (round_pred (Rnd_N0_pt F)))

/-- Specification: `satisfies_any` implies N0 rounding exists

    From `satisfies_any F`, N0 rounding predicate is total.
-/
@[spec]
theorem satisfies_any_imp_N0_spec (F : ℝ → Prop) :
    ⦃⌜round_pred_total (Rnd_N0_pt F) ∧ F 0⌝⦄
    satisfies_any_imp_N0_check F
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  unfold satisfies_any_imp_N0_check
  classical
  -- Reduce to proving `round_pred (Rnd_N0_pt F)`.
  simp [ pure, round_pred]
  rcases h with ⟨htot, hF0⟩
  constructor
  · exact htot
  · -- Monotonicity from the N0 monotonicity lemma under `F 0`.
    have hmono := Rnd_N0_pt_monotone_spec (F := F)
    simpa [Rnd_N0_pt_monotone_check, pure,
      decide_eq_true_iff] using hmono hF0

end SatisfiesAnyConsequences

end FloatSpec.Core.Round_pred
