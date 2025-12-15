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
import FloatSpec.src.Core.Zaux
-- import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do

/-
Coq typeclass: precision strictly positive.
Placed at root so both Core and higher layers can depend on it
without cyclic imports.
-/
class Prec_gt_0 (prec : Int) : Prop :=
  (pos : 0 < prec)

namespace FloatSpec.Core.Defs

section BasicDefinitions

/-- Floating-point number representation with mantissa and exponent

    A floating-point number is represented as Fnum × beta^Fexp where:
    - Fnum is the mantissa (significand), an integer
    - Fexp is the exponent, an integer
    - beta is the radix (base), typically 2 or 10

    This matches the Coq float record with a radix parameter.
-/
structure FlocqFloat (beta : Int) where
  /-- Mantissa (significand) -/
  Fnum : Int
  /-- Exponent -/
  Fexp : Int

-- Make the fields accessible without explicit beta parameter
variable {beta : Int}

/-- Convert FlocqFloat to real number

    The conversion formula is: Fnum × beta^Fexp
    This is the fundamental interpretation of floating-point numbers
    as approximations of real numbers.
-/

noncomputable def F2R (f : FlocqFloat beta) : Id ℝ :=
  pure (f.Fnum * (beta : ℝ) ^ f.Fexp)

/-- Specification: Float to real conversion

    The F2R function converts a floating-point representation
    to its corresponding real value using the formula:
    F2R(Fnum, Fexp) = Fnum × beta^Fexp

    This is the bridge between the discrete float representation
    and the continuous real numbers it approximates.
-/
@[spec]
theorem F2R_spec (f : FlocqFloat beta) :
    ⦃⌜beta > 1⌝⦄
    F2R f
    ⦃⇓result => ⌜result = f.Fnum * (beta : ℝ) ^ f.Fexp⌝⦄ := by
  intro _h
  unfold F2R
  rfl

end BasicDefinitions

section RoundingPredicates

/-- A rounding predicate is total

    For every real number, there exists at least one value
    in the format that the predicate relates to it.
    This ensures rounding is always possible.
-/
def round_pred_total (P : ℝ → ℝ → Prop) : Prop :=
  ∀ x : ℝ, ∃ f : ℝ, P x f

/-- A rounding predicate is monotone

    If x ≤ y and P relates x to f and y to g,
    then f ≤ g. This preserves the ordering of values
    through the rounding process.
-/
def round_pred_monotone (P : ℝ → ℝ → Prop) : Prop :=
  ∀ x y f g : ℝ, P x f → P y g → x ≤ y → f ≤ g

/-- A proper rounding predicate

    Combines totality and monotonicity to ensure
    well-behaved rounding operations.
-/
def round_pred (P : ℝ → ℝ → Prop) : Prop :=
  round_pred_total P ∧ round_pred_monotone P

end RoundingPredicates

section RoundingModes

/-- Rounding toward negative infinity (floor)

    Rounds to the largest representable value not exceeding x.
    This is also known as rounding down or floor rounding.
-/
def Rnd_DN_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ f ≤ x ∧ ∀ g : ℝ, F g → g ≤ x → g ≤ f

/-- Rounding toward positive infinity (ceiling)

    Rounds to the smallest representable value not less than x.
    This is also known as rounding up or ceiling rounding.
-/
def Rnd_UP_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ x ≤ f ∧ ∀ g : ℝ, F g → x ≤ g → f ≤ g

/-- Rounding toward zero (truncation)

    Rounds positive values down and negative values up,
    effectively truncating toward zero.
-/
def Rnd_ZR_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  (0 ≤ x → Rnd_DN_pt F x f) ∧ (x ≤ 0 → Rnd_UP_pt F x f)

/-- Rounding to nearest

    Rounds to the representable value closest to x.
    This definition allows any tie-breaking rule when
    two values are equidistant.
-/
def Rnd_N_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ ∀ g : ℝ, F g → |f - x| ≤ |g - x|

/-- Generic rounding to nearest with custom tie-breaking

    Extends Rnd_N_pt with a predicate P that specifies
    the tie-breaking rule when multiple values are nearest.
-/
def Rnd_NG_pt (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (x f : ℝ) : Prop :=
  Rnd_N_pt F x f ∧ (P x f ∨ ∀ f2 : ℝ, Rnd_N_pt F x f2 → f2 = f)

/-- Rounding to nearest, ties away from zero

    When two values are equidistant, chooses the one
    with larger absolute value.
-/
def Rnd_NA_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  Rnd_N_pt F x f ∧ ∀ f2 : ℝ, Rnd_N_pt F x f2 → |f2| ≤ |f|

/-- Rounding to nearest, ties toward zero

    When two values are equidistant, chooses the one
    with smaller absolute value.
-/
def Rnd_N0_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  Rnd_N_pt F x f ∧ ∀ f2 : ℝ, Rnd_N_pt F x f2 → |f| ≤ |f2|

end RoundingModes

section HelperFunctions

/-- Extract the mantissa from a FlocqFloat

    Simple accessor function for the mantissa field.
-/
def Fnum_extract {beta : Int} (f : FlocqFloat beta) : Id Int :=
  pure f.Fnum

/-- Specification: Mantissa extraction

    The extraction returns the Fnum field unchanged.
-/
@[spec]
theorem Fnum_extract_spec {beta : Int} (f : FlocqFloat beta) :
    ⦃⌜True⌝⦄
    Fnum_extract f
    ⦃⇓result => ⌜result = f.Fnum⌝⦄ := by
  intro _
  unfold Fnum_extract
  rfl

/-- Extract the exponent from a FlocqFloat

    Simple accessor function for the exponent field.
-/
def Fexp_extract {beta : Int} (f : FlocqFloat beta) : Id Int :=
  pure f.Fexp

/-- Specification: Exponent extraction

    The extraction returns the Fexp field unchanged.
-/
@[spec]
theorem Fexp_extract_spec {beta : Int} (f : FlocqFloat beta) :
    ⦃⌜True⌝⦄
    Fexp_extract f
    ⦃⇓result => ⌜result = f.Fexp⌝⦄ := by
  intro _
  unfold Fexp_extract
  rfl

/-- Create a FlocqFloat from mantissa and exponent

    Constructor function for building floating-point values.
-/
def make_float {beta : Int} (num exp : Int) : Id (FlocqFloat beta) :=
  pure ⟨num, exp⟩

/-- Specification: Float construction

    The constructor properly sets both fields.
-/
@[spec]
theorem make_float_spec {beta : Int} (num exp : Int) :
    ⦃⌜True⌝⦄
    make_float (beta := beta) num exp
    ⦃⇓result => ⌜result.Fnum = num ∧ result.Fexp = exp⌝⦄ := by
  intro _
  unfold make_float
  simp [pure]
  constructor <;> rfl

end HelperFunctions

section StructuralProperties

/-- Check if two FlocqFloats are equal

    Returns true if both mantissa and exponent match.
-/
def FlocqFloat_eq {beta : Int} (f g : FlocqFloat beta) : Id Bool :=
  pure (f.Fnum == g.Fnum && f.Fexp == g.Fexp)

/-- Specification: Float equality

    Two FlocqFloats are equal iff their components are equal.
-/
@[spec]
theorem FlocqFloat_eq_spec {beta : Int} (f g : FlocqFloat beta) :
    ⦃⌜True⌝⦄
    FlocqFloat_eq f g
    ⦃⇓result => ⌜result ↔ (f.Fnum = g.Fnum ∧ f.Fexp = g.Fexp)⌝⦄ := by
  intro _
  unfold FlocqFloat_eq
  -- The boolean equality check returns true iff both components are equal
  simp [Bool.and_eq_true]

/-- Convert zero float to real

    The zero float (0, 0) should convert to real zero.
-/
noncomputable def F2R_zero_float {beta : Int} : Id ℝ :=
  F2R (⟨0, 0⟩ : FlocqFloat beta)

/-- Specification: F2R preserves zero

    The zero float (0, 0) converts to real zero.
-/
@[spec]
theorem F2R_zero_spec {beta : Int} :
    ⦃⌜beta > 1⌝⦄
    F2R_zero_float (beta := beta)
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _h
  unfold F2R_zero_float F2R
  simp [pure]
  rfl

/-- Add two floats with same exponent

    When two floats have the same exponent, their sum
    can be computed by adding mantissas.
-/
noncomputable def F2R_add_same_exp {beta : Int} (f g : FlocqFloat beta) : Id (ℝ × ℝ) :=
  do
    let sum_float : FlocqFloat beta := ⟨f.Fnum + g.Fnum, f.Fexp⟩
    let f_real ← F2R f
    let g_real ← F2R g
    let sum_real ← F2R sum_float
    pure (sum_real, f_real + g_real)

/-- Specification: F2R is additive for same exponent

    When two floats have the same exponent, F2R distributes over addition.
-/
@[spec]
theorem F2R_add_same_exp_spec {beta : Int} (f g : FlocqFloat beta) :
    ⦃⌜f.Fexp = g.Fexp ∧ beta > 1⌝⦄
    F2R_add_same_exp f g
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  intro ⟨h_eq, _h_beta⟩
  unfold F2R_add_same_exp
  simp only [F2R, pure, h_eq, bind]
  -- Now we have a pair where we need to prove the two components are equal
  -- The left component: (f.Fnum + g.Fnum) * beta^g.Fexp
  -- The right component: f.Fnum * beta^g.Fexp + g.Fnum * beta^g.Fexp
  -- This follows from distributivity of multiplication over addition
  simp [add_mul]
  rfl

end StructuralProperties

end FloatSpec.Core.Defs
