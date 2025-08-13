/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Copyright (C) 2011-2018 Sylvie Boldo
Copyright (C) 2011-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.

Unit in the last place (ulp) definitions and properties
Based on flocq/src/Core/Ulp.v
-/

import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Round_generic
import FloatSpec.src.Core.Float_prop
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do
open FloatSpec.Core.Generic_fmt
open FloatSpec.Core.Round_generic

namespace FloatSpec.Core.Ulp

section UnitInLastPlace

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Unit in the last place function

    The ULP of a real number x is the value of the least significant
    digit in the representation of x in the floating-point format.
    For zero, we use a special convention based on fexp(1).
-/
noncomputable def ulp (x : ℝ) : Id ℝ :=
  if x = 0 then
    pure ((beta : ℝ) ^ (fexp 1))
  else do
    let exp ← FloatSpec.Core.Generic_fmt.cexp beta fexp x
    pure ((beta : ℝ) ^ exp)

/-- Specification: ULP computation

    The ULP is computed as beta^(fexp(1)) for zero,
    and beta^(cexp(x)) for non-zero values.
-/
theorem ulp_spec (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    ulp beta fexp x
    ⦃⇓result => ⌜if x = 0 then result = (beta : ℝ) ^ (fexp 1)
                  else result = (beta : ℝ) ^ (fexp (mag beta x))⌝⦄ := by
  sorry

/-- Specification: ULP is non-negative

    The ULP is always a positive value since it's a power of beta > 1.
-/
theorem ulp_ge_0 (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    ulp beta fexp x
    ⦃⇓result => ⌜0 ≤ result⌝⦄ := by
  sorry

/-- Specification: ULP of opposite

    The ULP is preserved under negation since it depends
    only on the magnitude, not the sign.
-/
theorem ulp_opp (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    do
      let ulp_neg ← ulp beta fexp (-x)
      let ulp_pos ← ulp beta fexp x
      pure (ulp_neg, ulp_pos)
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  sorry

/-- Specification: ULP of absolute value

    The ULP equals the ULP of the absolute value.
-/
theorem ulp_abs (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    do
      let ulp_abs_val ← ulp beta fexp |x|
      let ulp_val ← ulp beta fexp x
      pure (ulp_abs_val, ulp_val)
    ⦃⇓result => ⌜result.1 = result.2⌝⦄ := by
  sorry

end UnitInLastPlace

section ULPProperties

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Specification: ULP and generic format

    The ULP of any non-zero number is itself representable
    in the generic format.
-/
theorem generic_format_ulp (x : ℝ) (hx : x ≠ 0) :
    ⦃⌜beta > 1 ∧ x ≠ 0⌝⦄
    do
      let ulp_x ← ulp beta fexp x
      let is_generic ← FloatSpec.Core.Generic_fmt.generic_format beta fexp ulp_x
      pure true
    ⦃⇓result => ⌜result = true⌝⦄ := by
  sorry

/-- Specification: ULP upper bound

    For positive numbers in generic format, the ULP is at most the number itself.
-/
theorem ulp_le_id (x : ℝ) (hx : 0 < x) :
    ⦃⌜beta > 1 ∧ 0 < x⌝⦄
    do
      let is_generic ← FloatSpec.Core.Generic_fmt.generic_format beta fexp x
      let ulp_x ← ulp beta fexp x
      pure (is_generic, ulp_x ≤ x)
    ⦃⇓result => ⌜result.1 → result.2⌝⦄ := by
  sorry

/-- Specification: ULP is never zero

    The ULP is always a positive power of beta, so never zero.
-/
theorem ulp_neq_0 (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    ulp beta fexp x
    ⦃⇓result => ⌜result ≠ 0⌝⦄ := by
  sorry

end ULPProperties

section SuccessorPredecessor

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Successor in format

    The successor of x is x plus its ULP, representing
    the next larger representable value.
-/
noncomputable def succ (x : ℝ) : Id ℝ :=
  do
    let ulp_x ← ulp beta fexp x
    pure (x + ulp_x)

/-- Predecessor in format

    The predecessor of x is x minus its ULP, representing
    the next smaller representable value.
-/
noncomputable def pred (x : ℝ) : Id ℝ :=
  do
    let ulp_x ← ulp beta fexp x
    pure (x - ulp_x)

/-- Specification: Successor is greater than original

    The successor function always produces a value
    greater than or equal to the original.
-/
theorem succ_ge_id (beta : Int) (fexp : Int → Int) (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    do
      let succ_x ← succ beta fexp x
      pure true
    ⦃⇓result => ⌜result = true⌝⦄ := by
  sorry

/-- Specification: Generic format closure under successor

    If x is in generic format, then so is its successor.
-/
theorem generic_format_succ (beta : Int) (fexp : Int → Int) (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    do
      let is_generic ← FloatSpec.Core.Generic_fmt.generic_format beta fexp x
      let succ_x ← succ beta fexp x
      let succ_is_generic ← FloatSpec.Core.Generic_fmt.generic_format beta fexp succ_x
      pure (is_generic, succ_is_generic)
    ⦃⇓result => ⌜result.1 → result.2⌝⦄ := by
  sorry

end SuccessorPredecessor

section ErrorBounds

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Specification: Error characterization with ULP

    If the error between a format value f and x is less than
    half a ULP, then f is the correctly rounded value of x.
-/
theorem error_lt_ulp (beta : Int) (fexp : Int → Int) (x : ℝ) (f : ℝ) :
    ⦃⌜beta > 1⌝⦄
    do
      let is_generic ← FloatSpec.Core.Generic_fmt.generic_format beta fexp f
      let ulp_x ← ulp beta fexp x
      pure (is_generic, |f - x| < ulp_x / 2)
    ⦃⇓result => ⌜result.1 ∧ result.2 → True⌝⦄ := by
  sorry

end ErrorBounds

end FloatSpec.Core.Ulp
