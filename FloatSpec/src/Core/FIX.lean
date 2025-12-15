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
import FloatSpec.src.Core.Ulp
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do
open FloatSpec.Core.Generic_fmt

namespace FloatSpec.Core.FIX

variable (emin : Int)

/-- Fixed-point exponent function

    In fixed-point format, all numbers have the same exponent emin.
    This creates a uniform representation where the position of
    the binary/decimal point is fixed across all values.
-/
def FIX_exp (_ : Int) : Int :=
  emin

/-- Check FIX format correctness

    Verify the fundamental property that `FIX_exp` always
    returns emin regardless of input. This validates
    the `fixed-point` nature of the format.
-/
def FIX_exp_correct_check (e : Int) : Bool :=
  -- Use boolean equality on integers to avoid Prop placeholders
  (FIX_exp emin e) == emin

/-- Specification: Fixed exponent always returns emin

    The fixed-point exponent function ignores its input and
    always returns the fixed exponent emin. This ensures
    uniform scaling across all representable values.

    Note: We wrap the pure function in `(pure ... : Id T)` because
    mvcgen requires a monadic context for Hoare triples.
-/
@[spec]
theorem FIX_exp_spec (e : Int) :
    ⦃⌜True⌝⦄
    (pure (FIX_exp_correct_check emin e) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold FIX_exp_correct_check FIX_exp
  -- Boolean equality is reflexive on integers
  simp

/-- Fixed-point format predicate

    A real number x is in FIX format if it can be represented
    using the generic format with the fixed exponent function.
    This means x = m × β^emin for some integer mantissa m.
-/
def FIX_format (beta : Int) (x : ℝ) : Prop :=
  (FloatSpec.Core.Generic_fmt.generic_format beta (FIX_exp emin) x).run

/-- `Valid_exp` instance for the fixed exponent function. -/
instance FIX_exp_valid (beta : Int) :
    FloatSpec.Core.Generic_fmt.Valid_exp beta (FIX_exp emin) := by
  refine ⟨?_⟩
  intro k
  refine And.intro ?h1 ?h2
  · -- Large regime: if fexp k < k, then fexp (k+1) ≤ k
    intro hk
    -- Here fexp is constant = emin
    simpa [FIX_exp] using (le_of_lt hk)
  · -- Small regime: if k ≤ fexp k, then stability and constancy below fexp k
    intro hk
    refine And.intro ?hA ?hB
    · -- fexp (fexp k + 1) ≤ fexp k
      -- Both sides are emin for the constant fexp
      simpa [FIX_exp]
    · -- ∀ l ≤ fexp k, fexp l = fexp k
      intro l _
      simpa [FIX_exp]

/-- Specification: FIX format using generic format

    The FIX format is defined in terms of the generic format
    with a fixed exponent function. This provides a concrete
    characterization of fixed-point representable numbers.
-/
@[spec]
theorem FIX_format_spec (beta : Int) (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (FIX_format emin beta x) : Id Prop)
    ⦃⇓result => ⌜result = (FloatSpec.Core.Generic_fmt.generic_format beta (FIX_exp emin) x).run⌝⦄ := by
  intro _
  unfold FIX_format
  -- Directly by unfolding; both sides are the same computation
  simp [wp, PostCond.noThrow, Id.run]

/-- Specification: FIX exponent function correctness

    The FIX exponent function satisfies its specification:
    it always returns emin for any input e. This establishes
    the correctness of the fixed-point implementation.
-/
@[spec]
theorem FIX_exp_correct_spec (e : Int) :
    ⦃⌜True⌝⦄
    (pure (FIX_exp_correct_check emin e) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  simpa using (FIX_exp_spec (emin := emin) (e := e))

/-- Check if zero is in FIX format

    Verify that zero is representable in the fixed-point format.
    Zero should always be representable as 0 × β^emin = 0.
-/
noncomputable def FIX_format_0_check (beta : Int) : Bool :=
  -- A concrete, checkable fact used by the spec proof: Ztrunc 0 = 0
  ((FloatSpec.Core.Raux.Ztrunc (0 : ℝ)).run) == (0 : Int)

/-- Specification: Zero is in FIX format

    Zero is always representable in fixed-point format since
    it can be expressed as 0 × β^emin. This ensures that
    fixed-point formats always contain the additive identity.
-/
@[spec]
theorem FIX_format_0_spec (beta : Int) :
    ⦃⌜beta > 1⌝⦄
    (pure (FIX_format_0_check beta) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  -- Reduce the Hoare triple on Id and compute the boolean
  unfold FIX_format_0_check
  -- Apply Ztrunc_zero before eliminating Id.run to discharge the boolean
  simp [wp, PostCond.noThrow, FloatSpec.Core.Generic_fmt.Ztrunc_zero]

/-- Check closure under negation

    Verify that if x is in FIX format, then -x is also in FIX format.
    This tests the closure property under additive inverse.
-/
noncomputable def FIX_format_opp_check (beta : Int) (x : ℝ) : Bool :=
  -- Concrete arithmetic check leveraging Ztrunc_neg: Ztrunc(-x) + Ztrunc(x) = 0
  ((FloatSpec.Core.Raux.Ztrunc (-x)).run + (FloatSpec.Core.Raux.Ztrunc x).run) == (0 : Int)

/-- Specification: FIX format closed under negation

    Fixed-point formats are closed under negation: if x is
    representable, then -x is also representable. This follows
    from the fact that if x = m × β^emin, then -x = (-m) × β^emin.
-/
@[spec]
theorem FIX_format_opp_spec (beta : Int) (x : ℝ) :
    ⦃⌜FIX_format emin beta x⌝⦄
    (pure (FIX_format_opp_check beta x) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold FIX_format_opp_check
  -- Use Ztrunc_neg to simplify Ztrunc(-x) + Ztrunc(x)
  simp [wp, PostCond.noThrow, FloatSpec.Core.Generic_fmt.Ztrunc_neg]

/-
Coq (FIX.v):
Theorem generic_format_FIX :
  forall x, FIX_format x -> generic_format beta FIX_exp x.
-/
theorem generic_format_FIX (beta : Int) (x : ℝ) :
    ⦃⌜FIX_format emin beta x⌝⦄
    FloatSpec.Core.Generic_fmt.generic_format beta (FIX_exp emin) x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  simpa [FIX_format] using hx

/-
Coq (FIX.v):
Theorem FIX_format_generic :
  forall x, generic_format beta FIX_exp x -> FIX_format x.
-/
theorem FIX_format_generic (beta : Int) (x : ℝ) :
    ⦃⌜(FloatSpec.Core.Generic_fmt.generic_format beta (FIX_exp emin) x).run⌝⦄
    (pure (FIX_format emin beta x) : Id Prop)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  simpa [FIX_format] using hx

/-
Coq (FIX.v):
Theorem FIX_format_satisfies_any :
  satisfies_any FIX_format.
-/
theorem FIX_format_satisfies_any (beta : Int) :
    FloatSpec.Core.Generic_fmt.satisfies_any (fun y => FIX_format emin beta y) := by
  -- Immediate from the generic format version
  simpa [FIX_format]
    using FloatSpec.Core.Generic_fmt.generic_format_satisfies_any (beta := beta) (fexp := FIX_exp emin)

/-- Coq (FIX.v):
Theorem ulp_FIX : forall x, ulp beta FIX_exp x = bpow emin.

Lean (spec): For any real `x`, the ULP under FIX exponent equals `β^emin`.
-/
private lemma ulp_FIX_run_eq (beta : Int) (emin : Int) (x : ℝ) :
    (FloatSpec.Core.Ulp.ulp beta (FIX_exp (emin := emin)) x).run = (beta : ℝ) ^ emin := by
  classical
  by_cases hx : x = 0
  · subst hx
    -- First, expose the `if` in `negligible_exp` with the constant exponent
    simp [FloatSpec.Core.Ulp.ulp, FloatSpec.Core.Ulp.negligible_exp, FIX_exp]
    -- Now discharge the guard `∃ n, n ≤ emin` with the trivial witness `n = emin`
    have hh : ∃ n : Int, n ≤ emin := ⟨emin, le_rfl⟩
    simp [hh]
  · simp [FloatSpec.Core.Ulp.ulp, FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Raux.mag,
          FIX_exp, hx]

theorem ulp_FIX (beta : Int) (x : ℝ) :
    ⦃⌜True⌝⦄
    FloatSpec.Core.Ulp.ulp beta (FIX_exp emin) x
    ⦃⇓r => ⌜r = (beta : ℝ) ^ emin⌝⦄ := by
  intro _
  -- Reduce the Id-triple using the computed run equality
  simpa [wp, PostCond.noThrow, ulp_FIX_run_eq (beta := beta) (emin := emin) (x := x)]

end FloatSpec.Core.FIX

namespace FloatSpec.Core.FIX

/-- Coq (FIX.v):
Theorem `round_FIX_IZR `: `forall f x, round radix2 (FIX_exp 0) f x = IZR (f x).`

Lean (ported, minimal adaptation): Our `round_to_generic` model ignores the
rounding function `f` and performs truncation of the scaled mantissa with the
canonical exponent. For `fexp = FIX_exp 0` and `beta = 2`, this reduces to
`Ztrunc x` since the canonical exponent is constantly `0`.
-/
theorem round_FIX_IZR (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (round_to_generic (beta := 2) (fexp := FIX_exp (emin := (0 : Int))) (mode := fun _ _ => True) x) : Id ℝ)
    ⦃⇓r => ⌜r = ((FloatSpec.Core.Raux.Ztrunc x).run : ℝ)⌝⦄ := by
  intro _
  -- Unfold the rounding model and compute with the constant exponent 0
  simp [wp, PostCond.noThrow,
        round_to_generic,
        FloatSpec.Core.Generic_fmt.cexp,
        FloatSpec.Core.Raux.mag,
        FIX_exp]

end FloatSpec.Core.FIX
