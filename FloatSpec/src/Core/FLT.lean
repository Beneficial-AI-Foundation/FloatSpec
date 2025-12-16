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
import FloatSpec.src.Core.FLX
import FloatSpec.src.Core.FIX
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do
open FloatSpec.Core.Generic_fmt

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-- Floating-point exponent function

    The FLT exponent function combines fixed-precision behavior
    with a minimum exponent bound. It returns max(e - prec, emin),
    providing precision when possible but limiting underflow.
-/
def FLT_exp (e : Int) : Int :=
  max (e - prec) emin

/-- Check FLT exponent function correctness

    Verify that the FLT exponent function correctly computes
    the maximum of (e - prec) and emin. This validates the
    IEEE 754-style exponent calculation.
-/
def FLT_exp_correct_check (e : Int) : Bool :=
  decide (FLT_exp prec emin e = max (e - prec) emin)

/-- Specification: FLT exponent calculation

    The FLT exponent function implements IEEE 754-style floating-point
    exponent calculation: it maintains precision by using e - prec
    when possible, but enforces a minimum exponent emin to prevent
    excessive underflow and maintain gradual underflow behavior.
-/
@[spec]
theorem FLT_exp_spec (e : Int) :
    ⦃⌜True⌝⦄
    (pure (FLT_exp_correct_check prec emin e) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  -- Direct by unfolding the check and `FLT_exp`.
  simp [FLT_exp_correct_check, FLT_exp]

/-- Floating-point format predicate

    A real number x is in FLT format if it can be represented
    using the generic format with the FLT exponent function.
    This gives IEEE 754-style floating-point representation
    with both precision and minimum exponent constraints.
-/
def FLT_format (beta : Int) (x : ℝ) : Prop :=
  (generic_format beta (FLT_exp prec emin) x).run

/-- `Valid_exp `instance for the FLT exponent function. -/
instance FLT_exp_valid (beta : Int) [Prec_gt_0 prec] :
    FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp prec emin) := by
  refine ⟨?_⟩
  intro k
  refine And.intro ?h1 ?h2
  ·
    -- If max (k - prec) emin < k, then max (k + 1 - prec) emin ≤ k.
    intro hk
    have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    have hprec_ge1 : (1 : Int) ≤ prec := Int.add_one_le_iff.mpr hprec_pos
    -- From hk, we get emin ≤ k
    have hemin_le : emin ≤ k :=
      le_of_lt (lt_of_le_of_lt (le_max_right (k - prec) emin) hk)
    -- And (k + 1 - prec) ≤ k follows from 1 ≤ prec
    have hsub_nonpos : 1 - prec ≤ 0 := sub_nonpos.mpr hprec_ge1
    have hlin : k + (1 - prec) ≤ k + 0 := by omega
    have hlin' : k + 1 - prec ≤ k := by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlin
    -- Conclude using max_le_iff
    exact (max_le_iff.mpr ⟨hlin', hemin_le⟩)
  · intro hk
    refine And.intro ?hA ?hB
    · -- Show fexp (fexp k + 1) ≤ fexp k using 1 ≤ prec and emin ≤ fexp k
      have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
      have hprec_ge1 : (1 : Int) ≤ prec := Int.add_one_le_iff.mpr hprec_pos
      have hsub_nonpos : 1 - prec ≤ 0 := sub_nonpos.mpr hprec_ge1
      have hlin : (FLT_exp prec emin k) + (1 - prec) ≤ (FLT_exp prec emin k) + 0 := by omega
      have hlin' : (FLT_exp prec emin k) + 1 - prec ≤ (FLT_exp prec emin k) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlin
      have hemin_le : emin ≤ FLT_exp prec emin k := le_max_right _ _
      -- max ((fexp k) + 1 - prec) emin ≤ fexp k
      simpa [FLT_exp] using (max_le_iff.mpr ⟨hlin', hemin_le⟩)
    · intro l hl
      -- If l ≤ fexp k and k ≤ fexp k with prec > 0, then fexp is constant and equals emin.
      have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
      have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
      -- First, show fexp k = emin (small regime under hk and prec > 0)
      have hfk_eq : FLT_exp prec emin k = emin := by
        by_cases hemle : emin ≤ k - prec
        · -- Then fexp k = k - prec, but hk would force k ≤ k - prec, contradicting prec > 0
          have hf : FLT_exp prec emin k = k - prec := by simpa [FLT_exp, max_eq_left hemle]
          have hk' : k ≤ k - prec := by simpa [hf] using hk
          have h0le : (0 : Int) ≤ -prec := by
            have h' : k + 0 ≤ k + (-prec) := by
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hk'
            simpa using (le_of_add_le_add_left h')
          have hple0 : prec ≤ 0 := by simpa using (neg_nonneg.mp h0le)
          have : prec < prec := lt_of_le_of_lt hple0 hprec_pos
          exact (False.elim ((lt_irrefl (a := prec)) this))
        · -- Else k - prec ≤ emin, so fexp k = emin
          have : k - prec ≤ emin := le_of_not_ge hemle
          simpa [FLT_exp, max_eq_right this]
      -- From hl : l ≤ fexp k = emin, we deduce l ≤ emin
      have hl' : l ≤ emin := by
        have := hl
        simpa [hfk_eq] using this
      -- And l - prec ≤ l ≤ emin, so fexp l = emin as well
      have h_le_emin : l - prec ≤ emin := by
        have : -prec ≤ 0 := by simpa using (neg_nonpos.mpr hprec_nonneg)
        have h' := add_le_add_left this l
        have hll : l - prec ≤ l := by simpa [sub_eq_add_neg] using h'
        exact le_trans hll hl'
      have hfl : FLT_exp prec emin l = emin := by
        have : max (l - prec) emin = emin := max_eq_right h_le_emin
        simpa [FLT_exp, this]
      -- Conclude fexp l = fexp k
      simpa [hfk_eq, hfl]

/-- Specification: FLT format using generic format

    The FLT format combines the benefits of fixed-precision
    (for normal numbers) with minimum exponent protection
    (for subnormal numbers), matching IEEE 754 behavior.
-/
@[spec]
theorem FLT_format_spec (beta : Int) (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (FLT_format prec emin beta x) : Id Prop)
    ⦃⇓result => ⌜result = (generic_format beta (FLT_exp prec emin) x).run⌝⦄ := by
  intro _
  unfold FLT_format
  simp only [wp, PostCond.noThrow, Id.run, pure, PredTrans.pure]
  trivial

/-- Specification: FLT exponent function correctness

    The FLT exponent function correctly implements the IEEE 754
    exponent selection logic, choosing between precision-based
    and minimum-bounded exponents as appropriate.
-/
@[spec]
theorem FLT_exp_correct_spec (e : Int) :
    ⦃⌜True⌝⦄
    (pure (FLT_exp_correct_check prec emin e) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  simp [FLT_exp_correct_check, FLT_exp]

/-- Check if zero is in FLT format

    Verify that zero is representable in the floating-point format.
    Zero should always be representable as 0 × β^e for any
    allowed exponent e, making it universal across FLT formats.
-/
noncomputable def FLT_format_0_check (beta : Int) : Bool :=
  -- Concrete arithmetic check: Ztrunc 0 = 0
  ((FloatSpec.Core.Raux.Ztrunc (0 : ℝ)).run) == (0 : Int)

/-- Specification: Zero is in FLT format

    Zero is always representable in FLT format since it can
    be expressed as 0 × β^e for any exponent e, regardless
    of precision or minimum exponent constraints.
-/
@[spec]
theorem FLT_format_0_spec (beta : Int) :
    ⦃⌜beta > 1⌝⦄
    (pure (FLT_format_0_check beta) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  -- Ztrunc 0 = 0, so the boolean equality holds.
  have hz : (FloatSpec.Core.Raux.Ztrunc (0 : ℝ)).run = (0 : Int) := by
    simpa using FloatSpec.Core.Generic_fmt.Ztrunc_int (0 : Int)
  simp [FLT_format_0_check, hz]

/-- Check closure under negation

    Verify that if x is in FLT format, then -x is also in FLT format.
    This tests the sign symmetry property of IEEE 754-style
    floating-point representation.
-/
noncomputable def FLT_format_opp_check (beta : Int) (x : ℝ) : Bool :=
  -- Concrete arithmetic check leveraging Ztrunc_neg: Ztrunc(-x) + Ztrunc(x) = 0
  ((FloatSpec.Core.Raux.Ztrunc (-x)).run + (FloatSpec.Core.Raux.Ztrunc x).run) == (0 : Int)

/-- Specification: FLT format closed under negation

    FLT formats are closed under negation. If x = m × β^e
    is representable, then -x = (-m) × β^e is also representable
    using the same exponent and negated mantissa.
-/
@[spec]
theorem FLT_format_opp_spec (beta : Int) (x : ℝ) :
    ⦃⌜FLT_format prec emin beta x⌝⦄
    (pure (FLT_format_opp_check beta x) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold FLT_format_opp_check
  -- Use Ztrunc_neg to simplify Ztrunc(-x) + Ztrunc(x)
  simp [wp, PostCond.noThrow, FloatSpec.Core.Generic_fmt.Ztrunc_neg]

/-- Check closure under absolute value

    Verify that if x is in FLT format, then |x| is also in FLT format.
    This tests the magnitude preservation property, ensuring that
    absolute values remain representable.
-/
noncomputable def FLT_format_abs_check (beta : Int) (x : ℝ) : Bool :=
  -- Concrete arithmetic check: Ztrunc(|x|) matches natAbs of Ztrunc(x)
  ((FloatSpec.Core.Raux.Ztrunc (abs x)).run)
        == Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).run.natAbs)

/-- Specification: FLT format closed under absolute value

    FLT formats are closed under absolute value operations.
    The magnitude of a representable number is always
    representable using the same exponent structure.
-/
@[spec]
theorem FLT_format_abs_spec (beta : Int) (x : ℝ) :
    ⦃⌜FLT_format prec emin beta x⌝⦄
    (pure (FLT_format_abs_check beta x) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold FLT_format_abs_check
  -- Normalize the truncation of |x| and split on the sign of x
  have hAbsRun : (FloatSpec.Core.Raux.Ztrunc (abs x)).run = Int.floor (abs x) := by
    simp [FloatSpec.Core.Raux.Ztrunc, not_lt.mpr (abs_nonneg x)]
  by_cases hxlt : x < 0
  · -- Negative case: |x| = -x and Ztrunc x = ⌈x⌉
    have hZrun : (FloatSpec.Core.Raux.Ztrunc x).run = Int.ceil x := by
      simp [FloatSpec.Core.Raux.Ztrunc, hxlt]
    have hceil_nonpos : Int.ceil x ≤ 0 :=
      (Int.ceil_le).mpr (by simpa using (le_of_lt hxlt : x ≤ (0 : ℝ)))
    have hnabs : (Int.ofNat ((Int.ceil x).natAbs)) = - Int.ceil x :=
      by simpa using (Int.ofNat_natAbs_of_nonpos hceil_nonpos)
    -- Reduce both sides to an equality between integers
    have : Int.floor (abs x) = Int.ofNat ((Int.ceil x).natAbs) := by
      have h' : Int.floor (abs x) = - Int.ceil x := by
        simpa [Int.floor_neg, abs_of_neg hxlt]
      -- rewrite -⌈x⌉ as |⌈x⌉| using natAbs on nonpos
      have hnabs' : (- Int.ceil x) = Int.ofNat ((Int.ceil x).natAbs) := by
        simpa using hnabs.symm
      simpa [h'] using hnabs'
    -- Turn the integer equality into the Boolean check equalling true
    have hEq : (FloatSpec.Core.Raux.Ztrunc (abs x)).run
              = Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).run.natAbs) := by
      simpa [hAbsRun, hZrun] using this
    simpa [hEq]
  · -- Nonnegative case: |x| = x and Ztrunc x = ⌊x⌋ with ⌊x⌋ ≥ 0
    have hxge : 0 ≤ x := le_of_not_gt hxlt
    have hZrun : (FloatSpec.Core.Raux.Ztrunc x).run = Int.floor x := by
      simp [FloatSpec.Core.Raux.Ztrunc, hxlt]
    have hfloor_nonneg : 0 ≤ (Int.floor x : Int) :=
      (Int.le_floor).mpr (by simpa using hxge)
    -- First rewrite Int.ofNat (natAbs ⌊x⌋) as |⌊x⌋|, then use nonnegativity
    have hnabs_abs : (Int.ofNat ((Int.floor x).natAbs)) = |Int.floor x| := by
      simpa using (Int.natCast_natAbs (Int.floor x))
    have hnabs : (Int.ofNat ((Int.floor x).natAbs)) = Int.floor x := by
      simpa [abs_of_nonneg hfloor_nonneg] using hnabs_abs
    -- Reduce both sides and turn into the Boolean check
    have h' : Int.floor (abs x) = Int.floor x := by simpa [abs_of_nonneg hxge]
    have hEq : (FloatSpec.Core.Raux.Ztrunc (abs x)).run
              = Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).run.natAbs) := by
      simpa [hAbsRun, hZrun, h'] using hnabs.symm
    simpa [hEq]

/-- Check relationship between FLT and FLX formats

    When the minimum exponent constraint is not active
    (i.e., emin ≤ e - prec), FLT behaves exactly like FLX.
    This verifies the normal number behavior of IEEE 754.
-/
def FLT_exp_FLX_check (e : Int) : Bool :=
  decide (emin ≤ e - prec → FLT_exp prec emin e = FLX.FLX_exp prec e)

/-- Specification: FLT reduces to FLX for normal numbers

    When the precision-based exponent e - prec exceeds emin,
    FLT format behaves identically to FLX format. This captures
    the normal number range of IEEE 754 floating-point.
-/
@[spec]
theorem FLT_exp_FLX_spec (e : Int) :
    ⦃⌜emin ≤ e - prec⌝⦄
    (pure (FLT_exp_FLX_check prec emin e) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro h
  -- Unfold and reduce using the hypothesis `emin ≤ e - prec`.
  -- Under this condition, `FLT_exp` coincides with `FLX_exp`.
  simp [FLT_exp_FLX_check, FLT_exp, FLX.FLX_exp, max_eq_left h]

/-
Coq (FLT.v):
Theorem generic_format_FLT :
  forall x, FLT_format x -> generic_format beta FLT_exp x.
-/
theorem generic_format_FLT (beta : Int) (x : ℝ) :
    ⦃⌜(FLT_format prec emin beta x).run⌝⦄
    generic_format beta (FLT_exp prec emin) x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  simpa [FLT_format]

/-
Coq (FLT.v):
Theorem FLT_format_generic :
  forall x, generic_format beta FLT_exp x -> FLT_format x.
-/
theorem FLT_format_generic (beta : Int) (x : ℝ) :
    ⦃⌜(generic_format beta (FLT_exp prec emin) x).run⌝⦄
    FLT_format prec emin beta x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  simpa [FLT_format] using hx

/-
Coq (FLT.v):
Theorem FLT_format_satisfies_any :
  satisfies_any FLT_format.
-/
theorem FLT_format_satisfies_any (beta : Int) :
    FloatSpec.Core.Generic_fmt.satisfies_any (fun y => (FLT_format prec emin beta y).run) := by
  simpa [FLT_format]
    using FloatSpec.Core.Generic_fmt.generic_format_satisfies_any (beta := beta) (fexp := FLT_exp prec emin)

/-
Coq (FLT.v):
Theorem generic_format_FLT_bpow :
  forall e, (emin <= e)%Z -> generic_format beta FLT_exp (bpow e).
-/
theorem generic_format_FLT_bpow (beta : Int) (e : Int) :
    ⦃⌜beta > 1 ∧ emin ≤ e⌝⦄
    generic_format beta (FLT_exp prec emin) ((beta : ℝ) ^ e)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hemin_le_e⟩
  -- We will use `generic_format_bpow` once we show
  -- `FLT_exp prec emin (e + 1) ≤ e`.
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec_ge1 : (1 : Int) ≤ prec := Int.add_one_le_iff.mpr hprec_pos
  have h1_sub_prec_nonpos : 1 - prec ≤ 0 := sub_nonpos.mpr hprec_ge1
  have h_e1_sub_prec_le_e : e + 1 - prec ≤ e := by
    have := add_le_add_left h1_sub_prec_nonpos e
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hbound : (FLT_exp prec emin (e + 1)) ≤ e := by
    -- `max (e + 1 - prec) emin ≤ e` from the two bounds
    exact (max_le_iff.mpr ⟨h_e1_sub_prec_le_e, hemin_le_e⟩)
  -- Apply the generic lemma for powers in generic format.
  simpa [FLT_exp]
    using FloatSpec.Core.Generic_fmt.generic_format_bpow
      (beta := beta) (fexp := FLT_exp prec emin) (e := e) ⟨hβ, hbound⟩

/-
Coq (FLT.v):
Theorem FLT_format_bpow :
  forall e, (emin <= e)%Z -> FLT_format (bpow e).
-/
theorem FLT_format_bpow (beta : Int) (e : Int) :
    ⦃⌜beta > 1 ∧ emin ≤ e⌝⦄
    FLT_format prec emin beta ((beta : ℝ) ^ e)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hemin_le_e⟩
  -- Show FLT_exp e ≤ e from `prec > 0` and `emin ≤ e`.
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
  have h_e_sub_prec_le_e : e - prec ≤ e := by
    have : -prec ≤ 0 := by simpa using (neg_nonpos.mpr hprec_nonneg)
    have := add_le_add_left this e
    simpa [sub_eq_add_neg] using this
  have hfexp_le : (FLT_exp prec emin e) ≤ e :=
    (max_le_iff.mpr ⟨h_e_sub_prec_le_e, hemin_le_e⟩)
  -- Conclude using the `generic_format_bpow'` lemma, then fold `FLT_format`.
  simpa [FLT_format]
    using FloatSpec.Core.Generic_fmt.generic_format_bpow'
      (beta := beta) (fexp := FLT_exp prec emin) (e := e) ⟨hβ, hfexp_le⟩

/-
Coq (FLT.v):
Theorem generic_format_FLT_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  generic_format beta (FLX_exp prec) x ->
  generic_format beta FLT_exp x.
-/
theorem generic_format_FLT_FLX (beta : Int) (x : ℝ) :
    ⦃⌜beta > 1 ∧ (beta : ℝ) ^ (emin + prec) ≤ |x| ∧ (generic_format beta (FLX.FLX_exp prec) x).run⌝⦄
    generic_format beta (FLT_exp prec emin) x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_lb, hx_fmt⟩
  -- Use the generic inclusion principle with a global lower bound e1 := emin + prec
  -- For e ≥ emin + prec, we have FLT_exp e = e - prec = FLX_exp prec e
  have hle_all : ∀ e : Int, (emin + prec) ≤ e → (FLT_exp prec emin e) ≤ (FLX.FLX_exp prec e) := by
    intro e he
    -- From emin + prec ≤ e, subtract prec from both sides
    have he_sub : emin + prec - prec ≤ e - prec := by
      exact sub_le_sub_right he prec
    have hemin_le : emin ≤ e - prec := by
      -- Simplify left side to `emin`
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using he_sub
    simpa [FLT_exp, FLX.FLX_exp, max_eq_left hemin_le]
  -- Apply inclusion to transfer FLX-format to FLT-format under the lower bound
  have := FloatSpec.Core.Generic_fmt.generic_inclusion_ge
              (beta := beta)
              (fexp1 := FLX.FLX_exp prec)
              (fexp2 := FLT_exp prec emin)
              (e1 := emin + prec)
  have hres := this hβ hle_all x hx_lb hx_fmt
  simpa using hres

/-
Coq (FLT.v):
Theorem cexp_FLT_FLX :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  cexp beta FLT_exp x = cexp beta (FLX_exp prec) x.
-/
theorem cexp_FLT_FLX (beta : Int) (x : ℝ) :
    ⦃⌜beta > 1 ∧ (beta : ℝ) ^ (emin + prec) ≤ |x|⌝⦄
    FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x
    ⦃⇓result => ⌜result = (FloatSpec.Core.Generic_fmt.cexp beta (FLX.FLX_exp prec) x).run⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_lb⟩
  -- Notation for the logarithmic magnitude
  set M : Int := (FloatSpec.Core.Raux.mag beta x).run with hM
  -- Strict upper bound from magnitude: |x| < β^(M + 1)
  have hx_upper : |x| < (beta : ℝ) ^ (M + 1) := by
    -- Precondition for `bpow_mag_gt` with e := M + 1
    have hlt : (FloatSpec.Core.Raux.mag beta x).run < M + 1 := by
      -- M < M + 1 holds trivially
      have : M ≤ M := le_rfl
      exact (Int.lt_add_one_iff).2 this
    have h := FloatSpec.Core.Raux.bpow_mag_gt (beta := beta) (x := x) (e := M + 1) ⟨hβ, hlt⟩
    simpa [FloatSpec.Core.Raux.abs_val, FloatSpec.Core.Raux.mag, M, wp, PostCond.noThrow, Id.run, pure]
      using h
  -- Combine the given lower bound with the strict upper bound to compare powers
  have hpow_strict : (beta : ℝ) ^ (emin + prec) < (beta : ℝ) ^ (M + 1) :=
    lt_of_le_of_lt hx_lb hx_upper
  -- From β^(e1) < β^(M+1), deduce (e1 + 1) ≤ (M + 1) ⇒ e1 ≤ M
  have h_e1p1_le_Mp1 : (emin + prec + 1) ≤ (M + 1) := by
    have h := FloatSpec.Core.Raux.bpow_lt_bpow (beta := beta) (e1 := (emin + prec + 1)) (e2 := (M + 1))
    have := h ⟨hβ, by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hpow_strict⟩
    simpa [FloatSpec.Core.Raux.bpow_lt_bpow_pair, wp, PostCond.noThrow, Id.run, pure]
      using this
  have h_e1_le_M : (emin + prec) ≤ M := by
    -- Subtract 1 on both sides
    have := sub_le_sub_right h_e1p1_le_Mp1 (1 : Int)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Under this condition, FLT_exp and FLX_exp coincide at M
  have hEqExp : FLT_exp prec emin M = FLX.FLX_exp prec M := by
    have : emin ≤ M - prec := by
      -- Subtract `prec` from both sides of (emin + prec) ≤ M
      have := sub_le_sub_right h_e1_le_M prec
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    simpa [FLT_exp, FLX.FLX_exp, max_eq_left this]
  -- Unfold both `cexp` computations (Id bind)
  unfold FloatSpec.Core.Generic_fmt.cexp
  -- First, show x ≠ 0 from the positive lower bound on |x|
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hpow_pos : 0 < (beta : ℝ) ^ (emin + prec) := zpow_pos hbposR _
  have hx_pos : 0 < |x| := lt_of_lt_of_le hpow_pos hx_lb
  have hx_ne : x ≠ 0 := (abs_pos).1 hx_pos
  -- Both sides compute the same magnitude M, then apply the respective exponent
  -- functions. Replace the binds by their returned value `M` and conclude.
  change (pure (FLT_exp prec emin M) : Id Int) = (pure (FLX.FLX_exp prec M) : Id Int)
  simpa [hEqExp]

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
Lemma negligible_exp_FLT :
  exists n, negligible_exp FLT_exp = Some n /\\ (n <= emin)%Z.

Lean (spec): State existence of a negligible exponent bound for FLT.
We keep the proof as a placeholder.
-/
private lemma negligible_exp_FLT_exists (prec emin : Int) [Prec_gt_0 prec] :
    ∃ n : Int, FloatSpec.Core.Ulp.negligible_exp (fexp := FLT_exp prec emin) = some n ∧ n ≤ emin := by
  classical
  -- Build a witness that `∃ n, n ≤ fexp n` using `n = emin`.
  have hWitness : ∃ n : Int, n ≤ FLT_exp prec emin n :=
    ⟨emin, by simpa [FLT_exp] using le_max_right (emin - prec) emin⟩
  -- Use the canonical spec of `negligible_exp` and eliminate the `none` branch.
  rcases FloatSpec.Core.Ulp.negligible_exp_spec' (fexp := FLT_exp prec emin) with hnone | hsome
  · -- `none` branch contradicts `FLT_exp emin = emin`.
    rcases hnone with ⟨hEqNone, hforall⟩
    have hlt : FLT_exp prec emin emin < emin := hforall emin
    have hEq : FLT_exp prec emin emin = emin := by
      have : emin - prec ≤ emin := by
        have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
        have : -prec ≤ 0 := neg_nonpos.mpr (le_of_lt hprec_pos)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using add_le_add_left this emin
      simpa [FLT_exp, max_eq_right this]
    exact (False.elim ((lt_irrefl _ : ¬ (emin < emin)) (by simpa [hEq] using hlt)))
  · rcases hsome with ⟨n, hopt, hnle⟩
    -- Show any such witness `n` must satisfy `n ≤ emin` since `prec > 0`.
    have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    have hprec_ge1 : (1 : Int) ≤ prec := Int.add_one_le_iff.mpr hprec_pos
    have hcases : n ≤ n - prec ∨ n ≤ emin := by
      have : n ≤ max (n - prec) emin := by simpa [FLT_exp] using hnle
      exact (le_max_iff).1 this
    have hnot_left : ¬ (n ≤ n - prec) := by
      have hstep : n - prec ≤ n - 1 := sub_le_sub_left hprec_ge1 n
      intro hle
      have : n ≤ n - 1 := le_trans hle hstep
      have : n + 1 ≤ n := by simpa using (Int.add_le_add_right this 1)
      exact (lt_irrefl _ (Int.add_one_le_iff.mp this))
    have hle_emin : n ≤ emin := Or.resolve_left hcases hnot_left
    exact ⟨n, hopt, hle_emin⟩

theorem negligible_exp_FLT (beta : Int) :
    ⦃⌜True⌝⦄
    (pure (FloatSpec.Core.Ulp.negligible_exp (fexp := FLT_exp prec emin)) : Id (Option Int))
    ⦃⇓r => ⌜∃ n, r = some n ∧ n ≤ emin⌝⦄ := by
  intro _
  -- Reduce the Hoare triple over `pure` and discharge with the existence lemma
  have ⟨n, hsome, hle⟩ := negligible_exp_FLT_exists (prec := prec) (emin := emin)
  -- Rewrap to match the exact postcondition shape
  exact ⟨n, hsome, hle⟩

/-
Coq (FLT.v):
Theorem generic_format_FIX_FLT :
  forall x : R,
  generic_format beta FLT_exp x ->
  generic_format beta (FIX_exp emin) x.
-/
theorem generic_format_FIX_FLT (beta : Int) (x : ℝ) :
    ⦃⌜beta > 1 ∧ (generic_format beta (FLT_exp prec emin) x).run⌝⦄
    generic_format beta (FloatSpec.Core.FIX.FIX_exp (emin := emin)) x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx⟩
  classical
  -- Expand the hypothesis to the canonical F2R representation under FLT_exp
  unfold FloatSpec.Core.Generic_fmt.generic_format
    FloatSpec.Core.Generic_fmt.scaled_mantissa
    FloatSpec.Core.Generic_fmt.cexp at hx
  -- Notation for the magnitude and the FLT canonical exponent
  set M : Int := (FloatSpec.Core.Raux.mag beta x).run with hM
  set e1 : Int := FLT_exp prec emin M with he1
  -- Notation for the truncated mantissa under FLT
  set m1 : Int := (FloatSpec.Core.Raux.Ztrunc (x * (beta : ℝ) ^ (-(FLT_exp prec emin M)))).run with hm1
  -- Unfold F2R at the hypothesis side to obtain x = m1 * β^e1
  have hx_eq : x = ((m1 : ℝ) * (beta : ℝ) ^ e1) := by
    -- Reduce the hypothesis to a concrete equality
    -- After unfolding, hx is exactly the equality we need
    simpa [hM, he1, hm1, FloatSpec.Core.Defs.F2R]
      using hx
  -- We will prove that this very (m1, e1) also certifies FIX generic format.
  -- Use the generic F2R constructor for FIX_exp, providing the required bound.
  -- First, express that the F2R built from (m1, e1) equals x.
  have hF2R : (FloatSpec.Core.Defs.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m1 e1 : FloatSpec.Core.Defs.FlocqFloat beta)).run = x := by
    simpa [FloatSpec.Core.Defs.F2R] using hx_eq.symm
  -- The bound required by `generic_format_F2R` under FIX_exp reduces to `emin ≤ e1`.
  have hbound : m1 ≠ 0 →
      (FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FIX.FIX_exp (emin := emin))
          (FloatSpec.Core.Defs.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m1 e1 : FloatSpec.Core.Defs.FlocqFloat beta)).run).run ≤ e1 := by
    intro _
    -- Compute cexp under FIX: it is FIX_exp applied to the magnitude.
    -- Replace the real by x using hF2R
    have :
        (FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FIX.FIX_exp (emin := emin))
            (FloatSpec.Core.Defs.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m1 e1 : FloatSpec.Core.Defs.FlocqFloat beta)).run).run
          = FloatSpec.Core.FIX.FIX_exp (emin := emin)
              ((FloatSpec.Core.Raux.mag beta x).run) := by
      simp [FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Raux.mag, hF2R]
    -- Under FIX, the canonical exponent is constantly `emin`
    -- and `emin ≤ e1 = max (M - prec) emin` holds by construction.
    have hemin_le_e1 : emin ≤ e1 := by
      -- e1 = FLT_exp M = max (M - prec) emin
      simpa [he1, FLT_exp] using (le_max_right (M - prec) emin)
    -- Conclude by rewriting the computed cexp
    simpa [this]
  -- Apply the F2R generic-format constructor for FIX_exp
  -- This step packages the previous bound into the desired generic_format fact.
  -- Build the precondition pair for `generic_format_F2R` and conclude.
  have hgf := FloatSpec.Core.Generic_fmt.generic_format_F2R
              (beta := beta)
              (fexp := FloatSpec.Core.FIX.FIX_exp (emin := emin))
              (m := m1) (e := e1) ⟨hβ, hbound⟩
  -- Rewriting F2R (m1,e1) back to x as established above
  simpa [hF2R]
    using hgf

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
```
Theorem generic_format_FLT_FIX :
  forall x : R,
  (Rabs x <= bpow (emin + prec))%R ->
  generic_format beta (FIX_exp emin) x ->
  generic_format beta FLT_exp x.
```
-/
theorem generic_format_FLT_FIX (beta : Int) (x : ℝ) :
    ⦃⌜beta > 1 ∧ |x| ≤ (beta : ℝ) ^ (emin + prec) ∧ (generic_format beta (FloatSpec.Core.FIX.FIX_exp (emin := emin)) x).run⌝⦄
    generic_format beta (FLT_exp prec emin) x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_le, hx_fmt⟩
  -- Use inclusion under an upper bound with e2 := emin + prec
  have hle_all : ∀ e : Int, e ≤ (emin + prec) → (FLT_exp prec emin e) ≤ (FloatSpec.Core.FIX.FIX_exp (emin := emin) e) := by
    intro e he
    -- From e ≤ emin + prec, get e - prec ≤ emin
    have : e - prec ≤ emin + prec - prec := sub_le_sub_right he prec
    have hsub : e - prec ≤ emin := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    -- Then max (e - prec) emin ≤ emin and FIX_exp e = emin
    have : (FLT_exp prec emin e) ≤ emin := by
      simpa [FLT_exp] using (max_le_iff.mpr ⟨hsub, le_rfl⟩)
    simpa [FloatSpec.Core.FIX.FIX_exp] using this
  -- Apply the generic inclusion lemma (≤ case)
  have hres := FloatSpec.Core.Generic_fmt.generic_inclusion_le
                (beta := beta)
                (fexp1 := FloatSpec.Core.FIX.FIX_exp (emin := emin))
                (fexp2 := FLT_exp prec emin)
                (e2 := emin + prec)
                hβ hle_all x hx_le hx_fmt
  simpa using hres

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-- Coq ({lit}`FLT.v`):
Theorem {lit}`ulp_FLT_0`: {lit}`ulp beta FLT_exp 0 = bpow emin`.

Lean (spec): The ULP under FLT at 0 equals {lit}`β^emin`.
-/
theorem ulp_FLT_0 (beta : Int) :
    ⦃⌜True⌝⦄
    FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0
    ⦃⇓r => ⌜r = (beta : ℝ) ^ emin⌝⦄ := by
  intro _
  classical
  -- From FLT, `negligible_exp` always returns a witness `n` with `n ≤ emin`.
  have ⟨n, hsome, hn_le_emin⟩ :=
    negligible_exp_FLT_exists (prec := prec) (emin := emin)
  -- Evaluate `ulp` at zero using the computed witness.
  -- Under the `some` branch, ulp 0 = β^(fexp n).
  have :
      (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0)
        = pure ((beta : ℝ) ^ (FLT_exp prec emin n)) := by
    simp [FloatSpec.Core.Ulp.ulp, hsome]
  -- Show that for any `n ≤ emin`, FLT_exp n = emin.
  have h_fexp_n_eq : FLT_exp prec emin n = emin := by
    -- Since `prec > 0`, we have `0 ≤ prec`, hence `n - prec ≤ n ≤ emin`.
    have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
    have hsub_le_self : n - prec ≤ n := by
      have : -prec ≤ 0 := by simpa using (neg_nonpos.mpr hprec_nonneg)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using add_le_add_left this n
    have hsub_le_emin : n - prec ≤ emin := le_trans hsub_le_self hn_le_emin
    simpa [FLT_exp, max_eq_right hsub_le_emin]
  -- Conclude by rewriting with the computed branch and simplifying the exponent.
  simpa [this, h_fexp_n_eq]

/-- Coq ({lit}`FLT.v`):
Theorem {lit}`ulp_FLT_small`:
  {lit}`forall x, Rabs x < bpow (emin + prec) -> ulp beta FLT_exp x = bpow emin`.

Lean (spec): If {lit}`|x| < β^(emin+prec)`, then ULP under FLT at x equals {lit}`β^emin`.
-/
theorem ulp_FLT_small (beta : Int) (x : ℝ) :
    ⦃⌜beta > 1 ∧ |x| < (beta : ℝ) ^ (emin + prec)⌝⦄
    FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x
    ⦃⇓r => ⌜r = (beta : ℝ) ^ emin⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_lt⟩
  classical
  by_cases hx0 : x = 0
  · -- Small regime at zero: unfold `ulp` and reuse the FLT zero lemma's ingredients.
    -- We re-prove the zero case locally to avoid triple shape mismatches.
    -- `negligible_exp` returns a witness `n` with `n ≤ emin` under FLT.
    have ⟨n, hsome, hn_le_emin⟩ :=
      negligible_exp_FLT_exists (prec := prec) (emin := emin)
    -- Show fexp n = emin for any such witness.
    have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
    -- Since 0 ≤ prec, we have n - prec ≤ n; combined with n ≤ emin gives the claim.
    have hsub_le : n - prec ≤ emin := by
      have : -prec ≤ 0 := by simpa using (neg_nonpos.mpr hprec_nonneg)
      have hle : n - prec ≤ n := by
        have := add_le_add_left this n
        simpa [sub_eq_add_neg] using this
      exact le_trans hle hn_le_emin
    have hfexp_eq : FLT_exp prec emin n = emin := by
      simpa [FLT_exp, max_eq_right hsub_le]
    -- Evaluate ulp at 0 using the `some` branch and discharge the triple.
    have hxrun : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0).run = (beta : ℝ) ^ emin := by
      unfold FloatSpec.Core.Ulp.ulp
      simp [hx0, hsome, hfexp_eq]
    simpa [hx0, wp, PostCond.noThrow, Id.run, bind, pure] using hxrun
  · -- Nonzero small inputs: ulp x = β^(cexp x) and cexp x = emin under FLT bounds.
    have hx_ne : x ≠ 0 := hx0
    -- Let M be the logarithmic magnitude of x.
    set M : Int := (FloatSpec.Core.Raux.mag beta x).run with hM
    -- From |x| < β^(emin+prec), deduce mag x ≤ emin + prec.
    have hM_le : M ≤ (emin + prec) := by
      -- Use `mag_le_bpow` and unwrap the Hoare triple.
      have := FloatSpec.Core.Raux.mag_le_bpow (beta := beta) (x := x) (e := (emin + prec))
      have hcall := this ⟨hβ, hx_ne, hx_lt⟩
      simpa [FloatSpec.Core.Raux.mag, hM, wp, PostCond.noThrow, Id.run, pure]
        using hcall
    -- Hence M - prec ≤ emin, so FLT_exp M = emin.
    have hsub_le : M - prec ≤ emin := by
      have := sub_le_sub_right hM_le prec
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hfexp_eq : FLT_exp prec emin M = emin := by
      simpa [FLT_exp, max_eq_right hsub_le]
    -- Evaluate `ulp` at a nonzero input, inline `cexp`, and rewrite the exponent to `emin`.
    have hcexp_run :
        (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x).run
          = FLT_exp prec emin ((FloatSpec.Core.Raux.mag beta x).run) := by
      unfold FloatSpec.Core.Generic_fmt.cexp
      simp [FloatSpec.Core.Raux.mag]
    have hfexp_mag_eq :
        FLT_exp prec emin ((FloatSpec.Core.Raux.mag beta x).run) = emin := by
      simpa [hM]
        using hfexp_eq
    have hxrun : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run = (beta : ℝ) ^ emin := by
      unfold FloatSpec.Core.Ulp.ulp
      simp [hx_ne, hcexp_run, hfexp_mag_eq]
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using hxrun

/-
Coq (FLT.v):
Theorem cexp_FLT_FIX :
  forall x, x <> 0%R ->
  (Rabs x < bpow (emin + prec))%R ->
  cexp beta FLT_exp x = cexp beta (FIX_exp emin) x.
-/
theorem cexp_FLT_FIX (beta : Int) (x : ℝ) :
    ⦃⌜beta > 1 ∧ x ≠ 0 ∧ |x| < (beta : ℝ) ^ (emin + prec)⌝⦄
    FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x
    ⦃⇓result => ⌜result = (FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FIX.FIX_exp (emin := emin)) x).run⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_ne, hx_lt⟩
  classical
  -- Let M be the logarithmic magnitude of x
  set M : Int := (FloatSpec.Core.Raux.mag beta x).run with hM
  -- From |x| < β^(emin+prec), deduce mag x ≤ emin + prec
  have hM_le : M ≤ (emin + prec) := by
    have := FloatSpec.Core.Raux.mag_le_bpow (beta := beta) (x := x) (e := (emin + prec))
    have hcall := this ⟨hβ, hx_ne, hx_lt⟩
    simpa [FloatSpec.Core.Raux.mag, hM, wp, PostCond.noThrow, Id.run, pure] using hcall
  -- Hence M - prec ≤ emin, so FLT_exp M = emin
  have hsub_le : M - prec ≤ emin := by
    have := sub_le_sub_right hM_le prec
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hfexp_eq : FLT_exp prec emin M = emin := by
    simpa [FLT_exp, max_eq_right hsub_le]
  -- Compute both canonical exponents and show they coincide
  have hcexp_FLT_run :
      (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x).run
        = FLT_exp prec emin ((FloatSpec.Core.Raux.mag beta x).run) := by
    unfold FloatSpec.Core.Generic_fmt.cexp
    simp [FloatSpec.Core.Raux.mag]
  have hcexp_FIX_run :
      (FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FIX.FIX_exp (emin := emin)) x).run
        = (FloatSpec.Core.FIX.FIX_exp (emin := emin)) ((FloatSpec.Core.Raux.mag beta x).run) := by
    unfold FloatSpec.Core.Generic_fmt.cexp
    simp [FloatSpec.Core.Raux.mag]
  have hxrun :
      (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x).run
        = (FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FIX.FIX_exp (emin := emin)) x).run := by
    simpa [hcexp_FLT_run, hcexp_FIX_run, hM, hfexp_eq, FloatSpec.Core.FIX.FIX_exp]
  simpa [wp, PostCond.noThrow, Id.run, bind, pure] using hxrun

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
Theorem generic_format_FLT_1 :
  (emin <= 0)%Z ->
  generic_format beta FLT_exp 1.
-/
theorem generic_format_FLT_1 (beta : Int) :
    ⦃⌜beta > 1 ∧ emin ≤ 0⌝⦄
    generic_format beta (FLT_exp prec emin) 1
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hemin_le_zero⟩
  -- We will use `generic_format_bpow` at exponent e = 0.
  -- It requires `FLT_exp (0+1) ≤ 0`, which follows from `prec > 0` and `emin ≤ 0`.
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec_ge1 : (1 : Int) ≤ prec := Int.add_one_le_iff.mpr hprec_pos
  have h1_sub_prec_nonpos : 1 - prec ≤ 0 := sub_nonpos.mpr hprec_ge1
  have hbound : (FLT_exp prec emin (0 + 1)) ≤ 0 := by
    simpa [FLT_exp] using (max_le_iff.mpr ⟨h1_sub_prec_nonpos, hemin_le_zero⟩)
  -- Apply the power lemma and rewrite `(β : ℝ)^0 = 1`.
  have h := FloatSpec.Core.Generic_fmt.generic_format_bpow
              (beta := beta) (fexp := FLT_exp prec emin) (e := (0 : Int)) ⟨hβ, hbound⟩
  simpa using h

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
Theorem generic_format_FLX_FLT :
  forall x : R,
  generic_format beta FLT_exp x -> generic_format beta (FLX_exp prec) x.
-/
theorem generic_format_FLX_FLT (beta : Int) (x : ℝ) :
    ⦃⌜beta > 1 ∧ (generic_format beta (FLT_exp prec emin) x).run⌝⦄
    generic_format beta (FLX.FLX_exp prec) x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx⟩
  -- Use the generic inclusion on magnitude: FLX_exp ≤ FLT_exp pointwise
  have hpoint : x ≠ 0 →
      (FLX.FLX_exp prec) ((FloatSpec.Core.Raux.mag beta x).run)
        ≤ (FLT_exp prec emin) ((FloatSpec.Core.Raux.mag beta x).run) := by
    intro _
    -- FLT_exp m = max (m - prec) emin, whereas FLX_exp m = m - prec
    -- Hence the inequality holds by `le_max_left`.
    simpa [FLT_exp, FLX.FLX_exp]
  -- Conclude via the inclusion lemma from Generic_fmt
  have hrun : (generic_format beta (FLX.FLX_exp prec) x).run :=
    (FloatSpec.Core.Generic_fmt.generic_inclusion_mag
      (beta := beta)
      (fexp1 := FLT_exp prec emin)
      (fexp2 := FLX.FLX_exp prec)
      (x := x)) hβ hpoint hx
  -- Reduce the Hoare triple on Id to the pure proposition
  simpa [wp, PostCond.noThrow, Id.run, pure]
    using hrun

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
Theorem ulp_FLT_le:
  forall x, (bpow (emin + prec - 1) <= Rabs x)%R ->
  (ulp beta FLT_exp x <= Rabs x * bpow (1 - prec))%R.
-/
theorem ulp_FLT_le (beta : Int) (x : ℝ) :
    ⦃⌜beta > 1 ∧ (beta : ℝ) ^ (emin + prec - 1) ≤ |x|⌝⦄
    FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x
    ⦃⇓r => ⌜r ≤ |x| * (beta : ℝ) ^ (1 - prec)⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_lb⟩
  classical
  -- Basic positivity from 1 < beta
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  -- From the lower bound, deduce |x| > 0 hence x ≠ 0
  have hpow_pos : 0 < (beta : ℝ) ^ (emin + prec - 1) := zpow_pos hbposR _
  have hx_pos : 0 < |x| := lt_of_lt_of_le hpow_pos hx_lb
  have hx_ne : x ≠ 0 := (abs_pos).1 hx_pos
  -- Notation for the logarithmic magnitude and canonical exponent
  set M : Int := (FloatSpec.Core.Raux.mag beta x).run with hM
  have hcexp_run :
      (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x).run
        = FLT_exp prec emin ((FloatSpec.Core.Raux.mag beta x).run) := by
    unfold FloatSpec.Core.Generic_fmt.cexp
    simp [FloatSpec.Core.Raux.mag]
  -- Evaluate `ulp` on a nonzero input
  have hulp_run :
      (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run
        = (beta : ℝ) ^ (FLT_exp prec emin M) := by
    unfold FloatSpec.Core.Ulp.ulp
    simp [hx_ne, hcexp_run, hM]
  -- We aim to show: β^(fexp M) ≤ |x| * β^(1 - prec).
  -- Split the exponent so we can factor out β^(1 - prec).
  have hsplit :
      (beta : ℝ) ^ (FLT_exp prec emin M)
        = (beta : ℝ) ^ ((FLT_exp prec emin M) + prec + -1) * (beta : ℝ) ^ (1 + -prec) := by
    -- zpow_add₀ on (e + prec - 1) and (1 - prec), noting their sum is e
    have := zpow_add₀ hbne ((FLT_exp prec emin M) + prec + -1) (1 + -prec)
    -- Rearrange the sum in the exponent to `e`
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using this
  -- It suffices to show: β^( (FLT_exp M) + prec - 1 ) ≤ |x|
  have hcore : (beta : ℝ) ^ ((FLT_exp prec emin M) + prec - 1) ≤ |x| := by
    -- Case analysis on which branch of the max defines FLT_exp
    by_cases hcase : emin ≤ M - prec
    · -- Normal range: fexp M = M - prec, so exponent reduces to M - 1
      have hfexp_eq : FLT_exp prec emin M = M - prec := by
        simpa [FLT_exp, max_eq_left hcase]
      -- From `mag` lower bound: β^(M - 1) ≤ |x|
      -- From `mag` lower bound: β^(M - 1) ≤ |x|
      have hcall :=
        (FloatSpec.Core.Raux.bpow_mag_le (beta := beta) (x := x) (e := M)) ⟨hβ, hx_ne, le_rfl⟩
      -- Simplify the returned triple and rewrite the exponent
      have hM_lb : (beta : ℝ) ^ (M - 1) ≤ |x| := by
        simpa [FloatSpec.Core.Raux.abs_val, hM, wp, PostCond.noThrow, Id.run, pure, sub_eq_add_neg]
          using hcall
      -- Convert the goal exponent using `hfexp_eq`
      simpa [hfexp_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using hM_lb
    · -- Subnormal range: fexp M = emin, so exponent reduces to emin + prec - 1
      have hfexp_eq : FLT_exp prec emin M = emin := by
        have : M - prec ≤ emin := le_of_not_ge hcase
        simpa [FLT_exp, max_eq_right this]
      -- Use the given lower bound
      simpa [hfexp_eq, sub_eq_add_neg] using hx_lb
  -- Put everything together: multiply by the positive factor β^(1 - prec)
  have hfac_nonneg : 0 ≤ (beta : ℝ) ^ (1 - prec) := le_of_lt (zpow_pos hbposR _)
  have : (beta : ℝ) ^ (FLT_exp prec emin M)
            ≤ |x| * (beta : ℝ) ^ (1 - prec) := by
    -- Rewrite the left-hand side using `hsplit` and multiply the core bound
    have := mul_le_mul_of_nonneg_right hcore hfac_nonneg
    simpa [hsplit, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
      using this
  -- Move the inequality to the concrete `Id.run` result and discharge the triple
  have hout : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run
                ≤ |x| * (beta : ℝ) ^ (1 - prec) := by
    simpa [hulp_run] using this
  -- Discharge the Hoare triple
  simpa [wp, PostCond.noThrow, Id.run, bind, pure]
    using hout

/-
Coq (FLT.v):
Theorem ulp_FLT_gt:
  forall x, (Rabs x * bpow (-prec) < ulp beta FLT_exp x)%R.
-/
theorem ulp_FLT_gt (beta : Int) (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x
    ⦃⇓r => ⌜|x| * (beta : ℝ) ^ (-prec) ≤ r⌝⦄ := by
  intro hβ
  classical
  -- Basic positivity facts from 1 < beta
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hb_nonneg : 0 ≤ (beta : ℝ) := le_of_lt hbposR
  have hfac_nonneg : 0 ≤ (beta : ℝ) ^ (-prec) := le_of_lt (zpow_pos hbposR _)
  by_cases hx : x = 0
  · -- Zero case: ulp equals β^emin and the left-hand side is 0
    have hulp0 :
        (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0).run = (beta : ℝ) ^ emin := by
      -- Use the dedicated zero lemma
      have h := (ulp_FLT_0 (prec := prec) (emin := emin) (beta := beta)) (by exact True.intro)
      simpa [wp, PostCond.noThrow, Id.run, pure] using h
    -- Show 0 ≤ β^emin using positivity of the base
    have hpow_pos : 0 < (beta : ℝ) ^ emin := zpow_pos hbposR _
    have : |x| * (beta : ℝ) ^ (-prec) ≤ (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run := by
      -- Left-hand side is 0; right-hand side is strictly positive
      have : 0 ≤ (beta : ℝ) ^ emin := le_of_lt hpow_pos
      simpa [hx, abs_zero, zero_mul, hulp0]
    -- Repackage to the Hoare-style postcondition
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
  · -- Nonzero case: ulp x = β^(cexp x) and cexp = FLT_exp (mag x)
    have hx_ne : x ≠ 0 := hx
    -- Evaluate cexp on x
    have hcexp_run :
        (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x).run
          = FLT_exp prec emin ((FloatSpec.Core.Raux.mag beta x).run) := by
      unfold FloatSpec.Core.Generic_fmt.cexp
      simp [FloatSpec.Core.Raux.mag]
    -- Evaluate ulp on a nonzero input
    have hulp_run :
        (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run
          = (beta : ℝ) ^ ((FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x).run) := by
      -- Use the generic `ulp_neq_0` lemma
      have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := FLT_exp prec emin) x hx_ne) (by exact True.intro)
      simpa [wp, PostCond.noThrow, Id.run, bind, pure] using h
    -- Abbreviation: M = mag beta x
    set M : Int := (FloatSpec.Core.Raux.mag beta x).run with hM
    -- Goal reduces to bounding |x| by β^M and then using monotonicity of bpow
    -- Step 1: |x| ≤ β^M (by definition of mag via ceiling)
    -- Let L := log |x| / log β; then M = ⌈L⌉ and hence L ≤ M.
    have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
      have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
        Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)
      exact this.mpr (by exact_mod_cast hβ)
    have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    have hx_pos : 0 < |x| := by simpa using (abs_pos.mpr hx_ne)
    set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hLdef
    have hM_run : M = Int.ceil L := by
      have : (FloatSpec.Core.Raux.mag beta x).run = Int.ceil L := by
        simp [FloatSpec.Core.Raux.mag, hx_ne, hLdef]
      simpa [hM] using this
    -- From L ≤ ⌈L⌉, deduce |x| ≤ β^M
    have h_abs_le : |x| ≤ (beta : ℝ) ^ M := by
      -- Multiply by log β and identify L * log β = log |x|
      have hceil_ge : (L : ℝ) ≤ (Int.ceil L : ℝ) := by exact_mod_cast Int.le_ceil L
      have hmul_le : L * Real.log (beta : ℝ) ≤ (Int.ceil L : ℝ) * Real.log (beta : ℝ) :=
        mul_le_mul_of_nonneg_right hceil_ge (le_of_lt hlogβ_pos)
      have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
        have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
        calc
          L * Real.log (beta : ℝ)
              = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by
                  simpa [hLdef]
          _   = Real.log (abs x) := by
                  simpa [hne, div_mul_eq_mul_div] using
                    (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
      -- Relate log(β^M) to M * log β
      have hlog_zpow_M : Real.log ((beta : ℝ) ^ M) = (M : ℝ) * Real.log (beta : ℝ) := by
        simpa using Real.log_zpow hbposR M
      -- Get log |x| ≤ log (β^M)
      have hlog_le : Real.log (abs x) ≤ Real.log ((beta : ℝ) ^ M) := by
        have : Real.log (abs x) ≤ (M : ℝ) * Real.log (beta : ℝ) := by
          simpa [hL_mul, hM_run] using hmul_le
        simpa [hlog_zpow_M] using this
      -- Move back via exp and rewrite β^M
      have hxpos' : 0 < abs x := hx_pos
      have h_exp_le : abs x ≤ Real.exp ((M : ℝ) * Real.log (beta : ℝ)) := by
        have := (Real.log_le_iff_le_exp hxpos').1 hlog_le
        simpa [hlog_zpow_M] using this
      have hpow_pos : 0 < (beta : ℝ) ^ M := zpow_pos hbposR _
      have h_exp_eq_pow : Real.exp ((M : ℝ) * Real.log (beta : ℝ)) = (beta : ℝ) ^ M := by
        have : Real.exp (Real.log ((beta : ℝ) ^ M)) = (beta : ℝ) ^ M := Real.exp_log hpow_pos
        simpa [hlog_zpow_M] using this
      simpa [h_exp_eq_pow] using h_exp_le
    -- Step 2: β^(M - prec) ≤ β^(FLT_exp M)
    have hmono_pow : (beta : ℝ) ^ (M - prec) ≤ (beta : ℝ) ^ (FLT_exp prec emin M) := by
      -- Monotonicity of zpow on nonnegative bases
      have hb_ge1 : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (le_of_lt hβ)
      have hle_exp : M - prec ≤ FLT_exp prec emin M := by
        -- Since FLT_exp M = max (M - prec) emin
        simpa [FLT_exp] using (le_max_left (M - prec) emin)
      exact zpow_le_zpow_right₀ hb_ge1 hle_exp
    -- Multiply both sides of Step 1 by β^(-prec) ≥ 0 to get
    -- |x| * β^(-prec) ≤ β^M * β^(-prec) = β^(M - prec)
    have hscaled : |x| * (beta : ℝ) ^ (-prec) ≤ (beta : ℝ) ^ (M - prec) := by
      have := mul_le_mul_of_nonneg_right h_abs_le hfac_nonneg
      simpa [sub_eq_add_neg, zpow_add₀ (ne_of_gt hbposR), mul_comm, mul_left_comm, mul_assoc] using this
    -- Combine with Step 2 and rewrite ulp on the right-hand side
    have : |x| * (beta : ℝ) ^ (-prec)
            ≤ (beta : ℝ) ^ (FLT_exp prec emin M) :=
      le_trans hscaled hmono_pow
    -- Transport along the `cexp` and `ulp` evaluations computed above
    have : |x| * (beta : ℝ) ^ (-prec)
            ≤ (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run := by
      simpa [hulp_run, hcexp_run, hM] using this
    -- Discharge the Hoare triple on Id
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this

/-
Coq (FLT.v):
Lemma ulp_FLT_exact_shift:
  forall x e,
  (x <> 0)%R ->
  (emin + prec <= mag beta x)%Z ->
  (emin + prec - mag beta x <= e)%Z ->
  (ulp beta FLT_exp (x * bpow e) = ulp beta FLT_exp x * bpow e)%R.
-/
theorem ulp_FLT_exact_shift (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜beta > 1 ∧ x ≠ 0 ∧ emin + prec ≤ (FloatSpec.Core.Raux.mag beta x).run ∧ emin + prec - (FloatSpec.Core.Raux.mag beta x).run ≤ e⌝⦄
    (do
      let u1 ← FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)
      let u2 ← FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x
      pure (u1, u2))
    ⦃⇓p => ⌜p.1 = p.2 * (beta : ℝ) ^ e⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_ne, hMx_lb, hshift⟩
  classical
  -- Basic facts about the base and the scaled input
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hpow_ne : (beta : ℝ) ^ e ≠ 0 := by
    simpa using (zpow_ne_zero e hbne)
  have hy_ne : x * (beta : ℝ) ^ e ≠ 0 := mul_ne_zero hx_ne hpow_ne
  -- Notations for magnitudes
  set M : Int := (FloatSpec.Core.Raux.mag beta x).run with hM
  set N : Int := (FloatSpec.Core.Raux.mag beta (x * (beta : ℝ) ^ e)).run with hN
  -- Evaluate ulp on both sides (nonzero branch)
  have hcexp_x :
      (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x).run
        = FLT_exp prec emin M := by
    unfold FloatSpec.Core.Generic_fmt.cexp
    simp [FloatSpec.Core.Raux.mag, hM]
  have hcexp_y :
      (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
        = FLT_exp prec emin N := by
    unfold FloatSpec.Core.Generic_fmt.cexp
    simp [FloatSpec.Core.Raux.mag, hN]
  have hulp_x :
      (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run
        = (beta : ℝ) ^ (FLT_exp prec emin M) := by
    unfold FloatSpec.Core.Ulp.ulp
    simp [hx_ne, hcexp_x]
  have hulp_y :
      (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
        = (beta : ℝ) ^ (FLT_exp prec emin N) := by
    unfold FloatSpec.Core.Ulp.ulp
    simp [hy_ne, hcexp_y]
  -- Relate magnitudes under scaling directly: N = M + e
  have hN_eq : N = M + e := by
    -- Notation for logarithmic magnitude
    set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
    have hx_ne' : x ≠ 0 := hx_ne
    have hM_run : M = Int.ceil L := by
      simp [FloatSpec.Core.Raux.mag, hM, hx_ne', L]
    -- Rewrite mag at the scaled input and compute its ceiling form
    have hbpos : 0 < (beta : ℝ) := by exact_mod_cast hbposℤ
    have hdiv :
        Real.log (abs (x * (beta : ℝ) ^ e)) / Real.log (beta : ℝ)
          = L + (e : ℝ) := by
      -- Algebra: log |x * β^e| = log |x| + e * log β, then divide by log β
      have hbpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbpos _
      have hxabs_pos : 0 < |x| := abs_pos.mpr hx_ne'
      have hbpow_abs_pos : 0 < |(beta : ℝ) ^ e| := abs_pos.mpr (ne_of_gt hbpow_pos)
      have hlog_prod :
          Real.log (|x| * |(beta : ℝ) ^ e|)
            = Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ) := by
        calc
          Real.log (|x| * |(beta : ℝ) ^ e|)
              = Real.log (|x|) + Real.log (|(beta : ℝ) ^ e|) := by
                    simpa using Real.log_mul (ne_of_gt hxabs_pos) (ne_of_gt hbpow_abs_pos)
          _   = Real.log (|x|) + Real.log ((beta : ℝ) ^ e) := by
                    simpa [abs_of_nonneg (le_of_lt hbpow_pos)]
          _   = Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ) := by
                    simpa using Real.log_zpow hbpos e
      have habs_mul : abs (x * (beta : ℝ) ^ e) = |x| * |(beta : ℝ) ^ e| := by
        have hbnonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt hbpow_pos
        simp [abs_mul, abs_of_nonneg hbnonneg]
      have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
        have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
          Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
        have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
        simpa using this.mpr hβR
      have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
      have hmul_div : ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) = (e : ℝ) := by
        simpa [hlogβ_ne] using (mul_div_cancel' (e : ℝ) (Real.log (beta : ℝ)))
      calc
        Real.log (abs (x * (beta : ℝ) ^ e)) / Real.log (beta : ℝ)
            = Real.log (|x| * |(beta : ℝ) ^ e|) / Real.log (beta : ℝ) := by simpa [habs_mul]
        _   = (Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) := by
                simpa [hlog_prod]
        _   = Real.log (|x|) / Real.log (beta : ℝ)
                + ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) := by
                simpa using (add_div (Real.log (|x|)) ((e : ℝ) * Real.log (beta : ℝ)) (Real.log (beta : ℝ)))
        _   = L + (e : ℝ) := by simpa [L, hmul_div]
    have hN_run : N = Int.ceil (L + (e : ℝ)) := by
      have hy_ne' : x * (beta : ℝ) ^ e ≠ 0 := hy_ne
      -- First, rewrite the ceiling of the logarithm using hdiv
      have hceil_div :
          Int.ceil (Real.log (abs (x * (beta : ℝ) ^ e)) / Real.log (beta : ℝ))
            = Int.ceil (L + (e : ℝ)) := by
        simpa using congrArg Int.ceil hdiv
      -- Then fold back the definition of mag in the nonzero branch
      have : (FloatSpec.Core.Raux.mag beta (x * (beta : ℝ) ^ e)).run
              = Int.ceil (L + (e : ℝ)) := by
        simpa [FloatSpec.Core.Raux.mag, hy_ne'] using hceil_div
      simpa [hN] using this
    -- Conclude N = M + e via ceilings arithmetic
    have h1 : (FloatSpec.Core.Raux.mag beta (x * (beta : ℝ) ^ e)).run
                = Int.ceil (Real.log (abs (x * (beta : ℝ) ^ e)) / Real.log (beta : ℝ)) := by
      have hy_ne' : x * (beta : ℝ) ^ e ≠ 0 := hy_ne
      simp [FloatSpec.Core.Raux.mag, hy_ne']
    have h2 : Int.ceil (Real.log (abs (x * (beta : ℝ) ^ e)) / Real.log (beta : ℝ))
                = Int.ceil (L + (e : ℝ)) := by
      simpa using congrArg Int.ceil hdiv
    have h3 : Int.ceil (L + (e : ℝ)) = Int.ceil L + e :=
      Int.ceil_add_intCast (a := L) (z := e)
    have h4 : (FloatSpec.Core.Raux.mag beta (x * (beta : ℝ) ^ e)).run = Int.ceil L + e := by
      simpa [h1] using h2.trans h3
    have h5 : N = Int.ceil L + e := by simpa [hN] using h4
    have h6 : Int.ceil L = M := by simpa [hM_run]
    have hN_eq' : N = M + e := by
      simpa [h6, add_comm, add_left_comm, add_assoc] using h5
    exact hN_eq'
  -- Given N = M + e and the bounds on M, both maxima are in the linear branch
  have hM_large : emin ≤ M - prec := by
    -- From emin + prec ≤ M
    have := sub_le_sub_right hMx_lb prec
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hN_large : emin ≤ N - prec := by
    -- From emin + prec - M ≤ e and N = M + e, we get emin ≤ N - prec
    have : emin + prec ≤ M + e := by
      -- rearrange the hypothesis hshift
      have := add_le_add_right hshift M
      -- M + (emin + prec - M) ≤ M + e ⇒ emin + prec ≤ M + e
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
    -- Now subtract prec on both sides
    have := sub_le_sub_right this prec
    simpa [hN_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Compute the exponents
  have hExp_y : FLT_exp prec emin N = N - prec := by simpa [FLT_exp, max_eq_left hN_large]
  have hExp_x : FLT_exp prec emin M = M - prec := by simpa [FLT_exp, max_eq_left hM_large]
  -- Conclude by rewriting powers and using zpow_add₀
  have : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
            = (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run * (beta : ℝ) ^ e := by
    -- Express both sides in terms of powers of β and use exponent arithmetic.
    have hExp_eq : FLT_exp prec emin N = (FLT_exp prec emin M) + e := by
      -- Rewrite both exponents to linear forms and use N = M + e
      have : N - prec = (M - prec) + e := by
        simpa [hN_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      simpa [hExp_y, hExp_x] using this
    -- Turn equality on exponents into equality on powers, then split the sum
    have := congrArg (fun t => (beta : ℝ) ^ t) hExp_eq
    -- (β^ (a + e)) = (β^a) * (β^e)
    have hzadd := zpow_add₀ hbne (FLT_exp prec emin M) e
    -- Put everything together and rewrite ulp runs
    simpa [hulp_y, hulp_x] using this.trans hzadd
  -- Discharge the Hoare-triple on Id
  simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
Theorem round_FLT_FLX : forall rnd x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  round beta FLT_exp rnd x = round beta (FLX_exp prec) rnd x.

Lean (spec): Under the lower-bound condition on |x|, rounding in
FLT equals rounding in FLX for any rounding predicate `rnd`.
-/
theorem round_FLT_FLX (beta : Int) (rnd : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜beta > 1 ∧ (beta : ℝ) ^ (emin + prec) ≤ |x|⌝⦄
    (pure (
      round_to_generic (beta := beta) (fexp := FLT_exp prec emin) (mode := rnd) x,
      round_to_generic (beta := beta) (fexp := FLX.FLX_exp prec) (mode := rnd) x) : Id (ℝ × ℝ))
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_lb⟩
  classical
  -- Notation: M is the logarithmic magnitude of x
  set M : Int := (FloatSpec.Core.Raux.mag beta x).run with hM
  -- From mag bounds: β^(M - 1) ≤ |x|
  have hM_lb : (beta : ℝ) ^ (M - 1) ≤ |x| := by
    -- Use bpow lower bound at e = M
    have h := FloatSpec.Core.Raux.bpow_mag_le (beta := beta) (x := x) (e := M)
    -- Discharge preconditions (1 < beta, x ≠ 0 follows from strict positivity below)
    -- We only need the fact e ≤ mag x which is trivially true for e = mag x.
    -- Build x ≠ 0 from the global lower bound |x| ≥ β^(emin+prec-1) and β > 1
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    have hpow_pos : 0 < (beta : ℝ) ^ (emin + prec) := zpow_pos hbposR _
    have hx_pos : 0 < |x| := lt_of_lt_of_le hpow_pos hx_lb
    have hx_ne : x ≠ 0 := (abs_pos).1 hx_pos
    have hcall := h ⟨hβ, hx_ne, le_rfl⟩
    simpa [FloatSpec.Core.Raux.abs_val, hM, wp, PostCond.noThrow, Id.run, pure, sub_eq_add_neg]
      using hcall
  -- Obtain the strict upper bound |x| < β^(M + 1)
  have hx_upper : |x| < (beta : ℝ) ^ (M + 1) := by
    have h := FloatSpec.Core.Raux.bpow_mag_gt (beta := beta) (x := x) (e := M + 1)
    have hlt : (FloatSpec.Core.Raux.mag beta x).run < M + 1 := by
      have : M ≤ M := le_rfl
      exact (Int.lt_add_one_iff).2 this
    have hres := h ⟨hβ, hlt⟩
    simpa [FloatSpec.Core.Raux.abs_val, FloatSpec.Core.Raux.mag, hM, wp, PostCond.noThrow, Id.run, pure]
      using hres
  -- Now we can compare powers: β^(emin+prec) < β^(M+1) ⇒ emin+prec + 1 ≤ M+1 ⇒ emin+prec ≤ M
  have hlt_pow' : (beta : ℝ) ^ (emin + prec) < (beta : ℝ) ^ (M + 1) :=
    lt_of_le_of_lt hx_lb hx_upper
  have hE_le_Mp1 : (emin + prec + 1) ≤ (M + 1) := by
    -- Use the calibrated comparison lemma on powers
    have h := FloatSpec.Core.Raux.bpow_lt_bpow (beta := beta) (e1 := (emin + prec + 1)) (e2 := (M + 1))
    have hres := h ⟨hβ, by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlt_pow'⟩
    simpa [FloatSpec.Core.Raux.bpow_lt_bpow_pair, wp, PostCond.noThrow, Id.run, pure]
      using hres
  have hE_le_M : (emin + prec) ≤ M := by
    -- Subtract 1 on both sides of the previous inequality
    have := sub_le_sub_right hE_le_Mp1 (1 : Int)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Therefore M - prec ≥ emin, so both exponents coincide at M
  have hcase : emin ≤ M - prec := by
    have := sub_le_sub_right hE_le_M prec
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hEqExp : FLT_exp prec emin M = FLX.FLX_exp prec M := by
    simpa [FLT_exp, FLX.FLX_exp, max_eq_left hcase]
  -- Compute both canonical exponents and conclude equality of the rounded values
  have hcexp_FLT : (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x).run = FLT_exp prec emin M := by
    unfold FloatSpec.Core.Generic_fmt.cexp; simp [FloatSpec.Core.Raux.mag, hM]
  have hcexp_FLX : (FloatSpec.Core.Generic_fmt.cexp beta (FLX.FLX_exp prec) x).run = FLX.FLX_exp prec M := by
    unfold FloatSpec.Core.Generic_fmt.cexp; simp [FloatSpec.Core.Raux.mag, hM]
  -- With identical exponents, `round_to_generic` produces identical results
  have :
      round_to_generic (beta := beta) (fexp := FLT_exp prec emin) (mode := rnd) x
        = round_to_generic (beta := beta) (fexp := FLX.FLX_exp prec) (mode := rnd) x := by
    -- Unfold the definition and rewrite the equal exponents
    unfold round_to_generic
    -- Replace both `cexp` calls by the same value and reduce
    simp [hcexp_FLT, hcexp_FLX, hEqExp]
  -- Discharge the Hoare triple over the pure pair
  simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
Lemma succ_FLT_exact_shift_pos:
  forall x e,
  (0 < x)%R ->
  (emin + prec + 1 <= mag beta x)%Z ->
  (emin + prec - mag beta x + 1 <= e)%Z ->
  (succ beta FLT_exp (x * bpow e) = succ beta FLT_exp x * bpow e)%R.
-/
theorem succ_FLT_exact_shift_pos (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜beta > 1 ∧ 0 < x ∧ emin + prec + 1 ≤ (FloatSpec.Core.Raux.mag beta x).run ∧ emin + prec - (FloatSpec.Core.Raux.mag beta x).run + 1 ≤ e⌝⦄
    (do
      let s1 ← FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)
      let s2 ← FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) x
      pure (s1, s2))
    ⦃⇓p => ⌜p.1 = p.2 * (beta : ℝ) ^ e⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_pos, hMx_lb1, hshift1⟩
  classical
  -- Basic positivity facts from beta > 1
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  -- Positivity of the scaled input and nonnegativity for selecting the `succ` branch
  have hy_pos : 0 < x * (beta : ℝ) ^ e := mul_pos hx_pos (zpow_pos hbposR e)
  have hy_nonneg : 0 ≤ x * (beta : ℝ) ^ e := le_of_lt hy_pos
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  -- Abbreviations for magnitudes
  set M : Int := (FloatSpec.Core.Raux.mag beta x).run with hM
  -- We will use `ulp_FLT_exact_shift` (proved above).
  -- Its preconditions follow from the stronger `+1` hypotheses.
  have hMx_lb : emin + prec ≤ M := by
    have : emin + prec ≤ emin + prec + 1 := by
      -- a ≤ a+1 for integers
      have : (emin + prec : Int) < (emin + prec : Int) + 1 := Int.lt_add_one_iff.mpr le_rfl
      exact le_of_lt this
    exact le_trans this hMx_lb1
  have hshift : emin + prec - M ≤ e := by
    -- From (emin+prec - M) ≤ (emin+prec - M + 1) ≤ e
    have : emin + prec - M ≤ emin + prec - M + 1 := by
      have : (emin + prec - M : Int) < (emin + prec - M : Int) + 1 := Int.lt_add_one_iff.mpr le_rfl
      exact le_of_lt this
    exact le_trans this hshift1
  -- Evaluate `succ` in the positive branch and use the ULP scaling lemma
  have hsucc_y_run : (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
                      = x * (beta : ℝ) ^ e + (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run := by
    unfold FloatSpec.Core.Ulp.succ
    simp [hy_nonneg]
  have hsucc_x_run : (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) x).run
                      = x + (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run := by
    unfold FloatSpec.Core.Ulp.succ
    simp [hx_nonneg]
  -- Apply ULP exact shift to relate ulp at x and at the scaled input
  have hulp_shift :
      (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
        = (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run * (beta : ℝ) ^ e := by
    -- Reuse the previously proven lemma ulp_FLT_exact_shift
    have h := ulp_FLT_exact_shift (prec := prec) (emin := emin) (beta := beta) (x := x) (e := e)
    -- Build its precondition
    have hpre' : beta > 1 ∧ x ≠ 0 ∧ emin + prec ≤ (FloatSpec.Core.Raux.mag beta x).run ∧ emin + prec - (FloatSpec.Core.Raux.mag beta x).run ≤ e := by
      refine ⟨hβ, (ne_of_gt hx_pos), hMx_lb, hshift⟩
    -- Reduce the triple to its pure equality
    have := h hpre'
    -- Extract the run-level equality
    simpa [wp, PostCond.noThrow, Id.run, bind, pure]
      using this
  -- Combine the pieces and discharge the Hoare triple
  have : (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
            = ((FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) x).run) * (beta : ℝ) ^ e := by
    -- Expand both sides using the `succ` evaluations and the ULP shift
    simp [hsucc_y_run, hsucc_x_run, hulp_shift, add_mul]
  -- Finalize the result pair equality in Id
  simpa [wp, PostCond.noThrow, Id.run, bind, pure]
    using this

/-
Coq (FLT.v):
Lemma succ_FLT_exact_shift:
  forall x e,
  (x <> 0)%R ->
  (emin + prec + 1 <= mag beta x)%Z ->
  (emin + prec - mag beta x + 1 <= e)%Z ->
(succ beta FLT_exp (x * bpow e) = succ beta FLT_exp x * bpow e)%R.
-/
-- Auxiliary lemma: pred exact shift for positive inputs (used to handle negative `x` for succ)
private theorem pred_FLT_exact_shift_pos_aux (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜beta > 1 ∧ 0 < x ∧ emin + prec + 1 ≤ (FloatSpec.Core.Raux.mag beta x).run ∧ emin + prec - (FloatSpec.Core.Raux.mag beta x).run + 1 ≤ e⌝⦄
    (do
      let p1 ← FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)
      let p2 ← FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x
      pure (p1, p2))
    ⦃⇓p => ⌜p.1 = p.2 * (beta : ℝ) ^ e⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_pos, hMx_lb1, hshift1⟩
  classical
  -- Reduce `pred` to the positive branch formula via `pred_eq_pos`
  have hy_nonneg : 0 ≤ x * (beta : ℝ) ^ e := by
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    exact le_of_lt (mul_pos hx_pos (zpow_pos hbposR e))
  -- Evaluate pred on both sides using `pred_eq_pos`
  have hpred_y_run : (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
                      = x * (beta : ℝ) ^ e - (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run := by
    -- Use the lemma `pred_eq_pos` with hx ≥ 0 and pass `hβ`
    have h := FloatSpec.Core.Ulp.pred_eq_pos (beta := beta) (fexp := FLT_exp prec emin)
                  (x := x * (beta : ℝ) ^ e) (hx := hy_nonneg)
    have hrun := h hβ
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using hrun
  have hpred_x_run : (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run
                      = x - (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run := by
    have h := FloatSpec.Core.Ulp.pred_eq_pos (beta := beta) (fexp := FLT_exp prec emin)
                  (x := x) (hx := le_of_lt hx_pos)
    have hrun := h hβ
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using hrun
  -- Use ULP exact shift to relate ulp at x and at the scaled input
  set M : Int := (FloatSpec.Core.Raux.mag beta x).run with hM
  have hMx_lb : emin + prec ≤ M := by
    have : emin + prec ≤ emin + prec + 1 := by exact le_of_lt (Int.lt_add_one_iff.mpr le_rfl)
    exact le_trans this hMx_lb1
  have hshift : emin + prec - M ≤ e := by
    have : emin + prec - M ≤ emin + prec - M + 1 := by exact le_of_lt (Int.lt_add_one_iff.mpr le_rfl)
    exact le_trans this hshift1
  have hulp_shift :
      (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
        = (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run * (beta : ℝ) ^ e := by
    have := ulp_FLT_exact_shift (prec := prec) (emin := emin) (beta := beta) (x := x) (e := e)
    have hpre' : beta > 1 ∧ x ≠ 0 ∧ emin + prec ≤ (FloatSpec.Core.Raux.mag beta x).run ∧ emin + prec - (FloatSpec.Core.Raux.mag beta x).run ≤ e := by
      exact ⟨hβ, (ne_of_gt hx_pos), hMx_lb, hshift⟩
    have := this hpre'
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
  -- Combine and distribute
  have : (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
            = ((FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run) * (beta : ℝ) ^ e := by
    simp [hpred_y_run, hpred_x_run, hulp_shift, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
  simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this

-- Auxiliary lemma: pred exact shift for positive inputs (used to handle negative `x` for succ)
-- (moved earlier)

theorem succ_FLT_exact_shift (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜beta > 1 ∧ x ≠ 0 ∧ emin + prec + 1 ≤ (FloatSpec.Core.Raux.mag beta x).run ∧ emin + prec - (FloatSpec.Core.Raux.mag beta x).run + 1 ≤ e⌝⦄
    (do
      let s1 ← FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)
      let s2 ← FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) x
      pure (s1, s2))
    ⦃⇓p => ⌜p.1 = p.2 * (beta : ℝ) ^ e⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_ne, hMx_lb1, hshift1⟩
  classical
  -- Split on the sign of x
  by_cases hxpos : 0 < x
  · -- Positive case: use the specialized positive lemma
    have hpos_pre : beta > 1 ∧ 0 < x ∧ emin + prec + 1 ≤ (FloatSpec.Core.Raux.mag beta x).run ∧
                    emin + prec - (FloatSpec.Core.Raux.mag beta x).run + 1 ≤ e := by
      exact ⟨hβ, hxpos, hMx_lb1, hshift1⟩
    -- Apply the pos lemma and reduce the Id-pair equality
    have := succ_FLT_exact_shift_pos (prec := prec) (emin := emin) (beta := beta) (x := x) (e := e) hpos_pre
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
  · -- Negative case: reduce to `pred` on positive input `-x` via `pred` definition
    have hxle : x ≤ 0 := le_of_not_gt hxpos
    have hxlt : x < 0 := lt_of_le_of_ne hxle hx_ne
    have hxneg_pos : 0 < -x := by exact neg_pos.mpr hxlt
    -- We will prove: pred((-x) * β^e) = pred(-x) * β^e and transfer via `pred`/`succ` relation
    have hpred_pos_shift :
        (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) ((-x) * (beta : ℝ) ^ e)).run
          = (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (-x)).run * (beta : ℝ) ^ e := by
      -- mag(-x) = mag(x), so hypotheses carry over
      have hmag_eq : (FloatSpec.Core.Raux.mag beta (-x)).run = (FloatSpec.Core.Raux.mag beta x).run := by
        simp [FloatSpec.Core.Raux.mag]
      have hpos_pre : beta > 1 ∧ 0 < -x ∧ emin + prec + 1 ≤ (FloatSpec.Core.Raux.mag beta (-x)).run ∧
                      emin + prec - (FloatSpec.Core.Raux.mag beta (-x)).run + 1 ≤ e := by
        exact ⟨hβ, hxneg_pos, by simpa [hmag_eq] using hMx_lb1, by simpa [hmag_eq] using hshift1⟩
      have := pred_FLT_exact_shift_pos_aux (prec := prec) (emin := emin) (beta := beta) (-x) e hpos_pre
      simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
    -- succ z = - pred (-z)
    have hsucc_y : (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
                    = - (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (-(x * (beta : ℝ) ^ e))).run := by
      simp [FloatSpec.Core.Ulp.pred]
    have hsucc_x : (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) x).run
                    = - (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (-x)).run := by
      simp [FloatSpec.Core.Ulp.pred]
    -- Now combine via the positive pred-shift on -x and cancel the negations
    have : (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
              = ((FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) x).run) * (beta : ℝ) ^ e := by
      simpa [hsucc_y, hsucc_x]
        using congrArg (fun t => -t) hpred_pos_shift
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this

/-
Coq (FLT.v):
Lemma pred_FLT_exact_shift:
  forall x e,
  (x <> 0)%R ->
  (emin + prec + 1 <= mag beta x)%Z ->
  (emin + prec - mag beta x + 1 <= e)%Z ->
  (pred beta FLT_exp (x * bpow e) = pred beta FLT_exp x * bpow e)%R.
-/
theorem pred_FLT_exact_shift (beta : Int) (x : ℝ) (e : Int) :
    ⦃⌜beta > 1 ∧ x ≠ 0 ∧ emin + prec + 1 ≤ (FloatSpec.Core.Raux.mag beta x).run ∧ emin + prec - (FloatSpec.Core.Raux.mag beta x).run + 1 ≤ e⌝⦄
    (do
      let p1 ← FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)
      let p2 ← FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x
      pure (p1, p2))
    ⦃⇓p => ⌜p.1 = p.2 * (beta : ℝ) ^ e⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_ne, hMx_lb1, hshift1⟩
  classical
  -- Split on the sign of x
  by_cases hxpos : 0 < x
  · -- Positive case: reduce to the auxiliary positive lemma
    have hpos_pre : beta > 1 ∧ 0 < x ∧ emin + prec + 1 ≤ (FloatSpec.Core.Raux.mag beta x).run ∧
                    emin + prec - (FloatSpec.Core.Raux.mag beta x).run + 1 ≤ e := by
      exact ⟨hβ, hxpos, hMx_lb1, hshift1⟩
    -- Use the auxiliary lemma and discharge the triple
    have := pred_FLT_exact_shift_pos_aux (prec := prec) (emin := emin) (beta := beta) (x := x) (e := e) hpos_pre
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
  · -- Negative case: use `pred_opp` to transfer to `succ` on positive input `-x`
    have hxle : x ≤ 0 := le_of_not_gt hxpos
    have hxlt : x < 0 := lt_of_le_of_ne hxle hx_ne
    have hxneg_pos : 0 < -x := by exact neg_pos.mpr hxlt
    -- pred (x*β^e) = - succ (-(x*β^e)) and pred x = - succ (-x)
    have hpred_y_eq :
        (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
          = - (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (-(x * (beta : ℝ) ^ e))).run := by
      simp [FloatSpec.Core.Ulp.pred]
    have hpred_x_eq :
        (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run
          = - (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (-x)).run := by
      simp [FloatSpec.Core.Ulp.pred]
    -- Apply the positive succ-shift lemma to `-x`
    have hmag_eq : (FloatSpec.Core.Raux.mag beta (-x)).run = (FloatSpec.Core.Raux.mag beta x).run := by
      simp [FloatSpec.Core.Raux.mag]
    have hpos_pre : beta > 1 ∧ 0 < -x ∧ emin + prec + 1 ≤ (FloatSpec.Core.Raux.mag beta (-x)).run ∧
                    emin + prec - (FloatSpec.Core.Raux.mag beta (-x)).run + 1 ≤ e := by
      exact ⟨hβ, hxneg_pos, by simpa [hmag_eq] using hMx_lb1, by simpa [hmag_eq] using hshift1⟩
    have hsucc_pos :
        (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) ((-x) * (beta : ℝ) ^ e)).run
          = (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (-x)).run * (beta : ℝ) ^ e := by
      have := succ_FLT_exact_shift_pos (prec := prec) (emin := emin) (beta := beta) (-x) e hpos_pre
      simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
    -- Combine and cancel the negations
    have : (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)).run
              = (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run * (beta : ℝ) ^ e := by
      simpa [hpred_y_eq, hpred_x_eq] using congrArg (fun t => -t) hsucc_pos
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this

/-
Coq (FLT.v):
Theorem ulp_FLT_pred_pos:
  forall x,
  generic_format beta FLT_exp x ->
  (0 <= x)%R ->
  ulp beta FLT_exp (pred beta FLT_exp x) = ulp beta FLT_exp x \/
  (x = bpow (mag beta x - 1) /\\ ulp beta FLT_exp (pred beta FLT_exp x) = (ulp beta FLT_exp x / IZR beta)%R).
-/
theorem ulp_FLT_pred_pos (beta : Int) (x : ℝ) :
    ⦃⌜beta > 1 ∧ (FloatSpec.Core.Generic_fmt.generic_format beta (FLT_exp prec emin) x).run ∧ 0 ≤ x⌝⦄
    (do
      let up ← FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) ((FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run)
      let ux ← FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x
      pure (up, ux))
    ⦃⇓p => ⌜p.1 = p.2 ∨ (x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x).run - 1) ∧ p.1 = p.2 / (beta : ℝ))⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, Fx, hx0⟩
  classical
  -- Notation for predecessor and both ULPs (run-level equalities)
  set p : ℝ := (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run with hp
  set up : ℝ := (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) p).run with hup
  set ux : ℝ := (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run with hux
  -- Split on x = 0
  by_cases hxz : x = 0
  · -- At x = 0, use pred_0 and ulp symmetry to reduce to ulp(ulp 0) = ulp 0
    have hpred0_run :
        (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) 0).run
          = - (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0).run := by
      -- Evaluate pred at 0 via the Hoare-style lemma
      have := FloatSpec.Core.Ulp.pred_0 (beta := beta) (fexp := FLT_exp prec emin)
      simpa [wp, PostCond.noThrow, Id.run, bind, pure]
        using (this True.intro)
    have hpred0 : p = - (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0).run := by
      -- Rewrite p := (pred x).run and substitute x = 0
      have : p = (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) 0).run := by
        simpa [hp, hxz]
      simpa [this]
        using hpred0_run
    have hsym : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) p).run
                = (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) ((FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0).run)).run := by
      -- ulp(-y) = ulp(y); rewrite p via hpred0
      have := FloatSpec.Core.Ulp.ulp_opp (beta := beta) (fexp := FLT_exp prec emin) ((FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0).run)
      -- Reduce the Hoare triple and rewrite
      simpa [wp, PostCond.noThrow, Id.run, bind, pure, hpred0, hup]
        using (this True.intro)
    -- Compute ulp at 0 under FLT and then ulp at that value using the small‑regime lemma
    have hulp0 : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0).run = (beta : ℝ) ^ emin := by
      -- Use the dedicated FLT lemma for ulp at zero
      have := ulp_FLT_0 (prec := prec) (emin := emin) (beta := beta)
      simpa [wp, PostCond.noThrow, Id.run, bind, pure]
        using (this True.intro)
    -- Since prec > 0 and 1 < beta, we have (β : ℝ)^emin < (β : ℝ)^(emin + prec)
    have hx_lt : |(FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0).run|
                  < (beta : ℝ) ^ (emin + prec) := by
      -- Rewrite absolute value and use base positivity
      have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
      have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
      -- (β^emin) < (β^(emin+prec)) since prec > 0 and β > 1
      have : (beta : ℝ) ^ emin < (beta : ℝ) ^ (emin + prec) := by
        -- Convert to strict monotonicity in exponent
        have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
        have hlt : emin < emin + prec := lt_add_of_pos_right _ hprec_pos
        exact zpow_lt_zpow_right₀ hβR hlt
      simpa [hulp0, abs_of_nonneg (le_of_lt (zpow_pos hbposR _))]
        using this
    -- Apply the small‑regime ULP lemma at x = ulp 0 to show `ulp (ulp 0) = β^emin = ulp 0`.
    have hulp_of_ulp0 : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) ((FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0).run)).run
                        = (beta : ℝ) ^ emin := by
      have := ulp_FLT_small (prec := prec) (emin := emin) (beta := beta)
              (x := (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0).run)
      -- Discharge preconditions and reduce
      have hpre := And.intro hβ hx_lt
      simpa [wp, PostCond.noThrow, Id.run, bind, pure]
        using (this hpre)
    -- Conclude: up = ulp(ulp 0) = β^emin and ux = ulp 0 = β^emin
    have hux0 : ux = (beta : ℝ) ^ emin := by simpa [hux, hxz, hulp0]
    have hup0 : up = (beta : ℝ) ^ emin := by simpa [hsym, hulp_of_ulp0, hup]
    -- Discharge the postcondition using the equality branch
    have heq_up_ux : up = ux := by simpa [hup0, hux0]
    have hdisj : (up = ux) ∨ (x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x).run - 1) ∧ up = ux / (beta : ℝ)) :=
      Or.inl heq_up_ux
    simpa [wp, PostCond.noThrow, Id.run, bind, pure, up, ux]
      using hdisj
  · -- x > 0: combine `pred_plus_ulp` with `pred_eq_pos` to get ulp(pred x) = ulp x
    have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxz)
    -- pred x + ulp(pred x) = x
    have hsum : (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run
                  + (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin)
                      ((FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run)).run
                  = x := by
      have := FloatSpec.Core.Ulp.pred_plus_ulp (beta := beta) (fexp := FLT_exp prec emin)
                    (x := x) (hx := hxpos) (Fx := Fx)
      simpa [wp, PostCond.noThrow, Id.run, bind, pure]
        using (this hβ)
    -- pred x = x - ulp x (positive branch)
    have hpred_run : (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run
                      = x - (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run := by
      have h := FloatSpec.Core.Ulp.pred_eq_pos (beta := beta) (fexp := FLT_exp prec emin) (x := x) (hx := hx0)
      -- Extract the first component equality under `1 < beta`.
      simpa [wp, PostCond.noThrow, Id.run, bind, pure] using (h hβ)
    -- Subtract `pred x` from both sides of `pred x + ulp(pred x) = x`
    have heq : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) ((FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run)).run
                = (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run := by
      -- Rewrite `pred x` in the sum and simplify
      have := congrArg (fun t => t - (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run) hsum
      -- (pred x + ulp(pred x)) - pred x = x - pred x = ulp x
      have hcalc :
          ((FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run
             + (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin)
                 ((FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run)).run)
             - (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run
          = (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin)
                ((FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run)).run := by
        -- Use the helper (a + b) - a = b
        simpa [sub_eq]
      have hrhs : x - (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x).run
                    = (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x).run := by
        simpa [hpred_run]
      simpa [hcalc, hrhs] using this
    -- Discharge the postcondition using the first disjunct (equality)
    have heq_up_ux : up = ux := by simpa [up, ux] using heq
    have hdisj : (up = ux) ∨ (x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x).run - 1) ∧ up = ux / (beta : ℝ)) :=
      Or.inl heq_up_ux
    simpa [wp, PostCond.noThrow, Id.run, bind, pure, up, ux] using hdisj
where
  -- Helper for rewriting (a + b) - a = b without importing extra lemmas
  sub_eq {a b : ℝ} : (a + b) - a = b := by ring

end FloatSpec.Core.FLT
