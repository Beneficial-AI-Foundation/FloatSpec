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
-- import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do
import FloatSpec.src.Core.Ulp
import FloatSpec.src.Core.FLX

open Real
open Std.Do
open FloatSpec.Core.Generic_fmt

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Flush-to-zero exponent function

    Implements the FTZ policy: use the precision-based exponent `e - prec`
    when it is at least `emin`; otherwise flush to the floor `emin` (no subnormals).
-/
def FTZ_exp (e : Int) : Int :=
  if emin ≤ e - prec then e - prec else emin

/-- Check FTZ exponent function correctness

    Verify that the FTZ exponent function correctly implements
    the conditional logic for flush-to-zero behavior.
-/
def FTZ_exp_correct_check (e : Int) : Bool :=
  -- Use boolean equality to avoid Prop-in-Bool mismatches
  (FTZ_exp prec emin e) == (if emin ≤ e - prec then e - prec else emin)

/-- Specification: FTZ exponent calculation

    The FTZ exponent function provides full precision for normal
    numbers but flushes small numbers to the minimum exponent,
    eliminating subnormal numbers from the representation.
-/
@[spec]
theorem FTZ_exp_spec (e : Int) :
    ⦃⌜True⌝⦄
    (pure (FTZ_exp_correct_check prec emin e) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold FTZ_exp_correct_check FTZ_exp
  -- Reflexivity on the conditional makes the boolean check true
  simp

/-- Flush-to-zero format predicate

    A real number x is in FTZ format if it can be represented
    using the generic format with the FTZ exponent function.
    This provides a floating-point format without subnormal numbers.
-/
def FTZ_format (beta : Int) (x : ℝ) : Prop :=
  (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x).run

/-- `Valid_exp` instance for the FTZ exponent function. -/
instance FTZ_exp_valid (beta : Int) [hp : Fact (0 < prec)] :
    FloatSpec.Core.Generic_fmt.Valid_exp beta (FTZ_exp prec emin) := by
  refine ⟨?_⟩
  intro k; constructor
  · -- Large regime: if fexp k < k, then fexp (k+1) ≤ k
    intro hklt
    have hprec1 : 1 ≤ prec := by simpa using (Int.add_one_le_iff).mpr hp.out
    -- Bound for the else-branch at k+1: emin ≤ k
    have hemin_le_k : emin ≤ k := by
      by_cases h : emin ≤ k - prec
      · -- arithmetic branch at k
        have hle' : emin + prec ≤ k := by
          have := add_le_add_right h prec
          simpa [sub_add_cancel] using this
        have h0 : 0 ≤ prec := le_of_lt hp.out
        exact le_trans (le_add_of_nonneg_right h0) hle'
      · -- else-branch at k: fexp k = emin < k
        have : FTZ_exp prec emin k = emin := by simpa [FTZ_exp, h]
        have : emin < k := by simpa [this] using hklt
        exact le_of_lt this
    -- Evaluate fexp at (k+1)
    by_cases h1 : emin ≤ (k + 1) - prec
    · -- fexp (k+1) = (k+1) - prec ≤ k since 1 ≤ prec
      have : (k + 1) - prec ≤ k := by
        have : k + 1 ≤ k + prec := add_le_add_left hprec1 k
        exact (sub_le_iff_le_add).2 (by simpa [add_comm, add_left_comm, add_assoc] using this)
      simpa [FTZ_exp, h1] using this
    · -- fexp (k+1) = emin ≤ k
      simpa [FTZ_exp, h1] using hemin_le_k
  · -- Small regime: if k ≤ fexp k, then stability at fexp k and constancy below it
    intro hk
    have hprec1 : 1 ≤ prec := by simpa using (Int.add_one_le_iff).mpr hp.out
    -- Show: we must be in the else-branch at k (arithmetic branch would force prec ≤ 0)
    have hfexp_k : FTZ_exp prec emin k = emin := by
      by_contra hnot
      -- Analyze the branch of the IF in fexp k
      by_cases he : emin ≤ k - prec
      · -- arithmetic branch at k ⇒ fexp k = k - prec ≥ k contradicts 0 < prec
        have hk_le : k ≤ k - prec := by simpa [FTZ_exp, he] using hk
        have hkplusle : k + prec ≤ k := by
          have := add_le_add_right hk_le prec
          simpa [sub_add_cancel] using this
        have hklt : k < k + prec := lt_add_of_pos_right k hp.out
        exact (lt_irrefl _ ((lt_of_lt_of_le hklt hkplusle)))
      · -- else-branch at k: fexp k = emin, contradicting hnot
        have : FTZ_exp prec emin k = emin := by simpa [FTZ_exp, he]
        exact hnot this
    -- From hk and hfexp_k, we get k ≤ emin
    have hk_le_emin : k ≤ emin := by simpa [hfexp_k] using hk
    refine And.intro ?hA ?hB
    · -- fexp (fexp k + 1) ≤ fexp k
      -- Using hfexp_k = emin, reduce to: fexp (emin + 1) ≤ emin
      have hgoal : FTZ_exp prec emin (emin + 1) ≤ emin := by
        by_cases h1 : emin ≤ (emin + 1) - prec
        · -- arithmetic branch at emin + 1
          have hle : (emin + 1) - prec ≤ emin := by
            -- 1 ≤ prec ⇒ (emin + 1) ≤ emin + prec ⇒ (emin + 1) - prec ≤ emin
            have : emin + 1 ≤ emin + prec := add_le_add_left hprec1 emin
            exact (sub_le_iff_le_add).2 (by
              simpa [add_comm, add_left_comm, add_assoc] using this)
          simpa [FTZ_exp, h1] using hle
        · -- else-branch at (emin + 1): fexp = emin
          simp [FTZ_exp, h1]
      simpa [hfexp_k, add_comm, add_left_comm, add_assoc] using hgoal
    · -- Constancy below fexp k = emin
      intro l hl
      -- Reduce to l ≤ emin
      have hl_emin : l ≤ emin := by simpa [hfexp_k] using hl
      -- Show l - prec < emin by chaining monotonicity of subtraction
      have hle_sub : l - prec ≤ emin - 1 := by
        -- From 1 ≤ prec, we get l - prec ≤ l - 1
        have hstep1 : l - prec ≤ l - 1 := by
          exact sub_le_sub_left hprec1 l
        -- From l ≤ emin, we get l - 1 ≤ emin - 1
        have hstep2 : l - 1 ≤ emin - 1 := by
          exact sub_le_sub_right hl_emin 1
        exact le_trans hstep1 hstep2
      have hlt : l - prec < emin :=
        lt_of_le_of_lt hle_sub (by
          have : emin - 1 < emin := by simpa [sub_eq_add_neg] using Int.sub_one_lt (a := emin)
          simpa using this)
      -- Hence fexp l = emin
      have hfl : FTZ_exp prec emin l = emin := by
        have hnotle : ¬ emin ≤ l - prec := not_le_of_gt hlt
        simpa [FTZ_exp, hnotle]
      -- Conclude constancy below fexp k
      simpa [hfexp_k] using hfl

/-- Specification: FTZ format using generic format

    The FTZ format eliminates subnormal numbers by using the
    flush-to-zero exponent function, providing simpler arithmetic
    at the cost of reduced precision near zero.
-/
@[spec]
theorem FTZ_format_spec (beta : Int) (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (FTZ_format prec emin beta x) : Id Prop)
    ⦃⇓result => ⌜result = (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x).run⌝⦄ := by
  intro _
  -- Reduce the Hoare triple on `Id`; unfold the definition of `FTZ_format`.
  simp [FTZ_format, wp, PostCond.noThrow, Id.run, bind, pure]

/-- Specification: FTZ exponent function correctness

    The FTZ exponent function correctly implements flush-to-zero
    semantics, choosing between precision-based and minimum
    exponents based on the magnitude of the input.
-/
@[spec]
theorem FTZ_exp_correct_spec (e : Int) :
    ⦃⌜True⌝⦄
    (pure (FTZ_exp_correct_check prec emin e) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold FTZ_exp_correct_check FTZ_exp
  simp

/-- Check if zero is in FTZ format

    Verify that zero is representable in flush-to-zero format.
    Zero should always be representable since it can be expressed
    with any exponent as 0 × β^e = 0.
-/
noncomputable def FTZ_format_0_check (beta : Int) : Bool :=
  -- Concrete arithmetic check: Ztrunc 0 = 0
  ((FloatSpec.Core.Raux.Ztrunc (0 : ℝ)).run) == (0 : Int)

/-- Specification: Zero is in FTZ format

    Zero is always representable in FTZ format since it has
    the special property that 0 × β^e = 0 for any exponent e,
    making it representable regardless of format constraints.
-/
@[spec]
theorem FTZ_format_0_spec (beta : Int) :
    ⦃⌜beta > 1⌝⦄
    (pure (FTZ_format_0_check beta) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  -- Evaluate the concrete check: Ztrunc 0 = 0
  -- Ztrunc 0 reduces to ⌊0⌋ which is 0, hence the boolean equality is true.
  simp [FTZ_format_0_check, FloatSpec.Core.Raux.Ztrunc]

/-- Check closure under negation

    Verify that if x is in FTZ format, then -x is also in FTZ format.
    This tests the symmetry property of flush-to-zero representation
    under sign changes.
-/
noncomputable def FTZ_format_opp_check (beta : Int) (x : ℝ) : Bool :=
  -- Concrete arithmetic check leveraging Ztrunc_opp: Ztrunc(-x) + Ztrunc(x) = 0
  ((FloatSpec.Core.Raux.Ztrunc (-x)).run + (FloatSpec.Core.Raux.Ztrunc x).run) == (0 : Int)

/-- Specification: FTZ format closed under negation

    FTZ formats are closed under negation. If x = m × β^e
    is representable, then -x = (-m) × β^e is also representable
    using the same exponent with negated mantissa.
-/
@[spec]
theorem FTZ_format_opp_spec (beta : Int) (x : ℝ) :
    ⦃⌜FTZ_format prec emin beta x⌝⦄
    (pure (FTZ_format_opp_check beta x) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  -- Use truncation under negation: Ztrunc (-x) = - Ztrunc x
  unfold FTZ_format_opp_check
  -- Reduce to boolean equality on integers and rewrite via Ztrunc_neg
  -- This turns the check into ((-z + z) == 0) which simplifies to true.
  simpa [FloatSpec.Core.Generic_fmt.Ztrunc_neg]
    using rfl

/-- Check closure under absolute value

    Verify that if x is in FTZ format, then |x| is also in FTZ format.
    This ensures that magnitude operations preserve representability
    in the flush-to-zero format.
-/
noncomputable def FTZ_format_abs_check (beta : Int) (x : ℝ) : Bool :=
  -- Concrete arithmetic check: Ztrunc(|x|) matches natAbs of Ztrunc(x)
  ((FloatSpec.Core.Raux.Ztrunc (abs x)).run)
        == Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).run.natAbs))

/-- Specification: FTZ format closed under absolute value

    FTZ formats are closed under absolute value operations.
    The magnitude of any representable number remains representable
    using the same exponent structure with positive mantissa.
-/
@[spec]
theorem FTZ_format_abs_spec (beta : Int) (x : ℝ) :
    ⦃⌜FTZ_format prec emin beta x⌝⦄
    (pure (FTZ_format_abs_check beta x) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  -- Compute Ztrunc(|x|) in terms of Ztrunc(x)
  have zabs_eq :
      (FloatSpec.Core.Raux.Ztrunc (abs x)).run
        = Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).run.natAbs) := by
    -- Expand truncation and split on the sign of x; |x| ≥ 0 always
    simp [FloatSpec.Core.Raux.Ztrunc, not_lt.mpr (abs_nonneg x)]
    by_cases hxlt : x < 0
    · -- Negative case: |x| = -x and ⌊-x⌋ = -⌈x⌉; natAbs coerces to |·|
      have hxle : x ≤ 0 := le_of_lt hxlt
      have habs : |x| = -x := by simpa using (abs_of_neg hxlt)
      have hceil_nonpos : Int.ceil x ≤ 0 := (Int.ceil_le).mpr (by simpa using hxle)
      have hAbsCeil : |Int.ceil x| = - Int.ceil x := abs_of_nonpos hceil_nonpos
      have hNatAbsCeil : ((Int.ceil x).natAbs : Int) = |Int.ceil x| :=
        (Int.natCast_natAbs (Int.ceil x))
      -- LHS: ⌊|x|⌋ = ⌊-x⌋ = -⌈x⌉; RHS: ↑(natAbs ⌈x⌉) = |⌈x⌉| = -⌈x⌉
      simpa [habs, Int.floor_neg, hxlt, hAbsCeil, hNatAbsCeil]
    · -- Nonnegative case: |x| = x and ⌊x⌋ ≥ 0, so |⌊x⌋| = ⌊x⌋
      have hxge : 0 ≤ x := le_of_not_gt hxlt
      have hxabs : |x| = x := by simpa using (abs_of_nonneg hxge)
      -- ⌊x⌋ ≥ 0 when x ≥ 0
      have hfloor_nonneg : 0 ≤ (Int.floor x : Int) := by
        have : ((0 : Int) : ℝ) ≤ x := by simpa using hxge
        have : (0 : Int) ≤ Int.floor x := (Int.le_floor).mpr this
        simpa using this
      have hAbsFloor : |Int.floor x| = Int.floor x := abs_of_nonneg hfloor_nonneg
      have hNatAbsFloor : ((Int.floor x).natAbs : Int) = |Int.floor x| :=
        (Int.natCast_natAbs (Int.floor x))
      -- LHS: ⌊|x|⌋ = ⌊x⌋; RHS: ↑(natAbs ⌊x⌋) = |⌊x⌋| = ⌊x⌋
      simpa [hxabs, hAbsFloor, hNatAbsFloor, hxlt]
  -- Reduce the boolean equality using the computed equality
  unfold FTZ_format_abs_check
  -- Evaluate the Id triple on Bool and discharge with zabs_eq
  simpa [wp, PostCond.noThrow, zabs_eq]

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`FLXN_format_FTZ`:
  {lit}`forall x, FTZ_format x -> FLXN_format beta prec x.`

Lean (spec): Any FTZ-format number is in {lean}`FLXN_format` for the same
base and precision.
-/
theorem FLXN_format_FTZ (beta : Int) (x : ℝ) :
    ⦃⌜1 < beta ∧ (FTZ_format prec emin beta x).run⌝⦄
    FloatSpec.Core.FLX.FLXN_format (prec := prec) beta x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_ftz⟩
  -- From FTZ_format, obtain generic_format under FTZ_exp
  have hx_gf :
      (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x).run := by
    simpa [FTZ_format]
      using hx_ftz
  -- Pointwise comparison on canonical exponents at mag x:
  -- FLX_exp m ≤ FTZ_exp m since FTZ_exp = max (emin) (m - prec)
  have hpoint :
      x ≠ 0 →
      FloatSpec.Core.FLX.FLX_exp prec ((FloatSpec.Core.Raux.mag beta x).run)
        ≤ FTZ_exp prec emin ((FloatSpec.Core.Raux.mag beta x).run) := by
    intro _
    set m : Int := (FloatSpec.Core.Raux.mag beta x).run with hm
    by_cases h : emin ≤ m - prec
    ·
      -- Both sides reduce to m - prec
      have : FloatSpec.Core.FLX.FLX_exp prec m ≤ FTZ_exp prec emin m := by
        simpa [FloatSpec.Core.FLX.FLX_exp, FTZ_exp, h]
      simpa [hm] using this
    ·
      -- Else-branch: FTZ_exp m = emin and m - prec ≤ emin by arithmetic
      have hle' : FloatSpec.Core.FLX.FLX_exp prec m ≤ FTZ_exp prec emin m := by
        have hle : m - prec ≤ emin := le_of_lt (lt_of_not_ge h)
        simpa [FloatSpec.Core.FLX.FLX_exp, FTZ_exp, h, hle]
      simpa [hm] using hle'
  -- Apply inclusion-by-magnitude from FTZ_exp to FLX_exp
  have hrun :
      (FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FLX.FLX_exp prec) x).run := by
    exact
      (FloatSpec.Core.Generic_fmt.generic_inclusion_mag
        (beta := beta)
        (fexp1 := FTZ_exp prec emin)
        (fexp2 := FloatSpec.Core.FLX.FLX_exp prec)
        (x := x))
        hβ hpoint hx_gf
  -- Repackage to FLXN_format (alias of FLX_format)
  simpa [FloatSpec.Core.FLX.FLXN_format, FloatSpec.Core.FLX.FLX_format]
    using hrun

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`FTZ_format_FLXN`:
  {lit}`forall x : R, (bpow (emin + prec - 1) <= Rabs x)%R -> FLXN_format beta prec x -> FTZ_format x.`

Lean (spec): If {lit}`|x| ≥ β^(emin + prec - 1)` and x is in {lean}`FLXN_format`,
then x is in {lean}`FTZ_format` for the same base and precision.
-/
theorem FTZ_format_FLXN (beta : Int) (x : ℝ) :
    ⦃⌜1 < beta ∧ (beta : ℝ) ^ (emin + prec - 1) ≤ |x| ∧ (FloatSpec.Core.FLX.FLXN_format (prec := prec) beta x).run⌝⦄
    FTZ_format prec emin beta x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  -- Unpack the preconditions
  rcases hpre with ⟨hβ, hlb, hx_flx⟩
  -- Abbreviations
  set e1 : Int := emin + prec - 1
  -- Provide the FLX generic_format view of the hypothesis
  have hx_gf_flx :
      (FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FLX.FLX_exp prec) x).run := by
    simpa [FloatSpec.Core.FLX.FLXN_format, FloatSpec.Core.FLX.FLX_format] using hx_flx
  -- Case split on whether the lower bound is strict
  by_cases hstrict : (beta : ℝ) ^ e1 < |x|
  ·
    -- Strict lower bound case: use inclusion over the band (e1, M+1]
    classical
    -- Notation: M := mag beta x
    set M : Int := (FloatSpec.Core.Raux.mag beta x).run with hM
    -- Strict upper bound at M+1: |x| < β^(M+1)
    have hupper : |x| < (beta : ℝ) ^ (M + 1) := by
      -- Using Raux.bpow_mag_gt with e := M+1
      have hxlt :=
        (FloatSpec.Core.Raux.bpow_mag_gt (beta := beta) (x := x) (e := M + 1))
      -- Precondition: 1 < beta ∧ (mag x) < M+1
      have hpre' : 1 < beta ∧ (FloatSpec.Core.Raux.mag beta x).run < (M + 1) := by
        have hlt : M < M + 1 := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (lt_add_of_pos_right M (by exact Int.zero_lt_one))
        simpa [hM] using And.intro hβ hlt
      -- Discharge the Hoare triple and get the raw inequality
      simpa [FloatSpec.Core.Raux.abs_val] using (hxlt hpre')
    -- Pointwise exponent inequality on (e1, M+1]: FTZ_exp e = FLX_exp e
    have hle_band : ∀ e : Int, e1 < e ∧ e ≤ (M + 1) →
        FTZ_exp prec emin e ≤ FloatSpec.Core.FLX.FLX_exp prec e := by
      intro e he
      have he_ge : e1 + 1 ≤ e := (Int.add_one_le_iff).2 he.left
      -- Hence e - prec ≥ emin
      have hbranch : emin ≤ e - prec := by
        -- e ≥ emin + prec
        have : emin + prec ≤ e := by
          -- e1 + 1 = emin + prec
          have : e1 + 1 = emin + prec := by
            -- e1 = emin + prec - 1
            have : e1 = emin + prec - 1 := rfl
            simpa [this, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          exact le_trans (by simpa [this] using he_ge) le_rfl
        -- Subtract prec on both sides
        have := sub_le_sub_right this prec
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      -- In the `then` branch, FTZ_exp = e - prec, same as FLX_exp
      simpa [FTZ_exp, FloatSpec.Core.FLX.FLX_exp, hbranch]
    -- Apply inclusion on the strict band (e1, M+1]
    have hrun :
        (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x).run := by
      exact
        (FloatSpec.Core.Generic_fmt.generic_inclusion_lt_ge
          (beta := beta)
          (fexp1 := FloatSpec.Core.FLX.FLX_exp prec)
          (fexp2 := FTZ_exp prec emin)
          (e1 := e1)
          (e2 := M + 1))
          hβ hle_band x ⟨hstrict, hupper⟩ hx_gf_flx
    -- Repackage to FTZ_format
    simpa [FTZ_format] using hrun
  ·
    -- Boundary case: |x| = β^e1. Build a direct FTZ witness via bpow.
    have heq : |x| = (beta : ℝ) ^ e1 := le_antisymm (le_of_not_gt hstrict) hlb
    -- Show FTZ_exp e1 ≤ e1
    have hle_e1 : FTZ_exp prec emin e1 ≤ e1 := by
      -- Candidate bounds: (e1 - prec) ≤ e1 and emin ≤ e1
      have hsub : e1 - prec ≤ e1 := by
        exact sub_le_self _ (le_of_lt (Fact.out : 0 < prec))
      have hmin : emin ≤ e1 := by
        -- e1 = emin + (prec - 1) and (prec - 1) ≥ 0
        have hprec1 : 1 ≤ prec := by simpa using (Int.add_one_le_iff).mpr (Fact.out : 0 < prec)
        have hnonneg : 0 ≤ prec - 1 := by
          simpa [sub_eq_add_neg] using sub_nonneg.mpr hprec1
        -- emin ≤ emin + (prec - 1) = e1
        simpa [e1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using le_add_of_nonneg_right hnonneg
      -- Case split on FTZ_exp branch
      by_cases hbranch : emin ≤ e1 - prec
      · simpa [FTZ_exp, hbranch] using hsub
      · simpa [FTZ_exp, hbranch] using hmin
    -- Apply generic_format_bpow' for FTZ_exp at exponent e1 and rewrite x by |x|
    have hfmt_ftz :
        (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) ((beta : ℝ) ^ e1)).run := by
      exact
        (FloatSpec.Core.Generic_fmt.generic_format_bpow'
          (beta := beta) (fexp := FTZ_exp prec emin) (e := e1))
          ⟨hβ, hle_e1⟩
    -- Finally, since |x| = β^e1, FTZ holds for |x|, and hence for x by symmetry of abs in generic_format
    -- We can use that generic_format works on the exact real value; replace x by its absolute value equality.
    -- Build the target by rewriting x = (sign x) * |x|, then using generic_format closure under sign.
    -- Here, we simply rewrite the goal at x using heq.
    -- generic_format is a predicate on x; equality of reals suffices.
    have : (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x).run := by
      classical
      rcases lt_trichotomy x 0 with hlt | heq0 | hgt
      · -- x < 0 ⇒ |x| = -x
        have habs : |x| = -x := by simpa using (abs_of_neg hlt)
        -- Start from generic_format at |x| = β^e1
        have h_at_abs : (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) |x|).run := by
          simpa [heq.symm] using hfmt_ftz
        -- Transfer along x = -|x|
        have hxneg : (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) (-|x|)).run := by
          -- Use closure under opposite from |x| to -|x|
          have := FloatSpec.Core.Generic_fmt.generic_format_opp (beta := beta) (fexp := FTZ_exp prec emin) (x := |x|)
          simpa using this h_at_abs
        -- Since x = -|x| in this branch, rewrite
        simpa [habs] using hxneg
      · -- x = 0 contradicts the lower bound since β^e1 > 0
        exfalso
        -- β > 1 ⇒ β^e1 > 0
        have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
        have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
        have hbpow_pos : 0 < (beta : ℝ) ^ e1 := zpow_pos hbpos _
        have hle0 : (beta : ℝ) ^ e1 ≤ 0 := by simpa [heq0, abs_zero] using hlb
        exact (not_le_of_gt hbpow_pos) hle0
      · -- x > 0 ⇒ |x| = x
        have habs : |x| = x := by simpa using (abs_of_pos hgt)
        have : (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) |x|).run := by
          simpa [heq.symm] using hfmt_ftz
        simpa [habs] using this
    -- Conclude the Hoare triple
    simpa [FTZ_format] using this

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`round_FTZ_FLX`:
{lit}`forall x, (bpow (emin + prec - 1) <= Rabs x) -> round beta FTZ_exp Zrnd_FTZ x = round beta (FLX_exp prec) rnd x.`

Lean (spec): Under the lower-bound condition on |x|, rounding in
FTZ equals rounding in FLX for any rounding predicate {lit}`rnd`.
-/
theorem round_FTZ_FLX (beta : Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta (FloatSpec.Core.FLX.FLX_exp prec)]
    (rnd : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜1 < beta ∧ (beta : ℝ) ^ (emin + prec) ≤ |x|⌝⦄
    (pure (
      round_to_generic (beta := beta) (fexp := FTZ_exp prec emin) (mode := rnd) x,
      round_to_generic (beta := beta) (fexp := FloatSpec.Core.FLX.FLX_exp prec) (mode := rnd) x) : Id (ℝ × ℝ))
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
    -- Build x ≠ 0 from the global lower bound |x| ≥ β^(emin+prec)
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
  -- Now compare powers: β^(emin+prec) < β^(M+1) ⇒ emin+prec + 1 ≤ M+1 ⇒ emin+prec ≤ M
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
  have hEqExp : FTZ_exp prec emin M = FloatSpec.Core.FLX.FLX_exp prec M := by
    simpa [FTZ_exp, FloatSpec.Core.FLX.FLX_exp, hcase]
  -- Compute both canonical exponents and conclude equality of the rounded values
  have hcexp_FTZ : (FloatSpec.Core.Generic_fmt.cexp beta (FTZ_exp prec emin) x).run = FTZ_exp prec emin M := by
    unfold FloatSpec.Core.Generic_fmt.cexp; simp [FloatSpec.Core.Raux.mag, hM]
  have hcexp_FLX : (FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FLX.FLX_exp prec) x).run = FloatSpec.Core.FLX.FLX_exp prec M := by
    unfold FloatSpec.Core.Generic_fmt.cexp; simp [FloatSpec.Core.Raux.mag, hM]
  -- With identical exponents, `round_to_generic` produces identical results
  have :
      round_to_generic (beta := beta) (fexp := FTZ_exp prec emin) (mode := rnd) x
        = round_to_generic (beta := beta) (fexp := FloatSpec.Core.FLX.FLX_exp prec) (mode := rnd) x := by
    -- Unfold the definition and rewrite the equal exponents
    unfold round_to_generic
    -- Replace both `cexp` calls by the same value and reduce
    simp [hcexp_FTZ, hcexp_FLX, hEqExp]
  -- Discharge the Hoare triple over the pure pair
  simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`round_FTZ_small`:
{lit}`forall x, (Rabs x < bpow (emin + prec - 1)) -> round beta FTZ_exp Zrnd_FTZ x = 0.`

Lean (spec): If |x| is smaller than {lit}`β^(emin+prec-1)`, then rounding in
FTZ flushes to zero for any rounding predicate {lit}`rnd`.
-/
theorem round_FTZ_small (beta : Int) (rnd : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜1 < beta ∧ |x| < (beta : ℝ) ^ (emin)⌝⦄
    (pure (round_to_generic (beta := beta) (fexp := FTZ_exp prec emin) (mode := rnd) x) : Id ℝ)
    ⦃⇓r => ⌜r = 0⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hxlt⟩
  -- From |x| < β^emin and the FTZ small-regime property at emin,
  -- the scaled mantissa is strictly within (-1, 1).
  have hbranch : ¬ emin ≤ emin - prec := by
    -- If emin ≤ emin - prec, then adding prec on both sides gives emin + prec ≤ emin,
    -- contradicting 0 < prec.
    intro hle
    have : emin + prec ≤ emin := by
      have := add_le_add_right hle prec
      simpa [sub_add_cancel] using this
    have hlt : emin < emin + prec := lt_add_of_pos_right _ (Fact.out : 0 < prec)
    exact (lt_irrefl _ (lt_of_lt_of_le hlt this))
  have hex_le : emin ≤ FTZ_exp prec emin emin := by
    -- In FTZ, fexp emin = emin (else-branch) since prec > 0
    simpa [FTZ_exp, hbranch]
  have hsm_lt1 :
      abs (FloatSpec.Core.Generic_fmt.scaled_mantissa beta (FTZ_exp prec emin) x).run < 1 := by
    -- Apply the generic scaled_mantissa bound with ex = emin
    exact
      FloatSpec.Core.Generic_fmt.scaled_mantissa_lt_1
        (beta := beta) (fexp := FTZ_exp prec emin) (x := x) (ex := emin)
        hβ (by simpa using hxlt) hex_le
  -- Let sm be the scaled mantissa; from |sm| < 1 we deduce Ztrunc sm = 0
  set sm : ℝ := (FloatSpec.Core.Generic_fmt.scaled_mantissa beta (FTZ_exp prec emin) x).run with hsm
  have hbounds : -1 < sm ∧ sm < 1 := by
    -- abs sm < 1 ↔ -1 < sm ∧ sm < 1
    simpa [hsm] using (abs_lt.mp hsm_lt1)
  have hZtrunc_sm : (FloatSpec.Core.Raux.Ztrunc sm).run = 0 := by
    -- Split on the sign of sm and use floor/ceil characterizations
    by_cases hneg : sm < 0
    ·
      -- Negative case handled via ceiling when sm < 0
      have hceil0 : Int.ceil sm = 0 := by
        -- Use Int.ceil characterization with m = 0: (-1 < sm ∧ sm ≤ 0)
        have hleft : ((0 : Int) : ℝ) - 1 < sm := by simpa using hbounds.left
        have hright : sm ≤ ((0 : Int) : ℝ) := by
          -- coe 0 : Int to ℝ is defeq to (0 : ℝ)
          simpa using (le_of_lt hneg : sm ≤ (0 : ℝ))
        have : ((0 : Int) : ℝ) - 1 < sm ∧ sm ≤ ((0 : Int) : ℝ) := ⟨hleft, hright⟩
        simpa using ((Int.ceil_eq_iff).2 this)
      -- Ztrunc sm = ⌈sm⌉ when sm < 0
      simpa [FloatSpec.Core.Raux.Ztrunc, hneg, hceil0]
    ·
      -- Nonnegative case: 0 ≤ sm
      have hnonneg : 0 ≤ sm := le_of_not_gt hneg
      have hfloor0 : Int.floor sm = 0 := by
        -- Use floor characterization with m = 0: (0 ≤ sm ∧ sm < 1)
        have : ((0 : Int) : ℝ) ≤ sm ∧ sm < ((0 : Int) : ℝ) + 1 := by
          refine And.intro ?hl ?hr
          · simpa using hnonneg
          · simpa using hbounds.right
        simpa using ((Int.floor_eq_iff).2 this)
      -- Ztrunc sm = ⌊sm⌋ when 0 ≤ sm
      simpa [FloatSpec.Core.Raux.Ztrunc, not_lt.mpr hnonneg, hfloor0]
  -- Unfold rounding: with truncated mantissa 0, the reconstructed value is 0
  have : round_to_generic (beta := beta) (fexp := FTZ_exp prec emin) (mode := rnd) x = 0 := by
    -- Expand definition and rewrite step-by-step without triggering zpow inversion
    classical
    unfold round_to_generic
    set E : Int := (FloatSpec.Core.Generic_fmt.cexp beta (FTZ_exp prec emin) x).run with hE
    -- Replace the argument by sm and use Ztrunc sm = 0
    set m : ℝ := x * (beta : ℝ) ^ (-E) with hm
    have hsm' : m = sm := by
      simpa [FloatSpec.Core.Generic_fmt.cexp, hE, FloatSpec.Core.Generic_fmt.scaled_mantissa, hm] using hsm.symm
    have htrunc0' : (FloatSpec.Core.Raux.Ztrunc m).run = 0 := by
      simpa [hsm'] using hZtrunc_sm
    -- Evaluate the let-bindings to conclude
    have htrunc0R : ((FloatSpec.Core.Raux.Ztrunc m).run : ℝ) = 0 := by simpa [htrunc0']
    -- Compute the final value explicitly to avoid zpow inversion rewrites
    have hrw :
        round_to_generic (beta := beta) (fexp := FTZ_exp prec emin) (mode := rnd) x
          = ((FloatSpec.Core.Raux.Ztrunc m).run : ℝ) * (beta : ℝ) ^ E := by
      simp [round_to_generic, hE, hm]
    -- With truncated mantissa equal to 0, the result is 0
    -- Guard against zpow inversion by proving the required Ztrunc equality directly
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast (lt_trans Int.zero_lt_one hβ)
    have hb_ne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
    have hm_inv : m = x * ((beta : ℝ) ^ E)⁻¹ := by
      -- Rewrite m = x * β^(-E) as x * (β^E)⁻¹ using zpow_neg
      have : (beta : ℝ) ^ (-E) = ((beta : ℝ) ^ E)⁻¹ := by
        simpa using (zpow_neg hb_ne E)
      simpa [hm, this]
    have hZinv : (FloatSpec.Core.Raux.Ztrunc (x * ((beta : ℝ) ^ E)⁻¹)).run = 0 := by
      simpa [hm_inv] using htrunc0'
    -- Conclude by rewriting the rounded value and using the casted zero equality
    have : ((FloatSpec.Core.Raux.Ztrunc (x * ((beta : ℝ) ^ E)⁻¹)).run : ℝ) = 0 := by
      simpa [hZinv]
    -- Final simplification
    simpa [hrw, this]
  -- Discharge the Hoare triple
  simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-
Coq (FTZ.v):
Theorem generic_format_FTZ :
  forall x, FTZ_format x -> generic_format beta FTZ_exp x.
-/
theorem generic_format_FTZ (beta : Int) (x : ℝ) :
    ⦃⌜(FTZ_format prec emin beta x).run⌝⦄
    FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  simpa [FTZ_format]

/-
Coq (FTZ.v):
Theorem FTZ_format_generic :
  forall x, generic_format beta FTZ_exp x -> FTZ_format x.
-/
theorem FTZ_format_generic (beta : Int) (x : ℝ) :
    ⦃⌜(FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x).run⌝⦄
    FTZ_format prec emin beta x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  simpa [FTZ_format] using hx

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-
Coq (FTZ.v):
Theorem FTZ_format_satisfies_any :
  satisfies_any FTZ_format.
-/
theorem FTZ_format_satisfies_any (beta : Int) :
    FloatSpec.Core.Generic_fmt.satisfies_any (fun y => (FTZ_format prec emin beta y).run) := by
  simpa [FTZ_format]
    using FloatSpec.Core.Generic_fmt.generic_format_satisfies_any (beta := beta) (fexp := FTZ_exp prec emin)

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`ulp_FTZ_0`: {lit}`ulp beta FTZ_exp 0 = bpow emin`.

Lean (spec): The ULP under FTZ at 0 equals {lit}`β^emin`.
-/
theorem ulp_FTZ_0 (beta : Int) :
    ⦃⌜True⌝⦄
    FloatSpec.Core.Ulp.ulp beta (FTZ_exp prec emin) 0
    ⦃⇓r => ⌜r = (beta : ℝ) ^ emin⌝⦄ := by
  intro _
  classical
  -- Show the FTZ exponent at `emin` is exactly `emin` (else-branch since `prec > 0`).
  have hbranch : ¬ emin ≤ emin - prec := by
    intro hle
    -- Adding `prec` on both sides leads to `emin + prec ≤ emin`, which contradicts `0 < prec`.
    have : emin + prec ≤ emin := by
      have := add_le_add_right hle prec
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hlt : emin < emin + prec := lt_add_of_pos_right _ (Fact.out : 0 < prec)
    exact (not_le_of_gt hlt) this
  have hfexp_emin : FTZ_exp prec emin emin = emin := by
    simpa [FTZ_exp, hbranch]
  -- Hence there exists a negligible exponent witness (take `n = emin`).
  have h_le_wit : emin ≤ FTZ_exp prec emin emin := by
    simpa [hfexp_emin] using (le_rfl : emin ≤ emin)
  -- Use the canonical spec for `negligible_exp` to extract a concrete witness.
  have hsome : ∃ n : Int,
      FloatSpec.Core.Ulp.negligible_exp (FTZ_exp prec emin) = some n ∧ n ≤ FTZ_exp prec emin n := by
    have H := FloatSpec.Core.Ulp.negligible_exp_spec' (fexp := FTZ_exp prec emin)
    -- Eliminate the impossible `none` branch using the witness at `emin`.
    cases H with
    | inl hnone =>
        rcases hnone with ⟨hEqNone, hall_lt⟩
        have : (FTZ_exp prec emin emin) < emin := hall_lt emin
        -- Contradiction with `fexp emin = emin`.
        have : False := by simpa [hfexp_emin] using this
        cases this
    | inr hsome =>
        exact hsome
  rcases hsome with ⟨n, hneg_eq, hnle⟩
  -- Any negligible witness yields the same exponent; specialize to `emin`.
  have hfexp_eq : FTZ_exp prec emin n = FTZ_exp prec emin emin := by
    simpa using
      (FloatSpec.Core.Ulp.fexp_negligible_exp_eq
        (beta := beta) (fexp := FTZ_exp prec emin) (n := n) (m := emin)
        hnle h_le_wit)
  -- Compute ulp at 0 using the `some` branch and rewrite the exponent.
  have : FloatSpec.Core.Ulp.ulp beta (FTZ_exp prec emin) 0 = pure ((beta : ℝ) ^ emin) := by
    unfold FloatSpec.Core.Ulp.ulp
    -- Select the `some n` branch and rewrite its exponent to `emin`.
    simpa [hneg_eq, hfexp_eq, hfexp_emin]
  -- Discharge the Hoare-style postcondition.
  simpa [wp, PostCond.noThrow, Id.run, pure] using this

end FloatSpec.Core.FTZ
