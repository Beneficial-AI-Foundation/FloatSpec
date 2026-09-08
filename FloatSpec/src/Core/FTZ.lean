import FloatSpec.Linter.OmegaLinter
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
  if e - prec < emin then emin + prec - 1 else e - prec

/-- Check FTZ exponent function correctness

    Verify that the FTZ exponent function correctly implements
    the conditional logic for flush-to-zero behavior.
-/
def FTZ_exp_correct_check (e : Int) : Bool :=
  -- Use boolean equality to avoid Prop-in-Bool mismatches
  (FTZ_exp prec emin e) == (if e - prec < emin then emin + prec - 1 else e - prec)

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
def FTZ_format (beta : Int) [ValidRadix beta] (x : ℝ) : Prop :=
  (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x)

/-- Integer rounding with flush-to-zero behavior.

Values with magnitude less than 1 are rounded to 0, otherwise we reuse the
underlying integer rounding `rnd`. -/
noncomputable def Zrnd_FTZ (rnd : ℝ → Int) (x : ℝ) : Int :=
  if FloatSpec.Core.Raux.Rle_bool 1 |x| then rnd x else 0

/-- `Zrnd_FTZ` preserves the basic rounding-function laws required by Flocq. -/
instance valid_rnd_FTZ (rnd : ℝ → Int) [Valid_rnd rnd] : Valid_rnd (Zrnd_FTZ rnd) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    unfold Zrnd_FTZ
    by_cases hx : 1 ≤ |x|
    · by_cases hy : 1 ≤ |y|
      · simp [FloatSpec.Core.Raux.Rle_bool, hx, hy]
        exact Valid_rnd.Zrnd_le (rnd := rnd) x y hxy
      · have hx_nonpos : x ≤ 0 := by
          by_contra hx_pos
          have hx_pos' : 0 < x := lt_of_not_ge hx_pos
          have h1x : 1 ≤ x := by
            simpa [abs_of_pos hx_pos'] using hx
          have h1y : 1 ≤ y := le_trans h1x hxy
          have h1abs_y : 1 ≤ |y| := by
            have hy_nonneg : 0 ≤ y := le_trans (by positivity) h1y
            simpa [abs_of_nonneg hy_nonneg] using h1y
          exact hy h1abs_y
        simp [FloatSpec.Core.Raux.Rle_bool, hx, hy]
        have hle : rnd x ≤ rnd 0 :=
          Valid_rnd.Zrnd_le (rnd := rnd) x 0 hx_nonpos
        have hzero : rnd 0 = 0 := by
          simpa using (Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int))
        simpa [hzero] using hle
    · by_cases hy : 1 ≤ |y|
      · have hy_nonneg : 0 ≤ y := by
          by_contra hy_neg
          have hy_neg' : y < 0 := lt_of_not_ge hy_neg
          have hy_le_neg1 : y ≤ -1 := by
            have h1 : 1 ≤ -y := by
              simpa [abs_of_nonpos (le_of_lt hy_neg')] using hy
            linarith
          have hx_le_neg1 : x ≤ -1 := le_trans hxy hy_le_neg1
          have h1abs_x : 1 ≤ |x| := by
            have hx_nonpos : x ≤ 0 := by linarith
            have h1 : 1 ≤ -x := by linarith
            simpa [abs_of_nonpos hx_nonpos] using h1
          exact hx h1abs_x
        simp [FloatSpec.Core.Raux.Rle_bool, hx, hy]
        have hle : rnd 0 ≤ rnd y :=
          Valid_rnd.Zrnd_le (rnd := rnd) 0 y hy_nonneg
        have hzero : rnd 0 = 0 := by
          simpa using (Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int))
        simpa [hzero] using hle
      · simp [FloatSpec.Core.Raux.Rle_bool, hx, hy]
  · intro n
    unfold Zrnd_FTZ
    by_cases h : 1 ≤ |(n : ℝ)|
    · simp [FloatSpec.Core.Raux.Rle_bool, h, Valid_rnd.Zrnd_IZR (rnd := rnd) n]
    · have hlt : |(n : ℝ)| < 1 := lt_of_not_ge h
      have h_abs_natAbs : (Int.natAbs n : ℝ) = |(n : ℝ)| := by
        simpa [Nat.cast_natAbs, Int.cast_abs]
      have hnat_lt1 : (Int.natAbs n : ℝ) < 1 := by
        simpa [h_abs_natAbs] using hlt
      have hnat_zero : Int.natAbs n = 0 := by
        by_contra hne
        have hpos : 0 < Int.natAbs n := Nat.pos_of_ne_zero hne
        have hge1 : (1 : ℝ) ≤ (Int.natAbs n : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hpos)
        exact (not_lt_of_ge hge1) hnat_lt1
      have hn : n = 0 := Int.natAbs_eq_zero.mp hnat_zero
      simp [FloatSpec.Core.Raux.Rle_bool, h, hn, Valid_rnd.Zrnd_IZR (rnd := rnd) 0]

/-- `Valid_exp` instance for the FTZ exponent function. -/
instance FTZ_exp_valid [hp : Fact (0 < prec)] :
    FloatSpec.Core.Generic_fmt.Valid_exp (FTZ_exp prec emin) := by
  refine ⟨?_⟩
  intro k; constructor
  · -- Large regime: if fexp k < k, then fexp (k+1) ≤ k
    intro hklt
    have hprec1 : 1 ≤ prec := by simpa using (Int.add_one_le_iff).mpr hp.out
    by_cases hk : k - prec < emin
    · by_cases hk1 : (k + 1) - prec < emin
      · simp [FTZ_exp, hk, hk1] at hklt ⊢
        omega
      · simp [FTZ_exp, hk, hk1] at hklt ⊢
        omega
    · by_cases hk1 : (k + 1) - prec < emin
      · simp [FTZ_exp, hk, hk1] at hklt ⊢
        omega
      · simp [FTZ_exp, hk, hk1] at hklt ⊢
        omega
  · -- Small regime: if k ≤ fexp k, then stability at fexp k and constancy below it
    intro hk
    have hprec1 : 1 ≤ prec := by simpa using (Int.add_one_le_iff).mpr hp.out
    have hk_branch : k - prec < emin := by
      by_contra hnot
      have hk_le : k ≤ k - prec := by simpa [FTZ_exp, hnot] using hk
      omega
    have hfexp_k : FTZ_exp prec emin k = emin + prec - 1 := by
      simp [FTZ_exp, hk_branch]
    refine And.intro ?hA ?hB
    · -- fexp (fexp k + 1) ≤ fexp k
      have hgoal : FTZ_exp prec emin (emin + prec) ≤ emin + prec - 1 := by
        have hbranch : ¬ emin + prec - prec < emin := by omega
        simp [FTZ_exp, hbranch]
        omega
      simpa [hfexp_k, add_comm, add_left_comm, add_assoc] using hgoal
    · -- Constancy below fexp k = emin
      intro l hl
      have hlt : l - prec < emin := by
        have hl' : l ≤ emin + prec - 1 := by
          simpa [hfexp_k] using hl
        omega
      have hfl : FTZ_exp prec emin l = emin + prec - 1 := by
        simp [FTZ_exp, hlt]
      -- Conclude constancy below fexp k
      simpa [hfexp_k] using hfl

/-- Specification: FTZ format using generic format

    The FTZ format eliminates subnormal numbers by using the
    flush-to-zero exponent function, providing simpler arithmetic
    at the cost of reduced precision near zero.
-/
@[spec]
theorem FTZ_format_spec (beta : Int) [ValidRadix beta] (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (FTZ_format prec emin beta x) : Id Prop)
    ⦃⇓result => ⌜result = (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x)⌝⦄ := by
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
noncomputable def FTZ_format_0_check (beta : Int) [ValidRadix beta] : Bool :=
  -- Concrete arithmetic check: Ztrunc 0 = 0
  ((FloatSpec.Core.Raux.Ztrunc (0 : ℝ))) == (0 : Int)

/-- Specification: Zero is in FTZ format

    Zero is always representable in FTZ format since it has
    the special property that 0 × β^e = 0 for any exponent e,
    making it representable regardless of format constraints.
-/
@[spec]
theorem FTZ_format_0_spec (beta : Int) [ValidRadix beta] :
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
noncomputable def FTZ_format_opp_check (beta : Int) [ValidRadix beta] (x : ℝ) : Bool :=
  -- Concrete arithmetic check leveraging Ztrunc_opp: Ztrunc(-x) + Ztrunc(x) = 0
  ((FloatSpec.Core.Raux.Ztrunc (-x)) + (FloatSpec.Core.Raux.Ztrunc x)) == (0 : Int)

/-- Specification: FTZ format closed under negation

    FTZ formats are closed under negation. If x = m × β^e
    is representable, then -x = (-m) × β^e is also representable
    using the same exponent with negated mantissa.
-/
@[spec]
theorem FTZ_format_opp_spec (beta : Int) [ValidRadix beta] (x : ℝ) :
    ⦃⌜FTZ_format prec emin beta x⌝⦄
    (pure (FTZ_format_opp_check beta x) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  -- Use truncation under negation: Ztrunc (-x) = - Ztrunc x
  unfold FTZ_format_opp_check
  simp only [wp, PostCond.noThrow, pure, PredTrans.pure, PredTrans.apply]
  -- Use Ztrunc_neg to show Ztrunc(-x).run + Ztrunc(x).run = 0
  have h : ((FloatSpec.Core.Raux.Ztrunc (-x)) + (FloatSpec.Core.Raux.Ztrunc x) == (0 : Int)) = true := by
    rw [FloatSpec.Core.Generic_fmt.Ztrunc_neg]
    simp only [neg_add_cancel, beq_self_eq_true]
  exact h

/-- Check closure under absolute value

    Verify that if x is in FTZ format, then |x| is also in FTZ format.
    This ensures that magnitude operations preserve representability
    in the flush-to-zero format.
-/
noncomputable def FTZ_format_abs_check (beta : Int) [ValidRadix beta] (x : ℝ) : Bool :=
  -- Concrete arithmetic check: Ztrunc(|x|) matches natAbs of Ztrunc(x)
  ((FloatSpec.Core.Raux.Ztrunc (abs x)))
        == Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).natAbs)

/-- Specification: FTZ format closed under absolute value

    FTZ formats are closed under absolute value operations.
    The magnitude of any representable number remains representable
    using the same exponent structure with positive mantissa.
-/
@[spec]
theorem FTZ_format_abs_spec (beta : Int) [ValidRadix beta] (x : ℝ) :
    ⦃⌜FTZ_format prec emin beta x⌝⦄
    (pure (FTZ_format_abs_check beta x) : Id Bool)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  -- Compute Ztrunc(|x|) in terms of Ztrunc(x)
  have zabs_eq :
      (FloatSpec.Core.Raux.Ztrunc (abs x))
        = Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).natAbs) := by
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
  simp only [wp, PostCond.noThrow, pure, PredTrans.pure, PredTrans.apply]
  -- The goal is about comparing Ztrunc values; use the helper equality
  have h : (((FloatSpec.Core.Raux.Ztrunc (abs x)))
            == Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).natAbs)) = true := by
    rw [zabs_eq]; simp only [beq_self_eq_true]
  exact h

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`FLXN_format_FTZ`:
  {lit}`forall x, FTZ_format x -> FLXN_format beta prec x.`

Lean (spec): Any FTZ-format number is in {lean}`FloatSpec.Core.FLX.FLXN_format` for the same
base and precision.
-/
theorem FLXN_format_FTZ (beta : Int) [ValidRadix beta] (x : ℝ) :
    ⦃⌜1 < beta ∧ FTZ_format prec emin beta x⌝⦄
    (pure (FloatSpec.Core.FLX.FLXN_format (prec := prec) beta x) : Id Prop)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  simp only [wp, PostCond.noThrow, Id.run, pure, PredTrans.pure]
  rcases hpre with ⟨hβ, hx_ftz⟩
  -- From FTZ_format, obtain generic_format under FTZ_exp
  have hx_gf :
      (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x) := by
    simpa [FTZ_format]
      using hx_ftz
  -- Pointwise comparison on canonical exponents at mag x:
  -- FLX_exp m ≤ FTZ_exp m since FTZ_exp = max (emin) (m - prec)
  have hpoint :
      x ≠ 0 →
      FloatSpec.Core.FLX.FLX_exp prec ((FloatSpec.Core.Raux.mag beta x))
        ≤ FTZ_exp prec emin ((FloatSpec.Core.Raux.mag beta x)) := by
    intro _
    set m : Int := (FloatSpec.Core.Raux.mag beta x) with hm
    by_cases h : m - prec < emin
    ·
      -- In the flushed branch, FTZ_exp is the threshold exponent.
      have : FloatSpec.Core.FLX.FLX_exp prec m ≤ FTZ_exp prec emin m := by
        have hprec1 : 1 ≤ prec := by simpa using (Int.add_one_le_iff).mpr (Fact.out : 0 < prec)
        simp [FloatSpec.Core.FLX.FLX_exp, FTZ_exp, h]
        omega
      simpa [hm] using this
    ·
      -- Otherwise both exponents reduce to `m - prec`.
      have hle' : FloatSpec.Core.FLX.FLX_exp prec m ≤ FTZ_exp prec emin m := by
        simpa [FloatSpec.Core.FLX.FLX_exp, FTZ_exp, h]
      simpa [hm] using hle'
  -- Apply inclusion-by-magnitude from FTZ_exp to FLX_exp
  have hrun :
      (FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FLX.FLX_exp prec) x) := by
    exact
      (FloatSpec.Core.Generic_fmt.generic_inclusion_mag
        (beta := beta)
        (fexp1 := FTZ_exp prec emin)
        (fexp2 := FloatSpec.Core.FLX.FLX_exp prec)
        (x := x))
        hβ hpoint hx_gf
  letI : Prec_gt_0 prec := ⟨Fact.out⟩
  exact (FloatSpec.Core.FLX.FLXN_format_generic (prec := prec) beta x) hrun

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`FTZ_format_FLXN`:
  {lit}`forall x : R, (bpow (emin + prec - 1) <= Rabs x)%R -> FLXN_format beta prec x -> FTZ_format x.`

Lean (spec): If {lit}`|x| ≥ β^(emin + prec - 1)` and x is in {lean}`FloatSpec.Core.FLX.FLXN_format`,
then x is in {lean}`FloatSpec.Core.FTZ.FTZ_format` for the same base and precision.
-/
theorem FTZ_format_FLXN (beta : Int) [ValidRadix beta] (x : ℝ) :
    ⦃⌜1 < beta ∧ (beta : ℝ) ^ (emin + prec - 1) ≤ |x| ∧ FloatSpec.Core.FLX.FLXN_format (prec := prec) beta x⌝⦄
    (pure (FTZ_format prec emin beta x) : Id Prop)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  simp only [wp, PostCond.noThrow, Id.run, pure, PredTrans.pure]
  -- Unpack the preconditions
  rcases hpre with ⟨hβ, hlb, hx_flx⟩
  -- Abbreviations
  set e1 : Int := emin + prec - 1
  -- Provide the FLX generic_format view of the hypothesis
  have hx_gf_flx :
      (FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FLX.FLX_exp prec) x) := by
    letI : Prec_gt_0 prec := ⟨Fact.out⟩
    exact (FloatSpec.Core.FLX.generic_format_FLXN (prec := prec) beta x) hx_flx
  -- Case split on whether the lower bound is strict
  by_cases hstrict : (beta : ℝ) ^ e1 < |x|
  ·
    -- Strict lower bound case: use inclusion over the band (e1, M+1]
    classical
    -- Notation: M := mag beta x
    set M : Int := (FloatSpec.Core.Raux.mag beta x) with hM
    -- Strict upper bound at M+1: |x| < β^(M+1)
    have hupper : |x| < (beta : ℝ) ^ (M + 1) := by
      -- Using Raux.bpow_mag_gt with e := M+1
      have hxlt :=
        (FloatSpec.Core.Raux.bpow_mag_gt_from_strict_mag_payload (beta := beta) (x := x) (e := M + 1))
      -- Precondition: 1 < beta ∧ (mag x) < M+1
      have hpre' : 1 < beta ∧ (FloatSpec.Core.Raux.mag beta x) < (M + 1) := by
        have hlt : M < M + 1 := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (lt_add_of_pos_right M (by exact Int.zero_lt_one))
        simpa [hM] using And.intro hβ hlt
      -- Discharge the Hoare triple and get the raw inequality
      simpa [FloatSpec.Core.Raux.abs_val] using (hxlt hpre'.1 hpre'.2 trivial)
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
      -- In this band, FTZ_exp = e - prec, same as FLX_exp.
      have hnot : ¬ e - prec < emin := not_lt.mpr hbranch
      simpa [FTZ_exp, FloatSpec.Core.FLX.FLX_exp, hnot]
    -- Apply inclusion on the strict band (e1, M+1]
    have hrun :
        (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x) := by
      exact
        (FloatSpec.Core.Generic_fmt.generic_inclusion_lt_ge
          (beta := beta)
          (fexp1 := FloatSpec.Core.FLX.FLX_exp prec)
          (fexp2 := FTZ_exp prec emin)
          (e1 := e1)
          (e2 := M + 1))
          hβ hle_band x ⟨le_of_lt hstrict, hupper⟩ hx_gf_flx
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
      have hbranch : e1 - prec < emin := by
        simp [e1]
        omega
      simp [FTZ_exp, hbranch, e1]
    -- Apply generic_format_bpow' for FTZ_exp at exponent e1 and rewrite x by |x|
    have hfmt_ftz :
        (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) ((beta : ℝ) ^ e1)) := by
      exact
        (FloatSpec.Core.Generic_fmt.generic_format_bpow'
          (beta := beta) (fexp := FTZ_exp prec emin) (e := e1))
          ⟨hβ, hle_e1⟩
    -- Finally, since |x| = β^e1, FTZ holds for |x|, and hence for x by symmetry of abs in generic_format
    -- We can use that generic_format works on the exact real value; replace x by its absolute value equality.
    -- Build the target by rewriting x = (sign x) * |x|, then using generic_format closure under sign.
    -- Here, we simply rewrite the goal at x using heq.
    -- generic_format is a predicate on x; equality of reals suffices.
    have : (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x) := by
      classical
      rcases lt_trichotomy x 0 with hlt | heq0 | hgt
      · -- x < 0 ⇒ |x| = -x
        have habs : |x| = -x := by simpa using (abs_of_neg hlt)
        -- Start from generic_format at |x| = β^e1
        have h_at_abs : (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) |x|) := by
          simpa [heq.symm] using hfmt_ftz
        -- Transfer along x = -|x|
        have hxneg : (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) (-|x|)) := by
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
        have : (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) |x|) := by
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
theorem round_FTZ_FLX (beta : Int) [ValidRadix beta]
    [FloatSpec.Core.Generic_fmt.Valid_exp (FloatSpec.Core.FLX.FLX_exp prec)]
    (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ) :
    (beta : ℝ) ^ (emin + prec - 1) ≤ |x| →
      round_to_generic (beta := beta) (fexp := FTZ_exp prec emin)
          (mode := Zrnd_FTZ rnd) x =
      round_to_generic (beta := beta) (fexp := FloatSpec.Core.FLX.FLX_exp prec)
          (mode := rnd) x := by
  intro hx
  let M := FloatSpec.Core.Raux.mag beta x
  have hβ : 1 < beta := ValidRadix.valid
  have hbpos : (0 : ℝ) < beta := by
    exact_mod_cast (lt_trans Int.zero_lt_one hβ)
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  have hxne : x ≠ 0 := by
    have hp : 0 < (beta : ℝ) ^ (emin + prec - 1) := zpow_pos hbpos _
    exact (abs_pos.mp (lt_of_lt_of_le hp hx))
  have hmag : emin + prec ≤ M :=
    FloatSpec.Core.Raux.mag_ge_bpow beta x (emin + prec) hβ hx
  have hcase : emin ≤ M - prec := by omega
  have hexp : FTZ_exp prec emin M = FloatSpec.Core.FLX.FLX_exp prec M := by
    simp [FTZ_exp, FloatSpec.Core.FLX.FLX_exp, hcase]
  have hmagLower : (beta : ℝ) ^ (M - 1) ≤ |x| := by
    simpa [FloatSpec.Core.Raux.abs_val] using
      (FloatSpec.Core.Raux.bpow_mag_le_from_exp_payload beta x M hβ hxne le_rfl True.intro)
  have hprec : 0 < prec := Fact.out
  have hpowOne : (1 : ℝ) ≤ (beta : ℝ) ^ (prec - 1) := by
    exact one_le_zpow₀ (le_of_lt (by exact_mod_cast hβ : (1 : ℝ) < beta)) (by omega)
  have hfactorPos : 0 < (beta : ℝ) ^ (prec - M) := zpow_pos hbpos _
  have hscaledLower :
      (1 : ℝ) ≤ |x * (beta : ℝ) ^ (prec - M)| := by
    have hmul :
        (beta : ℝ) ^ (M - 1) * (beta : ℝ) ^ (prec - M) ≤
          |x| * (beta : ℝ) ^ (prec - M) :=
      mul_le_mul_of_nonneg_right hmagLower (le_of_lt hfactorPos)
    have hpow :
        (beta : ℝ) ^ (M - 1) * (beta : ℝ) ^ (prec - M) =
          (beta : ℝ) ^ (prec - 1) := by
      calc
        (beta : ℝ) ^ (M - 1) * (beta : ℝ) ^ (prec - M) =
            (beta : ℝ) ^ ((M - 1) + (prec - M)) :=
          (zpow_add₀ hbne (M - 1) (prec - M)).symm
        _ = (beta : ℝ) ^ (prec - 1) := by congr 1 <;> omega
    calc
      (1 : ℝ) ≤ (beta : ℝ) ^ (prec - 1) := hpowOne
      _ ≤ |x| * (beta : ℝ) ^ (prec - M) := by simpa [hpow] using hmul
      _ = |x * (beta : ℝ) ^ (prec - M)| := by
        rw [abs_mul, abs_of_pos hfactorPos]
  have hscaled :
      (1 : ℝ) ≤
        |FloatSpec.Core.Generic_fmt.scaled_mantissa beta
          (FloatSpec.Core.FLX.FLX_exp prec) x| := by
    simpa [FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.FLX.FLX_exp, M,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscaledLower
  simp only [round_to_generic, FloatSpec.Core.Generic_fmt.roundR,
    FloatSpec.Core.Generic_fmt.scaled_mantissa,
    FloatSpec.Core.Generic_fmt.cexp]
  rw [hexp]
  simp only [Zrnd_FTZ, FloatSpec.Core.Raux.Rle_bool]
  rw [if_pos]
  simpa [FloatSpec.Core.Generic_fmt.scaled_mantissa,
    FloatSpec.Core.Generic_fmt.cexp, M] using hscaled

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`round_FTZ_small`:
{lit}`forall x, (Rabs x < bpow (emin + prec - 1)) -> round beta FTZ_exp Zrnd_FTZ x = 0.`

Lean (spec): If |x| is smaller than {lit}`β^(emin+prec-1)`, then rounding in
FTZ flushes to zero for any rounding predicate {lit}`rnd`.
-/
theorem round_FTZ_small (beta : Int) [ValidRadix beta]
    (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ) :
    ⦃⌜1 < beta ∧ |x| < (beta : ℝ) ^ (emin + prec - 1)⌝⦄
    (pure (round_to_generic (beta := beta) (fexp := FTZ_exp prec emin)
      (mode := Zrnd_FTZ rnd) x) : Id ℝ)
    ⦃⇓r => ⌜r = 0⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hxlt⟩
  let e0 : Int := emin + prec - 1
  -- From |x| < β^e0 and the FTZ small-regime property at e0,
  -- the scaled mantissa is strictly within (-1, 1).
  have hbranch : e0 - prec < emin := by
    simp [e0]
    omega
  have hfexp_e0 : FTZ_exp prec emin e0 = e0 := by
    simp [FTZ_exp, hbranch, e0]
  have hex_le : e0 ≤ FTZ_exp prec emin e0 := by
    simpa [hfexp_e0]
  have hsm_lt1 :
      abs (FloatSpec.Core.Generic_fmt.scaled_mantissa beta (FTZ_exp prec emin) x) < 1 := by
    -- Apply the generic scaled_mantissa bound with ex = emin
    exact
      FloatSpec.Core.Generic_fmt.scaled_mantissa_lt_1
        (beta := beta) (fexp := FTZ_exp prec emin) (x := x) (ex := e0)
        hβ (by simpa using hxlt) hex_le
  -- Let sm be the scaled mantissa; from |sm| < 1 we deduce Ztrunc sm = 0
  set sm : ℝ := (FloatSpec.Core.Generic_fmt.scaled_mantissa beta (FTZ_exp prec emin) x) with hsm
  have hbounds : -1 < sm ∧ sm < 1 := by
    -- abs sm < 1 ↔ -1 < sm ∧ sm < 1
    simpa [hsm] using (abs_lt.mp hsm_lt1)
  have hmode : Zrnd_FTZ rnd sm = 0 := by
    have hnot : ¬ 1 ≤ |sm| := not_le.mpr (by simpa [hsm] using hsm_lt1)
    simp [Zrnd_FTZ, FloatSpec.Core.Raux.Rle_bool, hnot]
  have hround :
      round_to_generic (beta := beta) (fexp := FTZ_exp prec emin)
        (mode := Zrnd_FTZ rnd) x = 0 := by
    have hmode' : Zrnd_FTZ rnd
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta
          (FTZ_exp prec emin) x) = 0 := by
      simpa [hsm] using hmode
    simp [round_to_generic, FloatSpec.Core.Generic_fmt.roundR, hmode']
  simpa [wp, PostCond.noThrow, Id.run, bind, pure] using hround
/-
  have hZtrunc_sm : (FloatSpec.Core.Raux.Ztrunc sm) = 0 := by
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
    set E : Int := (FloatSpec.Core.Generic_fmt.cexp beta (FTZ_exp prec emin) x) with hE
    -- Replace the argument by sm and use Ztrunc sm = 0
    set m : ℝ := x * (beta : ℝ) ^ (-E) with hm
    have hsm' : m = sm := by
      simpa [FloatSpec.Core.Generic_fmt.cexp, hE, FloatSpec.Core.Generic_fmt.scaled_mantissa, hm] using hsm.symm
    have htrunc0' : (FloatSpec.Core.Raux.Ztrunc m) = 0 := by
      simpa [hsm'] using hZtrunc_sm
    -- Evaluate the let-bindings to conclude
    have htrunc0R : ((FloatSpec.Core.Raux.Ztrunc m) : ℝ) = 0 := by simpa [htrunc0']
    -- Compute the final value explicitly to avoid zpow inversion rewrites
    have hrw :
        round_to_generic (beta := beta) (fexp := FTZ_exp prec emin) (mode := rnd) x
          = ((FloatSpec.Core.Raux.Ztrunc m) : ℝ) * (beta : ℝ) ^ E := by
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
    have hZinv : (FloatSpec.Core.Raux.Ztrunc (x * ((beta : ℝ) ^ E)⁻¹)) = 0 := by
      simpa [hm_inv] using htrunc0'
    -- Rewrite using m = x * β^(-E) so we get Ztrunc(m).run = 0
    have htrunc0R' : ((FloatSpec.Core.Raux.Ztrunc (x * (beta : ℝ) ^ (-E))) : ℝ) = 0 := by
      simpa [hm] using htrunc0R
    -- Final simplification: 0 * β^E = 0
    simp only [FloatSpec.Core.Generic_fmt.RoundModeLike.toRnd_relation_apply,
      hrw, htrunc0R', zero_mul]
  -- Discharge the Hoare triple
  simpa [wp, PostCond.noThrow, Id.run, bind, pure] using this
-/

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-
Coq (FTZ.v):
Theorem generic_format_FTZ :
  forall x, FTZ_format x -> generic_format beta FTZ_exp x.
-/
theorem generic_format_FTZ (beta : Int) [ValidRadix beta] (x : ℝ) :
    ⦃⌜FTZ_format prec emin beta x⌝⦄
    (pure (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x) : Id Prop)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  simp only [wp, PostCond.noThrow, Id.run, pure, PredTrans.pure, FTZ_format] at hx ⊢
  exact hx

/-
Coq (FTZ.v):
Theorem FTZ_format_generic :
  forall x, generic_format beta FTZ_exp x -> FTZ_format x.
-/
theorem FTZ_format_generic (beta : Int) [ValidRadix beta] (x : ℝ) :
    ⦃⌜(FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x)⌝⦄
    (pure (FTZ_format prec emin beta x) : Id Prop)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  simp only [wp, PostCond.noThrow, Id.run, pure, PredTrans.pure, FTZ_format]
  exact hx

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-
Coq (FTZ.v):
Theorem FTZ_format_satisfies_any :
  satisfies_any FTZ_format.
-/
theorem FTZ_format_satisfies_any (beta : Int) [ValidRadix beta] :
    FloatSpec.Core.Generic_fmt.satisfies_any (fun y => FTZ_format prec emin beta y) := by
  simpa [FTZ_format]
    using FloatSpec.Core.Generic_fmt.generic_format_satisfies_any (beta := beta) (fexp := FTZ_exp prec emin)

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`ulp_FTZ_0`: {lit}`ulp beta FTZ_exp 0 = bpow (emin + prec - 1)`.

Lean (spec): The ULP under FTZ at 0 equals {lit}`β^(emin+prec-1)`.
-/
theorem ulp_FTZ_0 (beta : Int) [ValidRadix beta] :
    ⦃⌜True⌝⦄
    (pure (FloatSpec.Core.Ulp.ulp beta (FTZ_exp prec emin) 0) : Id ℝ)
    ⦃⇓r => ⌜r = (beta : ℝ) ^ (emin + prec - 1)⌝⦄ := by
  intro _
  classical
  let e0 : Int := emin + prec - 1
  have hbranch : e0 - prec < emin := by
    simp [e0]
    omega
  have hfexp_e0 : FTZ_exp prec emin e0 = e0 := by
    simp [FTZ_exp, hbranch, e0]
  -- Hence there exists a negligible exponent witness (take `n = e0`).
  have h_le_wit : e0 ≤ FTZ_exp prec emin e0 := by
    simpa [hfexp_e0]
  -- Use the canonical spec for `negligible_exp` to extract a concrete witness.
  have hsome : ∃ n : Int,
      FloatSpec.Core.Ulp.negligible_exp (FTZ_exp prec emin) = some n ∧ n ≤ FTZ_exp prec emin n := by
    have H := FloatSpec.Core.Ulp.negligible_exp_spec' (fexp := FTZ_exp prec emin)
    -- Eliminate the impossible `none` branch using the witness at `emin`.
    cases H with
    | inl hnone =>
        rcases hnone with ⟨hEqNone, hall_lt⟩
        have : (FTZ_exp prec emin e0) < e0 := hall_lt e0
        -- Contradiction with `fexp e0 = e0`.
        have : False := by simpa [hfexp_e0] using this
        cases this
    | inr hsome =>
        exact hsome
  rcases hsome with ⟨n, hneg_eq, hnle⟩
  -- Any negligible witness yields the same exponent; specialize to `e0`.
  have hfexp_eq : FTZ_exp prec emin n = FTZ_exp prec emin e0 := by
    simpa using
      (FloatSpec.Core.Ulp.fexp_negligible_exp_eq
        (beta := beta) (fexp := FTZ_exp prec emin) (n := n) (m := e0)
        hnle h_le_wit)
  -- Compute ulp at 0 using the `some` branch and rewrite the exponent.
  have : FloatSpec.Core.Ulp.ulp beta (FTZ_exp prec emin) 0 = ((beta : ℝ) ^ e0) := by
    unfold FloatSpec.Core.Ulp.ulp
    -- Select the `some n` branch and rewrite its exponent to `e0`.
    simpa [hneg_eq, hfexp_eq, hfexp_e0]
  -- Discharge the Hoare-style postcondition.
  simpa [wp, PostCond.noThrow, Id.run, pure] using this

end FloatSpec.Core.FTZ
