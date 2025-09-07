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

Generic floating-point format definitions and properties
Based on flocq/src/Core/Generic_fmt.v
-/

import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Round_pred
import FloatSpec.src.Core.Float_prop
-- import FloatSpec.src.Core.Digits
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do
open FloatSpec.Core.Defs
open FloatSpec.Core.Zaux
open FloatSpec.Core.Raux

namespace FloatSpec.Core.Generic_fmt

section ExponentFunction

/-- Magnitude function for real numbers

    Returns the exponent such that beta^(mag-1) ≤ |x| < beta^mag.
    For x = 0, returns an arbitrary value (typically 0).

    NOTE: Many proofs in this file require properties of mag that depend on:
    - Logarithm properties from Mathlib
    - The characterization: beta^(e-1) ≤ |x| < beta^e ↔ mag beta x = e
    - Monotonicity and other algebraic properties of mag

    These should be proven in a separate Mag.lean file before completing this file.
-/
noncomputable def mag (beta : Int) (x : ℝ) : Int :=
  if x = 0 then 0
  else ⌈Real.log (abs x) / Real.log (beta : ℝ)⌉

/-- Truncation function for real numbers

    Returns the integer part of a real number (toward zero).
    Equivalent to floor for positive numbers and ceiling for negative.
-/
noncomputable def Ztrunc (x : ℝ) : Int :=
  if x ≥ 0 then ⌊x⌋ else ⌈x⌉

/-- Ztrunc of an integer is itself -/
lemma Ztrunc_int (n : Int) : Ztrunc (n : ℝ) = n := by
  unfold Ztrunc
  by_cases h : (n : ℝ) ≥ 0
  · simp [h, Int.floor_intCast]
  · simp [h, Int.ceil_intCast]

/-- Powers of positive bases are nonzero -/
lemma zpow_ne_zero_of_pos (a : ℝ) (n : Int) (ha : 0 < a) : a ^ n ≠ 0 := by
  exact zpow_ne_zero n (ne_of_gt ha)

/-- A format satisfies_any if it contains representable values

    This property ensures that the floating-point format is non-empty
    and can represent at least some real numbers.
-/
def satisfies_any (F : ℝ → Prop) : Prop :=
  ∃ x : ℝ, F x

/-- Valid exponent property

    A valid exponent function must satisfy two key properties:
    1. For "large" values (where fexp k < k): monotonicity
    2. For "small" values (where k ≤ fexp k): constancy

    These ensure the format behaves well across all scales.
-/
public class Valid_exp (beta : Int) (fexp : Int → Int) : Prop where
  /-- Validity conditions for the exponent function -/
  valid_exp : ∀ k : Int,
    ((fexp k < k) → (fexp (k + 1) ≤ k)) ∧
    ((k ≤ fexp k) →
      (fexp (fexp k + 1) ≤ fexp k) ∧
      ∀ l : Int, (l ≤ fexp k) → fexp l = fexp k)

/-- Specification: Valid exponent for large values

    When fexp k < k (k is in the "large" regime),
    this property extends to all larger values.
-/
theorem valid_exp_large (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (k l : Int) (hk : fexp k < k) (h : k ≤ l) :
    fexp l < l := by
  -- Prepare decomposition of l as k + n with n ≥ 0
  have hn_nonneg : 0 ≤ l - k := sub_nonneg.mpr h
  have h_decomp_max : l = k + max (l - k) 0 := by
    have h1 : l = (l - k) + k := by
      have htmp : l - k + k = l := sub_add_cancel l k
      simpa [add_comm] using (eq_comm.mp htmp)
    simpa [add_comm, max_eq_left hn_nonneg] using h1
  -- Monotone extension to k + n for any natural n
  have step_all : ∀ n : Nat, fexp (k + Int.ofNat n) < k + Int.ofNat n := by
    intro n
    induction n with
    | zero => simpa using hk
    | succ n ih =>
        set m := k + Int.ofNat n with hm
        have hstep_le : fexp (m + 1) ≤ m := by
          have hpair := (Valid_exp.valid_exp (beta := beta) (fexp := fexp) m)
          exact (hpair.left) (by simpa [hm] using ih)
        have hm_lt_succ : m < m + 1 := by
          have : (0 : Int) < 1 := Int.zero_lt_one
          simpa [add_comm] using lt_add_of_pos_right m this
        have hlt : fexp (m + 1) < m + 1 := lt_of_le_of_lt hstep_le hm_lt_succ
        simpa [hm, Int.ofNat_succ, add_assoc] using hlt
  -- Instantiate with n = (l - k).toNat and rewrite
  have hmain : fexp (k + Int.ofNat (Int.toNat (l - k))) < k + Int.ofNat (Int.toNat (l - k)) :=
    step_all (Int.toNat (l - k))
  -- Rewrite Int.ofNat (Int.toNat z) as max z 0, then substitute decomposition of l
  have h_ofNat : (Int.ofNat (Int.toNat (l - k)) : Int) = max (l - k) 0 := Int.ofNat_toNat (l - k)
  have hmain' : fexp (k + max (l - k) 0) < k + max (l - k) 0 := by
    simpa [h_ofNat] using hmain
  have h_decomp_max' : k + max (l - k) 0 = l := by
    simpa [add_comm] using h_decomp_max.symm
  simpa [h_decomp_max'] using hmain'

/-- Specification: Valid exponent transitivity

    When fexp k < k, this extends to all values up to k.
-/
theorem valid_exp_large' (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (k l : Int) (hk : fexp k < k) (h : l ≤ k) :
    fexp l < k := by
  -- By contradiction: if k ≤ fexp l, constancy on the small regime at l forces k ≤ fexp k, contradicting hk
  by_contra hnot
  have hk_le : k ≤ fexp l := le_of_not_gt hnot
  have hpair := (Valid_exp.valid_exp (beta := beta) (fexp := fexp) l)
  have hsmall := (hpair.right)
  have hconst := (hsmall (le_trans h hk_le)).right
  have hkeq' : fexp k = fexp l := hconst k hk_le
  have hk_le' : k ≤ fexp k := by simpa [hkeq'] using hk_le
  exact (not_le_of_gt hk) hk_le'

end ExponentFunction

section CanonicalFormat

/-- Canonical exponent function

    For a real number x, returns the canonical exponent
    based on its magnitude and the format's exponent function.
-/
noncomputable def cexp (beta : Int) (fexp : Int → Int) (x : ℝ) : Id Int :=
  pure (fexp (mag beta x))

/-- Canonical float property

    A float is canonical if its exponent equals the
    canonical exponent of its real value.
-/
def canonical (beta : Int) (fexp : Int → Int) (f : FlocqFloat beta) : Prop :=
  f.Fexp = fexp (mag beta (F2R f).run)

/-- Scaled mantissa computation

    Scales x by the appropriate power of beta to obtain
    the hntissa in the canonical representation.
-/
noncomputable def scaled_mantissa (beta : Int) (fexp : Int → Int) (x : ℝ) : Id ℝ :=
  do
    let exp ← cexp beta fexp x
    pure (x * (beta : ℝ) ^ (-exp))

/-- Generic format predicate

    A real number is in generic format if it can be
    exactly represented with canonical exponent.
-/
def generic_format (beta : Int) (fexp : Int → Int) (x : ℝ) : Id Prop :=
  do
    let mantissa ← scaled_mantissa beta fexp x
    let exp ← cexp beta fexp x
    let truncated := Ztrunc mantissa
    let reconstructed ← F2R (FlocqFloat.mk truncated exp : FlocqFloat beta)
    pure (x = reconstructed)

end CanonicalFormat

section BasicProperties

/-- Specification: Canonical exponent computation

    The canonical exponent is determined by applying
    the format's exponent function to the magnitude.
-/
theorem cexp_spec (beta : Int) (fexp : Int → Int) (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    cexp beta fexp x
    ⦃⇓result => ⌜result = fexp (mag beta x)⌝⦄ := by
  intro _
  unfold cexp
  rfl

/-- Specification: Scaled mantissa computation

    The scaled mantissa is x scaled by beta^(-cexp(x)).
-/
theorem scaled_mantissa_spec (beta : Int) (fexp : Int → Int) (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    scaled_mantissa beta fexp x
    ⦃⇓result => ⌜result = x * (beta : ℝ) ^ (-(fexp (mag beta x)))⌝⦄ := by
  intro _
  unfold scaled_mantissa cexp
  rfl

/-- Specification: Generic format predicate

    x is in generic format iff x equals F2R of its
    canonical representation with truncated mantissa.
-/
theorem generic_format_spec (beta : Int) (fexp : Int → Int) (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    generic_format beta fexp x
    ⦃⇓result => ⌜result ↔ (x = (F2R (FlocqFloat.mk (Ztrunc (x * (beta : ℝ) ^ (-(fexp (mag beta x))))) (fexp (mag beta x)) : FlocqFloat beta)).run)⌝⦄ := by
  intro _
  unfold generic_format scaled_mantissa cexp
  rfl

/-- Truncation respects negation: Ztrunc(-x) = -Ztrunc(x) -/
theorem Ztrunc_neg (x : ℝ) : Ztrunc (-x) = - Ztrunc x := by
  unfold Ztrunc
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hnonneg : 0 ≤ x
    · -- x > 0 (since x ≠ 0)
      have hxpos : 0 < x := lt_of_le_of_ne hnonneg (Ne.symm hx)
      have hnot : ¬ 0 ≤ -x := by
        intro hge
        have hxle0 : x ≤ 0 := by simpa using (neg_nonneg.mp hge)
        exact (not_lt_of_ge hxle0) hxpos
      simpa [hnonneg, hnot, Int.ceil_neg]
    · -- x < 0
      have hxlt : x < 0 := lt_of_le_of_ne (le_of_not_ge hnonneg) (by simpa [hx])
      have hnonneg' : 0 ≤ -x := by simpa using (neg_nonneg.mpr (le_of_lt hxlt))
      simpa [hnonneg, hnonneg', Int.floor_neg]

/-- Truncation of an integer (as real) gives the same integer -/
theorem Ztrunc_intCast (z : Int) : Ztrunc (z : ℝ) = z := by
  unfold Ztrunc
  by_cases hz : (z : ℝ) ≥ 0
  · simp [hz, Int.floor_intCast]
  · simp [hz, Int.ceil_intCast]

/-- zpow product with negative exponent collapses to subtraction in exponent -/
theorem zpow_mul_sub {a : ℝ} (hbne : a ≠ 0) (e c : Int) :
    a ^ e * a ^ (-c) = a ^ (e - c) := by
  have := (zpow_add₀ hbne e (-c))
  simpa [sub_eq_add_neg] using this.symm

/-- zpow split: (e - c) then c gives back e -/
theorem zpow_sub_add {a : ℝ} (hbne : a ≠ 0) (e c : Int) :
    a ^ (e - c) * a ^ c = a ^ e := by
  simpa [sub_add_cancel] using (zpow_add₀ hbne (e - c) c).symm

/-- For nonnegative exponent, zpow reduces to Nat pow via toNat -/
theorem zpow_nonneg_toNat (a : ℝ) (k : Int) (hk : 0 ≤ k) :
    a ^ k = a ^ (Int.toNat k) := by
  have hofNat : (Int.toNat k : ℤ) = k := Int.toNat_of_nonneg hk
  rw [← hofNat]
  exact zpow_ofNat a (Int.toNat k)

/-- Specification: Zero is in generic format

    The real number zero can always be exactly
    represented in any well-formed floating-point format.
-/
theorem generic_format_0 (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] :
    ⦃⌜beta > 1⌝⦄
    generic_format beta fexp 0
    ⦃⇓result => ⌜result⌝⦄ := by
  intro _
  unfold generic_format scaled_mantissa cexp F2R
  -- After unfolding, goal reduces to 0 = 0
  simp [Ztrunc]

/-- Specification: Canonical exponent of opposite

    The canonical exponent is preserved under negation
    since magnitude is unaffected by sign.
-/
theorem cexp_opp (beta : Int) (fexp : Int → Int) (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    cexp beta fexp (-x)
    ⦃⇓result => ⌜result = (cexp beta fexp x).run⌝⦄ := by
  intro _
  unfold cexp
  -- We need to show that mag beta (-x) = mag beta x
  -- This follows from the fact that abs(-x) = abs(x)
  congr 1
  unfold mag
  -- For mag, we have two cases: x = 0 or x ≠ 0
  by_cases hx : x = 0
  · -- If x = 0, then -x = 0, so both mags are 0
    simp [hx]
  · -- If x ≠ 0, then -x ≠ 0, and abs(-x) = abs(x)
    have h_neg_ne : -x ≠ 0 := by simp [hx]
    simp [hx, h_neg_ne, abs_neg]

/-- Specification: Canonical exponent of absolute value

    The canonical exponent equals that of the absolute value
    since magnitude depends only on absolute value.
-/
theorem cexp_abs (beta : Int) (fexp : Int → Int) (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    cexp beta fexp (abs x)
    ⦃⇓result => ⌜result = (cexp beta fexp x).run⌝⦄ := by
  intro _
  unfold cexp
  -- We need to show that mag beta (abs x) = mag beta x
  -- This follows because mag already uses abs internally
  congr 1
  unfold mag
  -- For mag, we have two cases: x = 0 or x ≠ 0
  by_cases hx : x = 0
  · -- If x = 0, then abs x = 0, so both mags are 0
    simp [hx, abs_zero]
  · -- If x ≠ 0, then abs x ≠ 0, and abs(abs x) = abs x
    have h_abs_ne : abs x ≠ 0 := abs_ne_zero.mpr hx
    simp [hx, h_abs_ne, abs_abs]

/-- Specification: Generic format implies canonical representation

    Any number in generic format has a unique canonical
    floating-point representation.
-/
theorem canonical_generic_format (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ⦃⌜beta > 1 ∧ (generic_format beta fexp x).run⌝⦄
    do
      let mantissa ← scaled_mantissa beta fexp x
      let exp ← cexp beta fexp x
      pure (FlocqFloat.mk (Ztrunc mantissa) exp : FlocqFloat beta)
    ⦃⇓result => ⌜x = (F2R result).run → canonical beta fexp result⌝⦄ := by
  intro _
  -- Unfold the computations to expose the constructed float `result`
  simp [scaled_mantissa, cexp]
  -- Now prove the postcondition from the given equality
  intro hx
  -- Reduce to equality of exponents via congrArg on fexp ∘ mag
  -- Left-hand side is definally fexp (mag beta x)
  simpa [canonical]
    using congrArg (fun y : ℝ => fexp (mag beta y)) hx



/-- Specification: Scaled mantissa multiplication

    Multiplying the scaled mantissa by beta^cexp(x) recovers x.
-/
theorem scaled_mantissa_mult_bpow (beta : Int) (fexp : Int → Int) (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    do
      let sm ← scaled_mantissa beta fexp x
      let ce ← cexp beta fexp x
      pure (sm * (beta : ℝ) ^ ce)
    ⦃⇓result => ⌜result = x⌝⦄ := by
  intro hβ
  simp [scaled_mantissa, cexp]
  -- Denote the canonical exponent
  set e := fexp (mag beta x)
  -- Base is nonzero
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  -- x * β^(-e) * β^e = x
  calc
    x * ((beta : ℝ) ^ e)⁻¹ * (beta : ℝ) ^ e
        = (x * (beta : ℝ) ^ (-e)) * (beta : ℝ) ^ e := by simp [zpow_neg]
    _   = x * ((beta : ℝ) ^ (-e) * (beta : ℝ) ^ e) := by simpa [mul_assoc]
    _   = x * (beta : ℝ) ^ ((-e) + e) := by
          have h := (zpow_add₀ hbne (-e) e).symm
          simpa using congrArg (fun t => x * t) h
    _   = x := by simp

lemma Ztrunc_zero : Ztrunc (0 : ℝ) = 0 := by
  simp [Ztrunc]

/-- Specification: F2R in generic format

    F2R of a float is in generic format when the canonical
    exponent is bounded by the float's exponent.
-/
theorem generic_format_F2R (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (m e : Int) :
    ⦃⌜beta > 1 ∧ (m ≠ 0 → (cexp beta fexp (F2R (FlocqFloat.mk m e : FlocqFloat beta)).run).run ≤ e)⌝⦄
    generic_format beta fexp (F2R (FlocqFloat.mk m e : FlocqFloat beta)).run
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hbound⟩
  -- Unfold the goal shape
  simp [generic_format, scaled_mantissa, cexp, F2R]
  -- Notation: cexp for this x
  set c := fexp (mag beta ((m : ℝ) * (beta : ℝ) ^ e)) with hc
  -- Base positivity for zpow lemmas
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos

  by_cases hm : m = 0
  · -- x = 0 case: goal is Ztrunc 0 = 0 ∨ ↑beta ^ c = 0
    simp [hm]
    left
    simp [Ztrunc]
  · -- Nonzero mantissa case: goal is the equality
    have hcle : c ≤ e := by
      have := hbound hm
      simp [cexp, F2R] at this
      exact this

    -- Key lemmas for power manipulation
    have hinv : (beta : ℝ) ^ (-c) = ((beta : ℝ) ^ c)⁻¹ := zpow_neg _ _

    have hmul_pow : (beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹ = (beta : ℝ) ^ (e - c) := by
      rw [← hinv, ← zpow_add₀ hbne]
      simp [sub_eq_add_neg]

    have hpow_nonneg : 0 ≤ e - c := sub_nonneg.mpr hcle

    -- Convert zpow with nonnegative exponent to Nat power
    have hzpow_toNat : (beta : ℝ) ^ (e - c) = (beta : ℝ) ^ (Int.toNat (e - c)) := by
      rw [← Int.toNat_of_nonneg hpow_nonneg]
      exact zpow_ofNat _ _

    -- Cast of integer power to real
    have hcast_pow : (beta : ℝ) ^ (Int.toNat (e - c)) = ((beta ^ (Int.toNat (e - c)) : Int) : ℝ) := by
      rw [← Int.cast_pow]

    -- The scaled mantissa is an integer
    have htrunc_calc : Ztrunc ((m : ℝ) * (beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹) = m * beta ^ (Int.toNat (e - c)) := by
      calc Ztrunc ((m : ℝ) * (beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹)
          = Ztrunc ((m : ℝ) * ((beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹)) := by ring_nf
        _ = Ztrunc ((m : ℝ) * (beta : ℝ) ^ (e - c)) := by rw [hmul_pow]
        _ = Ztrunc ((m : ℝ) * (beta : ℝ) ^ (Int.toNat (e - c))) := by rw [hzpow_toNat]
        _ = Ztrunc ((m : ℝ) * ((beta ^ (Int.toNat (e - c)) : Int) : ℝ)) := by rw [hcast_pow]
        _ = Ztrunc (((m * beta ^ (Int.toNat (e - c))) : Int) : ℝ) := by simp [Int.cast_mul]
        _ = m * beta ^ (Int.toNat (e - c)) := Ztrunc_intCast _

    -- Power splitting lemma
    have hsplit : (beta : ℝ) ^ e = (beta : ℝ) ^ (e - c) * (beta : ℝ) ^ c := by
      rw [← zpow_add₀ hbne (e - c) c]
      simp [sub_add_cancel]

    -- Prove the main equality
    calc (m : ℝ) * (beta : ℝ) ^ e
        = (m : ℝ) * ((beta : ℝ) ^ (e - c) * (beta : ℝ) ^ c) := by rw [hsplit]
      _ = ((m : ℝ) * (beta : ℝ) ^ (e - c)) * (beta : ℝ) ^ c := by ring
      _ = ((m : ℝ) * (beta : ℝ) ^ (Int.toNat (e - c))) * (beta : ℝ) ^ c := by rw [← hzpow_toNat]
      _ = ((m : ℝ) * ((beta ^ (Int.toNat (e - c)) : Int) : ℝ)) * (beta : ℝ) ^ c := by rw [hcast_pow]
      _ = (((m * beta ^ (Int.toNat (e - c))) : Int) : ℝ) * (beta : ℝ) ^ c := by simp [Int.cast_mul]
      _ = (Ztrunc ((m : ℝ) * (beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹) : ℝ) * (beta : ℝ) ^ c := by rw [← htrunc_calc]

/-- Specification: Alternative F2R generic format

    If x equals F2R of a float and the exponent condition
    holds, then x is in generic format.
-/
theorem generic_format_F2R' (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) (f : FlocqFloat beta) :
    ⦃⌜beta > 1 ∧ (F2R f).run = x ∧ (x ≠ 0 → (cexp beta fexp x).run ≤ f.Fexp)⌝⦄
    generic_format beta fexp x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx, hbound⟩
  -- Transform the bound to the shape needed for generic_format_F2R
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos

  have hbound' : f.Fnum ≠ 0 → (cexp beta fexp (F2R (FlocqFloat.mk f.Fnum f.Fexp : FlocqFloat beta)).run).run ≤ f.Fexp := by
    intro hm
    have hxne : x ≠ 0 := by
      rw [← hx]
      simp [F2R]
      constructor
      · exact_mod_cast hm
      · exact zpow_ne_zero f.Fexp hbne
    -- Now apply the bound
    have := hbound hxne
    rw [← hx] at this
    simp [F2R] at this
    exact this

  -- Apply the previous lemma and rewrite x
  have := generic_format_F2R (beta := beta) (fexp := fexp) (m := f.Fnum) (e := f.Fexp) ⟨hβ, hbound'⟩
  rw [← hx]
  simp [F2R] at this ⊢
  exact this

-- Section: Canonical properties

/-- Specification: Canonical opposite

    The canonical property is preserved under negation of mantissa.
-/
theorem canonical_opp (beta : Int) (fexp : Int → Int) (m e : Int) (h : canonical beta fexp (FlocqFloat.mk m e)) :
    canonical beta fexp (FlocqFloat.mk (-m) e) := by
  -- canonical means f.Fexp = fexp (mag beta (F2R f).run)
  -- Since F2R negates with the mantissa and mag uses absolute value, the result is the same
  unfold canonical at h ⊢
  -- Show magnitude is invariant under negation of the real value
  -- F2R (mk (-m) e) = -(F2R (mk m e))
  have hF2R_neg : (F2R (FlocqFloat.mk (-m) e : FlocqFloat beta)).run =
      - (F2R (FlocqFloat.mk m e : FlocqFloat beta)).run := by
    unfold FloatSpec.Core.Defs.F2R
    simp
  -- mag beta (-x) = mag beta x
  have hmag : mag beta (-(F2R (FlocqFloat.mk m e : FlocqFloat beta)).run) =
      mag beta (F2R (FlocqFloat.mk m e : FlocqFloat beta)).run := by
    unfold mag
    by_cases hx : (F2R (FlocqFloat.mk m e : FlocqFloat beta)).run = 0
    · simp [hx]
    · have hneg : -((F2R (FlocqFloat.mk m e : FlocqFloat beta)).run) ≠ 0 := by simpa [hx]
      simp [hx, hneg, abs_neg]
  simpa [hF2R_neg, hmag] using h

/-- Specification: Canonical absolute value

    The canonical property is preserved under absolute value of mantissa.
-/
theorem canonical_abs (beta : Int) (fexp : Int → Int) (m e : Int) (h : canonical beta fexp (FlocqFloat.mk m e)) :
    canonical beta fexp (FlocqFloat.mk (abs m) e) := by
  unfold canonical at h ⊢
  -- Let x be the real value of (m, e) and y the real value of (|m|, e)
  set x := (F2R (FlocqFloat.mk m e : FlocqFloat beta)).run
  set y := (F2R (FlocqFloat.mk (abs m) e : FlocqFloat beta)).run
  have habs_xy : |y| = |x| := by
    -- abs (|m| * b^e) = |m| * |b^e| and abs (m * b^e) = |m| * |b^e|
    -- using (abs m : ℝ) = |(m : ℝ)|
    simp [x, y, FloatSpec.Core.Defs.F2R, abs_mul, Int.cast_abs, abs_abs]
  -- mag depends only on abs, so equal abs implies equal mag
  have hmag_xy : mag beta y = mag beta x := by
    unfold mag
    by_cases hx0 : x = 0
    · have hxabs0 : |x| = 0 := by simpa [hx0] using congrArg abs hx0
      have hyabs0 : |y| = 0 := by simpa [habs_xy.symm] using hxabs0
      have hy0 : y = 0 := (abs_eq_zero.mp hyabs0)
      simp [hx0, hy0]
    · have hy0 : y ≠ 0 := by
        -- if |y| = |x| and x ≠ 0 then y ≠ 0
        intro hy
        have : |y| = 0 := by simpa [hy]
        have : |x| = 0 := by simpa [habs_xy] using this
        exact hx0 (abs_eq_zero.mp this)
      -- nonzero case: use equality of abs to rewrite logs
      simp [hx0, hy0, habs_xy]
  simpa [x, y, hmag_xy] using h

/-- Specification: Canonical zero

    The zero float with exponent fexp(mag(0)) is canonical.
-/
theorem canonical_0 (beta : Int) (fexp : Int → Int) : canonical beta fexp (FlocqFloat.mk 0 (fexp (mag beta 0))) := by
  -- By definition, canonical means f.Fexp = fexp (mag beta (F2R f).run)
  unfold canonical F2R
  simp

/-- Specification: Canonical uniqueness

    If two floats are canonical and have the same real value,
    then they are equal as floats.
-/
theorem canonical_unique
    (beta : Int) (hbeta : 1 < beta) (fexp : Int → Int)
    (f1 f2 : FlocqFloat beta)
    (h1 : canonical beta fexp f1)
    (h2 : canonical beta fexp f2)
    (h : (F2R f1).run = (F2R f2).run) :
    f1 = f2 := by
  -- Canonicality pins the exponent to fexp (mag _ (F2R _).run)
  unfold canonical at h1 h2
  have heq_exp : f1.Fexp = f2.Fexp := by
    -- Since (F2R f1).run = (F2R f2).run, their magnitudes agree,
    -- hence the canonical exponents are equal.
    have hm : mag beta (F2R f1).run = mag beta (F2R f2).run := by
      simpa [h]
    have : fexp (mag beta (F2R f1).run) = fexp (mag beta (F2R f2).run) :=
      congrArg fexp hm
    calc
      f1.Fexp = fexp (mag beta (F2R f1).run) := h1
      _       = fexp (mag beta (F2R f2).run) := this
      _       = f2.Fexp := by simpa using h2.symm

  -- Expand F2R equality to the "mantissa * base^exp" form.
  have h_orig : (F2R f1).run = (F2R f2).run := h
  unfold F2R at h_orig
  simp at h_orig
  -- Make the exponents syntactically the same and prepare to cancel.
  have h_mul :
      (f1.Fnum : ℝ) * (beta : ℝ) ^ f2.Fexp
        = (f2.Fnum : ℝ) * (beta : ℝ) ^ f2.Fexp := by
    simpa [heq_exp] using h_orig

  -- Since beta > 1, in ℤ we have 0 < beta; cast to ℝ gives positivity.
  have hβ_posℝ : (0 : ℝ) < (beta : ℝ) := by
    have : (0 : Int) < beta := lt_trans Int.zero_lt_one hbeta
    exact_mod_cast this

  -- Positive base ⇒ zpow is positive, hence nonzero; we can cancel.
  have hpow_ne : (beta : ℝ) ^ f2.Fexp ≠ 0 := by
    have hβ_ne : (beta : ℝ) ≠ 0 := ne_of_gt hβ_posℝ
    -- any zpow of a nonzero base is nonzero
    simpa using (zpow_ne_zero (f2.Fexp) hβ_ne)

  -- Cancel the common factor to equate mantissas over ℝ.
  have h_cast : (f1.Fnum : ℝ) = (f2.Fnum : ℝ) :=
    mul_right_cancel₀ hpow_ne h_mul

  -- Injectivity of Int.cast gives equality of mantissas over ℤ.
  have heq_num : f1.Fnum = f2.Fnum := Int.cast_injective h_cast

  -- Finish by structure equality (same fields => same floats).
  cases f1
  cases f2
  simp at heq_num heq_exp
  simpa [heq_num, heq_exp]

-- Section: Scaled mantissa properties


/-- Specification: Scaled mantissa of zero

    The scaled mantissa of zero is zero.
-/
theorem scaled_mantissa_0 (beta : Int) (fexp : Int → Int) :
    ⦃⌜True⌝⦄
    scaled_mantissa beta fexp 0
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _
  unfold scaled_mantissa cexp
  simp

/-- Specification: Scaled mantissa of opposite

    The scaled mantissa of -x equals the negation of
    the scaled mantissa of x.
-/
theorem scaled_mantissa_opp (beta : Int) (fexp : Int → Int) (x : ℝ) :
    ⦃⌜True⌝⦄
    scaled_mantissa beta fexp (-x)
    ⦃⇓result => ⌜result = -((scaled_mantissa beta fexp x).run)⌝⦄ := by
  intro _
  unfold scaled_mantissa cexp
  -- Show exponents coincide since mag ignores sign
  have hmag : mag beta (-x) = mag beta x := by
    unfold mag
    by_cases hx : x = 0
    · simp [hx]
    · have h_neg_ne : -x ≠ 0 := by simp [hx]
      simp [hx, h_neg_ne, abs_neg]
  -- Rewrite with equal exponents
  simp [hmag, neg_mul]

/-- Specification: Scaled mantissa of absolute value

    The scaled mantissa of |x| equals the absolute value
    of the scaled mantissa of x.
-/
theorem scaled_mantissa_abs (beta : Int) (fexp : Int → Int) (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    scaled_mantissa beta fexp (abs x)
    ⦃⇓result => ⌜result = abs (scaled_mantissa beta fexp x).run⌝⦄ := by
  intro hβ
  unfold scaled_mantissa cexp
  -- Show exponents coincide since mag ignores sign
  have hmag : mag beta (abs x) = mag beta x := by
    unfold mag
    by_cases hx : x = 0
    · simp [hx, abs_zero]
    · have h_abs_ne : abs x ≠ 0 := abs_ne_zero.mpr hx
      simp [hx, h_abs_ne, abs_abs]
  -- Base positivity for handling absolute value of the power
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos

  -- Show that beta^(-fexp(...)) is positive
  have hpow_pos : 0 < (beta : ℝ) ^ (-(fexp (mag beta x))) := by
    -- Use that beta > 0 and zpow preserves positivity
    exact zpow_pos hbpos _
  have hpow_nonneg : 0 ≤ (beta : ℝ) ^ (-(fexp (mag beta x))) := le_of_lt hpow_pos

  -- Also need the inverse is positive
  have hinv_pos : 0 < ((beta : ℝ) ^ (fexp (mag beta x)))⁻¹ := by
    rw [← zpow_neg]
    exact hpow_pos
  have hinv_nonneg : 0 ≤ ((beta : ℝ) ^ (fexp (mag beta x)))⁻¹ := le_of_lt hinv_pos

  -- Rewrite using hmag and absolute value properties
  simp [hmag, abs_mul]
  -- The goal is now about |(β^fexp)⁻¹| = (β^fexp)⁻¹ ∨ x = 0
  by_cases hx : x = 0
  · right
    exact hx
  · left
    exact (abs_of_nonneg hinv_nonneg).symm
-- Section: Generic format closure properties

/-- Specification: Generic format opposite

    If x is in generic format, then -x is also in generic format.
-/
theorem generic_format_opp (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ⦃⌜(generic_format beta fexp x).run⌝⦄
    generic_format beta fexp (-x)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  -- Turn the precondition into the reconstruction equality for x
  have hx' := hx
  simp [generic_format, scaled_mantissa, cexp, F2R] at hx'
  -- Unfold target and rewrite using mag(-x) = mag(x)
  unfold generic_format scaled_mantissa cexp F2R
  -- Show mag is invariant under negation
  have hmag : mag beta (-x) = mag beta x := by
    unfold mag
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hneg0 : -x ≠ 0 := by simpa [hx0]
      simp [hx0, hneg0, abs_neg]
  -- Rewrite using the reconstruction equality for x
  have hxneg : -x = -((Ztrunc (x * (beta : ℝ) ^ (-(fexp (mag beta x)))) : ℝ) * (beta : ℝ) ^ (fexp (mag beta x))) := by
    simpa [neg_mul] using congrArg Neg.neg hx'
  -- Now transform to the required form for -x using Ztrunc_neg and hmag
  calc
    -x
        = -((Ztrunc (x * (beta : ℝ) ^ (-(fexp (mag beta x)))) : ℝ) * (beta : ℝ) ^ (fexp (mag beta x))) := by simpa using hxneg
    _   = (-(Ztrunc (x * (beta : ℝ) ^ (-(fexp (mag beta x)))) : ℝ)) * (beta : ℝ) ^ (fexp (mag beta x)) := by simp [neg_mul]
    _   = ((Ztrunc (-(x * (beta : ℝ) ^ (-(fexp (mag beta x))))) : Int) : ℝ) * (beta : ℝ) ^ (fexp (mag beta x)) := by
          simpa [Ztrunc_neg]
    _   = ((Ztrunc ((-x) * (beta : ℝ) ^ (-(fexp (mag beta x)))) : Int) : ℝ) * (beta : ℝ) ^ (fexp (mag beta x)) := by
          simp [mul_comm, mul_left_comm, mul_assoc, neg_mul, mul_neg]
    _   = ((Ztrunc ((-x) * (beta : ℝ) ^ (-(fexp (mag beta (-x))))) : Int) : ℝ) * (beta : ℝ) ^ (fexp (mag beta (-x))) := by
          simpa [hmag]

/-- Specification: Generic format absolute value

    If x is in generic format, then |x| is also in generic format.
-/
theorem generic_format_abs (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ⦃⌜(generic_format beta fexp x).run⌝⦄
    generic_format beta fexp (abs x)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hx
  by_cases h0 : 0 ≤ x
  · -- abs x = x
    simp [abs_of_nonneg h0]
    exact hx
  · -- abs x = -x
    have hneg : abs x = -x := by
      have : x < 0 := not_le.mp h0
      exact abs_of_neg this

    -- Use generic_format_opp to get that -x is in generic format
    have h_neg_format : (generic_format beta fexp (-x)).run := by
      exact (generic_format_opp beta fexp x) hx

    -- Rewrite the goal using abs x = -x
    rw [hneg]
    exact h_neg_format

/-- Specification: Generic format absolute value inverse

    If |x| is in generic format, then x is also in generic format.
-/
theorem generic_format_abs_inv (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ⦃⌜(generic_format beta fexp (abs x)).run⌝⦄
    generic_format beta fexp x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro h_abs
  by_cases h0 : 0 ≤ x
  · -- x ≥ 0, so x = |x|
    have : x = abs x := (abs_of_nonneg h0).symm
    rw [this]
    exact h_abs
  · -- x < 0, so x = -|x|
    have hlt : x < 0 := not_le.mp h0
    have : x = -(abs x) := by
      rw [abs_of_neg hlt]
      simp
    rw [this]
    -- Apply generic_format_opp to show -(|x|) is in generic format
    exact (generic_format_opp beta fexp (abs x)) h_abs

-- Section: Canonical exponent bounds



-- Section: Advanced properties

/-- Ulp (unit in the last place) preliminary definition -/
noncomputable def ulp_prelim (beta : Int) (fexp : Int → Int) (x : ℝ) : ℝ :=
  (beta : ℝ) ^ (cexp beta fexp x).run

/-- Round to format property -/
def round_to_format (F : ℝ → Prop) : Prop :=
  ∀ x, ∃ f, F f ∧ (∀ g, F g → abs (f - x) ≤ abs (g - x))

/-- Format bounded property -/
def format_bounded (F : ℝ → Prop) : Prop :=
  ∃ M : ℝ, ∀ x, F x → abs x ≤ M

/-- Format discrete property -/
def format_discrete (F : ℝ → Prop) : Prop :=
  ∀ x, F x → x ≠ 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ y, F y → y ≠ x → abs (y - x) ≥ δ

-- Section: Generic format satisfies properties


/-- Specification: Generic format satisfies rounding properties

    The generic format contains at least some representable values.
-/
theorem generic_format_satisfies_any (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] :
    satisfies_any (fun y => (generic_format beta fexp y).run) := by
  refine ⟨0, ?_⟩
  unfold generic_format scaled_mantissa cexp F2R
  simp [Ztrunc]


-- Section: Format intersection and union

/-- Intersection of two generic formats -/
def generic_format_inter (beta : Int) (fexp1 fexp2 : Int → Int) (x : ℝ) : Prop :=
  (generic_format beta fexp1 x).run ∧ (generic_format beta fexp2 x).run

/-- Union of two generic formats -/
def generic_format_union (beta : Int) (fexp1 fexp2 : Int → Int) (x : ℝ) : Prop :=
  (generic_format beta fexp1 x).run ∨ (generic_format beta fexp2 x).run



end BasicProperties

end FloatSpec.Core.Generic_fmt
