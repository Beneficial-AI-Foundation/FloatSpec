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
import FloatSpec.src.Core.Float_prop
-- import FloatSpec.src.Core.Digits
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do
open FloatSpec.Core.Defs
open FloatSpec.Core.Zaux
open FloatSpec.Core.Raux

namespace FloatSpec.Core.Generic_fmt

-- Allow 'sorry' to remain as warnings, not errors, in this file.
set_option warningAsError false

section ExponentFunction

-- /-- Magnitude function for real numbers

--     Returns the exponent such that beta^(mag-1) ≤ |x| < beta^mag.
--     For x = 0, returns an arbitrary value (typically 0).

--     NOTE: Many proofs in this file require properties of mag that depend on:
--     - Logarithm properties from Mathlib
--     - The characterization: beta^(e-1) ≤ |x| < beta^e ↔ mag beta x = e
--     - Monotonicity and other algebraic properties of mag

--     These should be proven in a separate Mag.lean file before completing this file.
-- -/
-- noncomputable def mag (beta : Int) (x : ℝ) : Int :=
--   if x = 0 then 0
--   else ⌈Real.log (abs x) / Real.log (beta : ℝ)⌉

-- /-- Truncation function for real numbers

--     Returns the integer part of a real number (toward zero).
--     Equivalent to floor for positive numbers and ceiling for negative.
-- -/
-- noncomputable def Ztrunc (x : ℝ) : Int :=
--   if x ≥ 0 then ⌊x⌋ else ⌈x⌉

/-- Ztrunc of an integer is itself (run form) -/
lemma Ztrunc_int (n : Int) : (Ztrunc (n : ℝ)).run = n := by
  -- Use the definition from Raux: Ztrunc returns `Id Int`
  unfold FloatSpec.Core.Raux.Ztrunc
  by_cases h : (n : ℝ) < 0
  · -- Negative integers still have ceil equal to themselves
    simp [h, Int.ceil_intCast]
  · -- Nonnegative branch uses floor
    simp [h, Int.floor_intCast]

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
        simpa [hm, Int.natCast_succ, add_assoc] using hlt
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
  do
    let m ← mag beta x
    pure (fexp m)

/-- Canonical float property

    A float is canonical if its exponent equals the
    canonical exponent of its real value.
-/
def canonical (beta : Int) (fexp : Int → Int) (f : FlocqFloat beta) : Prop :=
  f.Fexp = fexp ((mag beta (F2R f).run).run)

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
    let truncated ← Ztrunc mantissa
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
    ⦃⇓result => ⌜result = fexp ((mag beta x).run)⌝⦄ := by
  intro _; classical
  unfold cexp
  -- Unfolding `cexp` exposes a single bind; the triple reduces by simp
  simp [FloatSpec.Core.Raux.mag]

/-- Specification: Scaled mantissa computation

    The scaled mantissa is x scaled by beta^(-cexp(x)).
-/
theorem scaled_mantissa_spec (beta : Int) (fexp : Int → Int) (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    scaled_mantissa beta fexp x
    ⦃⇓result => ⌜result = x * (beta : ℝ) ^ (-(fexp ((mag beta x).run)))⌝⦄ := by
  intro _
  unfold scaled_mantissa cexp
  -- Unfolds to a single bind; simplify the Id triple
  simp [FloatSpec.Core.Raux.mag]

/-- Specification: Generic format predicate

    x is in generic format iff x equals F2R of its
    canonical representation with truncated mantissa.
-/
theorem generic_format_spec (beta : Int) (fexp : Int → Int) (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    generic_format beta fexp x
    ⦃⇓result => ⌜result ↔ (x = (F2R (FlocqFloat.mk ((Ztrunc (x * (beta : ℝ) ^ (-(fexp ((mag beta x).run))))).run) (fexp ((mag beta x).run)) : FlocqFloat beta)).run)⌝⦄ := by
  intro _
  unfold generic_format scaled_mantissa cexp
  -- After unfolding, the computation is purely `pure (x = …)`;
  -- the Hoare triple therefore reduces to a reflexive equivalence.
  simp [wp, PostCond.noThrow, Id.run, bind, pure,
        F2R, FloatSpec.Core.Raux.mag, FloatSpec.Core.Raux.Ztrunc]

/-- Truncation respects negation (run form): Ztrunc(-x) = -Ztrunc(x) -/
theorem Ztrunc_neg (x : ℝ) : (Ztrunc (-x)).run = - (Ztrunc x).run := by
  -- Direct from the definition in Raux
  unfold FloatSpec.Core.Raux.Ztrunc
  by_cases hx : x < 0
  · -- Then -x > 0, so use floor/ceil negation identity
    have hneg : ¬ (-x) < 0 := not_lt.mpr (le_of_lt (neg_pos.mpr hx))
    simp [hx, hneg, Int.floor_neg, Int.ceil_neg]
  · -- x ≥ 0
    by_cases hx0 : x = 0
    · subst hx0; simp
    · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hx0)
      have hlt_negx : (-x) < 0 := by simpa using (neg_neg_of_pos hxpos)
      simp [hx, hlt_negx, Int.floor_neg, Int.ceil_neg]

/-- Truncation of an integer (as real) gives the same integer (run form) -/
theorem Ztrunc_intCast (z : Int) : (Ztrunc (z : ℝ)).run = z := by
  simpa using Ztrunc_int z

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
  -- Unfold the computation and reduce the Hoare triple on `Id`
  unfold generic_format scaled_mantissa cexp F2R
  -- Everything is pure; `simp` closes the equality 0 = 0
  simp [wp, PostCond.noThrow, Id.run, bind, pure,
        FloatSpec.Core.Raux.mag, FloatSpec.Core.Raux.Ztrunc]

/-
Coq (Generic_fmt.v):
Theorem generic_format_bpow:
  forall e, generic_format beta fexp (bpow e).

Lean (spec): For any integer exponent `e`, the power `(β : ℝ)^e`
is representable in the generic format.
-/
-- moved below `generic_format_F2R`

/-- Coq (Generic_fmt.v): generic_format_bpow_inv'

    If `β^e` is representable in the generic format, then the exponent
    constraint `fexp (e + 1) ≤ e` holds.
-/
theorem generic_format_bpow_inv'
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (e : Int) :
    beta > 1 → (generic_format beta fexp ((beta : ℝ) ^ e)).run → fexp e ≤ e := by
  intro hβ hfmt
  -- Basic positivity facts about the base on ℝ
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbR_gt1 : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ

  -- Compute mag on a pure power: mag beta (β^e) = e
  have hmag_pow_run : (mag beta ((beta : ℝ) ^ e)).run = e := by
    have htrip := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := e)
    simpa [wp, PostCond.noThrow, Id.run, pure] using (htrip hβ)

  -- Expand the generic_format equality at x = (β : ℝ)^e
  have hEq0 : (beta : ℝ) ^ e
      = (((Ztrunc (((beta : ℝ) ^ e) * (beta : ℝ) ^ (-(fexp e)))).run : Int) : ℝ)
          * (beta : ℝ) ^ (fexp e) := by
    simpa [generic_format, scaled_mantissa, cexp, F2R, hmag_pow_run]
      using hfmt
  -- At this point, we have: (β^e) = (Ztrunc ((β^e) * (β ^ (-fexp e)))).run * (β^e)
  -- Let c := fexp e be the canonical exponent at x = β^e
  set c : Int := fexp e with hc

  -- Show c ≤ e by contradiction. If e < c, then the scaled mantissa is in (0,1),
  -- hence its truncation is 0 and the reconstruction cannot equal β^e > 0.
  have hc_le_e : c ≤ e := by
    by_contra hlt
    have hlt' : e < c := lt_of_not_ge hlt
    -- Strict monotonicity of zpow for bases > 1 gives: β^(e - c) < β^0 = 1
    have hpow_lt_one : (beta : ℝ) ^ (e - c) < 1 := by
      have hlt_ec0 : e - c < 0 := sub_lt_zero.mpr hlt'
      have : (beta : ℝ) ^ (e - c) < (beta : ℝ) ^ 0 :=
        zpow_lt_zpow_right₀ hbR_gt1 hlt_ec0
      simpa using this
    -- Positivity of β^(e - c)
    have hpow_pos : 0 < (beta : ℝ) ^ (e - c) := zpow_pos hbpos _

    -- Let the scaled mantissa be `arg := β^e * β^(-c)`
    set arg : ℝ := (beta : ℝ) ^ e * (beta : ℝ) ^ (-c)
    have harg_pos : 0 < arg := by
      have hbne' : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
      -- arg = β^(e-c) > 0
      simpa [arg, zpow_mul_sub hbne' e c]
        using (zpow_pos hbpos (e - c))
    have harg_lt_one : arg < 1 := by
      -- arg = β^(e-c) < 1 since e - c < 0
      have hlt_ec0 : e - c < 0 := sub_lt_zero.mpr hlt'
      have hpow_lt : (beta : ℝ) ^ (e - c) < (beta : ℝ) ^ 0 :=
        zpow_lt_zpow_right₀ hbR_gt1 hlt_ec0
      have hbne' : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
      have harg_eq : arg = (beta : ℝ) ^ (e - c) := by
        simpa [arg, zpow_mul_sub hbne' e c]
      simpa [harg_eq] using hpow_lt
    -- Hence the truncation of arg must be 0 (since 0 ≤ arg < 1)
    have htrunc_arg : (Ztrunc arg).run = 0 := by
      have hnotlt : ¬ arg < 0 := not_lt.mpr (le_of_lt harg_pos)
      have hfloor0 : Int.floor arg = 0 := by
        have : ((0 : Int) : ℝ) ≤ arg ∧ arg < ((0 : Int) : ℝ) + 1 := by
          exact And.intro (by exact_mod_cast (le_of_lt harg_pos)) (by simpa using harg_lt_one)
        simpa using ((Int.floor_eq_iff).2 this)
      simp [FloatSpec.Core.Raux.Ztrunc, hnotlt, hfloor0]
    -- But the reconstruction equality says β^e = (Ztrunc arg) * β^c,
    -- so β^e = 0, impossible since β > 0.
    have : False := by
      -- Align hEq0 to our `arg` and `c = fexp e` names
      have : (beta : ℝ) ^ e = (((Ztrunc arg).run : Int) : ℝ) * (beta : ℝ) ^ c := by
        simpa [arg, hc] using hEq0
      have : (beta : ℝ) ^ e = 0 := by simpa [htrunc_arg, mul_comm] using this
      exact (ne_of_gt (zpow_pos hbpos e)) this
    exact this.elim

    -- (rest of proof removed as unreachable after contradiction above)

  -- Conclude: c = fexp e ≤ e
  simpa [hc, hmag_pow_run] using hc_le_e

/-- Coq (Generic_fmt.v): generic_format_bpow_inv

    If `β^e` is representable in the generic format, then `fexp e ≤ e`.
-/
theorem generic_format_bpow_inv
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (e : Int) :
    beta > 1 → (generic_format beta fexp ((beta : ℝ) ^ e)).run → fexp e ≤ e := by
  -- Directly reuse the proved variant with the explicit `beta > 1` hypothesis.
  intro hβ hfmt
  exact generic_format_bpow_inv' (beta := beta) (fexp := fexp) (e := e) hβ hfmt

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
  -- mag depends only on |x|, so mag(-x) = mag(x)
  simp [FloatSpec.Core.Raux.mag, abs_neg]

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
  -- Proof deferred; follows from mag(|x|) = mag(x)
  -- mag depends only on |x|, so mag(|x|) = mag(x)
  simp [FloatSpec.Core.Raux.mag, abs_abs]

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

lemma Ztrunc_zero : (Ztrunc (0 : ℝ)).run = 0 := by
  simp [FloatSpec.Core.Raux.Ztrunc]

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
    simp [FloatSpec.Core.Raux.Ztrunc]
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
    have htrunc_calc : (Ztrunc ((m : ℝ) * (beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹)).run = m * beta ^ (Int.toNat (e - c)) := by
      calc (Ztrunc ((m : ℝ) * (beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹)).run
          = (Ztrunc ((m : ℝ) * ((beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹))).run := by ring_nf
        _ = (Ztrunc ((m : ℝ) * (beta : ℝ) ^ (e - c))).run := by rw [hmul_pow]
        _ = (Ztrunc ((m : ℝ) * (beta : ℝ) ^ (Int.toNat (e - c)))).run := by rw [hzpow_toNat]
        _ = (Ztrunc ((m : ℝ) * ((beta ^ (Int.toNat (e - c)) : Int) : ℝ))).run := by rw [hcast_pow]
        _ = (Ztrunc (((m * beta ^ (Int.toNat (e - c))) : Int) : ℝ)).run := by simp [Int.cast_mul]
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
      _ = (((Ztrunc ((m : ℝ) * (beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹)).run : Int) : ℝ) * (beta : ℝ) ^ c := by
            rw [← htrunc_calc]

/-- Coq (Generic_fmt.v):
Theorem generic_format_bpow:
  forall e, generic_format beta fexp (bpow e).

Lean (spec): For any integer exponent `e`, the power `(β : ℝ)^e`
is representable in the generic format provided `fexp (e+1) ≤ e`.
-/
theorem generic_format_bpow (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (e : Int) :
    ⦃⌜beta > 1 ∧ fexp (e + 1) ≤ e⌝⦄
    generic_format beta fexp ((beta : ℝ) ^ e)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hle_e1⟩
  -- From fexp (e+1) ≤ e and Valid_exp, derive fexp e ≤ e.
  have hlt_e1 : fexp (e + 1) < (e + 1) :=
    lt_of_le_of_lt hle_e1 (lt_add_of_pos_right _ Int.zero_lt_one)
  have hfe_le : fexp e ≤ e := by
    -- Use the backward propagation lemma with k = e+1 and l = e
    have hstep :=
      valid_exp_large' (beta := beta) (fexp := fexp)
        (k := e + 1) (l := e) hlt_e1 (le_of_lt (lt_add_of_pos_right _ Int.zero_lt_one))
    exact Int.lt_add_one_iff.mp hstep

  -- Compute mag on a pure power: mag beta (β^e) = e to obtain cexp(β^e) = fexp e
  have hmag_pow_run : (mag beta ((beta : ℝ) ^ e)).run = e := by
    have htrip := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := e)
    simpa [wp, PostCond.noThrow, Id.run, pure] using (htrip hβ)

  -- Use the general F2R lemma with m = 1 and the derived bound on cexp
  have hbound : (1 : Int) ≠ 0 → (cexp beta fexp (F2R (FlocqFloat.mk 1 e : FlocqFloat beta)).run).run ≤ e := by
    intro _
    -- cexp(β^e) = fexp (mag beta (β^e)).run = fexp e ≤ e
    simpa [cexp, FloatSpec.Core.Defs.F2R, hmag_pow_run]
      using hfe_le

  -- Conclude by applying the established `generic_format_F2R` lemma
  simpa [FloatSpec.Core.Defs.F2R] using
    (generic_format_F2R (beta := beta) (fexp := fexp) (m := 1) (e := e) ⟨hβ, hbound⟩)

/-- Coq (Generic_fmt.v): generic_format_bpow'

    Variant of `generic_format_bpow` under the simpler hypothesis `fexp e ≤ e`.
    This mirrors the Coq statement where `bpow'` assumes `fexp e ≤ e` directly.
    We produce the canonical representation with mantissa `1` and exponent `e`.
-/
theorem generic_format_bpow' (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (e : Int) :
    ⦃⌜beta > 1 ∧ fexp e ≤ e⌝⦄
    generic_format beta fexp ((beta : ℝ) ^ e)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hfe_le⟩
  -- Compute mag on a pure power: mag beta (β^e) = e ⇒ cexp(β^e) = fexp e
  have hmag_pow_run : (mag beta ((beta : ℝ) ^ e)).run = e := by
    have htrip := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := e)
    simpa [wp, PostCond.noThrow, Id.run, pure] using (htrip hβ)

  -- Provide the bound required by `generic_format_F2R` with mantissa m = 1
  have hbound : (1 : Int) ≠ 0 →
      (cexp beta fexp (F2R (FlocqFloat.mk 1 e : FlocqFloat beta)).run).run ≤ e := by
    intro _
    -- cexp(β^e) = fexp (mag beta (β^e)).run = fexp e ≤ e
    simpa [cexp, FloatSpec.Core.Defs.F2R, hmag_pow_run] using hfe_le

  -- Conclude by the general `generic_format_F2R` lemma
  simpa [FloatSpec.Core.Defs.F2R] using
    (generic_format_F2R (beta := beta) (fexp := fexp) (m := 1) (e := e) ⟨hβ, hbound⟩)

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
theorem canonical_0 (beta : Int) (fexp : Int → Int) :
    canonical beta fexp (FlocqFloat.mk 0 (fexp ((mag beta 0).run))) := by
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

/-- Coq (Generic_fmt.v): generic_format_canonical

    If a float `f` is canonical, then its real value `(F2R f)`
    is representable in the generic format.
-/
theorem generic_format_canonical
    (beta : Int) (fexp : Int → Int) (f : FlocqFloat beta) :
    canonical beta fexp f → (generic_format beta fexp (F2R f).run).run := by
  intro hcanon
  -- Set notations and extract the canonical equality on the exponent
  set x : ℝ := (F2R f).run
  have hx : x = (f.Fnum : ℝ) * (beta : ℝ) ^ f.Fexp := by
    simpa [x, F2R]
  have hcexp : fexp ((mag beta x).run) = f.Fexp := by
    -- canonical gives f.Fexp = fexp (mag beta (F2R f).run).run
    -- rewrite to the needed orientation
    simpa [x, canonical] using hcanon.symm
  -- Unfold the computation and rewrite the exponent via hcexp
  unfold generic_format scaled_mantissa cexp F2R
  simp [x, hcexp]
  -- Now the goal is: x = (((Ztrunc (x * (beta : ℝ) ^ (-(f.Fexp)))).run : Int) : ℝ) * (beta : ℝ) ^ f.Fexp
  -- Split on whether (β^e) = 0 to avoid any cancellation requirements
  by_cases hpow0 : (beta : ℝ) ^ f.Fexp = 0
  · -- In this case, x = 0 and the truncated scaled mantissa is 0
    have hx0 : x = 0 := by simpa [hx, hpow0]
    -- Reduce the right-hand side using hpow0; both sides become 0
    simp [x, hx0, hpow0, Ztrunc_zero]
  · -- Nonzero case: the scaled mantissa reduces to the integer mantissa
    -- Here we have ¬((β^e) = 0)
    have hne : (beta : ℝ) ^ f.Fexp ≠ 0 := by exact hpow0
    -- Prefer the form with (β^e)⁻¹ to match Lean's normalization
    have hxscale' : x * ((beta : ℝ) ^ f.Fexp)⁻¹ = (f.Fnum : ℝ) := by
      -- x = m * β^e ⇒ x * (β^e)⁻¹ = m
      calc
        x * ((beta : ℝ) ^ f.Fexp)⁻¹
            = ((f.Fnum : ℝ) * (beta : ℝ) ^ f.Fexp) * ((beta : ℝ) ^ f.Fexp)⁻¹ := by
                simpa [hx]
        _   = (f.Fnum : ℝ) * ((beta : ℝ) ^ f.Fexp * ((beta : ℝ) ^ f.Fexp)⁻¹) := by
                ring
        _   = (f.Fnum : ℝ) * (1 : ℝ) := by
                have : (beta : ℝ) ^ f.Fexp ≠ 0 := hne
                simp [this]
        _   = (f.Fnum : ℝ) := by simp
    have htr' : (Ztrunc (x * ((beta : ℝ) ^ f.Fexp)⁻¹)).run = f.Fnum := by
      simpa [hxscale'] using Ztrunc_int f.Fnum
    -- Convert the target's mantissa to this normalized form and reconstruct
    -- Finish by reconstructing x explicitly
    -- Simple cancellation identity (under hne): a * a⁻¹ = 1
    have hmul_cancel : (beta : ℝ) ^ f.Fexp * ((beta : ℝ) ^ f.Fexp)⁻¹ = (1 : ℝ) := by
      have : (beta : ℝ) ^ f.Fexp ≠ 0 := hne
      simp [this]
    calc
      x
          = (f.Fnum : ℝ) * (beta : ℝ) ^ f.Fexp := by simpa [hx]
      _   = (((Ztrunc (x * ((beta : ℝ) ^ f.Fexp)⁻¹)).run : Int) : ℝ) * (beta : ℝ) ^ f.Fexp := by
            simpa [htr']
      _   = ((((Ztrunc (x * ((beta : ℝ) ^ f.Fexp)⁻¹)).run : Int) : ℝ) * 1) * (beta : ℝ) ^ f.Fexp := by
            ring
      _   = ((((Ztrunc (x * ((beta : ℝ) ^ f.Fexp)⁻¹)).run : Int) : ℝ)
              * ((beta : ℝ) ^ f.Fexp * ((beta : ℝ) ^ f.Fexp)⁻¹)) * (beta : ℝ) ^ f.Fexp := by
            simpa [hmul_cancel]
      _   = (((Ztrunc (x * ((beta : ℝ) ^ f.Fexp)⁻¹)).run : Int) : ℝ) * (beta : ℝ) ^ f.Fexp := by
            -- Collapse the middle factor to 1 and simplify
            have : (beta : ℝ) ^ f.Fexp * ((beta : ℝ) ^ f.Fexp)⁻¹ = (1 : ℝ) := hmul_cancel
            simp [this, mul_comm, mul_left_comm, mul_assoc]


/-- Specification: Scaled mantissa of zero

    The scaled mantissa of zero is zero.
-/
theorem scaled_mantissa_0 (beta : Int) (fexp : Int → Int) :
    ⦃⌜True⌝⦄
    scaled_mantissa beta fexp 0
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _
  unfold scaled_mantissa cexp
  simp [mag]

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
  -- Reduce the Hoare triple on Id and handle cases on x = 0
  by_cases hx : x = 0
  · -- Both sides are 0 when x = 0
    simp [hx, FloatSpec.Core.Raux.mag, neg_mul]
  · -- Use definitional equality of mag under negation: abs (-x) = abs x
    have hneg0 : -x ≠ 0 := by simpa [hx]
    simp [FloatSpec.Core.Raux.mag, hx, hneg0, abs_neg, neg_mul]

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
  -- We'll actually need the base power to be nonnegative
  have hpow_pos_base : 0 < (beta : ℝ) ^ (fexp (mag beta x)) := by
    -- base > 0 ⇒ every zpow is > 0
    exact zpow_pos hbpos _
  have hpow_nonneg_base : 0 ≤ (beta : ℝ) ^ (fexp (mag beta x)) :=
    le_of_lt hpow_pos_base

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
    exact (abs_of_nonneg hpow_nonneg_base).symm
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
  have hxneg : -x = -((((Ztrunc (x * (beta : ℝ) ^ (-(fexp (mag beta x))))).run : Int) : ℝ) * (beta : ℝ) ^ (fexp (mag beta x))) := by
    simpa [neg_mul] using congrArg Neg.neg hx'
  -- Now transform to the required form for -x using Ztrunc_neg and hmag
  calc
    -x
        = -((((Ztrunc (x * (beta : ℝ) ^ (-(fexp (mag beta x))))).run : Int) : ℝ) * (beta : ℝ) ^ (fexp (mag beta x))) := by simpa using hxneg
    _   = (-(((Ztrunc (x * (beta : ℝ) ^ (-(fexp (mag beta x))))).run : Int) : ℝ)) * (beta : ℝ) ^ (fexp (mag beta x)) := by
          simp [neg_mul]
    _   = (((-(Ztrunc (x * (beta : ℝ) ^ (-(fexp (mag beta x))))).run) : Int) : ℝ) * (beta : ℝ) ^ (fexp (mag beta x)) := by
          simp
    _   = (((Ztrunc (-(x * (beta : ℝ) ^ (-(fexp (mag beta x)))))).run : Int) : ℝ) * (beta : ℝ) ^ (fexp (mag beta x)) := by
          simpa [Ztrunc_neg]
    _   = (((Ztrunc ((-x) * (beta : ℝ) ^ (-(fexp (mag beta x))))).run : Int) : ℝ) * (beta : ℝ) ^ (fexp (mag beta x)) := by
          simp [mul_comm, mul_left_comm, mul_assoc, neg_mul, mul_neg]
    _   = (((Ztrunc ((-x) * (beta : ℝ) ^ (-(fexp (mag beta (-x)))))).run : Int) : ℝ) * (beta : ℝ) ^ (fexp (mag beta (-x))) := by
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


/-- Coq (Generic_fmt.v): generic_format_EM

    Law of excluded middle for membership in the generic format.
    Either a real `x` is in the generic format or it is not.
-/
theorem generic_format_EM
    (beta : Int) (fexp : Int → Int) (x : ℝ) :
    (generic_format beta fexp x).run ∨ ¬ (generic_format beta fexp x).run := by
  -- Follows Coq's Generic_fmt.generic_format_EM
  classical
  exact Classical.em _


-- Section: Magnitude-related bounds

/-- Coq (Generic_fmt.v): scaled_mantissa_lt_1

    If `|x| < β^ex` and `ex ≤ fexp ex`, then the absolute value of the
    scaled mantissa of `x` is strictly less than 1.
-/
theorem scaled_mantissa_lt_1
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (x : ℝ) (ex : Int) :
    1 < beta → abs x < (beta : ℝ) ^ ex → ex ≤ fexp ex →
    abs (scaled_mantissa beta fexp x).run < 1 := by
  intro hβ hxlt hlex
  -- Reduce `scaled_mantissa` and `cexp`; introduce notations
  unfold scaled_mantissa cexp
  -- Handle the trivial case x = 0
  by_cases hx0 : x = 0
  · subst hx0
    simp [abs_zero]
  -- From 1 < beta on ℤ, deduce positivity on ℝ
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  -- Let m := mag beta x
  set m : Int := (mag beta x).run with hm
  -- From |x| < β^ex and x ≠ 0, we get m ≤ ex via Raux.mag_le_abs
  have hmag_le_ex : m ≤ ex := by
    have htrip := FloatSpec.Core.Raux.mag_le_abs (beta := beta) (x := x) (e := ex)
    have hx_ne : x ≠ 0 := by simpa using hx0
    have hrun : (mag beta x).run ≤ ex := by
      -- Consume the Hoare-style lemma to a pure inequality on `.run`
      simpa [wp, PostCond.noThrow, Id.run, pure, FloatSpec.Core.Raux.mag]
        using (htrip ⟨hβ, hx_ne, hxlt⟩)
    simpa [hm] using hrun
  -- Use the "small" regime constancy of fexp to replace fexp m with fexp ex
  have hfeq : fexp m = fexp ex := by
    -- From Valid_exp at k = ex and hypothesis ex ≤ fexp ex
    have hpair := (Valid_exp.valid_exp (beta := beta) (fexp := fexp) ex)
    have hsmall := hpair.right
    have hconst := (hsmall hlex).right
    have hm_le_fex : m ≤ fexp ex := le_trans hmag_le_ex hlex
    exact hconst m hm_le_fex
  -- Now bound the scaled mantissa strictly by 1
  -- After unfolding, the result is |x| * (β^(fexp m))⁻¹
  -- Use monotonicity under multiplication by the positive factor (β^(fexp m))⁻¹
  have hpow_pos_m : 0 < (beta : ℝ) ^ (fexp m) := zpow_pos hbpos _
  have hstep : abs x * ((beta : ℝ) ^ (fexp m))⁻¹
                  < (beta : ℝ) ^ ex * ((beta : ℝ) ^ (fexp m))⁻¹ := by
    have hpos : 0 < ((beta : ℝ) ^ (fexp m))⁻¹ := by
      exact inv_pos.mpr hpow_pos_m
    exact mul_lt_mul_of_pos_right hxlt hpos
  -- The right side equals β^(ex - fexp m)
  have hmul : (beta : ℝ) ^ ex * ((beta : ℝ) ^ (fexp m))⁻¹
                = (beta : ℝ) ^ (ex - fexp m) := by
    -- zpow product identity written with an inverse
    have : (beta : ℝ) ^ (-(fexp m)) = ((beta : ℝ) ^ (fexp m))⁻¹ := by simp [zpow_neg]
    have := zpow_add₀ hbne ex (-(fexp m))
    simpa [sub_eq_add_neg, this]
  -- Since ex ≤ fexp ex and fexp m = fexp ex, we have ex - fexp m ≤ 0
  have hdiff_le0 : ex - fexp m ≤ 0 := by
    have : ex ≤ fexp m := by simpa [hfeq] using hlex
    exact sub_nonpos.mpr this
  -- For bases > 1, β^(t) ≤ 1 when t ≤ 0
  have hpow_le_one : (beta : ℝ) ^ (ex - fexp m) ≤ 1 := by
    -- Rewrite as β^(ex - fexp m) ≤ β^0 and use monotonicity on exponents
    have hbgt1R : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
    -- If difference is strictly negative, we get a strict <; otherwise it is 0
    cases lt_or_eq_of_le hdiff_le0 with
    | inl hlt0 =>
        have : (beta : ℝ) ^ (ex - fexp m) < (beta : ℝ) ^ 0 :=
          zpow_lt_zpow_right₀ hbgt1R hlt0
        exact le_of_lt (by simpa using this)
    | inr heq0 =>
        simpa [heq0]
  -- Chain the strict and non-strict inequalities
  have : abs x * ((beta : ℝ) ^ (fexp m))⁻¹ < 1 := by
    have := lt_of_lt_of_le (by simpa [hmul] using hstep) hpow_le_one
    simpa using this
  -- Replace fexp m by fexp ex and finish, also rewrite `abs` of product
  have habs_pow : abs (((beta : ℝ) ^ (fexp m))⁻¹) = ((beta : ℝ) ^ (fexp m))⁻¹ := by
    have : 0 ≤ ((beta : ℝ) ^ (fexp m))⁻¹ := le_of_lt (inv_pos.mpr hpow_pos_m)
    simpa [abs_of_nonneg this]
  -- Target uses `abs (x * β^(-...))`; rewrite to the established bound
  have : abs (x * ((beta : ℝ) ^ (fexp m))⁻¹) < 1 := by
    -- abs (x * t) = |x| * |t| with t ≥ 0 here
    simpa [abs_mul, habs_pow] using this
  -- Use fexp m = fexp ex to match the goal expression
  -- First rewrite the inverse back to a negative exponent
  have hnegExp : abs (x * (beta : ℝ) ^ (-(fexp m))) < 1 := by
    simpa [zpow_neg]
      using this
  -- Done: translate back to the original `(scaled_mantissa ...).run` form
  have hgoal : abs (x * (beta : ℝ) ^ (-(fexp ((mag beta x).run)))) < 1 := by
    simpa [hm] using hnegExp
  -- Conclude by rewriting the goal through the definition of `scaled_mantissa`.
  have hrun : (scaled_mantissa beta fexp x).run
      = x * (beta : ℝ) ^ (-(fexp ((mag beta x).run))) := by
    simp [scaled_mantissa, cexp]
  simpa [hrun]
    using hgoal

/-- Coq (Generic_fmt.v): mantissa_DN_small_pos

    If `β^(ex-1) ≤ x < β^ex` and `ex ≤ fexp ex`, then
    `Int.floor (x * β^(-fexp ex)) = 0`.
-/
theorem mantissa_DN_small_pos
    (beta : Int) (fexp : Int → Int)
    (x : ℝ) (ex : Int) :
    ((beta : ℝ) ^ (ex - 1) ≤ x ∧ x < (beta : ℝ) ^ ex) →
    ex ≤ fexp ex →
    1 < beta →
    Int.floor (x * (beta : ℝ) ^ (-(fexp ex))) = 0 := by
  intro hxbounds hex_le hβ
  rcases hxbounds with ⟨hx_low, hx_high⟩
  -- Basic positivity facts about the base and powers
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  have hb_gt1R : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ

  -- From the lower bound, x is strictly positive
  have hx_pos : 0 < x :=
    lt_of_lt_of_le (zpow_pos hbpos (ex - 1)) hx_low

  -- Define the scaled mantissa argument
  set c : Int := fexp ex with hc
  set scaled : ℝ := x * (beta : ℝ) ^ (-(c)) with hscaled

  -- Show 0 ≤ scaled using strict positivity
  have hscaled_nonneg : 0 ≤ scaled := by
    have hscale_pos : 0 < (beta : ℝ) ^ (-(c)) := zpow_pos hbpos _
    have : 0 < scaled := by
      simpa [hscaled] using mul_pos hx_pos hscale_pos
    exact le_of_lt this

  -- Upper bound: scaled < 1
  have hlt_scaled' : scaled < (beta : ℝ) ^ (ex - c) := by
    -- Multiply the strict upper bound x < β^ex by the positive factor β^(-c)
    have hscale_pos : 0 < (beta : ℝ) ^ (-(c)) := zpow_pos hbpos _
    have : x * (beta : ℝ) ^ (-(c)) < (beta : ℝ) ^ ex * (beta : ℝ) ^ (-(c)) :=
      mul_lt_mul_of_pos_right hx_high hscale_pos
    -- Combine exponents
    have hmul : (beta : ℝ) ^ ex * ((beta : ℝ) ^ c)⁻¹ = (beta : ℝ) ^ (ex - c) := by
      have hneg : (beta : ℝ) ^ (-(c)) = ((beta : ℝ) ^ c)⁻¹ := by
        simp [zpow_neg]
      have := (zpow_mul_sub (a := (beta : ℝ)) (hbne := hbne) (e := ex) (c := c))
      -- zpow_mul_sub: β^ex * β^(-c) = β^(ex - c)
      simpa [hneg]
        using this
    simpa [hscaled, hmul]
      using this

  -- Show (beta : ℝ) ^ (ex - c) ≤ 1 using hex_le : ex ≤ c
  have hle_one : (beta : ℝ) ^ (ex - c) ≤ 1 := by
    -- First, 0 ≤ c - ex
    have hk_nonneg : 0 ≤ c - ex := by simpa [hc] using sub_nonneg.mpr hex_le
    -- Rewrite β^(c - ex) as a Nat power
    have hzpow_toNat : (beta : ℝ) ^ (c - ex)
        = (beta : ℝ) ^ (Int.toNat (c - ex)) := by
      simpa using zpow_nonneg_toNat (beta : ℝ) (c - ex) hk_nonneg
    -- For β ≥ 1, 1 ≤ β^n for all n : ℕ
    have hb_ge1 : (1 : ℝ) ≤ (beta : ℝ) := le_of_lt hb_gt1R
    -- Prove 1 ≤ β^(Int.toNat (c - ex)) by induction on n
    have one_le_pow_nat' : ∀ n : Nat, (1 : ℝ) ≤ (beta : ℝ) ^ n := by
      intro n
      induction n with
      | zero => simpa
      | succ n ih =>
          have hpow_nonneg : 0 ≤ (beta : ℝ) ^ n :=
            pow_nonneg (le_of_lt hbpos) n
          have : (1 : ℝ) * 1 ≤ (beta : ℝ) ^ n * (beta : ℝ) := by
            exact mul_le_mul ih hb_ge1 (by norm_num) hpow_nonneg
          simpa [pow_succ] using this
    have one_le_pow_nat : (1 : ℝ) ≤ (beta : ℝ) ^ (c - ex) := by
      simpa [hzpow_toNat] using one_le_pow_nat' (Int.toNat (c - ex))
    -- From 1 ≤ β^(c - ex), deduce β^(ex - c) ≤ 1 by multiplying both sides
    have hmul_id : (beta : ℝ) ^ (ex - c) * (beta : ℝ) ^ (c - ex) = 1 := by
      have := (zpow_add₀ hbne (ex - c) (c - ex)).symm
      simpa [sub_add_cancel] using this
    have hfac_nonneg : 0 ≤ (beta : ℝ) ^ (ex - c) := by
      exact le_of_lt (zpow_pos hbpos _)
    have hmul_le := mul_le_mul_of_nonneg_left one_le_pow_nat hfac_nonneg
    simpa [hmul_id, one_mul] using hmul_le

  -- Combine the strict inequality with the upper bound ≤ 1
  have hscaled_lt_one : scaled < 1 := lt_of_lt_of_le hlt_scaled' hle_one

  -- Apply the floor characterization at 0: 0 ≤ scaled < 1 ⇒ ⌊scaled⌋ = 0
  have hfloor0 : Int.floor scaled = 0 := by
    have : ((0 : Int) : ℝ) ≤ scaled ∧ scaled < ((0 : Int) : ℝ) + 1 := by
      exact And.intro (by simpa using hscaled_nonneg) (by simpa using hscaled_lt_one)
    simpa using ((Int.floor_eq_iff).2 this)
  simpa [hscaled]
    using hfloor0

/-- Coq (Generic_fmt.v): mantissa_UP_small_pos

    If `β^(ex-1) ≤ x < β^ex` and `ex ≤ fexp ex`, then
    `Int.ceil (x * β^(-fexp ex)) = 1`.
-/
theorem mantissa_UP_small_pos
    (beta : Int) (fexp : Int → Int)
    (x : ℝ) (ex : Int) :
    ((beta : ℝ) ^ (ex - 1) ≤ x ∧ x < (beta : ℝ) ^ ex) →
    ex ≤ fexp ex →
    1 < beta →
    Int.ceil (x * (beta : ℝ) ^ (-(fexp ex))) = 1 := by
  intro hxbounds hex_le hβ
  rcases hxbounds with ⟨hx_low, hx_high⟩
  -- Base positivity and nonzeroness
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos

  -- From the lower bound, x is strictly positive
  have hx_pos : 0 < x :=
    lt_of_lt_of_le (zpow_pos hbpos (ex - 1)) hx_low

  -- Define the scaled mantissa argument
  set c : Int := fexp ex with hc
  set scaled : ℝ := x * (beta : ℝ) ^ (-(c)) with hscaled

  -- Show 0 < scaled using strict positivity and positive scaling factor
  have hscaled_pos : 0 < scaled := by
    have hscale_pos : 0 < (beta : ℝ) ^ (-(c)) := zpow_pos hbpos _
    simpa [hscaled] using mul_pos hx_pos hscale_pos

  -- Upper bound: scaled ≤ 1
  have hle_scaled_one : scaled ≤ 1 := by
    -- First, a strict upper bound by multiplying the strict upper bound on x
    have hlt_scaled' : scaled < (beta : ℝ) ^ (ex - c) := by
      have hscale_pos : 0 < (beta : ℝ) ^ (-(c)) := zpow_pos hbpos _
      have : x * (beta : ℝ) ^ (-(c)) < (beta : ℝ) ^ ex * (beta : ℝ) ^ (-(c)) :=
        mul_lt_mul_of_pos_right hx_high hscale_pos
      -- Combine exponents: β^ex * β^(-c) = β^(ex - c)
      have hmul : (beta : ℝ) ^ ex * ((beta : ℝ) ^ c)⁻¹ = (beta : ℝ) ^ (ex - c) := by
        have hneg : (beta : ℝ) ^ (-(c)) = ((beta : ℝ) ^ c)⁻¹ := by
          simp [zpow_neg]
        have := (zpow_mul_sub (a := (beta : ℝ)) (hbne := hbne) (e := ex) (c := c))
        simpa [hneg] using this
      simpa [hscaled, hmul] using this
    -- Then show (beta : ℝ) ^ (ex - c) ≤ 1 from ex ≤ c
    have hle_one : (beta : ℝ) ^ (ex - c) ≤ 1 := by
      have hk_nonneg : 0 ≤ c - ex := by
        simpa [hc] using sub_nonneg.mpr hex_le
      -- Rewrite β^(c - ex) as a natural power
      have hzpow_toNat : (beta : ℝ) ^ (c - ex)
          = (beta : ℝ) ^ (Int.toNat (c - ex)) := by
        simpa using zpow_nonneg_toNat (beta : ℝ) (c - ex) hk_nonneg
      -- Since 1 < β, we have 1 ≤ β^n for all n : ℕ
      have hb_ge1 : (1 : ℝ) ≤ (beta : ℝ) := le_of_lt (by exact_mod_cast hβ)
      have one_le_pow_nat' : ∀ n : Nat, (1 : ℝ) ≤ (beta : ℝ) ^ n := by
        intro n
        induction n with
        | zero => simpa
        | succ n ih =>
            have hpow_nonneg : 0 ≤ (beta : ℝ) ^ n := pow_nonneg (le_of_lt hbpos) n
            have : (1 : ℝ) * 1 ≤ (beta : ℝ) ^ n * (beta : ℝ) := by
              exact mul_le_mul ih hb_ge1 (by norm_num) hpow_nonneg
            simpa [pow_succ] using this
      have one_le_pow_nat : (1 : ℝ) ≤ (beta : ℝ) ^ (c - ex) := by
        simpa [hzpow_toNat] using one_le_pow_nat' (Int.toNat (c - ex))
      -- From 1 ≤ β^(c - ex), deduce β^(ex - c) ≤ 1 via zpow_add₀
      have hmul_id : (beta : ℝ) ^ (ex - c) * (beta : ℝ) ^ (c - ex) = 1 := by
        have := (zpow_add₀ hbne (ex - c) (c - ex)).symm
        simpa [sub_add_cancel] using this
      have hfac_nonneg : 0 ≤ (beta : ℝ) ^ (ex - c) := by
        exact le_of_lt (zpow_pos hbpos _)
      have hmul_le := mul_le_mul_of_nonneg_left one_le_pow_nat hfac_nonneg
      simpa [hmul_id, one_mul] using hmul_le
    -- Combine strict and non-strict to get ≤ 1
    exact le_trans (le_of_lt hlt_scaled') hle_one

  -- Apply the ceiling characterization at 1: 0 < scaled ≤ 1 ⇒ ⌈scaled⌉ = 1
  have : (((1 : Int) : ℝ) - 1) < scaled ∧ scaled ≤ ((1 : Int) : ℝ) := by
    -- ((1:ℤ):ℝ) - 1 = 0
    simpa using And.intro hscaled_pos hle_scaled_one
  simpa [hscaled] using ((Int.ceil_eq_iff).2 this)

/-- Coq (Generic_fmt.v): scaled_mantissa_lt_bpow

    The absolute value of the scaled mantissa is bounded by a power of β
    depending on `mag x` and `cexp x`.

    Note: We assume `1 < beta` to ensure positivity of the real base and use
    a non‑strict bound `≤`, which is robust when `|x| = (β : ℝ)^e`.
-/
theorem scaled_mantissa_lt_bpow
    (beta : Int) (fexp : Int → Int) (x : ℝ)
    (hβ : 1 < beta) :
    abs (scaled_mantissa beta fexp x).run ≤
      (beta : ℝ) ^ ((mag beta x).run - (cexp beta fexp x).run) := by
  -- Base positivity for the real base
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbneR : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  -- Notation
  set e : Int := (mag beta x).run
  set c : Int := (cexp beta fexp x).run
  -- Scaled mantissa as a product
  have hsm : (scaled_mantissa beta fexp x).run = x * (beta : ℝ) ^ (-c) := by
    unfold FloatSpec.Core.Generic_fmt.scaled_mantissa FloatSpec.Core.Generic_fmt.cexp
    rfl
  -- Positivity of the scaling factor
  have hscale_pos : 0 < (beta : ℝ) ^ (-c) := zpow_pos hbposR _
  have hscale_nonneg : 0 ≤ (beta : ℝ) ^ (-c) := le_of_lt hscale_pos
  -- Bound abs x by β^e
  have h_upper_abs : abs x ≤ (beta : ℝ) ^ e := by
    by_cases hx0 : x = 0
    · have : 0 ≤ (beta : ℝ) ^ e := le_of_lt (zpow_pos hbposR _)
      simpa [hx0, abs_zero] using this
    · have hb_gt1R : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
      have hlogβ_pos : 0 < Real.log (beta : ℝ) :=
        (Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)).mpr hb_gt1R
      have hxpos : 0 < abs x := abs_pos.mpr hx0
      set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
      have hmageq : e = Int.ceil L := by
        have : (mag beta x).run = Int.ceil L := by
          unfold FloatSpec.Core.Raux.mag
          simp [hx0, L]
        simpa [e] using this
      have hceil_ge : (L : ℝ) ≤ (Int.ceil L : ℝ) := by exact_mod_cast Int.le_ceil L
      have hmul_le : L * Real.log (beta : ℝ) ≤ (Int.ceil L : ℝ) * Real.log (beta : ℝ) :=
        mul_le_mul_of_nonneg_right hceil_ge (le_of_lt hlogβ_pos)
      have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
        have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
        calc
          L * Real.log (beta : ℝ)
              = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by rfl
          _   = Real.log (abs x) := by simpa [hne] using (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
      -- Relate log(β^e) to e * log β
      have hlog_zpow_e : Real.log ((beta : ℝ) ^ e) = (e : ℝ) * Real.log (beta : ℝ) := by
        simpa using Real.log_zpow hbposR e
      -- Get the desired log inequality in the form log |x| ≤ log(β^e)
      have hlog_le : Real.log (abs x) ≤ Real.log ((beta : ℝ) ^ e) := by
        have : Real.log (abs x) ≤ (e : ℝ) * Real.log (beta : ℝ) := by
          simpa [hL_mul, hmageq] using hmul_le
        simpa [hlog_zpow_e] using this
      -- convert back via exp monotonicity
      have hxpos' : 0 < abs x := hxpos
      -- Move to exponentials, rewriting to `exp (e * log β)` to avoid simp changing forms later
      have h_exp_le : abs x ≤ Real.exp ((e : ℝ) * Real.log (beta : ℝ)) := by
        have := (Real.log_le_iff_le_exp hxpos').1 hlog_le
        simpa [hlog_zpow_e] using this
      -- Show `exp (e * log β) = β^e` and conclude
      have hypos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR _
      have h_exp_eq_pow : Real.exp ((e : ℝ) * Real.log (beta : ℝ)) = (beta : ℝ) ^ e := by
        have : Real.exp (Real.log ((beta : ℝ) ^ e)) = (beta : ℝ) ^ e := Real.exp_log hypos
        simpa [hlog_zpow_e] using this
      exact by simpa [h_exp_eq_pow]
        using h_exp_le
  -- Rewrite |β^(-c)| using positivity, and collapse the RHS product
  have habs_scaled_tmp : abs (scaled_mantissa beta fexp x).run = abs (x * (beta : ℝ) ^ (-c)) := by
    simpa [hsm]
  have hpow_c_pos : 0 < (beta : ℝ) ^ c := zpow_pos hbposR _
  have hpow_c_nonneg : 0 ≤ (beta : ℝ) ^ c := le_of_lt hpow_c_pos
  have hscale_inv_nonneg : 0 ≤ ((beta : ℝ) ^ c)⁻¹ := inv_nonneg.mpr (le_of_lt hpow_c_pos)
  have habs_scaled : abs (scaled_mantissa beta fexp x).run = abs x * ((beta : ℝ) ^ c)⁻¹ := by
    -- |x * β^(-c)| = |x| * |β^(-c)| = |x| * |(β^c)⁻¹| = |x| * |β^c|⁻¹
    -- and since β^c ≥ 0, |β^c| = β^c
    have : abs (scaled_mantissa beta fexp x).run = abs x * (abs ((beta : ℝ) ^ c))⁻¹ := by
      simpa [abs_mul, zpow_neg] using habs_scaled_tmp
    simpa [abs_of_nonneg hpow_c_nonneg] using this
  -- Combine the pieces and collapse the RHS product
  calc
    abs (scaled_mantissa beta fexp x).run
        = abs x * ((beta : ℝ) ^ c)⁻¹ := habs_scaled
    _   ≤ (beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹ := mul_le_mul_of_nonneg_right h_upper_abs hscale_inv_nonneg
    _   = (beta : ℝ) ^ (e - c) := by
          simpa [zpow_neg] using
            (FloatSpec.Core.Generic_fmt.zpow_mul_sub (a := (beta : ℝ)) (hbne := hbneR) (e := e) (c := c))

/-- Coq (Generic_fmt.v):
Theorem mag_generic_gt:
  forall x, x <> 0%R ->
  generic_format x ->
  (cexp x < mag beta x)%Z.

Lean (spec): If `x ≠ 0` and `x` is in `generic_format`, then
the canonical exponent is strictly less than `mag beta x`.
-/
-- Helper: Upper bound |x| ≤ β^(mag x)
private theorem abs_le_bpow_mag
    (beta : Int) (x : ℝ) (hβ : 1 < beta) :
    abs x ≤ (beta : ℝ) ^ ((mag beta x).run) := by
  -- Base positivity for the real base
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  by_cases hx0 : x = 0
  · have : 0 ≤ (beta : ℝ) ^ ((mag beta 0).run) := le_of_lt (zpow_pos hbposR _)
    simpa [hx0, abs_zero] using this
  · -- Use the definition of mag via ceiling of logarithms
    have hb_gt1R : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
    have hlogβ_pos : 0 < Real.log (beta : ℝ) :=
      (Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)).mpr hb_gt1R
    have hxpos : 0 < abs x := abs_pos.mpr hx0
    set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
    have hmageq : (mag beta x).run = Int.ceil L := by
      unfold FloatSpec.Core.Raux.mag
      simp [hx0, L]
    have hceil_ge : (L : ℝ) ≤ (Int.ceil L : ℝ) := by exact_mod_cast Int.le_ceil L
    have hmul_le : L * Real.log (beta : ℝ) ≤ (Int.ceil L : ℝ) * Real.log (beta : ℝ) :=
      mul_le_mul_of_nonneg_right hceil_ge (le_of_lt hlogβ_pos)
    have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
      have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
      calc
        L * Real.log (beta : ℝ)
            = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by rfl
        _   = Real.log (abs x) := by simpa [hne] using (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
    -- Relate log(β^e) to e * log β with e = mag x
    set e : Int := (mag beta x).run
    have hlog_zpow_e : Real.log ((beta : ℝ) ^ e) = (e : ℝ) * Real.log (beta : ℝ) := by
      simpa using Real.log_zpow hbposR e
    -- Get log |x| ≤ log (β^e)
    have hlog_le : Real.log (abs x) ≤ Real.log ((beta : ℝ) ^ e) := by
      have : Real.log (abs x) ≤ (e : ℝ) * Real.log (beta : ℝ) := by
        simpa [hL_mul, hmageq] using hmul_le
      simpa [hlog_zpow_e] using this
    -- Move back via exp and rewrite β^e
    have hxpos' : 0 < abs x := hxpos
    have h_exp_le : abs x ≤ Real.exp ((e : ℝ) * Real.log (beta : ℝ)) := by
      have := (Real.log_le_iff_le_exp hxpos').1 hlog_le
      simpa [hlog_zpow_e] using this
    have hpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR _
    have h_exp_eq_pow : Real.exp ((e : ℝ) * Real.log (beta : ℝ)) = (beta : ℝ) ^ e := by
      have : Real.exp (Real.log ((beta : ℝ) ^ e)) = (beta : ℝ) ^ e := Real.exp_log hpow_pos
      simpa [hlog_zpow_e] using this
    simpa [h_exp_eq_pow] using h_exp_le

/-- Revised (Lean) version: with our `mag` definition (upper bound is non‑strict),
    generic numbers satisfy `cexp x ≤ (mag x).run`.

    This differs from the Coq statement (`<`) which relies on a strict upper
    bound in the characterization of `mag`. We document the change in notes.
-/
theorem mag_generic_gt
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ⦃⌜1 < beta ∧ x ≠ 0 ∧ (generic_format beta fexp x).run⌝⦄
    cexp beta fexp x
    ⦃⇓e => ⌜e ≤ (mag beta x).run⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hx_ne, hx_fmt⟩
  -- Notations for the canonical and magnitude exponents
  set M : Int := (mag beta x).run
  -- Reduce the computation of cexp
  unfold cexp
  -- The program returns `fexp M`, reduce the Hoare triple on Id
  simp [FloatSpec.Core.Raux.mag]
  -- We now show `fexp M ≤ M`
  -- From generic_format, expand the reconstruction equality at x
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hx_eq : x
      = (((Ztrunc (x * (beta : ℝ) ^ (-(fexp M)))).run : Int) : ℝ)
          * (beta : ℝ) ^ (fexp M) := by
    -- Unfold `generic_format` at x and simplify
    simpa [generic_format, scaled_mantissa, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Raux.mag]
      using hx_fmt
  -- The truncated mantissa must be nonzero since x ≠ 0 and β^e ≠ 0
  have hZ_ne : (Ztrunc (x * (beta : ℝ) ^ (-(fexp M)))).run ≠ 0 := by
    -- Name the truncated mantissa to simplify rewriting
    set n : Int := (Ztrunc (x * (beta : ℝ) ^ (-(fexp M)))).run with hn
    intro hzero
    -- If n = 0, then the reconstruction equality forces x = 0
    have hx'' : x = (((n : Int) : ℝ) * (beta : ℝ) ^ (fexp M)) := by
      simpa [hn] using hx_eq
    have hx0' : x = (((0 : Int) : ℝ) * (beta : ℝ) ^ (fexp M)) := by
      simpa [hzero] using hx''
    have : x = 0 := by simpa using hx0'
    exact hx_ne this
  -- Lower bound: β^(fexp M) ≤ |x|
  have hpow_pos : 0 < (beta : ℝ) ^ (fexp M) := zpow_pos hbposR _
  -- For a nonzero integer, its absolute value as a real is ≥ 1
  have h_abs_m_ge1 : (1 : ℝ) ≤ |(((Ztrunc (x * (beta : ℝ) ^ (-(fexp M)))).run : Int) : ℝ)| := by
    set n : Int := (Ztrunc (x * (beta : ℝ) ^ (-(fexp M)))).run with hn
    have hne : n ≠ 0 := by simpa [hn] using hZ_ne
    -- natAbs n > 0 when n ≠ 0, hence 1 ≤ natAbs n
    have hnat_pos : 0 < Int.natAbs n := by
      -- natAbs n = 0 ↔ n = 0
      exact Nat.pos_of_ne_zero (by
        intro h0
        exact hne (Int.natAbs_eq_zero.mp h0))
    have hnat_ge1 : (1 : ℝ) ≤ (Int.natAbs n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hnat_pos)
    -- Relate |(n : ℝ)| to (Int.natAbs n : ℝ)
    have h_abs_natAbs : (Int.natAbs n : ℝ) = |(n : ℝ)| := by
      simpa [Int.cast_natAbs, Int.cast_abs]
    simpa [hn, h_abs_natAbs] using hnat_ge1
  have h_le_abs : (beta : ℝ) ^ (fexp M) ≤ abs x := by
    -- |x| = |m| * β^(fexp M) with |m| ≥ 1 and β^(fexp M) > 0
    have hx_abs :
        abs x =
          |(((Ztrunc (x * (beta : ℝ) ^ (-(fexp M)))).run : Int) : ℝ)|
            * (beta : ℝ) ^ (fexp M) := by
      -- Step 1: use the reconstruction equality inside the absolute value
      have hx_abs0 :
          abs x =
            abs ((((Ztrunc (x * (beta : ℝ) ^ (-(fexp M)))).run : Int) : ℝ)
                  * (beta : ℝ) ^ (fexp M)) := by
        simpa using congrArg abs hx_eq
      -- Step 2: split the absolute value of the product
      have hx_abs1 :
          abs x =
            abs (((Ztrunc (x * (beta : ℝ) ^ (-(fexp M)))).run : Int) : ℝ)
              * abs ((beta : ℝ) ^ (fexp M)) := by
        simpa [abs_mul] using hx_abs0
      -- Step 3: since β^(fexp M) ≥ 0, |β^(fexp M)| = β^(fexp M)
      have hpow_abs : abs ((beta : ℝ) ^ (fexp M)) = (beta : ℝ) ^ (fexp M) := by
        simpa [abs_of_nonneg (le_of_lt hpow_pos)]
      simpa [hpow_abs] using hx_abs1
    have hstep : (beta : ℝ) ^ (fexp M)
        ≤ |(((Ztrunc (x * (beta : ℝ) ^ (-(fexp M)))).run : Int) : ℝ)| * (beta : ℝ) ^ (fexp M) := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right h_abs_m_ge1 (le_of_lt hpow_pos)
    simpa [hx_abs] using hstep
  -- Upper bound: |x| ≤ β^M (by definition of mag)
  have h_abs_le : abs x ≤ (beta : ℝ) ^ M := abs_le_bpow_mag beta x hβ
  -- Chain inequalities: β^(fexp M) ≤ |x| ≤ β^M ⇒ fexp M ≤ M
  have hpow_le : (beta : ℝ) ^ (fexp M) ≤ (beta : ℝ) ^ M := le_trans h_le_abs h_abs_le
  -- Convert back to the exponents using monotonicity (bases > 1)
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- Use Raux helper lemma to relate powers and exponents
  have : (fexp M) ≤ M := by
    -- le_bpow: from (beta^e1) ≤ (beta^e2) under 1 < beta, deduce e1 ≤ e2
    have hmono := FloatSpec.Core.Raux.le_bpow (beta := beta) (e1 := fexp M) (e2 := M)
    -- Run the Hoare triple on the pure values to extract the inequality
    have := (hmono ⟨hβ, hpow_le⟩)
    simpa [FloatSpec.Core.Raux.le_bpow_check, wp, PostCond.noThrow, Id.run, pure]
      using this
  -- This matches the simplified goal (unfolding the definition of mag on runs)
  simpa [M, FloatSpec.Core.Raux.mag]

/-- Coq (Generic_fmt.v): abs_lt_bpow_prec

    Lean adaptation: with our `mag` characterization using a non‑strict upper
    bound, we obtain a non‑strict inequality. Under `1 < beta` and the
    hypothesis `∀ e, e - prec ≤ fexp e`, for any real `x` we have
    `|x| ≤ β^(prec + cexp(x))`.

    Note: Coq’s original statement is strict (`<`). See PROOF_CHANGES.md for
    rationale about the relaxed inequality in this port.
-/
theorem abs_lt_bpow_prec
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (prec : Int) :
    1 < beta →
    (∀ e : Int, e - prec ≤ fexp e) →
    ∀ x : ℝ, abs x ≤ (beta : ℝ) ^ (prec + (cexp beta fexp x).run) := by
  intro hβ hbound x
  -- Notations for magnitude and canonical exponent
  set M : Int := (mag beta x).run
  set c : Int := (cexp beta fexp x).run
  -- From the generic magnitude bound: |x| ≤ β^M
  have h_abs_le : abs x ≤ (beta : ℝ) ^ M :=
    abs_le_bpow_mag beta x hβ
  -- From the hypothesis on `fexp`, instantiated at `M`, we get `M - prec ≤ c`
  have hM_sub_prec_le_c : M - prec ≤ c := by
    simpa [c, M, cexp] using hbound M
  -- Add `prec` to both sides to obtain `M ≤ c + prec` (commutes to `prec + c`)
  have hM_le_prec_add_c : M ≤ prec + c := by
    -- add both sides by `prec` and rewrite `M - prec + prec = M`
    have := add_le_add_right hM_sub_prec_le_c prec
    simpa [sub_add_cancel, add_comm, add_left_comm, add_assoc] using this
  -- Monotonicity of powers in the exponent for bases > 1
  have hpow_mono := FloatSpec.Core.Raux.bpow_le (beta := beta) (e1 := M) (e2 := prec + c)
  have h_bpow_le : (beta : ℝ) ^ M ≤ (beta : ℝ) ^ (prec + c) := by
    have := (hpow_mono ⟨hβ, hM_le_prec_add_c⟩)
    simpa [FloatSpec.Core.Raux.bpow_le_check, wp, PostCond.noThrow, Id.run, pure]
      using this
  -- Chain the inequalities
  exact le_trans h_abs_le h_bpow_le

/-- Coq (Generic_fmt.v): generic_format_discrete

    If x lies strictly between two consecutive representable values at the
    canonical exponent `e := cexp x`, then x is not in the generic format.
-/
theorem generic_format_discrete
    (beta : Int) (fexp : Int → Int)
    (x : ℝ) (m : Int) :
    1 < beta →
    (let e := (cexp beta fexp x).run;
     ((F2R (FlocqFloat.mk m e : FlocqFloat beta)).run < x ∧
      x < (F2R (FlocqFloat.mk (m + 1) e : FlocqFloat beta)).run))
    → ¬ (generic_format beta fexp x).run := by
  intro hβ hx
  -- Name the canonical exponent and the common scaling factor s = β^e
  set e : Int := (cexp beta fexp x).run with he
  set s : ℝ := (beta : ℝ) ^ e with hs
  -- Unpack the strict inequalities around x
  have hxI : ((F2R (FlocqFloat.mk m e : FlocqFloat beta)).run < x ∧
               x < (F2R (FlocqFloat.mk (m + 1) e : FlocqFloat beta)).run) := by
    simpa [he] using hx
  have hxL : ((m : ℝ) * s) < x := by
    simpa [FloatSpec.Core.Defs.F2R, hs] using (And.left hxI)
  have hxR : x < (((m + 1 : Int) : ℝ) * s) := by
    simpa [FloatSpec.Core.Defs.F2R, hs] using (And.right hxI)
  -- Base positivity transfers to positive scaling factor s = β^e
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hspos : 0 < s := by
    -- zpow_pos requires positivity of the base on ℝ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    simpa [hs] using (zpow_pos hbposR e)
  -- Assume x is in generic format and derive a contradiction on the integer mantissa
  intro hx_fmt
  -- Expand the reconstruction equality given by generic_format at x
  have hx_eq : x
      = (((Ztrunc (x * (beta : ℝ) ^ (-(fexp ((mag beta x).run))))).run : Int) : ℝ)
          * (beta : ℝ) ^ (fexp ((mag beta x).run)) := by
    simpa [generic_format, scaled_mantissa, FloatSpec.Core.Defs.F2R]
      using hx_fmt
  -- Rewrite the exponent through the chosen name e
  have hx_eq' : x = (((Ztrunc (x * (beta : ℝ) ^ (-e))).run : Int) : ℝ) * s := by
    -- cexp beta fexp x = fexp (mag beta x).run, hence e is that value
    have : e = fexp ((mag beta x).run) := by
      simpa [cexp] using he
    simpa [hs, this] using hx_eq
  -- Denote the integer mantissa n produced by truncation
  set n : Int := (Ztrunc (x * (beta : ℝ) ^ (-e))).run with hn
  have hx_eq'' : x = ((n : Int) : ℝ) * s := by simpa [hn] using hx_eq'
  -- With s > 0: we have m < n < m+1 (impossible for integer n)
  -- s > 0: multiply-preserves-order, so m < n < m+1
  have hmn_lt : (m : ℝ) < (n : ℝ) := by
    have : (m : ℝ) * s < (n : ℝ) * s := by simpa [hx_eq''] using hxL
    exact (lt_of_mul_lt_mul_right this (le_of_lt hspos))
  have hnm1_lt : (n : ℝ) < (m + 1 : Int) := by
    have : (n : ℝ) * s < ((m + 1 : Int) : ℝ) * s := by simpa [hx_eq''] using hxR
    exact (lt_of_mul_lt_mul_right this (le_of_lt hspos))
  -- Move back to integers
  have hmn_int : m < n := (Int.cast_lt).1 (by simpa using hmn_lt)
  have hnm1_int : n < m + 1 := (Int.cast_lt).1 (by simpa using hnm1_lt)
  have : n ≤ m := Int.lt_add_one_iff.1 hnm1_int
  exact (not_lt_of_ge this) hmn_int

/-- Coq (Generic_fmt.v): generic_format_ge_bpow

    If all canonical exponents are bounded below by `emin`, then any
    strictly positive representable real number is at least `β^emin`.
-/
theorem generic_format_ge_bpow
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (emin : Int) :
    (1 < beta ∧ ∀ e : Int, emin ≤ fexp e) →
    ∀ x : ℝ, 0 < x → (generic_format beta fexp x).run → (beta : ℝ) ^ emin ≤ x := by
  intro hpre x hxpos hx_fmt
  -- Split hypotheses and basic positivity about the base
  rcases hpre with ⟨hβ, hbound⟩
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  -- Name the canonical exponent and the corresponding power
  set e : Int := fexp ((mag beta x).run) with he
  set s : ℝ := (beta : ℝ) ^ e with hs
  have hspos : 0 < s := by simpa [hs] using (zpow_pos hbposR e)
  have hsnonneg : 0 ≤ s := le_of_lt hspos

  -- Expand generic_format at x to obtain the exact reconstruction equality
  have hx_eq_raw : x
      = (((Ztrunc (x * (beta : ℝ) ^ (-(fexp ((mag beta x).run))))).run : Int) : ℝ)
          * (beta : ℝ) ^ (fexp ((mag beta x).run)) := by
    simpa [generic_format, scaled_mantissa, cexp, FloatSpec.Core.Defs.F2R]
      using hx_fmt
  -- Rewrite that equality using the chosen name e for the exponent
  have hx_eq : x = (((Ztrunc (x * (beta : ℝ) ^ (-e))).run : Int) : ℝ) * s := by
    have : e = fexp ((mag beta x).run) := by simpa [he]
    simpa [hs, this] using hx_eq_raw

  -- Denote the integer mantissa n produced by truncation
  set n : Int := (Ztrunc (x * (beta : ℝ) ^ (-e))).run with hn
  have hx_eq' : x = ((n : Int) : ℝ) * s := by simpa [hn] using hx_eq

  -- From x > 0 and s > 0, deduce n ≥ 1 (as an integer)
  have hn_pos_real : 0 < (n : ℝ) := by
    have : (0 : ℝ) * s < (n : ℝ) * s := by
      simpa [hx_eq', zero_mul] using hxpos
    exact (lt_of_mul_lt_mul_right this hsnonneg)
  have hn_pos_int : 0 < n := (Int.cast_lt).1 (by simpa using hn_pos_real)
  have h1_le_n : 1 ≤ n := by
    -- 0 + 1 ≤ n  ↔  0 < n
    simpa [Int.zero_add] using (Int.add_one_le_iff.mpr hn_pos_int)
  have h1_le_n_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1_le_n

  -- Therefore, s ≤ n * s, hence β^e ≤ x
  have h_pow_le_x : (beta : ℝ) ^ e ≤ x := by
    -- 1 * s ≤ n * s using s ≥ 0 and 1 ≤ n
    have : (1 : ℝ) * s ≤ (n : ℝ) * s := by
      exact mul_le_mul_of_nonneg_right h1_le_n_real hsnonneg
    simpa [hs, hx_eq', one_mul] using this

  -- Since emin ≤ fexp t for all t, in particular emin ≤ e
  have h_emin_le_e : emin ≤ e := by
    -- e = fexp (mag beta x).run
    have : e = fexp ((mag beta x).run) := by simpa [he]
    simpa [this] using hbound ((mag beta x).run)

  -- Monotonicity of zpow in the exponent for bases ≥ 1 gives β^emin ≤ β^e
  have hb_ge1R : (1 : ℝ) ≤ (beta : ℝ) := le_of_lt (by exact_mod_cast hβ)
  have h_pow_mono : (beta : ℝ) ^ emin ≤ (beta : ℝ) ^ e := by
    -- Use standard monotonicity of zpow on ℝ when the base is ≥ 1
    exact zpow_le_zpow_right₀ hb_ge1R h_emin_le_e

  -- Chain the inequalities
  exact le_trans h_pow_mono h_pow_le_x


-- Section: Format intersection and union

/-- Intersection of two generic formats -/
def generic_format_inter (beta : Int) (fexp1 fexp2 : Int → Int) (x : ℝ) : Prop :=
  (generic_format beta fexp1 x).run ∧ (generic_format beta fexp2 x).run

/-- Union of two generic formats -/
def generic_format_union (beta : Int) (fexp1 fexp2 : Int → Int) (x : ℝ) : Prop :=
  (generic_format beta fexp1 x).run ∨ (generic_format beta fexp2 x).run



end BasicProperties

-- Section: Rounding to integers (Coq: Zrnd_*)

/-- Valid integer rounding function

    A rounding function `rnd : ℝ → Int` is valid if it is monotone and
    agrees with the identity on integers. This mirrors Coq's `Valid_rnd`.
-/
class Valid_rnd (rnd : ℝ → Int) : Prop where
  /-- Monotonicity of integer rounding -/
  Zrnd_le : ∀ x y : ℝ, x ≤ y → rnd x ≤ rnd y
  /-- Agreement on integers: rounding an integer returns it -/
  Zrnd_IZR : ∀ n : Int, rnd (n : ℝ) = n

/-- Coq (Generic_fmt.v): Zrnd_DN_or_UP

    Any valid integer rounding is either floor or ceiling on every input.
    We state it in hoare-triple style around `pure (rnd x)`.
-/
theorem Zrnd_DN_or_UP (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (rnd x) : Id Int)
    ⦃⇓z => ⌜z = Int.floor x ∨ z = Int.ceil x⌝⦄ := by
  intro _; classical
  -- Reduce the Hoare triple on Id; goal becomes about `rnd x` directly
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Notations
  set n : Int := Int.floor x
  set c : Int := Int.ceil x
  -- Lower bound: n ≤ rnd x (monotonicity and identity on integers)
  have h_floor_le : (n : ℝ) ≤ x := by simpa [n] using (Int.floor_le x)
  have h1 : n ≤ rnd x := by
    have := (Valid_rnd.Zrnd_le (rnd := rnd) ((n : Int) : ℝ) x h_floor_le)
    simpa [Valid_rnd.Zrnd_IZR (rnd := rnd) n] using this
  -- Upper bound via ceiling: rnd x ≤ c
  have h_x_le_ceil : x ≤ (c : ℝ) := by simpa [c] using (Int.le_ceil x)
  have h2 : rnd x ≤ c := by
    have := (Valid_rnd.Zrnd_le (rnd := rnd) x ((c : Int) : ℝ) h_x_le_ceil)
    simpa [Valid_rnd.Zrnd_IZR (rnd := rnd) c] using this
  -- Also, c ≤ n + 1 (from x < n+1 and the characterization of ceil)
  have hceil_le : c ≤ n + 1 := by
    -- x < (n : ℝ) + 1 ⇒ x ≤ (n : ℝ) + 1
    have hxlt : x < (n : ℝ) + 1 := by simpa [n] using (Int.lt_floor_add_one x)
    have hxle : x ≤ (n : ℝ) + 1 := le_of_lt hxlt
    -- Coerce the RHS to an `Int` cast to use `Int.ceil_le`
    have hxle' : x ≤ ((n + 1 : Int) : ℝ) := by
      simpa [Int.cast_add, Int.cast_one] using hxle
    -- `Int.ceil_le` converts a real upper bound into an integer upper bound on the ceiling
    simpa [c] using (Int.ceil_le).mpr hxle'
  -- Case split on whether rnd x hits the lower endpoint n
  by_cases hEq : rnd x = n
  · -- rnd x = ⌊x⌋
    exact Or.inl (by simpa [n] using hEq)
  · -- Otherwise, since n ≤ rnd x and rnd x ≠ n, we have n + 1 ≤ rnd x
    have hlt : n < rnd x := lt_of_le_of_ne h1 (Ne.symm hEq)
    have h3 : n + 1 ≤ rnd x := (Int.add_one_le_iff.mpr hlt)
    -- Chain: n + 1 ≤ rnd x ≤ c and c ≤ n + 1 ⇒ c = n + 1
    have hcn1 : c = n + 1 := le_antisymm hceil_le (le_trans h3 h2)
    -- With c = n + 1, we also get c ≤ rnd x, hence equality rnd x = c
    have hcle : c ≤ rnd x := by simpa [hcn1] using h3
    have hrnd_eq_c : rnd x = c := le_antisymm h2 hcle
    exact Or.inr (by simpa [c] using hrnd_eq_c)

/-- Coq (Generic_fmt.v): Zrnd_ZR_or_AW

    Any valid integer rounding is either truncation (toward zero)
    or away-from-zero rounding on every input.
    We phrase the postcondition using the helper functions from Raux.
-/
theorem Zrnd_ZR_or_AW (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (rnd x) : Id Int)
    ⦃⇓z => ⌜z = (FloatSpec.Core.Raux.Ztrunc x).run ∨ z = (FloatSpec.Core.Raux.Zaway x).run⌝⦄ := by
  intro _; classical
  -- Reduce Hoare triple on Id to a pure goal about `rnd x`.
  simp [wp, PostCond.noThrow, Id.run, pure, FloatSpec.Core.Raux.Ztrunc, FloatSpec.Core.Raux.Zaway]
  -- Notations for floor and ceil
  set n : Int := Int.floor x
  set c : Int := Int.ceil x
  -- Lower and upper bounds via monotonicity + identity on integers
  have h_floor_le : (n : ℝ) ≤ x := by simpa [n] using (Int.floor_le x)
  have h1 : n ≤ rnd x := by
    have := (Valid_rnd.Zrnd_le (rnd := rnd) ((n : Int) : ℝ) x h_floor_le)
    simpa [Valid_rnd.Zrnd_IZR (rnd := rnd) n] using this
  have h_x_le_ceil : x ≤ (c : ℝ) := by simpa [c] using (Int.le_ceil x)
  have h2 : rnd x ≤ c := by
    have := (Valid_rnd.Zrnd_le (rnd := rnd) x ((c : Int) : ℝ) h_x_le_ceil)
    simpa [Valid_rnd.Zrnd_IZR (rnd := rnd) c] using this
  -- Also, c ≤ n + 1
  have hceil_le : c ≤ n + 1 := by
    have hxlt : x < (n : ℝ) + 1 := by simpa [n] using (Int.lt_floor_add_one x)
    have hxle : x ≤ (n : ℝ) + 1 := le_of_lt hxlt
    have hxle' : x ≤ ((n + 1 : Int) : ℝ) := by simpa [Int.cast_add, Int.cast_one] using hxle
    simpa [c] using (Int.ceil_le).mpr hxle'
  -- Split on the sign of x and translate floor/ceil to trunc/away accordingly.
  by_cases hx : x < 0
  ·
    -- For x < 0, goal simplifies to: rnd x = c ∨ rnd x = n.
    -- Case split on whether rnd x hits the lower endpoint n
    by_cases hEq : rnd x = n
    · -- rnd x = ⌊x⌋ ⇒ choose the right disjunct
      exact Or.inr (by simpa [hx, c, n] using hEq)
    · -- Otherwise, from n ≤ rnd x and rnd x ≠ n, deduce n+1 ≤ rnd x
      have hlt : n < rnd x := lt_of_le_of_ne h1 (Ne.symm hEq)
      have h3 : n + 1 ≤ rnd x := (Int.add_one_le_iff.mpr hlt)
      -- Chain: c ≤ n + 1 and rnd x ≤ c ⇒ rnd x = c
      have hrnd_eq_c : rnd x = c := by
        have : c ≤ rnd x := le_trans hceil_le h3
        exact le_antisymm h2 this
      -- Choose the left disjunct
      exact Or.inl (by simpa [hx, c, n] using hrnd_eq_c)
  ·
    -- For x ≥ 0, goal simplifies to: rnd x = n ∨ rnd x = c.
    -- Case split on whether rnd x hits the lower endpoint n
    by_cases hEq : rnd x = n
    · -- rnd x = ⌊x⌋ ⇒ choose the left disjunct
      exact Or.inl (by simpa [hx, c, n] using hEq)
    · -- Otherwise, from n ≤ rnd x and rnd x ≠ n, deduce n+1 ≤ rnd x
      have hlt : n < rnd x := lt_of_le_of_ne h1 (Ne.symm hEq)
      have h3 : n + 1 ≤ rnd x := (Int.add_one_le_iff.mpr hlt)
      -- Chain: c ≤ n + 1 and rnd x ≤ c ⇒ rnd x = c
      have hrnd_eq_c : rnd x = c := by
        have : c ≤ rnd x := le_trans hceil_le h3
        exact le_antisymm h2 this
      -- Choose the right disjunct
      exact Or.inr (by simpa [hx, c, n] using hrnd_eq_c)

-- Section: Znearest (round to nearest with tie-breaking choice)

/-- Coq (Generic_fmt.v): Znearest

    Round to nearest integer using a choice function on ties at half.
    If `Rcompare (x - ⌊x⌋) (1/2)` is:
    - Lt: return `⌊x⌋`
    - Eq: return `if choice ⌊x⌋ then ⌈x⌉ else ⌊x⌋`
    - Gt: return `⌈x⌉`
-/
noncomputable def Znearest (choice : Int → Bool) (x : ℝ) : Int :=
  let f := (FloatSpec.Core.Raux.Zfloor x).run
  let c := (FloatSpec.Core.Raux.Zceil x).run
  match (FloatSpec.Core.Raux.Rcompare (x - (f : ℝ)) (1/2)).run with
  | (-1) => f
  | 0    => if choice f then c else f
  | _    => c

/-- Coq (Generic_fmt.v): Znearest_DN_or_UP

    For any x, `Znearest x` is either `⌊x⌋` or `⌈x⌉` (depending on the
    comparison and the tie-breaking choice). We state it using the
    Hoare-triple style around the pure computation of `Znearest`.
-/
theorem Znearest_DN_or_UP (choice : Int → Bool) (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (Znearest choice x) : Id Int)
    ⦃⇓z => ⌜z = (FloatSpec.Core.Raux.Zfloor x).run ∨ z = (FloatSpec.Core.Raux.Zceil x).run⌝⦄ := by
  intro _; classical
  -- Reduce the Hoare triple on Id first
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Now prove Znearest returns either floor or ceil by case analysis
  -- Use 2⁻¹ to match pretty-printed normalization of 1/2 in goals
  set r : Int := (FloatSpec.Core.Raux.Rcompare (x - ((FloatSpec.Core.Raux.Zfloor x).run : ℝ)) (2⁻¹)).run with hr
  -- Expand Znearest to a single match for rewriting
  have hZ :
      Znearest choice x =
        (match (FloatSpec.Core.Raux.Rcompare (x - ((FloatSpec.Core.Raux.Zfloor x).run : ℝ)) (1/2)).run with
          | -1 => (FloatSpec.Core.Raux.Zfloor x).run
          | 0 => if choice (FloatSpec.Core.Raux.Zfloor x).run then (FloatSpec.Core.Raux.Zceil x).run else (FloatSpec.Core.Raux.Zfloor x).run
          | _ => (FloatSpec.Core.Raux.Zceil x).run) := by
    unfold Znearest; simp
  by_cases hneg : r = (-1)
  · -- Lt branch: Znearest = ⌊x⌋
    have hL :
        (match (FloatSpec.Core.Raux.Rcompare (x - ((FloatSpec.Core.Raux.Zfloor x).run : ℝ)) (2⁻¹)).run with
          | -1 => (FloatSpec.Core.Raux.Zfloor x).run
          | 0 => if choice (FloatSpec.Core.Raux.Zfloor x).run then (FloatSpec.Core.Raux.Zceil x).run else (FloatSpec.Core.Raux.Zfloor x).run
          | _ => (FloatSpec.Core.Raux.Zceil x).run)
        = (FloatSpec.Core.Raux.Zfloor x).run := by
      -- Rewrite the scrutinee to r and discharge by the -1 branch
      simp [hr.symm, hneg]
    exact Or.inl (by simpa [hZ] using hL)
  · by_cases heq : r = 0
    · -- Eq branch: Znearest = if choice ⌊x⌋ then ⌈x⌉ else ⌊x⌋
      by_cases hch : choice (FloatSpec.Core.Raux.Zfloor x).run
      · -- choose ceil
        have hR :
            (match (FloatSpec.Core.Raux.Rcompare (x - ((FloatSpec.Core.Raux.Zfloor x).run : ℝ)) (2⁻¹)).run with
              | -1 => (FloatSpec.Core.Raux.Zfloor x).run
              | 0 => if choice (FloatSpec.Core.Raux.Zfloor x).run then (FloatSpec.Core.Raux.Zceil x).run else (FloatSpec.Core.Raux.Zfloor x).run
              | _ => (FloatSpec.Core.Raux.Zceil x).run)
            = (FloatSpec.Core.Raux.Zceil x).run := by
          -- Rewrite the scrutinee to r and discharge by the 0-branch with hch
          simp [hr.symm, heq, hch]
        exact Or.inr (by simpa [hZ] using hR)
      · -- choose floor
        have hL :
            (match (FloatSpec.Core.Raux.Rcompare (x - ((FloatSpec.Core.Raux.Zfloor x).run : ℝ)) (2⁻¹)).run with
              | -1 => (FloatSpec.Core.Raux.Zfloor x).run
              | 0 => if choice (FloatSpec.Core.Raux.Zfloor x).run then (FloatSpec.Core.Raux.Zceil x).run else (FloatSpec.Core.Raux.Zfloor x).run
              | _ => (FloatSpec.Core.Raux.Zceil x).run)
            = (FloatSpec.Core.Raux.Zfloor x).run := by
          -- Rewrite the scrutinee to r and discharge by the 0-branch with ¬hch
          simp [hr.symm, heq, hch]
        exact Or.inl (by simpa [hZ] using hL)
    · -- Gt branch: Znearest = ⌈x⌉
      have hR :
          (match (FloatSpec.Core.Raux.Rcompare (x - ((FloatSpec.Core.Raux.Zfloor x).run : ℝ)) (2⁻¹)).run with
            | -1 => (FloatSpec.Core.Raux.Zfloor x).run
            | 0 => if choice (FloatSpec.Core.Raux.Zfloor x).run then (FloatSpec.Core.Raux.Zceil x).run else (FloatSpec.Core.Raux.Zfloor x).run
            | _ => (FloatSpec.Core.Raux.Zceil x).run)
          = (FloatSpec.Core.Raux.Zceil x).run := by
        -- Rewrite the scrutinee to r and discharge by the default branch
        have h1 : r ≠ -1 := hneg
        have h2 : r ≠ 0 := heq
        simp [hr.symm, h1, h2]
      exact Or.inr (by simpa [hZ] using hR)

/-- Check pair for Znearest_ge_floor: returns (⌊x⌋, Znearest x) -/
noncomputable def Znearest_ge_floor_check (choice : Int → Bool) (x : ℝ) : Id (Int × Int) :=
  do
    let f ← FloatSpec.Core.Raux.Zfloor x
    pure (f, Znearest choice x)

/-- Coq (Generic_fmt.v): Znearest_ge_floor

    Always `⌊x⌋ ≤ Znearest x`.
-/
theorem Znearest_ge_floor (choice : Int → Bool) (x : ℝ) :
    ⦃⌜True⌝⦄
    Znearest_ge_floor_check choice x
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _
  unfold Znearest_ge_floor_check
  -- Reduce the Hoare triple on Id to a pure inequality
  simp [wp, PostCond.noThrow, Id.run, bind, pure]
  -- We must show: ⌊x⌋ ≤ Znearest x. Use the dichotomy floor/ceil.
  have hdisj :
      Znearest choice x = (FloatSpec.Core.Raux.Zfloor x).run ∨
      Znearest choice x = (FloatSpec.Core.Raux.Zceil x).run := by
    -- Extract the disjunction from Znearest_DN_or_UP
    have h := (Znearest_DN_or_UP choice x) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure] using h
  -- Also, we have ⌊x⌋ ≤ ⌈x⌉ as integers
  have h_floor_le_ceil :
      (FloatSpec.Core.Raux.Zfloor x).run ≤ (FloatSpec.Core.Raux.Zceil x).run := by
    have h1 : ((FloatSpec.Core.Raux.Zfloor x).run : ℝ) ≤ x := by
      simpa [FloatSpec.Core.Raux.Zfloor] using (Int.floor_le x)
    have h2 : x ≤ ((FloatSpec.Core.Raux.Zceil x).run : ℝ) := by
      simpa [FloatSpec.Core.Raux.Zceil] using (Int.le_ceil x)
    have hreal : ((FloatSpec.Core.Raux.Zfloor x).run : ℝ)
                  ≤ ((FloatSpec.Core.Raux.Zceil x).run : ℝ) :=
      le_trans h1 h2
    exact (by exact_mod_cast hreal)
  -- Finish by cases on Znearest
  have hgoal : (FloatSpec.Core.Raux.Zfloor x).run ≤ Znearest choice x := by
    cases hdisj with
    | inl h =>
        -- Znearest = ⌊x⌋
        simpa [h] using
          (le_rfl : (FloatSpec.Core.Raux.Zfloor x).run ≤ (FloatSpec.Core.Raux.Zfloor x).run)
    | inr h =>
        -- Znearest = ⌈x⌉
        simpa [h] using h_floor_le_ceil
  exact hgoal

/- Check pair for Znearest_le_ceil: returns (Znearest x, ⌈x⌉) -/
noncomputable def Znearest_le_ceil_check (choice : Int → Bool) (x : ℝ) : Id (Int × Int) :=
  do
    let c ← FloatSpec.Core.Raux.Zceil x
    pure (Znearest choice x, c)

/-- Coq (Generic_fmt.v): Znearest_le_ceil

    Always `Znearest x ≤ ⌈x⌉`.
-/
theorem Znearest_le_ceil (choice : Int → Bool) (x : ℝ) :
    ⦃⌜True⌝⦄
    Znearest_le_ceil_check choice x
    ⦃⇓p => ⌜p.1 ≤ p.2⌝⦄ := by
  intro _
  unfold Znearest_le_ceil_check
  -- Reduce the Hoare triple on Id to a pure inequality
  simp [wp, PostCond.noThrow, Id.run, bind, pure]
  -- We must show: Znearest x ≤ ⌈x⌉. Use the dichotomy floor/ceil.
  have hdisj :
      Znearest choice x = (FloatSpec.Core.Raux.Zfloor x).run ∨
      Znearest choice x = (FloatSpec.Core.Raux.Zceil x).run := by
    -- Extract the disjunction from Znearest_DN_or_UP
    have h := (Znearest_DN_or_UP choice x) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure] using h
  -- Also, we have ⌊x⌋ ≤ ⌈x⌉ as integers
  have h_floor_le_ceil :
      (FloatSpec.Core.Raux.Zfloor x).run ≤ (FloatSpec.Core.Raux.Zceil x).run := by
    have h1 : ((FloatSpec.Core.Raux.Zfloor x).run : ℝ) ≤ x := by
      simpa [FloatSpec.Core.Raux.Zfloor] using (Int.floor_le x)
    have h2 : x ≤ ((FloatSpec.Core.Raux.Zceil x).run : ℝ) := by
      simpa [FloatSpec.Core.Raux.Zceil] using (Int.le_ceil x)
    have hreal : ((FloatSpec.Core.Raux.Zfloor x).run : ℝ)
                  ≤ ((FloatSpec.Core.Raux.Zceil x).run : ℝ) :=
      le_trans h1 h2
    exact (by exact_mod_cast hreal)
  -- Finish by cases on Znearest
  have hgoal : Znearest choice x ≤ (FloatSpec.Core.Raux.Zceil x).run := by
    cases hdisj with
    | inl h =>
        -- Znearest = ⌊x⌋
        simpa [h] using h_floor_le_ceil
    | inr h =>
        -- Znearest = ⌈x⌉
        simpa [h] using
          (le_rfl : (FloatSpec.Core.Raux.Zceil x).run ≤ (FloatSpec.Core.Raux.Zceil x).run)
  exact hgoal

/- Additional Znearest lemmas from Coq (placeholders, to be filled iteratively):
   Znearest_le_ceil, Znearest_N_strict, Znearest_half, Znearest_imp, Znearest_opp.
   We add them one-by-one following the pipeline instructions. -/

/-- Check value for Znearest_N_strict: |x - IZR (Znearest x)| -/
noncomputable def Znearest_N_strict_check (choice : Int → Bool) (x : ℝ) : Id ℝ :=
  pure (|x - (((Znearest choice x) : Int) : ℝ)|)

/-- Coq (Generic_fmt.v): Znearest_N_strict

    If `(x - ⌊x⌋) ≠ 1/2` then `|x - IZR (Znearest x)| < 1/2`.
-/
theorem Znearest_N_strict (choice : Int → Bool) (x : ℝ) :
    ⦃⌜x - (((FloatSpec.Core.Raux.Zfloor x).run : Int) : ℝ) ≠ (1/2)⌝⦄
    Znearest_N_strict_check choice x
    ⦃⇓r => ⌜r < (1/2)⌝⦄ := by
  intro _
  unfold Znearest_N_strict_check
  -- Reduce the Hoare triple on Id to a pure goal
  simp [wp, PostCond.noThrow, Id.run, pure]
  -- Notations for floor/ceil
  set f : Int := (FloatSpec.Core.Raux.Zfloor x).run with hf
  set c : Int := (FloatSpec.Core.Raux.Zceil x).run with hc
  -- Basic bounds: (f : ℝ) ≤ x < (f : ℝ) + 1 and x ≤ (c : ℝ)
  have h_floor_le : (f : ℝ) ≤ x := by simpa [hf, FloatSpec.Core.Raux.Zfloor] using (Int.floor_le x)
  have h_lt_floor_add_one : x < (f : ℝ) + 1 := by
    simpa [hf, FloatSpec.Core.Raux.Zfloor] using (Int.lt_floor_add_one x)
  have h_ceil_ge : x ≤ (c : ℝ) := by simpa [hc, FloatSpec.Core.Raux.Zceil] using (Int.le_ceil x)
  -- Translate to nonnegativity of (x - f) and of (c - x)
  have hxf_nonneg : 0 ≤ x - (f : ℝ) := sub_nonneg.mpr h_floor_le
  have hcx_nonneg : 0 ≤ (c : ℝ) - x := sub_nonneg.mpr h_ceil_ge
  -- Exclude the tie: (x - f) ≠ 1/2, so split on < or >
  have hx_ne : x - (f : ℝ) ≠ (1/2) := by
    -- Goal precondition is exactly this after unfolding casts
    simpa [hf] using
      (show x - (((FloatSpec.Core.Raux.Zfloor x).run : Int) : ℝ) ≠ (1/2) from ‹_›)
  -- Bridge lemma for the half constant: for ℝ, 2⁻¹ = 1/2
  have hhalf_id : (2⁻¹ : ℝ) = (1/2) := by
    -- Use zpow_neg_one to turn 2⁻¹ into (2)⁻¹, then 1/2
    simpa [zpow_neg_one, one_div] using (zpow_neg_one (2 : ℝ))
  by_cases hlt : x - (f : ℝ) < (1/2)
  · -- In this case, Rcompare returns -1, hence Znearest = ⌊x⌋
    have hrlt :
        (FloatSpec.Core.Raux.Rcompare (x - (f : ℝ)) (2⁻¹)).run = -1 := by
      -- Evaluate the comparison code directly under the hypothesis in the 2⁻¹ form
      have hxlt2 : x - (f : ℝ) < (2⁻¹) := by simpa [hhalf_id.symm] using hlt
      unfold FloatSpec.Core.Raux.Rcompare
      simp [Id.run, pure, hxlt2]
    have hzn : Znearest choice x = f := by
      -- Evaluate the match explicitly using hrlt to avoid fragile rewrites
      have hmatch :
          (match (FloatSpec.Core.Raux.Rcompare (x - (f : ℝ)) (2⁻¹)).run with
            | -1 => f
            | 0 => if choice f then c else f
            | _ => c) = f := by
        simpa [hrlt]
      unfold Znearest
      -- Replace internal lets by hf, hc and discharge by hmatch
      simpa [hf, hc, FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil] using hmatch
    -- Reduce goal via Znearest = f and use hlt with |x - f| = x - f
    have habs_near : |x - (((Znearest choice x) : Int) : ℝ)| = |x - (f : ℝ)| := by
      simpa [hzn]
    have hxlt : |x - (f : ℝ)| < (1/2) := by
      simpa [abs_of_nonneg hxf_nonneg] using hlt
    -- Convert RHS 1/2 to 2⁻¹ using hhalf_id
    have hxlt' : |x - (f : ℝ)| < (2⁻¹) := by simpa [hhalf_id.symm] using hxlt
    simpa [habs_near] using hxlt'
  · -- Otherwise, since (x - f) ∈ [0,1) and ≠ 1/2, we have 1/2 < x - f
    have hxgt : (2⁻¹) < x - (f : ℝ) := by
      -- From ¬(x - f < 1/2), get (1/2) ≤ (x - f); combined with ≠ yields strict
      have hxge : (2⁻¹) ≤ x - (f : ℝ) := by
        -- rewrite 2⁻¹ as (1/2) to use hlt
        simpa [hhalf_id.symm] using (le_of_not_lt hlt)
      -- turn ≠ into ≠ after rewriting 2⁻¹ ↔ 1/2
      have hx_ne' : x - (f : ℝ) ≠ (2⁻¹) := by simpa [hhalf_id.symm] using hx_ne
      exact lt_of_le_of_ne hxge (Ne.symm hx_ne')
    -- In this case, Rcompare returns 1, hence Znearest = ⌈x⌉
    have hzn : Znearest choice x = c := by
      -- Compute the comparison code: not < and not = forces the Gt branch
      have hnotlt : ¬ (x - (f : ℝ) < (2⁻¹)) := by
        -- rewrite target to 1/2 to use hlt
        simpa [hhalf_id.symm] using hlt
      have hnoteq : ¬ (x - (f : ℝ) = (2⁻¹)) := by
        -- rewrite target to 1/2 to use hx_ne
        simpa [hhalf_id.symm] using hx_ne
      have hrgt : (FloatSpec.Core.Raux.Rcompare (x - (f : ℝ)) (2⁻¹)).run = 1 := by
        unfold FloatSpec.Core.Raux.Rcompare
        simp [Id.run, pure, hnotlt, hnoteq]
      -- Evaluate the match explicitly using hrgt, avoiding extra simp rewrites
      have hmatch :
          (match (FloatSpec.Core.Raux.Rcompare (x - (f : ℝ)) (2⁻¹)).run with
            | -1 => f
            | 0 => if choice f then c else f
            | _ => c) = c := by
        -- With scrutinee = 1, the match selects the default branch
        simpa [hrgt]
      -- Now unfold Znearest and discharge by hmatch
      unfold Znearest
      -- Replace the internal lets by hf, hc but keep the scrutinee shape
      simpa [hf, hc, FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil] using hmatch
    -- Reduce goal via Znearest = c and rewrite |x - c| = c - x
    have habs_near : |x - (((Znearest choice x) : Int) : ℝ)| = |x - (c : ℝ)| := by
      simpa [hzn]
    have habs : |x - (c : ℝ)| = (c : ℝ) - x := by
      have hxle : x ≤ (c : ℝ) := h_ceil_ge
      have : |(c : ℝ) - x| = (c : ℝ) - x := abs_of_nonneg (sub_nonneg.mpr hxle)
      simpa [abs_sub_comm] using this
    -- Use c ≤ f + 1 to upper bound c - x by 1 - (x - f)
    have hceil_le : c ≤ f + 1 := by
      -- From x < f + 1, get x ≤ (f + 1 : ℝ), then apply ceil_le
      have hxle : x ≤ ((f + 1 : Int) : ℝ) := by
        have := le_of_lt h_lt_floor_add_one
        simpa [Int.cast_add, Int.cast_one] using this
      have : Int.ceil x ≤ f + 1 := (Int.ceil_le).mpr (by simpa using hxle)
      simpa [hc, FloatSpec.Core.Raux.Zceil] using this
    have hcx_le : (c : ℝ) - x ≤ (1 : ℝ) - (x - (f : ℝ)) := by
      -- (c : ℝ) ≤ (f : ℝ) + 1 ⇒ (c : ℝ) - x ≤ (f : ℝ) + 1 - x = 1 - (x - f)
      have : (c : ℝ) ≤ (f : ℝ) + 1 := by exact_mod_cast hceil_le
      have := sub_le_sub_right this x
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
    -- And 1 - (x - f) < 1/2, since 1/2 < x - f
    have hone_sub_lt : (1 : ℝ) - (x - (f : ℝ)) < (2⁻¹) := by
      -- Using sub_lt_iff_lt_add: 1 - (x - f) < 2⁻¹ ↔ 1 < (x - f) + 2⁻¹.
      -- From hxgt: 2⁻¹ < x - f, add 2⁻¹ to both sides and simplify (2⁻¹ + 2⁻¹ = 1).
      have : (1 : ℝ) < (2⁻¹) + (x - (f : ℝ)) := by
        have hx' := add_lt_add_right hxgt (2⁻¹)
        -- hx' : (2⁻¹) + (2⁻¹) < (x - (f : ℝ)) + (2⁻¹)
        -- Rewrite (2⁻¹) + (2⁻¹) to 1 via hhalf_id
        have hsum : (2⁻¹ : ℝ) + (2⁻¹) = (1 : ℝ) := by
          simpa [hhalf_id.symm, add_comm, add_left_comm, add_assoc] using (by norm_num : (1/2 : ℝ) + (1/2) = 1)
        simpa [hsum, add_comm, add_left_comm, add_assoc] using hx'
      exact (sub_lt_iff_lt_add).2 this
    -- Chain the bounds
    have : (c : ℝ) - x < (2⁻¹) := lt_of_le_of_lt hcx_le hone_sub_lt
    have : |x - (c : ℝ)| < (2⁻¹) := by simpa [habs] using this
    simpa [habs_near]

/-- Check value for Znearest_half: |x - IZR (Znearest x)| -/
noncomputable def Znearest_half_check (choice : Int → Bool) (x : ℝ) : Id ℝ :=
  Znearest_N_strict_check choice x

/-- Coq (Generic_fmt.v): Znearest_half

    Always `|x - IZR (Znearest x)| ≤ 1/2`.
-/
theorem Znearest_half (choice : Int → Bool) (x : ℝ) :
    ⦃⌜True⌝⦄
    Znearest_half_check choice x
    ⦃⇓r => ⌜r ≤ (1/2)⌝⦄ := by
  intro _
  unfold Znearest_half_check
  -- Reduce to the absolute-distance bound for Znearest
  simp [Znearest_N_strict_check, wp, PostCond.noThrow, Id.run, pure]
  classical
  -- Notations for floor/ceil as integers
  set f : Int := (FloatSpec.Core.Raux.Zfloor x).run with hf
  set c : Int := (FloatSpec.Core.Raux.Zceil x).run with hc
  -- Split on the midpoint case x - ⌊x⌋ = 1/2
  by_cases hmid : x - (f : ℝ) = (1/2)
  · -- At the midpoint, Znearest returns either floor or ceil;
    -- in both cases the distance to x is ≤ 1/2
    -- Basic bounds relating x, floor, and ceil
    have h_floor_le : (f : ℝ) ≤ x := by
      simpa [hf, FloatSpec.Core.Raux.Zfloor] using (Int.floor_le x)
    have h_ceil_ge : x ≤ (c : ℝ) := by
      simpa [hc, FloatSpec.Core.Raux.Zceil] using (Int.le_ceil x)
    have hxf_nonneg : 0 ≤ x - (f : ℝ) := sub_nonneg.mpr h_floor_le
    have hcx_nonneg : 0 ≤ (c : ℝ) - x := sub_nonneg.mpr h_ceil_ge
    -- Distance to floor equals 1/2
    have h_to_floor : |x - (f : ℝ)| = (1/2) := by
      simpa [abs_of_nonneg hxf_nonneg, hmid]
    -- Distance to ceil is at most 1/2
    have h_to_ceil_le : |x - (c : ℝ)| ≤ (1/2) := by
      -- Use that ⌈x⌉ ≤ ⌊x⌋ + 1 when x ≤ ⌊x⌋ + 1
      have hx_le_f1 : x ≤ (f : ℝ) + 1 := by
        -- from x = f + 1/2 (rearranged hmid)
        have hx_eq : x = (f : ℝ) + (1/2) := by
          have := hmid
          linarith
        have : (f : ℝ) + (1/2) ≤ (f : ℝ) + 1 := by
          have hhalf_le_one : (1/2 : ℝ) ≤ 1 := by norm_num
          exact add_le_add_left hhalf_le_one _
        exact le_trans (le_of_eq hx_eq) this
      have hceil_le : c ≤ f + 1 := by
        -- Int.ceil_le: ⌈x⌉ ≤ z ↔ x ≤ z
        have : x ≤ ((f + 1 : Int) : ℝ) := by
          simpa [Int.cast_add, Int.cast_one] using hx_le_f1
        simpa [hc, hf, FloatSpec.Core.Raux.Zceil, FloatSpec.Core.Raux.Zfloor]
          using (Int.ceil_le.mpr this)
      -- Translate to reals and subtract x on both sides
      have hceil_real_le : (c : ℝ) - x ≤ ((f + 1 : Int) : ℝ) - x :=
        sub_le_sub_right (by exact_mod_cast hceil_le) _
      -- Compute the RHS using hmid
      have h_rhs : ((f + 1 : Int) : ℝ) - x = (1/2) := by
        have hx_eq : x = (f : ℝ) + (1/2) := by
          have := hmid; linarith
        calc
          ((f + 1 : Int) : ℝ) - x
              = ((f : ℝ) + 1) - x := by simp [Int.cast_add, Int.cast_one]
          _   = ((f : ℝ) + 1) - ((f : ℝ) + (1/2)) := by simpa [hx_eq]
          _   = (1 : ℝ) - (1/2) := by ring
          _   = (1/2) := by norm_num
      -- Conclude using nonnegativity of c - x
      have h_abs_c : |x - (c : ℝ)| = (c : ℝ) - x := by
        have : |(c : ℝ) - x| = (c : ℝ) - x := abs_of_nonneg hcx_nonneg
        simpa [abs_sub_comm] using this
      have hcx_le_half : (c : ℝ) - x ≤ (1/2) := by
        -- Rewrite the RHS using h_rhs and evaluate
        have : (c : ℝ) - x ≤ ((f + 1 : Int) : ℝ) - x := hceil_real_le
        calc
          (c : ℝ) - x ≤ ((f + 1 : Int) : ℝ) - x := this
          _ = ((f : ℝ) + 1) - x := by simp [Int.cast_add, Int.cast_one]
          _ = ((f : ℝ) + 1) - ((f : ℝ) + (1/2)) := by
                have hx_eq : x = (f : ℝ) + (1/2) := by
                  have := hmid; linarith
                simpa [hx_eq]
          _ = (1/2) := by ring
      simpa [h_abs_c] using hcx_le_half
    -- Znearest is either floor or ceil; finish by cases
    have hdisj :
        Znearest choice x = (FloatSpec.Core.Raux.Zfloor x).run ∨
        Znearest choice x = (FloatSpec.Core.Raux.Zceil x).run := by
      have h := (Znearest_DN_or_UP choice x) True.intro
      simpa [wp, PostCond.noThrow, Id.run, pure] using h
    rcases hdisj with hZ | hZ
    · -- nearest = floor
      simpa [hZ, hf] using (le_of_eq h_to_floor)
    · -- nearest = ceil
      simpa [hZ, hc, abs_sub_comm] using h_to_ceil_le
  · -- Off the midpoint, invoke the strict bound and relax to ≤
    have hstrict := (Znearest_N_strict choice x) (by
      -- Precondition for the strict lemma: x - ⌊x⌋ ≠ 1/2
      simpa [hf] using hmid)
    have hlt : |x - (((Znearest choice x) : Int) : ℝ)| < (1/2) := by
      simpa [Znearest_N_strict_check, wp, PostCond.noThrow, Id.run, pure]
        using hstrict
    -- Convert to the 2⁻¹ form if needed and relax to ≤
    have hlt' : |x - (((Znearest choice x) : Int) : ℝ)| < (2⁻¹ : ℝ) := by
      simpa [zpow_neg_one, one_div] using hlt
    exact le_of_lt hlt'


/-- Check pair for Znearest_imp: returns (Znearest x, n) -/
noncomputable def Znearest_imp_check (choice : Int → Bool) (x : ℝ) (n : Int) : Id (Int × Int) :=
  pure (Znearest choice x, n)

/-- Coq (Generic_fmt.v): Znearest_imp

    If `|x - IZR n| < 1/2` then `Znearest x = n`.
-/
theorem Znearest_imp (choice : Int → Bool) (x : ℝ) (n : Int) :
    ⦃⌜|x - ((n : Int) : ℝ)| < (1/2)⌝⦄
    Znearest_imp_check choice x n
    ⦃⇓p => ⌜p.1 = p.2⌝⦄ := by
  intro _
  unfold Znearest_imp_check
  -- Reduce to a pure equality on Id
  simp [wp, PostCond.noThrow, Id.run, pure]
  classical
  -- From Znearest_half: |x - Znearest x| ≤ 1/2
  have hZ_le : |x - (((Znearest choice x) : Int) : ℝ)| ≤ (1/2) := by
    have h := (Znearest_half choice x) True.intro
    simpa [Znearest_half_check, Znearest_N_strict_check, wp, PostCond.noThrow, Id.run, pure] using h
  -- Triangle inequality to compare the two integers Znearest and n
  have hsum_lt : |x - ((n : Int) : ℝ)| + |x - (((Znearest choice x) : Int) : ℝ)| < 1 := by
    -- Combine as: (|x-n| < 1/2) and (|x-Z| ≤ 1/2) ⇒ sum < 1
    have h1 : |x - ((n : Int) : ℝ)| + |x - (((Znearest choice x) : Int) : ℝ)|
                < (1/2) + |x - (((Znearest choice x) : Int) : ℝ)| :=
      add_lt_add_right (‹|x - ((n : Int) : ℝ)| < (1/2)›) _
    have h2 : (1/2) + |x - (((Znearest choice x) : Int) : ℝ)|
                ≤ (1/2) + (1/2) := add_le_add_left hZ_le _
    have h3 : |x - ((n : Int) : ℝ)| + |x - (((Znearest choice x) : Int) : ℝ)|
                < (1/2) + (1/2) := lt_of_lt_of_le h1 h2
    -- Normalize (2⁻¹) + (2⁻¹) = 1 to match simplification on the RHS
    have htwo' : (2⁻¹ : ℝ) + (2⁻¹) = (1 : ℝ) := by
      simpa [zpow_neg_one, one_div, add_comm, add_left_comm, add_assoc]
        using (by norm_num : (1/2 : ℝ) + (1/2) = 1)
    have : (|x - ((n : Int) : ℝ)| + |x - (((Znearest choice x) : Int) : ℝ)|) < 1 :=
      by
        -- Lean may normalize (1/2) to (2⁻¹); discharge using htwo'
        simpa [htwo', zpow_neg_one, one_div] using h3
    simpa using this
  have hdiff_lt : |(((Znearest choice x) : Int) : ℝ) - ((n : Int) : ℝ)| < 1 := by
    -- Triangle inequality on ((Z) - n) = ((Z) - x) + (x - n)
    have hineq :
        |(((Znearest choice x) : Int) : ℝ) - ((n : Int) : ℝ)|
          ≤ |(((Znearest choice x) : Int) : ℝ) - x| + |x - ((n : Int) : ℝ)| := by
      have := abs_add ( (((Znearest choice x) : Int) : ℝ) - x) (x - ((n : Int) : ℝ))
      -- Rewrite ((Z) - n) as ((Z) - x) + (x - n)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, sub_add_sub_cancel]
        using this
    -- Also rewrite |((Z) - x)| to |x - (Z)|
    have hineq' :
        |(((Znearest choice x) : Int) : ℝ) - ((n : Int) : ℝ)|
          ≤ |x - (((Znearest choice x) : Int) : ℝ)| + |x - ((n : Int) : ℝ)| := by
      simpa [abs_sub_comm, add_comm] using hineq
    exact lt_of_le_of_lt hineq' (by simpa [add_comm] using hsum_lt)
  -- If the absolute value of an integer (as a real) is < 1, the integer is 0
  have : (Znearest choice x) - n = 0 := by
    -- by contradiction using natAbs ≥ 1 on nonzero integers
    by_contra hne
    have hnatpos : 0 < Int.natAbs ((Znearest choice x) - n) := by
      exact Int.natAbs_pos.mpr hne
    have hge1 : (1 : ℝ) ≤ (Int.natAbs ((Znearest choice x) - n) : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hnatpos)
    -- Relate |z| to natAbs z for integers z
    have h_eq_abs : ((Int.natAbs ((Znearest choice x) - n)) : ℝ)
                      = |(((Znearest choice x) - n : Int) : ℝ)| := by
      simpa [Int.cast_natAbs, Int.cast_abs]
    have : (1 : ℝ) ≤ |(((Znearest choice x) - n : Int) : ℝ)| := by simpa [h_eq_abs] using hge1
    -- Relate to the bound on |(Z : ℝ) - (n : ℝ)| using casts
    have hcast : |(((Znearest choice x) - n : Int) : ℝ)|
                  = |(((Znearest choice x) : Int) : ℝ) - ((n : Int) : ℝ)| := by
      simp [sub_eq_add_neg]
    exact (not_lt_of_ge (by simpa [hcast] using this)) hdiff_lt
  -- Conclude equality of integers
  have : (Znearest choice x) = n := sub_eq_zero.mp this
  simpa [this]

/- Section: Structural property of Znearest under negation -/

/-- Coq (Generic_fmt.v): Znearest_opp

    Precise relation between `Znearest` of `-x` and a transformed choice function.
    This follows the Coq statement:
      Znearest choice (-x) = - Znearest (fun t => bnot (choice (-(t+1)))) x.
-/
theorem Znearest_opp (choice : Int → Bool) (x : ℝ) :
    Znearest choice (-x)
      = - Znearest (fun t => ! choice (-(t + 1))) x := by
  sorry

/- Section: Rounding with Znearest (Coq: round_N_*) -/

-- Define the concrete round function used in Generic_fmt: apply the integer
-- rounding on the scaled mantissa, then rescale by the canonical exponent.
noncomputable def roundR (beta : Int) (fexp : Int → Int)
    (rnd : ℝ → Int) (x : ℝ) : ℝ :=
  let sm := (scaled_mantissa beta fexp x).run
  let e  := (cexp beta fexp x).run
  (((rnd sm : Int) : ℝ) * (beta : ℝ) ^ e)

/-- Coq (Generic_fmt.v): round_N_middle

    If x is exactly in the middle between its down- and up-rounded values,
    then rounding to nearest chooses the branch dictated by `choice` at the
    scaled mantissa.
-/
theorem round_N_middle
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (choice : Int → Bool) (x : ℝ)
    (hβ : 1 < beta)
    (hmid : x - roundR beta fexp (fun y => (FloatSpec.Core.Raux.Zfloor y).run) x
                  = roundR beta fexp (fun y => (FloatSpec.Core.Raux.Zceil y).run) x - x) :
    roundR beta fexp (Znearest choice) x
      = (if choice ((FloatSpec.Core.Raux.Zfloor ((scaled_mantissa beta fexp x).run)).run)
         then roundR beta fexp (fun y => (FloatSpec.Core.Raux.Zceil y).run) x
         else roundR beta fexp (fun y => (FloatSpec.Core.Raux.Zfloor y).run) x) := by
  sorry

/- Coq (Generic_fmt.v): round_N_small_pos

   If `β^(ex-1) ≤ x < β^ex` and `ex < fexp ex`, then rounding to nearest
   yields zero. We state it for the concrete `roundR` with `Znearest choice`.
-/
theorem round_N_small_pos
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (choice : Int → Bool) (x : ℝ) (ex : Int)
    (hβ : 1 < beta)
    (hx : (beta : ℝ) ^ (ex - 1) ≤ x ∧ x < (beta : ℝ) ^ ex)
    (hex_lt : fexp ex > ex) :
    roundR beta fexp (Znearest choice) x = 0 := by
  sorry

/- Coq (Generic_fmt.v): round_NA_pt

   Round-to-nearest, ties away from zero, is realized by `ZnearestA`.
   We state it as a pointwise predicate using the concrete `roundR`.
-/
noncomputable def ZnearestA := fun t : Int => decide (0 ≤ t)

theorem round_NA_pt
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (x : ℝ) :
    ∃ f, (generic_format beta fexp f).run ∧
      FloatSpec.Core.Defs.Rnd_NA_pt (fun y => (generic_format beta fexp y).run) x f := by
  sorry

/- Coq (Generic_fmt.v): round_N0_pt

   Round-to-nearest, ties toward zero, is realized by the choice `t < 0`.
-/
noncomputable def Znearest0 := fun t : Int => decide (t < 0)

theorem round_N0_pt
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (x : ℝ) :
    ∃ f, (generic_format beta fexp f).run ∧
      FloatSpec.Core.Defs.Rnd_N0_pt (fun y => (generic_format beta fexp y).run) x f := by
  sorry

/- Coq (Generic_fmt.v): round_N_opp

   Rounding to nearest commutes with negation up to the transformed choice.
-/
theorem round_N_opp
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (choice : Int → Bool) (x : ℝ) :
    roundR beta fexp (Znearest choice) (-x)
      = - roundR beta fexp (Znearest (fun t => ! choice (-(t + 1)))) x := by
  sorry

/- Coq (Generic_fmt.v): round_N0_opp

   For ties-to-zero choice `Znearest0`, rounding commutes with negation.
-/
theorem round_N0_opp
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (x : ℝ) :
    roundR beta fexp (Znearest (fun t : Int => decide (t < 0))) (-x)
      = - roundR beta fexp (Znearest (fun t : Int => decide (t < 0))) x := by
  sorry

/- Coq (Generic_fmt.v): round_N_small

   Signed variant of `round_N_small_pos`.
-/
theorem round_N_small
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (choice : Int → Bool) (x : ℝ) (ex : Int)
    (hβ : 1 < beta)
    (hx : (beta : ℝ) ^ (ex - 1) ≤ abs x ∧ abs x < (beta : ℝ) ^ ex)
    (hex_lt : fexp ex > ex) :
    roundR beta fexp (Znearest choice) x = 0 := by
  -- Split on the sign of x and reduce to the positive case
  sorry

-- (helper lemmas intentionally omitted at this stage)

/-- Coq (Generic_fmt.v): round_NA_opp

    For round-to-nearest-away-from-zero, rounding commutes with negation.
-/
theorem round_NA_opp
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (x : ℝ) :
    roundR beta fexp (Znearest (fun t : Int => decide (0 ≤ t))) (-x)
      = - roundR beta fexp (Znearest (fun t : Int => decide (0 ≤ t))) x := by
  sorry

-- Section: Inclusion between two formats (Coq: generic_inclusion_*)

section Inclusion

variable (beta : Int) (fexp1 fexp2 : Int → Int)
variable [Valid_exp beta fexp1] [Valid_exp beta fexp2]

/-- Coq (Generic_fmt.v): generic_inclusion_mag

    If for all nonzero x we have `fexp2 (mag x) ≤ fexp1 (mag x)`, then
    `generic_format fexp1 x → generic_format fexp2 x`.
-/
theorem generic_inclusion_mag (x : ℝ) :
    1 < beta →
    (x ≠ 0 → fexp2 ((mag beta x).run) ≤ fexp1 ((mag beta x).run)) →
    (generic_format beta fexp1 x).run →
    (generic_format beta fexp2 x).run := by
  intro hβ hle hx_fmt1
  classical
  -- Notation: M := mag beta x
  set M : Int := (mag beta x).run with hM
  -- Expand generic_format for fexp1 to get the explicit reconstruction of x
  have hx_eq : x
      = (((Ztrunc (x * (beta : ℝ) ^ (-(fexp1 M)))).run : Int) : ℝ)
          * (beta : ℝ) ^ (fexp1 M) := by
    simpa [generic_format, scaled_mantissa, cexp, F2R, hM]
      using hx_fmt1
  -- Name the mantissa and exponent from this reconstruction
  set m1 : Int := (Ztrunc (x * (beta : ℝ) ^ (-(fexp1 M)))).run with hm1
  set e1 : Int := fexp1 M with he1
  have hx_eq' : x = (((m1 : Int) : ℝ) * (beta : ℝ) ^ e1) := by
    simpa [m1, e1, hm1, he1] using hx_eq

  -- Bound needed by generic_format_F2R under fexp2
  have hbound' : m1 ≠ 0 →
      (cexp beta fexp2 (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run).run ≤ e1 := by
    intro hm1_ne
    -- From m1 ≠ 0 and β > 1, derive x ≠ 0 via the reconstruction equality
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    have hm1R_ne : ((m1 : Int) : ℝ) ≠ 0 := by exact_mod_cast hm1_ne
    have hpow_ne : (beta : ℝ) ^ e1 ≠ 0 := zpow_ne_zero e1 (ne_of_gt hbposR)
    have hx_ne : x ≠ 0 := by
      intro hx0
      have : ((m1 : ℝ) * (beta : ℝ) ^ e1) = 0 := by simpa [hx0] using congrArg id hx_eq'
      exact (mul_ne_zero hm1R_ne hpow_ne) this
    -- Instantiate the hypothesis on exponents using x ≠ 0
    have hleM : fexp2 M ≤ fexp1 M := by simpa [hM] using hle hx_ne
    -- Compute the canonical exponent on F2R (mk m1 e1) under fexp2
    have hx_F2R : (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run = x := by
      simpa [F2R, m1, e1] using hx_eq'.symm
    have hcexp_run :
        (cexp beta fexp2 (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run).run
          = fexp2 ((mag beta x).run) := by
      simp [cexp, FloatSpec.Core.Raux.mag, hx_F2R]
    -- Align shapes explicitly
    have hcexpEq :
        (cexp beta fexp2 (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run).run
          = fexp2 M := by simpa [hM] using hcexp_run
    -- Make the shape of the F2R argument match Lean's pretty-printed form
    have hcexpEq' :
        (cexp beta fexp2 (F2R (FlocqFloat.mk m1 (fexp1 ((mag beta x).run)) : FlocqFloat beta)).run).run
          = fexp2 M := by simpa [e1] using hcexpEq
    simpa [e1, hM, hcexpEq'] using hleM

  -- Apply the F2R generic-format constructor for fexp2
  have hgf2 :=
    (generic_format_F2R (beta := beta) (fexp := fexp2) (m := m1) (e := e1))
  have hres : (generic_format beta fexp2 (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run).run := by
    have := hgf2 ⟨hβ, hbound'⟩
    simpa [wp, PostCond.noThrow, Id.run, pure] using this
  -- Finally, rewrite (F2R (m1,e1)) back to x using hx_eq'.
  have hx_F2R : (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run = x := by
    simpa [F2R, m1, e1] using hx_eq'.symm
  simpa [hx_F2R] using hres

/-- Coq (Generic_fmt.v):
    Theorem generic_inclusion_lt_ge:
      ∀ e1 e2, (∀ e, e1 < e ≤ e2 → fexp2 e ≤ fexp1 e) →
      ∀ x, bpow e1 ≤ |x| < bpow e2 →
      generic_format fexp1 x → generic_format fexp2 x.

    Lean (spec): Reformulated with explicit zpow and `.run` projections. -/
theorem generic_inclusion_lt_ge (e1 e2 : Int) :
    1 < beta →
    (∀ e : Int, e1 < e ∧ e ≤ e2 → fexp2 e ≤ fexp1 e) →
    ∀ x : ℝ,
      (((beta : ℝ) ^ e1 < |x|) ∧ (|x| < (beta : ℝ) ^ e2)) →
      (generic_format beta fexp1 x).run →
      (generic_format beta fexp2 x).run := by
  intro hβ hle x hxB hx_fmt1
  classical
  -- Notation for the magnitude of x
  set M : Int := (mag beta x).run with hM
  -- Base positivity on ℝ
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  -- From the strict lower bound, x ≠ 0
  have hx_ne : x ≠ 0 := by
    have : 0 < |x| := lt_trans (zpow_pos hbposR e1) hxB.left
    exact (abs_pos.mp this)
  -- Upper bound gives M ≤ e2 via mag_le_abs
  have hM_le_e2 : M ≤ e2 := by
    have h := FloatSpec.Core.Raux.mag_le_abs (beta := beta) (x := x) (e := e2)
    have hrun : (mag beta x).run ≤ e2 := by
      simpa [wp, PostCond.noThrow, Id.run, pure, FloatSpec.Core.Raux.mag]
        using h ⟨hβ, hx_ne, hxB.right⟩
    simpa [hM] using hrun
  -- Lower bound gives e1 < M via mag_ge_bpow at e = e1 + 1
  have he1_lt_M : e1 < M := by
    have htrip := FloatSpec.Core.Raux.mag_ge_bpow (beta := beta) (x := x) (e := e1 + 1)
    have hrun : (e1 + 1) ≤ (mag beta x).run := by
      -- Precondition: 1 < beta ∧ β^(e1) < |x|
      have hret := htrip (by simpa using And.intro hβ hxB.left)
      simpa [wp, PostCond.noThrow, Id.run, pure, FloatSpec.Core.Raux.mag] using hret
    -- (e1 + 1) ≤ M ↔ e1 < M
    exact (Int.add_one_le_iff).1 (by simpa [hM] using hrun)
  -- Assemble the pointwise exponent comparison required by generic_inclusion_mag
  have hpoint : x ≠ 0 → fexp2 ((mag beta x).run) ≤ fexp1 ((mag beta x).run) := by
    intro _
    exact hle M ⟨he1_lt_M, hM_le_e2⟩
  -- Conclude by the previously proved inclusion-by-magnitude lemma
  exact (generic_inclusion_mag (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2) (x := x))
    hβ hpoint hx_fmt1

/-- Coq (Generic_fmt.v):
    Theorem generic_inclusion:
      ∀ e, fexp2 e ≤ fexp1 e → ∀ x,
      bpow (e-1) ≤ |x| ≤ bpow e →
      generic_format fexp1 x → generic_format fexp2 x.
-/
theorem generic_inclusion (e : Int) :
    1 < beta →
    fexp2 e ≤ fexp1 e →
    ∀ x : ℝ,
      (((beta : ℝ) ^ (e - 1) < |x|) ∧ (|x| ≤ (beta : ℝ) ^ e)) →
      (generic_format beta fexp1 x).run →
      (generic_format beta fexp2 x).run := by
  intro hβ hle_e x hx hfmt1
  classical
  -- From the tight bpow bounds with strict lower bound, deduce mag beta x = e
  have hmag_run : (mag beta x).run = e := by
    have h := FloatSpec.Core.Raux.mag_unique (beta := beta) (x := x) (e := e)
    have : 1 < beta ∧ ((beta : ℝ) ^ (e - 1) < |x| ∧ |x| ≤ (beta : ℝ) ^ e) := ⟨hβ, hx⟩
    simpa [wp, PostCond.noThrow, Id.run, pure, FloatSpec.Core.Raux.mag] using (h this)
  -- Pointwise inequality on the canonical exponent at x
  have hpoint : x ≠ 0 → fexp2 ((mag beta x).run) ≤ fexp1 ((mag beta x).run) := by
    intro _; simpa [hmag_run] using hle_e
  -- Conclude by the inclusion-by-magnitude lemma
  exact (generic_inclusion_mag (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2) (x := x))
    hβ hpoint hfmt1

/-- Coq (Generic_fmt.v):
    Theorem generic_inclusion_le_ge:
      ∀ e1 e2, e1 < e2 →
      (∀ e, e1 < e ≤ e2 → fexp2 e ≤ fexp1 e) →
      ∀ x, bpow e1 ≤ |x| ≤ bpow e2 →
      generic_format fexp1 x → generic_format fexp2 x.
-/
theorem generic_inclusion_le_ge (e1 e2 : Int) :
    1 < beta →
    e1 < e2 →
    (∀ e : Int, e1 < e ∧ e ≤ e2 → fexp2 e ≤ fexp1 e) →
    ∀ x : ℝ,
      (((beta : ℝ) ^ e1 < |x|) ∧ (|x| ≤ (beta : ℝ) ^ e2)) →
      (generic_format beta fexp1 x).run →
      (generic_format beta fexp2 x).run := by
  intro hβ he1e2 hle x hx hx_fmt1
  classical
  -- Split on the upper bound: either strict < or equality at the top endpoint
  have hx_upper := hx.right
  cases lt_or_eq_of_le hx_upper with
  | inl hx_top_lt =>
      -- Strict interior: apply the strict-bounds inclusion lemma
      exact
        (generic_inclusion_lt_ge (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
          (e1 := e1) (e2 := e2))
          hβ hle x ⟨hx.left, hx_top_lt⟩ hx_fmt1
  | inr hx_top_eq =>
      -- On the top boundary: reduce to the `generic_inclusion` lemma with e := e2
      -- Pointwise hypothesis at e2 comes from the range assumption
      have hle_e2 : fexp2 e2 ≤ fexp1 e2 := hle e2 ⟨he1e2, le_rfl⟩
      -- Build the tight bounds (β^(e2-1) < |x| ≤ β^e2)
      have hb_gt1R : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
      have hpow_lt : (beta : ℝ) ^ (e2 - 1) < (beta : ℝ) ^ e2 := by
        -- e2 - 1 < e2
        have hstep : (e2 - 1 : Int) < e2 := by
          have hneg : (-1 : Int) < 0 := by decide
          simpa [sub_eq_add_neg] using (add_lt_add_left hneg e2)
        exact zpow_lt_zpow_right₀ hb_gt1R hstep
      have hbounds : ((beta : ℝ) ^ (e2 - 1) < |x|) ∧ (|x| ≤ (beta : ℝ) ^ e2) := by
        constructor
        · simpa [hx_top_eq] using hpow_lt
        · simpa [hx_top_eq]
      -- Conclude via `generic_inclusion` at e2
      exact
        (generic_inclusion (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2) (e := e2))
          hβ hle_e2 x hbounds hx_fmt1

/-- Coq (Generic_fmt.v):
    Theorem generic_inclusion_le:
      ∀ e2, (∀ e, e ≤ e2 → fexp2 e ≤ fexp1 e) →
      ∀ x, |x| ≤ bpow e2 → generic_format fexp1 x → generic_format fexp2 x.
-/
theorem generic_inclusion_le (e2 : Int) :
    1 < beta →
    (∀ e : Int, e ≤ e2 → fexp2 e ≤ fexp1 e) →
    ∀ x : ℝ,
      (|x| ≤ (beta : ℝ) ^ e2) →
      (generic_format beta fexp1 x).run →
      (generic_format beta fexp2 x).run := by
  intro hβ hle_all x hx_le hx_fmt1
  classical
  -- Split on whether the upper bound is strict or attained.
  cases lt_or_eq_of_le hx_le with
  | inl hx_lt =>
      -- Strict upper bound case: build the pointwise inequality at mag x
      have hpoint : x ≠ 0 → fexp2 ((mag beta x).run) ≤ fexp1 ((mag beta x).run) := by
        intro hx_ne
        -- From |x| < β^e2 and x ≠ 0, obtain mag x ≤ e2
        have hmag_le : (mag beta x).run ≤ e2 := by
          have h := FloatSpec.Core.Raux.mag_le_abs (beta := beta) (x := x) (e := e2)
          have hrun : (mag beta x).run ≤ e2 := by
            simpa [wp, PostCond.noThrow, Id.run, pure, FloatSpec.Core.Raux.mag]
              using h ⟨hβ, hx_ne, hx_lt⟩
          simpa using hrun
        exact hle_all _ hmag_le
      -- Conclude via inclusion by magnitude
      exact (generic_inclusion_mag (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2) (x := x))
        hβ hpoint hx_fmt1
  | inr hx_eq =>
      -- Boundary case |x| = β^e2: strengthen to tight bounds at e2
      have hle_e2 : fexp2 e2 ≤ fexp1 e2 := hle_all e2 le_rfl
      -- Strict lower bound β^(e2-1) < β^e2 since β > 1
      have hb_gt1R : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
      have hpow_lt : (beta : ℝ) ^ (e2 - 1) < (beta : ℝ) ^ e2 := by
        have hstep : (e2 - 1 : Int) < e2 := by
          have hneg : (-1 : Int) < 0 := by decide
          simpa [sub_eq_add_neg] using (add_lt_add_left hneg e2)
        exact zpow_lt_zpow_right₀ hb_gt1R hstep
      have hbounds : ((beta : ℝ) ^ (e2 - 1) < |x|) ∧ (|x| ≤ (beta : ℝ) ^ e2) := by
        constructor
        · simpa [hx_eq] using hpow_lt
        · simpa [hx_eq]
      -- Apply the tight-bounds inclusion with e := e2
      exact (generic_inclusion (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2) (e := e2))
        hβ hle_e2 x hbounds hx_fmt1

/-- Coq (Generic_fmt.v):
    Theorem generic_inclusion_ge:
      ∀ e1, (∀ e, e1 < e → fexp2 e ≤ fexp1 e) →
      ∀ x, bpow e1 ≤ |x| → generic_format fexp1 x → generic_format fexp2 x.
-/
theorem generic_inclusion_ge (e1 : Int) :
    1 < beta →
    (∀ e : Int, e1 ≤ e → fexp2 e ≤ fexp1 e) →
    ∀ x : ℝ,
      ((beta : ℝ) ^ e1 ≤ |x|) →
      (generic_format beta fexp1 x).run →
      (generic_format beta fexp2 x).run := by
  intro hβ hle_all x hx_lb hx_fmt1
  classical
  -- Notation for the magnitude of x
  set M : Int := (mag beta x).run with hM
  -- Pointwise exponent comparison needed by `generic_inclusion_mag`
  have hpoint : x ≠ 0 → fexp2 ((mag beta x).run) ≤ fexp1 ((mag beta x).run) := by
    intro hx_ne
    -- Abbreviation for the logarithmic magnitude
    set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
    -- Under x ≠ 0, `(mag beta x).run = ⌈L⌉`
    have hmag_run : (mag beta x).run = Int.ceil L := by
      simp [mag, hx_ne, L]
    -- Base > 1 on ℝ and hence positive; log β > 0
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
    have hlogβ_pos : 0 < Real.log (beta : ℝ) :=
      (Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)).mpr hβR
    -- From (β : ℝ)^e1 ≤ |x|, take logs and divide by log β > 0 to get (e1 : ℝ) ≤ L
    have hbpow_pos : 0 < (beta : ℝ) ^ e1 := zpow_pos hbposR e1
    have hlog_le : Real.log ((beta : ℝ) ^ e1) ≤ Real.log (abs x) :=
      Real.log_le_log hbpow_pos hx_lb
    have hlog_pow : Real.log ((beta : ℝ) ^ e1) = (e1 : ℝ) * Real.log (beta : ℝ) := by
      simpa using Real.log_zpow hbposR e1
    have hL_ge : (e1 : ℝ) ≤ L := by
      have : (e1 : ℝ) * Real.log (beta : ℝ) ≤ Real.log (abs x) := by
        simpa [hlog_pow] using hlog_le
      -- Divide by positive log β
      have := (le_div_iff₀ hlogβ_pos).mpr this
      simpa [L] using this
    -- Ceil bounds: L ≤ ⌈L⌉, hence (e1 : ℝ) ≤ ⌈L⌉; back to integers by coercion
    have h_e1_le_ceilL : e1 ≤ Int.ceil L := by
      have : (e1 : ℝ) ≤ (Int.ceil L : ℝ) := le_trans hL_ge (Int.le_ceil L)
      exact_mod_cast this
    -- Conclude the desired pointwise inequality by instantiating `hle_all` at M
    have h_e1_le_M : e1 ≤ (mag beta x).run := by
      simpa [hmag_run] using h_e1_le_ceilL
    exact (hle_all ((mag beta x).run) h_e1_le_M)
  -- Apply inclusion-by-magnitude
  exact (generic_inclusion_mag (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2) (x := x))
    hβ hpoint hx_fmt1

end Inclusion

end FloatSpec.Core.Generic_fmt
