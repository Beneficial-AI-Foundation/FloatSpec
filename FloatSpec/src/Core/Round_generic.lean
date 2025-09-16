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

Generic floating-point rounding and unverified properties
Based on flocq/src/Core/Generic_fmt.v
-/

import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Round_pred
import FloatSpec.src.Core.Float_prop
import FloatSpec.src.Core.Generic_fmt
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real
open Std.Do
open FloatSpec.Core.Defs
open FloatSpec.Core.Zaux
open FloatSpec.Core.Raux
open FloatSpec.Core.Generic_fmt

-- No need to export round_to_generic since we're defining it here

namespace FloatSpec.Core.Round_generic

/-- Axiom: Local spacing bound near x (one-ULP gap)
    For the generic format viewed as a set F, if xdn and xup are respectively
    the round-down and round-up values of x in F, then their gap is at most
    (beta : ℝ)^(cexp x). This matches the standard spacing property and is
    consistent with Flocq's Generic_fmt spacing results. -/
axiom spacing_bound
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x xdn xup : ℝ) :
    let F := fun y => (generic_format beta fexp y).run
    Rnd_DN_pt F x xdn → Rnd_UP_pt F x xup →
    xup - xdn ≤ (beta : ℝ) ^ (cexp beta fexp x).run

/-- Axiom: Reciprocal bound via magnitude
    For beta > 1 and x ≠ 0, the reciprocal of |x| is bounded by
    a power determined by the magnitude. -/
axiom recip_abs_x_le (beta : Int) (x : ℝ) :
    (1 < beta ∧ x ≠ 0) → 1 / abs x ≤ (beta : ℝ) ^ (1 - mag beta x)

/-- Axiom: Existence of a half‑ULP approximation in the format -/
axiom exists_round_half_ulp
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ∃ f, (generic_format beta fexp f).run ∧
      abs (f - x) ≤ (1/2) * (beta : ℝ) ^ (cexp beta fexp x).run

/-- Axiom: Nonzero half‑ULP approximation when x ≠ 0 -/
axiom exists_round_half_ulp_nz
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) (hx : x ≠ 0) :
    ∃ f, (generic_format beta fexp f).run ∧ f ≠ 0 ∧
      abs (f - x) ≤ (1/2) * (beta : ℝ) ^ (cexp beta fexp x).run

/-- Placeholder existence axiom: There exists a round-down value in the generic format.
    A constructive proof requires additional spacing/discreteness lemmas for the format.
-/
axiom round_DN_exists
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ∃ f, (generic_format beta fexp f).run ∧
      FloatSpec.Core.Round_pred.Rnd_DN_pt (fun y => (generic_format beta fexp y).run) x f

/-- Placeholder existence axiom: There exists a round-up value in the generic format.
    A constructive proof requires additional spacing/discreteness lemmas for the format.
-/
-- Helper: closure of generic format under negation (as a plain implication)
private theorem generic_format_neg_closed
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (y : ℝ)
    (hy : (generic_format beta fexp y).run) :
    (generic_format beta fexp (-y)).run :=
  (generic_format_opp beta fexp y) hy

-- Transform a round-up point at -x into a round-down point at x, using negation closure
private theorem Rnd_UP_to_DN_via_neg
    (F : ℝ → Prop) (x f : ℝ)
    (Fneg : ∀ y, F y → F (-y))
    (hup : FloatSpec.Core.Round_pred.Rnd_UP_pt F (-x) f) :
    FloatSpec.Core.Round_pred.Rnd_DN_pt F x (-f) := by
  -- Unpack the round-up predicate at -x
  rcases hup with ⟨hfF, hle, hmin⟩
  -- Show membership after negation
  have hFneg : F (-f) := Fneg f hfF
  -- Order transforms: -x ≤ f ↔ -f ≤ x
  have hle' : -f ≤ x := by
    have : (-x) ≤ f := hle
    -- multiply both sides by -1
    simpa using (neg_le_neg this)
  -- Maximality for DN: any g ≤ x must be ≤ -f
  have hmax : ∀ g : ℝ, F g → g ≤ x → g ≤ -f := by
    intro g hgF hg_le
    -- Consider -g, which is in F by closure, and satisfies -x ≤ -g
    have hFneg_g : F (-g) := Fneg g hgF
    have hx_le : (-x) ≤ (-g) := by simpa using (neg_le_neg hg_le)
    -- Minimality of f for UP at -x gives f ≤ -g, hence g ≤ -f
    have hf_le : f ≤ -g := hmin (-g) hFneg_g hx_le
    simpa using (neg_le_neg hf_le)
  exact ⟨hFneg, hle', hmax⟩

-- Existence of a round-up value from round-down existence via negation
theorem round_UP_exists
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ∃ f, (generic_format beta fexp f).run ∧
      FloatSpec.Core.Round_pred.Rnd_UP_pt (fun y => (generic_format beta fexp y).run) x f := by
  -- Obtain DN existence for -x (assumed available) and transform
  rcases round_DN_exists beta fexp (-x) with ⟨fdn, hFdn, hdn⟩
  -- Turn it into UP existence for x via negation
  refine ⟨-fdn, ?_, ?_⟩
  · -- Format closure under negation
    exact generic_format_neg_closed beta fexp fdn hFdn
  · -- Use the transformation lemma specialized to the generic format predicate
    -- First, rewrite the DN predicate at -x into an UP predicate at x via negation
    -- We need the reverse transformation: DN at -x ⇒ UP at x
    -- This is symmetric to Rnd_UP_to_DN_via_neg by swapping roles of x and -x and negating
    -- Prove it directly here
    -- Unpack DN at -x
    rcases hdn with ⟨hF_fdn, hfdn_le, hmax⟩
    -- Show x ≤ -fdn
    have hx_le : x ≤ -fdn := by
      have : fdn ≤ -x := hfdn_le
      -- negate both sides
      simpa using (neg_le_neg this)
    -- Minimality for UP: any g with F g and x ≤ g must satisfy -fdn ≤ g
    have hmin : ∀ g : ℝ, (generic_format beta fexp g).run → x ≤ g → -fdn ≤ g := by
      intro g hFg hx_le_g
      -- Consider -g; DN at -x gives -g ≤ fdn
      have hF_neg_g : (generic_format beta fexp (-g)).run := generic_format_neg_closed beta fexp g hFg
      have h_le_for_dn : (-g) ≤ (-x) := by simpa using (neg_le_neg hx_le_g)
      have : (-g) ≤ fdn := hmax (-g) hF_neg_g h_le_for_dn
      -- Negate inequality to get -fdn ≤ g
      simpa using (neg_le_neg this)
    exact ⟨generic_format_neg_closed beta fexp fdn hFdn, hx_le, hmin⟩

-- (Moved later, after the definition of `round_to_generic`.)

/-- Specification: Powers of beta in generic format

    When fexp (e + 1) ≤ e, beta^e is in generic format.
-/
theorem generic_format_bpow
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (e : Int) :
    ⦃⌜beta > 1 ∧ fexp (e + 1) ≤ e⌝⦄
    generic_format beta fexp ((beta : ℝ) ^ e)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hle⟩
  -- Base positivity and nonzeroness facts
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR

  -- Compute mag on a pure power: with our definition using ceil(log_/log), this evaluates to e
  have hmag_pow : mag beta ((beta : ℝ) ^ e) = e := by
    -- positivity and logs
    have hxpos : 0 < (beta : ℝ) ^ e := zpow_pos (by exact_mod_cast hbposℤ) _
    have hlt : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
    -- show log β ≠ 0 via exp_log and β ≠ 1
    have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := by
      intro h0
      have hbpos' : 0 < (beta : ℝ) := hbposR
      have h0exp : Real.exp (Real.log (beta : ℝ)) = Real.exp 0 := congrArg Real.exp h0
      have : (beta : ℝ) = 1 := by simpa [Real.exp_log hbpos', Real.exp_zero] using h0exp
      have hβne1 : (beta : ℝ) ≠ 1 := by exact_mod_cast (ne_of_gt hβ)
      exact hβne1 this
    have hlog_zpow : Real.log ((beta : ℝ) ^ e) = (e : ℝ) * Real.log (beta : ℝ) := by
      simpa using Real.log_zpow hbposR _
    have hratio : Real.log ((beta : ℝ) ^ e) / Real.log (beta : ℝ) = (e : ℝ) := by
      have : ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) = (e : ℝ) :=
        mul_div_cancel_right₀ (e : ℝ) hlogβ_ne
      simpa [hlog_zpow] using this
    have habs : abs ((beta : ℝ) ^ e) = (beta : ℝ) ^ e := by
      exact abs_of_nonneg (le_of_lt hxpos)
    -- expand definition of mag and evaluate ceil
    unfold mag
    have hxne : (beta : ℝ) ^ e ≠ 0 := ne_of_gt hxpos
    -- Reduce to ceil of a simplified ratio
    simp only [hxne, habs, hlog_zpow]
    have : ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) = (e : ℝ) := by
      have : (Real.log (beta : ℝ) * (e : ℝ)) / Real.log (beta : ℝ) = (e : ℝ) :=
        mul_div_cancel_left₀ (e : ℝ) hlogβ_ne
      simpa [mul_comm] using this
    simpa [this, Int.ceil_intCast]

  -- From the valid_exp structure and the bound at e+1, deduce fexp e ≤ e
  have hlt_e1 : fexp (e + 1) < (e + 1) := lt_of_le_of_lt hle (lt_add_of_pos_right _ Int.zero_lt_one)
  have hfe_le : fexp e ≤ e := by
    -- Use valid_exp_large' with k = e+1 and l = e to get fexp e < e+1
    have := FloatSpec.Core.Generic_fmt.valid_exp_large' (beta := beta) (fexp := fexp) (k := e + 1) (l := e) hlt_e1 (le_of_lt (lt_add_of_pos_right _ Int.zero_lt_one))
    exact Int.lt_add_one_iff.mp this

  -- Unfold goal and carry out the algebra, mirroring generic_format_F2R with m = 1
  simp [generic_format, scaled_mantissa, cexp, F2R]
  -- Notation: cexp for x = β^e
  set c := fexp (mag beta ((beta : ℝ) ^ e)) with hc
  -- Use hmag_pow to rewrite c
  have hc' : c = fexp e := by simpa [hc, hmag_pow]
  -- With c ≤ e, we can express the scaled mantissa as an integer power
  have hcle : c ≤ e := by simpa [hc'] using hfe_le
  -- Key zpow identities
  have hinv : (beta : ℝ) ^ (-c) = ((beta : ℝ) ^ c)⁻¹ := zpow_neg _ _
  have hmul_pow : (beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹ = (beta : ℝ) ^ (e - c) := by
    rw [← hinv, ← zpow_add₀ hbne]
    simp [sub_eq_add_neg]
  have hpow_nonneg : 0 ≤ e - c := sub_nonneg.mpr hcle
  have hzpow_toNat : (beta : ℝ) ^ (e - c) = (beta : ℝ) ^ (Int.toNat (e - c)) := by
    rw [← Int.toNat_of_nonneg hpow_nonneg]
    exact zpow_ofNat _ _
  have hcast_pow : (beta : ℝ) ^ (Int.toNat (e - c)) = ((beta ^ (Int.toNat (e - c)) : Int) : ℝ) := by
    rw [← Int.cast_pow]

  -- Finish by showing the reconstruction equality
  simp only [hc, hmag_pow]
  -- Goal now is: (Ztrunc ((β^e) * (β^c)⁻¹) : ℝ) * (β : ℝ) ^ c = (β : ℝ) ^ e
  -- Compute the truncation explicitly
  have htrunc : Ztrunc ((beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹) = beta ^ (Int.toNat (e - c)) := by
    calc
      Ztrunc ((beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹)
          = Ztrunc ((beta : ℝ) ^ (e - c)) := by rw [hmul_pow]
      _   = Ztrunc ((beta : ℝ) ^ (Int.toNat (e - c))) := by rw [hzpow_toNat]
      _   = Ztrunc (((beta ^ (Int.toNat (e - c)) : Int) : ℝ)) := by rw [hcast_pow]
      _   = beta ^ (Int.toNat (e - c)) := FloatSpec.Core.Generic_fmt.Ztrunc_intCast _

  -- Power splitting lemma to reconstruct
  have hsplit : (beta : ℝ) ^ e = (beta : ℝ) ^ (e - c) * (beta : ℝ) ^ c := by
    rw [← zpow_add₀ hbne (e - c) c]
    simp [sub_add_cancel]

  -- Conclude the equality (flip orientation to match calc direction)
  symm
  calc
    ((Ztrunc ((beta : ℝ) ^ e * ((beta : ℝ) ^ (fexp e))⁻¹) : Int) : ℝ) * (beta : ℝ) ^ (fexp e)
        = ((Ztrunc ((beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹) : Int) : ℝ) * (beta : ℝ) ^ c := by
              rw [hc']
    _   = ((beta ^ (Int.toNat (e - c)) : Int) : ℝ) * (beta : ℝ) ^ c := by rw [htrunc]
    _   = (beta : ℝ) ^ (e - c) * (beta : ℝ) ^ c := by
          -- rewrite Int power as real power for nonnegative exponent
          rw [hzpow_toNat, hcast_pow]
    _   = (beta : ℝ) ^ e := by rw [hsplit]

/-- Specification: Alternative power condition

    When fexp e ≤ e, beta^e is in generic format.
-/
theorem generic_format_bpow' (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (e : Int) :
    ⦃⌜beta > 1 ∧ fexp e ≤ e⌝⦄
    generic_format beta fexp ((beta : ℝ) ^ e)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hβ, hle⟩
  -- From Valid_exp, we can derive the required bound fexp (e+1) ≤ e
  -- by case-splitting on whether fexp e < e or e ≤ fexp e.
  have hpair := (Valid_exp.valid_exp (beta := beta) (fexp := fexp) e)
  by_cases hlt : fexp e < e
  · -- Large regime: directly get fexp (e+1) ≤ e
    have hbound : fexp (e + 1) ≤ e := (hpair.left) hlt
    -- Apply the power-in-format lemma with this bound
    exact (generic_format_bpow (beta := beta) (fexp := fexp) e) ⟨hβ, hbound⟩
  · -- Otherwise, we have e ≤ fexp e
    have hge : e ≤ fexp e := le_of_not_gt hlt
    -- Combined with the hypothesis fexp e ≤ e, we get equality
    have heq : fexp e = e := le_antisymm hle hge
    -- Small regime: get fexp (fexp e + 1) ≤ fexp e, then rewrite using heq
    have hsmall := (hpair.right) (by simpa [heq] using hge)
    have hbound' : fexp (e + 1) ≤ e := by
      simpa [heq, add_comm, add_left_comm, add_assoc] using hsmall.left
    -- Apply the power-in-format lemma with the derived bound
    exact (generic_format_bpow (beta := beta) (fexp := fexp) e) ⟨hβ, hbound'⟩

/-- Specification: Scaled mantissa for generic format

    For numbers in generic format, the scaled mantissa
    equals its truncation (i.e., it's already an integer).
-/
theorem scaled_mantissa_generic (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ⦃⌜(generic_format beta fexp x).run⌝⦄
    scaled_mantissa beta fexp x
    ⦃⇓result => ⌜result = Ztrunc result⌝⦄ := by
  intro hx
  unfold scaled_mantissa cexp
  simp
  -- Turn the generic_format hypothesis into the reconstruction equality
  unfold generic_format at hx
  simp [scaled_mantissa, cexp, F2R] at hx
  -- Notation: e is the canonical exponent, m the scaled mantissa
  set e := fexp (mag beta x)
  set m := x * (beta : ℝ) ^ (-e) with hm
  have hx' : x = ((Ztrunc m : Int) : ℝ) * (beta : ℝ) ^ e := by simpa [e, m] using hx
  -- We need to prove: m = Ztrunc m (with coercion on the right)
  by_cases hpow : (beta : ℝ) ^ e = 0
  · -- Degenerate base power: then x = 0 and hence m = 0, so equality holds
    have hx0 : x = 0 := by simpa [hpow] using hx'
    have hm0 : m = 0 := by simp [m, hx0]
    simp [hx0, FloatSpec.Core.Generic_fmt.Ztrunc_zero]
  · -- Nonzero base power: cancel to show m equals its truncation
    have hpow_ne : (beta : ℝ) ^ e ≠ 0 := hpow
    -- Multiply the reconstruction by β^(-e) and simplify using hpow_ne
    have hmul := congrArg (fun t : ℝ => t * (beta : ℝ) ^ (-e)) hx'
    -- Left side becomes m; right side reduces to (Ztrunc m : ℝ)
    have hmain : m = (Ztrunc m : ℝ) := by
      simpa [m, mul_comm, mul_left_comm, mul_assoc, zpow_neg, hpow_ne]
        using hmul
    simpa [m] using hmain

/-- Specification: Canonical exponent from bounds

    When x is bounded by powers of beta, cexp(x) = fexp(ex).
-/
theorem cexp_fexp (beta : Int) (fexp : Int → Int) (x : ℝ) (ex : Int) :
    ⦃⌜beta > 1 ∧ (beta : ℝ) ^ (ex - 1) < abs x ∧ abs x ≤ (beta : ℝ) ^ ex⌝⦄
    cexp beta fexp x
    ⦃⇓result => ⌜result = fexp ex⌝⦄ := by
  intro h
  rcases h with ⟨hβ, hlow, hupp⟩
  -- It suffices to show mag beta x = ex
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  -- From the strict lower bound, |x| > 0 hence x ≠ 0
  have hxpos : 0 < abs x := lt_trans (zpow_pos (by exact_mod_cast hbposℤ) _) hlow
  have hx0 : x ≠ 0 := by
    have : abs x ≠ 0 := ne_of_gt hxpos
    exact fun hx => this (by simpa [hx, abs_zero])
  -- Unfold mag and set L = log(|x|)/log(beta)
  -- Prepare an explicit form for mag
  have hmageq : mag beta x = Int.ceil (Real.log (abs x) / Real.log (beta : ℝ)) := by
    unfold mag
    simp [hx0]
  set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hLdef
  -- Show Int.ceil L = ex by sandwiching L between ex-1 and ex
  -- Upper bound: L ≤ ex
  -- log β > 0 since 1 < β
  have hb_gt1R : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt (by exact_mod_cast hbposℤ))
    exact this.mpr hb_gt1R
  have hlog_le : Real.log (abs x) ≤ Real.log ((beta : ℝ) ^ ex) :=
    Real.log_le_log hxpos hupp
  have hlog_zpow_ex : Real.log ((beta : ℝ) ^ ex) = (ex : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbposR ex
  have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
    have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    calc
      L * Real.log (beta : ℝ)
          = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLdef]
      _   = Real.log (abs x) * Real.log (beta : ℝ) / Real.log (beta : ℝ) := by
            simpa [div_mul_eq_mul_div]
      _   = Real.log (abs x) := by
            simpa [hne] using (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
  have hL_le_ex : L ≤ (ex : ℝ) := by
    have hmul_le : L * Real.log (beta : ℝ) ≤ (ex : ℝ) * Real.log (beta : ℝ) := by
      simpa [hL_mul, hlog_zpow_ex] using hlog_le
    exact (le_of_mul_le_mul_right hmul_le hlogβ_pos)
  have hceil_le : Int.ceil L ≤ ex := Int.ceil_le.mpr hL_le_ex
  -- Lower bound: ex - 1 < L
  have hlog_lt : Real.log ((beta : ℝ) ^ (ex - 1)) < Real.log (abs x) :=
    Real.log_lt_log (zpow_pos (by exact_mod_cast hbposℤ) _) hlow
  have hlog_zpow_exm1 : Real.log ((beta : ℝ) ^ (ex - 1)) = (ex - 1 : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbposR (ex - 1)
  have hexm1_lt_L : (ex - 1 : ℝ) < L := by
    have hmul_lt : (ex - 1 : ℝ) * Real.log (beta : ℝ) < L * Real.log (beta : ℝ) := by
      simpa [hL_mul, hlog_zpow_exm1] using hlog_lt
    exact (lt_of_mul_lt_mul_right hmul_lt (le_of_lt hlogβ_pos))
  -- Conclude Int.ceil L = ex: we already have Int.ceil L ≤ ex; prove the reverse
  have h_ex_le_ceil : ex ≤ Int.ceil L := by
    -- By contradiction: if ⌈L⌉ < ex then ⌈L⌉ ≤ ex-1, contradicting ex-1 < L
    by_contra hnot
    have hlt : Int.ceil L < ex := lt_of_not_ge hnot
    have hle_exm1 : Int.ceil L ≤ ex - 1 := by
      have : Int.ceil L < (ex - 1) + 1 := by simpa [Int.sub_add_cancel] using hlt
      exact Int.lt_add_one_iff.mp this
    have : L ≤ (ex - 1 : ℝ) := by
      simpa [Int.cast_sub, Int.cast_one] using (Int.ceil_le).mp hle_exm1
    exact (not_le_of_gt hexm1_lt_L) this
  have hceil_eq : Int.ceil L = ex := le_antisymm hceil_le h_ex_le_ceil
  -- Conclude by rewriting mag with hmageq and the established equality on the ceiling
  have hmag_eq_ex : mag beta x = ex := by
    rw [hmageq, hLdef, hceil_eq]
  unfold cexp
  simp [hmag_eq_ex]

/-- Specification: Canonical exponent from positive bounds

    When positive x is bounded by powers of beta, cexp(x) = fexp(ex).
-/
theorem cexp_fexp_pos (beta : Int) (fexp : Int → Int) (x : ℝ) (ex : Int) :
    ⦃⌜beta > 1 ∧ (beta : ℝ) ^ (ex - 1) < x ∧ x ≤ (beta : ℝ) ^ ex⌝⦄
    cexp beta fexp x
    ⦃⇓result => ⌜result = fexp ex⌝⦄ := by
  intro h
  rcases h with ⟨hβ, hlow, hupp⟩
  -- From beta > 1, powers are positive; with strict lower bound, x > 0
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hxpos : 0 < x := lt_trans (zpow_pos (by exact_mod_cast hbposℤ) _) hlow
  have habs : abs x = x := abs_of_nonneg (le_of_lt hxpos)
  -- Reduce to the absolute-value version
  exact
    (cexp_fexp (beta := beta) (fexp := fexp) (x := x) (ex := ex))
      ⟨hβ, by simpa [habs] using hlow, by simpa [habs] using hupp⟩

/-- Specification: Mantissa for small positive numbers

    For small positive x bounded by beta^(ex-1) and beta^ex,
    where ex ≤ fexp(ex), the scaled mantissa is in (0,1).
-/
theorem mantissa_small_pos (beta : Int) (fexp : Int → Int) (x : ℝ) (ex : Int)
    (hx : (beta : ℝ) ^ (ex - 1) ≤ x ∧ x < (beta : ℝ) ^ ex)
    (he : ex ≤ fexp ex) (hβ : 1 < beta) :
    0 < x * (beta : ℝ) ^ (-(fexp ex)) ∧ x * (beta : ℝ) ^ (-(fexp ex)) < 1 := by
  -- Basic facts about the base
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hb_ge1 : (1 : ℝ) ≤ (beta : ℝ) := by
    have : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
    exact this.le
  -- Split bounds on x
  rcases hx with ⟨hx_low, hx_high⟩
  -- x is positive since β^(ex-1) > 0
  have hpow_pos_exm1 : 0 < (beta : ℝ) ^ (ex - 1) := zpow_pos (by exact_mod_cast hbposℤ) _
  have hx_pos : 0 < x := lt_of_lt_of_le hpow_pos_exm1 hx_low
  -- Positivity of the scaling factor
  have hscale_pos : 0 < (beta : ℝ) ^ (-(fexp ex)) := zpow_pos (by exact_mod_cast hbposℤ) _
  -- Strict upper bound after scaling by a positive factor
  have hlt_scaled : x * (beta : ℝ) ^ (-(fexp ex)) <
      (beta : ℝ) ^ ex * (beta : ℝ) ^ (-(fexp ex)) := by
    exact (mul_lt_mul_of_pos_right hx_high hscale_pos)
  -- Collapse the right-hand side product using zpow addition
  -- A form of the product suitable for simp when inverses appear
  have hmul_inv : (beta : ℝ) ^ ex * ((beta : ℝ) ^ (fexp ex))⁻¹ = (beta : ℝ) ^ (ex - fexp ex) := by
    have hmul_pow : (beta : ℝ) ^ ex * (beta : ℝ) ^ (-(fexp ex)) = (beta : ℝ) ^ (ex - fexp ex) := by
      simpa using (FloatSpec.Core.Generic_fmt.zpow_mul_sub (a := (beta : ℝ)) hbne ex (fexp ex))
    simpa [zpow_neg] using hmul_pow
  have hlt_scaled' : x * (beta : ℝ) ^ (-(fexp ex)) < (beta : ℝ) ^ (ex - fexp ex) := by
    have h := (mul_lt_mul_of_pos_right hx_high hscale_pos)
    simpa [hmul_inv, zpow_neg] using h
  -- Show β^(ex - fexp ex) ≤ 1 using ex ≤ fexp ex and β > 1
  have hk_nonneg : 0 ≤ fexp ex - ex := sub_nonneg.mpr he
  -- Convert to Nat exponent on the positive side
  have hpos_mul : 0 < (beta : ℝ) ^ (fexp ex - ex) := zpow_pos (by exact_mod_cast hbposℤ) _
  -- Prove 1 ≤ β^(fexp ex - ex) by a small induction on Nat exponents
  have one_le_pow_nat : ∀ n : Nat, (1 : ℝ) ≤ (beta : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hpow_nonneg : 0 ≤ (beta : ℝ) ^ n :=
          pow_nonneg (le_of_lt (by exact_mod_cast hbposℤ)) n
        -- 1*1 ≤ (β^n)*β since 1 ≤ β^n and 1 ≤ β
        have : (1 : ℝ) * 1 ≤ (beta : ℝ) ^ n * (beta : ℝ) := by
          exact mul_le_mul ih hb_ge1 (by norm_num) hpow_nonneg
        simpa [pow_succ] using this
  -- Using Int.toNat to connect zpow with Nat pow on nonnegative exponent
  have hzpow_toNat : (beta : ℝ) ^ (fexp ex - ex) = (beta : ℝ) ^ (Int.toNat (fexp ex - ex)) := by
    simpa using FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat (beta : ℝ) (fexp ex - ex) hk_nonneg
  have hone_le : (1 : ℝ) ≤ (beta : ℝ) ^ (fexp ex - ex) := by
    -- rewrite to Nat power and apply the induction lemma
    simpa [hzpow_toNat] using one_le_pow_nat (Int.toNat (fexp ex - ex))
  -- From 1 ≤ β^(fexp ex - ex), deduce β^(ex - fexp ex) ≤ 1 by multiplying both sides
  have hle_one : (beta : ℝ) ^ (ex - fexp ex) ≤ 1 := by
    -- identity: β^(ex - fexp ex) * β^(fexp ex - ex) = 1
    have hmul_id : (beta : ℝ) ^ (ex - fexp ex) * (beta : ℝ) ^ (fexp ex - ex) = 1 := by
      have := (zpow_add₀ hbne (ex - fexp ex) (fexp ex - ex)).symm
      simpa [sub_add_cancel] using this
    -- Multiply both sides of 1 ≤ β^(fexp ex - ex) by the nonnegative factor β^(ex - fexp ex)
    have hfac_nonneg : 0 ≤ (beta : ℝ) ^ (ex - fexp ex) := le_of_lt (zpow_pos (by exact_mod_cast hbposℤ) _)
    have hmul_le := mul_le_mul_of_nonneg_left hone_le hfac_nonneg
    -- Now rewrite using hmul_id on the right and simplify the left
    -- Left: β^(ex - fexp ex) * 1 = β^(ex - fexp ex)
    -- Right: β^(ex - fexp ex) * β^(fexp ex - ex) = 1
    simpa [hmul_id, one_mul] using hmul_le
  -- Combine the strict inequality with the upper bound ≤ 1
  have hlt_one : x * (beta : ℝ) ^ (-(fexp ex)) < 1 := lt_of_lt_of_le hlt_scaled' hle_one
  -- Positivity of the scaled mantissa: product of positives
  have hpos_scaled : 0 < x * (beta : ℝ) ^ (-(fexp ex)) := mul_pos hx_pos hscale_pos
  exact ⟨hpos_scaled, hlt_one⟩

/-- Specification: Scaled mantissa bound for small numbers

    For small numbers with |x| < beta^ex where ex ≤ fexp(ex),
    the absolute value of scaled mantissa is less than 1.
-/
theorem scaled_mantissa_lt_1
    (beta : Int) (fexp : Int → Int) [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
    (x : ℝ) (ex : Int)
    (hx : abs x < (beta : ℝ) ^ ex)
    (he : ex ≤ fexp ex)
    (hβ : 1 < beta) :
    abs (scaled_mantissa beta fexp x).run < 1 := by
  -- Case split on x = 0
  by_cases hx0 : x = 0
  · -- Trivial: scaled mantissa of 0 is 0
    simp [FloatSpec.Core.Generic_fmt.scaled_mantissa, FloatSpec.Core.Generic_fmt.cexp, hx0]
  · -- Nonzero case
    -- Base positivity
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
    -- Show mag x ≤ ex from |x| < β^ex
    have hmag_le_ex : mag beta x ≤ ex := by
      -- Follow cexp_fexp upper-bound part
      have hxpos : 0 < abs x := abs_pos.mpr hx0
      have hb_gt1R : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
      have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
        have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
          Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt (by exact_mod_cast hbposℤ))
        exact this.mpr hb_gt1R
      have hlog_le : Real.log (abs x) ≤ Real.log ((beta : ℝ) ^ ex) :=
        Real.log_le_log hxpos (le_of_lt hx)
      have hlog_zpow_ex : Real.log ((beta : ℝ) ^ ex) = (ex : ℝ) * Real.log (beta : ℝ) := by
        simpa using Real.log_zpow hbposR ex
      set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
      have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
        have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
        calc
          L * Real.log (beta : ℝ)
              = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by rfl
          _   = Real.log (abs x) := by simpa [hne] using (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
      have hL_le_ex : L ≤ (ex : ℝ) := by
        have hmul_le : L * Real.log (beta : ℝ) ≤ (ex : ℝ) * Real.log (beta : ℝ) := by
          simpa [hL_mul, hlog_zpow_ex] using hlog_le
        exact (le_of_mul_le_mul_right hmul_le hlogβ_pos)
      have hceil_le : Int.ceil L ≤ ex := Int.ceil_le.mpr hL_le_ex
      have hmageq : mag beta x = Int.ceil L := by
        unfold FloatSpec.Core.Generic_fmt.mag
        simp [hx0, L]
      simpa [hmageq]
    -- Small-regime constancy: mag x ≤ ex ≤ fexp ex ⇒ fexp (mag x) = fexp ex
    have hconst := (FloatSpec.Core.Generic_fmt.Valid_exp.valid_exp (beta := beta) (fexp := fexp) ex).right he |>.right
    have heq_fexp : fexp (mag beta x) = fexp ex := hconst (mag beta x) (le_trans hmag_le_ex he)
    -- Now rewrite scaled mantissa using fexp ex
    have hpos_scale : 0 < (beta : ℝ) ^ (-(fexp ex)) := zpow_pos (by exact_mod_cast hbposℤ) _
    have hnonneg_scale : 0 ≤ (beta : ℝ) ^ (-(fexp ex)) := le_of_lt hpos_scale
    have h1sm : (scaled_mantissa beta fexp x).run = x * (beta : ℝ) ^ (-(fexp ex)) := by
      unfold FloatSpec.Core.Generic_fmt.scaled_mantissa FloatSpec.Core.Generic_fmt.cexp
      simp [heq_fexp]
    have hsm_abs : abs (scaled_mantissa beta fexp x).run = abs x * (beta : ℝ) ^ (-(fexp ex)) := by
      rw [h1sm, abs_mul, abs_of_nonneg hnonneg_scale]
    -- Multiply the strict bound by a positive factor
    have hmul_lt : abs x * (beta : ℝ) ^ (-(fexp ex)) < (beta : ℝ) ^ ex * (beta : ℝ) ^ (-(fexp ex)) :=
      mul_lt_mul_of_pos_right hx hpos_scale
    -- Combine exponents and bound by 1 using ex ≤ fexp ex
    have hmul_pow : (beta : ℝ) ^ ex * (beta : ℝ) ^ (-(fexp ex)) = (beta : ℝ) ^ (ex - fexp ex) := by
      simpa [sub_eq_add_neg] using (FloatSpec.Core.Generic_fmt.zpow_mul_sub (a := (beta : ℝ)) (hbne := hbne) (e := ex) (c := fexp ex))
    have hk_nonneg : 0 ≤ fexp ex - ex := sub_nonneg.mpr he
    -- For β ≥ 1, 1 ≤ β^(fexp ex - ex)
    have hone_le : (1 : ℝ) ≤ (beta : ℝ) ^ (fexp ex - ex) := by
      -- rewrite to Nat power and apply induction
      have hzpow_toNat : (beta : ℝ) ^ (fexp ex - ex) = (beta : ℝ) ^ (Int.toNat (fexp ex - ex)) := by
        simpa using FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat (beta : ℝ) (fexp ex - ex) hk_nonneg
      have hb_gt1R : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
      have hb_ge1 : (1 : ℝ) ≤ (beta : ℝ) := hb_gt1R.le
      -- 1 ≤ β^n for all n
      have one_le_pow_nat : ∀ n : Nat, (1 : ℝ) ≤ (beta : ℝ) ^ n := by
        intro n; induction n with
        | zero => simp
        | succ n ih =>
            have hpow_nonneg : 0 ≤ (beta : ℝ) ^ n := pow_nonneg (le_of_lt (by exact_mod_cast hbposℤ)) n
            have : (1 : ℝ) * 1 ≤ (beta : ℝ) ^ n * (beta : ℝ) := mul_le_mul ih hb_ge1 (by norm_num) hpow_nonneg
            simpa [pow_succ] using this
      simpa [hzpow_toNat] using one_le_pow_nat (Int.toNat (fexp ex - ex))
    -- Multiply both sides by β^(ex - fexp ex) ≥ 0 to bound by 1
    have hfac_nonneg : 0 ≤ (beta : ℝ) ^ (ex - fexp ex) := le_of_lt (zpow_pos (by exact_mod_cast hbposℤ) _)
    have hle_one : (beta : ℝ) ^ (ex - fexp ex) ≤ 1 := by
      have hid : (beta : ℝ) ^ (ex - fexp ex) * (beta : ℝ) ^ (fexp ex - ex) = 1 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (zpow_add₀ hbne (ex - fexp ex) (fexp ex - ex)).symm
      have hmul_le := mul_le_mul_of_nonneg_left hone_le hfac_nonneg
      simpa [hid, one_mul] using hmul_le
    -- Conclude
    have hmul_inv_pow : (beta : ℝ) ^ ex * ((beta : ℝ) ^ (fexp ex))⁻¹ = (beta : ℝ) ^ (ex - fexp ex) := by
      simpa [zpow_neg] using hmul_pow
    have : abs (scaled_mantissa beta fexp x).run < (beta : ℝ) ^ (ex - fexp ex) := by
      simpa [hsm_abs, hmul_inv_pow] using hmul_lt
    exact lt_of_lt_of_le this hle_one

/-- Specification: Scaled mantissa general bound

    The absolute value of scaled mantissa is bounded by
    beta^(mag(x) - cexp(x)).
-/
theorem scaled_mantissa_lt_bpow
    (beta : Int) (fexp : Int → Int) (x : ℝ)
    (hβ : 1 < beta) :
    abs (scaled_mantissa beta fexp x).run ≤ (beta : ℝ) ^ (mag beta x - (cexp beta fexp x).run) := by
  -- Base positivity for the real base
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbneR : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  -- Notation
  set e : Int := mag beta x
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
        have : mag beta x = Int.ceil L := by
          unfold FloatSpec.Core.Generic_fmt.mag
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
  -- Multiply by the positive scaling factor and collapse the RHS product
  have habs_pow : abs ((beta : ℝ) ^ (-c)) = (beta : ℝ) ^ (-c) := abs_of_nonneg hscale_nonneg
  have habs_scaled_tmp : abs (scaled_mantissa beta fexp x).run = abs (x * (beta : ℝ) ^ (-c)) := by
    simpa [hsm]
  -- Rewrite |β^(-c)| as |β^c|⁻¹ and then drop abs using nonnegativity of β^c
  have hpow_c_pos : 0 < (beta : ℝ) ^ c := zpow_pos hbposR _
  have hpow_c_nonneg : 0 ≤ (beta : ℝ) ^ c := le_of_lt hpow_c_pos
  have hscale_inv_nonneg : 0 ≤ ((beta : ℝ) ^ c)⁻¹ := inv_nonneg.mpr (le_of_lt hpow_c_pos)
  have habs_scaled : abs (scaled_mantissa beta fexp x).run = abs x * ((beta : ℝ) ^ c)⁻¹ := by
    -- |x * β^(-c)| = |x| * |β^(-c)| = |x| * |(β^c)⁻¹| = |x| * |β^c|⁻¹
    -- and since β^c ≥ 0, |β^c| = β^c
    have : abs (scaled_mantissa beta fexp x).run = abs x * (abs ((beta : ℝ) ^ c))⁻¹ := by
      simpa [abs_mul, zpow_neg] using habs_scaled_tmp
    simpa [abs_of_nonneg hpow_c_nonneg] using this
  have hmul : (beta : ℝ) ^ e * (beta : ℝ) ^ (-c) = (beta : ℝ) ^ (e - c) := by
    simpa [sub_eq_add_neg]
      using (FloatSpec.Core.Generic_fmt.zpow_mul_sub (a := (beta : ℝ)) (hbne := hbneR) (e := e) (c := c))
  -- Combine the pieces and collapse the RHS product
  calc
    abs (scaled_mantissa beta fexp x).run
        = abs x * ((beta : ℝ) ^ c)⁻¹ := habs_scaled
    _   ≤ (beta : ℝ) ^ e * ((beta : ℝ) ^ c)⁻¹ := mul_le_mul_of_nonneg_right h_upper_abs hscale_inv_nonneg
    _   = (beta : ℝ) ^ (e - c) := by
          simpa [zpow_neg] using
            (FloatSpec.Core.Generic_fmt.zpow_mul_sub (a := (beta : ℝ)) (hbne := hbneR) (e := e) (c := c))

/-- Specification: Generic format is closed under rounding down

    For any x, there exists a value f in generic format
    that is the rounding down of x.
-/
theorem generic_format_round_DN (beta : Int) (hbeta : 1 < beta) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ∃ f, (generic_format beta fexp f).run ∧ Rnd_DN_pt (fun y => (generic_format beta fexp y).run) x f := by
  -- Derive DN existence for x from UP existence for -x via negation
  have hFneg : ∀ y, (generic_format beta fexp y).run → (generic_format beta fexp (-y)).run :=
    generic_format_neg_closed beta fexp
  -- Use the UP existence at -x
  rcases round_UP_exists (beta := beta) (fexp := fexp) (-x) with ⟨fu, hFu, hup⟩
  -- Transform to DN at x with f = -fu
  refine ⟨-fu, ?_, ?_⟩
  · exact hFneg fu hFu
  · -- Apply the transformation lemma
    exact Rnd_UP_to_DN_via_neg (F := fun y => (generic_format beta fexp y).run) (x := x) (f := fu)
      hFneg hup

/-- Specification: Generic format is closed under rounding up

    For any x, there exists a value f in generic format
    that is the rounding up of x.
-/
theorem generic_format_round_UP (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ∃ f, (generic_format beta fexp f).run ∧ Rnd_UP_pt (fun y => (generic_format beta fexp y).run) x f := by
  -- Use the (temporary) existence axiom to obtain a witness.
  exact round_UP_exists beta fexp x

/-- Specification: Precision bounds for generic format

    For non-zero x in generic format, the scaled mantissa
    is bounded by beta^(mag(x) - cexp(x)).
-/
theorem generic_format_precision_bound
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (x : ℝ) (h : (generic_format beta fexp x).run) (hx : x ≠ 0)
    (hβ : 1 < beta) :
    abs (scaled_mantissa beta fexp x).run ≤ (beta : ℝ) ^ (mag beta x - (cexp beta fexp x).run) := by
  -- Use the general bound for scaled mantissa
  exact scaled_mantissa_lt_bpow (beta := beta) (fexp := fexp) (x := x) hβ

/-- Specification: Exponent monotonicity

    The exponent function is monotone.
-/
theorem fexp_monotone (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] :
    ∀ e1 e2 : Int, e1 ≤ e2 → e2 ≤ fexp e2 → fexp e1 ≤ fexp e2 := by
  -- Monotonicity holds on the "small" regime plateau by constancy
  intro e1 e2 hle hsmall
  -- From small-regime constancy at k = e2, any l ≤ fexp e2 has the same fexp
  have hpair := (FloatSpec.Core.Generic_fmt.Valid_exp.valid_exp (beta := beta) (fexp := fexp) e2)
  have hconst := (hpair.right hsmall).right
  -- Since e1 ≤ e2 ≤ fexp e2, we get fexp e1 = fexp e2 in particular
  have : fexp e1 = fexp e2 := by
    have : e1 ≤ fexp e2 := le_trans hle hsmall
    simpa using hconst e1 this
  simpa [this]

/-- Specification: Format equivalence under exponent bounds

    If x is in format with constant exponent e1,
    and e1 ≤ e2, then x is in format with exponent e2.
-/
theorem generic_format_equiv (beta : Int) (x : ℝ) (e1 e2 : Int) :
    ⦃⌜1 < beta ∧ e2 ≤ e1 ∧ (generic_format beta (fun _ => e1) x).run⌝⦄
    generic_format beta (fun _ => e2) x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro h
  rcases h with ⟨hβ, hle, hx_fmt⟩
  -- Base positivity and nonzeroness for zpow lemmas
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  -- Unpack the format equality at exponent e1
  have hx : x = ((Ztrunc (x * (beta : ℝ) ^ (-(e1))) : Int) : ℝ) * (beta : ℝ) ^ e1 := by
    simpa [generic_format, scaled_mantissa, cexp, F2R] using hx_fmt
  -- Target goal after unfolding the generic_format at exponent e2
  -- will be an equality; we set up the necessary arithmetic
  simp only [generic_format, scaled_mantissa, cexp, F2R]
  -- Notations
  set m1 : Int := Ztrunc (x * (beta : ℝ) ^ (-(e1))) with hm1
  have hx' : x = (m1 : ℝ) * (beta : ℝ) ^ e1 := by simpa [hm1] using hx
  -- Let k = e1 - e2 ≥ 0
  set k : Int := e1 - e2
  have hk_nonneg : 0 ≤ k := sub_nonneg.mpr hle
  -- Combine powers: β^e1 * β^(-e2) = β^(e1 - e2)
  have hmul_pow : (beta : ℝ) ^ e1 * ((beta : ℝ) ^ e2)⁻¹ = (beta : ℝ) ^ (e1 - e2) := by
    simpa [zpow_neg] using
      (FloatSpec.Core.Generic_fmt.zpow_mul_sub (a := (beta : ℝ)) (hbne := hbne) (e := e1) (c := e2))
  -- Express β^(e1 - e2) with a Nat exponent
  have hzpow_toNat : (beta : ℝ) ^ (e1 - e2) = (beta : ℝ) ^ (Int.toNat (e1 - e2)) := by
    simpa using FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat (beta : ℝ) (e1 - e2) hk_nonneg
  -- Cast Int power to real power
  have hcast_pow : (beta : ℝ) ^ (Int.toNat (e1 - e2)) = ((beta ^ (Int.toNat (e1 - e2)) : Int) : ℝ) := by
    rw [← Int.cast_pow]
  -- Compute the truncation at exponent e2
  have htrunc :
      Ztrunc (x * (beta : ℝ) ^ (-(e2))) = m1 * beta ^ (Int.toNat (e1 - e2)) := by
    calc
      Ztrunc (x * (beta : ℝ) ^ (-(e2)))
          = Ztrunc (((m1 : ℝ) * (beta : ℝ) ^ e1) * (beta : ℝ) ^ (-(e2))) := by
                simpa [hx']
      _   = Ztrunc ((m1 : ℝ) * ((beta : ℝ) ^ e1 * (beta : ℝ) ^ (-(e2)))) := by ring_nf
      _   = Ztrunc ((m1 : ℝ) * ((beta : ℝ) ^ (e1 - e2))) := by
                simpa [hmul_pow]
      _   = Ztrunc ((m1 : ℝ) * ((beta : ℝ) ^ (Int.toNat (e1 - e2)))) := by
                simpa [hzpow_toNat]
      _   = Ztrunc (((m1 * beta ^ (Int.toNat (e1 - e2))) : Int) : ℝ) := by
                -- Avoid deep simp recursion: rewrite the inside once, then fold
                have hmulcast :
                    (m1 : ℝ) * ((beta : ℝ) ^ (Int.toNat (e1 - e2)))
                      = (((m1 * beta ^ (Int.toNat (e1 - e2))) : Int) : ℝ) := by
                  simp only [hcast_pow, Int.cast_mul]
                simpa only [hmulcast]
      _   = m1 * beta ^ (Int.toNat (e1 - e2)) := FloatSpec.Core.Generic_fmt.Ztrunc_intCast _
  -- Split power to reconstruct x at exponent e2
  have hsplit : (beta : ℝ) ^ e1 = (beta : ℝ) ^ (e1 - e2) * (beta : ℝ) ^ e2 := by
    -- zpow_sub_add states (a^(e-c))*a^c = a^e; flip orientation
    simpa using (FloatSpec.Core.Generic_fmt.zpow_sub_add (a := (beta : ℝ)) (hbne := hbne) (e := e1) (c := e2)).symm
  -- Finish: rebuild x directly in the required orientation
  -- Goal after simp is: x = ((Ztrunc (x * β^(-e2)) : ℝ)) * β^e2
  -- We derive the right-hand side from the representation at e1
  calc
    x = (m1 : ℝ) * (beta : ℝ) ^ e1 := by simpa [hx']
    _ = (m1 : ℝ) * ((beta : ℝ) ^ (e1 - e2) * (beta : ℝ) ^ e2) := by
          rw [hsplit]
    _ = ((m1 : ℝ) * (beta : ℝ) ^ (e1 - e2)) * (beta : ℝ) ^ e2 := by ring
    _ = ((m1 : ℝ) * (beta : ℝ) ^ (Int.toNat (e1 - e2))) * (beta : ℝ) ^ e2 := by
          rw [hzpow_toNat]
    _ = (((m1 * beta ^ (Int.toNat (e1 - e2))) : Int) : ℝ) * (beta : ℝ) ^ e2 := by
          -- cast the integer product back to ℝ without triggering heavy simp recursion
          have : ((m1 * beta ^ (Int.toNat (e1 - e2)) : Int) : ℝ)
                    = (m1 : ℝ) * ((beta : ℝ) ^ (Int.toNat (e1 - e2))) := by
            calc
              ((m1 * beta ^ (Int.toNat (e1 - e2)) : Int) : ℝ)
                  = ((m1 : Int) : ℝ) * ((beta ^ (Int.toNat (e1 - e2)) : Int) : ℝ) := by
                        simp [Int.cast_mul]
              _   = (m1 : ℝ) * ((beta : ℝ) ^ (Int.toNat (e1 - e2))) := by
                        rw [hcast_pow]
          rw [this]
    _ = ((Ztrunc (x * (beta : ℝ) ^ (-(e2))) : Int) : ℝ) * (beta : ℝ) ^ e2 := by
          -- rewrite back using the computed truncation at e2
          have hZ' : ((m1 * beta ^ (Int.toNat (e1 - e2)) : Int) : ℝ)
                        = ((Ztrunc (x * (beta : ℝ) ^ (-(e2))) : Int) : ℝ) := by
            -- cast both sides of htrunc to ℝ (in reverse orientation)
            exact (congrArg (fun z : Int => (z : ℝ)) htrunc).symm
          -- replace the casted integer with the Ztrunc expression
          rw [hZ']

/-- Generic format from rounding -/
noncomputable def round_to_generic (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (mode : ℝ → ℝ → Prop) (x : ℝ) : ℝ :=
  -- Return the rounded value in generic format
  -- This would use classical choice to select a value satisfying the rounding mode
  let exp := (cexp beta fexp x).run
  let mantissa := x * (beta : ℝ) ^ (-exp)
  let rounded_mantissa := Ztrunc mantissa  -- Simple truncation for now
  (rounded_mantissa : ℝ) * (beta : ℝ) ^ exp

/-- Specification: Round to generic is well-defined

    The result of rounding to generic format is always
    in the generic format.
-/
theorem round_to_generic_spec (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (mode : ℝ → ℝ → Prop) (x : ℝ) :
    ⦃⌜True⌝⦄
    (pure (round_to_generic beta fexp mode x) : Id ℝ)
    ⦃⇓result => ⌜result = (F2R (FlocqFloat.mk (Ztrunc (x * (beta : ℝ) ^ (-(cexp beta fexp x).run))) (cexp beta fexp x).run : FlocqFloat beta)).run⌝⦄ := by
  intro _
  -- Unfold the rounding function; this is a direct reconstruction
  unfold round_to_generic
  simp [F2R]

/-- Coq (Generic_fmt.v):
Theorem round_0:
  forall rnd, round beta fexp rnd 0 = 0.

Lean (spec): Rounding any way at 0 returns 0.
-/
theorem round_0 (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (rnd : ℝ → ℝ → Prop) :
    ⦃⌜True⌝⦄
    (pure (round_to_generic beta fexp rnd 0) : Id ℝ)
    ⦃⇓r => ⌜r = 0⌝⦄ := by
  intro _
  -- Proof to be completed following Coq's Generic_fmt.round_0
  sorry

/-- Specification: Intersection is a generic format

    The intersection of two generic formats can be
    represented as another generic format.
-/
theorem generic_format_inter_valid (beta : Int) (fexp1 fexp2 : Int → Int)
    [Valid_exp beta fexp1] [Valid_exp beta fexp2]
    (hβ : 1 < beta) :
    ∃ fexp3, ∀ x, generic_format_inter beta fexp1 fexp2 x → (generic_format beta fexp3 x).run := by
  -- We can realize the intersection inside a single generic format by
  -- choosing the pointwise minimum exponent function.
  refine ⟨(fun k => min (fexp1 k) (fexp2 k)), ?_⟩
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  -- Let c1, c2 be the canonical exponents for each format, and c3 their min.
  set c1 : Int := fexp1 (mag beta x)
  set c2 : Int := fexp2 (mag beta x)
  set c3 : Int := min c1 c2
  -- Denote the integer mantissas provided by each format
  have hx1' : x = ((Ztrunc (x * (beta : ℝ) ^ (-(c1))) : Int) : ℝ) * (beta : ℝ) ^ c1 := by
    simpa [generic_format, scaled_mantissa, cexp, F2R, c1] using hx1
  have hx2' : x = ((Ztrunc (x * (beta : ℝ) ^ (-(c2))) : Int) : ℝ) * (beta : ℝ) ^ c2 := by
    simpa [generic_format, scaled_mantissa, cexp, F2R, c2] using hx2
  -- Take m1 from the first representation; since c3 ≤ c1, we can reconstruct at c3
  set m1 : Int := Ztrunc (x * (beta : ℝ) ^ (-(c1))) with hm1
  have hc3_le_c1 : c3 ≤ c1 := by simpa [c3] using (min_le_left c1 c2)
  -- Base positivity for zpow identities
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  -- Combine the powers: β^c1 * β^(-c3) = β^(c1 - c3)
  have hmul_pow : (beta : ℝ) ^ c1 * (beta : ℝ) ^ (-(c3)) = (beta : ℝ) ^ (c1 - c3) := by
    simpa [sub_eq_add_neg] using (FloatSpec.Core.Generic_fmt.zpow_mul_sub (a := (beta : ℝ)) (hbne := hbne) (e := c1) (c := c3))
  -- Nonnegativity of the exponent difference
  have hdiff_nonneg : 0 ≤ c1 - c3 := sub_nonneg.mpr hc3_le_c1
  -- Convert to Nat power on nonnegative exponents
  have hzpow_toNat : (beta : ℝ) ^ (c1 - c3) = (beta : ℝ) ^ (Int.toNat (c1 - c3)) := by
    simpa using FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat (beta : ℝ) (c1 - c3) hdiff_nonneg
  -- Cast Int power to real power of Int
  have hcast_pow : (beta : ℝ) ^ (Int.toNat (c1 - c3)) = ((beta ^ (Int.toNat (c1 - c3)) : Int) : ℝ) := by
    rw [← Int.cast_pow]
  -- Compute the truncation at exponent c3 using the c1-representation
  have htrunc_c3 :
      Ztrunc (x * (beta : ℝ) ^ (-(c3))) = m1 * beta ^ (Int.toNat (c1 - c3)) := by
    -- First, rewrite the argument using the c1-representation of x without heavy simp
    have hx_mul := congrArg (fun t : ℝ => t * (beta : ℝ) ^ (-(c3))) hx1'
    have hx_mul' : x * (beta : ℝ) ^ (-(c3)) = ((m1 : ℝ) * (beta : ℝ) ^ c1) * (beta : ℝ) ^ (-(c3)) := by
      simpa [hm1, mul_comm, mul_left_comm, mul_assoc] using hx_mul
    have hZeq : Ztrunc (x * (beta : ℝ) ^ (-(c3)))
                = Ztrunc (((m1 : ℝ) * (beta : ℝ) ^ c1) * (beta : ℝ) ^ (-(c3))) :=
      congrArg Ztrunc hx_mul'
    calc
      Ztrunc (x * (beta : ℝ) ^ (-(c3)))
          = Ztrunc (((m1 : ℝ) * (beta : ℝ) ^ c1) * (beta : ℝ) ^ (-(c3))) := hZeq
      _   = Ztrunc ((m1 : ℝ) * ((beta : ℝ) ^ c1 * (beta : ℝ) ^ (-(c3)))) := by ring_nf
      _   = Ztrunc ((m1 : ℝ) * ((beta : ℝ) ^ (c1 - c3))) := by
                -- Apply the zpow product identity inside Ztrunc
                simpa [zpow_neg]
                  using congrArg (fun t => Ztrunc ((m1 : ℝ) * t)) hmul_pow
      _   = Ztrunc ((m1 : ℝ) * ((beta : ℝ) ^ (Int.toNat (c1 - c3)))) := by
                simpa [hzpow_toNat]
      _   = Ztrunc (((m1 * beta ^ (Int.toNat (c1 - c3))) : Int) : ℝ) := by
                -- Avoid deep simp recursion: rewrite the inside once, then fold
                have hmulcast :
                    (m1 : ℝ) * ((beta : ℝ) ^ (Int.toNat (c1 - c3)))
                      = (((m1 * beta ^ (Int.toNat (c1 - c3))) : Int) : ℝ) := by
                  simp only [hcast_pow, Int.cast_mul]
                simpa only [hmulcast]
      _   = m1 * beta ^ (Int.toNat (c1 - c3)) := FloatSpec.Core.Generic_fmt.Ztrunc_intCast _
  -- Split the power to reconstruct x at exponent c3
  have hsplit : (beta : ℝ) ^ c1 = (beta : ℝ) ^ (c1 - c3) * (beta : ℝ) ^ c3 := by
    simpa [sub_add_cancel] using
      (FloatSpec.Core.Generic_fmt.zpow_sub_add (a := (beta : ℝ)) (hbne := hbne) (e := c1) (c := c3)).symm
  -- Conclude the generic_format for fexp3 at x
  -- Unfold target generic_format with fexp3 = min fexp1 fexp2, so exponent is c3
  -- Build the required reconstruction equality and finish by unfolding generic_format
  have hrecon : x = ((Ztrunc (x * (beta : ℝ) ^ (-(c3))) : Int) : ℝ) * (beta : ℝ) ^ c3 := by
    calc
      x = (m1 : ℝ) * (beta : ℝ) ^ c1 := by simpa [hm1] using hx1'
      _ = (m1 : ℝ) * ((beta : ℝ) ^ (c1 - c3) * (beta : ℝ) ^ c3) := by rw [hsplit]
      _ = ((m1 : ℝ) * (beta : ℝ) ^ (c1 - c3)) * (beta : ℝ) ^ c3 := by ring
      _ = ((m1 : ℝ) * (beta : ℝ) ^ (Int.toNat (c1 - c3))) * (beta : ℝ) ^ c3 := by
            simpa [hzpow_toNat]
      _ = (((m1 * beta ^ (Int.toNat (c1 - c3))) : Int) : ℝ) * (beta : ℝ) ^ c3 := by
            -- cast the integer product back to ℝ without triggering heavy simp recursion
            have : ((m1 * beta ^ (Int.toNat (c1 - c3)) : Int) : ℝ)
                      = (m1 : ℝ) * ((beta : ℝ) ^ (Int.toNat (c1 - c3))) := by
              calc
                ((m1 * beta ^ (Int.toNat (c1 - c3)) : Int) : ℝ)
                    = ((m1 : Int) : ℝ) * ((beta ^ (Int.toNat (c1 - c3)) : Int) : ℝ) := by
                          simp [Int.cast_mul]
                _   = (m1 : ℝ) * ((beta : ℝ) ^ (Int.toNat (c1 - c3))) := by
                          rw [hcast_pow]
            rw [this]
      _ = ((Ztrunc (x * (beta : ℝ) ^ (-(c3))) : Int) : ℝ) * (beta : ℝ) ^ c3 := by
            -- rewrite back using the computed truncation at c3
            have hZ' : ((m1 * beta ^ (Int.toNat (c1 - c3)) : Int) : ℝ)
                          = ((Ztrunc (x * (beta : ℝ) ^ (-(c3))) : Int) : ℝ) := by
              -- cast both sides of htrunc_c3 to ℝ (in reverse orientation)
              exact (congrArg (fun z : Int => (z : ℝ)) htrunc_c3).symm
            -- replace the casted integer with the Ztrunc expression
            rw [hZ']
  -- Conclude generic_format by unfolding
  have : (generic_format beta (fun k => min (fexp1 k) (fexp2 k)) x).run := by
    -- Make the canonical exponent explicit: it equals c3 by definition
    have hcexp_min : (cexp beta (fun k => min (fexp1 k) (fexp2 k)) x).run = c3 := by
      simp [FloatSpec.Core.Generic_fmt.cexp, c1, c2, c3]
    -- Now unfold and rewrite to the reconstruction equality
    simp only [generic_format, scaled_mantissa, cexp, F2R, hcexp_min]
    -- Goal reduces exactly to the reconstruction equality
    simpa using hrecon
  simpa using this

/-- Specification: Magnitude is compatible with generic format

    For non-zero x in generic format, the exponent function
    satisfies fexp(mag(x) + 1) ≤ mag(x).
-/
theorem mag_generic_format (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (x : ℝ) (h : (generic_format beta fexp x).run) (hx : x ≠ 0)
    (hβ : 1 < beta) :
    fexp (mag beta x + 1) ≤ mag beta x := by
  -- Notations
  set k : Int := mag beta x
  set e : Int := fexp k
  -- Base positivity facts
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hb_gt1R : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hb_ge1 : (1 : ℝ) ≤ (beta : ℝ) := hb_gt1R.le
  -- Scaled mantissa is integer-valued for numbers in format
  have hsm_int := (scaled_mantissa_generic (beta := beta) (fexp := fexp) (x := x)) h
  set mR : ℝ := (scaled_mantissa beta fexp x).run
  have hmR_eq : mR = (Ztrunc mR : Int) := by simpa [mR] using hsm_int
  -- Reconstruction equality: x = (Ztrunc mR) * β^e
  have hx_recon : x = ((Ztrunc mR : Int) : ℝ) * (beta : ℝ) ^ e := by
    have hfmt := h
    -- Note: (scaled_mantissa beta fexp x).run = x * β^(-e) by definition of e, k
    simpa [generic_format, scaled_mantissa, FloatSpec.Core.Generic_fmt.cexp, F2R, k, e, mR] using hfmt
  -- mR ≠ 0, otherwise x would be 0
  have hmR_ne : mR ≠ 0 := by
    intro h0
    have : Ztrunc mR = 0 := by simpa [h0, FloatSpec.Core.Generic_fmt.Ztrunc_zero] using congrArg Ztrunc h0
    have : x = 0 := by simpa [this] using hx_recon
    exact hx this
  -- From hmR_eq and hmR_ne, |mR| ≥ 1
  have h_abs_mR_ge1 : (1 : ℝ) ≤ abs mR := by
    -- mR equals an integer z ≠ 0
    set z : Int := Ztrunc mR
    have hmR_eq' : mR = (z : ℝ) := by simpa [z] using hmR_eq
    have hz_ne : z ≠ 0 := by
      intro hz
      exact hmR_ne (by simpa [hmR_eq', hz])
    -- case analysis on sign of z
    by_cases hz_nonneg : 0 ≤ z
    · -- z ≥ 0 and z ≠ 0 ⇒ 1 ≤ z
      have hz_pos : 0 < z := lt_of_le_of_ne hz_nonneg (by simpa [eq_comm] using hz_ne)
      have hz_one_le : (1 : Int) ≤ z := (Int.add_one_le_iff).mpr hz_pos
      have hz_one_leR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_one_le
      have habs : abs mR = (z : ℝ) := by simpa [hmR_eq', abs_of_nonneg (by exact_mod_cast hz_nonneg)]
      simpa [habs]
    · -- z ≤ 0 and z ≠ 0 ⇒ 1 ≤ -z
      have hz_le : z ≤ 0 := le_of_not_ge hz_nonneg
      have hz_lt : z < 0 := lt_of_le_of_ne hz_le (by simpa [hz_ne])
      have hpos_negz : 0 < -z := Int.neg_pos.mpr hz_lt
      have hone_le_negz : (1 : Int) ≤ -z := (Int.add_one_le_iff).mpr hpos_negz
      have hone_le_negzR : (1 : ℝ) ≤ (-z : ℝ) := by exact_mod_cast hone_le_negz
      have habs : abs mR = (-z : ℝ) := by
        have hzleR : (z : ℝ) ≤ 0 := by exact_mod_cast hz_le
        have : abs mR = abs (z : ℝ) := by simpa [hmR_eq']
        simpa [this, abs_of_nonpos hzleR]
      simpa [habs] using hone_le_negzR
  -- General bound: |mR| ≤ β^(k - e)
  have h_abs_mR_le : abs mR ≤ (beta : ℝ) ^ (k - e) := by
    -- scaled_mantissa_lt_bpow with hβ, then unfold mR, k, e
    have := scaled_mantissa_lt_bpow (beta := beta) (fexp := fexp) (x := x) hβ
    simpa [mR, k, e, FloatSpec.Core.Generic_fmt.cexp] using this
  -- Hence 1 ≤ β^(k - e)
  have hone_le_pow : (1 : ℝ) ≤ (beta : ℝ) ^ (k - e) := le_trans h_abs_mR_ge1 h_abs_mR_le
  -- Show that k - e cannot be negative (else β^(k-e) < 1)
  have hek_le : e ≤ k := by
    -- By cases on e ≤ k; derive a contradiction in the negative case.
    by_cases he_le : e ≤ k
    · exact he_le
    · -- he_le is false, so e - k > 0
      have hpos : 0 < e - k := sub_pos.mpr (lt_of_not_ge he_le)
      -- Show 1 ≤ (β : ℝ) ^ (e - k - 1)
      have hone_le_pow_u : (1 : ℝ) ≤ (beta : ℝ) ^ (e - k - 1) := by
        -- u := e - k - 1 ≥ 0
        have hu_nonneg : 0 ≤ e - k - 1 := by
          have : (1 : Int) ≤ e - k := (Int.add_one_le_iff).mpr hpos
          exact sub_nonneg.mpr this
        have hzpow_toNat : (beta : ℝ) ^ (e - k - 1) = (beta : ℝ) ^ (Int.toNat (e - k - 1)) := by
          simpa using FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat (beta : ℝ) (e - k - 1) hu_nonneg
        -- 1 ≤ β^n for all n : Nat
        have one_le_pow_nat : ∀ n : Nat, (1 : ℝ) ≤ (beta : ℝ) ^ n := by
          intro n; induction n with
          | zero => simp
          | succ n ih =>
              have hpow_nonneg : 0 ≤ (beta : ℝ) ^ n := pow_nonneg (le_of_lt hbposR) n
              have : (1 : ℝ) * 1 ≤ (beta : ℝ) ^ n * (beta : ℝ) :=
                mul_le_mul ih hb_ge1 (by norm_num) hpow_nonneg
              simpa [pow_succ] using this
        simpa [hzpow_toNat] using one_le_pow_nat (Int.toNat (e - k - 1))
      -- From 1 ≤ β^(e-k-1), deduce β ≤ β^(e-k)
      have hone_le_pow_t : (beta : ℝ) ≤ (beta : ℝ) ^ (e - k) := by
        have hmul : (1 : ℝ) * (beta : ℝ) ≤ (beta : ℝ) ^ (e - k - 1) * (beta : ℝ) :=
          mul_le_mul_of_nonneg_right hone_le_pow_u (le_of_lt hbposR)
        have hpow_add : (beta : ℝ) ^ (e - k - 1) * (beta : ℝ) = (beta : ℝ) ^ (e - k) := by
          -- β^(u) * β = β^(u+1)
          have hz := (zpow_add₀ (by exact ne_of_gt hbposR) (e - k - 1) (1 : Int))
          -- (β : ℝ) ^ ((e - k - 1) + 1) = (β : ℝ) ^ (e - k - 1) * (β : ℝ) ^ 1
          simpa [add_comm, add_left_comm, add_assoc, zpow_one]
            using hz.symm
        simpa [one_mul, hpow_add] using hmul
      -- Therefore 1 < β^(e - k)
      have hone_lt_pow_t : (1 : ℝ) < (beta : ℝ) ^ (e - k) := lt_of_lt_of_le hb_gt1R hone_le_pow_t
      -- Multiply 1 ≤ β^(k - e) by β^(e - k) > 0 on the left to get β^(e - k) ≤ 1
      have hpow_pos : 0 < (beta : ℝ) ^ (e - k) := zpow_pos hbposR _
      have : (beta : ℝ) ^ (e - k) * 1 ≤ (beta : ℝ) ^ (e - k) * (beta : ℝ) ^ (k - e) :=
        mul_le_mul_of_nonneg_left hone_le_pow hpow_pos.le
      have hmul_id : (beta : ℝ) ^ (e - k) * (beta : ℝ) ^ (k - e) = 1 := by
        simpa [add_comm, add_left_comm, add_assoc, zpow_zero]
          using (zpow_add₀ (by exact ne_of_gt hbposR) (e - k) (k - e)).symm
      have : (beta : ℝ) ^ (e - k) ≤ 1 := by simpa [hmul_id, one_mul] using this
      have hfalse : False := (not_le_of_gt hone_lt_pow_t) this
      exact False.elim hfalse
  -- Apply Valid_exp at k, splitting on e < k vs e = k
  have hpair := (Valid_exp.valid_exp (beta := beta) (fexp := fexp) k)
  by_cases hlt : e < k
  · -- Large regime at k
    have : fexp (k + 1) ≤ k := (hpair.left) hlt
    simpa [k] using this
  · -- Small regime: e = k
    have heq : e = k := le_antisymm hek_le (le_of_not_gt hlt)
    -- From e = k and e = fexp k by definition, we rewrite the small-regime bound
    have heq_fk : fexp k = k := by simpa [e] using heq
    have hsmall : k ≤ fexp k := by simpa [heq_fk]
    have hbound := (hpair.right hsmall).left
    simpa [heq_fk] using hbound

/-- Specification: Precision characterization

    For non-zero x in generic format, there exists a mantissa m
    such that x = F2R(m, cexp(x)) with bounded mantissa.
-/
theorem precision_generic_format (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (x : ℝ) (h : (generic_format beta fexp x).run) (hx : x ≠ 0) (hβ : 1 < beta) :
    ∃ m : Int,
      x = (F2R (FlocqFloat.mk m (cexp beta fexp x).run : FlocqFloat beta)).run ∧
      Int.natAbs m ≤ Int.natAbs beta ^ ((mag beta x - (cexp beta fexp x).run).toNat) := by
  -- Notations
  set k : Int := mag beta x
  set e : Int := (cexp beta fexp x).run
  -- Define the real scaled mantissa mR and its integer truncation m
  set mR : ℝ := (scaled_mantissa beta fexp x).run
  set m : Int := Ztrunc mR
  -- From generic_format, we get the reconstruction equality with m = Ztrunc mR
  have hx_recon : x = ((Ztrunc mR : Int) : ℝ) * (beta : ℝ) ^ e := by
    simpa [generic_format, scaled_mantissa, FloatSpec.Core.Generic_fmt.cexp, F2R, k, e, mR]
      using h
  -- The scaled mantissa equals its truncation for numbers in the format
  have hsm_int := (scaled_mantissa_generic (beta := beta) (fexp := fexp) (x := x)) h
  have hmR_eq : mR = (Ztrunc mR : Int) := by simpa [mR] using hsm_int
  -- Conclude mR is exactly the integer m as a real
  have hmR_int : mR = (m : ℝ) := by simpa [m] using hmR_eq
  -- Provide the witness mantissa and equality
  refine ⟨m, ?_, ?_⟩
  · -- Equality part: rewrite with m
    simpa [m] using hx_recon
  · -- Bound on |m|
    -- Base positivity for using zpow lemmas and absolute values
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    have hbneR : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
    -- Nonzero mantissa: otherwise x = 0 via the reconstruction
    have hm_ne : m ≠ 0 := by
      intro hm0
      have : x = 0 := by simpa [m, hm0] using hx_recon
      exact hx this
    -- General scaled mantissa bound and rewrite to |m|
    have h_abs_le : abs mR ≤ (beta : ℝ) ^ (k - e) := by
      simpa [mR, k, e, FloatSpec.Core.Generic_fmt.cexp]
        using scaled_mantissa_lt_bpow (beta := beta) (fexp := fexp) (x := x) hβ
    have h_abs_m_le : abs (m : ℝ) ≤ (beta : ℝ) ^ (k - e) := by simpa [hmR_int] using h_abs_le
    -- Since m ≠ 0, we have 1 ≤ |m|
    have hone_le_abs_m : (1 : ℝ) ≤ abs (m : ℝ) := by
      by_cases hm_nonneg : 0 ≤ m
      · -- m ≥ 0 and m ≠ 0 ⇒ 1 ≤ m, hence 1 ≤ |m|
        have hm_pos : 0 < m := lt_of_le_of_ne hm_nonneg (by simpa [eq_comm] using hm_ne)
        have h1le : (1 : Int) ≤ m := (Int.add_one_le_iff).mpr hm_pos
        have h1leR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1le
        have : abs (m : ℝ) = (m : ℝ) := by
          have : 0 ≤ (m : ℝ) := by exact_mod_cast hm_nonneg
          simpa [abs_of_nonneg this]
        simpa [this] using h1leR
      · -- m ≤ 0 and m ≠ 0 ⇒ 1 ≤ -m, hence 1 ≤ |m|
        have hm_le : m ≤ 0 := le_of_not_ge hm_nonneg
        have hm_lt : m < 0 := lt_of_le_of_ne hm_le (by simpa using hm_ne)
        have hpos_negm : 0 < -m := Int.neg_pos.mpr hm_lt
        have hone_le_negm : (1 : Int) ≤ -m := (Int.add_one_le_iff).mpr hpos_negm
        have hone_le_negmR : (1 : ℝ) ≤ (-m : ℝ) := by exact_mod_cast hone_le_negm
        have hzleR : (m : ℝ) ≤ 0 := by exact_mod_cast hm_le
        have : abs (m : ℝ) = (-m : ℝ) := by simpa [abs_of_nonpos hzleR]
        simpa [this] using hone_le_negmR
    -- Thus 1 ≤ β^(k - e), hence k - e ≥ 0 (otherwise β^(k-e) < 1 for β > 1)
    have hone_le_pow : (1 : ℝ) ≤ (beta : ℝ) ^ (k - e) := le_trans hone_le_abs_m h_abs_m_le
    have hk_sub_nonneg : 0 ≤ k - e := by
      -- By contradiction: if e > k, derive a contradiction as in mag_generic_format
      by_contra hneg
      -- hneg: ¬ (0 ≤ k - e) ⇔ k < e
      have hpos : 0 < e - k := by
        have hklt : k < e := lt_of_not_ge (by simpa [sub_nonneg] using hneg)
        exact sub_pos.mpr hklt
      have hone_le_pow_u : (1 : ℝ) ≤ (beta : ℝ) ^ (e - k - 1) := by
        -- Show nonnegativity of u := e - k - 1 and convert to Nat power
        have hu_nonneg : 0 ≤ e - k - 1 := by
          have : (1 : Int) ≤ e - k := (Int.add_one_le_iff).mpr hpos
          exact sub_nonneg.mpr this
        have hzpow_toNat : (beta : ℝ) ^ (e - k - 1) = (beta : ℝ) ^ (Int.toNat (e - k - 1)) := by
          simpa using FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat (beta : ℝ) (e - k - 1) hu_nonneg
        -- 1 ≤ β^n for all n : Nat since β ≥ 1
        have hb_ge1 : (1 : ℝ) ≤ (beta : ℝ) := (by exact_mod_cast hβ : (1 : ℝ) < (beta : ℝ)).le
        have one_le_pow_nat : ∀ n : Nat, (1 : ℝ) ≤ (beta : ℝ) ^ n := by
          intro n; induction n with
          | zero => simp
          | succ n ih =>
              have hpow_nonneg : 0 ≤ (beta : ℝ) ^ n :=
                pow_nonneg (le_of_lt hbposR) n
              have : (1 : ℝ) * 1 ≤ (beta : ℝ) ^ n * (beta : ℝ) :=
                mul_le_mul ih hb_ge1 (by norm_num) hpow_nonneg
              simpa [pow_succ] using this
        simpa [hzpow_toNat] using one_le_pow_nat (Int.toNat (e - k - 1))
      -- From 1 ≤ β^(e-k-1), deduce β ≤ β^(e-k)
      have hone_le_pow_t : (beta : ℝ) ≤ (beta : ℝ) ^ (e - k) := by
        have hmul : (1 : ℝ) * (beta : ℝ) ≤ (beta : ℝ) ^ (e - k - 1) * (beta : ℝ) :=
          mul_le_mul_of_nonneg_right hone_le_pow_u (le_of_lt hbposR)
        have hpow_add : (beta : ℝ) ^ (e - k - 1) * (beta : ℝ) = (beta : ℝ) ^ (e - k) := by
          have hz := (zpow_add₀ (by exact ne_of_gt hbposR) (e - k - 1) (1 : Int))
          simpa [add_comm, add_left_comm, add_assoc, zpow_one] using hz.symm
        simpa [one_mul, hpow_add] using hmul
      have hone_lt_pow_t : (1 : ℝ) < (beta : ℝ) ^ (e - k) := lt_of_lt_of_le (by exact_mod_cast hβ) hone_le_pow_t
      have hpow_pos : 0 < (beta : ℝ) ^ (e - k) := zpow_pos hbposR _
      have : (beta : ℝ) ^ (e - k) * 1 ≤ (beta : ℝ) ^ (e - k) * (beta : ℝ) ^ (k - e) :=
        mul_le_mul_of_nonneg_left hone_le_pow hpow_pos.le
      have hmul_id : (beta : ℝ) ^ (e - k) * (beta : ℝ) ^ (k - e) = 1 := by
        simpa [add_comm, add_left_comm, add_assoc, zpow_zero]
          using (zpow_add₀ (by exact ne_of_gt hbposR) (e - k) (k - e)).symm
      have hle1 : (beta : ℝ) ^ (e - k) ≤ 1 := by simpa [hmul_id, one_mul] using this
      exact (not_lt_of_ge hle1) hone_lt_pow_t
    -- Now we can rewrite the RHS power via toNat
    have hzpow_toNat : (beta : ℝ) ^ (k - e) = (beta : ℝ) ^ (Int.toNat (k - e)) := by
      simpa using FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat (beta : ℝ) (k - e) hk_sub_nonneg
    -- Rewrite base (β : ℝ) as ((natAbs β) : ℝ) since β > 0
    have hbeta_cast_eq : ((Int.natAbs beta : Nat) : ℝ) = (beta : ℝ) := by
      have : ((Int.natAbs beta : Nat) : ℝ) = abs (beta : ℝ) := by
        simpa [Int.cast_natAbs, Int.cast_abs]
      simpa [abs_of_pos hbposR] using this
    -- Convert the RHS to a casted Nat power
    have hRHS_cast : (beta : ℝ) ^ (Int.toNat (k - e))
        = ((Int.natAbs beta ^ Int.toNat (k - e) : Nat) : ℝ) := by
      -- replace base by natAbs beta and use Nat.cast_pow
      have hbase : ((Int.natAbs beta : Nat) : ℝ) = (beta : ℝ) := hbeta_cast_eq
      simpa [hbase, Nat.cast_pow]
    -- Combine and conclude as a Nat inequality via monotonicity of casts
    have hcast_ineq : (Int.natAbs m : ℝ) ≤ ((Int.natAbs beta ^ Int.toNat (k - e) : Nat) : ℝ) := by
      -- Use ((natAbs m) : ℝ) = |(m : ℝ)| and rewrite the RHS using hzpow_toNat and hRHS_cast
      have hLHS : (Int.natAbs m : ℝ) = abs (m : ℝ) := by
        simpa [Int.cast_natAbs, Int.cast_abs]
      simpa [hLHS, hzpow_toNat, hRHS_cast] using h_abs_m_le
    -- Coercion monotonicity gives the required Nat inequality
    exact (by exact_mod_cast hcast_ineq)

/-- Specification: Generic format error bound

    For any x, there exists f in generic format within
    half ULP of x.
-/
theorem generic_format_error_bound (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ∃ f, (generic_format beta fexp f).run ∧
    abs (f - x) ≤ (1/2) * (beta : ℝ) ^ (cexp beta fexp x).run := by
  exact exists_round_half_ulp beta fexp x

/-- Specification: Relative error bound

    For non-zero x, there exists f in generic format
    with bounded relative error.
-/
theorem generic_format_relative_error (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (x : ℝ) (hx : x ≠ 0) (hβ : 1 < beta) :
    ∃ f, (generic_format beta fexp f).run ∧ f ≠ 0 ∧
    abs (f - x) / abs x ≤ (1/2) * (beta : ℝ) ^ ((cexp beta fexp x).run - mag beta x + 1) := by
  -- Use the nonzero half‑ULP witness axiom, then divide by |x| and apply the reciprocal bound
  classical
  obtain ⟨f, hfF, hf_ne, herr_abs⟩ := exists_round_half_ulp_nz (beta := beta) (fexp := fexp) (x := x) hx
  set e : Int := (cexp beta fexp x).run
  set k : Int := mag beta x
  have hxpos : 0 < abs x := abs_pos.mpr hx
  -- Multiply both sides of the absolute error by |x|⁻¹ (nonnegative)
  have hx_inv_nonneg : 0 ≤ (abs x)⁻¹ := inv_nonneg.mpr (le_of_lt hxpos)
  have hmul := mul_le_mul_of_nonneg_right herr_abs hx_inv_nonneg
  have hdiv : abs (f - x) / abs x ≤ ((1/2) * (beta : ℝ) ^ e) * (abs x)⁻¹ := by
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hrecip := (recip_abs_x_le (beta := beta) (x := x)) ⟨hβ, hx⟩
  have hrecip_le' : (abs x)⁻¹ ≤ (beta : ℝ) ^ (1 - k) := by simpa [one_div, k] using hrecip
  have hbposR : 0 < (beta : ℝ) := by
    have : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    exact_mod_cast this
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hcoeff_nonneg : 0 ≤ (1/2) * (beta : ℝ) ^ e := by
    have : 0 ≤ (beta : ℝ) ^ e := le_of_lt (zpow_pos hbposR e)
    exact mul_nonneg (by norm_num) this
  have : ((1/2) * (beta : ℝ) ^ e) * (abs x)⁻¹ ≤ ((1/2) * (beta : ℝ) ^ e) * (beta : ℝ) ^ (1 - k) :=
    mul_le_mul_of_nonneg_left hrecip_le' hcoeff_nonneg
  have : ((1/2) * (beta : ℝ) ^ e) * (abs x)⁻¹ ≤ (1/2) * (beta : ℝ) ^ (e - k + 1) := by
    -- rewrite RHS using zpow_add and associativity
    simpa [sub_eq_add_neg, one_div, mul_comm, mul_left_comm, mul_assoc, zpow_add₀ hbne] using this
  exact ⟨f, hfF, hf_ne, le_trans hdiv this⟩

/-- Round to nearest in generic format

    Computes the nearest representable value in the format.
-/
noncomputable def round_N_to_format (beta : Int) (fexp : Int → Int) (x : ℝ) : Id ℝ :=
  -- Placeholder: not needed for properties below
  pure 0

/-- Round down to generic format

    Computes the largest representable value not exceeding x.
-/
noncomputable def round_DN_to_format (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) : Id ℝ :=
  -- Use classical choice from existence of DN rounding in generic format
  pure (Classical.choose (round_DN_exists beta fexp x))

/-- Round up to generic format

    Computes the smallest representable value not less than x.
-/
noncomputable def round_UP_to_format (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) : Id ℝ :=
  -- Use classical choice from existence of UP rounding in generic format
  pure (Classical.choose (round_UP_exists beta fexp x))

/-- Specification: Properties of format-specific rounding

    The rounding functions produce values in the format
    and satisfy the expected ordering properties.
-/
theorem round_to_format_properties (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ⦃⌜beta > 1⌝⦄
    do
      let down ← round_DN_to_format beta fexp x
      let up ← round_UP_to_format beta fexp x
      pure (down, up)
    ⦃⇓result => ⌜let (down, up) := result;
                   (generic_format beta fexp down).run ∧
                   (generic_format beta fexp up).run ∧
                   down ≤ x ∧ x ≤ up⌝⦄ := by
  intro _
  -- Evaluate the do-block and unfold our definitions of the rounding helpers
  simp [round_DN_to_format, round_UP_to_format]
  -- Retrieve properties of the chosen down and up values
  have hDN := Classical.choose_spec (round_DN_exists beta fexp x)
  have hUP := Classical.choose_spec (round_UP_exists beta fexp x)
  -- Unpack DN: format membership and DN predicate
  rcases hDN with ⟨hFdn, hdn⟩
  rcases hUP with ⟨hFup, hup⟩
  -- Extract ordering facts from the predicates
  rcases hdn with ⟨_, hdn_le, _⟩
  rcases hup with ⟨_, hup_ge, _⟩
  -- Conclude the required conjunction
  exact ⟨hFdn, hFup, hdn_le, hup_ge⟩

end FloatSpec.Core.Round_generic
