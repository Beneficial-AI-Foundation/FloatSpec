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
  sorry

/-- Specification: Generic format is closed under rounding up

    For any x, there exists a value f in generic format
    that is the rounding up of x.
-/
theorem generic_format_round_UP (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ∃ f, (generic_format beta fexp f).run ∧ Rnd_UP_pt (fun y => (generic_format beta fexp y).run) x f := by
  sorry

/-- Specification: Precision bounds for generic format

    For non-zero x in generic format, the scaled mantissa
    is bounded by beta^(mag(x) - cexp(x)).
-/
theorem generic_format_precision_bound (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) (h : (generic_format beta fexp x).run) (hx : x ≠ 0) :
    abs (scaled_mantissa beta fexp x).run < (beta : ℝ) ^ (mag beta x - (cexp beta fexp x).run) := by
  sorry

/-- Specification: Exponent monotonicity

    The exponent function is monotone.
-/
theorem fexp_monotone (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] : ∀ e1 e2 : Int, e1 ≤ e2 → fexp e1 ≤ fexp e2 := by
  sorry

/-- Specification: Format equivalence under exponent bounds

    If x is in format with constant exponent e1,
    and e1 ≤ e2, then x is in format with exponent e2.
-/
theorem generic_format_equiv (beta : Int) (x : ℝ) (e1 e2 : Int) :
    ⦃⌜e1 ≤ e2 ∧ (generic_format beta (fun _ => e1) x).run⌝⦄
    generic_format beta (fun _ => e2) x
    ⦃⇓result => ⌜result⌝⦄ := by
  intro h
  simp [generic_format] at h
  sorry

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
    generic_format beta fexp (round_to_generic beta fexp mode x)
    ⦃⇓result => ⌜result⌝⦄ := by
  intro _
  sorry

/-- Specification: Intersection is a generic format

    The intersection of two generic formats can be
    represented as another generic format.
-/
theorem generic_format_inter_valid (beta : Int) (fexp1 fexp2 : Int → Int)
    [Valid_exp beta fexp1] [Valid_exp beta fexp2] :
    ∃ fexp3, ∀ x, generic_format_inter beta fexp1 fexp2 x ↔ (generic_format beta fexp3 x).run := by
  sorry

/-- Specification: Magnitude is compatible with generic format

    For non-zero x in generic format, the exponent function
    satisfies fexp(mag(x) + 1) ≤ mag(x).
-/
theorem mag_generic_format (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) (h : (generic_format beta fexp x).run) (hx : x ≠ 0) :
    fexp (mag beta x + 1) ≤ mag beta x := by
  sorry

/-- Specification: Precision characterization

    For non-zero x in generic format, there exists a mantissa m
    such that x = F2R(m, cexp(x)) with bounded mantissa.
-/
theorem precision_generic_format (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) (h : (generic_format beta fexp x).run) (hx : x ≠ 0) :
    ∃ m : Int, x = (F2R (FlocqFloat.mk m (cexp beta fexp x).run : FlocqFloat beta)).run ∧
    Int.natAbs m < Int.natAbs beta ^ ((mag beta x - (cexp beta fexp x).run).toNat) := by
  sorry

/-- Specification: Generic format error bound

    For any x, there exists f in generic format within
    half ULP of x.
-/
theorem generic_format_error_bound (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) :
    ∃ f, (generic_format beta fexp f).run ∧
    abs (f - x) ≤ (1/2) * (beta : ℝ) ^ (cexp beta fexp x).run := by
  sorry

/-- Specification: Relative error bound

    For non-zero x, there exists f in generic format
    with bounded relative error.
-/
theorem generic_format_relative_error (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp] (x : ℝ) (hx : x ≠ 0) :
    ∃ f, (generic_format beta fexp f).run ∧ f ≠ 0 ∧
    abs (f - x) / abs x ≤ (1/2) * (beta : ℝ) ^ ((cexp beta fexp x).run - mag beta x) := by
  sorry

/-- Round to nearest in generic format

    Computes the nearest representable value in the format.
-/
noncomputable def round_N_to_format (beta : Int) (fexp : Int → Int) (x : ℝ) : Id ℝ :=
  sorry -- Implementation would use classical choice

/-- Round down to generic format

    Computes the largest representable value not exceeding x.
-/
noncomputable def round_DN_to_format (beta : Int) (fexp : Int → Int) (x : ℝ) : Id ℝ :=
  sorry -- Implementation would use classical choice

/-- Round up to generic format

    Computes the smallest representable value not less than x.
-/
noncomputable def round_UP_to_format (beta : Int) (fexp : Int → Int) (x : ℝ) : Id ℝ :=
  sorry -- Implementation would use classical choice

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
  simp [round_DN_to_format, round_UP_to_format]
  sorry -- This requires implementing the rounding functions and proving their properties

end FloatSpec.Core.Round_generic
