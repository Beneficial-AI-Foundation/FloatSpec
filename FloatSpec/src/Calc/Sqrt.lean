/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Helper functions and theorems for computing the rounded square root of a floating-point number
Translated from Coq file: flocq/src/Calc/Sqrt.v
-/

import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Digits
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Float_prop
import FloatSpec.src.Calc.Bracket
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Std.Do.Triple
import Std.Tactic.Do
import FloatSpec.src.SimprocWP

open Real FloatSpec.Calc.Bracket FloatSpec.Core.Defs FloatSpec.Core.Digits FloatSpec.Core.Generic_fmt FloatSpec.Core.Raux
open FloatSpec.Core.Generic_fmt
open Std.Do

namespace FloatSpec.Calc.Sqrt

variable (beta : Int)
variable (fexp : Int → Int)

section MagnitudeBounds

/-- Helper lemma: ⌊a/2⌋ + 1 = (⌊a⌋ + 2) / 2 for any real a.
    This is the floor-based identity needed for Raux.mag (floor+1 definition).
-/
private lemma floor_half_plus_one_eq_floor_add_two_div_two (a : ℝ) :
    ⌊a / 2⌋ + 1 = (⌊a⌋ + 2) / 2 := by
  -- Let f = ⌊a⌋, then f ≤ a < f + 1
  set f := ⌊a⌋ with hf_def
  have h_lb : (f : ℝ) ≤ a := Int.floor_le a
  have h_ub : a < (f : ℝ) + 1 := Int.lt_floor_add_one a
  -- Case split on whether f is even or odd
  rcases Int.even_or_odd f with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- f = 2k (even case): (f + 2) / 2 = k + 1
    have hfdiv : (f + 2) / 2 = k + 1 := by omega
    rw [hfdiv]
    -- Need to show ⌊a/2⌋ + 1 = k + 1, i.e., ⌊a/2⌋ = k
    -- From f ≤ a < f + 1 and f = 2k, we get 2k ≤ a < 2k + 1
    -- So k ≤ a/2 < k + 1/2, hence ⌊a/2⌋ = k
    have hf_eq : (f : ℝ) = 2 * k := by rw [hk]; push_cast; ring
    have h_lb' : (k : ℝ) ≤ a / 2 := by
      have : (2 : ℝ) * k ≤ a := by rw [← hf_eq]; exact h_lb
      linarith
    have h_ub' : a / 2 < (k : ℝ) + 1 := by
      have : a < (2 : ℝ) * k + 1 := by rw [← hf_eq]; linarith
      linarith
    have hfloor : ⌊a / 2⌋ = k := Int.floor_eq_iff.mpr ⟨h_lb', h_ub'⟩
    omega
  · -- f = 2k + 1 (odd case): (f + 2) / 2 = k + 1
    have hfdiv : (f + 2) / 2 = k + 1 := by omega
    rw [hfdiv]
    -- Need to show ⌊a/2⌋ + 1 = k + 1, i.e., ⌊a/2⌋ = k
    -- From f ≤ a < f + 1 and f = 2k + 1, we get 2k + 1 ≤ a < 2k + 2
    -- So k + 1/2 ≤ a/2 < k + 1, hence ⌊a/2⌋ = k
    have hf_eq : (f : ℝ) = 2 * k + 1 := by rw [hk]; push_cast; ring
    have h_lb' : (k : ℝ) ≤ a / 2 := by
      have : (2 : ℝ) * k + 1 ≤ a := by rw [← hf_eq]; exact h_lb
      linarith
    have h_ub' : a / 2 < (k : ℝ) + 1 := by
      have : a < (2 : ℝ) * k + 2 := by
        calc a < (f : ℝ) + 1 := h_ub
          _ = (2 * k + 1) + 1 := by rw [hf_eq]
          _ = 2 * k + 2 := by ring
      linarith
    have hfloor : ⌊a / 2⌋ = k := Int.floor_eq_iff.mpr ⟨h_lb', h_ub'⟩
    omega

/-- Helper lemma: ⌈a/2⌉ = (⌈a⌉ + 1) / 2 for any real a.
    This is a standard identity relating ceiling of half to half of ceiling.
-/
private lemma ceil_half_eq_ceil_add_one_div_two (a : ℝ) :
    ⌈a / 2⌉ = (⌈a⌉ + 1) / 2 := by
  -- Use the characterization of ceiling: ⌈x⌉ is the smallest integer ≥ x
  -- We show both sides equal by proving they satisfy the same defining property
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  -- Let c = ⌈a⌉, then c - 1 < a ≤ c
  set c := ⌈a⌉ with hc_def
  have h_ub : a ≤ c := Int.le_ceil a
  have h_lb : (c : ℝ) - 1 < a := by
    have h := Int.ceil_lt_add_one a
    linarith
  -- We need to show ⌈a/2⌉ = (c + 1) / 2
  -- Case split on whether c is even or odd
  rcases Int.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- c = 2k (even case): (c + 1) / 2 = k
    have hcdiv : (c + 1) / 2 = k := by omega
    rw [hcdiv]
    -- Need to show ⌈a/2⌉ = k, i.e., k - 1 < a/2 ≤ k
    apply Int.ceil_eq_iff.mpr
    constructor
    · -- k - 1 < a/2
      -- From c - 1 < a, we get 2k - 1 < a, so k - 1/2 < a/2, so k - 1 < a/2
      have : (c : ℝ) - 1 < a := h_lb
      rw [hk] at this
      have : (2 : ℝ) * k - 1 < a := by push_cast at this ⊢; linarith
      have : k - (1 : ℝ) / 2 < a / 2 := by linarith
      linarith
    · -- a/2 ≤ k
      -- From a ≤ c = 2k, we get a/2 ≤ k
      have : a ≤ (c : ℝ) := h_ub
      rw [hk] at this
      push_cast at this
      linarith
  · -- c = 2k + 1 (odd case): (c + 1) / 2 = k + 1
    have hcdiv : (c + 1) / 2 = k + 1 := by omega
    rw [hcdiv]
    -- Need to show ⌈a/2⌉ = k + 1, i.e., k < a/2 ≤ k + 1
    apply Int.ceil_eq_iff.mpr
    constructor
    · -- k < a/2
      -- From c - 1 < a and c = 2k + 1, we get 2k < a, so k < a/2
      have : (c : ℝ) - 1 < a := h_lb
      rw [hk] at this
      have h2k_lt : (2 : ℝ) * k < a := by push_cast at this ⊢; linarith
      -- Goal: ↑(k + 1) - 1 < a / 2, i.e., k < a/2
      simp only [Int.cast_add, Int.cast_one]
      linarith
    · -- a/2 ≤ k + 1
      -- From a ≤ c = 2k + 1, we get a ≤ 2k + 1, so a/2 ≤ k + 1/2 < k + 1
      have : a ≤ (c : ℝ) := h_ub
      rw [hk] at this
      have : a ≤ (2 : ℝ) * k + 1 := by push_cast at this ⊢; linarith
      have : a / 2 ≤ k + (1 : ℝ) / 2 := by linarith
      simp only [Int.cast_add, Int.cast_one]
      linarith

/-
 Helper lemma: mag(sqrt x) = (mag x + 1) / 2 for positive x.
 This is the Lean4 equivalent of the Coq `mag_sqrt` lemma.
 Uses Raux.mag (floor+1 definition) which matches Coq semantics.
-/
private lemma mag_sqrt_eq_div2 (x : ℝ) (hx_pos : 0 < x) (hβ : 1 < beta) :
    FloatSpec.Core.Raux.mag beta (Real.sqrt x) =
      (FloatSpec.Core.Raux.mag beta x + 1) / 2 := by
  -- Unfold the floor+1 based mag definition
  unfold FloatSpec.Core.Raux.mag
  -- Establish non-zeroness for both x and sqrt(x)
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hsqrt_ne : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr hx_pos
  -- Simplify the conditionals
  simp only [hx_ne, hsqrt_ne, ite_false]
  -- Simplify absolute values (both positive)
  have habs_sqrt : |Real.sqrt x| = Real.sqrt x := abs_of_pos (Real.sqrt_pos.mpr hx_pos)
  have habs_x : |x| = x := abs_of_pos hx_pos
  rw [habs_sqrt, habs_x]
  -- Use log(sqrt x) = log(x) / 2
  have hlog_sqrt : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt (le_of_lt hx_pos)
  rw [hlog_sqrt]
  -- Now goal is: ⌊(Real.log x / 2) / Real.log β⌋ + 1 = (⌊Real.log x / Real.log β⌋ + 1 + 1) / 2
  -- Rewrite (log x / 2) / log β = (log x / log β) / 2
  have hdiv_assoc : Real.log x / 2 / Real.log (beta : ℝ) = (Real.log x / Real.log (beta : ℝ)) / 2 := by
    field_simp
  rw [hdiv_assoc]
  -- Apply the floor-based helper lemma: ⌊a/2⌋ + 1 = (⌊a⌋ + 2) / 2
  have hfloor := floor_half_plus_one_eq_floor_add_two_div_two (Real.log x / Real.log (beta : ℝ))
  -- The RHS is (⌊log x / log β⌋ + 1 + 1) / 2 = (⌊log x / log β⌋ + 2) / 2
  omega

/-
 Helper lemma: for a positive integer m, Raux.mag beta (m : ℝ) = Zdigits beta m.
 Uses Raux.mag (floor+1 definition) which correctly matches Zdigits bounds.
 Note: Float_prop.mag uses ceiling which does NOT match Zdigits for exact powers of beta.
-/
private lemma mag_eq_Zdigits (m : Int) (hm_pos : 0 < m) (hβ : 1 < beta) :
    FloatSpec.Core.Raux.mag beta (m : ℝ) = Zdigits beta m := by
  -- Get bounds from Zdigits_correct
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hdig := Zdigits_correct beta m hβ hm_ne
  -- Extract the bounds from the wp-style spec
  simp only [wp, PostCond.noThrow, pure, PredTrans.pure] at hdig
  obtain ⟨hlow_int, hupp_int⟩ := hdig
  -- Set d = Zdigits beta m
  set d := Zdigits beta m with hd_def
  -- Since m > 0, we have |m| = m
  have hm_abs : |m| = m := abs_of_pos hm_pos
  -- Rewrite bounds using |m| = m
  rw [hm_abs] at hlow_int hupp_int
  -- Convert (m : ℝ) > 0
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := Int.cast_pos.mpr hm_pos
  -- Get beta positivity
  have hβ_pos : 0 < beta := lt_trans (by norm_num : (0 : Int) < 1) hβ
  have hβ_real_pos : (0 : ℝ) < (beta : ℝ) := Int.cast_pos.mpr hβ_pos
  -- Get d > 0 from Zdigits_gt_0
  have hd_pos : 0 < d := by
    have := Zdigits_gt_0 beta m hβ hm_ne
    simp only [wp, PostCond.noThrow, pure, PredTrans.pure] at this
    exact this
  -- For d > 0, d.natAbs = d and (d-1).natAbs = d - 1
  have hd_nonneg : 0 ≤ d := le_of_lt hd_pos
  have hd_sub_nonneg : 0 ≤ d - 1 := by linarith
  have hd_natAbs : (d.natAbs : Int) = d := Int.natAbs_of_nonneg hd_nonneg
  have hd_sub_natAbs : ((d - 1).natAbs : Int) = d - 1 := Int.natAbs_of_nonneg hd_sub_nonneg
  -- Convert integer power bounds to real zpow bounds
  -- Lower bound: beta ^ (d-1).natAbs ≤ m → (beta : ℝ) ^ (d-1) ≤ (m : ℝ)
  have hlow_real : (beta : ℝ) ^ (d - 1) ≤ (m : ℝ) := by
    have h1 : (beta : ℝ) ^ (d - 1) = (beta : ℝ) ^ ((d - 1).natAbs : ℤ) := by
      rw [hd_sub_natAbs]
    rw [h1, zpow_natCast]
    have h2 : ((beta ^ (d - 1).natAbs : Int) : ℝ) ≤ (m : ℝ) := by
      exact Int.cast_le.mpr hlow_int
    convert h2 using 1
    simp only [Int.cast_pow]
  -- Upper bound: m < beta ^ d.natAbs → (m : ℝ) < (beta : ℝ) ^ d
  have hupp_real : (m : ℝ) < (beta : ℝ) ^ d := by
    have h1 : (beta : ℝ) ^ d = (beta : ℝ) ^ (d.natAbs : ℤ) := by
      rw [hd_natAbs]
    rw [h1, zpow_natCast]
    have h2 : (m : ℝ) < ((beta ^ d.natAbs : Int) : ℝ) := by
      exact Int.cast_lt.mpr hupp_int
    convert h2 using 2
    simp only [Int.cast_pow]
  -- Use mag_unique_pos from Raux: if β^(e-1) ≤ x < β^e then mag β x = e
  -- The bounds from Zdigits_correct exactly match!
  have hmag := FloatSpec.Core.Raux.mag_unique_pos beta (m : ℝ) d
  simp only [wp, PostCond.noThrow, Id.run, bind, pure] at hmag
  exact hmag hβ hm_real_pos hlow_real hupp_real trivial

/-
 Helper lemma: mag(x * β^e) = mag(x) + e for nonzero x.
-/
private lemma mag_mult_bpow_eq (x : ℝ) (e : Int) (hx : x ≠ 0) (hβ : 1 < beta) :
    FloatSpec.Core.Raux.mag beta (x * (beta : ℝ) ^ e) =
    FloatSpec.Core.Raux.mag beta x + e := by
  -- Unfold mag for both sides
  unfold FloatSpec.Core.Raux.mag
  -- Set up positivity for beta
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hbpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbpos e
  have hbpow_ne : (beta : ℝ) ^ e ≠ 0 := ne_of_gt hbpow_pos
  -- The product is nonzero
  have hxmul_ne : x * (beta : ℝ) ^ e ≠ 0 := mul_ne_zero hx hbpow_ne
  -- Simplify conditionals
  simp only [hxmul_ne, hx, ite_false]
  -- Now we need: ⌊log|x * β^e| / log β⌋ + 1 = (⌊log|x| / log β⌋ + 1) + e
  -- i.e., ⌊log|x * β^e| / log β⌋ = ⌊log|x| / log β⌋ + e
  -- Log properties
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
    exact this.mpr hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  -- |x * β^e| = |x| * β^e since β^e > 0
  have habs_prod : |x * (beta : ℝ) ^ e| = |x| * (beta : ℝ) ^ e := by
    rw [abs_mul, abs_of_pos hbpow_pos]
  -- log(|x| * β^e) = log|x| + e * log β (when |x| > 0)
  have hxabs_pos : 0 < |x| := abs_pos.mpr hx
  have hlog_prod : Real.log (|x| * (beta : ℝ) ^ e) = Real.log |x| + (e : ℝ) * Real.log (beta : ℝ) := by
    rw [Real.log_mul (ne_of_gt hxabs_pos) hbpow_ne]
    rw [Real.log_zpow (beta : ℝ) e]
  -- Divide by log β: (log|x| + e * log β) / log β = log|x| / log β + e
  have hdiv : (Real.log |x| + (e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) =
              Real.log |x| / Real.log (beta : ℝ) + (e : ℝ) := by
    field_simp [hlogβ_ne]
  -- Combine: log|x * β^e| / log β = log|x| / log β + e
  have hquot : Real.log |x * (beta : ℝ) ^ e| / Real.log (beta : ℝ) =
               Real.log |x| / Real.log (beta : ℝ) + (e : ℝ) := by
    rw [habs_prod, hlog_prod, hdiv]
  -- Apply floor additive property: ⌊L + e⌋ = ⌊L⌋ + e for integer e
  rw [hquot]
  rw [Int.floor_add_intCast]
  ring

lemma mag_sqrt_F2R (m1 e1 : Int) (Hm1 : 0 < m1) (Hβ : 1 < beta) :
    FloatSpec.Core.Raux.mag beta (Real.sqrt (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)))
      = (Zdigits beta m1 + e1 + 1) / 2 := by
  -- Step 1: F2R is positive since m1 > 0
  have hF2R_pos : 0 < F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) := by
    exact FloatSpec.Core.Float_prop.F2R_gt_0 (beta := beta) (f := FlocqFloat.mk m1 e1) Hβ Hm1
  -- Step 2: Use mag_sqrt_eq_div2
  have h_sqrt_mag := mag_sqrt_eq_div2 beta (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) hF2R_pos Hβ
  rw [h_sqrt_mag]
  -- Step 3: F2R = m1 * β^e1, so mag(F2R) = mag(m1) + e1 using our helper
  have hm1_ne : m1 ≠ 0 := ne_of_gt Hm1
  have hm1_real_ne : (m1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm1_ne
  -- F2R { Fnum := m1, Fexp := e1 } = m1 * β^e1
  have hF2R_eq : F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) = (m1 : ℝ) * (beta : ℝ) ^ e1 := by
    simp only [F2R, FlocqFloat.mk]
  rw [hF2R_eq]
  have h_mag_mult := mag_mult_bpow_eq beta (m1 : ℝ) e1 hm1_real_ne Hβ
  rw [h_mag_mult]
  -- Step 4: Use mag_eq_Zdigits to get mag(m1) = Zdigits m1
  have h_mag_eq := mag_eq_Zdigits beta m1 Hm1 Hβ
  rw [h_mag_eq]

end MagnitudeBounds

section CoreSquareRoot

/-- Core square root function

    Computes integer square root with remainder for location determination.
    This matches the Coq definition {name}`Fsqrt_core`.
-/
def Fsqrt_core (m1 e1 e : Int) : (Int × Location) :=
  let m1' := m1 * beta ^ Int.natAbs (e1 - 2 * e)
  let q := Int.sqrt m1'
  let r := m1' - q * q
  let l := if r = 0 then Location.loc_Exact
           else Location.loc_Inexact (if r ≤ q then Ordering.lt else Ordering.gt)
  (q, l)

/-- Specification: Core square root computation is correct

    The core routine returns (m, l) such that `inbetween_float beta m e (sqrt (F2R f)) l`
    holds, matching the Coq theorem {name}`Fsqrt_core_correct`.
-/
theorem Fsqrt_core_correct (m1 e1 e : Int) (Hm1 : 0 < m1) (He : 2 * e ≤ e1) (Hβ : 1 < beta) :
    let (m, l) := Fsqrt_core beta m1 e1 e
    inbetween_float beta m e (Real.sqrt (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta))) l := by
  -- Unfold Fsqrt_core
  simp only [Fsqrt_core]
  -- Set up key values
  set m1' := m1 * beta ^ Int.natAbs (e1 - 2 * e) with hm1'_def
  set q := Int.sqrt m1' with hq_def
  set r := m1' - q * q with hr_def
  -- Establish positivity facts
  have hβ_pos : 0 < beta := lt_trans (by norm_num : (0 : Int) < 1) Hβ
  have hβR_pos : (0 : ℝ) < (beta : ℝ) := Int.cast_pos.mpr hβ_pos
  have hβR_one : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast Hβ
  have hbpow_pos : 0 < beta ^ Int.natAbs (e1 - 2 * e) := by positivity
  have hm1'_pos : 0 < m1' := by
    rw [hm1'_def]
    exact mul_pos Hm1 hbpow_pos
  -- Integer square root bounds
  have hm1'_nat : m1'.toNat = m1'.natAbs := by
    have hle : (0 : Int) ≤ m1' := Int.le_of_lt hm1'_pos
    have h1 : (m1'.toNat : Int) = m1' := Int.toNat_of_nonneg hle
    have h2 : (m1'.natAbs : Int) = m1' := Int.natAbs_of_nonneg hle
    exact Nat.cast_inj.mp (h1.trans h2.symm)
  have hq_eq : q = (m1'.toNat.sqrt : Int) := by
    rw [hq_def, Int.sqrt, hm1'_nat]
  -- q² ≤ m1'
  have hq_sq_le : q * q ≤ m1' := by
    rw [hq_eq]
    have h := Nat.sqrt_le m1'.toNat
    have hcast : ((m1'.toNat.sqrt * m1'.toNat.sqrt : Nat) : Int) ≤ (m1'.toNat : Int) := by
      exact_mod_cast h
    simp only [Nat.cast_mul] at hcast
    rw [Int.toNat_of_nonneg (le_of_lt hm1'_pos)] at hcast
    convert hcast using 1
  -- m1' < (q + 1)²
  have hm1'_lt_succ : m1' < (q + 1) * (q + 1) := by
    rw [hq_eq]
    have h := Nat.lt_succ_sqrt m1'.toNat
    have hcast : (m1'.toNat : Int) < (((m1'.toNat.sqrt + 1) * (m1'.toNat.sqrt + 1)) : Nat) := by
      exact_mod_cast h
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast
    rw [Int.toNat_of_nonneg (le_of_lt hm1'_pos)] at hcast
    convert hcast using 1
  -- q ≥ 0 since it's a sqrt
  have hq_nonneg : 0 ≤ q := Int.sqrt_nonneg m1'
  -- r = m1' - q² is the remainder, and 0 ≤ r
  have hr_nonneg : 0 ≤ r := by
    rw [hr_def]
    exact Int.sub_nonneg_of_le hq_sq_le
  -- r < 2*q + 1 (from m1' < (q+1)²)
  have hr_bound : r < 2 * q + 1 := by
    rw [hr_def]
    have h : m1' < q * q + 2 * q + 1 := by ring_nf; ring_nf at hm1'_lt_succ; exact hm1'_lt_succ
    linarith
  -- Key relationship: F2R(m1, e1) = m1' * beta^(2*e) when e1 ≥ 2*e
  have he_diff_nonneg : 0 ≤ e1 - 2 * e := by linarith
  have hnatabs_eq : Int.natAbs (e1 - 2 * e) = (e1 - 2 * e).toNat := by
    have h1 : ((e1 - 2 * e).natAbs : Int) = e1 - 2 * e := Int.natAbs_of_nonneg he_diff_nonneg
    have h2 : ((e1 - 2 * e).toNat : Int) = e1 - 2 * e := Int.toNat_of_nonneg he_diff_nonneg
    exact Nat.cast_inj.mp (h1.trans h2.symm)
  have hF2R_eq : F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) =
                 (m1' : ℝ) * (beta : ℝ) ^ (2 * e) := by
    simp only [F2R, FlocqFloat.mk]
    rw [hm1'_def]
    have hexp_split : e1 = (e1 - 2 * e) + 2 * e := by ring
    conv_lhs => rw [hexp_split]
    rw [zpow_add₀ (ne_of_gt hβR_pos)]
    have hnat_pow : (beta : ℝ) ^ (e1 - 2 * e) = (beta : ℝ) ^ Int.natAbs (e1 - 2 * e) := by
      rw [hnatabs_eq]
      -- Goal: (beta : ℝ) ^ (e1 - 2 * e) = (beta : ℝ) ^ (e1 - 2 * e).toNat
      -- Use Int.toNat_of_nonneg.symm to rewrite (e1 - 2 * e) as ↑((e1 - 2 * e).toNat)
      -- Then zpow_natCast.symm: a ^ n = a ^ (↑n : ℤ)
      conv_lhs => rw [← Int.toNat_of_nonneg he_diff_nonneg]
      exact (zpow_natCast (beta : ℝ) (e1 - 2 * e).toNat).symm
    rw [hnat_pow]
    push_cast
    ring
  -- sqrt(F2R) = sqrt(m1') * beta^e
  have hsqrt_F2R : Real.sqrt (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) =
                   Real.sqrt (m1' : ℝ) * (beta : ℝ) ^ e := by
    rw [hF2R_eq]
    have hm1'R_nonneg : (0 : ℝ) ≤ (m1' : ℝ) := by exact_mod_cast le_of_lt hm1'_pos
    have hbpow2e_nonneg : (0 : ℝ) ≤ (beta : ℝ) ^ (2 * e) := zpow_nonneg (le_of_lt hβR_pos) _
    rw [Real.sqrt_mul hm1'R_nonneg]
    congr 1
    rw [show (2 : Int) * e = e + e by ring, zpow_add₀ (ne_of_gt hβR_pos)]
    rw [Real.sqrt_mul (zpow_nonneg (le_of_lt hβR_pos) e) ((beta : ℝ) ^ e)]
    rw [Real.mul_self_sqrt (zpow_nonneg (le_of_lt hβR_pos) e)]
  -- F2R(q, e) = q * beta^e and F2R(q+1, e) = (q+1) * beta^e
  have hF2R_q : F2R (FlocqFloat.mk q e : FlocqFloat beta) = (q : ℝ) * (beta : ℝ) ^ e := by
    simp only [F2R, FlocqFloat.mk]
  have hF2R_q1 : F2R (FlocqFloat.mk (q + 1) e : FlocqFloat beta) = ((q : ℝ) + 1) * (beta : ℝ) ^ e := by
    simp only [F2R, FlocqFloat.mk, Int.cast_add, Int.cast_one]
  -- Real sqrt bounds: q ≤ sqrt(m1') < q + 1
  have hqR_nonneg : (0 : ℝ) ≤ (q : ℝ) := Int.cast_nonneg hq_nonneg
  have hsqrt_lb : (q : ℝ) ≤ Real.sqrt (m1' : ℝ) := by
    rw [← Real.sqrt_sq hqR_nonneg]
    apply Real.sqrt_le_sqrt
    have : (q * q : Int) ≤ m1' := hq_sq_le
    have hcast : ((q * q : Int) : ℝ) ≤ (m1' : ℝ) := Int.cast_le.mpr this
    simp only [Int.cast_mul] at hcast
    convert hcast using 1
    ring
  have hsqrt_ub : Real.sqrt (m1' : ℝ) < (q : ℝ) + 1 := by
    have hq1_pos : (0 : ℝ) < (q : ℝ) + 1 := by linarith
    rw [← Real.sqrt_sq (le_of_lt hq1_pos)]
    apply Real.sqrt_lt_sqrt
    · exact_mod_cast le_of_lt hm1'_pos
    · have : m1' < (q + 1) * (q + 1) := hm1'_lt_succ
      have hcast : (m1' : ℝ) < (((q + 1) * (q + 1) : Int) : ℝ) := Int.cast_lt.mpr this
      simp only [Int.cast_mul, Int.cast_add, Int.cast_one] at hcast
      convert hcast using 1
      ring
  -- Scale by beta^e to get bounds on sqrt(F2R)
  have hbpow_e_pos : (0 : ℝ) < (beta : ℝ) ^ e := zpow_pos hβR_pos e
  have hsqrt_F2R_lb : F2R (FlocqFloat.mk q e : FlocqFloat beta) ≤
                      Real.sqrt (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) := by
    rw [hsqrt_F2R, hF2R_q]
    exact mul_le_mul_of_nonneg_right hsqrt_lb (le_of_lt hbpow_e_pos)
  have hsqrt_F2R_ub : Real.sqrt (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) <
                      F2R (FlocqFloat.mk (q + 1) e : FlocqFloat beta) := by
    rw [hsqrt_F2R, hF2R_q1]
    exact mul_lt_mul_of_pos_right hsqrt_ub hbpow_e_pos
  -- Now prove the inbetween relation by case split on r = 0
  unfold inbetween_float
  split_ifs with hr_zero
  · -- Case: r = 0, so sqrt is exact
    apply inbetween.inbetween_Exact
    rw [hsqrt_F2R, hF2R_q]
    congr 1
    -- r = 0 means m1' = q², so sqrt(m1') = q
    have hm1'_eq_qq : m1' = q * q := by
      rw [hr_def] at hr_zero
      linarith
    have hm1'R_eq : (m1' : ℝ) = (q : ℝ) * (q : ℝ) := by
      rw [hm1'_eq_qq]
      push_cast
      ring
    rw [hm1'R_eq, Real.sqrt_mul_self hqR_nonneg]
  · -- Case: r ≠ 0, so sqrt is inexact
    have hr_pos : 0 < r := by
      have : r ≠ 0 := hr_zero
      omega
    -- The location depends on r ≤ q vs r > q
    -- We need: d < sqrt(F2R) < u where d = F2R(q,e), u = F2R(q+1,e)
    have hstrict_lb : F2R (FlocqFloat.mk q e : FlocqFloat beta) <
                      Real.sqrt (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) := by
      rw [hsqrt_F2R, hF2R_q]
      apply mul_lt_mul_of_pos_right _ hbpow_e_pos
      rw [← Real.sqrt_sq hqR_nonneg]
      apply Real.sqrt_lt_sqrt
      · exact sq_nonneg (q : ℝ)
      · have : q * q < m1' := by
          have hne : m1' ≠ q * q := by
            intro heq
            have : r = 0 := by rw [hr_def, heq]; ring
            exact hr_zero this
          omega
        have hcast : ((q * q : Int) : ℝ) < (m1' : ℝ) := Int.cast_lt.mpr this
        simp only [Int.cast_mul] at hcast
        convert hcast using 1
        ring
    -- Apply inbetween_Inexact
    apply inbetween.inbetween_Inexact
    · exact ⟨hstrict_lb, hsqrt_F2R_ub⟩
    · -- Prove the compare relation
      -- Midpoint is (F2R(q,e) + F2R(q+1,e)) / 2 = (q + 1/2) * beta^e
      -- Need to compare sqrt(m1') with q + 1/2, equivalently m1' with (q + 1/2)²
      -- (q + 1/2)² = q² + q + 1/4, so 2*m1' vs 2*q² + 2*q + 1/2, i.e., 4*m1' vs 4*q² + 4*q + 1
      -- 4*(m1' - q²) vs 4*q + 1, i.e., 4*r vs 4*q + 1
      -- Location is lt if 4*r < 4*q + 1, i.e., r ≤ q
      -- Location is gt if 4*r > 4*q + 1, i.e., r > q (since both integers)
      rw [hsqrt_F2R, hF2R_q, hF2R_q1]
      -- Midpoint calculation
      have hmid : ((q : ℝ) * (beta : ℝ) ^ e + ((q : ℝ) + 1) * (beta : ℝ) ^ e) / 2 =
                  ((q : ℝ) + 1 / 2) * (beta : ℝ) ^ e := by ring
      rw [hmid]
      -- Compare sqrt(m1') * beta^e with (q + 1/2) * beta^e
      -- This is equivalent to comparing sqrt(m1') with q + 1/2
      have hcmp_scale : Bracket.compare (Real.sqrt (m1' : ℝ) * (beta : ℝ) ^ e)
                                (((q : ℝ) + 1 / 2) * (beta : ℝ) ^ e) =
                        Bracket.compare (Real.sqrt (m1' : ℝ)) ((q : ℝ) + 1 / 2) := by
        -- Prove by unfolding Bracket.compare and using that c > 0 preserves order
        unfold Bracket.compare
        -- Multiplying by positive preserves < and >
        have h_lt_iff : Real.sqrt (m1' : ℝ) * (beta : ℝ) ^ e < ((q : ℝ) + 1 / 2) * (beta : ℝ) ^ e ↔
                        Real.sqrt (m1' : ℝ) < (q : ℝ) + 1 / 2 := by
          constructor
          · intro h
            exact (mul_lt_mul_iff_of_pos_right hbpow_e_pos).mp h
          · intro h
            exact mul_lt_mul_of_pos_right h hbpow_e_pos
        have h_gt_iff : Real.sqrt (m1' : ℝ) * (beta : ℝ) ^ e > ((q : ℝ) + 1 / 2) * (beta : ℝ) ^ e ↔
                        Real.sqrt (m1' : ℝ) > (q : ℝ) + 1 / 2 := by
          constructor
          · intro h
            exact (mul_lt_mul_iff_of_pos_right hbpow_e_pos).mp h
          · intro h
            exact mul_lt_mul_of_pos_right h hbpow_e_pos
        simp only [h_lt_iff, h_gt_iff]
      rw [hcmp_scale]
      -- Now compare sqrt(m1') with q + 1/2
      -- sqrt(m1') < q + 1/2 iff m1' < (q + 1/2)² = q² + q + 1/4 iff m1' ≤ q² + q (integer)
      -- iff r ≤ q
      -- In this case (case pos), we have h✝ : r ≤ q, so goal is Ordering.lt
      rename_i hrq  -- rename h✝ to hrq for clarity
      unfold Bracket.compare
      have hsqrt_lt_mid : Real.sqrt (m1' : ℝ) < (q : ℝ) + 1 / 2 := by
        have hmid_sq : ((q : ℝ) + 1 / 2) ^ 2 = (q : ℝ) ^ 2 + (q : ℝ) + 1 / 4 := by ring
        have hmid_pos : (0 : ℝ) < (q : ℝ) + 1 / 2 := by linarith
        rw [← Real.sqrt_sq (le_of_lt hmid_pos)]
        apply Real.sqrt_lt_sqrt
        · exact_mod_cast le_of_lt hm1'_pos
        · rw [sq]
          have hm1'_le : m1' ≤ q * q + q := by
            rw [hr_def] at hrq
            linarith
          have hcast : (m1' : ℝ) ≤ ((q * q + q : Int) : ℝ) := Int.cast_le.mpr hm1'_le
          calc (m1' : ℝ) ≤ (q : ℝ) * (q : ℝ) + (q : ℝ) := by
                 simp only [Int.cast_add, Int.cast_mul] at hcast; exact hcast
            _ < (q : ℝ) * (q : ℝ) + (q : ℝ) + 1 / 4 := by linarith
            _ = ((q : ℝ) + 1 / 2) * ((q : ℝ) + 1 / 2) := by ring
      simp only [hsqrt_lt_mid, ↓reduceIte]
  · -- Case: r ≠ 0 and r > q (case neg), so sqrt is inexact with Location.loc_Inexact Ordering.gt
    have hr_pos : 0 < r := by
      have : r ≠ 0 := hr_zero
      omega
    rename_i hrq_neg  -- h✝ : ¬r ≤ q
    have hr_gt_q : q < r := by omega
    -- We need: d < sqrt(F2R) < u where d = F2R(q,e), u = F2R(q+1,e)
    have hstrict_lb : F2R (FlocqFloat.mk q e : FlocqFloat beta) <
                      Real.sqrt (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)) := by
      rw [hsqrt_F2R, hF2R_q]
      apply mul_lt_mul_of_pos_right _ hbpow_e_pos
      rw [← Real.sqrt_sq hqR_nonneg]
      apply Real.sqrt_lt_sqrt
      · exact sq_nonneg (q : ℝ)
      · have : q * q < m1' := by
          have hne : m1' ≠ q * q := by
            intro heq
            have : r = 0 := by rw [hr_def, heq]; ring
            exact hr_zero this
          omega
        have hcast : ((q * q : Int) : ℝ) < (m1' : ℝ) := Int.cast_lt.mpr this
        simp only [Int.cast_mul] at hcast
        convert hcast using 1
        ring
    -- Apply inbetween_Inexact
    apply inbetween.inbetween_Inexact
    · exact ⟨hstrict_lb, hsqrt_F2R_ub⟩
    · -- Prove the compare relation: Bracket.compare ... = Ordering.gt
      rw [hsqrt_F2R, hF2R_q, hF2R_q1]
      have hmid : ((q : ℝ) * (beta : ℝ) ^ e + ((q : ℝ) + 1) * (beta : ℝ) ^ e) / 2 =
                  ((q : ℝ) + 1 / 2) * (beta : ℝ) ^ e := by ring
      rw [hmid]
      have hcmp_scale : Bracket.compare (Real.sqrt (m1' : ℝ) * (beta : ℝ) ^ e)
                                (((q : ℝ) + 1 / 2) * (beta : ℝ) ^ e) =
                        Bracket.compare (Real.sqrt (m1' : ℝ)) ((q : ℝ) + 1 / 2) := by
        unfold Bracket.compare
        have h_lt_iff : Real.sqrt (m1' : ℝ) * (beta : ℝ) ^ e < ((q : ℝ) + 1 / 2) * (beta : ℝ) ^ e ↔
                        Real.sqrt (m1' : ℝ) < (q : ℝ) + 1 / 2 := by
          constructor
          · intro h
            exact (mul_lt_mul_iff_of_pos_right hbpow_e_pos).mp h
          · intro h
            exact mul_lt_mul_of_pos_right h hbpow_e_pos
        have h_gt_iff : Real.sqrt (m1' : ℝ) * (beta : ℝ) ^ e > ((q : ℝ) + 1 / 2) * (beta : ℝ) ^ e ↔
                        Real.sqrt (m1' : ℝ) > (q : ℝ) + 1 / 2 := by
          constructor
          · intro h
            exact (mul_lt_mul_iff_of_pos_right hbpow_e_pos).mp h
          · intro h
            exact mul_lt_mul_of_pos_right h hbpow_e_pos
        simp only [h_lt_iff, h_gt_iff]
      rw [hcmp_scale]
      -- Now prove Bracket.compare (sqrt m1') (q + 1/2) = Ordering.gt
      unfold Bracket.compare
      have hsqrt_gt_mid : (q : ℝ) + 1 / 2 < Real.sqrt (m1' : ℝ) := by
        have hmid_pos : (0 : ℝ) < (q : ℝ) + 1 / 2 := by linarith
        rw [← Real.sqrt_sq (le_of_lt hmid_pos)]
        apply Real.sqrt_lt_sqrt
        · exact sq_nonneg _
        · rw [sq]
          have hm1'_gt : q * q + q < m1' := by
            rw [hr_def] at hr_gt_q
            linarith
          -- For integers, a < b implies a + 1 ≤ b
          have hm1'_ge : q * q + q + 1 ≤ m1' := by omega
          have hcast : ((q * q + q + 1 : Int) : ℝ) ≤ (m1' : ℝ) := Int.cast_le.mpr hm1'_ge
          calc ((q : ℝ) + 1 / 2) * ((q : ℝ) + 1 / 2)
              = (q : ℝ) * (q : ℝ) + (q : ℝ) + 1 / 4 := by ring
            _ < (q : ℝ) * (q : ℝ) + (q : ℝ) + 1 := by linarith
            _ = ((q * q + q + 1 : Int) : ℝ) := by push_cast; ring
            _ ≤ (m1' : ℝ) := hcast
      have hnotlt : ¬ Real.sqrt (m1' : ℝ) < (q : ℝ) + 1 / 2 := not_lt.mpr (le_of_lt hsqrt_gt_mid)
      simp only [hnotlt, ↓reduceIte, hsqrt_gt_mid]

end CoreSquareRoot

section MainSquareRoot

/-- Main square root function

    Computes the square root with automatic exponent selection.
    This matches the Coq definition {name}`Fsqrt`.
-/
def Fsqrt (x : FlocqFloat beta) : (Int × Int × Location) :=
  let m1 := x.Fnum
  let e1 := x.Fexp
  let d := Zdigits beta m1
  let e' := d + e1 + 1
  let e := min (fexp (e' / 2)) (e1 / 2)
  let (m, l) := Fsqrt_core beta m1 e1 e
  (m, e, l)

/-- Specification: Square root computation is correct

    The result satisfies `e ≤ cexp beta fexp (sqrt (F2R x))` and the
    inbetween relation. This matches the Coq theorem {name}`Fsqrt_correct`.
-/
theorem Fsqrt_correct (x : FlocqFloat beta) (Hx : 0 < F2R x) (Hβ : 1 < beta)
    [Hfexp : Valid_exp beta fexp] :
    let (m, e, l) := Fsqrt beta fexp x
    e ≤ cexp beta fexp (Real.sqrt (F2R x)) ∧
    inbetween_float beta m e (Real.sqrt (F2R x)) l := by
  -- Extract mantissa and exponent from x
  set m1 := x.Fnum with hm1_def
  set e1 := x.Fexp with he1_def
  -- Step 1: Get Hm1 : 0 < m1 from Hx : 0 < F2R x
  have Hm1 : 0 < m1 := FloatSpec.Core.Float_prop.gt_0_F2R beta x Hβ Hx
  -- Unfold Fsqrt and set up the key values
  simp only [Fsqrt]
  set d := Zdigits beta m1 with hd_def
  set e' := d + e1 + 1 with he'_def
  set e := min (fexp (e' / 2)) (e1 / 2) with he_def
  -- Step 2: Prove He : 2 * e ≤ e1
  have He : 2 * e ≤ e1 := by
    -- e ≤ e1 / 2 by min_le_right
    have h_le_half : e ≤ e1 / 2 := min_le_right (fexp (e' / 2)) (e1 / 2)
    -- 2 * (e1 / 2) ≤ e1 for integer division
    have h_div2 : 2 * (e1 / 2) ≤ e1 := Int.mul_ediv_self_le (by norm_num : (2 : Int) ≠ 0)
    -- Combine: 2 * e ≤ 2 * (e1 / 2) ≤ e1
    calc 2 * e ≤ 2 * (e1 / 2) := Int.mul_le_mul_of_nonneg_left h_le_half (by norm_num)
      _ ≤ e1 := h_div2
  -- Step 3: Apply Fsqrt_core_correct for the inbetween relation
  have hcore := Fsqrt_core_correct beta m1 e1 e Hm1 He Hβ
  -- Let m_out and l_out be the components of Fsqrt_core result
  set result := Fsqrt_core beta m1 e1 e with hresult_def
  set m_out := result.1 with hm_out_def
  set l_out := result.2 with hl_out_def
  -- The goal after simp becomes about m_out, e, l_out
  simp only [hresult_def.symm, hm_out_def.symm, hl_out_def.symm] at hcore ⊢
  constructor
  · -- Step 4: Prove e ≤ cexp beta fexp (sqrt (F2R x))
    -- e ≤ fexp (e' / 2) by min_le_left
    have h_le_fexp : e ≤ fexp (e' / 2) := min_le_left (fexp (e' / 2)) (e1 / 2)
    -- cexp beta fexp (sqrt (F2R x)) = fexp (mag beta (sqrt (F2R x)))
    unfold cexp
    -- Rewrite x to FlocqFloat.mk m1 e1 in the goal
    have hx_eq : x = FlocqFloat.mk m1 e1 := by
      cases x
      simp only [hm1_def, he1_def]
    rw [hx_eq]
    -- mag beta (sqrt (F2R (FlocqFloat.mk m1 e1))) = (Zdigits beta m1 + e1 + 1) / 2 by mag_sqrt_F2R
    have hmag := mag_sqrt_F2R beta m1 e1 Hm1 Hβ
    -- (Zdigits beta m1 + e1 + 1) / 2 = e' / 2
    have he'_eq : (Zdigits beta m1 + e1 + 1) / 2 = e' / 2 := by
      simp only [he'_def, hd_def]
    rw [he'_eq] at hmag
    rw [hmag]
    exact h_le_fexp
  · -- The inbetween relation follows from Fsqrt_core_correct
    -- Need to show the float representations match
    have hx_eq : x = FlocqFloat.mk m1 e1 := by
      cases x
      simp only [hm1_def, he1_def]
    rw [hx_eq]
    exact hcore

end MainSquareRoot

end FloatSpec.Calc.Sqrt
