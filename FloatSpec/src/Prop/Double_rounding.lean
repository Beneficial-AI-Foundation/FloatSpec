import FloatSpec.src.Core
import FloatSpec.src.Core.FTZ
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import Mathlib.Data.Real.Basic

open Std.Do

-- Double rounding properties
-- Translated from Coq file: flocq/src/Prop/Double_rounding.v

variable (beta : Int) [ValidRadix beta]

/-! Midpoint helpers, corresponding to Coq's `midp` and `midp'`. -/

noncomputable def round_round_eq (fexp1 fexp2 : Int → Int)
    (choice1 choice2 : Int → Bool) (x : ℝ) : Prop :=
  FloatSpec.Core.Generic_fmt.roundR beta fexp1
      (FloatSpec.Core.Generic_fmt.Znearest choice1)
      (FloatSpec.Core.Generic_fmt.roundR beta fexp2
        (FloatSpec.Core.Generic_fmt.Znearest choice2) x)
    =
    FloatSpec.Core.Generic_fmt.roundR beta fexp1
      (FloatSpec.Core.Generic_fmt.Znearest choice1) x

noncomputable def midp (fexp : Int → Int)
    (x : ℝ) : ℝ :=
  FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x
    + (1 / 2) * ulp beta fexp x

noncomputable def midp' (fexp : Int → Int)
    (x : ℝ) : ℝ :=
  FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x
    - (1 / 2) * ulp beta fexp x

/-- Coq: `round_round_lt_mid_same_place`. -/
theorem round_round_lt_mid_same_place (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    fexp2 (FloatSpec.Core.Raux.mag beta x) =
      fexp1 (FloatSpec.Core.Raux.mag beta x) →
    x < midp beta fexp1 x →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  classical
  intro hx_pos hfexp hx_mid
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  set e : Int := fexp1 (FloatSpec.Core.Raux.mag beta x) with he
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 x with hsm
  set n : Int := FloatSpec.Core.Generic_fmt.rnd_floor sm with hn
  set xdn : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_floor x with hxdn
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR e
  have hcexp1 : FloatSpec.Core.Generic_fmt.cexp beta fexp1 x = e := by
    simpa [FloatSpec.Core.Generic_fmt.cexp, e, he]
  have hcexp2 : FloatSpec.Core.Generic_fmt.cexp beta fexp2 x = e := by
    simpa [FloatSpec.Core.Generic_fmt.cexp, e, he, hfexp]
  have hsm_def : sm = x * (beta : ℝ) ^ (-e) := by
    simpa [FloatSpec.Core.Generic_fmt.scaled_mantissa, hcexp1] using hsm
  have hscaled : sm * (beta : ℝ) ^ e = x := by
    have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
      (beta := beta) (fexp := fexp1) (x := x)
    simpa [wp, PostCond.noThrow, Id.run, pure, sm, hsm, e, hcexp1]
      using h hβ
  have hxdn_eval : xdn = ((n : ℝ) * (beta : ℝ) ^ e) := by
    simpa [xdn, hxdn, FloatSpec.Core.Generic_fmt.roundR, sm, hsm,
      n, hn, e, hcexp1]
  have hfloor_le : (n : ℝ) ≤ sm := by
    simpa [n, hn, FloatSpec.Core.Generic_fmt.rnd_floor, FloatSpec.Core.Raux.Zfloor]
      using Int.floor_le sm
  have hnonneg : 0 ≤ sm - (n : ℝ) := sub_nonneg.mpr hfloor_le
  have hxdn_le_x : xdn ≤ x := by
    have hmul := mul_le_mul_of_nonneg_right hfloor_le (le_of_lt hpow_pos)
    simpa [hxdn_eval, hscaled] using hmul
  have hdiff_mid : x - xdn < (1 / 2) * ulp beta fexp1 x := by
    have hx_mid' : x < (1 / 2) * ulp beta fexp1 x + xdn := by
      simpa [midp, xdn, hxdn, add_comm] using hx_mid
    simpa [sub_lt_iff_lt_add] using hx_mid'
  have hulp : ulp beta fexp1 x = (beta : ℝ) ^ e := by
    have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp1)
      (x := x) (hx := hx_ne)) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure, e, hcexp1] using h
  have hscaled_diff :
      (sm - (n : ℝ)) * (beta : ℝ) ^ e = x - xdn := by
    rw [sub_mul, hscaled, hxdn_eval]
  have hmul_lt : (sm - (n : ℝ)) * (beta : ℝ) ^ e < (1 / 2) * (beta : ℝ) ^ e := by
    simpa [hscaled_diff, hulp] using hdiff_mid
  have hdist_floor : |sm - (n : ℝ)| < (1 / 2 : ℝ) := by
    have hlt : sm - (n : ℝ) < (1 / 2 : ℝ) := by
      nlinarith [hpow_pos, hmul_lt]
    simpa [abs_of_nonneg hnonneg] using hlt
  have hsm2 : FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 x = sm := by
    simp [FloatSpec.Core.Generic_fmt.scaled_mantissa, hcexp2, hsm_def]
  have hZ1 :
      FloatSpec.Core.Generic_fmt.Znearest choice1 sm = n := by
    have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice1 sm n) hdist_floor
    simpa [wp,
      PostCond.noThrow, Id.run, pure] using h
  have hZ2 :
      FloatSpec.Core.Generic_fmt.Znearest choice2
          (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 x) = n := by
    simpa [hsm2] using
      (by
        have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice2 sm n) hdist_floor
        simpa [wp,
          PostCond.noThrow, Id.run, pure] using h)
  have hinner :
      FloatSpec.Core.Generic_fmt.roundR beta fexp2
          (FloatSpec.Core.Generic_fmt.Znearest choice2) x = xdn := by
    calc
      FloatSpec.Core.Generic_fmt.roundR beta fexp2
          (FloatSpec.Core.Generic_fmt.Znearest choice2) x
          = ((FloatSpec.Core.Generic_fmt.Znearest choice2
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 x) : ℤ) : ℝ) *
              (beta : ℝ) ^ e := by
                simp [FloatSpec.Core.Generic_fmt.roundR, hcexp2]
      _ = (n : ℝ) * (beta : ℝ) ^ e := by rw [hZ2]
      _ = xdn := hxdn_eval.symm
  have hright :
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          (FloatSpec.Core.Generic_fmt.Znearest choice1) x = xdn := by
    calc
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          (FloatSpec.Core.Generic_fmt.Znearest choice1) x
          = ((FloatSpec.Core.Generic_fmt.Znearest choice1 sm : ℤ) : ℝ) *
              (beta : ℝ) ^ e := by
                simp [FloatSpec.Core.Generic_fmt.roundR, hcexp1, sm, hsm]
      _ = (n : ℝ) * (beta : ℝ) ^ e := by rw [hZ1]
      _ = xdn := hxdn_eval.symm
  have hxdn_fmt :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 xdn := by
    simpa [xdn, hxdn] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := beta) (fexp := fexp1)
        (rnd := FloatSpec.Core.Generic_fmt.rnd_floor) (x := x) hβ
  have hleft_fix :
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          (FloatSpec.Core.Generic_fmt.Znearest choice1) xdn = xdn :=
    FloatSpec.Core.Generic_fmt.roundR_generic
      (beta := beta) (fexp := fexp1)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest choice1)
      (x := xdn) hβ hxdn_fmt
  simpa [round_round_eq, hinner, hright, hleft_fix]

/-- Coq: `round_round_gt_mid_same_place`. -/
theorem round_round_gt_mid_same_place (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    fexp2 (FloatSpec.Core.Raux.mag beta x) =
      fexp1 (FloatSpec.Core.Raux.mag beta x) →
    midp' beta fexp1 x < x →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  classical
  intro hx_pos hfexp hx_mid
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  set e : Int := fexp1 (FloatSpec.Core.Raux.mag beta x) with he
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 x with hsm
  set n : Int := FloatSpec.Core.Generic_fmt.rnd_ceil sm with hn
  set xup : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_ceil x with hxup
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR e
  have hcexp1 : FloatSpec.Core.Generic_fmt.cexp beta fexp1 x = e := by
    simpa [FloatSpec.Core.Generic_fmt.cexp, e, he]
  have hcexp2 : FloatSpec.Core.Generic_fmt.cexp beta fexp2 x = e := by
    simpa [FloatSpec.Core.Generic_fmt.cexp, e, he, hfexp]
  have hsm_def : sm = x * (beta : ℝ) ^ (-e) := by
    simpa [FloatSpec.Core.Generic_fmt.scaled_mantissa, hcexp1] using hsm
  have hscaled : sm * (beta : ℝ) ^ e = x := by
    have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
      (beta := beta) (fexp := fexp1) (x := x)
    simpa [wp, PostCond.noThrow, Id.run, pure, sm, hsm, e, hcexp1]
      using h hβ
  have hxup_eval : xup = ((n : ℝ) * (beta : ℝ) ^ e) := by
    simpa [xup, hxup, FloatSpec.Core.Generic_fmt.roundR, sm, hsm,
      n, hn, e, hcexp1]
  have hceil_ge : sm ≤ (n : ℝ) := by
    simpa [n, hn, FloatSpec.Core.Generic_fmt.rnd_ceil, FloatSpec.Core.Raux.Zceil]
      using Int.le_ceil sm
  have hnonneg : 0 ≤ (n : ℝ) - sm := sub_nonneg.mpr hceil_ge
  have hx_le_xup : x ≤ xup := by
    have hmul := mul_le_mul_of_nonneg_right hceil_ge (le_of_lt hpow_pos)
    simpa [hxup_eval, hscaled] using hmul
  have hdiff_mid : xup - x < (1 / 2) * ulp beta fexp1 x := by
    have hx_mid' : xup - (1 / 2) * ulp beta fexp1 x < x := by
      simpa [midp', xup, hxup] using hx_mid
    linarith
  have hulp : ulp beta fexp1 x = (beta : ℝ) ^ e := by
    have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp1)
      (x := x) (hx := hx_ne)) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure, e, hcexp1] using h
  have hscaled_diff :
      ((n : ℝ) - sm) * (beta : ℝ) ^ e = xup - x := by
    rw [sub_mul, hxup_eval, hscaled]
  have hmul_lt : ((n : ℝ) - sm) * (beta : ℝ) ^ e < (1 / 2) * (beta : ℝ) ^ e := by
    simpa [hscaled_diff, hulp] using hdiff_mid
  have hdist_ceil : |sm - (n : ℝ)| < (1 / 2 : ℝ) := by
    have hlt : (n : ℝ) - sm < (1 / 2 : ℝ) := by
      nlinarith [hpow_pos, hmul_lt]
    have hdist : |(n : ℝ) - sm| < (1 / 2 : ℝ) := by
      simpa [abs_of_nonneg hnonneg] using hlt
    simpa [abs_sub_comm] using hdist
  have hsm2 : FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 x = sm := by
    simp [FloatSpec.Core.Generic_fmt.scaled_mantissa, hcexp2, hsm_def]
  have hZ1 :
      FloatSpec.Core.Generic_fmt.Znearest choice1 sm = n := by
    have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice1 sm n) hdist_ceil
    simpa [wp,
      PostCond.noThrow, Id.run, pure] using h
  have hZ2 :
      FloatSpec.Core.Generic_fmt.Znearest choice2
          (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 x) = n := by
    simpa [hsm2] using
      (by
        have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice2 sm n) hdist_ceil
        simpa [wp,
          PostCond.noThrow, Id.run, pure] using h)
  have hinner :
      FloatSpec.Core.Generic_fmt.roundR beta fexp2
          (FloatSpec.Core.Generic_fmt.Znearest choice2) x = xup := by
    calc
      FloatSpec.Core.Generic_fmt.roundR beta fexp2
          (FloatSpec.Core.Generic_fmt.Znearest choice2) x
          = ((FloatSpec.Core.Generic_fmt.Znearest choice2
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 x) : ℤ) : ℝ) *
              (beta : ℝ) ^ e := by
                simp [FloatSpec.Core.Generic_fmt.roundR, hcexp2]
      _ = (n : ℝ) * (beta : ℝ) ^ e := by rw [hZ2]
      _ = xup := hxup_eval.symm
  have hright :
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          (FloatSpec.Core.Generic_fmt.Znearest choice1) x = xup := by
    calc
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          (FloatSpec.Core.Generic_fmt.Znearest choice1) x
          = ((FloatSpec.Core.Generic_fmt.Znearest choice1 sm : ℤ) : ℝ) *
              (beta : ℝ) ^ e := by
                simp [FloatSpec.Core.Generic_fmt.roundR, hcexp1, sm, hsm]
      _ = (n : ℝ) * (beta : ℝ) ^ e := by rw [hZ1]
      _ = xup := hxup_eval.symm
  have hxup_fmt :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 xup := by
    simpa [xup, hxup] using
      FloatSpec.Core.Generic_fmt.generic_format_roundR
        (beta := beta) (fexp := fexp1)
        (rnd := FloatSpec.Core.Generic_fmt.rnd_ceil) (x := x) hβ
  have hleft_fix :
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          (FloatSpec.Core.Generic_fmt.Znearest choice1) xup = xup :=
    FloatSpec.Core.Generic_fmt.roundR_generic
      (beta := beta) (fexp := fexp1)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest choice1)
      (x := xup) hβ hxup_fmt
  simpa [round_round_eq, hinner, hright, hleft_fix]

/-- Coq: `round_round_gt_mid_further_place'`. -/
theorem round_round_gt_mid_further_place' (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
      fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 →
    FloatSpec.Core.Generic_fmt.roundR beta fexp2
        (FloatSpec.Core.Generic_fmt.Znearest choice2) x <
      (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) →
    midp' beta fexp1 x + (1 / 2) * ulp beta fexp2 x < x →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  classical
  intro hx_pos hfexp hx_binade hx_mid
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  set m : Int := FloatSpec.Core.Raux.mag beta x with hm
  set e1 : Int := fexp1 m with he1
  set e2 : Int := fexp2 m with he2
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 x with hsm
  set n : Int := FloatSpec.Core.Generic_fmt.rnd_ceil sm with hn
  set xup : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_ceil x with hxup
  set xnn : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp2
    (FloatSpec.Core.Generic_fmt.Znearest choice2) x with hxnn
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hpow1_pos : 0 < (beta : ℝ) ^ e1 := zpow_pos hbposR e1
  have hpow2_pos : 0 < (beta : ℝ) ^ e2 := zpow_pos hbposR e2
  have hhalf_pos : (0 : ℝ) < (1 / 2) := by norm_num
  have hcexp1x : FloatSpec.Core.Generic_fmt.cexp beta fexp1 x = e1 := by
    simpa [FloatSpec.Core.Generic_fmt.cexp, m, hm, e1, he1]
  have hcexp2x : FloatSpec.Core.Generic_fmt.cexp beta fexp2 x = e2 := by
    simpa [FloatSpec.Core.Generic_fmt.cexp, m, hm, e2, he2]
  have hscaled : sm * (beta : ℝ) ^ e1 = x := by
    have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
      (beta := beta) (fexp := fexp1) (x := x)
    simpa [wp, PostCond.noThrow, Id.run, pure, sm, hsm, e1, hcexp1x]
      using h hβ
  have hxup_eval : xup = ((n : ℝ) * (beta : ℝ) ^ e1) := by
    simpa [xup, hxup, FloatSpec.Core.Generic_fmt.roundR, sm, hsm,
      n, hn, e1, hcexp1x]
  have hceil_ge : sm ≤ (n : ℝ) := by
    simpa [n, hn, FloatSpec.Core.Generic_fmt.rnd_ceil, FloatSpec.Core.Raux.Zceil]
      using Int.le_ceil sm
  have hx_le_xup : x ≤ xup := by
    have hmul := mul_le_mul_of_nonneg_right hceil_ge (le_of_lt hpow1_pos)
    simpa [hxup_eval, hscaled] using hmul
  have hPxxup : 0 ≤ xup - x := sub_nonneg.mpr hx_le_xup
  have hulp1 : ulp beta fexp1 x = (beta : ℝ) ^ e1 := by
    have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp1)
      (x := x) (hx := hx_ne)) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure, e1, hcexp1x] using h
  have hulp2 : ulp beta fexp2 x = (beta : ℝ) ^ e2 := by
    have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp2)
      (x := x) (hx := hx_ne)) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure, e2, hcexp2x] using h
  have hdiff_diff :
      xup - x < (1 / 2) * (ulp beta fexp1 x - ulp beta fexp2 x) := by
    have hx_mid' :
        xup - (1 / 2) * ulp beta fexp1 x +
            (1 / 2) * ulp beta fexp2 x < x := by
      simpa [midp', xup, hxup] using hx_mid
    linarith
  have hulp2_nonneg : 0 ≤ ulp beta fexp2 x := by
    rw [hulp2]
    exact le_of_lt hpow2_pos
  have hdiff_mid : xup - x < (1 / 2) * ulp beta fexp1 x := by
    nlinarith
  have hscaled_diff :
      ((n : ℝ) - sm) * (beta : ℝ) ^ e1 = xup - x := by
    rw [sub_mul, hxup_eval, hscaled]
  have hdist_ceil : |sm - (n : ℝ)| < (1 / 2 : ℝ) := by
    have hmul_lt :
        ((n : ℝ) - sm) * (beta : ℝ) ^ e1 < (1 / 2) * (beta : ℝ) ^ e1 := by
      simpa [hscaled_diff, hulp1] using hdiff_mid
    have hnonneg : 0 ≤ (n : ℝ) - sm := sub_nonneg.mpr hceil_ge
    have hlt : (n : ℝ) - sm < (1 / 2 : ℝ) := by
      nlinarith [hpow1_pos, hmul_lt]
    have hdist : |(n : ℝ) - sm| < (1 / 2 : ℝ) := by
      simpa [abs_of_nonneg hnonneg] using hlt
    simpa [abs_sub_comm] using hdist
  have hZ_right :
      FloatSpec.Core.Generic_fmt.Znearest choice1 sm = n := by
    have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice1 sm n) hdist_ceil
    simpa [wp,
      PostCond.noThrow, Id.run, pure] using h
  have hright :
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          (FloatSpec.Core.Generic_fmt.Znearest choice1) x = xup := by
    calc
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          (FloatSpec.Core.Generic_fmt.Znearest choice1) x
          = ((FloatSpec.Core.Generic_fmt.Znearest choice1 sm : ℤ) : ℝ) *
              (beta : ℝ) ^ e1 := by
                simp [FloatSpec.Core.Generic_fmt.roundR, hcexp1x, sm, hsm]
      _ = (n : ℝ) * (beta : ℝ) ^ e1 := by rw [hZ_right]
      _ = xup := hxup_eval.symm
  have herr :
      |xnn - x| ≤ (1 / 2) * ulp beta fexp2 x := by
    simpa [xnn, hxnn] using
      (FloatSpec.Core.Ulp.error_le_half_ulp_roundR
        (beta := beta) (fexp := fexp2) (choice := choice2) (x := x) hβ)
  have herr_bpow :
      |xnn - x| ≤ (1 / 2) * (beta : ℝ) ^ e2 := by
    simpa [hulp2] using herr
  have hdiff_bpow :
      xup - x < (1 / 2) * ((beta : ℝ) ^ e1 - (beta : ℝ) ^ e2) := by
    simpa [hulp1, hulp2] using hdiff_diff
  have hdist_xnn_xup :
      |xnn - xup| < (1 / 2) * (beta : ℝ) ^ e1 := by
    have htri : |xnn - xup| ≤ |xnn - x| + |x - xup| := by
      have h := abs_add_le (xnn - x) (x - xup)
      have hsum : xnn - x + (x - xup) = xnn - xup := by ring
      simpa [hsum] using h
    have hx_abs : |x - xup| = xup - x := by
      simpa [abs_sub_comm] using abs_of_nonneg hPxxup
    have hsum_lt :
        |xnn - x| + |x - xup| <
          (1 / 2) * (beta : ℝ) ^ e2 +
            (1 / 2) * ((beta : ℝ) ^ e1 - (beta : ℝ) ^ e2) := by
      rw [hx_abs]
      nlinarith [herr_bpow, hdiff_bpow]
    have hrhs :
        (1 / 2) * (beta : ℝ) ^ e2 +
            (1 / 2) * ((beta : ℝ) ^ e1 - (beta : ℝ) ^ e2) =
          (1 / 2) * (beta : ℝ) ^ e1 := by ring
    rw [hrhs] at hsum_lt
    exact lt_of_le_of_lt htri hsum_lt
  by_cases hxnn0 : xnn = 0
  · have hx_le_half_e2 : x ≤ (1 / 2) * (beta : ℝ) ^ e2 := by
      have hx_abs0 : |xnn - x| = x := by
        simpa [hxnn0, abs_of_pos hx_pos]
      simpa [hx_abs0] using herr_bpow
    have hfexp_lt : e2 < e1 := by
      have hf : e2 ≤ e1 - 1 := by simpa [m, hm, e1, he1, e2, he2] using hfexp
      exact Int.lt_of_le_sub_one hf
    have hbpow_lt : (beta : ℝ) ^ e2 < (beta : ℝ) ^ e1 := by
      have htrip := FloatSpec.Core.Raux.bpow_lt (beta := beta)
        (e1 := e2) (e2 := e1) hβ hfexp_lt
      simpa [FloatSpec.Core.Raux.bpow_lt_check, wp, PostCond.noThrow, Id.run, pure]
        using htrip True.intro
    have hx_lt_half_e1 : x < (1 / 2) * (beta : ℝ) ^ e1 := by
      nlinarith [hhalf_pos, hx_le_half_e2, hbpow_lt]
    have hsm_pos : 0 < sm := by
      nlinarith [hscaled, hpow1_pos, hx_pos]
    have hsm_lt_half : sm < (1 / 2 : ℝ) := by
      nlinarith [hscaled, hpow1_pos, hx_lt_half_e1]
    have hdist_zero : |sm - (0 : ℝ)| < (1 / 2 : ℝ) := by
      simpa [abs_of_nonneg (le_of_lt hsm_pos)] using hsm_lt_half
    have hZ_zero :
        FloatSpec.Core.Generic_fmt.Znearest choice1 sm = 0 := by
      have hdist_zero' : |sm - (((0 : Int) : ℝ))| < (1 / 2 : ℝ) := by
        simpa using hdist_zero
      have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice1 sm 0) hdist_zero'
      simpa [wp,
        PostCond.noThrow, Id.run, pure] using h
    have hright_zero :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) x = 0 := by
      calc
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) x
            = ((FloatSpec.Core.Generic_fmt.Znearest choice1 sm : ℤ) : ℝ) *
                (beta : ℝ) ^ e1 := by
                  simp [FloatSpec.Core.Generic_fmt.roundR, hcexp1x, sm, hsm]
        _ = 0 := by simp [hZ_zero]
    have hleft_zero :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) xnn = 0 := by
      have hfmt0 :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (0 : ℝ) :=
        FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp1)
      have hround0 :=
        FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := beta) (fexp := fexp1)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice1)
          (x := (0 : ℝ)) hβ hfmt0
      simpa [hxnn0] using hround0
    simpa [round_round_eq, hxnn, hright_zero, hleft_zero]
  · have hxnn_nonneg : 0 ≤ xnn := by
      have hfmt0 :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (0 : ℝ) :=
        FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp2)
      have h := FloatSpec.Core.Generic_fmt.roundR_ge_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
        (x := (0 : ℝ)) (y := x) hβ hfmt0 (le_of_lt hx_pos)
      simpa [xnn, hxnn] using h
    have hxnn_abs_lt : |xnn| < (beta : ℝ) ^ m := by
      simpa [abs_of_nonneg hxnn_nonneg, xnn, hxnn, m, hm] using hx_binade
    have hmag_le : FloatSpec.Core.Raux.mag beta xnn ≤ m := by
      have htrip := FloatSpec.Core.Raux.mag_le_bpow (beta := beta)
        (x := xnn) (e := m) hβ hxnn0 hxnn_abs_lt
      exact htrip True.intro
    have hmag_ge : m ≤ FloatSpec.Core.Raux.mag beta xnn := by
      have h := FloatSpec.Core.Generic_fmt.mag_roundR_ge
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2) (x := x) hβ
      simpa [xnn, hxnn, m, hm] using h hxnn0
    have hmag_eq : FloatSpec.Core.Raux.mag beta xnn = m :=
      le_antisymm hmag_le hmag_ge
    set smnn : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 xnn with hsmnn
    have hcexp1_xnn : FloatSpec.Core.Generic_fmt.cexp beta fexp1 xnn = e1 := by
      simpa [FloatSpec.Core.Generic_fmt.cexp, hmag_eq, e1, he1]
    have hscaled_nn : smnn * (beta : ℝ) ^ e1 = xnn := by
      have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
        (beta := beta) (fexp := fexp1) (x := xnn)
      simpa [wp, PostCond.noThrow, Id.run, pure, smnn, hsmnn, e1, hcexp1_xnn]
        using h hβ
    have hscaled_nn_diff :
        (smnn - (n : ℝ)) * (beta : ℝ) ^ e1 = xnn - xup := by
      rw [sub_mul, hscaled_nn, hxup_eval]
    have hdist_nn : |smnn - (n : ℝ)| < (1 / 2 : ℝ) := by
      have hmul_lt :
          |(smnn - (n : ℝ)) * (beta : ℝ) ^ e1| <
            (1 / 2) * (beta : ℝ) ^ e1 := by
        simpa [hscaled_nn_diff] using hdist_xnn_xup
      rw [abs_mul, abs_of_pos hpow1_pos] at hmul_lt
      exact lt_of_mul_lt_mul_right hmul_lt (le_of_lt hpow1_pos)
    have hZ_left :
        FloatSpec.Core.Generic_fmt.Znearest choice1 smnn = n := by
      have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice1 smnn n) hdist_nn
      simpa [wp,
        PostCond.noThrow, Id.run, pure] using h
    have hleft :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) xnn = xup := by
      calc
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) xnn
            = ((FloatSpec.Core.Generic_fmt.Znearest choice1 smnn : ℤ) : ℝ) *
                (beta : ℝ) ^ e1 := by
                  change
                    (((FloatSpec.Core.Generic_fmt.Znearest choice1
                        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 xnn) : Int) : ℝ) *
                      (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 xnn)
                    =
                    ((FloatSpec.Core.Generic_fmt.Znearest choice1 smnn : ℤ) : ℝ) *
                      (beta : ℝ) ^ e1
                  rw [hcexp1_xnn, ← hsmnn]
        _ = (n : ℝ) * (beta : ℝ) ^ e1 := by rw [hZ_left]
        _ = xup := hxup_eval.symm
    simpa [round_round_eq, hxnn, hright, hleft]

/-- Coq: `round_round_gt_mid_further_place`. -/
theorem round_round_gt_mid_further_place (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
      fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 →
    fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
      FloatSpec.Core.Raux.mag beta x →
    midp' beta fexp1 x + (1 / 2) * ulp beta fexp2 x < x →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  classical
  intro hx_pos hfexp hfexp1 hx_mid
  set m : Int := FloatSpec.Core.Raux.mag beta x with hm
  set e1 : Int := fexp1 m with he1
  set e2 : Int := fexp2 m with he2
  set xnn : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp2
    (FloatSpec.Core.Generic_fmt.Znearest choice2) x with hxnn
  by_cases hxnn_lt : xnn < (beta : ℝ) ^ m
  · exact round_round_gt_mid_further_place' (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2) (x := x) hβ
      hx_pos (by simpa [m, hm, e1, he1, e2, he2] using hfexp)
      (by simpa [xnn, hxnn, m, hm] using hxnn_lt) hx_mid
  · have hxnn_ge : (beta : ℝ) ^ m ≤ xnn := le_of_not_gt hxnn_lt
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
    have hpow1_pos : 0 < (beta : ℝ) ^ e1 := zpow_pos hbposR e1
    have hpow2_pos : 0 < (beta : ℝ) ^ e2 := zpow_pos hbposR e2
    have hcexp1x : FloatSpec.Core.Generic_fmt.cexp beta fexp1 x = e1 := by
      simpa [FloatSpec.Core.Generic_fmt.cexp, m, hm, e1, he1]
    have hcexp2x : FloatSpec.Core.Generic_fmt.cexp beta fexp2 x = e2 := by
      simpa [FloatSpec.Core.Generic_fmt.cexp, m, hm, e2, he2]
    have hulp1 : ulp beta fexp1 x = (beta : ℝ) ^ e1 := by
      have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp1)
        (x := x) (hx := hx_ne)) True.intro
      simpa [wp, PostCond.noThrow, Id.run, pure, e1, hcexp1x] using h
    have hulp2 : ulp beta fexp2 x = (beta : ℝ) ^ e2 := by
      have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp2)
        (x := x) (hx := hx_ne)) True.intro
      simpa [wp, PostCond.noThrow, Id.run, pure, e2, hcexp2x] using h
    have hx_lt_bpow : x < (beta : ℝ) ^ m := by
      have htrip := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := x) hβ hx_ne
      simpa [wp, PostCond.noThrow, Id.run, pure, FloatSpec.Core.Raux.abs_val,
        abs_of_pos hx_pos, m, hm] using htrip True.intro
    have herr :
        |xnn - x| ≤ (1 / 2) * ulp beta fexp2 x := by
      simpa [xnn, hxnn] using
        (FloatSpec.Core.Ulp.error_le_half_ulp_roundR
          (beta := beta) (fexp := fexp2) (choice := choice2) (x := x) hβ)
    have hxnn_upper : xnn < (beta : ℝ) ^ m + (1 / 2) * (beta : ℝ) ^ e2 := by
      have hxnn_le : xnn ≤ x + (1 / 2) * ulp beta fexp2 x := by
        have hle_abs : xnn - x ≤ |xnn - x| := le_abs_self (xnn - x)
        linarith
      nlinarith [hxnn_le, hx_lt_bpow, hulp2]
    have he2_lt_m : e2 < m := by
      have hf : e2 ≤ e1 - 1 := by simpa [m, hm, e1, he1, e2, he2] using hfexp
      have he1_le : e1 ≤ m := by simpa [m, hm, e1, he1] using hfexp1
      omega
    have he2_le_m : e2 ≤ m := le_of_lt he2_lt_m
    set k2 : Int := beta ^ Int.toNat (m - e2) with hk2
    have hk2_cast : (k2 : ℝ) = (beta : ℝ) ^ (m - e2) := by
      have hnonneg : 0 ≤ m - e2 := sub_nonneg.mpr he2_le_m
      have hz : (beta : ℝ) ^ (m - e2) =
          (beta : ℝ) ^ Int.toNat (m - e2) :=
        FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat
          (a := (beta : ℝ)) (k := m - e2) (hk := hnonneg)
      have hcast : (beta : ℝ) ^ Int.toNat (m - e2) =
          ((beta ^ Int.toNat (m - e2) : Int) : ℝ) := by
        simpa using (Int.cast_pow (R := ℝ) (x := beta) (n := Int.toNat (m - e2)))
      simpa [k2, hk2, hz] using hcast.symm
    have hk2_mul : (k2 : ℝ) * (beta : ℝ) ^ e2 = (beta : ℝ) ^ m := by
      calc
        (k2 : ℝ) * (beta : ℝ) ^ e2
            = (beta : ℝ) ^ (m - e2) * (beta : ℝ) ^ e2 := by rw [hk2_cast]
        _ = (beta : ℝ) ^ m := by
          simpa [sub_add_cancel] using
            (FloatSpec.Core.Generic_fmt.zpow_sub_add
              (a := (beta : ℝ)) (hbne := hbne) (e := m) (c := e2))
    set sm2 : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 x with hsm2
    set z2 : Int := FloatSpec.Core.Generic_fmt.Znearest choice2 sm2 with hz2
    have hxnn_eval : xnn = (z2 : ℝ) * (beta : ℝ) ^ e2 := by
      simpa [xnn, hxnn, FloatSpec.Core.Generic_fmt.roundR, sm2, hsm2, z2, hz2, e2,
        hcexp2x]
    have hz2_ge : k2 ≤ z2 := by
      have hmul : (k2 : ℝ) * (beta : ℝ) ^ e2 ≤ (z2 : ℝ) * (beta : ℝ) ^ e2 := by
        simpa [hk2_mul, hxnn_eval] using hxnn_ge
      have hreal : (k2 : ℝ) ≤ (z2 : ℝ) :=
        le_of_mul_le_mul_right hmul hpow2_pos
      exact_mod_cast hreal
    have hz2_lt : z2 < k2 + 1 := by
      have hmul : (z2 : ℝ) * (beta : ℝ) ^ e2 <
          ((k2 : ℝ) + (1 / 2 : ℝ)) * (beta : ℝ) ^ e2 := by
        have htarget :
            (beta : ℝ) ^ m + (1 / 2) * (beta : ℝ) ^ e2 =
              ((k2 : ℝ) + (1 / 2 : ℝ)) * (beta : ℝ) ^ e2 := by
          calc
            (beta : ℝ) ^ m + (1 / 2) * (beta : ℝ) ^ e2
                = (k2 : ℝ) * (beta : ℝ) ^ e2 +
                    (1 / 2) * (beta : ℝ) ^ e2 := by rw [hk2_mul]
            _ = ((k2 : ℝ) + (1 / 2 : ℝ)) * (beta : ℝ) ^ e2 := by ring
        have hxnn_upper_eval :
            (z2 : ℝ) * (beta : ℝ) ^ e2 <
              (beta : ℝ) ^ m + (1 / 2) * (beta : ℝ) ^ e2 := by
          simpa [hxnn_eval] using hxnn_upper
        rw [htarget] at hxnn_upper_eval
        exact hxnn_upper_eval
      have hreal_half : (z2 : ℝ) < (k2 : ℝ) + (1 / 2 : ℝ) :=
        lt_of_mul_lt_mul_right hmul (le_of_lt hpow2_pos)
      have hreal_one : (z2 : ℝ) < ((k2 + 1 : Int) : ℝ) := by
        have : (k2 : ℝ) + (1 / 2 : ℝ) < (k2 : ℝ) + 1 := by norm_num
        exact lt_trans hreal_half (by simpa [Int.cast_add, Int.cast_one] using this)
      exact_mod_cast hreal_one
    have hz2_eq : z2 = k2 := by
      exact le_antisymm (Int.lt_add_one_iff.mp hz2_lt) hz2_ge
    have hxnn_pow : xnn = (beta : ℝ) ^ m := by
      calc
        xnn = (z2 : ℝ) * (beta : ℝ) ^ e2 := hxnn_eval
        _ = (k2 : ℝ) * (beta : ℝ) ^ e2 := by rw [hz2_eq]
        _ = (beta : ℝ) ^ m := hk2_mul
    have hdiff_diff :
        (FloatSpec.Core.Generic_fmt.roundR beta fexp1
            FloatSpec.Core.Generic_fmt.rnd_ceil x) - x <
          (1 / 2) * (ulp beta fexp1 x - ulp beta fexp2 x) := by
      have hx_mid' :
          FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_ceil x -
              (1 / 2) * ulp beta fexp1 x +
              (1 / 2) * ulp beta fexp2 x < x := by
        simpa [midp'] using hx_mid
      linarith
    have hceil_nonneg :
        0 ≤
          FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_ceil x - x := by
      set smc : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 x with hsmc
      set nc : Int := FloatSpec.Core.Generic_fmt.rnd_ceil smc with hnc
      have hscaledc : smc * (beta : ℝ) ^ e1 = x := by
        have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
          (beta := beta) (fexp := fexp1) (x := x)
        simpa [wp, PostCond.noThrow, Id.run, pure, smc, hsmc, e1, hcexp1x]
          using h hβ
      have hceil_ge : smc ≤ (nc : ℝ) := by
        simpa [nc, hnc, FloatSpec.Core.Generic_fmt.rnd_ceil, FloatSpec.Core.Raux.Zceil]
          using Int.le_ceil smc
      have hmul :=
        mul_le_mul_of_nonneg_right hceil_ge (le_of_lt hpow1_pos)
      have hround_eval :
          FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_ceil x =
            (nc : ℝ) * (beta : ℝ) ^ e1 := by
        simpa [FloatSpec.Core.Generic_fmt.roundR, smc, hsmc, nc, hnc, e1, hcexp1x]
      have hx_le_round :
          x ≤ FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_ceil x := by
        simpa [hscaledc, hround_eval] using hmul
      exact sub_nonneg.mpr hx_le_round
    have hx_to_pow :
        |x - (beta : ℝ) ^ m| < (1 / 2) * ulp beta fexp1 x := by
      have herr' : |x - xnn| ≤ (1 / 2) * ulp beta fexp2 x := by
        simpa [abs_sub_comm] using herr
      have hulp2_lt_hulp1 : (1 / 2) * ulp beta fexp2 x <
          (1 / 2) * ulp beta fexp1 x := by
        nlinarith [hdiff_diff, hceil_nonneg]
      exact lt_of_le_of_lt (by simpa [hxnn_pow] using herr') hulp2_lt_hulp1
    have he1_le_m : e1 ≤ m := by simpa [m, hm, e1, he1] using hfexp1
    set k1 : Int := beta ^ Int.toNat (m - e1) with hk1
    have hk1_cast : (k1 : ℝ) = (beta : ℝ) ^ (m - e1) := by
      have hnonneg : 0 ≤ m - e1 := sub_nonneg.mpr he1_le_m
      have hz : (beta : ℝ) ^ (m - e1) =
          (beta : ℝ) ^ Int.toNat (m - e1) :=
        FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat
          (a := (beta : ℝ)) (k := m - e1) (hk := hnonneg)
      have hcast : (beta : ℝ) ^ Int.toNat (m - e1) =
          ((beta ^ Int.toNat (m - e1) : Int) : ℝ) := by
        simpa using (Int.cast_pow (R := ℝ) (x := beta) (n := Int.toNat (m - e1)))
      simpa [k1, hk1, hz] using hcast.symm
    have hk1_mul : (k1 : ℝ) * (beta : ℝ) ^ e1 = (beta : ℝ) ^ m := by
      calc
        (k1 : ℝ) * (beta : ℝ) ^ e1
            = (beta : ℝ) ^ (m - e1) * (beta : ℝ) ^ e1 := by rw [hk1_cast]
        _ = (beta : ℝ) ^ m := by
          simpa [sub_add_cancel] using
            (FloatSpec.Core.Generic_fmt.zpow_sub_add
              (a := (beta : ℝ)) (hbne := hbne) (e := m) (c := e1))
    set sm1 : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 x with hsm1
    have hscaled1 : sm1 * (beta : ℝ) ^ e1 = x := by
      have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
        (beta := beta) (fexp := fexp1) (x := x)
      simpa [wp, PostCond.noThrow, Id.run, pure, sm1, hsm1, e1, hcexp1x]
        using h hβ
    have hdist1 : |sm1 - (k1 : ℝ)| < (1 / 2 : ℝ) := by
      have hdiff :
          (sm1 - (k1 : ℝ)) * (beta : ℝ) ^ e1 =
            x - (beta : ℝ) ^ m := by
        rw [sub_mul, hscaled1, hk1_mul]
      have hmul_lt :
          |(sm1 - (k1 : ℝ)) * (beta : ℝ) ^ e1| <
            (1 / 2) * (beta : ℝ) ^ e1 := by
        simpa [hdiff, hulp1] using hx_to_pow
      rw [abs_mul, abs_of_pos hpow1_pos] at hmul_lt
      exact lt_of_mul_lt_mul_right hmul_lt (le_of_lt hpow1_pos)
    have hZ1 :
        FloatSpec.Core.Generic_fmt.Znearest choice1 sm1 = k1 := by
      have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice1 sm1 k1) hdist1
      simpa [wp,
        PostCond.noThrow, Id.run, pure] using h
    have hright :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) x =
          (beta : ℝ) ^ m := by
      calc
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) x
            = ((FloatSpec.Core.Generic_fmt.Znearest choice1 sm1 : Int) : ℝ) *
                (beta : ℝ) ^ e1 := by
                  simp [FloatSpec.Core.Generic_fmt.roundR, sm1, hsm1, e1, hcexp1x]
        _ = (k1 : ℝ) * (beta : ℝ) ^ e1 := by rw [hZ1]
        _ = (beta : ℝ) ^ m := hk1_mul
    have hfexp1_m_lt : e1 < m ∨ e1 = m := lt_or_eq_of_le he1_le_m
    have hfexp1_m1_le : fexp1 (m + 1) ≤ m := by
      rcases hfexp1_m_lt with hlt | heq
      · have hpair := (FloatSpec.Core.Generic_fmt.Valid_exp.valid_exp
          (beta := beta) (fexp := fexp1) m)
        exact hpair.left (by simpa [e1, he1] using hlt)
      · have hpair := (FloatSpec.Core.Generic_fmt.Valid_exp.valid_exp
          (beta := beta) (fexp := fexp1) m)
        have hsmall := hpair.right (by simpa [e1, he1, heq])
        simpa [e1, he1, heq] using hsmall.1
    have hbpow_fmt1 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 ((beta : ℝ) ^ m) := by
      have htrip := FloatSpec.Core.Generic_fmt.generic_format_bpow
        (beta := beta) (fexp := fexp1) (e := m)
      simpa [wp, PostCond.noThrow, Id.run, pure] using htrip ⟨hβ, hfexp1_m1_le⟩
    have hleft :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) xnn =
          (beta : ℝ) ^ m := by
      have hfix := FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp1)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice1)
        (x := (beta : ℝ) ^ m) hβ hbpow_fmt1
      simpa [hxnn_pow] using hfix
    simpa [round_round_eq, xnn, hxnn, hright, hleft]

/-- Coq: `round_round_gt_mid`. -/
theorem round_round_gt_mid (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
      fexp1 (FloatSpec.Core.Raux.mag beta x) →
    fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
      FloatSpec.Core.Raux.mag beta x →
    midp' beta fexp1 x < x →
    (fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 →
      midp' beta fexp1 x + (1 / 2) * ulp beta fexp2 x < x) →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  intro hx_pos hf21 hf1 hx_mid hx_further
  by_cases h12 :
      fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        fexp2 (FloatSpec.Core.Raux.mag beta x)
  · have heq :
        fexp2 (FloatSpec.Core.Raux.mag beta x) =
          fexp1 (FloatSpec.Core.Raux.mag beta x) :=
      le_antisymm hf21 h12
    exact round_round_gt_mid_same_place (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2) (x := x) hβ
      hx_pos heq hx_mid
  · have hlt :
        fexp2 (FloatSpec.Core.Raux.mag beta x) <
          fexp1 (FloatSpec.Core.Raux.mag beta x) :=
      lt_of_le_of_ne hf21 (by
        intro heq
        exact h12 (by simpa [heq]))
    have hfurther :
        fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 :=
      Int.le_sub_one_iff.mpr hlt
    exact round_round_gt_mid_further_place (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2) (x := x) hβ
      hx_pos hfurther hf1 (hx_further hfurther)

/-- Coq: `round_round_lt_mid_further_place'`. -/
theorem round_round_lt_mid_further_place' (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
      fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 →
    x < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) -
      (1 / 2) * ulp beta fexp2 x →
    x < midp beta fexp1 x - (1 / 2) * ulp beta fexp2 x →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  classical
  intro hx_pos hfexp hx_binade hx_mid
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  set m : Int := FloatSpec.Core.Raux.mag beta x with hm
  set e1 : Int := fexp1 m with he1
  set e2 : Int := fexp2 m with he2
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 x with hsm
  set n : Int := FloatSpec.Core.Generic_fmt.rnd_floor sm with hn
  set xdn : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_floor x with hxdn
  set xnn : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp2
    (FloatSpec.Core.Generic_fmt.Znearest choice2) x with hxnn
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hpow1_pos : 0 < (beta : ℝ) ^ e1 := zpow_pos hbposR e1
  have hpow2_pos : 0 < (beta : ℝ) ^ e2 := zpow_pos hbposR e2
  have hhalf_pos : (0 : ℝ) < (1 / 2) := by norm_num
  have hcexp1x : FloatSpec.Core.Generic_fmt.cexp beta fexp1 x = e1 := by
    simpa [FloatSpec.Core.Generic_fmt.cexp, m, hm, e1, he1]
  have hcexp2x : FloatSpec.Core.Generic_fmt.cexp beta fexp2 x = e2 := by
    simpa [FloatSpec.Core.Generic_fmt.cexp, m, hm, e2, he2]
  have hsm_def : sm = x * (beta : ℝ) ^ (-e1) := by
    simpa [FloatSpec.Core.Generic_fmt.scaled_mantissa, hcexp1x] using hsm
  have hscaled : sm * (beta : ℝ) ^ e1 = x := by
    have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
      (beta := beta) (fexp := fexp1) (x := x)
    simpa [wp, PostCond.noThrow, Id.run, pure, sm, hsm, e1, hcexp1x]
      using h hβ
  have hxdn_eval : xdn = ((n : ℝ) * (beta : ℝ) ^ e1) := by
    simpa [xdn, hxdn, FloatSpec.Core.Generic_fmt.roundR, sm, hsm,
      n, hn, e1, hcexp1x]
  have hfloor_le : (n : ℝ) ≤ sm := by
    simpa [n, hn, FloatSpec.Core.Generic_fmt.rnd_floor, FloatSpec.Core.Raux.Zfloor]
      using Int.floor_le sm
  have hxdn_le_x : xdn ≤ x := by
    have hmul := mul_le_mul_of_nonneg_right hfloor_le (le_of_lt hpow1_pos)
    simpa [hxdn_eval, hscaled] using hmul
  have hPxxdn : 0 ≤ x - xdn := sub_nonneg.mpr hxdn_le_x
  have hulp1 : ulp beta fexp1 x = (beta : ℝ) ^ e1 := by
    have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp1)
      (x := x) (hx := hx_ne)) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure, e1, hcexp1x] using h
  have hulp2 : ulp beta fexp2 x = (beta : ℝ) ^ e2 := by
    have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp2)
      (x := x) (hx := hx_ne)) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure, e2, hcexp2x] using h
  have hdiff_diff :
      x - xdn < (1 / 2) * (ulp beta fexp1 x - ulp beta fexp2 x) := by
    have hx_mid' :
        x < xdn + (1 / 2) * ulp beta fexp1 x -
            (1 / 2) * ulp beta fexp2 x := by
      simpa [midp, xdn, hxdn] using hx_mid
    linarith
  have hulp2_nonneg : 0 ≤ ulp beta fexp2 x := by
    rw [hulp2]
    exact le_of_lt hpow2_pos
  have hdiff_mid : x - xdn < (1 / 2) * ulp beta fexp1 x := by
    nlinarith
  have hscaled_diff :
      (sm - (n : ℝ)) * (beta : ℝ) ^ e1 = x - xdn := by
    rw [sub_mul, hscaled, hxdn_eval]
  have hdist_floor : |sm - (n : ℝ)| < (1 / 2 : ℝ) := by
    have hmul_lt :
        (sm - (n : ℝ)) * (beta : ℝ) ^ e1 < (1 / 2) * (beta : ℝ) ^ e1 := by
      simpa [hscaled_diff, hulp1] using hdiff_mid
    have hnonneg : 0 ≤ sm - (n : ℝ) := sub_nonneg.mpr hfloor_le
    have hlt : sm - (n : ℝ) < (1 / 2 : ℝ) := by
      nlinarith [hpow1_pos, hmul_lt]
    simpa [abs_of_nonneg hnonneg] using hlt
  have hZ_right :
      FloatSpec.Core.Generic_fmt.Znearest choice1 sm = n := by
    have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice1 sm n) hdist_floor
    simpa [wp,
      PostCond.noThrow, Id.run, pure] using h
  have hright :
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          (FloatSpec.Core.Generic_fmt.Znearest choice1) x = xdn := by
    calc
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          (FloatSpec.Core.Generic_fmt.Znearest choice1) x
          = ((FloatSpec.Core.Generic_fmt.Znearest choice1 sm : ℤ) : ℝ) *
              (beta : ℝ) ^ e1 := by
                simp [FloatSpec.Core.Generic_fmt.roundR, hcexp1x, sm, hsm]
      _ = (n : ℝ) * (beta : ℝ) ^ e1 := by rw [hZ_right]
      _ = xdn := hxdn_eval.symm
  have herr :
      |xnn - x| ≤ (1 / 2) * ulp beta fexp2 x := by
    simpa [xnn, hxnn] using
      (FloatSpec.Core.Ulp.error_le_half_ulp_roundR
        (beta := beta) (fexp := fexp2) (choice := choice2) (x := x) hβ)
  have herr_bpow :
      |xnn - x| ≤ (1 / 2) * (beta : ℝ) ^ e2 := by
    simpa [hulp2] using herr
  have hdiff_bpow :
      x - xdn < (1 / 2) * ((beta : ℝ) ^ e1 - (beta : ℝ) ^ e2) := by
    simpa [hulp1, hulp2] using hdiff_diff
  have hdist_xnn_xdn :
      |xnn - xdn| < (1 / 2) * (beta : ℝ) ^ e1 := by
    have htri : |xnn - xdn| ≤ |xnn - x| + |x - xdn| := by
      have h := abs_add_le (xnn - x) (x - xdn)
      have hsum : xnn - x + (x - xdn) = xnn - xdn := by ring
      simpa [hsum] using h
    have hx_abs : |x - xdn| = x - xdn := abs_of_nonneg hPxxdn
    have hsum_lt :
        |xnn - x| + |x - xdn| <
          (1 / 2) * (beta : ℝ) ^ e2 +
            (1 / 2) * ((beta : ℝ) ^ e1 - (beta : ℝ) ^ e2) := by
      rw [hx_abs]
      nlinarith [herr_bpow, hdiff_bpow]
    have hrhs :
        (1 / 2) * (beta : ℝ) ^ e2 +
            (1 / 2) * ((beta : ℝ) ^ e1 - (beta : ℝ) ^ e2) =
          (1 / 2) * (beta : ℝ) ^ e1 := by ring
    rw [hrhs] at hsum_lt
    exact lt_of_le_of_lt htri hsum_lt
  by_cases hxnn0 : xnn = 0
  · have hx_le_half_e2 : x ≤ (1 / 2) * (beta : ℝ) ^ e2 := by
      have hx_abs0 : |xnn - x| = x := by
        simpa [hxnn0, abs_of_pos hx_pos]
      simpa [hx_abs0] using herr_bpow
    have hfexp_lt : e2 < e1 := by
      have hf : e2 ≤ e1 - 1 := by simpa [m, hm, e1, he1, e2, he2] using hfexp
      exact Int.lt_of_le_sub_one hf
    have hbpow_lt : (beta : ℝ) ^ e2 < (beta : ℝ) ^ e1 := by
      have htrip := FloatSpec.Core.Raux.bpow_lt (beta := beta)
        (e1 := e2) (e2 := e1) hβ hfexp_lt
      simpa [FloatSpec.Core.Raux.bpow_lt_check, wp, PostCond.noThrow, Id.run, pure]
        using htrip True.intro
    have hx_lt_half_e1 : x < (1 / 2) * (beta : ℝ) ^ e1 := by
      nlinarith [hhalf_pos, hx_le_half_e2, hbpow_lt]
    have hsm_pos : 0 < sm := by
      nlinarith [hscaled, hpow1_pos, hx_pos]
    have hsm_lt_half : sm < (1 / 2 : ℝ) := by
      nlinarith [hscaled, hpow1_pos, hx_lt_half_e1]
    have hdist_zero : |sm - (0 : ℝ)| < (1 / 2 : ℝ) := by
      simpa [abs_of_nonneg (le_of_lt hsm_pos)] using hsm_lt_half
    have hZ_zero :
        FloatSpec.Core.Generic_fmt.Znearest choice1 sm = 0 := by
      have hdist_zero' : |sm - (((0 : Int) : ℝ))| < (1 / 2 : ℝ) := by
        simpa using hdist_zero
      have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice1 sm 0) hdist_zero'
      simpa [wp,
        PostCond.noThrow, Id.run, pure] using h
    have hright_zero :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) x = 0 := by
      calc
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) x
            = ((FloatSpec.Core.Generic_fmt.Znearest choice1 sm : ℤ) : ℝ) *
                (beta : ℝ) ^ e1 := by
                  simp [FloatSpec.Core.Generic_fmt.roundR, hcexp1x, sm, hsm]
        _ = 0 := by simp [hZ_zero]
    have hleft_zero :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) xnn = 0 := by
      have hfmt0 :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (0 : ℝ) :=
        FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp1)
      have hround0 :=
        FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := beta) (fexp := fexp1)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice1)
          (x := (0 : ℝ)) hβ hfmt0
      simpa [hxnn0] using hround0
    simpa [round_round_eq, hxnn, hright_zero, hleft_zero]
  · have hxnn_abs_lt : |xnn| < (beta : ℝ) ^ m := by
      have htri : |xnn| ≤ |xnn - x| + |x| := by
        have h := abs_add_le (xnn - x) x
        have hsum : xnn - x + x = xnn := by ring
        simpa [hsum] using h
      have hx_abs : |x| = x := abs_of_pos hx_pos
      have hx_binade_bpow :
          x < (beta : ℝ) ^ m - (1 / 2) * (beta : ℝ) ^ e2 := by
        simpa [m, hm, hulp2] using hx_binade
      have hsum_lt :
          |xnn - x| + |x| < (beta : ℝ) ^ m := by
        rw [hx_abs]
        linarith [herr_bpow, hx_binade_bpow]
      exact lt_of_le_of_lt htri hsum_lt
    have hmag_le : FloatSpec.Core.Raux.mag beta xnn ≤ m := by
      have htrip := FloatSpec.Core.Raux.mag_le_bpow (beta := beta)
        (x := xnn) (e := m) hβ hxnn0 hxnn_abs_lt
      exact htrip True.intro
    have hmag_ge : m ≤ FloatSpec.Core.Raux.mag beta xnn := by
      have h := FloatSpec.Core.Generic_fmt.mag_roundR_ge
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2) (x := x) hβ
      simpa [xnn, hxnn, m, hm] using h hxnn0
    have hmag_eq : FloatSpec.Core.Raux.mag beta xnn = m :=
      le_antisymm hmag_le hmag_ge
    set smnn : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 xnn with hsmnn
    have hcexp1_xnn : FloatSpec.Core.Generic_fmt.cexp beta fexp1 xnn = e1 := by
      simpa [FloatSpec.Core.Generic_fmt.cexp, hmag_eq, e1, he1]
    have hscaled_nn : smnn * (beta : ℝ) ^ e1 = xnn := by
      have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
        (beta := beta) (fexp := fexp1) (x := xnn)
      simpa [wp, PostCond.noThrow, Id.run, pure, smnn, hsmnn, e1, hcexp1_xnn]
        using h hβ
    have hscaled_nn_diff :
        (smnn - (n : ℝ)) * (beta : ℝ) ^ e1 = xnn - xdn := by
      rw [sub_mul, hscaled_nn, hxdn_eval]
    have hdist_nn : |smnn - (n : ℝ)| < (1 / 2 : ℝ) := by
      have hmul_lt :
          |(smnn - (n : ℝ)) * (beta : ℝ) ^ e1| <
            (1 / 2) * (beta : ℝ) ^ e1 := by
        simpa [hscaled_nn_diff] using hdist_xnn_xdn
      rw [abs_mul, abs_of_pos hpow1_pos] at hmul_lt
      exact lt_of_mul_lt_mul_right hmul_lt (le_of_lt hpow1_pos)
    have hZ_left :
        FloatSpec.Core.Generic_fmt.Znearest choice1 smnn = n := by
      have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice1 smnn n) hdist_nn
      simpa [wp,
        PostCond.noThrow, Id.run, pure] using h
    have hleft :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) xnn = xdn := by
      calc
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) xnn
            = ((FloatSpec.Core.Generic_fmt.Znearest choice1 smnn : ℤ) : ℝ) *
                (beta : ℝ) ^ e1 := by
                  change
                    (((FloatSpec.Core.Generic_fmt.Znearest choice1
                        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 xnn) : Int) : ℝ) *
                      (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 xnn)
                    =
                    ((FloatSpec.Core.Generic_fmt.Znearest choice1 smnn : ℤ) : ℝ) *
                      (beta : ℝ) ^ e1
                  rw [hcexp1_xnn, ← hsmnn]
        _ = (n : ℝ) * (beta : ℝ) ^ e1 := by rw [hZ_left]
        _ = xdn := hxdn_eval.symm
    simpa [round_round_eq, hxnn, hright, hleft]

/-- Coq: `round_round_lt_mid_further_place`. -/
theorem round_round_lt_mid_further_place (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
      fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 →
    fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
      FloatSpec.Core.Raux.mag beta x →
    x < midp beta fexp1 x - (1 / 2) * ulp beta fexp2 x →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  classical
  intro hx_pos hfexp hfexp1 hx_mid
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  set m : Int := FloatSpec.Core.Raux.mag beta x with hm
  set e1 : Int := fexp1 m with he1
  set e2 : Int := fexp2 m with he2
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 x with hsm
  set n : Int := FloatSpec.Core.Generic_fmt.rnd_floor sm with hn
  set xdn : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_floor x with hxdn
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hpow1_pos : 0 < (beta : ℝ) ^ e1 := zpow_pos hbposR e1
  have hcexp1x : FloatSpec.Core.Generic_fmt.cexp beta fexp1 x = e1 := by
    simpa [FloatSpec.Core.Generic_fmt.cexp, m, hm, e1, he1]
  have hcexp2x : FloatSpec.Core.Generic_fmt.cexp beta fexp2 x = e2 := by
    simpa [FloatSpec.Core.Generic_fmt.cexp, m, hm, e2, he2]
  have hscaled : sm * (beta : ℝ) ^ e1 = x := by
    have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
      (beta := beta) (fexp := fexp1) (x := x)
    simpa [wp, PostCond.noThrow, Id.run, pure, sm, hsm, e1, hcexp1x]
      using h hβ
  have hxdn_eval : xdn = ((n : ℝ) * (beta : ℝ) ^ e1) := by
    simpa [xdn, hxdn, FloatSpec.Core.Generic_fmt.roundR, sm, hsm,
      n, hn, e1, hcexp1x]
  have hfloor_le : (n : ℝ) ≤ sm := by
    simpa [n, hn, FloatSpec.Core.Generic_fmt.rnd_floor, FloatSpec.Core.Raux.Zfloor]
      using Int.floor_le sm
  have hxdn_le_x : xdn ≤ x := by
    have hmul := mul_le_mul_of_nonneg_right hfloor_le (le_of_lt hpow1_pos)
    simpa [hxdn_eval, hscaled] using hmul
  have hulp1 : ulp beta fexp1 x = (beta : ℝ) ^ e1 := by
    have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp1)
      (x := x) (hx := hx_ne)) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure, e1, hcexp1x] using h
  have hulp2 : ulp beta fexp2 x = (beta : ℝ) ^ e2 := by
    have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp2)
      (x := x) (hx := hx_ne)) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure, e2, hcexp2x] using h
  have hx_mid' :
      x < xdn + (1 / 2) * ulp beta fexp1 x -
          (1 / 2) * ulp beta fexp2 x := by
    simpa [midp, xdn, hxdn] using hx_mid
  have hxdn_half_le_bpow :
      xdn + (1 / 2) * ulp beta fexp1 x ≤ (beta : ℝ) ^ m := by
    by_cases hxdn0 : xdn = 0
    · have he1_le_m : e1 ≤ m := by
        simpa [m, hm, e1, he1] using hfexp1
      have hulp1_le : ulp beta fexp1 x ≤ (beta : ℝ) ^ m := by
        have htrip := FloatSpec.Core.Raux.bpow_le (beta := beta)
          (e1 := e1) (e2 := m) hβ he1_le_m
        simpa [hulp1, FloatSpec.Core.Raux.bpow_le_check, wp,
          PostCond.noThrow, Id.run, pure] using htrip True.intro
      have hulp1_nonneg : 0 ≤ ulp beta fexp1 x := by
        rw [hulp1]
        exact le_of_lt hpow1_pos
      nlinarith
    · have hsm_pos : 0 < sm := by
        nlinarith [hscaled, hpow1_pos, hx_pos]
      have hn_nonneg : (0 : Int) ≤ n := by
        simpa [n, hn, FloatSpec.Core.Generic_fmt.rnd_floor, FloatSpec.Core.Raux.Zfloor]
          using Int.floor_nonneg.mpr (le_of_lt hsm_pos)
      have hxdn_nonneg : 0 ≤ xdn := by
        rw [hxdn_eval]
        exact mul_nonneg (by exact_mod_cast hn_nonneg) (le_of_lt hpow1_pos)
      have hxdn_pos : 0 < xdn := lt_of_le_of_ne hxdn_nonneg (Ne.symm hxdn0)
      have hxdn_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 xdn := by
        simpa [xdn, hxdn] using
          FloatSpec.Core.Generic_fmt.generic_format_roundR
            (beta := beta) (fexp := fexp1)
            (rnd := FloatSpec.Core.Generic_fmt.rnd_floor) (x := x) hβ
      have hxdn_lt_bpow : xdn < (beta : ℝ) ^ m := by
        have htrip := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := x) hβ hx_ne
        have hx_lt : x < (beta : ℝ) ^ m := by
          simpa [wp, PostCond.noThrow, Id.run, pure, FloatSpec.Core.Raux.abs_val,
            abs_of_pos hx_pos, m, hm] using htrip True.intro
        exact lt_of_le_of_lt hxdn_le_x hx_lt
      have hid :
          xdn + ulp beta fexp1 xdn ≤ (beta : ℝ) ^ m := by
        have htrip := FloatSpec.Core.Ulp.id_p_ulp_le_bpow
          (beta := beta) (fexp := fexp1) (x := xdn) (e := m)
          hxdn_pos hxdn_fmt hxdn_lt_bpow
        simpa [wp, PostCond.noThrow, Id.run, bind, pure] using htrip hβ
      have hxdn_abs_lt : |xdn| < (beta : ℝ) ^ m := by
        simpa [abs_of_pos hxdn_pos] using hxdn_lt_bpow
      have hmag_le : FloatSpec.Core.Raux.mag beta xdn ≤ m := by
        have htrip := FloatSpec.Core.Raux.mag_le_bpow (beta := beta)
          (x := xdn) (e := m) hβ hxdn0 hxdn_abs_lt
        exact htrip True.intro
      have hmag_ge : m ≤ FloatSpec.Core.Raux.mag beta xdn := by
        have h := FloatSpec.Core.Generic_fmt.mag_roundR_ge
          (beta := beta) (fexp := fexp1)
          (rnd := FloatSpec.Core.Generic_fmt.rnd_floor) (x := x) hβ
        simpa [xdn, hxdn, m, hm] using h hxdn0
      have hmag_eq : FloatSpec.Core.Raux.mag beta xdn = m :=
        le_antisymm hmag_le hmag_ge
      have hcexp_xdn : FloatSpec.Core.Generic_fmt.cexp beta fexp1 xdn = e1 := by
        simpa [FloatSpec.Core.Generic_fmt.cexp, hmag_eq, e1, he1]
      have hulp_xdn : ulp beta fexp1 xdn = (beta : ℝ) ^ e1 := by
        have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp1)
          (x := xdn) (hx := hxdn0)) True.intro
        simpa [wp, PostCond.noThrow, Id.run, pure, e1, hcexp_xdn] using h
      have hid_x :
          xdn + ulp beta fexp1 x ≤ (beta : ℝ) ^ m := by
        simpa [hulp_xdn, hulp1] using hid
      have hulp1_nonneg : 0 ≤ ulp beta fexp1 x := by
        rw [hulp1]
        exact le_of_lt hpow1_pos
      nlinarith
  have hx_binade :
      x < (beta : ℝ) ^ m - (1 / 2) * ulp beta fexp2 x := by
    linarith [hx_mid', hxdn_half_le_bpow]
  exact round_round_lt_mid_further_place' (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (x := x) hβ
    hx_pos (by simpa [m, hm, e1, he1, e2, he2] using hfexp)
    (by simpa [m, hm] using hx_binade) hx_mid

/-- Coq: `round_round_lt_mid`. -/
theorem round_round_lt_mid (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
      fexp1 (FloatSpec.Core.Raux.mag beta x) →
    fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
      FloatSpec.Core.Raux.mag beta x →
    x < midp beta fexp1 x →
    (fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 →
      x < midp beta fexp1 x - (1 / 2) * ulp beta fexp2 x) →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  intro hx_pos hf21 hf1 hx_mid hx_further
  by_cases h12 :
      fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        fexp2 (FloatSpec.Core.Raux.mag beta x)
  · have heq :
        fexp2 (FloatSpec.Core.Raux.mag beta x) =
          fexp1 (FloatSpec.Core.Raux.mag beta x) :=
      le_antisymm hf21 h12
    exact round_round_lt_mid_same_place (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2) (x := x) hβ
      hx_pos heq hx_mid
  · have hlt :
        fexp2 (FloatSpec.Core.Raux.mag beta x) <
          fexp1 (FloatSpec.Core.Raux.mag beta x) :=
      lt_of_le_of_ne hf21 (by
        intro heq
        exact h12 (by simpa [heq]))
    have hfurther :
        fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 :=
      Int.le_sub_one_iff.mpr hlt
    exact round_round_lt_mid_further_place (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2) (x := x) hβ
      hx_pos hfurther hf1 (hx_further hfurther)

private theorem ceil_eq_floor_add_one_of_not_int (x : ℝ)
    (hnot : ¬ ∃ z : Int, x = (z : ℝ)) :
    Int.ceil x = Int.floor x + 1 := by
  have hceil_le : Int.ceil x ≤ Int.floor x + 1 :=
    Int.ceil_le_floor_add_one x
  have hfloor_lt : Int.floor x < Int.ceil x := by
    by_contra hnot_lt
    have hceil_le_floor : Int.ceil x ≤ Int.floor x := le_of_not_gt hnot_lt
    have hx_le_floor : x ≤ (Int.floor x : ℝ) :=
      le_trans (Int.le_ceil x) (by exact_mod_cast hceil_le_floor)
    have hfloor_le_x : (Int.floor x : ℝ) ≤ x := Int.floor_le x
    have hx_eq : x = (Int.floor x : ℝ) := le_antisymm hx_le_floor hfloor_le_x
    exact hnot ⟨Int.floor x, hx_eq⟩
  omega

private theorem roundR_ceil_eq_floor_add_ulp_pos (fexp : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp] (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    ¬ FloatSpec.Core.Generic_fmt.generic_format beta fexp x →
    FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x =
      FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x
        + ulp beta fexp x := by
  classical
  intro hx_pos hnot_fmt
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x with he
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x with hsm
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hnot_int : ¬ ∃ z : Int, sm = (z : ℝ) := by
    intro hz
    rcases hz with ⟨z, hz⟩
    have hscaled :
        sm * (beta : ℝ) ^ e = x := by
      have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
        (beta := beta) (fexp := fexp) (x := x)
      simpa [wp, PostCond.noThrow, Id.run, pure, sm, hsm, e, he] using h hβ
    have hx_repr :
        x = FloatSpec.Core.Defs.F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk z e :
            FloatSpec.Core.Defs.FlocqFloat beta) := by
      calc
        x = sm * (beta : ℝ) ^ e := hscaled.symm
        _ = (z : ℝ) * (beta : ℝ) ^ e := by rw [hz]
        _ = FloatSpec.Core.Defs.F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk z e :
            FloatSpec.Core.Defs.FlocqFloat beta) := by
              simp [FloatSpec.Core.Defs.F2R]
    have htrunc : FloatSpec.Core.Raux.Ztrunc sm = z := by
      simp [FloatSpec.Core.Raux.Ztrunc, hz]
    have hfmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp x := by
      unfold FloatSpec.Core.Generic_fmt.generic_format
      change x = FloatSpec.Core.Defs.F2R
        (FloatSpec.Core.Defs.FlocqFloat.mk
          (FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x))
          (FloatSpec.Core.Generic_fmt.cexp beta fexp x) :
            FloatSpec.Core.Defs.FlocqFloat beta)
      rw [← hsm, ← he, htrunc]
      exact hx_repr
    exact hnot_fmt hfmt
  have hceil :
      FloatSpec.Core.Generic_fmt.rnd_ceil sm =
        FloatSpec.Core.Generic_fmt.rnd_floor sm + 1 := by
    simpa [FloatSpec.Core.Generic_fmt.rnd_ceil, FloatSpec.Core.Generic_fmt.rnd_floor,
      FloatSpec.Core.Raux.Zceil, FloatSpec.Core.Raux.Zfloor]
      using ceil_eq_floor_add_one_of_not_int sm hnot_int
  have hulp : ulp beta fexp x = (beta : ℝ) ^ e := by
    have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp)
      (x := x) (hx := hx_ne)) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure, e, he] using h
  simp [FloatSpec.Core.Generic_fmt.roundR, sm, hsm, e, he, hceil, hulp,
    Int.cast_add, add_mul]

/-- Coq: `round_round_really_zero`.

If the first format exponent is at least two places above the current binade,
then both the direct first rounding and the first rounding after the second
rounding are zero. This is the early small-value branch used by Coq's
`round_round_all_mid_cases`. -/
theorem round_round_really_zero (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    FloatSpec.Core.Raux.mag beta x ≤
      fexp1 (FloatSpec.Core.Raux.mag beta x) - 2 →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  classical
  intro hx_pos hf1_really
  set m : Int := FloatSpec.Core.Raux.mag beta x with hm
  set xnn : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp2
    (FloatSpec.Core.Generic_fmt.Znearest choice2) x with hxnn
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hlow_x : (beta : ℝ) ^ (m - 1) ≤ x := by
    have htrip := FloatSpec.Core.Raux.mag_lower_bound
      (beta := beta) (x := x) hβ hx_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Raux.abs_val, abs_of_pos hx_pos, m, hm]
      using htrip True.intro
  have hupp_x : x < (beta : ℝ) ^ m := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := x) hβ hx_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Raux.abs_val, abs_of_pos hx_pos, m, hm]
      using htrip True.intro
  have hf1_really_m : m ≤ fexp1 m - 2 := by
    simpa [m, hm] using hf1_really
  have hf1_gt_m : fexp1 m > m := by omega
  have hright :
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          (FloatSpec.Core.Generic_fmt.Znearest choice1) x = 0 :=
    FloatSpec.Core.Generic_fmt.round_N_small_pos
      (beta := beta) (fexp := fexp1) (choice := choice1)
      (x := x) (ex := m) hβ ⟨hlow_x, hupp_x⟩ hf1_gt_m
  have hzero_fmt1 :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 0 :=
    FloatSpec.Core.Generic_fmt.generic_format_0_run
      (beta := beta) (fexp := fexp1)
  have hzero_fmt2 :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp2 0 :=
    FloatSpec.Core.Generic_fmt.generic_format_0_run
      (beta := beta) (fexp := fexp2)
  have hxnn_nonneg : 0 ≤ xnn := by
    have h := FloatSpec.Core.Generic_fmt.roundR_ge_generic
      (beta := beta) (fexp := fexp2)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
      (x := (0 : ℝ)) (y := x) hβ hzero_fmt2 (le_of_lt hx_pos)
    simpa [xnn, hxnn] using h
  by_cases hxnn0 : xnn = 0
  · have hleft :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) xnn = 0 := by
      have hfix := FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp1)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice1)
        (x := (0 : ℝ)) hβ hzero_fmt1
      simpa [hxnn0] using hfix
    simpa [round_round_eq, xnn, hxnn, hright, hleft]
  · by_cases hf2_le : fexp2 m ≤ m
    · have hfmt_bpow_m :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp2 ((beta : ℝ) ^ m) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_bpow'
          (beta := beta) (fexp := fexp2) (e := m)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip ⟨hβ, hf2_le⟩
      have hx_le_bpow_m : x ≤ (beta : ℝ) ^ m := le_of_lt hupp_x
      have hxnn_le_bpow_m : xnn ≤ (beta : ℝ) ^ m := by
        have h := FloatSpec.Core.Generic_fmt.roundR_le_generic
          (beta := beta) (fexp := fexp2)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
          (x := x) (y := (beta : ℝ) ^ m) hβ hfmt_bpow_m hx_le_bpow_m
        simpa [xnn, hxnn] using h
      by_cases hxnn_lt : xnn < (beta : ℝ) ^ m
      · have hxnn_abs_lt : |xnn| < (beta : ℝ) ^ m := by
          simpa [abs_of_nonneg hxnn_nonneg] using hxnn_lt
        have hmag_le : FloatSpec.Core.Raux.mag beta xnn ≤ m := by
          have htrip := FloatSpec.Core.Raux.mag_le_bpow
            (beta := beta) (x := xnn) (e := m) hβ hxnn0 hxnn_abs_lt
          exact htrip True.intro
        have hmag_ge : m ≤ FloatSpec.Core.Raux.mag beta xnn := by
          have h := FloatSpec.Core.Generic_fmt.mag_roundR_ge
            (beta := beta) (fexp := fexp2)
            (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2) (x := x) hβ
          simpa [xnn, hxnn, m, hm] using h hxnn0
        have hmag_eq : FloatSpec.Core.Raux.mag beta xnn = m :=
          le_antisymm hmag_le hmag_ge
        have hlow_xnn : (beta : ℝ) ^ (m - 1) ≤ xnn := by
          have htrip := FloatSpec.Core.Raux.mag_lower_bound
            (beta := beta) (x := xnn) hβ hxnn0
          simpa [wp, PostCond.noThrow, Id.run, pure,
            FloatSpec.Core.Raux.abs_val, abs_of_nonneg hxnn_nonneg, hmag_eq]
            using htrip True.intro
        have hleft :
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
                (FloatSpec.Core.Generic_fmt.Znearest choice1) xnn = 0 :=
          FloatSpec.Core.Generic_fmt.round_N_small_pos
            (beta := beta) (fexp := fexp1) (choice := choice1)
            (x := xnn) (ex := m) hβ ⟨hlow_xnn, hxnn_lt⟩ hf1_gt_m
        simpa [round_round_eq, xnn, hxnn, hright, hleft]
      · have hbpow_le_xnn : (beta : ℝ) ^ m ≤ xnn := le_of_not_gt hxnn_lt
        have hxnn_eq_bpow : xnn = (beta : ℝ) ^ m :=
          le_antisymm hxnn_le_bpow_m hbpow_le_xnn
        have hf1_m_le : m ≤ fexp1 m := by omega
        have hf1_const :
            fexp1 (m + 1) = fexp1 m := by
          have hpair := FloatSpec.Core.Generic_fmt.Valid_exp.valid_exp
            (beta := beta) (fexp := fexp1) m
          have hconst := (hpair.right hf1_m_le).right
          exact hconst (m + 1) (by omega)
        have hf1_gt_succ : fexp1 (m + 1) > m + 1 := by
          rw [hf1_const]
          omega
        have hlow_bpow : (beta : ℝ) ^ ((m + 1) - 1) ≤ (beta : ℝ) ^ m := by
          simpa using (le_rfl : (beta : ℝ) ^ m ≤ (beta : ℝ) ^ m)
        have hupp_bpow : (beta : ℝ) ^ m < (beta : ℝ) ^ (m + 1) := by
          have htrip := FloatSpec.Core.Raux.bpow_lt
            (beta := beta) (e1 := m) (e2 := m + 1) hβ (by omega)
          simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
        have hleft_bpow :
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
                (FloatSpec.Core.Generic_fmt.Znearest choice1) ((beta : ℝ) ^ m) = 0 :=
          FloatSpec.Core.Generic_fmt.round_N_small_pos
            (beta := beta) (fexp := fexp1) (choice := choice1)
            (x := (beta : ℝ) ^ m) (ex := m + 1) hβ
            ⟨by simpa using hlow_bpow, by simpa using hupp_bpow⟩ hf1_gt_succ
        have hleft :
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
                (FloatSpec.Core.Generic_fmt.Znearest choice1) xnn = 0 := by
          simpa [hxnn_eq_bpow] using hleft_bpow
        simpa [round_round_eq, xnn, hxnn, hright, hleft]
    · have hf2_gt : fexp2 m > m := by omega
      have hxnn_zero :
          xnn = 0 := by
        have h := FloatSpec.Core.Generic_fmt.round_N_small_pos
          (beta := beta) (fexp := fexp2) (choice := choice2)
          (x := x) (ex := m) hβ ⟨hlow_x, hupp_x⟩ hf2_gt
        simpa [xnn, hxnn] using h
      exact (hxnn0 hxnn_zero).elim

/-- Coq: `round_round_zero`.

In the top-binade case `fexp1 (mag x) = mag x + 1`, if `x` is still below
the upper binade boundary by at least a half ulp of the second format, then
both the direct first rounding and the first rounding after the second rounding
are zero. This is the zero branch used by Coq's
`round_round_all_mid_cases`. -/
theorem round_round_zero (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    fexp1 (FloatSpec.Core.Raux.mag beta x) =
      FloatSpec.Core.Raux.mag beta x + 1 →
    x < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) -
        (1 / 2) * ulp beta fexp2 x →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  classical
  intro hx_pos hf1_top hx_small
  set m : Int := FloatSpec.Core.Raux.mag beta x with hm
  set xnn : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp2
    (FloatSpec.Core.Generic_fmt.Znearest choice2) x with hxnn
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hlow_x : (beta : ℝ) ^ (m - 1) ≤ x := by
    have htrip := FloatSpec.Core.Raux.mag_lower_bound
      (beta := beta) (x := x) hβ hx_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Raux.abs_val, abs_of_pos hx_pos, m, hm]
      using htrip True.intro
  have hupp_x : x < (beta : ℝ) ^ m := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := x) hβ hx_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Raux.abs_val, abs_of_pos hx_pos, m, hm]
      using htrip True.intro
  have hf1_top_m : fexp1 m = m + 1 := by
    simpa [m, hm] using hf1_top
  have hf1_gt : fexp1 m > m := by
    omega
  have hright :
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          (FloatSpec.Core.Generic_fmt.Znearest choice1) x = 0 :=
    FloatSpec.Core.Generic_fmt.round_N_small_pos
      (beta := beta) (fexp := fexp1) (choice := choice1)
      (x := x) (ex := m) hβ ⟨hlow_x, hupp_x⟩ hf1_gt
  have hzero_fmt2 :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp2 0 :=
    FloatSpec.Core.Generic_fmt.generic_format_0_run
      (beta := beta) (fexp := fexp2)
  have hxnn_nonneg : 0 ≤ xnn := by
    have h := FloatSpec.Core.Generic_fmt.roundR_ge_generic
      (beta := beta) (fexp := fexp2)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
      (x := (0 : ℝ)) (y := x) hβ hzero_fmt2 (le_of_lt hx_pos)
    simpa [xnn, hxnn] using h
  have herr :
      |xnn - x| ≤ (1 / 2) * ulp beta fexp2 x := by
    simpa [xnn, hxnn] using
      (FloatSpec.Core.Ulp.error_le_half_ulp_roundR
        (beta := beta) (fexp := fexp2) (choice := choice2) (x := x) hβ)
  have hxnn_lt : xnn < (beta : ℝ) ^ m := by
    have hdelta : xnn - x ≤ |xnn - x| := le_abs_self (xnn - x)
    have hx_small' :
        x < (beta : ℝ) ^ m - (1 / 2) * ulp beta fexp2 x := by
      simpa [m, hm] using hx_small
    linarith
  by_cases hxnn0 : xnn = 0
  · have hzero_fmt1 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 0 :=
      FloatSpec.Core.Generic_fmt.generic_format_0_run
        (beta := beta) (fexp := fexp1)
    have hleft :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) xnn = 0 := by
      have hfix := FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp1)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice1)
        (x := (0 : ℝ)) hβ hzero_fmt1
      simpa [hxnn0] using hfix
    simpa [round_round_eq, xnn, hxnn, hright, hleft]
  · have hxnn_abs_lt : |xnn| < (beta : ℝ) ^ m := by
      simpa [abs_of_nonneg hxnn_nonneg] using hxnn_lt
    have hmag_le : FloatSpec.Core.Raux.mag beta xnn ≤ m := by
      have htrip := FloatSpec.Core.Raux.mag_le_bpow
        (beta := beta) (x := xnn) (e := m) hβ hxnn0 hxnn_abs_lt
      exact htrip True.intro
    have hmag_ge : m ≤ FloatSpec.Core.Raux.mag beta xnn := by
      have h := FloatSpec.Core.Generic_fmt.mag_roundR_ge
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2) (x := x) hβ
      simpa [xnn, hxnn, m, hm] using h hxnn0
    have hmag_eq : FloatSpec.Core.Raux.mag beta xnn = m :=
      le_antisymm hmag_le hmag_ge
    have hlow_xnn : (beta : ℝ) ^ (m - 1) ≤ xnn := by
      have htrip := FloatSpec.Core.Raux.mag_lower_bound
        (beta := beta) (x := xnn) hβ hxnn0
      simpa [wp, PostCond.noThrow, Id.run, pure,
        FloatSpec.Core.Raux.abs_val, abs_of_nonneg hxnn_nonneg, hmag_eq]
        using htrip True.intro
    have hleft :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) xnn = 0 :=
      FloatSpec.Core.Generic_fmt.round_N_small_pos
        (beta := beta) (fexp := fexp1) (choice := choice1)
        (x := xnn) (ex := m) hβ ⟨hlow_xnn, hxnn_lt⟩ hf1_gt
    simpa [round_round_eq, xnn, hxnn, hright, hleft]

/-- Coq: `round_round_mid_cases`. -/
theorem round_round_mid_cases (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
      fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 →
    fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
      FloatSpec.Core.Raux.mag beta x →
    (|x - midp beta fexp1 x| ≤ (1 / 2) * ulp beta fexp2 x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 x) →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  classical
  intro hx_pos hf21 hf1 hmid
  rcases FloatSpec.Core.Generic_fmt.generic_format_EM beta fexp1 x with hfmt | hnot_fmt
  · have hx_fmt2 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 x :=
      FloatSpec.Core.Generic_fmt.generic_inclusion_mag
        (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2) (x := x) hβ
        (by
          intro _
          exact le_trans hf21 (by omega)) hfmt
    have hinner :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) x = x :=
      FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2) (x := x) hβ hx_fmt2
    simp [round_round_eq, hinner]
  · set rd : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor x with hrd
    set u1 : ℝ := ulp beta fexp1 x with hu1
    set u2 : ℝ := ulp beta fexp2 x with hu2
    have hceil :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1 FloatSpec.Core.Generic_fmt.rnd_ceil x =
          rd + u1 := by
      simpa [rd, hrd, u1, hu1] using
        roundR_ceil_eq_floor_add_ulp_pos (beta := beta)
          (fexp := fexp1) (x := x) hβ hx_pos hnot_fmt
    by_cases hlt : x - rd < (1 / 2) * (u1 - u2)
    · exact round_round_lt_mid_further_place (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2) (x := x) hβ
        hx_pos hf21 hf1 (by
          simp [midp, rd, hrd, u1, hu1, u2, hu2]
          linarith)
    · have hge : (1 / 2) * (u1 - u2) ≤ x - rd := le_of_not_gt hlt
      by_cases hgt : (1 / 2) * (u1 + u2) < x - rd
      · exact round_round_gt_mid_further_place (beta := beta)
          (fexp1 := fexp1) (fexp2 := fexp2)
          (choice1 := choice1) (choice2 := choice2) (x := x) hβ
          hx_pos hf21 hf1 (by
            simp [midp', rd, hrd, u1, hu1, u2, hu2, hceil]
            linarith)
      · have hle : x - rd ≤ (1 / 2) * (u1 + u2) := le_of_not_gt hgt
        exact hmid (by
          simp [midp, rd, hrd, u1, hu1, u2, hu2, abs_le]
          constructor <;> linarith)

/-- Coq: `round_round_all_mid_cases`, factored at `round_round_really_zero`.

This is the dispatcher used by Coq's positive division lemma. The only
remaining branch kept as an explicit premise is the earlier
`round_round_really_zero` case, where the first format exponent is at least two
places above `mag x`. The top-binade branch is discharged here by the restored
`round_round_zero`, and the ordinary midpoint band is delegated to
`round_round_mid_cases`. -/
theorem round_round_all_mid_cases_from_really_zero (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
      fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 →
    (fexp1 (FloatSpec.Core.Raux.mag beta x) ≥
        FloatSpec.Core.Raux.mag beta x + 2 →
      round_round_eq beta fexp1 fexp2 choice1 choice2 x) →
    (fexp1 (FloatSpec.Core.Raux.mag beta x) =
        FloatSpec.Core.Raux.mag beta x + 1 →
      (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) -
          (1 / 2) * ulp beta fexp2 x ≤ x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 x) →
    (fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        FloatSpec.Core.Raux.mag beta x →
      midp beta fexp1 x - (1 / 2) * ulp beta fexp2 x ≤ x ∧
        x < midp beta fexp1 x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 x) →
    (fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        FloatSpec.Core.Raux.mag beta x →
      x = midp beta fexp1 x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 x) →
    (fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        FloatSpec.Core.Raux.mag beta x →
      midp beta fexp1 x < x ∧
        x ≤ midp beta fexp1 x + (1 / 2) * ulp beta fexp2 x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 x) →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  classical
  intro hx_pos hf2 hreally htop hlow hmid_eq hhigh
  set m : Int := FloatSpec.Core.Raux.mag beta x with hm
  rcases lt_trichotomy m (fexp1 m - 1) with hlt | heq | hgt
  · apply hreally
    simpa [m, hm] using (by omega : fexp1 m ≥ m + 2)
  · have hf1_top_m : fexp1 m = m + 1 := by omega
    have hf1_top :
        fexp1 (FloatSpec.Core.Raux.mag beta x) =
          FloatSpec.Core.Raux.mag beta x + 1 := by
      simpa [m, hm] using hf1_top_m
    by_cases hsmall :
        x < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) -
          (1 / 2) * ulp beta fexp2 x
    · exact round_round_zero (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2) (x := x) hβ
        hx_pos hf1_top hsmall
    · exact htop hf1_top (le_of_not_gt hsmall)
  · have hf1_le_m : fexp1 m ≤ m := by omega
    have hf1_le :
        fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
          FloatSpec.Core.Raux.mag beta x := by
      simpa [m, hm] using hf1_le_m
    apply round_round_mid_cases (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2) (x := x) hβ
      hx_pos hf2 hf1_le
    intro hband
    rcases lt_trichotomy x (midp beta fexp1 x) with hlt_mid | heq_mid | hgt_mid
    · apply hlow hf1_le
      constructor
      · rw [abs_le] at hband
        linarith
      · exact hlt_mid
    · exact hmid_eq hf1_le heq_mid
    · apply hhigh hf1_le
      constructor
      · exact hgt_mid
      · rw [abs_le] at hband
        linarith

/-- Coq: `round_round_all_mid_cases`. -/
theorem round_round_all_mid_cases (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta) :
    0 < x →
    fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
      fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 →
    (fexp1 (FloatSpec.Core.Raux.mag beta x) =
        FloatSpec.Core.Raux.mag beta x + 1 →
      (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) -
          (1 / 2) * ulp beta fexp2 x ≤ x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 x) →
    (fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        FloatSpec.Core.Raux.mag beta x →
      midp beta fexp1 x - (1 / 2) * ulp beta fexp2 x ≤ x ∧
        x < midp beta fexp1 x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 x) →
    (fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        FloatSpec.Core.Raux.mag beta x →
      x = midp beta fexp1 x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 x) →
    (fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        FloatSpec.Core.Raux.mag beta x →
      midp beta fexp1 x < x ∧
        x ≤ midp beta fexp1 x + (1 / 2) * ulp beta fexp2 x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 x) →
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  classical
  intro hx_pos hf2 htop hlow hmid_eq hhigh
  exact round_round_all_mid_cases_from_really_zero (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (x := x) hβ
    hx_pos hf2
    (by
      intro hf1_really
      exact round_round_really_zero (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2) (x := x) hβ
        hx_pos (by omega))
    htop hlow hmid_eq hhigh

/-- Coq: `mag_sqrt_disj`. -/
theorem mag_sqrt_disj (x : ℝ) (hβ : 1 < beta) :
    0 < x →
    FloatSpec.Core.Raux.mag beta x =
        2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x) - 1 ∨
      FloatSpec.Core.Raux.mag beta x =
        2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
  intro hx_pos
  have hmag_sqrt :
      FloatSpec.Core.Raux.mag beta (Real.sqrt x) =
        Int.floor ((Real.log x / Real.log (beta : ℝ)) / 2) + 1 := by
    have h := (FloatSpec.Core.Raux.mag_sqrt (beta := beta) (x := x) hβ hx_pos) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure] using h
  have hmag_x :
      FloatSpec.Core.Raux.mag beta x =
        Int.floor (Real.log x / Real.log (beta : ℝ)) + 1 := by
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    simp [FloatSpec.Core.Raux.mag, hx_ne, abs_of_pos hx_pos]
  set n : Int := Int.floor (Real.log x / Real.log (beta : ℝ)) with hn
  set m : Int := Int.floor ((Real.log x / Real.log (beta : ℝ)) / 2) with hm
  have hmagx_n :
      FloatSpec.Core.Raux.mag beta x = n + 1 := by
    rw [hmag_x, hn]
  have hmagsqrt_m :
      FloatSpec.Core.Raux.mag beta (Real.sqrt x) = m + 1 := by
    rw [hmag_sqrt, hm]
  have hfloor_div :
      m = n / 2 := by
    rw [hm, hn]
    exact Int.floor_div_natCast (Real.log x / Real.log (beta : ℝ)) 2
  have hdecomp : 2 * (n / 2) + n % 2 = n := by
    simpa using (Int.mul_ediv_add_emod n 2)
  rcases Int.emod_two_eq_zero_or_one n with hmod | hmod
  · left
    have hn_even : n = 2 * m := by
      have h := hdecomp
      rw [hmod] at h
      rw [← hfloor_div] at h
      omega
    rw [hmagx_n, hmagsqrt_m]
    omega
  · right
    have hn_odd : n = 2 * m + 1 := by
      have h := hdecomp
      rw [hmod] at h
      rw [← hfloor_div] at h
      omega
    rw [hmagx_n, hmagsqrt_m]
    omega

/-! Structural hypotheses used by the omitted Flocq double-rounding lemmas. -/

/-- Coq: `mag_mult_disj`.

The magnitude of a nonzero product is either the sum of magnitudes or one less.
-/
theorem mag_mult_disj (x y : ℝ) (hβ : 1 < beta)
    (hx_ne : x ≠ 0) (hy_ne : y ≠ 0) :
    FloatSpec.Core.Raux.mag beta (x * y) =
        FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y - 1 ∨
      FloatSpec.Core.Raux.mag beta (x * y) =
        FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y := by
  have htrip := FloatSpec.Core.Raux.mag_mult
    (beta := beta) (x := x) (y := y) hβ hx_ne hy_ne
  have hbounds :
      FloatSpec.Core.Raux.mag beta (x * y) ≤
          FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y ∧
        FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y - 1 ≤
          FloatSpec.Core.Raux.mag beta (x * y) := by
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  omega

/-- Coq: `mag_minus_disj`.

If `y` is at least two binades below positive `x`, then `x - y` has magnitude
`mag x` or `mag x - 1`. -/
theorem mag_minus_disj (x y : ℝ) (hβ : 1 < beta)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hmy : FloatSpec.Core.Raux.mag beta y ≤ FloatSpec.Core.Raux.mag beta x - 2) :
    FloatSpec.Core.Raux.mag beta (x - y) = FloatSpec.Core.Raux.mag beta x ∨
      FloatSpec.Core.Raux.mag beta (x - y) =
        FloatSpec.Core.Raux.mag beta x - 1 := by
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hy_upper :
      y < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta y := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := y) hβ hy_ne
    simpa [FloatSpec.Core.Raux.abs_val, abs_of_pos hy_pos]
      using htrip True.intro
  have hx_lower :
      (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) ≤ x := by
    have htrip := FloatSpec.Core.Raux.mag_lower_bound
      (beta := beta) (x := x) hβ hx_ne
    simpa [FloatSpec.Core.Raux.abs_val, abs_of_pos hx_pos]
      using htrip True.intro
  have hpow_y_le :
      (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta y ≤
        (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 2) := by
    have htrip := FloatSpec.Core.Raux.bpow_le
      (beta := beta)
      (e1 := FloatSpec.Core.Raux.mag beta y)
      (e2 := FloatSpec.Core.Raux.mag beta x - 2) hβ hmy
    simpa [FloatSpec.Core.Raux.bpow_le_check] using htrip True.intro
  have hpow_lt :
      (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 2) <
        (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) := by
    have hlt : FloatSpec.Core.Raux.mag beta x - 2 <
        FloatSpec.Core.Raux.mag beta x - 1 := by omega
    have htrip := FloatSpec.Core.Raux.bpow_lt
      (beta := beta)
      (e1 := FloatSpec.Core.Raux.mag beta x - 2)
      (e2 := FloatSpec.Core.Raux.mag beta x - 1) hβ hlt
    simpa [FloatSpec.Core.Raux.bpow_lt_check] using htrip True.intro
  have hy_lt_x : y < x := by
    linarith
  have hminus := FloatSpec.Core.Raux.mag_minus
    (beta := beta) (x := x) (y := y) hβ hy_pos hy_lt_x
  have hlb := FloatSpec.Core.Raux.mag_minus_lb
    (beta := beta) (x := x) (y := y) hβ hx_pos hy_pos hmy
  have hupper :
      FloatSpec.Core.Raux.mag beta (x - y) ≤
        FloatSpec.Core.Raux.mag beta x := by
    simpa [wp, PostCond.noThrow, Id.run, pure] using hminus True.intro
  have hlower :
      FloatSpec.Core.Raux.mag beta x - 1 ≤
        FloatSpec.Core.Raux.mag beta (x - y) := by
    simpa [wp, PostCond.noThrow, Id.run, pure] using hlb True.intro
  omega

/-- Coq: `mag_minus_separated`.

If positive `x` is generic and strictly above the lower edge of its binade, and
`y` is small enough relative to the canonical exponent at `x`, subtracting `y`
does not change the magnitude of `x`. -/
theorem mag_minus_separated (fexp : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
    (x y : ℝ) (hβ : 1 < beta)
    (hx_pos : 0 < x) (hy_pos : 0 < y) (hyx : y < x)
    (hx_gt_bpow :
      (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) < x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp x)
    (hmy :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp (FloatSpec.Core.Raux.mag beta x)) :
    FloatSpec.Core.Raux.mag beta (x - y) =
      FloatSpec.Core.Raux.mag beta x := by
  let e : Int := FloatSpec.Core.Raux.mag beta x - 1
  let edge : ℝ := (beta : ℝ) ^ e
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hxy_pos : 0 < x - y := sub_pos.mpr hyx
  have hxy_abs : |x - y| = x - y := abs_of_pos hxy_pos
  have hy_upper :
      y < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta y := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := y) hβ hy_ne
    simpa [FloatSpec.Core.Raux.abs_val, abs_of_pos hy_pos]
      using htrip True.intro
  have hpow_y_le :
      (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta y ≤
        (beta : ℝ) ^ (fexp (FloatSpec.Core.Raux.mag beta x)) := by
    have htrip := FloatSpec.Core.Raux.bpow_le
      (beta := beta)
      (e1 := FloatSpec.Core.Raux.mag beta y)
      (e2 := fexp (FloatSpec.Core.Raux.mag beta x)) hβ hmy
    simpa [FloatSpec.Core.Raux.bpow_le_check] using htrip True.intro
  have hy_lt_ulp_edge :
      y < ulp beta fexp edge := by
    have hulp := FloatSpec.Core.Ulp.ulp_bpow
      (beta := beta) (fexp := fexp) (e := e)
    have hulp_eval : ulp beta fexp edge =
        (beta : ℝ) ^ (fexp (FloatSpec.Core.Raux.mag beta x)) := by
      have heq : e + 1 = FloatSpec.Core.Raux.mag beta x := by
        simp [e]
      simpa [edge, e, heq] using hulp hβ
    rw [hulp_eval]
    exact lt_of_lt_of_le hy_upper hpow_y_le
  have hfexp_lt :
      fexp (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp) (x := x)
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp]
      using htrip ⟨hβ, hx_ne, hx_fmt⟩
  have hedge_fmt :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp edge := by
    have hpre :
        fexp (e + 1) ≤ e := by
      have heq : e + 1 = FloatSpec.Core.Raux.mag beta x := by
        simp [e]
      rw [heq]
      omega
    have htrip := FloatSpec.Core.Generic_fmt.generic_format_bpow
      (beta := beta) (fexp := fexp) (e := e)
    simpa [edge] using htrip ⟨hβ, hpre⟩
  have hedge_nonneg : 0 ≤ edge := by
    have hbpos : (0 : ℝ) < (beta : ℝ) := by
      exact_mod_cast (lt_trans Int.zero_lt_one hβ)
    exact le_of_lt (zpow_pos hbpos e)
  have hsucc_eq :
      FloatSpec.Core.Ulp.succ beta fexp edge = edge + ulp beta fexp edge := by
    have htrip := FloatSpec.Core.Ulp.succ_eq_pos
      (beta := beta) (fexp := fexp) (x := edge) hedge_nonneg
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hsucc_le_x :
      FloatSpec.Core.Ulp.succ beta fexp edge ≤ x := by
    have htrip := FloatSpec.Core.Ulp.succ_le_lt
      (beta := beta) (fexp := fexp) (x := edge) (y := x)
      hedge_fmt hx_fmt hx_gt_bpow
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hβ
  have hlow : (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) ≤ |x - y| := by
    have hedge_add_lt : edge + y < edge + ulp beta fexp edge := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_lt_add_left hy_lt_ulp_edge edge
    have hedge_add_le_x : edge + ulp beta fexp edge ≤ x := by
      simpa [hsucc_eq] using hsucc_le_x
    have hedge_add_y_lt_x : edge + y < x :=
      lt_of_lt_of_le hedge_add_lt hedge_add_le_x
    have hedge_lt_sub : edge < x - y := by linarith
    simpa [edge, e, hxy_abs] using le_of_lt hedge_lt_sub
  have hupp : |x - y| < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta x := by
    have hx_upper :
        x < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta x := by
      have htrip := FloatSpec.Core.Raux.mag_upper_bound
        (beta := beta) (x := x) hβ hx_ne
      simpa [FloatSpec.Core.Raux.abs_val, abs_of_pos hx_pos]
        using htrip True.intro
    have hxy_lt_x : x - y < x := by linarith
    simpa [hxy_abs] using lt_trans hxy_lt_x hx_upper
  have hmag := FloatSpec.Core.Raux.mag_unique
    (beta := beta) (x := x - y) (e := FloatSpec.Core.Raux.mag beta x)
    hβ hlow hupp
  simpa [wp, PostCond.noThrow, Id.run, pure] using hmag True.intro

/-- Coq: `round_round_mult_hyp`. -/
def round_round_mult_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex ey, fexp2 (ex + ey) ≤ fexp1 ex + fexp1 ey) ∧
  (∀ ex ey, fexp2 (ex + ey - 1) ≤ fexp1 ex + fexp1 ey)

/-- Coq: `round_round_mult_aux`.

Products of two values in the wider format `fexp1` are representable in
`fexp2` when `round_round_mult_hyp` relates the exponent functions. -/
theorem round_round_mult_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta) (hfexp : round_round_mult_hyp fexp1 fexp2)
    (x y : ℝ) :
    FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
    FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
    FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x * y) := by
  intro hx hy
  by_cases hx0 : x = 0
  · subst x
    simpa using
      (FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp2))
  by_cases hy0 : y = 0
  · subst y
    simpa using
      (FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp2))
  classical
  set ex : Int := FloatSpec.Core.Raux.mag beta x with hex
  set ey : Int := FloatSpec.Core.Raux.mag beta y with hey
  set mx : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 x) with hmx
  set my : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 y) with hmy
  set eprod : Int := fexp1 ex + fexp1 ey with heprod
  have hx_repr : x = ((mx : ℝ) * (beta : ℝ) ^ (fexp1 ex)) := by
    simpa [FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Defs.F2R,
      mx, ex] using hx
  have hy_repr : y = ((my : ℝ) * (beta : ℝ) ^ (fexp1 ey)) := by
    simpa [FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Defs.F2R,
      my, ey] using hy
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hxy_repr :
      x * y = (((mx * my : Int) : ℝ) * (beta : ℝ) ^ eprod) := by
    calc
      x * y
          = ((mx : ℝ) * (beta : ℝ) ^ (fexp1 ex)) *
              ((my : ℝ) * (beta : ℝ) ^ (fexp1 ey)) := by
                rw [hx_repr, hy_repr]
      _ = ((mx : ℝ) * (my : ℝ)) *
              ((beta : ℝ) ^ (fexp1 ex) * (beta : ℝ) ^ (fexp1 ey)) := by ring
      _ = ((mx : ℝ) * (my : ℝ)) *
              (beta : ℝ) ^ (fexp1 ex + fexp1 ey) := by
                rw [(_root_.zpow_add₀ hbne (fexp1 ex) (fexp1 ey)).symm]
      _ = (((mx * my : Int) : ℝ) * (beta : ℝ) ^ eprod) := by
                simp [Int.cast_mul, eprod]
  have hmag_raw := (FloatSpec.Core.Raux.mag_mult beta x y hβ hx0 hy0) (by trivial)
  have hmag :
      FloatSpec.Core.Raux.mag beta (x * y) ≤ ex + ey ∧
        ex + ey - 1 ≤ FloatSpec.Core.Raux.mag beta (x * y) := by
    simpa [ex, ey] using hmag_raw
  have hmag_cases :
      FloatSpec.Core.Raux.mag beta (x * y) = ex + ey ∨
        FloatSpec.Core.Raux.mag beta (x * y) = ex + ey - 1 := by
    grind
  have hcexp_le :
      FloatSpec.Core.Generic_fmt.cexp beta fexp2 (x * y) ≤ eprod := by
    unfold FloatSpec.Core.Generic_fmt.cexp
    rcases hmag_cases with hxy_mag | hxy_mag
    · simpa [hxy_mag, ex, ey, eprod] using hfexp.1 ex ey
    · simpa [hxy_mag, ex, ey, eprod] using hfexp.2 ex ey
  have hprod_eq_f2r :
      x * y =
        FloatSpec.Core.Defs.F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk (mx * my) eprod :
            FloatSpec.Core.Defs.FlocqFloat beta) := by
    simpa [FloatSpec.Core.Defs.F2R] using hxy_repr
  have hfmt_f2r :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp2
        (FloatSpec.Core.Defs.F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk (mx * my) eprod :
            FloatSpec.Core.Defs.FlocqFloat beta)) := by
    exact
      (FloatSpec.Core.Generic_fmt.generic_format_F2R
        (beta := beta) (fexp := fexp2) (m := mx * my) (e := eprod))
        ⟨hβ, by
          intro _
          rw [← hprod_eq_f2r]
          exact hcexp_le⟩
  rw [hxy_repr]
  simpa [FloatSpec.Core.Defs.F2R] using hfmt_f2r

/-- Coq: `round_round_mult`. -/
theorem round_round_mult (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (mode : FloatSpec.Calc.Round.Mode)
    [FloatSpec.Core.Generic_fmt.Valid_rnd mode.rnd]
    (hβ : 1 < beta) (hfexp : round_round_mult_hyp fexp1 fexp2)
    (x y : ℝ) :
    FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
    FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
    FloatSpec.Calc.Round.round beta fexp1 mode
        (FloatSpec.Calc.Round.round beta fexp2 mode (x * y))
      = FloatSpec.Calc.Round.round beta fexp1 mode (x * y) := by
  intro hx hy
  have hxy_format :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x * y) :=
    round_round_mult_aux (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      hβ hfexp x y hx hy
  have hxy_round :
      FloatSpec.Calc.Round.round beta fexp2 mode (x * y) = x * y := by
    unfold FloatSpec.Calc.Round.round
    exact FloatSpec.Core.Generic_fmt.roundR_generic
      (beta := beta) (fexp := fexp2) (rnd := mode.rnd) (x := x * y) hβ hxy_format
  rw [hxy_round]

/-- Coq: `round_round_mult_FLX`. -/
theorem round_round_mult_FLX (prec prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (mode : FloatSpec.Calc.Round.Mode)
    [FloatSpec.Core.Generic_fmt.Valid_rnd mode.rnd]
    (hβ : 1 < beta) :
    2 * prec ≤ prec' →
    ∀ x y,
      FloatSpec.Core.FLX.FLX_format prec beta x →
      FloatSpec.Core.FLX.FLX_format prec beta y →
      FloatSpec.Calc.Round.round beta (FloatSpec.Core.FLX.FLX_exp prec) mode
          (FloatSpec.Calc.Round.round beta (FloatSpec.Core.FLX.FLX_exp prec') mode (x * y))
        = FloatSpec.Calc.Round.round beta (FloatSpec.Core.FLX.FLX_exp prec) mode (x * y) := by
  intro hprec x y hx hy
  have hfexp :
      round_round_mult_hyp
        (FloatSpec.Core.FLX.FLX_exp prec)
        (FloatSpec.Core.FLX.FLX_exp prec') := by
    constructor
    · intro ex ey
      simp [FloatSpec.Core.FLX.FLX_exp]
      grind
    · intro ex ey
      simp [FloatSpec.Core.FLX.FLX_exp]
      grind
  exact
    round_round_mult (beta := beta)
      (fexp1 := FloatSpec.Core.FLX.FLX_exp prec)
      (fexp2 := FloatSpec.Core.FLX.FLX_exp prec')
      (mode := mode) hβ hfexp x y
      (by simpa [FloatSpec.Core.FLX.FLX_format] using hx)
      (by simpa [FloatSpec.Core.FLX.FLX_format] using hy)

/-- Coq: `round_round_mult_FLT`. -/
theorem round_round_mult_FLT (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (mode : FloatSpec.Calc.Round.Mode)
    [FloatSpec.Core.Generic_fmt.Valid_rnd mode.rnd]
    (hβ : 1 < beta) :
    emin' ≤ 2 * emin →
    2 * prec ≤ prec' →
    ∀ x y,
      FloatSpec.Core.FLT.FLT_format prec emin beta x →
      FloatSpec.Core.FLT.FLT_format prec emin beta y →
      FloatSpec.Calc.Round.round beta (FloatSpec.Core.FLT.FLT_exp prec emin) mode
          (FloatSpec.Calc.Round.round beta (FloatSpec.Core.FLT.FLT_exp prec' emin') mode (x * y))
        = FloatSpec.Calc.Round.round beta (FloatSpec.Core.FLT.FLT_exp prec emin) mode (x * y) := by
  intro hemin hprec x y hx hy
  have hfexp :
      round_round_mult_hyp
        (FloatSpec.Core.FLT.FLT_exp prec emin)
        (FloatSpec.Core.FLT.FLT_exp prec' emin') := by
    constructor
    · intro ex ey
      simp [FloatSpec.Core.FLT.FLT_exp]
      grind
    · intro ex ey
      simp [FloatSpec.Core.FLT.FLT_exp]
      grind
  exact
    round_round_mult (beta := beta)
      (fexp1 := FloatSpec.Core.FLT.FLT_exp prec emin)
      (fexp2 := FloatSpec.Core.FLT.FLT_exp prec' emin')
      (mode := mode) hβ hfexp x y
      (by simpa [FloatSpec.Core.FLT.FLT_format] using hx)
      (by simpa [FloatSpec.Core.FLT.FLT_format] using hy)

/-- Coq: `round_round_mult_FTZ`. -/
theorem round_round_mult_FTZ (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (mode : FloatSpec.Calc.Round.Mode)
    [FloatSpec.Core.Generic_fmt.Valid_rnd mode.rnd]
    (hβ : 1 < beta) :
    emin' + prec' ≤ 2 * emin + prec →
    2 * prec ≤ prec' →
    ∀ x y,
      FloatSpec.Core.FTZ.FTZ_format prec emin beta x →
      FloatSpec.Core.FTZ.FTZ_format prec emin beta y →
      FloatSpec.Calc.Round.round beta (FloatSpec.Core.FTZ.FTZ_exp prec emin) mode
          (FloatSpec.Calc.Round.round beta (FloatSpec.Core.FTZ.FTZ_exp prec' emin') mode (x * y))
        = FloatSpec.Calc.Round.round beta (FloatSpec.Core.FTZ.FTZ_exp prec emin) mode (x * y) := by
  intro hemin hprec x y hx hy
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec'_pos : 0 < prec' := (Prec_gt_0.pos : 0 < prec')
  haveI : Fact (0 < prec) := ⟨(Prec_gt_0.pos : 0 < prec)⟩
  haveI : Fact (0 < prec') := ⟨(Prec_gt_0.pos : 0 < prec')⟩
  have hfexp :
      round_round_mult_hyp
        (FloatSpec.Core.FTZ.FTZ_exp prec emin)
        (FloatSpec.Core.FTZ.FTZ_exp prec' emin') := by
    constructor
    · intro ex ey
      unfold FloatSpec.Core.FTZ.FTZ_exp
      split_ifs <;> grind
    · intro ex ey
      unfold FloatSpec.Core.FTZ.FTZ_exp
      split_ifs <;> grind
  exact
    round_round_mult (beta := beta)
      (fexp1 := FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (fexp2 := FloatSpec.Core.FTZ.FTZ_exp prec' emin')
      (mode := mode) hβ hfexp x y
      (by simpa [FloatSpec.Core.FTZ.FTZ_format] using hx)
      (by simpa [FloatSpec.Core.FTZ.FTZ_format] using hy)

/-- Coq: `round_round_sqrt_hyp`. -/
def round_round_sqrt_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex)) ∧
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1)) ∧
  (∀ ex, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - 2)

/-- First interval extraction used by Coq `round_round_sqrt_aux`.

If the desired midpoint gap fails, then `sqrt x` lies between the two
quantities Coq calls `a + b` and `a + b'`, where `a` is the down-rounded
sqrt and `b`, `b'` are the half-ulp offsets. -/
theorem round_round_sqrt_mid_bounds_from_not_gap (fexp1 fexp2 : Int → Int)
    (x : ℝ)
    (hnot :
      ¬ ((1 / 2) * ulp beta fexp2 (Real.sqrt x) <
          |Real.sqrt x - midp beta fexp1 (Real.sqrt x)|)) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    let u1 := ulp beta fexp1 (Real.sqrt x)
    let u2 := ulp beta fexp2 (Real.sqrt x)
    a + (1 / 2) * (u1 - u2) ≤ Real.sqrt x ∧
      Real.sqrt x ≤ a + (1 / 2) * (u1 + u2) := by
  classical
  dsimp
  have hle :
      |Real.sqrt x - midp beta fexp1 (Real.sqrt x)| ≤
        (1 / 2) * ulp beta fexp2 (Real.sqrt x) := le_of_not_gt hnot
  have hbounds := abs_le.mp hle
  unfold midp at hbounds
  constructor <;> linarith

/-- Square the interval bounds used by Coq `round_round_sqrt_aux`.

This packages the two Coq assertions `Hsl` and `Hsr`: if `sqrt x` lies between
`a + b` and `a + b'`, then squaring those nonnegative endpoints gives the
corresponding lower and upper bounds on `x`. -/
theorem round_round_sqrt_sq_bounds_from_interval (x a u1 u2 b bp : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hb : b = (1 / 2) * (u1 - u2))
    (hbp : bp = (1 / 2) * (u1 + u2))
    (hl_nonneg : 0 ≤ a + b)
    (hr_nonneg : 0 ≤ a + bp)
    (hl : a + b ≤ Real.sqrt x)
    (hr : Real.sqrt x ≤ a + bp) :
    a * a + u1 * a - u2 * a + b * b ≤ x ∧
      x ≤ a * a + u1 * a + u2 * a + bp * bp := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hlower_mul :
      (a + b) * (a + b) ≤ Real.sqrt x * Real.sqrt x :=
    mul_le_mul hl hl hl_nonneg hsqrt_nonneg
  have hupper_mul :
      Real.sqrt x * Real.sqrt x ≤ (a + bp) * (a + bp) :=
    mul_le_mul hr hr hsqrt_nonneg hr_nonneg
  have hsqrt_sq : Real.sqrt x * Real.sqrt x = x := by
    simpa [pow_two] using Real.sq_sqrt hx_nonneg
  rw [hsqrt_sq] at hlower_mul hupper_mul
  have hb_two : 2 * b = u1 - u2 := by
    nlinarith [hb]
  have hbp_two : 2 * bp = u1 + u2 := by
    nlinarith [hbp]
  have hlower_id :
      a * a + u1 * a - u2 * a + b * b = (a + b) * (a + b) := by
    calc
      a * a + u1 * a - u2 * a + b * b =
          a * a + (u1 - u2) * a + b * b := by ring
      _ = a * a + (2 * b) * a + b * b := by rw [← hb_two]
      _ = (a + b) * (a + b) := by ring
  have hupper_id :
      a * a + u1 * a + u2 * a + bp * bp = (a + bp) * (a + bp) := by
    calc
      a * a + u1 * a + u2 * a + bp * bp =
          a * a + (u1 + u2) * a + bp * bp := by ring
      _ = a * a + (2 * bp) * a + bp * bp := by rw [← hbp_two]
      _ = (a + bp) * (a + bp) := by ring
  constructor
  · simpa [hlower_id] using hlower_mul
  · simpa [hupper_id] using hupper_mul

/-- Positivity of the half-ulp offsets in Coq `round_round_sqrt_aux`.

This packages Coq's `Phu1`, `Phu2`, `Pb`, and `Pb'` facts after rewriting
the nonzero ULPs of `sqrt x` to powers. -/
theorem round_round_sqrt_offsets_pos (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1) :
    let u1 := ulp beta fexp1 (Real.sqrt x)
    let u2 := ulp beta fexp2 (Real.sqrt x)
    let b := (1 / 2) * (u1 - u2)
    let bp := (1 / 2) * (u1 + u2)
    0 < (1 / 2) * u1 ∧ 0 < (1 / 2) * u2 ∧ 0 < b ∧ 0 < bp := by
  classical
  dsimp
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hsqrt_ne : Real.sqrt x ≠ 0 := ne_of_gt hsqrt_pos
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hhalf_pos : (0 : ℝ) < (1 / 2) := by norm_num
  have hu1_eq :
      ulp beta fexp1 (Real.sqrt x) =
        (beta : ℝ) ^
          fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := Real.sqrt x) hsqrt_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp] using htrip True.intro
  have hu2_eq :
      ulp beta fexp2 (Real.sqrt x) =
        (beta : ℝ) ^
          fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp2) (x := Real.sqrt x) hsqrt_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp] using htrip True.intro
  have hu1_pos : 0 < ulp beta fexp1 (Real.sqrt x) := by
    simpa [hu1_eq] using
      zpow_pos hbposR (fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)))
  have hu2_pos : 0 < ulp beta fexp2 (Real.sqrt x) := by
    simpa [hu2_eq] using
      zpow_pos hbposR (fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)))
  have hf2_lt :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) <
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) := by
    omega
  have hu2_lt_u1 :
      ulp beta fexp2 (Real.sqrt x) <
        ulp beta fexp1 (Real.sqrt x) := by
    rw [hu1_eq, hu2_eq]
    exact zpow_lt_zpow_right₀ hβR hf2_lt
  constructor
  · exact mul_pos hhalf_pos hu1_pos
  constructor
  · exact mul_pos hhalf_pos hu2_pos
  constructor
  · exact mul_pos hhalf_pos (sub_pos.mpr hu2_lt_u1)
  · exact mul_pos hhalf_pos (add_pos hu1_pos hu2_pos)

/-- Upper-endpoint estimate in the `a = 0` branch of Coq
`round_round_sqrt_aux`.

If the floor rounding `a` of `sqrt x` is zero, the upper interval bound
`sqrt x <= a + b'` and the exponent gap `fexp2 <= fexp1 - 1` force
`sqrt x < beta^(fexp1 (mag (sqrt x)))`. -/
theorem round_round_sqrt_sqrt_lt_bpow_of_zero_floor
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta) (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    let u1 := ulp beta fexp1 (Real.sqrt x)
    let u2 := ulp beta fexp2 (Real.sqrt x)
    a = 0 →
    Real.sqrt x ≤ a + (1 / 2) * (u1 + u2) →
    Real.sqrt x <
      (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) := by
  classical
  dsimp
  intro ha0 hr
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hsqrt_ne : Real.sqrt x ≠ 0 := ne_of_gt hsqrt_pos
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hu1_eq :
      ulp beta fexp1 (Real.sqrt x) =
        (beta : ℝ) ^
          fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := Real.sqrt x) hsqrt_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp] using htrip True.intro
  have hu2_eq :
      ulp beta fexp2 (Real.sqrt x) =
        (beta : ℝ) ^
          fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp2) (x := Real.sqrt x) hsqrt_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp] using htrip True.intro
  have hf2_lt :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) <
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) := by
    omega
  have hu2_lt_u1 :
      ulp beta fexp2 (Real.sqrt x) <
        ulp beta fexp1 (Real.sqrt x) := by
    rw [hu1_eq, hu2_eq]
    exact zpow_lt_zpow_right₀ hβR hf2_lt
  have hsqrt_le_bp :
      Real.sqrt x ≤
        (1 / 2) *
          (ulp beta fexp1 (Real.sqrt x) + ulp beta fexp2 (Real.sqrt x)) := by
    simpa [ha0] using hr
  have hbp_lt_u1 :
      (1 / 2) *
          (ulp beta fexp1 (Real.sqrt x) + ulp beta fexp2 (Real.sqrt x)) <
        ulp beta fexp1 (Real.sqrt x) := by
    nlinarith [hu2_lt_u1]
  have hsqrt_lt_u1 :
      Real.sqrt x < ulp beta fexp1 (Real.sqrt x) :=
    lt_of_le_of_lt hsqrt_le_bp hbp_lt_u1
  simpa [hu1_eq] using hsqrt_lt_u1

/-- Floor-style `roundR` is nonnegative on nonnegative inputs.

This is the direct Lean counterpart of the Coq step
`rewrite <- round_0; apply round_le` used in `round_round_sqrt_aux`. -/
theorem roundR_floor_nonneg (fexp : Int → Int) (x : ℝ)
    (hβ : 1 < beta) (hx_nonneg : 0 ≤ x) :
    0 ≤ FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Generic_fmt.rnd_floor x := by
  classical
  set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x with he
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x with hsm
  set n : Int := FloatSpec.Core.Generic_fmt.rnd_floor sm with hn
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR e
  have hscale_nonneg : 0 ≤ (beta : ℝ) ^ (-e) :=
    le_of_lt (zpow_pos hbposR (-e))
  have hsm_nonneg : 0 ≤ sm := by
    have hsm_def : sm = x * (beta : ℝ) ^ (-e) := by
      simpa [sm, hsm, e, he, FloatSpec.Core.Generic_fmt.scaled_mantissa]
    simpa [hsm_def] using mul_nonneg hx_nonneg hscale_nonneg
  have hn_nonneg_int : (0 : Int) ≤ n := by
    have hfloor_nonneg : (0 : Int) ≤ Int.floor sm :=
      Int.floor_nonneg.mpr hsm_nonneg
    simpa [n, hn, FloatSpec.Core.Generic_fmt.rnd_floor,
      FloatSpec.Core.Raux.Zfloor] using hfloor_nonneg
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast hn_nonneg_int
  have hround_eval :
      FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_floor x =
        (n : ℝ) * (beta : ℝ) ^ e := by
    simpa [FloatSpec.Core.Generic_fmt.roundR, sm, hsm, n, hn, e, he]
  rw [hround_eval]
  exact mul_nonneg hn_nonneg (le_of_lt hpow_pos)

/-- Coq `round_round_sqrt_aux` fact `Nna`: the floor-rounded square root is
nonnegative. -/
theorem round_round_sqrt_floor_nonneg (fexp : Int → Int) (x : ℝ)
    (hβ : 1 < beta) :
    0 ≤ FloatSpec.Core.Generic_fmt.roundR beta fexp
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x) :=
  roundR_floor_nonneg (beta := beta) (fexp := fexp) (x := Real.sqrt x)
    hβ (Real.sqrt_nonneg x)

/-- Scaled-mantissa bound used in the `a = 0` branch of Coq
`round_round_sqrt_aux`.

After the branch inequalities show `x < beta^(2 * e)`, and the exponent
hypothesis gives `2 * e ≤ fexp (mag x)`, the first-format scaled mantissa of
`x` is strictly below one. -/
theorem round_round_sqrt_scaled_mantissa_lt_one_from_pow (fexp : Int → Int)
    (x : ℝ) (e : Int)
    (hβ : 1 < beta) (hx_nonneg : 0 ≤ x)
    (hx_lt : x < (beta : ℝ) ^ (2 * e))
    (hexp :
      2 * e ≤ fexp (FloatSpec.Core.Raux.mag beta x)) :
    |FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x| < 1 := by
  classical
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  let m : Int := FloatSpec.Core.Raux.mag beta x
  have hscale_pos : 0 < ((beta : ℝ) ^ (fexp m))⁻¹ :=
    inv_pos.mpr (zpow_pos hbposR (fexp m))
  have hstep :
      x * ((beta : ℝ) ^ (fexp m))⁻¹ <
        (beta : ℝ) ^ (2 * e) * ((beta : ℝ) ^ (fexp m))⁻¹ := by
    exact mul_lt_mul_of_pos_right hx_lt hscale_pos
  have hneg :
      (beta : ℝ) ^ (-(fexp m)) = ((beta : ℝ) ^ (fexp m))⁻¹ := by
    simp [zpow_neg]
  have hprod :
      (beta : ℝ) ^ (2 * e) * ((beta : ℝ) ^ (fexp m))⁻¹ =
        (beta : ℝ) ^ (2 * e - fexp m) := by
    rw [← hneg]
    simpa [sub_eq_add_neg] using
      (zpow_add₀ hbne (2 * e) (-(fexp m))).symm
  have hdiff_le : 2 * e - fexp m ≤ 0 := by
    exact sub_nonpos.mpr (by simpa [m] using hexp)
  have hpow_le_one :
      (beta : ℝ) ^ (2 * e - fexp m) ≤ 1 := by
    have hpow_le :
        (beta : ℝ) ^ (2 * e - fexp m) ≤ (beta : ℝ) ^ (0 : Int) :=
      (zpow_right_strictMono₀ hβR).monotone hdiff_le
    simpa using hpow_le
  have hlt :
      x * ((beta : ℝ) ^ (fexp m))⁻¹ < 1 :=
    lt_of_lt_of_le (by simpa [hprod] using hstep) hpow_le_one
  have hscaled_eval :
      FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x =
        x * ((beta : ℝ) ^ (fexp m))⁻¹ := by
    simp [FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Generic_fmt.cexp, m, zpow_neg]
  have hscaled_nonneg :
      0 ≤ x * ((beta : ℝ) ^ (fexp m))⁻¹ :=
    mul_nonneg hx_nonneg (le_of_lt hscale_pos)
  simpa [hscaled_eval, abs_of_nonneg hscaled_nonneg] using hlt

/-- A nonnegative formatted value with scaled mantissa below one is zero.

This is the final normalization step needed after the `a = 0` branch of Coq
`round_round_sqrt_aux` derives a strict scaled-mantissa bound for `x`. -/
theorem generic_format_eq_zero_of_scaled_mantissa_lt_one (fexp : Int → Int)
    (x : ℝ) (hβ : 1 < beta)
    (hx_nonneg : 0 ≤ x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp x)
    (hsm_lt :
      |FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x| < 1) :
    x = 0 := by
  classical
  set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x with he
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x with hsm
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hscale_nonneg : 0 ≤ (beta : ℝ) ^ (-e) :=
    le_of_lt (zpow_pos hbposR (-e))
  have hsm_nonneg : 0 ≤ sm := by
    have hsm_eval : sm = x * (beta : ℝ) ^ (-e) := by
      simpa [sm, hsm, e, he, FloatSpec.Core.Generic_fmt.scaled_mantissa]
    simpa [hsm_eval] using mul_nonneg hx_nonneg hscale_nonneg
  have hsm_lt_one : sm < 1 := by
    have hsm_abs : |sm| < 1 := by simpa [sm, hsm] using hsm_lt
    exact lt_of_le_of_lt (le_abs_self sm) hsm_abs
  have hfloor_eq : Int.floor sm = 0 := by
    have hfloor_nonneg : (0 : Int) ≤ Int.floor sm :=
      Int.floor_nonneg.mpr hsm_nonneg
    have hsm_lt_one_int : sm < ((1 : Int) : ℝ) := by
      simpa using hsm_lt_one
    have hfloor_lt_one : Int.floor sm < 1 :=
      Int.floor_lt.mpr hsm_lt_one_int
    omega
  have htrunc_zero : FloatSpec.Core.Raux.Ztrunc sm = 0 := by
    simp [FloatSpec.Core.Raux.Ztrunc, not_lt.mpr hsm_nonneg, hfloor_eq]
  have hx_repr :
      x =
        ((FloatSpec.Core.Raux.Ztrunc sm : Int) : ℝ) *
          (beta : ℝ) ^ e := by
    simpa [FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Defs.F2R,
      sm, hsm, e, he] using hx_fmt
  simpa [htrunc_zero] using hx_repr

/-- Contradiction package for the `a = 0` branch of Coq
`round_round_sqrt_aux`.

Once the branch has shown `sqrt x < beta^e`, the exponent hypothesis turns this
into a scaled-mantissa bound for `x`; a positive formatted `x` then cannot
exist. -/
theorem round_round_sqrt_pos_contra_of_sqrt_lt_bpow (fexp : Int → Int)
    (x : ℝ) (e : Int)
    (hβ : 1 < beta)
    (hx_pos : 0 < x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp x)
    (hsqrt_lt : Real.sqrt x < (beta : ℝ) ^ e)
    (hexp :
      2 * e ≤ fexp (FloatSpec.Core.Raux.mag beta x)) :
    False := by
  classical
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR e
  have hsqrt_sq_lt :
      (Real.sqrt x) ^ 2 < ((beta : ℝ) ^ e) ^ 2 := by
    nlinarith [hsqrt_lt, hsqrt_nonneg, hpow_pos]
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hx_pos)
  have hpow_sq :
      ((beta : ℝ) ^ e) ^ 2 = (beta : ℝ) ^ (2 * e) := by
    simpa [pow_two, two_mul] using (zpow_add₀ hbne e e).symm
  have hx_lt : x < (beta : ℝ) ^ (2 * e) := by
    simpa [hsqrt_sq, hpow_sq] using hsqrt_sq_lt
  have hsm_lt :
      |FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x| < 1 :=
    round_round_sqrt_scaled_mantissa_lt_one_from_pow
      (beta := beta) (fexp := fexp) (x := x) (e := e)
      hβ (le_of_lt hx_pos) hx_lt hexp
  have hx_zero :
      x = 0 :=
    generic_format_eq_zero_of_scaled_mantissa_lt_one
      (beta := beta) (fexp := fexp) (x := x)
      hβ (le_of_lt hx_pos) hx_fmt hsm_lt
  exact (ne_of_gt hx_pos) hx_zero

/-- The `a = 0` contradiction branch of Coq `round_round_sqrt_aux`.

Here `a` is the first-format floor rounding of `sqrt x`.  The upper interval
bound gives `sqrt x < beta^(fexp1 (mag (sqrt x)))`; the generic-format and
exponent hypotheses then force the positive value `x` to be zero. -/
theorem round_round_sqrt_zero_floor_contra
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hf1 :
      2 * fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x)) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    let u1 := ulp beta fexp1 (Real.sqrt x)
    let u2 := ulp beta fexp2 (Real.sqrt x)
    a = 0 →
    Real.sqrt x ≤ a + (1 / 2) * (u1 + u2) →
    False := by
  classical
  dsimp
  intro ha0 hr
  have hsqrt_lt :
      Real.sqrt x <
        (beta : ℝ) ^
          fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) :=
    round_round_sqrt_sqrt_lt_bpow_of_zero_floor
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ hx_pos hf2 ha0 hr
  exact
    round_round_sqrt_pos_contra_of_sqrt_lt_bpow
      (beta := beta) (fexp := fexp1) (x := x)
      (e := fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)))
      hβ hx_pos hx_fmt hsqrt_lt hf1

/-- The `a = 0` branch specialized to the negated midpoint-gap case in Coq
`round_round_sqrt_aux`.

This derives the exponent inequality `Hf1` from `round_round_sqrt_hyp` and
uses `round_round_sqrt_mid_bounds_from_not_gap` for the upper interval bound. -/
theorem round_round_sqrt_zero_floor_contra_from_not_gap
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hnot :
      ¬ ((1 / 2) * ulp beta fexp2 (Real.sqrt x) <
          |Real.sqrt x - midp beta fexp1 (Real.sqrt x)|)) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    a = 0 →
    False := by
  classical
  dsimp
  intro ha0
  have hbounds :=
    round_round_sqrt_mid_bounds_from_not_gap
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hnot
  have hf1 :
      2 * fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) := by
    rcases mag_sqrt_disj (beta := beta) x hβ hx_pos with hmag | hmag
    · simpa [hmag] using
        Hexp.2.1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x))
    · simpa [hmag] using
        Hexp.1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x))
  exact
    round_round_sqrt_zero_floor_contra
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ hx_pos hf2 hx_fmt hf1 ha0 hbounds.2

/-- Coq's `Hf1` exponent side condition, stated in the `cexp` form needed for
the scaled-integer `Hr'` reduction.

This is the same `mag_sqrt_disj` case split used in the zero-floor branch:
`round_round_sqrt_hyp` supplies the lower bound at either `2*mag(sqrt x)` or
`2*mag(sqrt x)-1`, and `cexp x` unfolds to `fexp1 (mag x)`. -/
theorem round_round_sqrt_target_le_cexp_from_hyp
    (fexp1 fexp2 : Int → Int)
    (x : ℝ) (hβ : 1 < beta)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (hx_pos : 0 < x) :
    2 * fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
      FloatSpec.Core.Generic_fmt.cexp beta fexp1 x := by
  classical
  rcases mag_sqrt_disj (beta := beta) x hβ hx_pos with hmag | hmag
  · simpa [FloatSpec.Core.Generic_fmt.cexp, hmag] using
      Hexp.2.1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x))
  · simpa [FloatSpec.Core.Generic_fmt.cexp, hmag] using
      Hexp.1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x))

/-- Algebraic residual positivity in the `a ≠ 0` branch of Coq
`round_round_sqrt_aux`.

Coq proves the transformed inequality
`u2 * (a + 1/2*u1) < 1/4*(u2^2 + u1^2)` by bounding the center point by
`beta^(mag (sqrt x))` and then using the exponent hypothesis. This lemma
packages the final algebraic conversion of that transformed inequality into
`0 < -(u2*a) + b*b`, where `b = 1/2*(u1-u2)`. -/
theorem round_round_sqrt_residual_pos_of_transformed_bound
    (a u1 u2 b : ℝ)
    (hb : b = (1 / 2) * (u1 - u2))
    (htrans :
      u2 * (a + (1 / 2) * u1) <
        (1 / 4) * (u2 ^ 2 + u1 ^ 2)) :
    0 < -(u2 * a) + b * b := by
  subst b
  nlinarith

/-- Residual positivity in the `a ≠ 0` branch from the two inequalities Coq
proves before the final algebraic step.

If the center point is strictly below `B` and `u2 * B` is bounded by the
quarter-square sum, then the residual
`-(u2*a) + (1/2*(u1-u2))^2` is positive. -/
theorem round_round_sqrt_residual_pos_from_bounds
    (a u1 u2 b B : ℝ)
    (hb : b = (1 / 2) * (u1 - u2))
    (hu2_pos : 0 < u2)
    (hcenter : a + (1 / 2) * u1 < B)
    (hB :
      u2 * B ≤ (1 / 4) * (u2 ^ 2 + u1 ^ 2)) :
    0 < -(u2 * a) + b * b := by
  have htrans :
      u2 * (a + (1 / 2) * u1) <
        (1 / 4) * (u2 ^ 2 + u1 ^ 2) := by
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hcenter hu2_pos) hB
  exact round_round_sqrt_residual_pos_of_transformed_bound
    (a := a) (u1 := u1) (u2 := u2) (b := b) hb htrans

/-- Power bound used in the `a ≠ 0` residual estimate of Coq
`round_round_sqrt_aux`.

For `u1 = beta^e1` and `u2 = beta^e2`, the exponent gap
`e2 + m <= 2*e1 - 2` gives
`u2 * beta^m <= beta^(-2) * u1^2`; since `2 <= beta`, this is at most
`1/4 * (u2^2 + u1^2)`. -/
theorem round_round_sqrt_u2_bpow_le_quarter_sum
    (e1 e2 m : Int) (u1 u2 : ℝ)
    (hβ : 1 < beta)
    (hu1 : u1 = (beta : ℝ) ^ e1)
    (hu2 : u2 = (beta : ℝ) ^ e2)
    (hexp : e2 + m ≤ 2 * e1 - 2) :
    u2 * (beta : ℝ) ^ m ≤ (1 / 4) * (u2 ^ 2 + u1 ^ 2) := by
  classical
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hmul_pow :
      u2 * (beta : ℝ) ^ m = (beta : ℝ) ^ (e2 + m) := by
    calc
      u2 * (beta : ℝ) ^ m = (beta : ℝ) ^ e2 * (beta : ℝ) ^ m := by
        rw [hu2]
      _ = (beta : ℝ) ^ (e2 + m) := by
        exact (zpow_add₀ hbne e2 m).symm
  have hpow_gap :
      (beta : ℝ) ^ (e2 + m) ≤ (beta : ℝ) ^ (2 * e1 - 2) :=
    (zpow_right_strictMono₀ hβR).monotone hexp
  have hpow_id :
      (beta : ℝ) ^ (2 * e1 - 2) =
        (beta : ℝ) ^ (-2 : Int) * ((beta : ℝ) ^ e1) ^ 2 := by
    have hidx : 2 * e1 - 2 = (-2 : Int) + e1 + e1 := by ring
    calc
      (beta : ℝ) ^ (2 * e1 - 2) =
          (beta : ℝ) ^ ((-2 : Int) + e1 + e1) := by rw [hidx]
      _ = (beta : ℝ) ^ ((-2 : Int) + e1) * (beta : ℝ) ^ e1 := by
        exact zpow_add₀ hbne ((-2 : Int) + e1) e1
      _ = ((beta : ℝ) ^ (-2 : Int) * (beta : ℝ) ^ e1) *
          (beta : ℝ) ^ e1 := by
        rw [zpow_add₀ hbne (-2 : Int) e1]
      _ = (beta : ℝ) ^ (-2 : Int) * ((beta : ℝ) ^ e1) ^ 2 := by ring
  have hleft :
      u2 * (beta : ℝ) ^ m ≤ (beta : ℝ) ^ (-2 : Int) * u1 ^ 2 := by
    calc
      u2 * (beta : ℝ) ^ m = (beta : ℝ) ^ (e2 + m) := hmul_pow
      _ ≤ (beta : ℝ) ^ (2 * e1 - 2) := hpow_gap
      _ = (beta : ℝ) ^ (-2 : Int) * u1 ^ 2 := by
        simpa [hu1] using hpow_id
  have hb_ge2ℤ : (2 : Int) ≤ beta := by omega
  have hb_ge2R : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hb_ge2ℤ
  have hb_sq_ge4 : (4 : ℝ) ≤ (beta : ℝ) ^ 2 := by
    nlinarith
  have hcoeff :
      (beta : ℝ) ^ (-2 : Int) ≤ (1 / 4 : ℝ) := by
    have hb_sq_pos : 0 < (beta : ℝ) ^ 2 := sq_pos_of_ne_zero hbne
    have hinv : (((beta : ℝ) ^ 2)⁻¹) ≤ ((4 : ℝ)⁻¹) :=
      (inv_le_inv₀ hb_sq_pos (by norm_num : (0 : ℝ) < 4)).2 hb_sq_ge4
    have hneg : (beta : ℝ) ^ (-2 : Int) = (((beta : ℝ) ^ 2)⁻¹) := by
      simp [zpow_neg, pow_two]
      field_simp [hbne]
    have hfour : ((4 : ℝ)⁻¹) = (1 / 4 : ℝ) := by norm_num
    rw [hneg]
    calc
      (((beta : ℝ) ^ 2)⁻¹) ≤ ((4 : ℝ)⁻¹) := hinv
      _ = (1 / 4 : ℝ) := hfour
  have hcoeff_mul :
      (beta : ℝ) ^ (-2 : Int) * u1 ^ 2 ≤ (1 / 4 : ℝ) * u1 ^ 2 :=
    mul_le_mul_of_nonneg_right hcoeff (sq_nonneg u1)
  have hquarter :
      (1 / 4 : ℝ) * u1 ^ 2 ≤ (1 / 4 : ℝ) * (u2 ^ 2 + u1 ^ 2) := by
    nlinarith [sq_nonneg u2]
  exact le_trans hleft (le_trans hcoeff_mul hquarter)

/-- Center-point bound in the `a ≠ 0` branch of Coq
`round_round_sqrt_aux`.

For the positive floor rounding `a = round_DN (sqrt x)`, Coq uses
`mag_DN`, `cexp_DN`, `round_DN_pt`, and `id_p_ulp_le_bpow` to show that the
midpoint center `a + 1/2*u1` is strictly below the binade upper bound of
`sqrt x`. -/
theorem round_round_sqrt_center_lt_bpow_of_pos_floor
    (fexp1 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (x : ℝ) (hβ : 1 < beta) (hx_pos : 0 < x) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    let u1 := ulp beta fexp1 (Real.sqrt x)
    0 < a →
      a + (1 / 2) * u1 <
        (beta : ℝ) ^
          FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
  classical
  dsimp
  intro ha_pos
  set s : ℝ := Real.sqrt x with hs
  set a : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_floor s with ha
  set u1 : ℝ := ulp beta fexp1 s with hu1
  have hs_pos : 0 < s := by
    simpa [s, hs] using Real.sqrt_pos.mpr hx_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hdn :
      FloatSpec.Core.Defs.Rnd_DN_pt
        (fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) s a := by
    simpa [a, ha] using
      FloatSpec.Core.Generic_fmt.round_DN_pt
        (beta := beta) (fexp := fexp1) (x := s) hβ
  have ha_fmt :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 a := hdn.1
  have ha_le_s : a ≤ s := hdn.2.1
  have hs_lt_bpow :
      s < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := s) hβ hs_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Raux.abs_val, abs_of_pos hs_pos] using htrip True.intro
  have ha_lt_bpow :
      a < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s :=
    lt_of_le_of_lt ha_le_s hs_lt_bpow
  have hid :
      a + ulp beta fexp1 a ≤
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s := by
    have htrip := FloatSpec.Core.Ulp.id_p_ulp_le_bpow
      (beta := beta) (fexp := fexp1) (x := a)
      (e := FloatSpec.Core.Raux.mag beta s)
      ha_pos ha_fmt ha_lt_bpow
    simpa [wp, PostCond.noThrow, Id.run, bind, pure] using htrip hβ
  have hcexp :
      FloatSpec.Core.Generic_fmt.cexp beta fexp1 a =
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 s := by
    have htrip := FloatSpec.Core.Generic_fmt.cexp_DN
      (beta := beta) (fexp := fexp1) (x := s)
    have himp :
        0 <
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor s →
          FloatSpec.Core.Generic_fmt.cexp beta fexp1
              (FloatSpec.Core.Generic_fmt.roundR beta fexp1
                FloatSpec.Core.Generic_fmt.rnd_floor s) =
            FloatSpec.Core.Generic_fmt.cexp beta fexp1 s := by
      simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hβ
    simpa [a, ha] using himp (by simpa [a, ha] using ha_pos)
  have hulp_a :
      ulp beta fexp1 a =
        (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 a := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := a) ha_ne
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hulp_s :
      ulp beta fexp1 s =
        (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 s := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := s) hs_ne
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hulp_eq : ulp beta fexp1 a = u1 := by
    calc
      ulp beta fexp1 a =
          (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 a := hulp_a
      _ = (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 s := by
        rw [hcexp]
      _ = ulp beta fexp1 s := by rw [hulp_s]
      _ = u1 := by rw [hu1]
  have hu1_pos : 0 < u1 := by
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    rw [← hulp_eq, hulp_a]
    exact zpow_pos hbposR _
  have hhalf_lt : (1 / 2) * u1 < u1 := by
    nlinarith [hu1_pos]
  have hcenter_lt : a + (1 / 2) * u1 < a + ulp beta fexp1 a := by
    nlinarith [hhalf_lt, hulp_eq]
  exact lt_of_lt_of_le hcenter_lt hid

/-- Residual positivity in the `a ≠ 0` branch once the Coq exponent side
condition has been isolated.

This composes the center estimate for positive floor rounding with the
quarter-square power estimate. The remaining upstream work is to derive the
`hexp` premise from `round_round_sqrt_hyp` in the relevant square-root
magnitude case and plug this into the final interval contradiction. -/
theorem round_round_sqrt_residual_pos_from_pos_floor_and_exp
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta) (hx_pos : 0 < x)
    (hexp :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) +
          FloatSpec.Core.Raux.mag beta (Real.sqrt x) ≤
        2 * fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 2) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    let u1 := ulp beta fexp1 (Real.sqrt x)
    let u2 := ulp beta fexp2 (Real.sqrt x)
    let b := (1 / 2) * (u1 - u2)
    0 < a → 0 < -(u2 * a) + b * b := by
  classical
  dsimp
  intro ha_pos
  set s : ℝ := Real.sqrt x with hs
  set a : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_floor s with ha
  set u1 : ℝ := ulp beta fexp1 s with hu1
  set u2 : ℝ := ulp beta fexp2 s with hu2
  set b : ℝ := (1 / 2) * (u1 - u2) with hb
  have hs_pos : 0 < s := by
    simpa [s, hs] using Real.sqrt_pos.mpr hx_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hu1_pow :
      u1 =
        (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta s) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := s) hs_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp, u1, hu1] using htrip True.intro
  have hu2_pow :
      u2 =
        (beta : ℝ) ^ fexp2 (FloatSpec.Core.Raux.mag beta s) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp2) (x := s) hs_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp, u2, hu2] using htrip True.intro
  have hu2_pos : 0 < u2 := by
    rw [hu2_pow]
    exact zpow_pos hbposR _
  have hcenter :
      a + (1 / 2) * u1 <
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s := by
    have h := round_round_sqrt_center_lt_bpow_of_pos_floor
      (beta := beta) (fexp1 := fexp1) (x := x) hβ hx_pos
    simpa [s, hs, a, ha, u1, hu1] using h (by simpa [a, ha] using ha_pos)
  have hexp_s :
      fexp2 (FloatSpec.Core.Raux.mag beta s) +
          FloatSpec.Core.Raux.mag beta s ≤
        2 * fexp1 (FloatSpec.Core.Raux.mag beta s) - 2 := by
    simpa [s, hs] using hexp
  have hB :
      u2 * (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s ≤
        (1 / 4) * (u2 ^ 2 + u1 ^ 2) :=
    round_round_sqrt_u2_bpow_le_quarter_sum
      (beta := beta)
      (e1 := fexp1 (FloatSpec.Core.Raux.mag beta s))
      (e2 := fexp2 (FloatSpec.Core.Raux.mag beta s))
      (m := FloatSpec.Core.Raux.mag beta s)
      (u1 := u1) (u2 := u2) hβ hu1_pow hu2_pow hexp_s
  exact
    round_round_sqrt_residual_pos_from_bounds
      (a := a) (u1 := u1) (u2 := u2) (b := b)
      (B := (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s)
      (by rw [hb]) hu2_pos hcenter hB

/-- Exponent side condition used by Coq in the `a ≠ 0` branch of
`round_round_sqrt_aux`.

This factors the recurring derivation of
`fexp2 (mag (sqrt x)) + mag (sqrt x) <= 2*fexp1 (mag (sqrt x)) - 2`
from `round_round_sqrt_hyp`, `mag_sqrt_disj`, and the generic-format
magnitude fact for `x`. -/
theorem round_round_sqrt_exp_premise_from_hyp
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (x : ℝ) (hβ : 1 < beta)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) +
        FloatSpec.Core.Raux.mag beta (Real.sqrt x) ≤
      2 * fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 2 := by
  classical
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hfx_lt :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp1) x
    have hcexp_lt :
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 x <
          FloatSpec.Core.Raux.mag beta x := by
      simpa [wp, PostCond.noThrow, Id.run, pure] using
        htrip ⟨hβ, hx_ne, hx_fmt⟩
    simpa [FloatSpec.Core.Generic_fmt.cexp] using hcexp_lt
  have hlarge :
      fexp1 (2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x)) <
        2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
    rcases mag_sqrt_disj (beta := beta) x hβ hx_pos with hmag | hmag
    · apply FloatSpec.Core.Generic_fmt.valid_exp_large
        (beta := beta) (fexp := fexp1)
        (k := FloatSpec.Core.Raux.mag beta x)
        (l := 2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x))
        hfx_lt
      omega
    · simpa [← hmag] using hfx_lt
  exact Hexp.2.2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) hlarge

/-- Residual positivity in the `a ≠ 0` branch directly from
`round_round_sqrt_hyp` and the generic-format assumption on `x`. -/
theorem round_round_sqrt_residual_pos_from_pos_floor
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    let u1 := ulp beta fexp1 (Real.sqrt x)
    let u2 := ulp beta fexp2 (Real.sqrt x)
    let b := (1 / 2) * (u1 - u2)
    0 < a → 0 < -(u2 * a) + b * b := by
  classical
  have hexp :=
    round_round_sqrt_exp_premise_from_hyp
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ Hexp hx_pos hx_fmt
  exact
    round_round_sqrt_residual_pos_from_pos_floor_and_exp
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ hx_pos hexp

/-- Final algebraic contradiction shape in the `a ≠ 0` branch of Coq
`round_round_sqrt_aux`.

After Coq reduces the upper bound to `x <= a*a + u1*a`, the lower square
bound and positive residual `0 < -(u2*a) + b*b` are inconsistent. -/
theorem round_round_sqrt_nonzero_residual_contra
    (x a u1 u2 b : ℝ)
    (hsl : a * a + u1 * a - u2 * a + b * b ≤ x)
    (hr : x ≤ a * a + u1 * a)
    (hres : 0 < -(u2 * a) + b * b) :
    False := by
  nlinarith

/-- Tail estimate used inside Coq's `Hr'` upper-bound reduction for
`round_round_sqrt_aux`.

This packages the real-arithmetic part after the center product is bounded:
from `u2 * B <= 1/2*u1^2`, `a + 1/2*u1 < B`, and `u2^2 < u1^2`, the upper
tail `u2*a + b'^2` is strictly below `u1^2`. -/
theorem round_round_sqrt_upper_tail_lt_u1_sq_from_bounds
    (a u1 u2 bp B : ℝ)
    (hbp : bp = (1 / 2) * (u1 + u2))
    (hu2_pos : 0 < u2)
    (hcenter : a + (1 / 2) * u1 < B)
    (hB : u2 * B ≤ (1 / 2) * u1 ^ 2)
    (hu2sq : u2 ^ 2 < u1 ^ 2) :
    u2 * a + bp * bp < u1 ^ 2 := by
  subst bp
  have hprod : u2 * (a + (1 / 2) * u1) < (1 / 2) * u1 ^ 2 := by
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hcenter hu2_pos) hB
  nlinarith

/-- Variant of the upper-tail estimate using the quarter-square sum bound.

The residual-positivity branch already proves
`u2 * B <= 1/4*(u2^2 + u1^2)`.  Together with `u2^2 < u1^2`, this is enough
for the same Coq tail estimate `u2*a + b'^2 < u1^2`. -/
theorem round_round_sqrt_upper_tail_lt_u1_sq_from_quarter_sum
    (a u1 u2 bp B : ℝ)
    (hbp : bp = (1 / 2) * (u1 + u2))
    (hu2_pos : 0 < u2)
    (hcenter : a + (1 / 2) * u1 < B)
    (hB : u2 * B ≤ (1 / 4) * (u2 ^ 2 + u1 ^ 2))
    (hu2sq : u2 ^ 2 < u1 ^ 2) :
    u2 * a + bp * bp < u1 ^ 2 := by
  subst bp
  have hprod :
      u2 * (a + (1 / 2) * u1) <
        (1 / 4) * (u2 ^ 2 + u1 ^ 2) := by
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hcenter hu2_pos) hB
  nlinarith

/-- Upper-tail estimate in the `a ≠ 0` branch once the Coq exponent side
condition has been isolated.

This packages the remaining nonzero-floor tail input used by
`round_round_sqrt_nonzero_floor_contra_from_tail`: the center estimate gives
`a + 1/2*u1 < beta^(mag (sqrt x))`, the exponent premise gives the
quarter-square bound, and the first/second format exponent gap gives
`u2^2 < u1^2`. -/
theorem round_round_sqrt_upper_tail_from_pos_floor_and_exp
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta) (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hexp :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) +
          FloatSpec.Core.Raux.mag beta (Real.sqrt x) ≤
        2 * fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 2) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    let u1 := ulp beta fexp1 (Real.sqrt x)
    let u2 := ulp beta fexp2 (Real.sqrt x)
    let bp := (1 / 2) * (u1 + u2)
    0 < a → u2 * a + bp * bp < u1 ^ 2 := by
  classical
  dsimp
  intro ha_pos
  set s : ℝ := Real.sqrt x with hs
  set a : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_floor s with ha
  set u1 : ℝ := ulp beta fexp1 s with hu1
  set u2 : ℝ := ulp beta fexp2 s with hu2
  set bp : ℝ := (1 / 2) * (u1 + u2) with hbp
  have hs_pos : 0 < s := by
    simpa [s, hs] using Real.sqrt_pos.mpr hx_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hu1_pow :
      u1 =
        (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta s) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := s) hs_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp, u1, hu1] using htrip True.intro
  have hu2_pow :
      u2 =
        (beta : ℝ) ^ fexp2 (FloatSpec.Core.Raux.mag beta s) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp2) (x := s) hs_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp, u2, hu2] using htrip True.intro
  have hu2_pos : 0 < u2 := by
    rw [hu2_pow]
    exact zpow_pos hbposR _
  have hf2_lt :
      fexp2 (FloatSpec.Core.Raux.mag beta s) <
        fexp1 (FloatSpec.Core.Raux.mag beta s) := by
    have hf2_s :
        fexp2 (FloatSpec.Core.Raux.mag beta s) ≤
          fexp1 (FloatSpec.Core.Raux.mag beta s) - 1 := by
      simpa [s, hs] using hf2
    omega
  have hu2_lt_u1 : u2 < u1 := by
    rw [hu1_pow, hu2_pow]
    exact zpow_lt_zpow_right₀ hβR hf2_lt
  have hu2sq : u2 ^ 2 < u1 ^ 2 := by
    nlinarith [hu2_pos, hu2_lt_u1]
  have hcenter :
      a + (1 / 2) * u1 <
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s := by
    have h := round_round_sqrt_center_lt_bpow_of_pos_floor
      (beta := beta) (fexp1 := fexp1) (x := x) hβ hx_pos
    simpa [s, hs, a, ha, u1, hu1] using h (by simpa [a, ha] using ha_pos)
  have hexp_s :
      fexp2 (FloatSpec.Core.Raux.mag beta s) +
          FloatSpec.Core.Raux.mag beta s ≤
        2 * fexp1 (FloatSpec.Core.Raux.mag beta s) - 2 := by
    simpa [s, hs] using hexp
  have hB :
      u2 * (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s ≤
        (1 / 4) * (u2 ^ 2 + u1 ^ 2) :=
    round_round_sqrt_u2_bpow_le_quarter_sum
      (beta := beta)
      (e1 := fexp1 (FloatSpec.Core.Raux.mag beta s))
      (e2 := fexp2 (FloatSpec.Core.Raux.mag beta s))
      (m := FloatSpec.Core.Raux.mag beta s)
      (u1 := u1) (u2 := u2) hβ hu1_pow hu2_pow hexp_s
  exact
    round_round_sqrt_upper_tail_lt_u1_sq_from_quarter_sum
      (a := a) (u1 := u1) (u2 := u2) (bp := bp)
      (B := (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s)
      (by rw [hbp]) hu2_pos hcenter hB hu2sq

/-- Upper-tail estimate in the nonzero-floor branch directly from
`round_round_sqrt_hyp` and the generic-format assumption on `x`. -/
theorem round_round_sqrt_upper_tail_from_pos_floor
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    let u1 := ulp beta fexp1 (Real.sqrt x)
    let u2 := ulp beta fexp2 (Real.sqrt x)
    let bp := (1 / 2) * (u1 + u2)
    0 < a → u2 * a + bp * bp < u1 ^ 2 := by
  classical
  have hexp :=
    round_round_sqrt_exp_premise_from_hyp
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ Hexp hx_pos hx_fmt
  exact
    round_round_sqrt_upper_tail_from_pos_floor_and_exp
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ hx_pos hf2 hexp

/-- Algebraic consequence of the upper tail estimate used by Coq's `Hr'`.

Once `x` is bounded by the squared upper interval endpoint and the upper tail
is strictly below `u1^2`, `x` lies strictly below the next grid point
`a*a + u1*a + u1^2`. The remaining `Hr'` work is the integer/generic-format
rounding step that turns this strict next-grid bound into
`x <= a*a + u1*a`. -/
theorem round_round_sqrt_upper_next_grid_bound
    (x a u1 u2 bp : ℝ)
    (hsr : x ≤ a * a + u1 * a + u2 * a + bp * bp)
    (htail : u2 * a + bp * bp < u1 ^ 2) :
    x < a * a + u1 * a + u1 ^ 2 := by
  nlinarith

/-- Integer-grid exclusion used by Coq's `Hr'` upper-bound reduction.

After scaling by the positive factor `scale`, formatted `x` is an integer
grid point `mx`, while the lower and next upper endpoints are consecutive
integer grid points `ma^2 + ma` and `ma^2 + ma + 1`. A strict bound below the
next endpoint therefore forces `x` to be at most the lower endpoint. -/
theorem round_round_sqrt_upper_grid_le_of_scaled_int
    (x a u1 scale : ℝ) (mx ma : Int)
    (hscale_pos : 0 < scale)
    (hx_scaled : x * scale = (mx : ℝ))
    (hlower_scaled : (a * a + u1 * a) * scale =
      ((ma * ma + ma : Int) : ℝ))
    (hnext_scaled : (a * a + u1 * a + u1 ^ 2) * scale =
      ((ma * ma + ma + 1 : Int) : ℝ))
    (hnext : x < a * a + u1 * a + u1 ^ 2) :
    x ≤ a * a + u1 * a := by
  have hscaled_lt : (mx : ℝ) < ((ma * ma + ma + 1 : Int) : ℝ) := by
    rw [← hx_scaled, ← hnext_scaled]
    exact mul_lt_mul_of_pos_right hnext hscale_pos
  have hmx_lt : mx < ma * ma + ma + 1 := by
    exact_mod_cast hscaled_lt
  have hmx_le : mx ≤ ma * ma + ma := by
    omega
  have hscaled_le : x * scale ≤ (a * a + u1 * a) * scale := by
    rw [hx_scaled, hlower_scaled]
    exact_mod_cast hmx_le
  exact le_of_mul_le_mul_right hscaled_le hscale_pos

/-- Normalize the scaling factor used in Coq's `Hr'` proof.

Coq scales by `bpow (-2 * e)`. In Lean this form is easier to combine with
the endpoint algebra as `(β^e)⁻¹ * (β^e)⁻¹`. -/
theorem round_round_sqrt_scale_neg_two_eq_inv_sq
    (beta : Int) [ValidRadix beta] (e : Int) (hβ : 1 < beta) :
    (beta : ℝ) ^ (-(2 * e)) =
      ((beta : ℝ) ^ e)⁻¹ * ((beta : ℝ) ^ e)⁻¹ := by
  have hbposI : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposI
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  calc
    (beta : ℝ) ^ (-(2 * e)) = (beta : ℝ) ^ (-(e + e)) := by ring_nf
    _ = ((beta : ℝ) ^ (e + e))⁻¹ := by rw [zpow_neg]
    _ = (((beta : ℝ) ^ e * (beta : ℝ) ^ e))⁻¹ := by
      rw [(zpow_add₀ hbne e e).symm]
    _ = ((beta : ℝ) ^ e)⁻¹ * ((beta : ℝ) ^ e)⁻¹ := by rw [mul_inv]

/-- Scaled endpoint equalities for the consecutive integer grid in Coq's `Hr'`.

If the first-round floor value is `a = ma*p`, the first ulp is `u1 = p`, and
the scale is `p⁻¹*p⁻¹`, then the lower endpoint and the next endpoint scale to
the consecutive integers `ma^2 + ma` and `ma^2 + ma + 1`. -/
theorem round_round_sqrt_scaled_endpoints_of_unit
    (a u1 scale p : ℝ) (ma : Int)
    (hp_ne : p ≠ 0)
    (ha : a = (ma : ℝ) * p)
    (hu1 : u1 = p)
    (hscale : scale = p⁻¹ * p⁻¹) :
    (a * a + u1 * a) * scale = ((ma * ma + ma : Int) : ℝ) ∧
      (a * a + u1 * a + u1 ^ 2) * scale =
        ((ma * ma + ma + 1 : Int) : ℝ) := by
  subst a
  subst u1
  subst scale
  constructor
  · field_simp [hp_ne]
    norm_num [Int.cast_add, Int.cast_mul]
    ring
  · field_simp [hp_ne]
    norm_num [Int.cast_add, Int.cast_mul]
    ring

/-- Grid representation of the positive first-format floor rounding of
`sqrt x`.

Coq's nonzero branch writes the first floor-rounded value as `ma * beta^e`
with `e = fexp1 (mag (sqrt x))`, and also rewrites the first ulp to the same
power. This packages both facts from `round_DN_pt`, `cexp_DN`,
`generic_format`, and `ulp_neq_0`. -/
theorem round_round_sqrt_floor_grid_of_pos
    (fexp1 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (x : ℝ) (hβ : 1 < beta) (hx_pos : 0 < x) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    let u1 := ulp beta fexp1 (Real.sqrt x)
    let e := fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x))
    let p := (beta : ℝ) ^ e
    0 < a → ∃ ma : Int, a = (ma : ℝ) * p ∧ u1 = p := by
  classical
  dsimp
  intro ha_pos
  set s : ℝ := Real.sqrt x with hs
  set a : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_floor s with ha
  set u1 : ℝ := ulp beta fexp1 s with hu1
  set e : Int := fexp1 (FloatSpec.Core.Raux.mag beta s) with he
  set p : ℝ := (beta : ℝ) ^ e with hp
  have hs_pos : 0 < s := by
    simpa [s, hs] using Real.sqrt_pos.mpr hx_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hdn :
      FloatSpec.Core.Defs.Rnd_DN_pt
        (fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) s a := by
    simpa [a, ha] using
      FloatSpec.Core.Generic_fmt.round_DN_pt
        (beta := beta) (fexp := fexp1) (x := s) hβ
  have ha_fmt :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 a := hdn.1
  have hcexp :
      FloatSpec.Core.Generic_fmt.cexp beta fexp1 a =
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 s := by
    have htrip := FloatSpec.Core.Generic_fmt.cexp_DN
      (beta := beta) (fexp := fexp1) (x := s)
    have himp :
        0 <
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor s →
          FloatSpec.Core.Generic_fmt.cexp beta fexp1
              (FloatSpec.Core.Generic_fmt.roundR beta fexp1
                FloatSpec.Core.Generic_fmt.rnd_floor s) =
            FloatSpec.Core.Generic_fmt.cexp beta fexp1 s := by
      simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hβ
    simpa [a, ha] using himp (by simpa [a, ha] using ha_pos)
  have hu1_pow :
      u1 = (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 s := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := s) hs_ne
    simpa [wp, PostCond.noThrow, Id.run, pure, u1, hu1] using htrip True.intro
  let ma : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 a)
  have ha_grid_cexp :
      a = (ma : ℝ) *
        (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 a := by
    simpa [FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Defs.F2R, ma] using ha_fmt
  refine ⟨ma, ?_, ?_⟩
  · calc
      a = (ma : ℝ) *
          (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 a :=
        ha_grid_cexp
      _ = (ma : ℝ) *
          (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 s := by
        rw [hcexp]
      _ = (ma : ℝ) * p := by
        simp [p, hp, e, FloatSpec.Core.Generic_fmt.cexp]
  · calc
      u1 = (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 s := hu1_pow
      _ = p := by
        simp [p, hp, e, FloatSpec.Core.Generic_fmt.cexp]

/-- A formatted real has an integer scaled mantissa.

This is the `generic_format`/`F2R` extraction needed by Coq's `Hr'` proof:
unfolding `generic_format` gives
`x = Ztrunc (scaled_mantissa x) * beta^(cexp x)`, so multiplying by
`beta^(-cexp x)` recovers the integer mantissa. -/
theorem round_round_sqrt_scaled_mantissa_int_of_generic_format
    (beta : Int) [ValidRadix beta] (fexp : Int → Int) (x : ℝ)
    (hβ : 1 < beta)
    (hfmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp x) :
    FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x =
      (((FloatSpec.Core.Raux.Ztrunc
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)) : Int) : ℝ) := by
  have hbposI : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposI
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  set c : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x with hc
  set m : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x) with hm
  have hfmt' : x = (m : ℝ) * (beta : ℝ) ^ c := by
    simpa [FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Defs.F2R, c, hc, m, hm]
      using hfmt
  have hscale : x * (beta : ℝ) ^ (-c) = (m : ℝ) := by
    calc
      x * (beta : ℝ) ^ (-c)
          = ((m : ℝ) * (beta : ℝ) ^ c) * (beta : ℝ) ^ (-c) := by rw [hfmt']
      _ = (m : ℝ) * ((beta : ℝ) ^ c * (beta : ℝ) ^ (-c)) := by ring
      _ = (m : ℝ) * (beta : ℝ) ^ (c + -c) := by
        rw [(zpow_add₀ hbne c (-c)).symm]
      _ = (m : ℝ) := by simp
  have hsm :
      FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x =
        x * (beta : ℝ) ^ (-c) := by
    simp [FloatSpec.Core.Generic_fmt.scaled_mantissa, c]
  calc
    FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x =
        x * (beta : ℝ) ^ (-c) := hsm
    _ = (m : ℝ) := hscale
    _ = (((FloatSpec.Core.Raux.Ztrunc
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)) : Int) : ℝ) := by
      simp [m]

/-- Formatted `x` gives the scaled integer point required by Coq's `Hr'`.

When the canonical exponent of `x` is `2*e`, scaling by `beta^(-2*e)`
is exactly scaling by `beta^(-cexp x)`, hence the result is the integer
truncated scaled mantissa. -/
theorem round_round_sqrt_scaled_int_of_generic_format_at_exp
    (beta : Int) [ValidRadix beta] (fexp : Int → Int) (x scale : ℝ) (e : Int)
    (hβ : 1 < beta)
    (hfmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp x)
    (hcexp : FloatSpec.Core.Generic_fmt.cexp beta fexp x = 2 * e)
    (hscale : scale = (beta : ℝ) ^ (-(2 * e))) :
    x * scale =
      (((FloatSpec.Core.Raux.Ztrunc
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)) : Int) : ℝ) := by
  have hsm_int :=
    round_round_sqrt_scaled_mantissa_int_of_generic_format
      (beta := beta) (fexp := fexp) (x := x) hβ hfmt
  have hsm : FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x = x * scale := by
    calc
      FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x
          = x * (beta : ℝ) ^ (-(FloatSpec.Core.Generic_fmt.cexp beta fexp x)) := by
            simp [FloatSpec.Core.Generic_fmt.scaled_mantissa]
      _ = x * (beta : ℝ) ^ (-(2 * e)) := by rw [hcexp]
      _ = x * scale := by rw [hscale]
  rw [← hsm]
  exact hsm_int

/-- Formatted `x` remains an integer grid point when scaled to any lower
exponent.

Coq's `Hr'` branch scales `x` by `beta^(-target)` where the target exponent is
known only to be below the canonical exponent of `x`.  This helper turns the
canonical `generic_format` representation into the needed integer witness after
rescaling. -/
theorem round_round_sqrt_scaled_int_of_generic_format_le_exp
    (beta : Int) [ValidRadix beta] (fexp : Int → Int) (x scale : ℝ) (target : Int)
    (hβ : 1 < beta)
    (hfmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp x)
    (hle : target ≤ FloatSpec.Core.Generic_fmt.cexp beta fexp x)
    (hscale : scale = (beta : ℝ) ^ (-target)) :
    ∃ mx : Int, x * scale = (mx : ℝ) := by
  have hbposI : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposI
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  set c : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x with hc
  set m : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x) with hm
  have hfmt' : x = (m : ℝ) * (beta : ℝ) ^ c := by
    simpa [FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Defs.F2R, c, hc, m, hm]
      using hfmt
  have hdiff_nonneg : 0 ≤ c - target := by
    exact sub_nonneg.mpr (by simpa [c, hc] using hle)
  have hpow_sub :
      (beta : ℝ) ^ c * (beta : ℝ) ^ (-target) =
        (beta : ℝ) ^ (c - target) := by
    simpa using
      (FloatSpec.Core.Generic_fmt.zpow_mul_sub
        (a := (beta : ℝ)) (hbne := hbne) (e := c) (c := target))
  have hzpow_toNat :
      (beta : ℝ) ^ (c - target) =
        (beta : ℝ) ^ (Int.toNat (c - target)) := by
    simpa using
      FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat
        (beta : ℝ) (c - target) hdiff_nonneg
  have hcast_pow :
      (beta : ℝ) ^ (Int.toNat (c - target)) =
        ((beta ^ (Int.toNat (c - target)) : Int) : ℝ) := by
    rw [← Int.cast_pow]
  refine ⟨m * beta ^ (Int.toNat (c - target)), ?_⟩
  calc
    x * scale
        = ((m : ℝ) * (beta : ℝ) ^ c) * (beta : ℝ) ^ (-target) := by
            rw [hfmt', hscale]
    _ = (m : ℝ) * ((beta : ℝ) ^ c * (beta : ℝ) ^ (-target)) := by ring
    _ = (m : ℝ) * (beta : ℝ) ^ (c - target) := by rw [hpow_sub]
    _ = (m : ℝ) * (beta : ℝ) ^ (Int.toNat (c - target)) := by rw [hzpow_toNat]
    _ = ((m * beta ^ (Int.toNat (c - target)) : Int) : ℝ) := by
      simp only [hcast_pow, Int.cast_mul]

/-- Coq's `Hr'` upper-bound reduction after the strict next-grid estimate.

The preceding helpers provide the integer-grid facts needed by Coq after
scaling with `beta^(-2*e)`: formatted `x` scales to an integer, while
`a*a + u1*a` and `a*a + u1*a + u1^2` scale to consecutive integer points.
Together with the strict next-grid bound this gives the desired
`x <= a*a + u1*a`. -/
theorem round_round_sqrt_hr_upper_bound_from_grid
    (fexp1 fexp2 : Int → Int)
    (x a u1 scale p : ℝ) (e ma : Int)
    (hβ : 1 < beta)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (he : e = fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)))
    (hp : p = (beta : ℝ) ^ e)
    (ha : a = (ma : ℝ) * p)
    (hu1 : u1 = p)
    (hscale : scale = (beta : ℝ) ^ (-(2 * e)))
    (hnext : x < a * a + u1 * a + u1 ^ 2) :
    x ≤ a * a + u1 * a := by
  have hbposI : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposI
  have hscale_pos : 0 < scale := by
    rw [hscale]
    exact zpow_pos hbpos (-(2 * e))
  have htarget :
      2 * e ≤ FloatSpec.Core.Generic_fmt.cexp beta fexp1 x := by
    have h :=
      round_round_sqrt_target_le_cexp_from_hyp
        (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
        (x := x) hβ Hexp hx_pos
    simpa [he] using h
  rcases
      round_round_sqrt_scaled_int_of_generic_format_le_exp
        (beta := beta) (fexp := fexp1) (x := x) (scale := scale)
        (target := 2 * e) hβ hx_fmt htarget hscale
    with ⟨mx, hx_scaled⟩
  have hp_ne : p ≠ 0 := by
    rw [hp]
    exact ne_of_gt (zpow_pos hbpos e)
  have hscale_inv : scale = p⁻¹ * p⁻¹ := by
    calc
      scale = (beta : ℝ) ^ (-(2 * e)) := hscale
      _ = ((beta : ℝ) ^ e)⁻¹ * ((beta : ℝ) ^ e)⁻¹ :=
        round_round_sqrt_scale_neg_two_eq_inv_sq (beta := beta) (e := e) hβ
      _ = p⁻¹ * p⁻¹ := by rw [hp]
  have hendpoints :=
    round_round_sqrt_scaled_endpoints_of_unit
      (a := a) (u1 := u1) (scale := scale) (p := p)
      (ma := ma) hp_ne ha hu1 hscale_inv
  exact
    round_round_sqrt_upper_grid_le_of_scaled_int
      (x := x) (a := a) (u1 := u1) (scale := scale)
      (mx := mx) (ma := ma) hscale_pos hx_scaled
      hendpoints.1 hendpoints.2 hnext

/-- Coq's `Hr'` upper-bound reduction from the squared upper interval and tail
estimate.

This composes the real upper-next-grid bound with the integer-grid reduction,
so downstream `round_round_sqrt_aux` assembly can use the Coq-shaped hypotheses
`Hsr` and the tail estimate directly. -/
theorem round_round_sqrt_hr_upper_bound_from_tail
    (fexp1 fexp2 : Int → Int)
    (x a u1 u2 bp scale p : ℝ) (e ma : Int)
    (hβ : 1 < beta)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (he : e = fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)))
    (hp : p = (beta : ℝ) ^ e)
    (ha : a = (ma : ℝ) * p)
    (hu1 : u1 = p)
    (hscale : scale = (beta : ℝ) ^ (-(2 * e)))
    (hsr : x ≤ a * a + u1 * a + u2 * a + bp * bp)
    (htail : u2 * a + bp * bp < u1 ^ 2) :
    x ≤ a * a + u1 * a := by
  have hnext :
      x < a * a + u1 * a + u1 ^ 2 :=
    round_round_sqrt_upper_next_grid_bound
      (x := x) (a := a) (u1 := u1) (u2 := u2) (bp := bp) hsr htail
  exact
    round_round_sqrt_hr_upper_bound_from_grid
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) (a := a) (u1 := u1) (scale := scale) (p := p)
      (e := e) (ma := ma) hβ Hexp hx_pos hx_fmt he hp ha hu1 hscale hnext

/-- The `a ≠ 0` contradiction branch of Coq `round_round_sqrt_aux`, once the
upper-tail estimate has been established.

This combines the lower square bound, the `Hr'` upper-bound reduction, and the
residual positivity lemma into the final contradiction used before the proof
returns the midpoint gap. -/
theorem round_round_sqrt_nonzero_floor_contra_from_tail
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x a u1 u2 b bp scale p : ℝ) (e ma : Int)
    (hβ : 1 < beta)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (ha_def :
      a = FloatSpec.Core.Generic_fmt.roundR beta fexp1
        FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x))
    (hu1_def : u1 = ulp beta fexp1 (Real.sqrt x))
    (hu2_def : u2 = ulp beta fexp2 (Real.sqrt x))
    (hb_def : b = (1 / 2) * (u1 - u2))
    (he : e = fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)))
    (hp : p = (beta : ℝ) ^ e)
    (ha_grid : a = (ma : ℝ) * p)
    (hu1_grid : u1 = p)
    (hscale : scale = (beta : ℝ) ^ (-(2 * e)))
    (ha_pos : 0 < a)
    (hsl : a * a + u1 * a - u2 * a + b * b ≤ x)
    (hsr : x ≤ a * a + u1 * a + u2 * a + bp * bp)
    (htail : u2 * a + bp * bp < u1 ^ 2) :
    False := by
  have hres0 :=
    round_round_sqrt_residual_pos_from_pos_floor
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ Hexp hx_pos hx_fmt
  have ha_pos0 :
      0 <
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
          FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x) := by
    simpa [← ha_def] using ha_pos
  have hres : 0 < -(u2 * a) + b * b := by
    simpa [← ha_def, ← hu1_def, ← hu2_def, hb_def] using hres0 ha_pos0
  have hr :
      x ≤ a * a + u1 * a :=
    round_round_sqrt_hr_upper_bound_from_tail
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) (a := a) (u1 := u1) (u2 := u2) (bp := bp)
      (scale := scale) (p := p) (e := e) (ma := ma)
      hβ Hexp hx_pos hx_fmt he hp ha_grid hu1_grid hscale hsr htail
  exact
    round_round_sqrt_nonzero_residual_contra
      (x := x) (a := a) (u1 := u1) (u2 := u2) (b := b)
      hsl hr hres

/-- The `a ≠ 0` contradiction branch of Coq `round_round_sqrt_aux` with the
upper-tail estimate derived from the square-root exponent hypotheses.

This is the nonzero-floor branch in the shape needed by the final
midpoint-gap assembly: it starts from the interval square bounds and grid
representation facts, then derives the tail estimate internally from
`round_round_sqrt_hyp`, the first/second format exponent gap, and
`generic_format beta fexp1 x`. -/
theorem round_round_sqrt_nonzero_floor_contra
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x a u1 u2 b bp scale p : ℝ) (e ma : Int)
    (hβ : 1 < beta)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (ha_def :
      a = FloatSpec.Core.Generic_fmt.roundR beta fexp1
        FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x))
    (hu1_def : u1 = ulp beta fexp1 (Real.sqrt x))
    (hu2_def : u2 = ulp beta fexp2 (Real.sqrt x))
    (hb_def : b = (1 / 2) * (u1 - u2))
    (hbp_def : bp = (1 / 2) * (u1 + u2))
    (he : e = fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)))
    (hp : p = (beta : ℝ) ^ e)
    (ha_grid : a = (ma : ℝ) * p)
    (hu1_grid : u1 = p)
    (hscale : scale = (beta : ℝ) ^ (-(2 * e)))
    (ha_pos : 0 < a)
    (hsl : a * a + u1 * a - u2 * a + b * b ≤ x)
    (hsr : x ≤ a * a + u1 * a + u2 * a + bp * bp) :
    False := by
  have htail0 :=
    round_round_sqrt_upper_tail_from_pos_floor
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ Hexp hx_pos hf2 hx_fmt
  have ha_pos0 :
      0 <
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
          FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x) := by
    simpa [← ha_def] using ha_pos
  have htail : u2 * a + bp * bp < u1 ^ 2 := by
    simpa [← ha_def, ← hu1_def, ← hu2_def, hbp_def] using htail0 ha_pos0
  exact
    round_round_sqrt_nonzero_floor_contra_from_tail
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) (a := a) (u1 := u1) (u2 := u2) (b := b) (bp := bp)
      (scale := scale) (p := p) (e := e) (ma := ma)
      hβ Hexp hx_pos hx_fmt ha_def hu1_def hu2_def hb_def
      he hp ha_grid hu1_grid hscale ha_pos hsl hsr htail

/-- Coq: `round_round_sqrt_radix_ge_4_hyp`. -/
def round_round_sqrt_radix_ge_4_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex)) ∧
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1)) ∧
  (∀ ex, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - 1)

/-- Radix-`ge_4` variant of the zero-floor contradiction branch.

The zero branch only needs the first two square-root exponent hypotheses, which
are shared by `round_round_sqrt_hyp` and `round_round_sqrt_radix_ge_4_hyp`. -/
theorem round_round_sqrt_zero_floor_contra_from_not_gap_radix_ge_4
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta)
    (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hnot :
      ¬ ((1 / 2) * ulp beta fexp2 (Real.sqrt x) <
          |Real.sqrt x - midp beta fexp1 (Real.sqrt x)|)) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    a = 0 →
    False := by
  classical
  dsimp
  intro ha0
  have hbounds :=
    round_round_sqrt_mid_bounds_from_not_gap
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hnot
  have hf1 :
      2 * fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) := by
    rcases mag_sqrt_disj (beta := beta) x hβ hx_pos with hmag | hmag
    · simpa [hmag] using
        Hexp.2.1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x))
    · simpa [hmag] using
        Hexp.1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x))
  exact
    round_round_sqrt_zero_floor_contra
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ hx_pos hf2 hx_fmt hf1 ha0 hbounds.2

/-- Radix-`ge_4` power bound used in the nonzero branch.

The radix-specific Flocq proof has the weaker exponent premise
`e2 + m <= 2*e1 - 1`.  The additional assumption `4 <= beta` compensates for
this, giving `beta^(-1) <= 1/4`. -/
theorem round_round_sqrt_u2_bpow_le_quarter_sum_radix_ge_4
    (e1 e2 m : Int) (u1 u2 : ℝ)
    (hβ : 1 < beta)
    (hβ4 : 4 ≤ beta)
    (hu1 : u1 = (beta : ℝ) ^ e1)
    (hu2 : u2 = (beta : ℝ) ^ e2)
    (hexp : e2 + m ≤ 2 * e1 - 1) :
    u2 * (beta : ℝ) ^ m ≤ (1 / 4) * (u2 ^ 2 + u1 ^ 2) := by
  classical
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hmul_pow :
      u2 * (beta : ℝ) ^ m = (beta : ℝ) ^ (e2 + m) := by
    calc
      u2 * (beta : ℝ) ^ m = (beta : ℝ) ^ e2 * (beta : ℝ) ^ m := by
        rw [hu2]
      _ = (beta : ℝ) ^ (e2 + m) := by
        exact (zpow_add₀ hbne e2 m).symm
  have hpow_gap :
      (beta : ℝ) ^ (e2 + m) ≤ (beta : ℝ) ^ (2 * e1 - 1) :=
    (zpow_right_strictMono₀ hβR).monotone hexp
  have hpow_id :
      (beta : ℝ) ^ (2 * e1 - 1) =
        (beta : ℝ) ^ (-1 : Int) * ((beta : ℝ) ^ e1) ^ 2 := by
    have hidx : 2 * e1 - 1 = (-1 : Int) + e1 + e1 := by ring
    calc
      (beta : ℝ) ^ (2 * e1 - 1) =
          (beta : ℝ) ^ ((-1 : Int) + e1 + e1) := by rw [hidx]
      _ = (beta : ℝ) ^ ((-1 : Int) + e1) * (beta : ℝ) ^ e1 := by
        exact zpow_add₀ hbne ((-1 : Int) + e1) e1
      _ = ((beta : ℝ) ^ (-1 : Int) * (beta : ℝ) ^ e1) *
          (beta : ℝ) ^ e1 := by
        rw [zpow_add₀ hbne (-1 : Int) e1]
      _ = (beta : ℝ) ^ (-1 : Int) * ((beta : ℝ) ^ e1) ^ 2 := by ring
  have hleft :
      u2 * (beta : ℝ) ^ m ≤ (beta : ℝ) ^ (-1 : Int) * u1 ^ 2 := by
    calc
      u2 * (beta : ℝ) ^ m = (beta : ℝ) ^ (e2 + m) := hmul_pow
      _ ≤ (beta : ℝ) ^ (2 * e1 - 1) := hpow_gap
      _ = (beta : ℝ) ^ (-1 : Int) * u1 ^ 2 := by
        simpa [hu1] using hpow_id
  have hb_ge4R : (4 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hβ4
  have hcoeff :
      (beta : ℝ) ^ (-1 : Int) ≤ (1 / 4 : ℝ) := by
    have hinv : ((beta : ℝ)⁻¹) ≤ ((4 : ℝ)⁻¹) :=
      (inv_le_inv₀ hbposR (by norm_num : (0 : ℝ) < 4)).2 hb_ge4R
    have hneg : (beta : ℝ) ^ (-1 : Int) = (beta : ℝ)⁻¹ := by
      simp [zpow_neg]
    have hfour : ((4 : ℝ)⁻¹) = (1 / 4 : ℝ) := by norm_num
    rw [hneg]
    calc
      (beta : ℝ)⁻¹ ≤ ((4 : ℝ)⁻¹) := hinv
      _ = (1 / 4 : ℝ) := hfour
  have hcoeff_mul :
      (beta : ℝ) ^ (-1 : Int) * u1 ^ 2 ≤ (1 / 4 : ℝ) * u1 ^ 2 :=
    mul_le_mul_of_nonneg_right hcoeff (sq_nonneg u1)
  have hquarter :
      (1 / 4 : ℝ) * u1 ^ 2 ≤ (1 / 4 : ℝ) * (u2 ^ 2 + u1 ^ 2) := by
    nlinarith [sq_nonneg u2]
  exact le_trans hleft (le_trans hcoeff_mul hquarter)

/-- Radix-`ge_4` exponent premise for the nonzero residual branch. -/
theorem round_round_sqrt_exp_premise_from_radix_ge_4_hyp
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (x : ℝ) (hβ : 1 < beta)
    (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) +
        FloatSpec.Core.Raux.mag beta (Real.sqrt x) ≤
      2 * fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1 := by
  classical
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hfx_lt :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp1) x
    have hcexp_lt :
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 x <
          FloatSpec.Core.Raux.mag beta x := by
      simpa [wp, PostCond.noThrow, Id.run, pure] using
        htrip ⟨hβ, hx_ne, hx_fmt⟩
    simpa [FloatSpec.Core.Generic_fmt.cexp] using hcexp_lt
  have hlarge :
      fexp1 (2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x)) <
        2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
    rcases mag_sqrt_disj (beta := beta) x hβ hx_pos with hmag | hmag
    · apply FloatSpec.Core.Generic_fmt.valid_exp_large
        (beta := beta) (fexp := fexp1)
        (k := FloatSpec.Core.Raux.mag beta x)
        (l := 2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x))
        hfx_lt
      omega
    · simpa [← hmag] using hfx_lt
  exact Hexp.2.2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) hlarge

/-- Radix-`ge_4` residual positivity in the nonzero floor branch. -/
theorem round_round_sqrt_residual_pos_from_pos_floor_radix_ge_4
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta) (hβ4 : 4 ≤ beta)
    (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    let u1 := ulp beta fexp1 (Real.sqrt x)
    let u2 := ulp beta fexp2 (Real.sqrt x)
    let b := (1 / 2) * (u1 - u2)
    0 < a → 0 < -(u2 * a) + b * b := by
  classical
  dsimp
  intro ha_pos
  set s : ℝ := Real.sqrt x with hs
  set a : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_floor s with ha
  set u1 : ℝ := ulp beta fexp1 s with hu1
  set u2 : ℝ := ulp beta fexp2 s with hu2
  set b : ℝ := (1 / 2) * (u1 - u2) with hb
  have hs_pos : 0 < s := by
    simpa [s, hs] using Real.sqrt_pos.mpr hx_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hu1_pow :
      u1 =
        (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta s) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := s) hs_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp, u1, hu1] using htrip True.intro
  have hu2_pow :
      u2 =
        (beta : ℝ) ^ fexp2 (FloatSpec.Core.Raux.mag beta s) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp2) (x := s) hs_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp, u2, hu2] using htrip True.intro
  have hu2_pos : 0 < u2 := by
    rw [hu2_pow]
    exact zpow_pos hbposR _
  have hcenter :
      a + (1 / 2) * u1 <
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s := by
    have h := round_round_sqrt_center_lt_bpow_of_pos_floor
      (beta := beta) (fexp1 := fexp1) (x := x) hβ hx_pos
    simpa [s, hs, a, ha, u1, hu1] using h (by simpa [a, ha] using ha_pos)
  have hexp :=
    round_round_sqrt_exp_premise_from_radix_ge_4_hyp
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ Hexp hx_pos hx_fmt
  have hexp_s :
      fexp2 (FloatSpec.Core.Raux.mag beta s) +
          FloatSpec.Core.Raux.mag beta s ≤
        2 * fexp1 (FloatSpec.Core.Raux.mag beta s) - 1 := by
    simpa [s, hs] using hexp
  have hB :
      u2 * (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s ≤
        (1 / 4) * (u2 ^ 2 + u1 ^ 2) :=
    round_round_sqrt_u2_bpow_le_quarter_sum_radix_ge_4
      (beta := beta)
      (e1 := fexp1 (FloatSpec.Core.Raux.mag beta s))
      (e2 := fexp2 (FloatSpec.Core.Raux.mag beta s))
      (m := FloatSpec.Core.Raux.mag beta s)
      (u1 := u1) (u2 := u2) hβ hβ4 hu1_pow hu2_pow hexp_s
  exact
    round_round_sqrt_residual_pos_from_bounds
      (a := a) (u1 := u1) (u2 := u2) (b := b)
      (B := (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s)
      (by rw [hb]) hu2_pos hcenter hB

/-- Radix-`ge_4` upper-tail estimate in the nonzero floor branch. -/
theorem round_round_sqrt_upper_tail_from_pos_floor_radix_ge_4
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta) (hβ4 : 4 ≤ beta)
    (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    let a := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x)
    let u1 := ulp beta fexp1 (Real.sqrt x)
    let u2 := ulp beta fexp2 (Real.sqrt x)
    let bp := (1 / 2) * (u1 + u2)
    0 < a → u2 * a + bp * bp < u1 ^ 2 := by
  classical
  dsimp
  intro ha_pos
  set s : ℝ := Real.sqrt x with hs
  set a : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_floor s with ha
  set u1 : ℝ := ulp beta fexp1 s with hu1
  set u2 : ℝ := ulp beta fexp2 s with hu2
  set bp : ℝ := (1 / 2) * (u1 + u2) with hbp
  have hs_pos : 0 < s := by
    simpa [s, hs] using Real.sqrt_pos.mpr hx_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hu1_pow :
      u1 =
        (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta s) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := s) hs_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp, u1, hu1] using htrip True.intro
  have hu2_pow :
      u2 =
        (beta : ℝ) ^ fexp2 (FloatSpec.Core.Raux.mag beta s) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp2) (x := s) hs_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Generic_fmt.cexp, u2, hu2] using htrip True.intro
  have hu2_pos : 0 < u2 := by
    rw [hu2_pow]
    exact zpow_pos hbposR _
  have hf2_lt :
      fexp2 (FloatSpec.Core.Raux.mag beta s) <
        fexp1 (FloatSpec.Core.Raux.mag beta s) := by
    have hf2_s :
        fexp2 (FloatSpec.Core.Raux.mag beta s) ≤
          fexp1 (FloatSpec.Core.Raux.mag beta s) - 1 := by
      simpa [s, hs] using hf2
    omega
  have hu2_lt_u1 : u2 < u1 := by
    rw [hu1_pow, hu2_pow]
    exact zpow_lt_zpow_right₀ hβR hf2_lt
  have hu2sq : u2 ^ 2 < u1 ^ 2 := by
    nlinarith [hu2_pos, hu2_lt_u1]
  have hcenter :
      a + (1 / 2) * u1 <
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s := by
    have h := round_round_sqrt_center_lt_bpow_of_pos_floor
      (beta := beta) (fexp1 := fexp1) (x := x) hβ hx_pos
    simpa [s, hs, a, ha, u1, hu1] using h (by simpa [a, ha] using ha_pos)
  have hexp :=
    round_round_sqrt_exp_premise_from_radix_ge_4_hyp
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ Hexp hx_pos hx_fmt
  have hexp_s :
      fexp2 (FloatSpec.Core.Raux.mag beta s) +
          FloatSpec.Core.Raux.mag beta s ≤
        2 * fexp1 (FloatSpec.Core.Raux.mag beta s) - 1 := by
    simpa [s, hs] using hexp
  have hB :
      u2 * (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s ≤
        (1 / 4) * (u2 ^ 2 + u1 ^ 2) :=
    round_round_sqrt_u2_bpow_le_quarter_sum_radix_ge_4
      (beta := beta)
      (e1 := fexp1 (FloatSpec.Core.Raux.mag beta s))
      (e2 := fexp2 (FloatSpec.Core.Raux.mag beta s))
      (m := FloatSpec.Core.Raux.mag beta s)
      (u1 := u1) (u2 := u2) hβ hβ4 hu1_pow hu2_pow hexp_s
  exact
    round_round_sqrt_upper_tail_lt_u1_sq_from_quarter_sum
      (a := a) (u1 := u1) (u2 := u2) (bp := bp)
      (B := (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta s)
      (by rw [hbp]) hu2_pos hcenter hB hu2sq

/-- Radix-`ge_4` target exponent bound for the integer-grid reduction. -/
theorem round_round_sqrt_target_le_cexp_from_radix_ge_4_hyp
    (fexp1 fexp2 : Int → Int)
    (x : ℝ) (hβ : 1 < beta)
    (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
    (hx_pos : 0 < x) :
    2 * fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
      FloatSpec.Core.Generic_fmt.cexp beta fexp1 x := by
  classical
  rcases mag_sqrt_disj (beta := beta) x hβ hx_pos with hmag | hmag
  · simpa [FloatSpec.Core.Generic_fmt.cexp, hmag] using
      Hexp.2.1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x))
  · simpa [FloatSpec.Core.Generic_fmt.cexp, hmag] using
      Hexp.1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x))

/-- Integer-grid `Hr' reduction with the target exponent supplied explicitly. -/
theorem round_round_sqrt_hr_upper_bound_from_grid_of_target
    (fexp1 : Int → Int)
    (x a u1 scale p : ℝ) (e ma : Int)
    (hβ : 1 < beta)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (htarget : 2 * e ≤ FloatSpec.Core.Generic_fmt.cexp beta fexp1 x)
    (hp : p = (beta : ℝ) ^ e)
    (ha : a = (ma : ℝ) * p)
    (hu1 : u1 = p)
    (hscale : scale = (beta : ℝ) ^ (-(2 * e)))
    (hnext : x < a * a + u1 * a + u1 ^ 2) :
    x ≤ a * a + u1 * a := by
  have hbposI : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposI
  have hscale_pos : 0 < scale := by
    rw [hscale]
    exact zpow_pos hbpos (-(2 * e))
  rcases
      round_round_sqrt_scaled_int_of_generic_format_le_exp
        (beta := beta) (fexp := fexp1) (x := x) (scale := scale)
        (target := 2 * e) hβ hx_fmt htarget hscale
    with ⟨mx, hx_scaled⟩
  have hp_ne : p ≠ 0 := by
    rw [hp]
    exact ne_of_gt (zpow_pos hbpos e)
  have hscale_inv : scale = p⁻¹ * p⁻¹ := by
    calc
      scale = (beta : ℝ) ^ (-(2 * e)) := hscale
      _ = ((beta : ℝ) ^ e)⁻¹ * ((beta : ℝ) ^ e)⁻¹ :=
        round_round_sqrt_scale_neg_two_eq_inv_sq (beta := beta) (e := e) hβ
      _ = p⁻¹ * p⁻¹ := by rw [hp]
  have hendpoints :=
    round_round_sqrt_scaled_endpoints_of_unit
      (a := a) (u1 := u1) (scale := scale) (p := p)
      (ma := ma) hp_ne ha hu1 hscale_inv
  exact
    round_round_sqrt_upper_grid_le_of_scaled_int
      (x := x) (a := a) (u1 := u1) (scale := scale)
      (mx := mx) (ma := ma) hscale_pos hx_scaled
      hendpoints.1 hendpoints.2 hnext

/-- Nonzero-floor contradiction with residual and target bounds supplied
explicitly, used by the radix-`ge_4` branch. -/
theorem round_round_sqrt_nonzero_floor_contra_from_tail_of_residual
    (fexp1 : Int → Int)
    (x a u1 u2 b bp scale p : ℝ) (e ma : Int)
    (hβ : 1 < beta)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (htarget : 2 * e ≤ FloatSpec.Core.Generic_fmt.cexp beta fexp1 x)
    (hp : p = (beta : ℝ) ^ e)
    (ha_grid : a = (ma : ℝ) * p)
    (hu1_grid : u1 = p)
    (hscale : scale = (beta : ℝ) ^ (-(2 * e)))
    (hsl : a * a + u1 * a - u2 * a + b * b ≤ x)
    (hsr : x ≤ a * a + u1 * a + u2 * a + bp * bp)
    (hres : 0 < -(u2 * a) + b * b)
    (htail : u2 * a + bp * bp < u1 ^ 2) :
    False := by
  have hnext :
      x < a * a + u1 * a + u1 ^ 2 :=
    round_round_sqrt_upper_next_grid_bound
      (x := x) (a := a) (u1 := u1) (u2 := u2) (bp := bp) hsr htail
  have hr :
      x ≤ a * a + u1 * a :=
    round_round_sqrt_hr_upper_bound_from_grid_of_target
      (beta := beta) (fexp1 := fexp1)
      (x := x) (a := a) (u1 := u1) (scale := scale) (p := p)
      (e := e) (ma := ma) hβ hx_fmt htarget hp ha_grid hu1_grid hscale hnext
  exact
    round_round_sqrt_nonzero_residual_contra
      (x := x) (a := a) (u1 := u1) (u2 := u2) (b := b)
      hsl hr hres

/-- Radix-`ge_4` nonzero-floor contradiction branch. -/
theorem round_round_sqrt_nonzero_floor_contra_radix_ge_4
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x a u1 u2 b bp scale p : ℝ) (e ma : Int)
    (hβ : 1 < beta)
    (hβ4 : 4 ≤ beta)
    (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (ha_def :
      a = FloatSpec.Core.Generic_fmt.roundR beta fexp1
        FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x))
    (hu1_def : u1 = ulp beta fexp1 (Real.sqrt x))
    (hu2_def : u2 = ulp beta fexp2 (Real.sqrt x))
    (hb_def : b = (1 / 2) * (u1 - u2))
    (hbp_def : bp = (1 / 2) * (u1 + u2))
    (he : e = fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)))
    (hp : p = (beta : ℝ) ^ e)
    (ha_grid : a = (ma : ℝ) * p)
    (hu1_grid : u1 = p)
    (hscale : scale = (beta : ℝ) ^ (-(2 * e)))
    (ha_pos : 0 < a)
    (hsl : a * a + u1 * a - u2 * a + b * b ≤ x)
    (hsr : x ≤ a * a + u1 * a + u2 * a + bp * bp) :
    False := by
  have hres0 :=
    round_round_sqrt_residual_pos_from_pos_floor_radix_ge_4
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ hβ4 Hexp hx_pos hx_fmt
  have htail0 :=
    round_round_sqrt_upper_tail_from_pos_floor_radix_ge_4
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ hβ4 Hexp hx_pos hf2 hx_fmt
  have ha_pos0 :
      0 <
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
          FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x) := by
    simpa [← ha_def] using ha_pos
  have hres : 0 < -(u2 * a) + b * b := by
    simpa [← ha_def, ← hu1_def, ← hu2_def, hb_def] using hres0 ha_pos0
  have htail : u2 * a + bp * bp < u1 ^ 2 := by
    simpa [← ha_def, ← hu1_def, ← hu2_def, hbp_def] using htail0 ha_pos0
  have htarget :
      2 * e ≤ FloatSpec.Core.Generic_fmt.cexp beta fexp1 x := by
    have h :=
      round_round_sqrt_target_le_cexp_from_radix_ge_4_hyp
        (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
        (x := x) hβ Hexp hx_pos
    simpa [he] using h
  exact
    round_round_sqrt_nonzero_floor_contra_from_tail_of_residual
      (beta := beta) (fexp1 := fexp1)
      (x := x) (a := a) (u1 := u1) (u2 := u2) (b := b) (bp := bp)
      (scale := scale) (p := p) (e := e) (ma := ma)
      hβ hx_fmt htarget hp ha_grid hu1_grid hscale hsl hsr hres htail

/-- Coq `round_round_sqrt_aux` midpoint-gap payload, factored through the
checked zero-floor and nonzero-floor contradiction packages.

If the midpoint gap failed, the interval bounds around `sqrt x` give the
square bounds on `x`.  The floor-rounded value is nonnegative; the `a = 0`
case contradicts the generic-format hypothesis through the zero-floor package,
while the positive case uses the grid witness and the nonzero-floor package.
-/
theorem round_round_sqrt_aux_midpoint_gap
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    (1 / 2) * ulp beta fexp2 (Real.sqrt x) <
      |Real.sqrt x - midp beta fexp1 (Real.sqrt x)| := by
  classical
  by_contra hnot
  set a : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x) with ha
  set u1 : ℝ := ulp beta fexp1 (Real.sqrt x) with hu1
  set u2 : ℝ := ulp beta fexp2 (Real.sqrt x) with hu2
  set b : ℝ := (1 / 2) * (u1 - u2) with hb
  set bp : ℝ := (1 / 2) * (u1 + u2) with hbp
  set e : Int := fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) with he
  set p : ℝ := (beta : ℝ) ^ e with hp
  set scale : ℝ := (beta : ℝ) ^ (-(2 * e)) with hscale
  have hbounds0 :=
    round_round_sqrt_mid_bounds_from_not_gap
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hnot
  have hbounds : a + b ≤ Real.sqrt x ∧ Real.sqrt x ≤ a + bp := by
    simpa [a, ha, u1, hu1, u2, hu2, b, hb, bp, hbp] using hbounds0
  have hoffsets :=
    round_round_sqrt_offsets_pos
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ hx_pos hf2
  have hb_pos : 0 < b := by
    simpa [u1, hu1, u2, hu2, b, hb, bp, hbp] using hoffsets.2.2.1
  have hbp_pos : 0 < bp := by
    simpa [u1, hu1, u2, hu2, b, hb, bp, hbp] using hoffsets.2.2.2
  have ha_nonneg : 0 ≤ a := by
    have h := round_round_sqrt_floor_nonneg
      (beta := beta) (fexp := fexp1) (x := x) hβ
    simpa [a, ha] using h
  have hsq :=
    round_round_sqrt_sq_bounds_from_interval
      (x := x) (a := a) (u1 := u1) (u2 := u2)
      (b := b) (bp := bp) (le_of_lt hx_pos)
      (by rw [hb]) (by rw [hbp])
      (by linarith [ha_nonneg, hb_pos])
      (by linarith [ha_nonneg, hbp_pos])
      hbounds.1 hbounds.2
  by_cases ha_zero : a = 0
  · have hzero :=
      round_round_sqrt_zero_floor_contra_from_not_gap
        (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
        (x := x) hβ Hexp hx_pos hf2 hx_fmt hnot
    exact hzero (by simpa [a, ha] using ha_zero)
  · have ha_pos : 0 < a := by
      exact lt_of_le_of_ne ha_nonneg (Ne.symm ha_zero)
    have hgrid0 :=
      round_round_sqrt_floor_grid_of_pos
        (beta := beta) (fexp1 := fexp1) (x := x) hβ hx_pos
    have hgrid : ∃ ma : Int, a = (ma : ℝ) * p ∧ u1 = p := by
      simpa [a, ha, u1, hu1, e, he, p, hp] using
        hgrid0 (by simpa [a, ha] using ha_pos)
    rcases hgrid with ⟨ma, ha_grid, hu1_grid⟩
    exact
      round_round_sqrt_nonzero_floor_contra
        (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
        (x := x) (a := a) (u1 := u1) (u2 := u2) (b := b) (bp := bp)
        (scale := scale) (p := p) (e := e) (ma := ma)
        hβ Hexp hx_pos hf2 hx_fmt ha hu1 hu2 hb hbp he hp
        ha_grid hu1_grid hscale ha_pos hsq.1 hsq.2

/-- Coq `round_round_sqrt_radix_ge_4_aux` midpoint-gap payload.

This is the radix-`ge_4` counterpart of `round_round_sqrt_aux_midpoint_gap`.
The interval and zero-floor branches are shared; the nonzero-floor branch uses
the weaker radix-specific exponent premise together with `4 <= beta`. -/
theorem round_round_sqrt_radix_ge_4_aux_midpoint_gap
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x : ℝ) (hβ : 1 < beta) (hβ4 : 4 ≤ beta)
    (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    (1 / 2) * ulp beta fexp2 (Real.sqrt x) <
      |Real.sqrt x - midp beta fexp1 (Real.sqrt x)| := by
  classical
  by_contra hnot
  set a : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp1
    FloatSpec.Core.Generic_fmt.rnd_floor (Real.sqrt x) with ha
  set u1 : ℝ := ulp beta fexp1 (Real.sqrt x) with hu1
  set u2 : ℝ := ulp beta fexp2 (Real.sqrt x) with hu2
  set b : ℝ := (1 / 2) * (u1 - u2) with hb
  set bp : ℝ := (1 / 2) * (u1 + u2) with hbp
  set e : Int := fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) with he
  set p : ℝ := (beta : ℝ) ^ e with hp
  set scale : ℝ := (beta : ℝ) ^ (-(2 * e)) with hscale
  have hbounds0 :=
    round_round_sqrt_mid_bounds_from_not_gap
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hnot
  have hbounds : a + b ≤ Real.sqrt x ∧ Real.sqrt x ≤ a + bp := by
    simpa [a, ha, u1, hu1, u2, hu2, b, hb, bp, hbp] using hbounds0
  have hoffsets :=
    round_round_sqrt_offsets_pos
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (x := x) hβ hx_pos hf2
  have hb_pos : 0 < b := by
    simpa [u1, hu1, u2, hu2, b, hb, bp, hbp] using hoffsets.2.2.1
  have hbp_pos : 0 < bp := by
    simpa [u1, hu1, u2, hu2, b, hb, bp, hbp] using hoffsets.2.2.2
  have ha_nonneg : 0 ≤ a := by
    have h := round_round_sqrt_floor_nonneg
      (beta := beta) (fexp := fexp1) (x := x) hβ
    simpa [a, ha] using h
  have hsq :=
    round_round_sqrt_sq_bounds_from_interval
      (x := x) (a := a) (u1 := u1) (u2 := u2)
      (b := b) (bp := bp) (le_of_lt hx_pos)
      (by rw [hb]) (by rw [hbp])
      (by linarith [ha_nonneg, hb_pos])
      (by linarith [ha_nonneg, hbp_pos])
      hbounds.1 hbounds.2
  by_cases ha_zero : a = 0
  · have hzero :=
      round_round_sqrt_zero_floor_contra_from_not_gap_radix_ge_4
        (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
        (x := x) hβ Hexp hx_pos hf2 hx_fmt hnot
    exact hzero (by simpa [a, ha] using ha_zero)
  · have ha_pos : 0 < a := by
      exact lt_of_le_of_ne ha_nonneg (Ne.symm ha_zero)
    have hgrid0 :=
      round_round_sqrt_floor_grid_of_pos
        (beta := beta) (fexp1 := fexp1) (x := x) hβ hx_pos
    have hgrid : ∃ ma : Int, a = (ma : ℝ) * p ∧ u1 = p := by
      simpa [a, ha, u1, hu1, e, he, p, hp] using
        hgrid0 (by simpa [a, ha] using ha_pos)
    rcases hgrid with ⟨ma, ha_grid, hu1_grid⟩
    exact
      round_round_sqrt_nonzero_floor_contra_radix_ge_4
        (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
        (x := x) (a := a) (u1 := u1) (u2 := u2) (b := b) (bp := bp)
        (scale := scale) (p := p) (e := e) (ma := ma)
        hβ hβ4 Hexp hx_pos hf2 hx_fmt ha hu1 hu2 hb hbp he hp
        ha_grid hu1_grid hscale ha_pos hsq.1 hsq.2

/-- Coq: `round_round_sqrt_aux`. -/
theorem round_round_sqrt_aux
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (x : ℝ) (hβ : 1 < beta)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    (1 / 2) * ulp beta fexp2 (Real.sqrt x) <
      |Real.sqrt x - midp beta fexp1 (Real.sqrt x)| := by
  exact round_round_sqrt_aux_midpoint_gap (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) hβ Hexp
    hx_pos hf2 hx_fmt

/-- Coq: `round_round_sqrt_radix_ge_4_aux`. -/
theorem round_round_sqrt_radix_ge_4_aux
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta) (hβ4 : 4 ≤ beta)
    (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
    (x : ℝ)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    (1 / 2) * ulp beta fexp2 (Real.sqrt x) <
      |Real.sqrt x - midp beta fexp1 (Real.sqrt x)| := by
  exact round_round_sqrt_radix_ge_4_aux_midpoint_gap (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) hβ hβ4 Hexp
    hx_pos hf2 hx_fmt

/-- Coq `round_round_sqrt`, final positive case factored at
`round_round_sqrt_aux`.

This packages the non-arithmetic wrapper step: once the midpoint-gap payload
for `sqrt x` is available, `round_round_mid_cases` gives the desired double
rounding equality. -/
theorem round_round_sqrt_pos_from_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ) (hβ : 1 < beta)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
        FloatSpec.Core.Raux.mag beta (Real.sqrt x))
    (hgap :
      (1 / 2) * ulp beta fexp2 (Real.sqrt x) <
        |Real.sqrt x - midp beta fexp1 (Real.sqrt x)|) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (Real.sqrt x) := by
  classical
  exact
    round_round_mid_cases (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2) (x := Real.sqrt x) hβ
      (Real.sqrt_pos.mpr hx_pos) hf2 hf1
      (fun hmid => False.elim ((not_lt_of_ge hmid) hgap))

/-- Coq `round_round_sqrt`, factored at the missing arithmetic lemma
`round_round_sqrt_aux`.

The assumed `haux` is exactly the midpoint-gap payload supplied by upstream
`round_round_sqrt_aux`; this theorem proves the remaining sign, magnitude, and
midpoint-case wrapper logic. -/
theorem round_round_sqrt_from_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (haux :
      ∀ x : ℝ,
        0 < x →
        fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
          fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1 →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
        (1 / 2) * ulp beta fexp2 (Real.sqrt x) <
          |Real.sqrt x - midp beta fexp1 (Real.sqrt x)|)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2) :
    ∀ x : ℝ,
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 (Real.sqrt x) := by
  classical
  intro x hx_fmt
  by_cases hx_pos : 0 < x
  · have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hfx_lt :
        fexp1 (FloatSpec.Core.Raux.mag beta x) <
          FloatSpec.Core.Raux.mag beta x := by
      have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
        (beta := beta) (fexp := fexp1) x
      have hcexp_lt :
          FloatSpec.Core.Generic_fmt.cexp beta fexp1 x <
            FloatSpec.Core.Raux.mag beta x := by
        simpa [wp, PostCond.noThrow, Id.run, pure] using
          htrip ⟨hβ, hx_ne, hx_fmt⟩
      simpa [FloatSpec.Core.Generic_fmt.cexp] using hcexp_lt
    have hfsx_lt :
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) <
          FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
      by_cases hx_le_one : x ≤ 1
      · have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
        have hx_le_sqrt : x ≤ Real.sqrt x := by
          exact (Real.le_sqrt hx_nonneg hx_nonneg).2 (by nlinarith)
        have habs :
            |x| ≤ |Real.sqrt x| := by
          simpa [abs_of_nonneg hx_nonneg,
            abs_of_nonneg (Real.sqrt_nonneg x)] using hx_le_sqrt
        have hmag_le :
            FloatSpec.Core.Raux.mag beta x ≤
              FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
          have htrip := FloatSpec.Core.Raux.mag_le (beta := beta)
            (x := x) (y := Real.sqrt x) hβ hx_ne habs
          simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
        exact FloatSpec.Core.Generic_fmt.valid_exp_large
          (beta := beta) (fexp := fexp1)
          (k := FloatSpec.Core.Raux.mag beta x)
          (l := FloatSpec.Core.Raux.mag beta (Real.sqrt x)) hfx_lt hmag_le
      · have hx_gt_one : 1 < x := lt_of_not_ge hx_le_one
        have hf1_one_lt : fexp1 1 < 1 := by
          have h := Hexp.2.1 1
          have h' : 2 * fexp1 1 ≤ fexp1 1 := by
            simpa using h
          omega
        have hmag_ge_one :
            (1 : Int) ≤ FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
          have hsqrt_gt_one : 1 < Real.sqrt x := by
            rw [← Real.sqrt_one]
            apply Real.sqrt_lt_sqrt
            · norm_num
            · exact hx_gt_one
          have hlt :
              (beta : ℝ) ^ ((1 : Int) - 1) < |Real.sqrt x| := by
            simpa [abs_of_pos (lt_trans zero_lt_one hsqrt_gt_one)] using
              hsqrt_gt_one
          have htrip := FloatSpec.Core.Raux.mag_ge_bpow
            (beta := beta) (x := Real.sqrt x) (e := 1) hβ (le_of_lt hlt)
          simpa using htrip
        exact FloatSpec.Core.Generic_fmt.valid_exp_large
          (beta := beta) (fexp := fexp1)
          (k := 1) (l := FloatSpec.Core.Raux.mag beta (Real.sqrt x))
          hf1_one_lt hmag_ge_one
    have hf1 :
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
          FloatSpec.Core.Raux.mag beta (Real.sqrt x) := le_of_lt hfsx_lt
    have hf2 :
        fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
          fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1 := by
      have hlarge :
          fexp1 (2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x)) <
            2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
        rcases mag_sqrt_disj (beta := beta) x hβ hx_pos with hmag | hmag
        · have hlarge_x :
              fexp1 (FloatSpec.Core.Raux.mag beta x) <
                FloatSpec.Core.Raux.mag beta x := hfx_lt
          apply FloatSpec.Core.Generic_fmt.valid_exp_large
            (beta := beta) (fexp := fexp1)
            (k := FloatSpec.Core.Raux.mag beta x)
            (l := 2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x))
            hlarge_x
          omega
        · simpa [← hmag] using hfx_lt
      have h := Hexp.2.2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) hlarge
      omega
    exact
      round_round_sqrt_pos_from_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2) (x := x) hβ
        hx_pos hf2 hf1 (haux x hx_pos hf2 hx_fmt)
  · have hx_nonpos : x ≤ 0 := le_of_not_gt hx_pos
    have hsqrt : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos hx_nonpos
    have hzero_fmt1 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 0 :=
      FloatSpec.Core.Generic_fmt.generic_format_0_run
        (beta := beta) (fexp := fexp1)
    have hzero_fmt2 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 0 :=
      FloatSpec.Core.Generic_fmt.generic_format_0_run
        (beta := beta) (fexp := fexp2)
    have hinner0 :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) 0 = 0 :=
      FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2) (x := 0) hβ hzero_fmt2
    have houter0 :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) 0 = 0 :=
      FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp1)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice1) (x := 0) hβ hzero_fmt1
    simpa [round_round_eq, hsqrt, hinner0, houter0]

/-- Coq: `round_round_sqrt`. -/
theorem round_round_sqrt (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2) :
    ∀ x : ℝ,
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 (Real.sqrt x) := by
  exact
    round_round_sqrt_from_aux
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2) hβ
      (fun x hx_pos hf2 hx_fmt =>
        round_round_sqrt_aux_midpoint_gap
          (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
          (x := x) hβ Hexp hx_pos hf2 hx_fmt)
      Hexp

/-- Coq: `FLX_round_round_sqrt_hyp`. -/
theorem FLX_round_round_sqrt_hyp (prec prec' : Int) [Prec_gt_0 prec]
    (hprec : 2 * prec + 2 ≤ prec') :
    round_round_sqrt_hyp
      (FloatSpec.Core.FLX.FLX_exp prec)
      (FloatSpec.Core.FLX.FLX_exp prec') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  unfold round_round_sqrt_hyp FloatSpec.Core.FLX.FLX_exp
  constructor
  · intro ex
    omega
  constructor
  · intro ex
    omega
  · intro ex _
    omega

/-- Coq: `FLT_round_round_sqrt_hyp`. -/
theorem FLT_round_round_sqrt_hyp
    (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (hemin : emin ≤ 0)
    (heminprec : emin' ≤ emin - prec - 2 ∨
      2 * emin' ≤ emin - 4 * prec - 2)
    (hprec : 2 * prec + 2 ≤ prec') :
    round_round_sqrt_hyp
      (FloatSpec.Core.FLT.FLT_exp prec emin)
      (FloatSpec.Core.FLT.FLT_exp prec' emin') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec'_pos : 0 < prec' := (Prec_gt_0.pos : 0 < prec')
  rcases heminprec with heminprec | heminprec
  · unfold round_round_sqrt_hyp FloatSpec.Core.FLT.FLT_exp
    constructor
    · intro ex
      grind
    constructor
    · intro ex
      grind
    · intro ex h
      grind
  · unfold round_round_sqrt_hyp FloatSpec.Core.FLT.FLT_exp
    constructor
    · intro ex
      grind
    constructor
    · intro ex
      grind
    · intro ex h
      grind

/-- Coq: `FTZ_round_round_sqrt_hyp`. -/
theorem FTZ_round_round_sqrt_hyp
    (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
    (hprec : 2 * prec + 2 ≤ prec') :
    round_round_sqrt_hyp
      (FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (FloatSpec.Core.FTZ.FTZ_exp prec' emin') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec'_pos : 0 < prec' := (Prec_gt_0.pos : 0 < prec')
  rcases hemin with ⟨hemin_low, hemin_high⟩
  unfold round_round_sqrt_hyp FloatSpec.Core.FTZ.FTZ_exp
  constructor
  · intro ex
    split_ifs <;> omega
  constructor
  · intro ex
    split_ifs <;> omega
  · intro ex h
    split_ifs at h ⊢ <;> omega

/-- Coq: `round_round_sqrt_FLX`. -/
theorem round_round_sqrt_FLX (prec prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hprec : 2 * prec + 2 ≤ prec')
    (x : ℝ)
    (hx : FloatSpec.Core.FLX.FLX_format prec beta x) :
    round_round_eq beta
      (FloatSpec.Core.FLX.FLX_exp prec)
      (FloatSpec.Core.FLX.FLX_exp prec')
      choice1 choice2 (Real.sqrt x) := by
  exact
    round_round_sqrt (beta := beta)
      (fexp1 := FloatSpec.Core.FLX.FLX_exp prec)
      (fexp2 := FloatSpec.Core.FLX.FLX_exp prec')
      (choice1 := choice1) (choice2 := choice2) hβ
      (FLX_round_round_sqrt_hyp (prec := prec) (prec' := prec') hprec)
      x (by simpa [FloatSpec.Core.FLX.FLX_format] using hx)

/-- Coq: `round_round_sqrt_FLT`. -/
theorem round_round_sqrt_FLT (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hemin : emin ≤ 0)
    (heminprec : emin' ≤ emin - prec - 2 ∨
      2 * emin' ≤ emin - 4 * prec - 2)
    (hprec : 2 * prec + 2 ≤ prec')
    (x : ℝ)
    (hx : FloatSpec.Core.FLT.FLT_format prec emin beta x) :
    round_round_eq beta
      (FloatSpec.Core.FLT.FLT_exp prec emin)
      (FloatSpec.Core.FLT.FLT_exp prec' emin')
      choice1 choice2 (Real.sqrt x) := by
  exact
    round_round_sqrt (beta := beta)
      (fexp1 := FloatSpec.Core.FLT.FLT_exp prec emin)
      (fexp2 := FloatSpec.Core.FLT.FLT_exp prec' emin')
      (choice1 := choice1) (choice2 := choice2) hβ
      (FLT_round_round_sqrt_hyp
        (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
        hemin heminprec hprec)
      x (by simpa [FloatSpec.Core.FLT.FLT_format] using hx)

/-- Coq: `round_round_sqrt_FTZ`. -/
theorem round_round_sqrt_FTZ (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
    (hprec : 2 * prec + 2 ≤ prec')
    (x : ℝ)
    (hx : FloatSpec.Core.FTZ.FTZ_format prec emin beta x) :
    round_round_eq beta
      (FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (FloatSpec.Core.FTZ.FTZ_exp prec' emin')
      choice1 choice2 (Real.sqrt x) := by
  exact
    round_round_sqrt (beta := beta)
      (fexp1 := FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (fexp2 := FloatSpec.Core.FTZ.FTZ_exp prec' emin')
      (choice1 := choice1) (choice2 := choice2) hβ
      (FTZ_round_round_sqrt_hyp
        (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
        hemin hprec)
      x (by simpa [FloatSpec.Core.FTZ.FTZ_format] using hx)

/-- Coq `round_round_sqrt_radix_ge_4`, factored at the missing arithmetic lemma
`round_round_sqrt_radix_ge_4_aux`.

The assumed `haux` is the radix-4 midpoint-gap payload. This theorem proves the
remaining final-wrapper logic, including the weaker radix-4 exponent side
condition. -/
theorem round_round_sqrt_radix_ge_4_from_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (haux :
      ∀ x : ℝ,
        0 < x →
        fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
          fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1 →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
        (1 / 2) * ulp beta fexp2 (Real.sqrt x) <
          |Real.sqrt x - midp beta fexp1 (Real.sqrt x)|)
    (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2) :
    ∀ x : ℝ,
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 (Real.sqrt x) := by
  classical
  intro x hx_fmt
  by_cases hx_pos : 0 < x
  · have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hfx_lt :
        fexp1 (FloatSpec.Core.Raux.mag beta x) <
          FloatSpec.Core.Raux.mag beta x := by
      have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
        (beta := beta) (fexp := fexp1) x
      have hcexp_lt :
          FloatSpec.Core.Generic_fmt.cexp beta fexp1 x <
            FloatSpec.Core.Raux.mag beta x := by
        simpa [wp, PostCond.noThrow, Id.run, pure] using
          htrip ⟨hβ, hx_ne, hx_fmt⟩
      simpa [FloatSpec.Core.Generic_fmt.cexp] using hcexp_lt
    have hfsx_lt :
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) <
          FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
      by_cases hx_le_one : x ≤ 1
      · have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
        have hx_le_sqrt : x ≤ Real.sqrt x := by
          exact (Real.le_sqrt hx_nonneg hx_nonneg).2 (by nlinarith)
        have habs :
            |x| ≤ |Real.sqrt x| := by
          simpa [abs_of_nonneg hx_nonneg,
            abs_of_nonneg (Real.sqrt_nonneg x)] using hx_le_sqrt
        have hmag_le :
            FloatSpec.Core.Raux.mag beta x ≤
              FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
          have htrip := FloatSpec.Core.Raux.mag_le (beta := beta)
            (x := x) (y := Real.sqrt x) hβ hx_ne habs
          simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
        exact FloatSpec.Core.Generic_fmt.valid_exp_large
          (beta := beta) (fexp := fexp1)
          (k := FloatSpec.Core.Raux.mag beta x)
          (l := FloatSpec.Core.Raux.mag beta (Real.sqrt x)) hfx_lt hmag_le
      · have hx_gt_one : 1 < x := lt_of_not_ge hx_le_one
        have hf1_one_lt : fexp1 1 < 1 := by
          have h := Hexp.2.1 1
          have h' : 2 * fexp1 1 ≤ fexp1 1 := by
            simpa using h
          omega
        have hmag_ge_one :
            (1 : Int) ≤ FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
          have hsqrt_gt_one : 1 < Real.sqrt x := by
            rw [← Real.sqrt_one]
            apply Real.sqrt_lt_sqrt
            · norm_num
            · exact hx_gt_one
          have hlt :
              (beta : ℝ) ^ ((1 : Int) - 1) < |Real.sqrt x| := by
            simpa [abs_of_pos (lt_trans zero_lt_one hsqrt_gt_one)] using
              hsqrt_gt_one
          have htrip := FloatSpec.Core.Raux.mag_ge_bpow
            (beta := beta) (x := Real.sqrt x) (e := 1) hβ (le_of_lt hlt)
          simpa using htrip
        exact FloatSpec.Core.Generic_fmt.valid_exp_large
          (beta := beta) (fexp := fexp1)
          (k := 1) (l := FloatSpec.Core.Raux.mag beta (Real.sqrt x))
          hf1_one_lt hmag_ge_one
    have hf1 :
        fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
          FloatSpec.Core.Raux.mag beta (Real.sqrt x) := le_of_lt hfsx_lt
    have hf2 :
        fexp2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) ≤
          fexp1 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) - 1 := by
      have hlarge :
          fexp1 (2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x)) <
            2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
        rcases mag_sqrt_disj (beta := beta) x hβ hx_pos with hmag | hmag
        · have hlarge_x :
              fexp1 (FloatSpec.Core.Raux.mag beta x) <
                FloatSpec.Core.Raux.mag beta x := hfx_lt
          apply FloatSpec.Core.Generic_fmt.valid_exp_large
            (beta := beta) (fexp := fexp1)
            (k := FloatSpec.Core.Raux.mag beta x)
            (l := 2 * FloatSpec.Core.Raux.mag beta (Real.sqrt x))
            hlarge_x
          omega
        · simpa [← hmag] using hfx_lt
      have h := Hexp.2.2 (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) hlarge
      omega
    exact
      round_round_sqrt_pos_from_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2) (x := x) hβ
        hx_pos hf2 hf1 (haux x hx_pos hf2 hx_fmt)
  · have hx_nonpos : x ≤ 0 := le_of_not_gt hx_pos
    have hsqrt : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos hx_nonpos
    have hzero_fmt1 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 0 :=
      FloatSpec.Core.Generic_fmt.generic_format_0_run
        (beta := beta) (fexp := fexp1)
    have hzero_fmt2 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 0 :=
      FloatSpec.Core.Generic_fmt.generic_format_0_run
        (beta := beta) (fexp := fexp2)
    have hinner0 :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) 0 = 0 :=
      FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2) (x := 0) hβ hzero_fmt2
    have houter0 :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) 0 = 0 :=
      FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp1)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice1) (x := 0) hβ hzero_fmt1
    simpa [round_round_eq, hsqrt, hinner0, houter0]

/-- Coq: `round_round_sqrt_radix_ge_4`. -/
theorem round_round_sqrt_radix_ge_4 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta) (hβ4 : 4 ≤ beta)
    (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2) :
    ∀ x : ℝ,
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 (Real.sqrt x) := by
  exact
    round_round_sqrt_radix_ge_4_from_aux
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2) hβ
      (fun x hx_pos hf2 hx_fmt =>
        round_round_sqrt_radix_ge_4_aux_midpoint_gap
          (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
          (x := x) hβ hβ4 Hexp hx_pos hf2 hx_fmt)
      Hexp

/-- Coq: `FLX_round_round_sqrt_radix_ge_4_hyp`. -/
theorem FLX_round_round_sqrt_radix_ge_4_hyp (prec prec' : Int)
    [Prec_gt_0 prec]
    (hprec : 2 * prec + 1 ≤ prec') :
    round_round_sqrt_radix_ge_4_hyp
      (FloatSpec.Core.FLX.FLX_exp prec)
      (FloatSpec.Core.FLX.FLX_exp prec') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  unfold round_round_sqrt_radix_ge_4_hyp FloatSpec.Core.FLX.FLX_exp
  constructor
  · intro ex
    omega
  constructor
  · intro ex
    omega
  · intro ex _
    omega

/-- Coq: `FLT_round_round_sqrt_radix_ge_4_hyp`. -/
theorem FLT_round_round_sqrt_radix_ge_4_hyp
    (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (hemin : emin ≤ 0)
    (heminprec : emin' ≤ emin - prec - 1 ∨
      2 * emin' ≤ emin - 4 * prec)
    (hprec : 2 * prec + 1 ≤ prec') :
    round_round_sqrt_radix_ge_4_hyp
      (FloatSpec.Core.FLT.FLT_exp prec emin)
      (FloatSpec.Core.FLT.FLT_exp prec' emin') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec'_pos : 0 < prec' := (Prec_gt_0.pos : 0 < prec')
  rcases heminprec with heminprec | heminprec
  · unfold round_round_sqrt_radix_ge_4_hyp FloatSpec.Core.FLT.FLT_exp
    constructor
    · intro ex
      grind
    constructor
    · intro ex
      grind
    · intro ex h
      grind
  · unfold round_round_sqrt_radix_ge_4_hyp FloatSpec.Core.FLT.FLT_exp
    constructor
    · intro ex
      grind
    constructor
    · intro ex
      grind
    · intro ex h
      grind

/-- Coq: `FTZ_round_round_sqrt_radix_ge_4_hyp`. -/
theorem FTZ_round_round_sqrt_radix_ge_4_hyp
    (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
    (hprec : 2 * prec + 1 ≤ prec') :
    round_round_sqrt_radix_ge_4_hyp
      (FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (FloatSpec.Core.FTZ.FTZ_exp prec' emin') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec'_pos : 0 < prec' := (Prec_gt_0.pos : 0 < prec')
  rcases hemin with ⟨hemin_low, hemin_high⟩
  unfold round_round_sqrt_radix_ge_4_hyp FloatSpec.Core.FTZ.FTZ_exp
  constructor
  · intro ex
    split_ifs <;> omega
  constructor
  · intro ex
    split_ifs <;> omega
  · intro ex h
    split_ifs at h ⊢ <;> omega

/-- Coq: `round_round_sqrt_radix_ge_4_FLX`. -/
theorem round_round_sqrt_radix_ge_4_FLX (prec prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hβ4 : 4 ≤ beta)
    (hprec : 2 * prec + 1 ≤ prec')
    (x : ℝ)
    (hx : FloatSpec.Core.FLX.FLX_format prec beta x) :
    round_round_eq beta
      (FloatSpec.Core.FLX.FLX_exp prec)
      (FloatSpec.Core.FLX.FLX_exp prec')
      choice1 choice2 (Real.sqrt x) := by
  exact
    round_round_sqrt_radix_ge_4 (beta := beta)
      (fexp1 := FloatSpec.Core.FLX.FLX_exp prec)
      (fexp2 := FloatSpec.Core.FLX.FLX_exp prec')
      (choice1 := choice1) (choice2 := choice2) hβ hβ4
      (FLX_round_round_sqrt_radix_ge_4_hyp
        (prec := prec) (prec' := prec') hprec)
      x (by simpa [FloatSpec.Core.FLX.FLX_format] using hx)

/-- Coq: `round_round_sqrt_radix_ge_4_FLT`. -/
theorem round_round_sqrt_radix_ge_4_FLT (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hβ4 : 4 ≤ beta)
    (hemin : emin ≤ 0)
    (heminprec : emin' ≤ emin - prec - 1 ∨
      2 * emin' ≤ emin - 4 * prec)
    (hprec : 2 * prec + 1 ≤ prec')
    (x : ℝ)
    (hx : FloatSpec.Core.FLT.FLT_format prec emin beta x) :
    round_round_eq beta
      (FloatSpec.Core.FLT.FLT_exp prec emin)
      (FloatSpec.Core.FLT.FLT_exp prec' emin')
      choice1 choice2 (Real.sqrt x) := by
  exact
    round_round_sqrt_radix_ge_4 (beta := beta)
      (fexp1 := FloatSpec.Core.FLT.FLT_exp prec emin)
      (fexp2 := FloatSpec.Core.FLT.FLT_exp prec' emin')
      (choice1 := choice1) (choice2 := choice2) hβ hβ4
      (FLT_round_round_sqrt_radix_ge_4_hyp
        (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
        hemin heminprec hprec)
      x (by simpa [FloatSpec.Core.FLT.FLT_format] using hx)

/-- Coq: `round_round_sqrt_radix_ge_4_FTZ`. -/
theorem round_round_sqrt_radix_ge_4_FTZ (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hβ4 : 4 ≤ beta)
    (hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
    (hprec : 2 * prec + 1 ≤ prec')
    (x : ℝ)
    (hx : FloatSpec.Core.FTZ.FTZ_format prec emin beta x) :
    round_round_eq beta
      (FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (FloatSpec.Core.FTZ.FTZ_exp prec' emin')
      choice1 choice2 (Real.sqrt x) := by
  exact
    round_round_sqrt_radix_ge_4 (beta := beta)
      (fexp1 := FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (fexp2 := FloatSpec.Core.FTZ.FTZ_exp prec' emin')
      (choice1 := choice1) (choice2 := choice2) hβ hβ4
      (FTZ_round_round_sqrt_radix_ge_4_hyp
        (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
        hemin hprec)
      x (by simpa [FloatSpec.Core.FTZ.FTZ_format] using hx)

/-- Coq: `mag_div_disj`. -/
theorem mag_div_disj (x y : ℝ)
    (hβ : 1 < beta)
    (hx_pos : 0 < x) (hy_pos : 0 < y) :
    FloatSpec.Core.Raux.mag beta (x / y) =
        FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
      FloatSpec.Core.Raux.mag beta (x / y) =
        FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1 := by
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have htrip := FloatSpec.Core.Raux.mag_div
    (beta := beta) (x := x) (y := y) hβ hx_ne hy_ne
  have hbounds :
      FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ≤
          FloatSpec.Core.Raux.mag beta (x / y) ∧
        FloatSpec.Core.Raux.mag beta (x / y) ≤
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1 := by
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  omega

/-- Coq: `round_round_div_hyp`. -/
def round_round_div_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex, fexp2 ex ≤ fexp1 ex - 1) ∧
  (∀ ex ey, fexp1 ex < ex → fexp1 ey < ey →
            fexp1 (ex - ey) ≤ ex - ey + 1 →
            fexp2 (ex - ey) ≤ fexp1 ex - ey) ∧
  (∀ ex ey, fexp1 ex < ex → fexp1 ey < ey →
            fexp1 (ex - ey + 1) ≤ ex - ey + 1 + 1 →
            fexp2 (ex - ey + 1) ≤ fexp1 ex - ey) ∧
  (∀ ex ey, fexp1 ex < ex → fexp1 ey < ey →
            fexp1 (ex - ey) ≤ ex - ey →
            fexp2 (ex - ey) ≤ fexp1 (ex - ey) + fexp1 ey - ey) ∧
  (∀ ex ey, fexp1 ex < ex → fexp1 ey < ey →
            fexp1 (ex - ey) = ex - ey + 1 →
            fexp2 (ex - ey) ≤ ex - ey - ey + fexp1 ey)

/-- Real contradiction step used by Coq `round_round_div_aux0`.

Once the integer-scaling part of the proof gives a gap between `x` and the
binade boundary, and the exponent part shows the half second-format ulp is
smaller than that gap after multiplication by `y`, the forbidden top-binade
band is impossible. -/
theorem round_round_div_aux0_contra_from_gap
    (x y p u2 gap : ℝ)
    (hy_pos : 0 < y)
    (hband : p - (1 / 2) * u2 ≤ x / y)
    (hgap : x ≤ p * y - gap)
    (hsmall : (1 / 2) * u2 * y < gap) : False := by
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hmul := mul_le_mul_of_nonneg_right hband (le_of_lt hy_pos)
  have hband_y : p * y - (1 / 2) * u2 * y ≤ x := by
    have hcancel : (x / y) * y = x := by
      field_simp [hy_ne]
    nlinarith [hmul]
  have hstrict : p * y - gap < p * y - (1 / 2) * u2 * y := by
    linarith
  linarith

/-- Exponent-to-gap comparison used in Coq `round_round_div_aux0`.

Both branches of the Coq proof reduce the small-ulp side condition to an
integer exponent inequality of the form `uExp + yMag ≤ gapExp`, together with
the magnitude bound `y < beta^yMag`. This lemma performs the real-valued
power comparison. -/
theorem round_round_div_aux0_half_ulp_y_lt_gap_pow
    (y : ℝ) (uExp yMag gapExp : Int)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hy_lt : y < (beta : ℝ) ^ yMag)
    (hexp : uExp + yMag ≤ gapExp) :
    (1 / 2) * (beta : ℝ) ^ uExp * y < (beta : ℝ) ^ gapExp := by
  have _hy_nonneg : 0 ≤ y := le_of_lt hy_pos
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hhalf_pos : (0 : ℝ) < (1 / 2) := by norm_num
  have hscale_pos : 0 < (1 / 2) * (beta : ℝ) ^ uExp :=
    mul_pos hhalf_pos (zpow_pos hbposR uExp)
  have hstep :
      (1 / 2) * (beta : ℝ) ^ uExp * y <
        (1 / 2) * (beta : ℝ) ^ uExp * (beta : ℝ) ^ yMag := by
    simpa [mul_assoc] using mul_lt_mul_of_pos_left hy_lt hscale_pos
  have hprod :
      (1 / 2) * (beta : ℝ) ^ uExp * (beta : ℝ) ^ yMag =
        (1 / 2) * (beta : ℝ) ^ (uExp + yMag) := by
    calc
      (1 / 2) * (beta : ℝ) ^ uExp * (beta : ℝ) ^ yMag
          = (1 / 2) * ((beta : ℝ) ^ uExp * (beta : ℝ) ^ yMag) := by ring
      _ = (1 / 2) * (beta : ℝ) ^ (uExp + yMag) := by
            rw [← zpow_add₀ hbne uExp yMag]
  have hpow_le :
      (beta : ℝ) ^ (uExp + yMag) ≤ (beta : ℝ) ^ gapExp :=
    ((zpow_right_strictMono₀ hβR).monotone hexp)
  have hhalf_le :
      (1 / 2) * (beta : ℝ) ^ (uExp + yMag) ≤
        (beta : ℝ) ^ (uExp + yMag) := by
    have hpow_nonneg : 0 ≤ (beta : ℝ) ^ (uExp + yMag) :=
      le_of_lt (zpow_pos hbposR _)
    nlinarith
  have hstep_gap :
      (1 / 2) * (beta : ℝ) ^ uExp * y <
        (1 / 2) * (beta : ℝ) ^ (uExp + yMag) := by
    rw [← hprod]
    exact hstep
  exact lt_of_lt_of_le hstep_gap (le_trans hhalf_le hpow_le)

/-- Power comparison used by Coq `round_round_div_aux1` and
`round_round_div_aux2`.

Unlike the aux0 helper above, the midpoint-band branches need the full
second-format ulp scaled by `y` to be below the relevant gap. -/
theorem round_round_div_ulp_y_lt_gap_pow
    (y : ℝ) (uExp yMag gapExp : Int)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hy_lt : y < (beta : ℝ) ^ yMag)
    (hexp : uExp + yMag ≤ gapExp) :
    (beta : ℝ) ^ uExp * y < (beta : ℝ) ^ gapExp := by
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hscale_pos : 0 < (beta : ℝ) ^ uExp :=
    zpow_pos hbposR uExp
  have hstep :
      (beta : ℝ) ^ uExp * y <
        (beta : ℝ) ^ uExp * (beta : ℝ) ^ yMag := by
    exact mul_lt_mul_of_pos_left hy_lt hscale_pos
  have hprod :
      (beta : ℝ) ^ uExp * (beta : ℝ) ^ yMag =
        (beta : ℝ) ^ (uExp + yMag) := by
    exact (zpow_add₀ hbne uExp yMag).symm
  have hpow_le :
      (beta : ℝ) ^ (uExp + yMag) ≤ (beta : ℝ) ^ gapExp :=
    ((zpow_right_strictMono₀ hβR).monotone hexp)
  exact lt_of_lt_of_le (by simpa [hprod] using hstep) hpow_le

/-- Integer exponent gap for the first branch of Coq `round_round_div_aux0`.

In the branch where the mantissa arithmetic gives the gap
`beta^(mag (x / y) + fexp1 (mag y))`, the small-ulp comparison reduces to this
integer inequality. Upstream proves it by splitting `mag_div_disj` and applying
the fifth clause of `round_round_div_hyp` in both cases. -/
theorem round_round_div_aux0_top_gap_exp_first
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (hexp : round_round_div_hyp fexp1 fexp2)
    (mx my mxy : Int)
    (hfx : fexp1 mx < mx)
    (hfy : fexp1 my < my)
    (htop : fexp1 mxy = mxy + 1)
    (hdisj : mxy = mx - my ∨ mxy = mx - my + 1) :
    fexp2 mxy + my ≤ mxy + fexp1 my := by
  rcases hdisj with hxy | hxy
  · subst mxy
    have hle := hexp.2.2.2.2 mx my hfx hfy htop
    omega
  · subst mxy
    have hfx_succ : fexp1 (mx + 1) < mx + 1 := by
      have hstep := (FloatSpec.Core.Generic_fmt.Valid_exp.valid_exp
        (beta := beta) (fexp := fexp1) mx).left hfx
      omega
    have harg : (mx + 1) - my = mx - my + 1 := by omega
    have htop' : fexp1 ((mx + 1) - my) = (mx + 1) - my + 1 := by
      rw [harg]
      simpa [add_assoc] using htop
    have hle := hexp.2.2.2.2 (mx + 1) my hfx_succ hfy htop'
    have hle' : fexp2 (mx - my + 1) ≤ (mx + 1) - my - my + fexp1 my := by
      simpa [harg] using hle
    omega

/-- Integer exponent gap for the second branch of Coq `round_round_div_aux0`.

In the branch where the mantissa arithmetic gives the gap `beta^(fexp1 (mag x))`,
the small-ulp comparison reduces to this inequality. Upstream obtains it by
splitting `mag_div_disj`: the two cases use the second and third clauses of
`round_round_div_hyp`, with the top-binade equality supplying the required
first-format exponent bound. -/
theorem round_round_div_aux0_top_gap_exp_second
    (fexp1 fexp2 : Int → Int)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (mx my mxy : Int)
    (hfx : fexp1 mx < mx)
    (hfy : fexp1 my < my)
    (htop : fexp1 mxy = mxy + 1)
    (hdisj : mxy = mx - my ∨ mxy = mx - my + 1) :
    fexp2 mxy + my ≤ fexp1 mx := by
  rcases hdisj with hxy | hxy
  · subst mxy
    have hbound : fexp1 (mx - my) ≤ mx - my + 1 := by
      omega
    have hle := hexp.2.1 mx my hfx hfy hbound
    omega
  · subst mxy
    have hbound : fexp1 (mx - my + 1) ≤ mx - my + 1 + 1 := by
      omega
    have hle := hexp.2.2.1 mx my hfx hfy hbound
    omega

/-- First-branch half-ulp bound used by Coq `round_round_div_aux0`.

After the first branch's integer exponent inequality has been established, the
real comparison says that the half second-format ulp of `x / y`, scaled by
`y`, is strictly smaller than the branch gap
`beta^(mag (x / y) + fexp1 (mag y))`. -/
theorem round_round_div_aux0_half_ulp_lt_first_gap
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (htop :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
        FloatSpec.Core.Raux.mag beta (x / y) + 1)
    (hdisj :
      FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
        FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1) :
    (1 / 2) * ulp beta fexp2 (x / y) * y <
      (beta : ℝ) ^
        (FloatSpec.Core.Raux.mag beta (x / y) +
          fexp1 (FloatSpec.Core.Raux.mag beta y)) := by
  let mx : Int := FloatSpec.Core.Raux.mag beta x
  let my : Int := FloatSpec.Core.Raux.mag beta y
  let mxy : Int := FloatSpec.Core.Raux.mag beta (x / y)
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hxy_ne : x / y ≠ 0 := ne_of_gt hxy_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hy_lt : y < (beta : ℝ) ^ my := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := y) hβ hy_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Raux.abs_val, abs_of_pos hy_pos, my]
      using htrip True.intro
  have hulp :
      ulp beta fexp2 (x / y) = (beta : ℝ) ^ (fexp2 mxy) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp2) (x := x / y) hxy_ne
    simpa [mxy, FloatSpec.Core.Generic_fmt.cexp, wp,
      PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hexp_gap :
      fexp2 mxy + my ≤ mxy + fexp1 my :=
    round_round_div_aux0_top_gap_exp_first (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) hexp mx my mxy
      (by simpa [mx] using hfx) (by simpa [my] using hfy)
      (by simpa [mxy] using htop) (by simpa [mx, my, mxy] using hdisj)
  have hsmall :=
    round_round_div_aux0_half_ulp_y_lt_gap_pow (beta := beta)
      (y := y) (uExp := fexp2 mxy) (yMag := my)
      (gapExp := mxy + fexp1 my) hβ hy_pos hy_lt hexp_gap
  simpa [hulp, my, mxy] using hsmall

/-- Full second-format ulp bound for the first branch of Coq
`round_round_div_aux1`/`round_round_div_aux2`.

This is the same exponent comparison as aux0's first branch, but without the
factor `1/2`; it corresponds to the `u2 * bpow (mag y)` subproof in Flocq. -/
theorem round_round_div_ulp_lt_first_gap
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (htop :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
        FloatSpec.Core.Raux.mag beta (x / y) + 1)
    (hdisj :
      FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
        FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1) :
    ulp beta fexp2 (x / y) * y <
      (beta : ℝ) ^
        (FloatSpec.Core.Raux.mag beta (x / y) +
          fexp1 (FloatSpec.Core.Raux.mag beta y)) := by
  let mx : Int := FloatSpec.Core.Raux.mag beta x
  let my : Int := FloatSpec.Core.Raux.mag beta y
  let mxy : Int := FloatSpec.Core.Raux.mag beta (x / y)
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hxy_ne : x / y ≠ 0 := ne_of_gt hxy_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hy_lt : y < (beta : ℝ) ^ my := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := y) hβ hy_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Raux.abs_val, abs_of_pos hy_pos, my]
      using htrip True.intro
  have hulp :
      ulp beta fexp2 (x / y) = (beta : ℝ) ^ (fexp2 mxy) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp2) (x := x / y) hxy_ne
    simpa [mxy, FloatSpec.Core.Generic_fmt.cexp, wp,
      PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hexp_gap :
      fexp2 mxy + my ≤ mxy + fexp1 my :=
    round_round_div_aux0_top_gap_exp_first (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) hexp mx my mxy
      (by simpa [mx] using hfx) (by simpa [my] using hfy)
      (by simpa [mxy] using htop) (by simpa [mx, my, mxy] using hdisj)
  have hsmall :=
    round_round_div_ulp_y_lt_gap_pow (beta := beta)
      (y := y) (uExp := fexp2 mxy) (yMag := my)
      (gapExp := mxy + fexp1 my) hβ hy_pos hy_lt hexp_gap
  simpa [hulp, my, mxy] using hsmall

/-- Second-branch half-ulp bound used by Coq `round_round_div_aux0`.

After the second branch's integer exponent inequality has been established, the
real comparison says that the half second-format ulp of `x / y`, scaled by
`y`, is strictly smaller than the branch gap `beta^(fexp1 (mag x))`. -/
theorem round_round_div_aux0_half_ulp_lt_second_gap
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (htop :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
        FloatSpec.Core.Raux.mag beta (x / y) + 1)
    (hdisj :
      FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
        FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1) :
    (1 / 2) * ulp beta fexp2 (x / y) * y <
      (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x) := by
  let mx : Int := FloatSpec.Core.Raux.mag beta x
  let my : Int := FloatSpec.Core.Raux.mag beta y
  let mxy : Int := FloatSpec.Core.Raux.mag beta (x / y)
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hxy_ne : x / y ≠ 0 := ne_of_gt hxy_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hy_lt : y < (beta : ℝ) ^ my := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := y) hβ hy_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Raux.abs_val, abs_of_pos hy_pos, my]
      using htrip True.intro
  have hulp :
      ulp beta fexp2 (x / y) = (beta : ℝ) ^ (fexp2 mxy) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp2) (x := x / y) hxy_ne
    simpa [mxy, FloatSpec.Core.Generic_fmt.cexp, wp,
      PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hexp_gap :
      fexp2 mxy + my ≤ fexp1 mx :=
    round_round_div_aux0_top_gap_exp_second
      (fexp1 := fexp1) (fexp2 := fexp2) hexp mx my mxy
      (by simpa [mx] using hfx) (by simpa [my] using hfy)
      (by simpa [mxy] using htop) (by simpa [mx, my, mxy] using hdisj)
  have hsmall :=
    round_round_div_aux0_half_ulp_y_lt_gap_pow (beta := beta)
      (y := y) (uExp := fexp2 mxy) (yMag := my)
      (gapExp := fexp1 mx) hβ hy_pos hy_lt hexp_gap
  simpa [hulp, mx, my, mxy] using hsmall

/-- Full second-format ulp bound for the second branch of Coq
`round_round_div_aux1`/`round_round_div_aux2`. -/
theorem round_round_div_ulp_lt_second_gap
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (htop :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
        FloatSpec.Core.Raux.mag beta (x / y) + 1)
    (hdisj :
      FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
        FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1) :
    ulp beta fexp2 (x / y) * y <
      (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x) := by
  let mx : Int := FloatSpec.Core.Raux.mag beta x
  let my : Int := FloatSpec.Core.Raux.mag beta y
  let mxy : Int := FloatSpec.Core.Raux.mag beta (x / y)
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hxy_ne : x / y ≠ 0 := ne_of_gt hxy_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hy_lt : y < (beta : ℝ) ^ my := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := y) hβ hy_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Raux.abs_val, abs_of_pos hy_pos, my]
      using htrip True.intro
  have hulp :
      ulp beta fexp2 (x / y) = (beta : ℝ) ^ (fexp2 mxy) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp2) (x := x / y) hxy_ne
    simpa [mxy, FloatSpec.Core.Generic_fmt.cexp, wp,
      PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hexp_gap :
      fexp2 mxy + my ≤ fexp1 mx :=
    round_round_div_aux0_top_gap_exp_second
      (fexp1 := fexp1) (fexp2 := fexp2) hexp mx my mxy
      (by simpa [mx] using hfx) (by simpa [my] using hfy)
      (by simpa [mxy] using htop) (by simpa [mx, my, mxy] using hdisj)
  have hsmall :=
    round_round_div_ulp_y_lt_gap_pow (beta := beta)
      (y := y) (uExp := fexp2 mxy) (yMag := my)
      (gapExp := fexp1 mx) hβ hy_pos hy_lt hexp_gap
  simpa [hulp, mx, my, mxy] using hsmall

/-- Integer exponent gap for the first branch of Coq `round_round_div_aux1`
and `round_round_div_aux2`.

This is the non-top-binade analogue of
`round_round_div_aux0_top_gap_exp_first`: the fourth clause of
`round_round_div_hyp` gives
`fexp2 mxy + my <= fexp1 mxy + fexp1 my` from
`fexp1 mxy <= mxy`. -/
theorem round_round_div_low_gap_exp_first
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (hexp : round_round_div_hyp fexp1 fexp2)
    (mx my mxy : Int)
    (hfx : fexp1 mx < mx)
    (hfy : fexp1 my < my)
    (hf1 : fexp1 mxy ≤ mxy)
    (hdisj : mxy = mx - my ∨ mxy = mx - my + 1) :
    fexp2 mxy + my ≤ fexp1 mxy + fexp1 my := by
  rcases hdisj with hxy | hxy
  · subst mxy
    have hle := hexp.2.2.2.1 mx my hfx hfy hf1
    omega
  · subst mxy
    have hfx_succ : fexp1 (mx + 1) < mx + 1 := by
      have hstep := (FloatSpec.Core.Generic_fmt.Valid_exp.valid_exp
        (beta := beta) (fexp := fexp1) mx).left hfx
      omega
    have harg : (mx + 1) - my = mx - my + 1 := by omega
    have hf1' : fexp1 ((mx + 1) - my) ≤ (mx + 1) - my := by
      simpa [harg] using hf1
    have hle := hexp.2.2.2.1 (mx + 1) my hfx_succ hfy hf1'
    have hle' :
        fexp2 (mx - my + 1) ≤
          fexp1 (mx - my + 1) + fexp1 my - my := by
      simpa [harg] using hle
    omega

/-- Integer exponent gap for the second branch of Coq `round_round_div_aux1`
and `round_round_div_aux2`.

This is the non-top-binade analogue of
`round_round_div_aux0_top_gap_exp_second`; it uses the second and third clauses
of `round_round_div_hyp` after the `mag_div_disj` split. -/
theorem round_round_div_low_gap_exp_second
    (fexp1 fexp2 : Int → Int)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (mx my mxy : Int)
    (hfx : fexp1 mx < mx)
    (hfy : fexp1 my < my)
    (hf1 : fexp1 mxy ≤ mxy)
    (hdisj : mxy = mx - my ∨ mxy = mx - my + 1) :
    fexp2 mxy + my ≤ fexp1 mx := by
  rcases hdisj with hxy | hxy
  · subst mxy
    have hbound : fexp1 (mx - my) ≤ mx - my + 1 := by
      omega
    have hle := hexp.2.1 mx my hfx hfy hbound
    omega
  · subst mxy
    have hbound : fexp1 (mx - my + 1) ≤ mx - my + 1 + 1 := by
      omega
    have hle := hexp.2.2.1 mx my hfx hfy hbound
    omega

/-- Full second-format ulp bound for the first non-top branch of Coq
`round_round_div_aux1`/`round_round_div_aux2`. -/
theorem round_round_div_ulp_lt_first_gap_low
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        FloatSpec.Core.Raux.mag beta (x / y))
    (hdisj :
      FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
        FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1) :
    ulp beta fexp2 (x / y) * y <
      (beta : ℝ) ^
        (fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) +
          fexp1 (FloatSpec.Core.Raux.mag beta y)) := by
  let mx : Int := FloatSpec.Core.Raux.mag beta x
  let my : Int := FloatSpec.Core.Raux.mag beta y
  let mxy : Int := FloatSpec.Core.Raux.mag beta (x / y)
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hxy_ne : x / y ≠ 0 := ne_of_gt hxy_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hy_lt : y < (beta : ℝ) ^ my := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := y) hβ hy_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Raux.abs_val, abs_of_pos hy_pos, my]
      using htrip True.intro
  have hulp :
      ulp beta fexp2 (x / y) = (beta : ℝ) ^ (fexp2 mxy) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp2) (x := x / y) hxy_ne
    simpa [mxy, FloatSpec.Core.Generic_fmt.cexp, wp,
      PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hexp_gap :
      fexp2 mxy + my ≤ fexp1 mxy + fexp1 my :=
    round_round_div_low_gap_exp_first (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) hexp mx my mxy
      (by simpa [mx] using hfx) (by simpa [my] using hfy)
      (by simpa [mxy] using hf1) (by simpa [mx, my, mxy] using hdisj)
  have hsmall :=
    round_round_div_ulp_y_lt_gap_pow (beta := beta)
      (y := y) (uExp := fexp2 mxy) (yMag := my)
      (gapExp := fexp1 mxy + fexp1 my) hβ hy_pos hy_lt hexp_gap
  simpa [hulp, my, mxy] using hsmall

/-- Full second-format ulp bound for the second non-top branch of Coq
`round_round_div_aux1`/`round_round_div_aux2`. -/
theorem round_round_div_ulp_lt_second_gap_low
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        FloatSpec.Core.Raux.mag beta (x / y))
    (hdisj :
      FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
        FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1) :
    ulp beta fexp2 (x / y) * y <
      (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x) := by
  let mx : Int := FloatSpec.Core.Raux.mag beta x
  let my : Int := FloatSpec.Core.Raux.mag beta y
  let mxy : Int := FloatSpec.Core.Raux.mag beta (x / y)
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hxy_ne : x / y ≠ 0 := ne_of_gt hxy_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hy_lt : y < (beta : ℝ) ^ my := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := y) hβ hy_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Raux.abs_val, abs_of_pos hy_pos, my]
      using htrip True.intro
  have hulp :
      ulp beta fexp2 (x / y) = (beta : ℝ) ^ (fexp2 mxy) := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp2) (x := x / y) hxy_ne
    simpa [mxy, FloatSpec.Core.Generic_fmt.cexp, wp,
      PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hexp_gap :
      fexp2 mxy + my ≤ fexp1 mx :=
    round_round_div_low_gap_exp_second
      (fexp1 := fexp1) (fexp2 := fexp2) hexp mx my mxy
      (by simpa [mx] using hfx) (by simpa [my] using hfy)
      (by simpa [mxy] using hf1) (by simpa [mx, my, mxy] using hdisj)
  have hsmall :=
    round_round_div_ulp_y_lt_gap_pow (beta := beta)
      (y := y) (uExp := fexp2 mxy) (yMag := my)
      (gapExp := fexp1 mx) hβ hy_pos hy_lt hexp_gap
  simpa [hulp, mx, my, mxy] using hsmall

/-- First-branch top-binade contradiction for Coq `round_round_div_aux0`.

This packages the final contradiction once the branch-specific mantissa
arithmetic has produced the gap
`x ≤ beta^(mag (x / y)) * y - beta^(mag (x / y) + fexp1 (mag y))`. -/
theorem round_round_div_aux0_first_gap_contra
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (htop :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
        FloatSpec.Core.Raux.mag beta (x / y) + 1)
    (hdisj :
      FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
        FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1)
    (hband :
      (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
          (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y)
    (hgap :
      x ≤
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
          (beta : ℝ) ^
            (FloatSpec.Core.Raux.mag beta (x / y) +
              fexp1 (FloatSpec.Core.Raux.mag beta y))) :
    False := by
  have hsmall :=
    round_round_div_aux0_half_ulp_lt_first_gap (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) hβ hexp x y
      hx_pos hy_pos hfx hfy htop hdisj
  exact round_round_div_aux0_contra_from_gap
    (x := x) (y := y)
    (p := (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y))
    (u2 := ulp beta fexp2 (x / y))
    (gap := (beta : ℝ) ^
      (FloatSpec.Core.Raux.mag beta (x / y) +
        fexp1 (FloatSpec.Core.Raux.mag beta y)))
    hy_pos hband hgap hsmall

/-- Second-branch top-binade contradiction for Coq `round_round_div_aux0`.

This packages the final contradiction once the branch-specific mantissa
arithmetic has produced the gap
`x ≤ beta^(mag (x / y)) * y - beta^(fexp1 (mag x))`. -/
theorem round_round_div_aux0_second_gap_contra
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (htop :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
        FloatSpec.Core.Raux.mag beta (x / y) + 1)
    (hdisj :
      FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
        FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1)
    (hband :
      (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
          (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y)
    (hgap :
      x ≤
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
          (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x)) :
    False := by
  have hsmall :=
    round_round_div_aux0_half_ulp_lt_second_gap (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) hβ hexp x y
      hx_pos hy_pos hfx hfy htop hdisj
  exact round_round_div_aux0_contra_from_gap
    (x := x) (y := y)
    (p := (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y))
    (u2 := ulp beta fexp2 (x / y))
    (gap := (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x))
    hy_pos hband hgap hsmall

/-- Top-binade contradiction from the two Coq `round_round_div_aux0` gap cases.

This is the final dispatcher after the mantissa arithmetic has reduced the
top-binade case to one of the two branch gaps used by Coq's aux0 proof. -/
theorem round_round_div_aux0_gap_cases_contra
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (htop :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
        FloatSpec.Core.Raux.mag beta (x / y) + 1)
    (hband :
      (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
          (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y)
    (hgap :
      x ≤
          (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
            (beta : ℝ) ^
              (FloatSpec.Core.Raux.mag beta (x / y) +
                fexp1 (FloatSpec.Core.Raux.mag beta y)) ∨
        x ≤
          (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
            (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x)) :
    False := by
  have hdisj := mag_div_disj (beta := beta) (x := x) (y := y) hβ hx_pos hy_pos
  rcases hgap with hfirst | hsecond
  · exact round_round_div_aux0_first_gap_contra (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) hβ hexp x y
      hx_pos hy_pos hfx hfy htop hdisj hband hfirst
  · exact round_round_div_aux0_second_gap_contra (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) hβ hexp x y
      hx_pos hy_pos hfx hfy htop hdisj hband hsecond

/-- First aux0 mantissa branch as real arithmetic.

This ports the first arithmetic sub-block of Coq `round_round_div_aux0` after
`generic_format` has been unfolded. If the formatted values are
`x = mx * beta^fx` and `y = my * beta^fy`, the branch
`0 ≤ fx - mxy - fy` and the binade upper bound `x / y < beta^mxy` imply the
first gap
`x ≤ beta^mxy * y - beta^(mxy + fy)`. -/
theorem round_round_div_aux0_first_gap_from_repr
    (x y : ℝ) (mx my fx fy mxy : Int)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hx_repr : x = (mx : ℝ) * (beta : ℝ) ^ fx)
    (hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy)
    (hbranch : 0 ≤ fx - mxy - fy)
    (hdiv_lt : x / y < (beta : ℝ) ^ mxy) :
    x ≤
      (beta : ℝ) ^ mxy * y -
        (beta : ℝ) ^ (mxy + fy) := by
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hpow_fy_pos : 0 < (beta : ℝ) ^ fy := zpow_pos hbposR fy
  have hmy_pos_real : 0 < (my : ℝ) := by
    rw [hy_repr] at hy_pos
    by_contra hnot
    have hmy_nonpos : (my : ℝ) ≤ 0 := le_of_not_gt hnot
    have hprod_nonpos :
        (my : ℝ) * (beta : ℝ) ^ fy ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hmy_nonpos (le_of_lt hpow_fy_pos)
    linarith
  have hmy_pos_int : 0 < my := by exact_mod_cast hmy_pos_real
  let d : Int := fx - mxy - fy
  have hd_nonneg : 0 ≤ d := by simpa [d] using hbranch
  let n : Nat := Int.toNat d
  have hd_eq : (n : Int) = d := by
    simpa [n] using Int.toNat_of_nonneg hd_nonneg
  have hpow_d_nat : (beta : ℝ) ^ d = (beta : ℝ) ^ n := by
    simpa [n] using
      FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat (beta : ℝ) d hd_nonneg
  have hpow_d_cast : (beta : ℝ) ^ n = ((beta ^ n : Int) : ℝ) := by
    rw [← Int.cast_pow]
  have hsplit_fx :
      (beta : ℝ) ^ fx =
        (beta : ℝ) ^ d * (beta : ℝ) ^ (mxy + fy) := by
    have hsum : d + (mxy + fy) = fx := by
      dsimp [d]
      omega
    calc
      (beta : ℝ) ^ fx = (beta : ℝ) ^ (d + (mxy + fy)) := by rw [hsum]
      _ = (beta : ℝ) ^ d * (beta : ℝ) ^ (mxy + fy) := by
            exact zpow_add₀ hbne d (mxy + fy)
  have hsplit_mfy :
      (beta : ℝ) ^ mxy * (beta : ℝ) ^ fy =
        (beta : ℝ) ^ (mxy + fy) := by
    exact (zpow_add₀ hbne mxy fy).symm
  have hxy_lt : x < (beta : ℝ) ^ mxy * y := by
    have hmul := mul_lt_mul_of_pos_right hdiv_lt hy_pos
    have hcancel : (x / y) * y = x := by
      field_simp [hy_ne]
    calc
      x = (x / y) * y := hcancel.symm
      _ < (beta : ℝ) ^ mxy * y := hmul
  have hscaled_lt :
      ((mx * beta ^ n : Int) : ℝ) < (my : ℝ) := by
    have hlt_repr :
        (mx : ℝ) * (beta : ℝ) ^ d * (beta : ℝ) ^ (mxy + fy) <
          (my : ℝ) * (beta : ℝ) ^ (mxy + fy) := by
      calc
        (mx : ℝ) * (beta : ℝ) ^ d * (beta : ℝ) ^ (mxy + fy)
            = (mx : ℝ) * (beta : ℝ) ^ fx := by rw [hsplit_fx]; ring
        _ = x := hx_repr.symm
        _ < (beta : ℝ) ^ mxy * y := hxy_lt
        _ = (my : ℝ) * (beta : ℝ) ^ (mxy + fy) := by
              rw [hy_repr]
              rw [← hsplit_mfy]
              ring
    have hpow_gap_pos : 0 < (beta : ℝ) ^ (mxy + fy) :=
      zpow_pos hbposR (mxy + fy)
    have hlt_cancel :
        (mx : ℝ) * (beta : ℝ) ^ d < (my : ℝ) := by
      exact lt_of_mul_lt_mul_right hlt_repr (le_of_lt hpow_gap_pos)
    calc
      ((mx * beta ^ n : Int) : ℝ)
          = (mx : ℝ) * ((beta ^ n : Int) : ℝ) := by
              rw [Int.cast_mul]
      _ = (mx : ℝ) * (beta : ℝ) ^ n := by rw [Int.cast_pow]
      _ = (mx : ℝ) * (beta : ℝ) ^ d := by rw [hpow_d_nat]
      _ < (my : ℝ) := hlt_cancel
  have hint_lt : mx * beta ^ n < my := by
    exact_mod_cast hscaled_lt
  have hint_le : mx * beta ^ n ≤ my - 1 := by
    omega
  have hreal_le : ((mx * beta ^ n : Int) : ℝ) ≤ (my - 1 : Int) := by
    exact_mod_cast hint_le
  have hpow_gap_nonneg : 0 ≤ (beta : ℝ) ^ (mxy + fy) :=
    le_of_lt (zpow_pos hbposR (mxy + fy))
  have hmul_le :
      ((mx * beta ^ n : Int) : ℝ) * (beta : ℝ) ^ (mxy + fy) ≤
        ((my - 1 : Int) : ℝ) * (beta : ℝ) ^ (mxy + fy) :=
    mul_le_mul_of_nonneg_right hreal_le hpow_gap_nonneg
  calc
    x = (mx : ℝ) * (beta : ℝ) ^ fx := hx_repr
    _ = (mx : ℝ) * (beta : ℝ) ^ d * (beta : ℝ) ^ (mxy + fy) := by
          rw [hsplit_fx]
          ring
    _ = ((mx * beta ^ n : Int) : ℝ) * (beta : ℝ) ^ (mxy + fy) := by
          rw [Int.cast_mul, Int.cast_pow]
          rw [← hpow_d_nat]
    _ ≤ ((my - 1 : Int) : ℝ) * (beta : ℝ) ^ (mxy + fy) := hmul_le
    _ = (beta : ℝ) ^ mxy * y - (beta : ℝ) ^ (mxy + fy) := by
          rw [hy_repr]
          rw [← hsplit_mfy]
          rw [Int.cast_sub]
          ring

/-- First aux0 mantissa branch from formatted numerator and denominator.

This is the formatted-value version of
`round_round_div_aux0_first_gap_from_repr`: the integer mantissas are extracted
from the two `generic_format` witnesses exactly as in the Coq proof after
unfolding `generic_format`, `F2R`, `scaled_mantissa`, and `cexp`. -/
theorem round_round_div_aux0_first_gap_from_format
    (fexp1 : Int → Int)
    (x y : ℝ)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hbranch :
      0 ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
          FloatSpec.Core.Raux.mag beta (x / y) -
          fexp1 (FloatSpec.Core.Raux.mag beta y))
    (hdiv_lt : x / y < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y)) :
    x ≤
      (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
        (beta : ℝ) ^
          (FloatSpec.Core.Raux.mag beta (x / y) +
            fexp1 (FloatSpec.Core.Raux.mag beta y)) := by
  let mx : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 x)
  let my : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 y)
  let fx : Int := fexp1 (FloatSpec.Core.Raux.mag beta x)
  let fy : Int := fexp1 (FloatSpec.Core.Raux.mag beta y)
  let mxy : Int := FloatSpec.Core.Raux.mag beta (x / y)
  have hx_repr : x = (mx : ℝ) * (beta : ℝ) ^ fx := by
    simpa [FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Defs.F2R,
      mx, fx] using hx_fmt
  have hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy := by
    simpa [FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Defs.F2R,
      my, fy] using hy_fmt
  exact round_round_div_aux0_first_gap_from_repr (beta := beta)
    (x := x) (y := y) (mx := mx) (my := my)
    (fx := fx) (fy := fy) (mxy := mxy) hβ hy_pos
    hx_repr hy_repr
    (by simpa [fx, fy, mxy] using hbranch)
    (by simpa [mxy] using hdiv_lt)

/-- Second aux0 mantissa branch as real arithmetic.

This is the symmetric branch of Coq `round_round_div_aux0`: after unfolding the
formatted witnesses, the branch
`fexp1 (mag x) < mag (x / y) + fexp1 (mag y)` makes the missing unit in the
gap live at the numerator exponent `fx`. -/
theorem round_round_div_aux0_second_gap_from_repr
    (x y : ℝ) (mx my fx fy mxy : Int)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hx_repr : x = (mx : ℝ) * (beta : ℝ) ^ fx)
    (hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy)
    (hbranch : fx - mxy - fy < 0)
    (hdiv_lt : x / y < (beta : ℝ) ^ mxy) :
    x ≤
      (beta : ℝ) ^ mxy * y -
        (beta : ℝ) ^ fx := by
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  let d : Int := mxy + fy - fx
  have hd_pos : 0 < d := by
    dsimp [d]
    omega
  have hd_nonneg : 0 ≤ d := le_of_lt hd_pos
  let n : Nat := Int.toNat d
  have hpow_d_nat : (beta : ℝ) ^ d = (beta : ℝ) ^ n := by
    simpa [n] using
      FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat (beta : ℝ) d hd_nonneg
  have hsplit_right :
      (beta : ℝ) ^ (mxy + fy) =
        (beta : ℝ) ^ d * (beta : ℝ) ^ fx := by
    have hsum : d + fx = mxy + fy := by
      dsimp [d]
      omega
    calc
      (beta : ℝ) ^ (mxy + fy) = (beta : ℝ) ^ (d + fx) := by rw [hsum]
      _ = (beta : ℝ) ^ d * (beta : ℝ) ^ fx := by
            exact zpow_add₀ hbne d fx
  have hsplit_mfy :
      (beta : ℝ) ^ mxy * (beta : ℝ) ^ fy =
        (beta : ℝ) ^ (mxy + fy) := by
    exact (zpow_add₀ hbne mxy fy).symm
  have hxy_lt : x < (beta : ℝ) ^ mxy * y := by
    have hmul := mul_lt_mul_of_pos_right hdiv_lt hy_pos
    have hcancel : (x / y) * y = x := by
      field_simp [hy_ne]
    calc
      x = (x / y) * y := hcancel.symm
      _ < (beta : ℝ) ^ mxy * y := hmul
  have hscaled_lt :
      (mx : ℝ) < ((my * beta ^ n : Int) : ℝ) := by
    have hlt_repr :
        (mx : ℝ) * (beta : ℝ) ^ fx <
          (my : ℝ) * (beta : ℝ) ^ (mxy + fy) := by
      calc
        (mx : ℝ) * (beta : ℝ) ^ fx = x := hx_repr.symm
        _ < (beta : ℝ) ^ mxy * y := hxy_lt
        _ = (my : ℝ) * (beta : ℝ) ^ (mxy + fy) := by
              rw [hy_repr]
              rw [← hsplit_mfy]
              ring
    have hpow_fx_pos : 0 < (beta : ℝ) ^ fx := zpow_pos hbposR fx
    have hlt_cancel :
        (mx : ℝ) < (my : ℝ) * (beta : ℝ) ^ d := by
      have hlt_factor :
          (mx : ℝ) * (beta : ℝ) ^ fx <
            ((my : ℝ) * (beta : ℝ) ^ d) * (beta : ℝ) ^ fx := by
        calc
          (mx : ℝ) * (beta : ℝ) ^ fx
              < (my : ℝ) * (beta : ℝ) ^ (mxy + fy) := hlt_repr
          _ = ((my : ℝ) * (beta : ℝ) ^ d) * (beta : ℝ) ^ fx := by
                rw [hsplit_right]
                ring
      exact lt_of_mul_lt_mul_right hlt_factor (le_of_lt hpow_fx_pos)
    calc
      (mx : ℝ) < (my : ℝ) * (beta : ℝ) ^ d := hlt_cancel
      _ = (my : ℝ) * (beta : ℝ) ^ n := by rw [hpow_d_nat]
      _ = ((my * beta ^ n : Int) : ℝ) := by
            rw [Int.cast_mul, Int.cast_pow]
  have hint_lt : mx < my * beta ^ n := by
    exact_mod_cast hscaled_lt
  have hint_le : mx ≤ my * beta ^ n - 1 := by
    omega
  have hreal_le : (mx : ℝ) ≤ ((my * beta ^ n - 1 : Int) : ℝ) := by
    exact_mod_cast hint_le
  have hpow_fx_nonneg : 0 ≤ (beta : ℝ) ^ fx :=
    le_of_lt (zpow_pos hbposR fx)
  have hmul_le :
      (mx : ℝ) * (beta : ℝ) ^ fx ≤
        ((my * beta ^ n - 1 : Int) : ℝ) * (beta : ℝ) ^ fx :=
    mul_le_mul_of_nonneg_right hreal_le hpow_fx_nonneg
  calc
    x = (mx : ℝ) * (beta : ℝ) ^ fx := hx_repr
    _ ≤ ((my * beta ^ n - 1 : Int) : ℝ) * (beta : ℝ) ^ fx := hmul_le
    _ = ((my : ℝ) * (beta : ℝ) ^ d - 1) * (beta : ℝ) ^ fx := by
          rw [Int.cast_sub, Int.cast_mul, Int.cast_pow]
          rw [← hpow_d_nat]
          norm_num
    _ = (my : ℝ) * (beta : ℝ) ^ (mxy + fy) - (beta : ℝ) ^ fx := by
          rw [hsplit_right]
          ring
    _ = (beta : ℝ) ^ mxy * y - (beta : ℝ) ^ fx := by
          rw [hy_repr]
          rw [← hsplit_mfy]
          ring

/-- Second aux0 mantissa branch from formatted numerator and denominator. -/
theorem round_round_div_aux0_second_gap_from_format
    (fexp1 : Int → Int)
    (x y : ℝ)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hbranch :
      fexp1 (FloatSpec.Core.Raux.mag beta x) -
          FloatSpec.Core.Raux.mag beta (x / y) -
          fexp1 (FloatSpec.Core.Raux.mag beta y) < 0)
    (hdiv_lt : x / y < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y)) :
    x ≤
      (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
        (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x) := by
  let mx : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 x)
  let my : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 y)
  let fx : Int := fexp1 (FloatSpec.Core.Raux.mag beta x)
  let fy : Int := fexp1 (FloatSpec.Core.Raux.mag beta y)
  let mxy : Int := FloatSpec.Core.Raux.mag beta (x / y)
  have hx_repr : x = (mx : ℝ) * (beta : ℝ) ^ fx := by
    simpa [FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Defs.F2R,
      mx, fx] using hx_fmt
  have hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy := by
    simpa [FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Defs.F2R,
      my, fy] using hy_fmt
  exact round_round_div_aux0_second_gap_from_repr (beta := beta)
    (x := x) (y := y) (mx := mx) (my := my)
    (fx := fx) (fy := fy) (mxy := mxy) hβ hy_pos
    hx_repr hy_repr
    (by simpa [fx, fy, mxy] using hbranch)
    (by simpa [mxy] using hdiv_lt)

/-- Coq `round_round_div_aux0` branch split.

This is the `Zle_or_lt` split on
`fexp1 (mag x) - mag (x / y) - fexp1 (mag y)` from the upstream proof. It
separates the remaining mantissa arithmetic into the first gap branch and the
second gap branch, matching the two cases consumed by
`round_round_div_aux0_gap_cases_contra`. -/
theorem round_round_div_aux0_gap_cases_from_exponent_split
    (fexp1 : Int → Int)
    (x y : ℝ)
    (hfirst :
      0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            FloatSpec.Core.Raux.mag beta (x / y) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        x ≤
          (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
            (beta : ℝ) ^
              (FloatSpec.Core.Raux.mag beta (x / y) +
                fexp1 (FloatSpec.Core.Raux.mag beta y)))
    (hsecond :
      fexp1 (FloatSpec.Core.Raux.mag beta x) -
          FloatSpec.Core.Raux.mag beta (x / y) -
          fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        x ≤
          (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
            (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x)) :
    x ≤
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
          (beta : ℝ) ^
            (FloatSpec.Core.Raux.mag beta (x / y) +
              fexp1 (FloatSpec.Core.Raux.mag beta y)) ∨
      x ≤
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
          (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x) := by
  by_cases hsplit :
      0 ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
          FloatSpec.Core.Raux.mag beta (x / y) -
          fexp1 (FloatSpec.Core.Raux.mag beta y)
  · exact Or.inl (hfirst hsplit)
  · exact Or.inr (hsecond (lt_of_not_ge hsplit))

/-- Coq `round_round_div_aux0` gap disjunction from formatted inputs.

This composes the upstream `Zle_or_lt` split with the two checked mantissa
arithmetic branches, leaving only the standard binade upper bound on `x / y` as
input. -/
theorem round_round_div_aux0_gap_cases_from_format
    (fexp1 : Int → Int)
    (x y : ℝ)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hdiv_lt : x / y < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y)) :
    x ≤
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
          (beta : ℝ) ^
            (FloatSpec.Core.Raux.mag beta (x / y) +
              fexp1 (FloatSpec.Core.Raux.mag beta y)) ∨
      x ≤
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
          (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x) := by
  exact round_round_div_aux0_gap_cases_from_exponent_split (beta := beta)
    (fexp1 := fexp1) (x := x) (y := y)
    (by
      intro hbranch
      exact round_round_div_aux0_first_gap_from_format (beta := beta)
        (fexp1 := fexp1) (x := x) (y := y) hβ hy_pos hx_fmt hy_fmt
        hbranch hdiv_lt)
    (by
      intro hbranch
      exact round_round_div_aux0_second_gap_from_format (beta := beta)
        (fexp1 := fexp1) (x := x) (y := y) hβ hy_pos hx_fmt hy_fmt
        hbranch hdiv_lt)

/-- Coq `round_round_div_aux0`, factored at the mantissa gap arithmetic.

The upstream proof first unfolds the `generic_format` witnesses for `x` and
`y`, then proves one of the two real gap inequalities consumed by
`round_round_div_aux0_gap_cases_contra`. This theorem packages the surrounding
logic: once that gap disjunction is available, the top-binade branch is
excluded in the exact shape required by the division dispatcher. -/
theorem round_round_div_aux0_from_gap_cases
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hgap :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
          FloatSpec.Core.Raux.mag beta (x / y) + 1 →
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
            (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y →
        x ≤
            (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
              (beta : ℝ) ^
                (FloatSpec.Core.Raux.mag beta (x / y) +
                  fexp1 (FloatSpec.Core.Raux.mag beta y)) ∨
          x ≤
            (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
              (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x)) :
    fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
        FloatSpec.Core.Raux.mag beta (x / y) + 1 →
      ¬ ((beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
          (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y) := by
  intro htop hband
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp1) x
    simpa [wp, PostCond.noThrow, Id.run, pure] using
      htrip ⟨hβ, hx_ne, hx_fmt⟩
  have hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp1) y
    simpa [wp, PostCond.noThrow, Id.run, pure] using
      htrip ⟨hβ, hy_ne, hy_fmt⟩
  exact round_round_div_aux0_gap_cases_contra (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) hβ hexp x y
    hx_pos hy_pos hfx hfy htop hband (hgap htop hband)

/-- Coq `round_round_div_aux0` with the mantissa gap arithmetic restored.

This closes the top-binade branch directly from the formatted numerator and
denominator. It is the aux0 exclusion needed by the remaining division
wrappers. -/
theorem round_round_div_aux0_from_format
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
        FloatSpec.Core.Raux.mag beta (x / y) + 1 →
      ¬ ((beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
          (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y) := by
  apply round_round_div_aux0_from_gap_cases (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) hβ hexp x y
    hx_pos hy_pos hx_fmt hy_fmt
  intro _htop _hband
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hxy_ne : x / y ≠ 0 := ne_of_gt hxy_pos
  have hdiv_lt :
      x / y < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := x / y) hβ hxy_ne
    simpa [wp, PostCond.noThrow, Id.run, pure,
      FloatSpec.Core.Raux.abs_val, abs_of_pos hxy_pos]
      using htrip True.intro
  exact round_round_div_aux0_gap_cases_from_format (beta := beta)
    (fexp1 := fexp1) (x := x) (y := y) hβ hy_pos
    hx_fmt hy_fmt hdiv_lt

/-- Coq `round_round_div_aux0`, factored at the two `Zle_or_lt` branches.

This refines `round_round_div_aux0_from_gap_cases`: instead of asking for a
single disjunction, it exposes the two branch inequalities generated by the
integer split in the Coq proof. -/
theorem round_round_div_aux0_from_exponent_split
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hfirst :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
          FloatSpec.Core.Raux.mag beta (x / y) + 1 →
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
            (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y →
        0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            FloatSpec.Core.Raux.mag beta (x / y) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        x ≤
          (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
            (beta : ℝ) ^
              (FloatSpec.Core.Raux.mag beta (x / y) +
                fexp1 (FloatSpec.Core.Raux.mag beta y)))
    (hsecond :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
          FloatSpec.Core.Raux.mag beta (x / y) + 1 →
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
            (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y →
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
            FloatSpec.Core.Raux.mag beta (x / y) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        x ≤
          (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
            (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x)) :
    fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
        FloatSpec.Core.Raux.mag beta (x / y) + 1 →
      ¬ ((beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
          (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y) := by
  apply round_round_div_aux0_from_gap_cases (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) hβ hexp x y
    hx_pos hy_pos hx_fmt hy_fmt
  intro htop hband
  exact round_round_div_aux0_gap_cases_from_exponent_split (beta := beta)
    (fexp1 := fexp1) (x := x) (y := y)
    (hfirst htop hband) (hsecond htop hband)

/-- Positive division wrapper for the main branch of Coq `round_round_div_aux`.

The hard arithmetic in upstream `round_round_div_aux0`/`aux1`/`aux2` is exactly
what discharges the remaining midpoint/top-binade alternatives. This lemma
factors the already-restored midpoint dispatcher for the case where the first
format exponent at `x / y` is not the top-binade exceptional case. -/
theorem round_round_div_pos_from_mid_case (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (_hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (_hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        FloatSpec.Core.Raux.mag beta (x / y))
    (hmid :
      |x / y - midp beta fexp1 (x / y)| ≤
          (1 / 2) * ulp beta fexp2 (x / y) →
        round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y)) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) - 1 :=
    hexp.1 (FloatSpec.Core.Raux.mag beta (x / y))
  exact round_round_mid_cases (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (x := x / y) hβ
    hxy_pos hf2 hf1 hmid

/-- Positive division wrapper from the midpoint-band exclusions.

This is the non-top-binade dispatcher used by Coq `round_round_div_aux`: the
lower and upper midpoint bands are precisely the branches discharged upstream by
`round_round_div_aux1` and `round_round_div_aux2`; the exact midpoint case is
kept as an explicit premise because it is handled upstream by the even-radix
midpoint theorem. -/
theorem round_round_div_pos_from_mid_exclusions (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        FloatSpec.Core.Raux.mag beta (x / y))
    (hlow :
      ¬ (midp beta fexp1 (x / y) -
            (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y ∧
          x / y < midp beta fexp1 (x / y)))
    (hmid_eq :
      x / y = midp beta fexp1 (x / y) →
        round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y))
    (hhigh :
      ¬ (midp beta fexp1 (x / y) < x / y ∧
          x / y ≤ midp beta fexp1 (x / y) +
            (1 / 2) * ulp beta fexp2 (x / y))) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  classical
  apply round_round_div_pos_from_mid_case (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (hβ := hβ)
    (hexp := hexp) (x := x) (y := y)
    (hx_pos := hx_pos) (hy_pos := hy_pos)
    hx_fmt hy_fmt (hf1 := hf1)
  intro hband
  rcases lt_trichotomy (x / y) (midp beta fexp1 (x / y)) with hlt | heq | hgt
  · exfalso
    apply hlow
    constructor
    · rw [abs_le] at hband
      linarith
    · exact hlt
  · exact hmid_eq heq
  · exfalso
    apply hhigh
    constructor
    · exact hgt
    · rw [abs_le] at hband
      linarith

/-- Midpoint branch reduced to second-format representability.

Coq's `round_round_eq_mid_beta_even` proves this representability from even
radix and midpoint arithmetic. This helper records the final, reusable step:
once the midpoint value is in the second format, the inner rounding is fixed,
so double rounding is immediate. -/
theorem round_round_eq_of_second_generic (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta)
    (hfmt2 : FloatSpec.Core.Generic_fmt.generic_format beta fexp2 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  have hinner :
      FloatSpec.Core.Generic_fmt.roundR beta fexp2
          (FloatSpec.Core.Generic_fmt.Znearest choice2) x = x :=
    FloatSpec.Core.Generic_fmt.roundR_generic
      (beta := beta) (fexp := fexp2)
      (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
      (x := x) hβ hfmt2
  simp [round_round_eq, hinner]

/-- Exact midpoint branch factored at second-format representability.

This is the branch used in Coq `round_round_div_aux` after
`round_round_eq_mid_beta_even` constructs the second-format representation of
the midpoint. -/
theorem round_round_mid_eq_from_second_generic (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (x : ℝ)
    (hβ : 1 < beta)
    (_hx_pos : 0 < x)
    (_hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 1)
    (_hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        FloatSpec.Core.Raux.mag beta x)
    (_hmid : x = midp beta fexp1 x)
    (hfmt2 : FloatSpec.Core.Generic_fmt.generic_format beta fexp2 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x :=
  round_round_eq_of_second_generic (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (x := x) hβ hfmt2

/-- Coq: `round_round_eq_mid_beta_even`.

At an exact midpoint of the first format, even radix makes that midpoint
representable in the second format under the division-stack exponent gap.
The double-rounding equality then follows because the inner rounding fixes the
midpoint value. -/
theorem round_round_eq_mid_beta_even (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (x : ℝ)
    (hx_pos : 0 < x)
    (hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta x) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 1)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        FloatSpec.Core.Raux.mag beta x)
    (hmid : x = midp beta fexp1 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  classical
  rcases heven with ⟨n, hbeta_even⟩
  let m : Int := FloatSpec.Core.Raux.mag beta x
  let e1 : Int := fexp1 m
  let e2 : Int := fexp2 m
  let rd : ℝ :=
    FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor x
  let sm1 : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 x
  let z1 : Int := FloatSpec.Core.Generic_fmt.rnd_floor sm1
  let k : Int := e1 - e2
  let d : Int := e1 - 1 - e2
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbneR : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hcexp1 : FloatSpec.Core.Generic_fmt.cexp beta fexp1 x = e1 := by
    simp [FloatSpec.Core.Generic_fmt.cexp, m, e1]
  have hcexp2 : FloatSpec.Core.Generic_fmt.cexp beta fexp2 x = e2 := by
    simp [FloatSpec.Core.Generic_fmt.cexp, m, e2]
  have hk_nonneg : 0 ≤ k := by
    dsimp [k, e1, e2, m] at *
    omega
  have hd_nonneg : 0 ≤ d := by
    dsimp [d, e1, e2, m] at *
    omega
  have hsm1_def : sm1 = x * (beta : ℝ) ^ (-e1) := by
    simp [sm1, FloatSpec.Core.Generic_fmt.scaled_mantissa, hcexp1]
  have hrd_eval : rd = (z1 : ℝ) * (beta : ℝ) ^ e1 := by
    simp [rd, z1, sm1, FloatSpec.Core.Generic_fmt.roundR, hcexp1]
  have hdn :
      FloatSpec.Core.Defs.Rnd_DN_pt
        (fun y => FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) x rd := by
    simpa [rd] using
      FloatSpec.Core.Generic_fmt.round_DN_pt
        (beta := beta) (fexp := fexp1) (x := x) hβ
  have hzero_fmt1 :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 0 :=
    FloatSpec.Core.Generic_fmt.generic_format_0_run
      (beta := beta) (fexp := fexp1)
  have hrd_nonneg : 0 ≤ rd :=
    hdn.2.2 0 hzero_fmt1 (le_of_lt hx_pos)
  have hrd_le_x : rd ≤ x := hdn.2.1
  have hmid_diff :
      x - rd = (1 / 2) * ulp beta fexp1 x := by
    simp [midp, rd] at hmid
    linarith
  have hulp1 : ulp beta fexp1 x = (beta : ℝ) ^ e1 := by
    have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := fexp1)
      (x := x) (hx := hx_ne)) True.intro
    simpa [wp, PostCond.noThrow, Id.run, pure, hcexp1] using h
  have hx_from_mid : x = rd + (1 / 2) * (beta : ℝ) ^ e1 := by
    simpa [midp, rd, hulp1] using hmid
  have hrd_part :
      (((FloatSpec.Core.Raux.Zfloor
          (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 rd) : Int) : ℝ) *
            (beta : ℝ) ^ e2) = rd := by
    by_cases hrd_zero : rd = 0
    · have hsm_zero :
          FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 rd = 0 := by
        simpa [hrd_zero, wp, PostCond.noThrow, Id.run, pure] using
          (FloatSpec.Core.Generic_fmt.scaled_mantissa_0 beta fexp2 True.intro)
      have hfloor_zero :
          FloatSpec.Core.Raux.Zfloor
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 rd) = 0 := by
        rw [hsm_zero]
        simp [FloatSpec.Core.Raux.Zfloor]
      rw [hfloor_zero, hrd_zero]
      simp
    · have hrd_pos : 0 < rd := lt_of_le_of_ne hrd_nonneg (Ne.symm hrd_zero)
      have hmag_rd_le : FloatSpec.Core.Raux.mag beta rd ≤ m := by
        have habs : |rd| ≤ |x| := by
          simpa [abs_of_nonneg hrd_nonneg, abs_of_pos hx_pos] using hrd_le_x
        have htrip := FloatSpec.Core.Raux.mag_le
          (beta := beta) (x := rd) (y := x) hβ hrd_zero habs
        simpa [wp, PostCond.noThrow, Id.run, pure, m] using htrip True.intro
      have hmag_x_le_rd : m ≤ FloatSpec.Core.Raux.mag beta rd := by
        have h := FloatSpec.Core.Generic_fmt.mag_roundR_ge
          (beta := beta) (fexp := fexp1)
          (rnd := FloatSpec.Core.Generic_fmt.rnd_floor) (x := x) hβ
        simpa [rd, m] using h hrd_zero
      have hmag_rd : FloatSpec.Core.Raux.mag beta rd = m :=
        le_antisymm hmag_rd_le hmag_x_le_rd
      have hcexp2_rd :
          FloatSpec.Core.Generic_fmt.cexp beta fexp2 rd = e2 := by
        simp [FloatSpec.Core.Generic_fmt.cexp, e2, m, hmag_rd]
      have hpow_k_nat :
          (beta : ℝ) ^ k = (beta : ℝ) ^ (Int.toNat k) := by
        simpa using
          FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat (beta : ℝ) k hk_nonneg
      have hpow_k_cast :
          (beta : ℝ) ^ (Int.toNat k) =
            ((beta ^ (Int.toNat k) : Int) : ℝ) := by
        rw [← Int.cast_pow]
      have hsm2_rd :
          FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 rd =
            ((z1 * beta ^ (Int.toNat k) : Int) : ℝ) := by
        calc
          FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 rd
              = rd * (beta : ℝ) ^ (-e2) := by
                  simp [FloatSpec.Core.Generic_fmt.scaled_mantissa, hcexp2_rd]
          _ = ((z1 : ℝ) * (beta : ℝ) ^ e1) * (beta : ℝ) ^ (-e2) := by
                  rw [hrd_eval]
          _ = (z1 : ℝ) * ((beta : ℝ) ^ e1 * (beta : ℝ) ^ (-e2)) := by ring
          _ = (z1 : ℝ) * (beta : ℝ) ^ (e1 - e2) := by
                  rw [← zpow_add₀ hbneR e1 (-e2)]
                  ring_nf
          _ = (z1 : ℝ) * (beta : ℝ) ^ k := by simp [k]
          _ = (z1 : ℝ) * (beta : ℝ) ^ (Int.toNat k) := by rw [hpow_k_nat]
          _ = ((z1 * beta ^ (Int.toNat k) : Int) : ℝ) := by
                  rw [Int.cast_mul, Int.cast_pow]
      have hfloor :
          FloatSpec.Core.Raux.Zfloor
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 rd) =
              z1 * beta ^ (Int.toNat k) := by
        rw [hsm2_rd]
        have hfloor_int :
            Int.floor (((z1 * beta ^ (Int.toNat k) : Int) : ℝ)) =
              z1 * beta ^ (Int.toNat k) :=
          Int.floor_intCast (R := ℝ) (z := z1 * beta ^ (Int.toNat k))
        simpa [FloatSpec.Core.Raux.Zfloor] using hfloor_int
      have hsplit : (beta : ℝ) ^ e1 =
          (beta : ℝ) ^ k * (beta : ℝ) ^ e2 := by
        have h := FloatSpec.Core.Generic_fmt.zpow_sub_add
          (a := (beta : ℝ)) (hbne := hbneR) (e := e1) (c := e2)
        simpa [k] using h.symm
      calc
        (((FloatSpec.Core.Raux.Zfloor
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 rd) : Int) : ℝ) *
              (beta : ℝ) ^ e2)
            = (((z1 * beta ^ (Int.toNat k) : Int) : ℝ) *
                (beta : ℝ) ^ e2) := by rw [hfloor]
        _ = ((z1 : ℝ) * (beta : ℝ) ^ (Int.toNat k)) *
              (beta : ℝ) ^ e2 := by rw [Int.cast_mul, Int.cast_pow]
        _ = ((z1 : ℝ) * (beta : ℝ) ^ k) * (beta : ℝ) ^ e2 := by
              rw [hpow_k_nat]
        _ = (z1 : ℝ) * (beta : ℝ) ^ e1 := by rw [hsplit]; ring
        _ = rd := hrd_eval.symm
  have hhalf_part :
      (((n * beta ^ (Int.toNat d) : Int) : ℝ) * (beta : ℝ) ^ e2) =
        (1 / 2) * (beta : ℝ) ^ e1 := by
    have hpow_d_nat :
        (beta : ℝ) ^ d = (beta : ℝ) ^ (Int.toNat d) := by
      simpa using
        FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat (beta : ℝ) d hd_nonneg
    have hpow_d_cast :
        (beta : ℝ) ^ (Int.toNat d) =
          ((beta ^ (Int.toNat d) : Int) : ℝ) := by
      rw [← Int.cast_pow]
    have hsplit : (beta : ℝ) ^ e1 =
        (beta : ℝ) ^ d * (beta : ℝ) ^ e2 * (beta : ℝ) := by
      have hde : d + e2 + 1 = e1 := by
        dsimp [d]
        omega
      calc
        (beta : ℝ) ^ e1 = (beta : ℝ) ^ (d + e2 + 1) := by rw [hde]
        _ = (beta : ℝ) ^ ((d + e2) + 1) := by ring_nf
        _ = (beta : ℝ) ^ (d + e2) * (beta : ℝ) ^ 1 := by
              simpa using (zpow_add₀ hbneR (d + e2) 1)
        _ = ((beta : ℝ) ^ d * (beta : ℝ) ^ e2) * (beta : ℝ) ^ 1 := by
              exact congrArg (fun t => t * (beta : ℝ) ^ 1)
                (zpow_add₀ hbneR d e2)
        _ = (beta : ℝ) ^ d * (beta : ℝ) ^ e2 * (beta : ℝ) := by
              simp [zpow_one]
    calc
      (((n * beta ^ (Int.toNat d) : Int) : ℝ) * (beta : ℝ) ^ e2)
          = ((n : ℝ) * (beta : ℝ) ^ (Int.toNat d)) *
              (beta : ℝ) ^ e2 := by rw [Int.cast_mul, Int.cast_pow]
      _ = ((n : ℝ) * (beta : ℝ) ^ d) * (beta : ℝ) ^ e2 := by
            rw [hpow_d_nat]
      _ = (1 / 2) * ((beta : ℝ) ^ d * (beta : ℝ) ^ e2 * (beta : ℝ)) := by
            have hbetaR : (beta : ℝ) = 2 * (n : ℝ) := by
              exact_mod_cast hbeta_even
            rw [hbetaR]
            ring
      _ = (1 / 2) * (beta : ℝ) ^ e1 := by rw [hsplit]
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Raux.Zfloor
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 rd) +
          n * beta ^ (Int.toNat d))
      e2
  have hf_val : FloatSpec.Core.Defs.F2R f = x := by
    calc
      FloatSpec.Core.Defs.F2R f
          = (((FloatSpec.Core.Raux.Zfloor
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 rd) +
                n * beta ^ (Int.toNat d) : Int) : ℝ) *
              (beta : ℝ) ^ e2) := by
                simp [f, FloatSpec.Core.Defs.F2R]
      _ = (((FloatSpec.Core.Raux.Zfloor
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 rd) : Int) : ℝ) *
              (beta : ℝ) ^ e2) +
            (((n * beta ^ (Int.toNat d) : Int) : ℝ) *
              (beta : ℝ) ^ e2) := by
                rw [Int.cast_add, add_mul]
      _ = rd + (1 / 2) * (beta : ℝ) ^ e1 := by
                rw [hrd_part, hhalf_part]
      _ = x := hx_from_mid.symm
  have hfmt2 :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp2 x := by
    have htrip := FloatSpec.Core.Generic_fmt.generic_format_F2R'
      (beta := beta) (fexp := fexp2) (x := x) (f := f)
    simpa [wp, PostCond.noThrow, Id.run, pure, f, hcexp2] using
      htrip ⟨hβ, hf_val, by intro _; exact le_rfl⟩
  exact round_round_mid_eq_from_second_generic (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (x := x) hβ
    hx_pos hf2 hf1 hmid hfmt2

/-- Positive division wrapper from all Coq `round_round_div_aux` branch premises.

This is the exact dispatcher shape after restoring Coq's
`round_round_all_mid_cases`: the really-zero branch is internal, the top-binade
branch is discharged by the `round_round_div_aux0` exclusion, and the ordinary
midpoint bands are discharged by the `round_round_div_aux1`/`aux2` exclusions
plus the exact-midpoint case. The arithmetic exclusions are still separate
premises here. -/
theorem round_round_div_pos_from_all_exclusions (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (_hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (_hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (htop :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
          FloatSpec.Core.Raux.mag beta (x / y) + 1 →
        ¬ ((beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta (x / y)) -
              (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y))
    (hlow :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        ¬ (midp beta fexp1 (x / y) -
              (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y ∧
            x / y < midp beta fexp1 (x / y)))
    (hmid_eq :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        x / y = midp beta fexp1 (x / y) →
          round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y))
    (hhigh :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        ¬ (midp beta fexp1 (x / y) < x / y ∧
            x / y ≤ midp beta fexp1 (x / y) +
              (1 / 2) * ulp beta fexp2 (x / y))) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  classical
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) - 1 :=
    hexp.1 (FloatSpec.Core.Raux.mag beta (x / y))
  exact round_round_all_mid_cases (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (x := x / y) hβ
    hxy_pos hf2
    (by
      intro hf1_top htop_band
      exact False.elim ((htop hf1_top) htop_band))
    (by
      intro hf1_le hband
      exact False.elim ((hlow hf1_le) hband))
    (by
      intro hf1_le hmid
      exact hmid_eq hf1_le hmid)
    (by
      intro hf1_le hband
      exact False.elim ((hhigh hf1_le) hband))

/-- Positive division wrapper after restoring Coq's even-radix midpoint branch.

This is the Coq `round_round_div_aux` dispatcher with the exact midpoint branch
closed by `round_round_eq_mid_beta_even`; only the three arithmetic exclusions
corresponding to upstream `round_round_div_aux0`, `round_round_div_aux1`, and
`round_round_div_aux2` remain as premises. -/
theorem round_round_div_pos_from_branch_exclusions_even
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (htop :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
          FloatSpec.Core.Raux.mag beta (x / y) + 1 →
        ¬ ((beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta (x / y)) -
              (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y))
    (hlow :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        ¬ (midp beta fexp1 (x / y) -
              (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y ∧
            x / y < midp beta fexp1 (x / y)))
    (hhigh :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        ¬ (midp beta fexp1 (x / y) < x / y ∧
            x / y ≤ midp beta fexp1 (x / y) +
              (1 / 2) * ulp beta fexp2 (x / y))) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hf2 :
      fexp2 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) - 1 :=
    hexp.1 (FloatSpec.Core.Raux.mag beta (x / y))
  exact round_round_div_pos_from_all_exclusions (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (hβ := hβ)
    (hexp := hexp) (x := x) (y := y)
    hx_pos hy_pos hx_fmt hy_fmt htop hlow
    (by
      intro hf1 hmid
      exact round_round_eq_mid_beta_even (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        hβ heven (x := x / y) hxy_pos hf2 hf1 hmid)
    hhigh

/-- Coq `round_round_div_aux1`, first wrapper step.

The upstream proof first cuts the lower midpoint band to an equivalent
floor-gap contradiction:
`1/2 * (ulp1 - ulp2) <= z - round_DN z < 1/2 * ulp1`. This helper records
that non-arithmetic normalization step. -/
theorem round_round_div_aux1_from_floor_gap
    (fexp1 fexp2 : Int → Int)
    (z : ℝ)
    (hgap :
      ¬ ((1 / 2) * (ulp beta fexp1 z - ulp beta fexp2 z) ≤
            z -
              FloatSpec.Core.Generic_fmt.roundR beta fexp1
                FloatSpec.Core.Generic_fmt.rnd_floor z ∧
          z -
              FloatSpec.Core.Generic_fmt.roundR beta fexp1
                FloatSpec.Core.Generic_fmt.rnd_floor z <
            (1 / 2) * ulp beta fexp1 z)) :
    ¬ (midp beta fexp1 z -
          (1 / 2) * ulp beta fexp2 z ≤ z ∧
        z < midp beta fexp1 z) := by
  intro hband
  apply hgap
  constructor
  · unfold midp at hband
    linarith
  · unfold midp at hband
    linarith

/-- Contradiction form for the normalized floor-gap interval in Coq
`round_round_div_aux1`.

After the first `cut`, aux1 proves the strict upper bound
`z - round_DN z < 1/2 * (ulp1 - ulp2)`, contradicting the lower endpoint of
the normalized interval. -/
theorem round_round_div_aux1_floor_gap_contra_from_upper
    (fexp1 fexp2 : Int → Int)
    (z : ℝ)
    (hupper :
      z -
          FloatSpec.Core.Generic_fmt.roundR beta fexp1
            FloatSpec.Core.Generic_fmt.rnd_floor z <
        (1 / 2) * (ulp beta fexp1 z - ulp beta fexp2 z)) :
    ¬ ((1 / 2) * (ulp beta fexp1 z - ulp beta fexp2 z) ≤
          z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z ∧
        z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z <
          (1 / 2) * ulp beta fexp1 z) := by
  intro hgap
  exact (not_lt_of_ge hgap.1) hupper

/-- Real arithmetic core of Coq `round_round_div_aux1`.

After multiplying the target inequality by `y` and then by `2`, both aux1
branches reduce to a scaled branch bound together with the full-ulp gap
comparison `u2 * y < gap`. -/
theorem round_round_div_aux1_floor_gap_upper_from_scaled_bound
    (x y xdn u1 u2 gap : ℝ)
    (hy_pos : 0 < y)
    (hscaled : 2 * x ≤ 2 * xdn * y + u1 * y - gap)
    (hgap : u2 * y < gap) :
    x / y - xdn < (1 / 2) * (u1 - u2) := by
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hstrict :
      2 * x < (2 * xdn + (u1 - u2)) * y := by
    nlinarith
  have htarget_mul :
      (x / y - xdn) * y < ((1 / 2) * (u1 - u2)) * y := by
    have hcancel : (x / y) * y = x := by
      field_simp [hy_ne]
    nlinarith
  exact lt_of_mul_lt_mul_right htarget_mul (le_of_lt hy_pos)

/-- Coq `round_round_div_aux1` real core with the actual floor and ulp terms.

The integer branch proofs establish the scaled inequality for `x`; the full-ulp
gap comparison then gives the strict normalized floor-gap upper bound. -/
theorem round_round_div_aux1_floor_gap_upper_from_scaled_branch
    (fexp1 fexp2 : Int → Int)
    (x y gap : ℝ)
    (hy_pos : 0 < y)
    (hscaled :
      2 * x ≤
        2 *
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) * y +
          ulp beta fexp1 (x / y) * y - gap)
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    x / y -
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
          FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
      (1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)) := by
  exact round_round_div_aux1_floor_gap_upper_from_scaled_bound
    (x := x) (y := y)
    (xdn := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (x / y))
    (u1 := ulp beta fexp1 (x / y))
    (u2 := ulp beta fexp2 (x / y))
    (gap := gap) hy_pos hscaled hgap

/-- Integer-grid strengthening used in Coq `round_round_div_aux1`.

After multiplying the upper floor-gap inequality by `y` and by `2`, the proof
has a strict inequality between two quantities that are both integer multiples
of the branch gap. This turns the strict inequality into a one-gap margin. -/
theorem round_round_div_aux1_scaled_upper_from_grid
    (x y xdn u1 gap : ℝ) (A B : Int)
    (hy_pos : 0 < y)
    (hgap_pos : 0 < gap)
    (hleft_grid : 2 * x = (A : ℝ) * gap)
    (hright_grid : 2 * xdn * y + u1 * y = (B : ℝ) * gap)
    (hupper : x / y - xdn < (1 / 2) * u1) :
    2 * x ≤ 2 * xdn * y + u1 * y - gap := by
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hstrict :
      2 * x < 2 * xdn * y + u1 * y := by
    have hmul := mul_lt_mul_of_pos_right hupper hy_pos
    have hcancel : (x / y) * y = x := by
      field_simp [hy_ne]
    nlinarith
  have hAB_real : (A : ℝ) < (B : ℝ) := by
    have hscaled : (A : ℝ) * gap < (B : ℝ) * gap := by
      simpa [hleft_grid, hright_grid] using hstrict
    exact lt_of_mul_lt_mul_right hscaled (le_of_lt hgap_pos)
  have hAB : A < B := by
    exact_mod_cast hAB_real
  have hA_le : A ≤ B - 1 := by
    omega
  have hreal_le : (A : ℝ) ≤ (B - 1 : Int) := by
    exact_mod_cast hA_le
  calc
    2 * x = (A : ℝ) * gap := hleft_grid
    _ ≤ ((B - 1 : Int) : ℝ) * gap :=
        mul_le_mul_of_nonneg_right hreal_le (le_of_lt hgap_pos)
    _ = (B : ℝ) * gap - gap := by
        rw [Int.cast_sub]
        ring
    _ = 2 * xdn * y + u1 * y - gap := by
        rw [← hright_grid]

/-- Integer-grid strengthening used in Coq `round_round_div_aux2`.

This is the lower-gap analogue of
`round_round_div_aux1_scaled_upper_from_grid`. -/
theorem round_round_div_aux2_scaled_lower_from_grid
    (x y xdn u1 gap : ℝ) (A B : Int)
    (hy_pos : 0 < y)
    (hgap_pos : 0 < gap)
    (hleft_grid : 2 * xdn * y + u1 * y = (A : ℝ) * gap)
    (hright_grid : 2 * x = (B : ℝ) * gap)
    (hlower : (1 / 2) * u1 < x / y - xdn) :
    2 * xdn * y + u1 * y + gap ≤ 2 * x := by
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hstrict :
      2 * xdn * y + u1 * y < 2 * x := by
    have hmul := mul_lt_mul_of_pos_right hlower hy_pos
    have hcancel : (x / y) * y = x := by
      field_simp [hy_ne]
    nlinarith
  have hAB_real : (A : ℝ) < (B : ℝ) := by
    have hscaled : (A : ℝ) * gap < (B : ℝ) * gap := by
      simpa [hleft_grid, hright_grid] using hstrict
    exact lt_of_mul_lt_mul_right hscaled (le_of_lt hgap_pos)
  have hAB : A < B := by
    exact_mod_cast hAB_real
  have hA_le : A + 1 ≤ B := by
    omega
  have hreal_le : ((A + 1 : Int) : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hA_le
  calc
    2 * xdn * y + u1 * y + gap
        = (A : ℝ) * gap + gap := by rw [← hleft_grid]
    _ = ((A + 1 : Int) : ℝ) * gap := by
        rw [Int.cast_add]
        norm_num
        ring
    _ ≤ (B : ℝ) * gap :=
        mul_le_mul_of_nonneg_right hreal_le (le_of_lt hgap_pos)
    _ = 2 * x := by
        rw [← hright_grid]

/-- Right-hand integer grid identity for Coq `round_round_div_aux1`/`aux2`.

Once the divisor, floor-rounded quotient, and first-format ulp have been
expanded as powers of `beta`, the branch endpoint
`2 * round_DN z * y + ulp1 * y` is an integer multiple of the branch gap. -/
theorem round_round_div_floor_right_grid_from_repr
    (y xdn u1 gap : ℝ) (my k fz fy : Int)
    (hβ : 1 < beta)
    (hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy)
    (hxdn_repr : xdn = (k : ℝ) * (beta : ℝ) ^ fz)
    (hu1 : u1 = (beta : ℝ) ^ fz)
    (hgap : gap = (beta : ℝ) ^ (fz + fy)) :
    2 * xdn * y + u1 * y = ((2 * k * my + my : Int) : ℝ) * gap := by
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  rw [hy_repr, hxdn_repr, hu1, hgap]
  have hpow :
      (beta : ℝ) ^ fz * (beta : ℝ) ^ fy =
        (beta : ℝ) ^ (fz + fy) := by
    exact (zpow_add₀ hbne fz fy).symm
  rw [← hpow]
  rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
  ring

/-- Right-hand grid identity with the `roundR` and `ulp` representations
extracted directly.

This removes the explicit floor-rounded quotient and ulp representation
premises from the common endpoint used by Coq `round_round_div_aux1`/`aux2`. -/
theorem round_round_div_floor_right_grid
    (fexp : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
    (z y gap : ℝ) (my fy : Int)
    (hβ : 1 < beta)
    (hz_ne : z ≠ 0)
    (hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy)
    (hgap :
      gap =
        (beta : ℝ) ^
          (FloatSpec.Core.Generic_fmt.cexp beta fexp z + fy)) :
    2 *
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor z * y +
        ulp beta fexp z * y =
      ((2 *
              FloatSpec.Core.Generic_fmt.rnd_floor
                (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp z) *
            my + my : Int) : ℝ) * gap := by
  let k : Int :=
    FloatSpec.Core.Generic_fmt.rnd_floor
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp z)
  let fz : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp z
  have hxdn_repr :
      FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_floor z =
        (k : ℝ) * (beta : ℝ) ^ fz := by
    simp [k, fz, FloatSpec.Core.Generic_fmt.roundR]
  have hu1 : ulp beta fexp z = (beta : ℝ) ^ fz := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp) (x := z) hz_ne
    simpa [wp, PostCond.noThrow, Id.run, pure, fz] using htrip True.intro
  have hgrid :=
    round_round_div_floor_right_grid_from_repr (beta := beta)
      (y := y)
      (xdn := FloatSpec.Core.Generic_fmt.roundR beta fexp
        FloatSpec.Core.Generic_fmt.rnd_floor z)
      (u1 := ulp beta fexp z) (gap := gap)
      (my := my) (k := k) (fz := fz) (fy := fy)
      hβ hy_repr hxdn_repr hu1 hgap
  simpa [k, fz] using hgrid

/-- Right-hand grid identity with the denominator representation extracted from
`generic_format`.

This removes the explicit `y = my * beta^fy` premise from the common endpoint
used by Coq `round_round_div_aux1`/`aux2`. -/
theorem round_round_div_floor_right_grid_from_generic
    (fexp fexpY : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
    (z y gap : ℝ)
    (hβ : 1 < beta)
    (hz_ne : z ≠ 0)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexpY y)
    (hgap :
      gap =
        (beta : ℝ) ^
          (FloatSpec.Core.Generic_fmt.cexp beta fexp z +
            FloatSpec.Core.Generic_fmt.cexp beta fexpY y)) :
    2 *
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor z * y +
        ulp beta fexp z * y =
      ((2 *
              FloatSpec.Core.Generic_fmt.rnd_floor
                (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp z) *
              FloatSpec.Core.Raux.Ztrunc
                (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y) +
            FloatSpec.Core.Raux.Ztrunc
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y) :
          Int) : ℝ) * gap := by
  have hy_repr :
      y =
        (FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y) : ℝ) *
          (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexpY y := by
    simpa [FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Defs.F2R] using hy_fmt
  exact round_round_div_floor_right_grid (beta := beta)
    (fexp := fexp) (z := z) (y := y) (gap := gap)
    (my := FloatSpec.Core.Raux.Ztrunc
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y))
    (fy := FloatSpec.Core.Generic_fmt.cexp beta fexpY y)
    hβ hz_ne hy_repr hgap

/-- Right-hand integer grid identity when the branch gap is below the
denominator/floor endpoint exponent.

This is the second-branch analogue of
`round_round_div_floor_right_grid_from_repr`: if
`fz + fy = d + gapExp`, the endpoint is still an integer multiple of
`beta^gapExp`, with the extra factor absorbed into the integer coefficient. -/
theorem round_round_div_floor_right_grid_from_repr_offset
    (y xdn u1 gap : ℝ) (my k fz fy gapExp : Int) (d : Nat)
    (hβ : 1 < beta)
    (hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy)
    (hxdn_repr : xdn = (k : ℝ) * (beta : ℝ) ^ fz)
    (hu1 : u1 = (beta : ℝ) ^ fz)
    (hgap : gap = (beta : ℝ) ^ gapExp)
    (hoff : fz + fy = (d : Int) + gapExp) :
    2 * xdn * y + u1 * y =
      (((2 * k * my + my) * beta ^ d : Int) : ℝ) * gap := by
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hexact :=
    round_round_div_floor_right_grid_from_repr (beta := beta)
      (y := y) (xdn := xdn) (u1 := u1)
      (gap := (beta : ℝ) ^ (fz + fy))
      (my := my) (k := k) (fz := fz) (fy := fy)
      hβ hy_repr hxdn_repr hu1 rfl
  calc
    2 * xdn * y + u1 * y =
        ((2 * k * my + my : Int) : ℝ) * (beta : ℝ) ^ (fz + fy) := by
          simpa using hexact
    _ = ((2 * k * my + my : Int) : ℝ) *
          ((beta : ℝ) ^ (d : Int) * (beta : ℝ) ^ gapExp) := by
          rw [hoff, zpow_add₀ hbne]
    _ = (((2 * k * my + my) * beta ^ d : Int) : ℝ) * gap := by
          have hdnat : (beta : ℝ) ^ (d : Int) = (beta : ℝ) ^ d :=
            zpow_ofNat (beta : ℝ) d
          rw [hgap, Int.cast_mul, Int.cast_pow]
          rw [hdnat]
          ring_nf

/-- Right-hand grid identity with the denominator representation extracted from
`generic_format`, for the branch where the endpoint exponent has a nonnegative
offset over the chosen gap exponent. -/
theorem round_round_div_floor_right_grid_from_generic_offset
    (fexp fexpY : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
    (z y gap : ℝ) (gapExp : Int) (d : Nat)
    (hβ : 1 < beta)
    (hz_ne : z ≠ 0)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexpY y)
    (hgap : gap = (beta : ℝ) ^ gapExp)
    (hoff :
      FloatSpec.Core.Generic_fmt.cexp beta fexp z +
          FloatSpec.Core.Generic_fmt.cexp beta fexpY y =
        (d : Int) + gapExp) :
    2 *
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor z * y +
        ulp beta fexp z * y =
      (((2 *
              FloatSpec.Core.Generic_fmt.rnd_floor
                (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp z) *
              FloatSpec.Core.Raux.Ztrunc
                (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y) +
            FloatSpec.Core.Raux.Ztrunc
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y)) *
            beta ^ d : Int) : ℝ) * gap := by
  let k : Int :=
    FloatSpec.Core.Generic_fmt.rnd_floor
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp z)
  let my : Int :=
    FloatSpec.Core.Raux.Ztrunc
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y)
  let fz : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp z
  let fy : Int := FloatSpec.Core.Generic_fmt.cexp beta fexpY y
  have hy_repr :
      y = (my : ℝ) * (beta : ℝ) ^ fy := by
    simpa [my, fy, FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Defs.F2R] using hy_fmt
  have hxdn_repr :
      FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_floor z =
        (k : ℝ) * (beta : ℝ) ^ fz := by
    simp [k, fz, FloatSpec.Core.Generic_fmt.roundR]
  have hu1 : ulp beta fexp z = (beta : ℝ) ^ fz := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp) (x := z) hz_ne
    simpa [wp, PostCond.noThrow, Id.run, pure, fz] using htrip True.intro
  have hoff' : fz + fy = (d : Int) + gapExp := by
    simpa [fz, fy] using hoff
  have hgrid :=
    round_round_div_floor_right_grid_from_repr_offset (beta := beta)
      (y := y)
      (xdn := FloatSpec.Core.Generic_fmt.roundR beta fexp
        FloatSpec.Core.Generic_fmt.rnd_floor z)
      (u1 := ulp beta fexp z) (gap := gap)
      (my := my) (k := k) (fz := fz) (fy := fy)
      (gapExp := gapExp) (d := d)
      hβ hy_repr hxdn_repr hu1 hgap hoff'
  simpa [k, my, fz, fy] using hgrid

/-- Left-hand integer grid identity for Coq `round_round_div_aux1`/`aux2`.

When the numerator exponent is a nonnegative offset above the branch gap
exponent, `2 * x` is an integer multiple of the same gap. -/
theorem round_round_div_numerator_left_grid_from_repr
    (x gap : ℝ) (mx : Int) (fx gapExp : Int) (d : Nat)
    (hβ : 1 < beta)
    (hx_repr : x = (mx : ℝ) * (beta : ℝ) ^ fx)
    (hgap : gap = (beta : ℝ) ^ gapExp)
    (hfx : fx = (d : Int) + gapExp) :
    2 * x = ((2 * mx * beta ^ d : Int) : ℝ) * gap := by
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  rw [hx_repr, hgap, hfx]
  have hpow :
      (beta : ℝ) ^ ((d : Int) + gapExp) =
        (beta : ℝ) ^ (d : Int) * (beta : ℝ) ^ gapExp := by
    exact zpow_add₀ hbne (d : Int) gapExp
  rw [hpow]
  rw [Int.cast_mul, Int.cast_mul, Int.cast_pow]
  norm_num
  ring

/-- Left-hand grid identity with the numerator representation extracted from
`generic_format`.

This removes the explicit `x = mx * beta^fx` premise from the numerator side of
Coq `round_round_div_aux1`/`aux2`; the mantissa is the truncation of the scaled
mantissa at the canonical exponent. -/
theorem round_round_div_numerator_left_grid_from_generic
    (fexp : Int → Int)
    (x gap : ℝ) (gapExp : Int) (d : Nat)
    (hβ : 1 < beta)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp x)
    (hgap : gap = (beta : ℝ) ^ gapExp)
    (hcexp : FloatSpec.Core.Generic_fmt.cexp beta fexp x = (d : Int) + gapExp) :
    2 * x =
      ((2 *
            FloatSpec.Core.Raux.Ztrunc
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x) *
            beta ^ d : Int) : ℝ) * gap := by
  have hx_repr :
      x =
        (FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x) : ℝ) *
          (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp x := by
    simpa [FloatSpec.Core.Generic_fmt.generic_format,
      FloatSpec.Core.Defs.F2R] using hx_fmt
  exact round_round_div_numerator_left_grid_from_repr (beta := beta)
    (x := x) (gap := gap)
    (mx := FloatSpec.Core.Raux.Ztrunc
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x))
    (fx := FloatSpec.Core.Generic_fmt.cexp beta fexp x)
    (gapExp := gapExp) (d := d) hβ hx_repr hgap hcexp

/-- Coq `round_round_div_aux1` branch contradiction after the grid step.

This combines the normalized floor-gap interval, the integer-lattice
strengthening, and the full second-format ulp/gap comparison. -/
theorem round_round_div_aux1_floor_gap_contra_from_grid
    (fexp1 fexp2 : Int → Int)
    (x y gap : ℝ) (A B : Int)
    (hy_pos : 0 < y)
    (hgap_pos : 0 < gap)
    (hleft_grid : 2 * x = (A : ℝ) * gap)
    (hright_grid :
      2 *
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) * y +
          ulp beta fexp1 (x / y) * y =
        (B : ℝ) * gap)
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    ¬ ((1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)) ≤
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ∧
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
          (1 / 2) * ulp beta fexp1 (x / y)) := by
  intro hnorm
  have hscaled :=
    round_round_div_aux1_scaled_upper_from_grid
      (x := x) (y := y)
      (xdn := FloatSpec.Core.Generic_fmt.roundR beta fexp1
        FloatSpec.Core.Generic_fmt.rnd_floor (x / y))
      (u1 := ulp beta fexp1 (x / y))
      (gap := gap) (A := A) (B := B)
      hy_pos hgap_pos hleft_grid hright_grid hnorm.2
  have hupper :=
    round_round_div_aux1_floor_gap_upper_from_scaled_branch (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
      (gap := gap) hy_pos hscaled hgap
  exact (not_lt_of_ge hnorm.1) hupper

/-- First non-top branch of Coq `round_round_div_aux1` after the mantissa
scaled inequality has been established. -/
theorem round_round_div_aux1_first_low_from_scaled
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        FloatSpec.Core.Raux.mag beta (x / y))
    (hdisj :
      FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
        FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1)
    (hscaled :
      2 * x ≤
        2 *
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) * y +
          ulp beta fexp1 (x / y) * y -
            (beta : ℝ) ^
              (fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) +
                fexp1 (FloatSpec.Core.Raux.mag beta y))) :
    x / y -
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
          FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
      (1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)) := by
  have hgap :=
    round_round_div_ulp_lt_first_gap_low (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (hβ := hβ) (hexp := hexp)
      (x := x) (y := y) hx_pos hy_pos hfx hfy hf1 hdisj
  exact round_round_div_aux1_floor_gap_upper_from_scaled_branch (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := (beta : ℝ) ^
      (fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) +
        fexp1 (FloatSpec.Core.Raux.mag beta y)))
    hy_pos hscaled hgap

/-- Second non-top branch of Coq `round_round_div_aux1` after the mantissa
scaled inequality has been established. -/
theorem round_round_div_aux1_second_low_from_scaled
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        FloatSpec.Core.Raux.mag beta (x / y))
    (hdisj :
      FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
        FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1)
    (hscaled :
      2 * x ≤
        2 *
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) * y +
          ulp beta fexp1 (x / y) * y -
            (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x)) :
    x / y -
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
          FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
      (1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)) := by
  have hgap :=
    round_round_div_ulp_lt_second_gap_low (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (hβ := hβ) (hexp := hexp)
      (x := x) (y := y) hx_pos hy_pos hfx hfy hf1 hdisj
  exact round_round_div_aux1_floor_gap_upper_from_scaled_branch (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x))
    hy_pos hscaled hgap

/-- Coq `round_round_div_aux1` exponent split after the first `cut`.

The remaining arithmetic in aux1 is split on
`fexp1 (mag x) - fexp1 (mag z) - fexp1 (mag y)`, where `z = x / y` in the
division proof. Each branch only needs to establish the same strict upper
bound on the floor gap. -/
theorem round_round_div_aux1_floor_gap_from_exponent_split
    (fexp1 fexp2 : Int → Int)
    (x y z : ℝ)
    (hfirst :
      0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            fexp1 (FloatSpec.Core.Raux.mag beta z) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z <
          (1 / 2) * (ulp beta fexp1 z - ulp beta fexp2 z))
    (hsecond :
      fexp1 (FloatSpec.Core.Raux.mag beta x) -
          fexp1 (FloatSpec.Core.Raux.mag beta z) -
          fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z <
          (1 / 2) * (ulp beta fexp1 z - ulp beta fexp2 z)) :
    ¬ ((1 / 2) * (ulp beta fexp1 z - ulp beta fexp2 z) ≤
          z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z ∧
        z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z <
          (1 / 2) * ulp beta fexp1 z) := by
  by_cases hsplit :
      0 ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
          fexp1 (FloatSpec.Core.Raux.mag beta z) -
          fexp1 (FloatSpec.Core.Raux.mag beta y)
  · exact round_round_div_aux1_floor_gap_contra_from_upper (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (z := z) (hfirst hsplit)
  · exact round_round_div_aux1_floor_gap_contra_from_upper (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (z := z)
      (hsecond (lt_of_not_ge hsplit))

/-- Coq `round_round_div_aux1` reduced to its two exponent-split arithmetic
branches. -/
theorem round_round_div_aux1_from_exponent_split
    (fexp1 fexp2 : Int → Int)
    (x y z : ℝ)
    (hfirst :
      0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            fexp1 (FloatSpec.Core.Raux.mag beta z) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z <
          (1 / 2) * (ulp beta fexp1 z - ulp beta fexp2 z))
    (hsecond :
      fexp1 (FloatSpec.Core.Raux.mag beta x) -
          fexp1 (FloatSpec.Core.Raux.mag beta z) -
          fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z <
          (1 / 2) * (ulp beta fexp1 z - ulp beta fexp2 z)) :
    ¬ (midp beta fexp1 z -
          (1 / 2) * ulp beta fexp2 z ≤ z ∧
        z < midp beta fexp1 z) := by
  exact round_round_div_aux1_from_floor_gap (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (z := z)
    (round_round_div_aux1_floor_gap_from_exponent_split (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y) (z := z)
      hfirst hsecond)

/-- Coq `round_round_div_aux2`, first wrapper step.

The upstream proof cuts the upper midpoint band to the floor-gap interval
`1/2 * ulp1 < z - round_DN z <= 1/2 * (ulp1 + ulp2)`. -/
theorem round_round_div_aux2_from_floor_gap
    (fexp1 fexp2 : Int → Int)
    (z : ℝ)
    (hgap :
      ¬ ((1 / 2) * ulp beta fexp1 z <
            z -
              FloatSpec.Core.Generic_fmt.roundR beta fexp1
                FloatSpec.Core.Generic_fmt.rnd_floor z ∧
          z -
              FloatSpec.Core.Generic_fmt.roundR beta fexp1
                FloatSpec.Core.Generic_fmt.rnd_floor z ≤
            (1 / 2) * (ulp beta fexp1 z + ulp beta fexp2 z))) :
    ¬ (midp beta fexp1 z < z ∧
        z ≤ midp beta fexp1 z +
          (1 / 2) * ulp beta fexp2 z) := by
  intro hband
  apply hgap
  constructor
  · unfold midp at hband
    linarith
  · unfold midp at hband
    linarith

/-- Contradiction form for the normalized floor-gap interval in Coq
`round_round_div_aux2`.

After the first `cut`, aux2 proves
`1/2 * (ulp1 + ulp2) < z - round_DN z`, contradicting the upper endpoint of
the normalized interval. -/
theorem round_round_div_aux2_floor_gap_contra_from_lower
    (fexp1 fexp2 : Int → Int)
    (z : ℝ)
    (hlower :
      (1 / 2) * (ulp beta fexp1 z + ulp beta fexp2 z) <
        z -
          FloatSpec.Core.Generic_fmt.roundR beta fexp1
            FloatSpec.Core.Generic_fmt.rnd_floor z) :
    ¬ ((1 / 2) * ulp beta fexp1 z <
          z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z ∧
        z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z ≤
          (1 / 2) * (ulp beta fexp1 z + ulp beta fexp2 z)) := by
  intro hgap
  exact (not_lt_of_ge hgap.2) hlower

/-- Real arithmetic core of Coq `round_round_div_aux2`.

After multiplying the target inequality by `y` and then by `2`, both aux2
branches reduce to a scaled lower bound together with the full-ulp gap
comparison `u2 * y < gap`. -/
theorem round_round_div_aux2_floor_gap_lower_from_scaled_bound
    (x y xdn u1 u2 gap : ℝ)
    (hy_pos : 0 < y)
    (hgap : u2 * y < gap)
    (hscaled : 2 * xdn * y + u1 * y + gap ≤ 2 * x) :
    (1 / 2) * (u1 + u2) < x / y - xdn := by
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have htarget_mul :
      ((1 / 2) * (u1 + u2)) * y < (x / y - xdn) * y := by
    have hcancel : (x / y) * y = x := by
      field_simp [hy_ne]
    nlinarith
  exact lt_of_mul_lt_mul_right htarget_mul (le_of_lt hy_pos)

/-- Coq `round_round_div_aux2` real core with the actual floor and ulp terms. -/
theorem round_round_div_aux2_floor_gap_lower_from_scaled_branch
    (fexp1 fexp2 : Int → Int)
    (x y gap : ℝ)
    (hy_pos : 0 < y)
    (hgap : ulp beta fexp2 (x / y) * y < gap)
    (hscaled :
      2 *
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) * y +
          ulp beta fexp1 (x / y) * y + gap ≤
        2 * x) :
    (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y)) <
      x / y -
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
          FloatSpec.Core.Generic_fmt.rnd_floor (x / y) := by
  exact round_round_div_aux2_floor_gap_lower_from_scaled_bound
    (x := x) (y := y)
    (xdn := FloatSpec.Core.Generic_fmt.roundR beta fexp1
      FloatSpec.Core.Generic_fmt.rnd_floor (x / y))
    (u1 := ulp beta fexp1 (x / y))
    (u2 := ulp beta fexp2 (x / y))
    (gap := gap) hy_pos hgap hscaled

/-- Coq `round_round_div_aux2` branch contradiction after the grid step.

This is the upper-midpoint analogue of
`round_round_div_aux1_floor_gap_contra_from_grid`. -/
theorem round_round_div_aux2_floor_gap_contra_from_grid
    (fexp1 fexp2 : Int → Int)
    (x y gap : ℝ) (A B : Int)
    (hy_pos : 0 < y)
    (hgap_pos : 0 < gap)
    (hleft_grid :
      2 *
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) * y +
          ulp beta fexp1 (x / y) * y =
        (A : ℝ) * gap)
    (hright_grid : 2 * x = (B : ℝ) * gap)
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    ¬ ((1 / 2) * ulp beta fexp1 (x / y) <
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ∧
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ≤
          (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y))) := by
  intro hnorm
  have hscaled :=
    round_round_div_aux2_scaled_lower_from_grid
      (x := x) (y := y)
      (xdn := FloatSpec.Core.Generic_fmt.roundR beta fexp1
        FloatSpec.Core.Generic_fmt.rnd_floor (x / y))
      (u1 := ulp beta fexp1 (x / y))
      (gap := gap) (A := A) (B := B)
      hy_pos hgap_pos hleft_grid hright_grid hnorm.1
  have hlower :=
    round_round_div_aux2_floor_gap_lower_from_scaled_branch (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
      (gap := gap) hy_pos hgap hscaled
  exact (not_lt_of_ge hnorm.2) hlower

/-- Coq `round_round_div_aux1` branch contradiction from formatted
representations.

This packages the two integer-grid representation identities into the aux1
floor-gap contradiction, leaving only the extraction of those representations
from `generic_format` and `roundR` for the branch proof. -/
theorem round_round_div_aux1_floor_gap_contra_from_repr
    (fexp1 fexp2 : Int → Int)
    (x y gap : ℝ) (mx my k fx fz fy : Int) (d : Nat)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hgap_pos : 0 < gap)
    (hx_repr : x = (mx : ℝ) * (beta : ℝ) ^ fx)
    (hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy)
    (hxdn_repr :
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
        FloatSpec.Core.Generic_fmt.rnd_floor (x / y) =
        (k : ℝ) * (beta : ℝ) ^ fz)
    (hu1 : ulp beta fexp1 (x / y) = (beta : ℝ) ^ fz)
    (hgap_repr : gap = (beta : ℝ) ^ (fz + fy))
    (hfx : fx = (d : Int) + (fz + fy))
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    ¬ ((1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)) ≤
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ∧
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
          (1 / 2) * ulp beta fexp1 (x / y)) := by
  have hleft :=
    round_round_div_numerator_left_grid_from_repr (beta := beta)
      (x := x) (gap := gap) (mx := mx) (fx := fx)
      (gapExp := fz + fy) (d := d) hβ hx_repr hgap_repr hfx
  have hright :=
    round_round_div_floor_right_grid_from_repr (beta := beta)
      (y := y)
      (xdn := FloatSpec.Core.Generic_fmt.roundR beta fexp1
        FloatSpec.Core.Generic_fmt.rnd_floor (x / y))
      (u1 := ulp beta fexp1 (x / y))
      (gap := gap) (my := my) (k := k) (fz := fz) (fy := fy)
      hβ hy_repr hxdn_repr hu1 hgap_repr
  exact round_round_div_aux1_floor_gap_contra_from_grid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := gap) (A := 2 * mx * beta ^ d) (B := 2 * k * my + my)
    hy_pos hgap_pos hleft hright hgap

/-- Coq `round_round_div_aux2` branch contradiction from formatted
representations.

This is the upper-midpoint analogue of
`round_round_div_aux1_floor_gap_contra_from_repr`. -/
theorem round_round_div_aux2_floor_gap_contra_from_repr
    (fexp1 fexp2 : Int → Int)
    (x y gap : ℝ) (mx my k fx fz fy : Int) (d : Nat)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hgap_pos : 0 < gap)
    (hx_repr : x = (mx : ℝ) * (beta : ℝ) ^ fx)
    (hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy)
    (hxdn_repr :
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
        FloatSpec.Core.Generic_fmt.rnd_floor (x / y) =
        (k : ℝ) * (beta : ℝ) ^ fz)
    (hu1 : ulp beta fexp1 (x / y) = (beta : ℝ) ^ fz)
    (hgap_repr : gap = (beta : ℝ) ^ (fz + fy))
    (hfx : fx = (d : Int) + (fz + fy))
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    ¬ ((1 / 2) * ulp beta fexp1 (x / y) <
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ∧
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ≤
          (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y))) := by
  have hright :=
    round_round_div_numerator_left_grid_from_repr (beta := beta)
      (x := x) (gap := gap) (mx := mx) (fx := fx)
      (gapExp := fz + fy) (d := d) hβ hx_repr hgap_repr hfx
  have hleft :=
    round_round_div_floor_right_grid_from_repr (beta := beta)
      (y := y)
      (xdn := FloatSpec.Core.Generic_fmt.roundR beta fexp1
        FloatSpec.Core.Generic_fmt.rnd_floor (x / y))
      (u1 := ulp beta fexp1 (x / y))
      (gap := gap) (my := my) (k := k) (fz := fz) (fy := fy)
      hβ hy_repr hxdn_repr hu1 hgap_repr
  exact round_round_div_aux2_floor_gap_contra_from_grid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := gap) (A := 2 * k * my + my) (B := 2 * mx * beta ^ d)
    hy_pos hgap_pos hleft hright hgap

/-- Coq `round_round_div_aux1` branch contradiction with the right endpoint
extracted from `roundR` and `ulp`.

This keeps only the numerator, divisor, and branch-gap representations explicit;
the floor-rounded quotient and first ulp power are derived internally. -/
theorem round_round_div_aux1_floor_gap_contra_from_direct_right_grid
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (x y gap : ℝ) (mx my fx fy : Int) (d : Nat)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hz_ne : x / y ≠ 0)
    (hgap_pos : 0 < gap)
    (hx_repr : x = (mx : ℝ) * (beta : ℝ) ^ fx)
    (hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy)
    (hgap_repr :
      gap =
        (beta : ℝ) ^
          (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) + fy))
    (hfx :
      fx =
        (d : Int) +
          (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) + fy))
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    ¬ ((1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)) ≤
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ∧
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
          (1 / 2) * ulp beta fexp1 (x / y)) := by
  have hleft :=
    round_round_div_numerator_left_grid_from_repr (beta := beta)
      (x := x) (gap := gap) (mx := mx) (fx := fx)
      (gapExp := FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) + fy)
      (d := d) hβ hx_repr hgap_repr hfx
  have hright :=
    round_round_div_floor_right_grid (beta := beta)
      (fexp := fexp1) (z := x / y) (y := y) (gap := gap)
      (my := my) (fy := fy) hβ hz_ne hy_repr hgap_repr
  exact round_round_div_aux1_floor_gap_contra_from_grid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := gap) (A := 2 * mx * beta ^ d)
    (B :=
      2 *
            FloatSpec.Core.Generic_fmt.rnd_floor
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1
                (x / y)) *
          my +
        my)
    hy_pos hgap_pos hleft hright hgap

/-- Coq `round_round_div_aux2` branch contradiction with the right endpoint
extracted from `roundR` and `ulp`.

This is the upper-midpoint analogue of
`round_round_div_aux1_floor_gap_contra_from_direct_right_grid`. -/
theorem round_round_div_aux2_floor_gap_contra_from_direct_right_grid
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (x y gap : ℝ) (mx my fx fy : Int) (d : Nat)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hz_ne : x / y ≠ 0)
    (hgap_pos : 0 < gap)
    (hx_repr : x = (mx : ℝ) * (beta : ℝ) ^ fx)
    (hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy)
    (hgap_repr :
      gap =
        (beta : ℝ) ^
          (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) + fy))
    (hfx :
      fx =
        (d : Int) +
          (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) + fy))
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    ¬ ((1 / 2) * ulp beta fexp1 (x / y) <
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ∧
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ≤
          (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y))) := by
  have hright :=
    round_round_div_numerator_left_grid_from_repr (beta := beta)
      (x := x) (gap := gap) (mx := mx) (fx := fx)
      (gapExp := FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) + fy)
      (d := d) hβ hx_repr hgap_repr hfx
  have hleft :=
    round_round_div_floor_right_grid (beta := beta)
      (fexp := fexp1) (z := x / y) (y := y) (gap := gap)
      (my := my) (fy := fy) hβ hz_ne hy_repr hgap_repr
  exact round_round_div_aux2_floor_gap_contra_from_grid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := gap)
    (A :=
      2 *
            FloatSpec.Core.Generic_fmt.rnd_floor
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1
                (x / y)) *
          my +
        my)
    (B := 2 * mx * beta ^ d)
    hy_pos hgap_pos hleft hright hgap

/-- Coq `round_round_div_aux1` branch contradiction with the numerator
representation extracted from `generic_format`.

Together with `round_round_div_floor_right_grid`, this leaves only the divisor
and branch-gap representations explicit for the aux1 lattice contradiction. -/
theorem round_round_div_aux1_floor_gap_contra_from_generic_left_grid
    (fexp1 fexp2 fexpX : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (x y gap : ℝ) (my fy : Int) (d : Nat)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hz_ne : x / y ≠ 0)
    (hgap_pos : 0 < gap)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexpX x)
    (hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy)
    (hgap_repr :
      gap =
        (beta : ℝ) ^
          (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) + fy))
    (hcexp_x :
      FloatSpec.Core.Generic_fmt.cexp beta fexpX x =
        (d : Int) +
          (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) + fy))
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    ¬ ((1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)) ≤
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ∧
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
          (1 / 2) * ulp beta fexp1 (x / y)) := by
  have hleft :=
    round_round_div_numerator_left_grid_from_generic (beta := beta)
      (fexp := fexpX) (x := x) (gap := gap)
      (gapExp := FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) + fy)
      (d := d) hβ hx_fmt hgap_repr hcexp_x
  have hright :=
    round_round_div_floor_right_grid (beta := beta)
      (fexp := fexp1) (z := x / y) (y := y) (gap := gap)
      (my := my) (fy := fy) hβ hz_ne hy_repr hgap_repr
  exact round_round_div_aux1_floor_gap_contra_from_grid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := gap)
    (A :=
      2 *
          FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpX x) *
        beta ^ d)
    (B :=
      2 *
            FloatSpec.Core.Generic_fmt.rnd_floor
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1
                (x / y)) *
          my +
        my)
    hy_pos hgap_pos hleft hright hgap

/-- Coq `round_round_div_aux2` branch contradiction with the numerator
representation extracted from `generic_format`.

This is the upper-midpoint analogue of
`round_round_div_aux1_floor_gap_contra_from_generic_left_grid`. -/
theorem round_round_div_aux2_floor_gap_contra_from_generic_left_grid
    (fexp1 fexp2 fexpX : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (x y gap : ℝ) (my fy : Int) (d : Nat)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hz_ne : x / y ≠ 0)
    (hgap_pos : 0 < gap)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexpX x)
    (hy_repr : y = (my : ℝ) * (beta : ℝ) ^ fy)
    (hgap_repr :
      gap =
        (beta : ℝ) ^
          (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) + fy))
    (hcexp_x :
      FloatSpec.Core.Generic_fmt.cexp beta fexpX x =
        (d : Int) +
          (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) + fy))
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    ¬ ((1 / 2) * ulp beta fexp1 (x / y) <
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ∧
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ≤
          (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y))) := by
  have hright :=
    round_round_div_numerator_left_grid_from_generic (beta := beta)
      (fexp := fexpX) (x := x) (gap := gap)
      (gapExp := FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) + fy)
      (d := d) hβ hx_fmt hgap_repr hcexp_x
  have hleft :=
    round_round_div_floor_right_grid (beta := beta)
      (fexp := fexp1) (z := x / y) (y := y) (gap := gap)
      (my := my) (fy := fy) hβ hz_ne hy_repr hgap_repr
  exact round_round_div_aux2_floor_gap_contra_from_grid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := gap)
    (A :=
      2 *
            FloatSpec.Core.Generic_fmt.rnd_floor
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1
                (x / y)) *
          my +
        my)
    (B :=
      2 *
          FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpX x) *
        beta ^ d)
    hy_pos hgap_pos hleft hright hgap

/-- Coq `round_round_div_aux1` branch contradiction with numerator and
denominator endpoint representations both extracted from `generic_format`.

Only the branch-gap exponent identity remains explicit at this layer. -/
theorem round_round_div_aux1_floor_gap_contra_from_generic_grids
    (fexp1 fexp2 fexpX fexpY : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (x y gap : ℝ) (d : Nat)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hz_ne : x / y ≠ 0)
    (hgap_pos : 0 < gap)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexpX x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexpY y)
    (hgap_repr :
      gap =
        (beta : ℝ) ^
          (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
            FloatSpec.Core.Generic_fmt.cexp beta fexpY y))
    (hcexp_x :
      FloatSpec.Core.Generic_fmt.cexp beta fexpX x =
        (d : Int) +
          (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
            FloatSpec.Core.Generic_fmt.cexp beta fexpY y))
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    ¬ ((1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)) ≤
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ∧
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
          (1 / 2) * ulp beta fexp1 (x / y)) := by
  have hleft :=
    round_round_div_numerator_left_grid_from_generic (beta := beta)
      (fexp := fexpX) (x := x) (gap := gap)
      (gapExp :=
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
          FloatSpec.Core.Generic_fmt.cexp beta fexpY y)
      (d := d) hβ hx_fmt hgap_repr hcexp_x
  have hright :=
    round_round_div_floor_right_grid_from_generic (beta := beta)
      (fexp := fexp1) (fexpY := fexpY)
      (z := x / y) (y := y) (gap := gap)
      hβ hz_ne hy_fmt hgap_repr
  exact round_round_div_aux1_floor_gap_contra_from_grid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := gap)
    (A :=
      2 *
          FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpX x) *
        beta ^ d)
    (B :=
      2 *
            FloatSpec.Core.Generic_fmt.rnd_floor
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1
                (x / y)) *
              FloatSpec.Core.Raux.Ztrunc
                (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y) +
          FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y))
    hy_pos hgap_pos hleft hright hgap

/-- Coq `round_round_div_aux2` branch contradiction with numerator and
denominator endpoint representations both extracted from `generic_format`.

This is the upper-midpoint analogue of
`round_round_div_aux1_floor_gap_contra_from_generic_grids`. -/
theorem round_round_div_aux2_floor_gap_contra_from_generic_grids
    (fexp1 fexp2 fexpX fexpY : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (x y gap : ℝ) (d : Nat)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hz_ne : x / y ≠ 0)
    (hgap_pos : 0 < gap)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexpX x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexpY y)
    (hgap_repr :
      gap =
        (beta : ℝ) ^
          (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
            FloatSpec.Core.Generic_fmt.cexp beta fexpY y))
    (hcexp_x :
      FloatSpec.Core.Generic_fmt.cexp beta fexpX x =
        (d : Int) +
          (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
            FloatSpec.Core.Generic_fmt.cexp beta fexpY y))
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    ¬ ((1 / 2) * ulp beta fexp1 (x / y) <
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ∧
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ≤
          (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y))) := by
  have hright :=
    round_round_div_numerator_left_grid_from_generic (beta := beta)
      (fexp := fexpX) (x := x) (gap := gap)
      (gapExp :=
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
          FloatSpec.Core.Generic_fmt.cexp beta fexpY y)
      (d := d) hβ hx_fmt hgap_repr hcexp_x
  have hleft :=
    round_round_div_floor_right_grid_from_generic (beta := beta)
      (fexp := fexp1) (fexpY := fexpY)
      (z := x / y) (y := y) (gap := gap)
      hβ hz_ne hy_fmt hgap_repr
  exact round_round_div_aux2_floor_gap_contra_from_grid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := gap)
    (A :=
      2 *
            FloatSpec.Core.Generic_fmt.rnd_floor
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1
                (x / y)) *
              FloatSpec.Core.Raux.Ztrunc
                (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y) +
          FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y))
    (B :=
      2 *
          FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpX x) *
        beta ^ d)
    hy_pos hgap_pos hleft hright hgap

/-- Coq `round_round_div_aux1` second-branch contradiction with numerator and
denominator endpoint representations both extracted from `generic_format`.

Here the branch gap is the numerator exponent, while the denominator/floor
endpoint has a nonnegative offset over that gap. -/
theorem round_round_div_aux1_floor_gap_contra_from_generic_grids_right_offset
    (fexp1 fexp2 fexpX fexpY : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (x y gap : ℝ) (d : Nat)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hz_ne : x / y ≠ 0)
    (hgap_pos : 0 < gap)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexpX x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexpY y)
    (hgap_repr :
      gap =
        (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexpX x)
    (hright_cexp :
      FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
          FloatSpec.Core.Generic_fmt.cexp beta fexpY y =
        (d : Int) + FloatSpec.Core.Generic_fmt.cexp beta fexpX x)
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    ¬ ((1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)) ≤
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ∧
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
          (1 / 2) * ulp beta fexp1 (x / y)) := by
  have hleft :=
    round_round_div_numerator_left_grid_from_generic (beta := beta)
      (fexp := fexpX) (x := x) (gap := gap)
      (gapExp := FloatSpec.Core.Generic_fmt.cexp beta fexpX x)
      (d := 0) hβ hx_fmt hgap_repr (by omega)
  have hright :=
    round_round_div_floor_right_grid_from_generic_offset (beta := beta)
      (fexp := fexp1) (fexpY := fexpY)
      (z := x / y) (y := y) (gap := gap)
      (gapExp := FloatSpec.Core.Generic_fmt.cexp beta fexpX x)
      (d := d) hβ hz_ne hy_fmt hgap_repr hright_cexp
  exact round_round_div_aux1_floor_gap_contra_from_grid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := gap)
    (A :=
      2 *
          FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpX x) *
        beta ^ (0 : Nat))
    (B :=
      (2 *
            FloatSpec.Core.Generic_fmt.rnd_floor
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1
                (x / y)) *
              FloatSpec.Core.Raux.Ztrunc
                (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y) +
          FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y)) *
        beta ^ d)
    hy_pos hgap_pos hleft hright hgap

/-- Coq `round_round_div_aux2` second-branch contradiction with numerator and
denominator endpoint representations both extracted from `generic_format`.

This is the upper-midpoint analogue of
`round_round_div_aux1_floor_gap_contra_from_generic_grids_right_offset`. -/
theorem round_round_div_aux2_floor_gap_contra_from_generic_grids_right_offset
    (fexp1 fexp2 fexpX fexpY : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    (x y gap : ℝ) (d : Nat)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hz_ne : x / y ≠ 0)
    (hgap_pos : 0 < gap)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexpX x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexpY y)
    (hgap_repr :
      gap =
        (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexpX x)
    (hright_cexp :
      FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
          FloatSpec.Core.Generic_fmt.cexp beta fexpY y =
        (d : Int) + FloatSpec.Core.Generic_fmt.cexp beta fexpX x)
    (hgap : ulp beta fexp2 (x / y) * y < gap) :
    ¬ ((1 / 2) * ulp beta fexp1 (x / y) <
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ∧
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) ≤
          (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y))) := by
  have hright :=
    round_round_div_numerator_left_grid_from_generic (beta := beta)
      (fexp := fexpX) (x := x) (gap := gap)
      (gapExp := FloatSpec.Core.Generic_fmt.cexp beta fexpX x)
      (d := 0) hβ hx_fmt hgap_repr (by omega)
  have hleft :=
    round_round_div_floor_right_grid_from_generic_offset (beta := beta)
      (fexp := fexp1) (fexpY := fexpY)
      (z := x / y) (y := y) (gap := gap)
      (gapExp := FloatSpec.Core.Generic_fmt.cexp beta fexpX x)
      (d := d) hβ hz_ne hy_fmt hgap_repr hright_cexp
  exact round_round_div_aux2_floor_gap_contra_from_grid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := gap)
    (A :=
      (2 *
            FloatSpec.Core.Generic_fmt.rnd_floor
              (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1
                (x / y)) *
              FloatSpec.Core.Raux.Ztrunc
                (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y) +
          FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpY y)) *
        beta ^ d)
    (B :=
      2 *
          FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpX x) *
        beta ^ (0 : Nat))
    hy_pos hgap_pos hleft hright hgap

/-- Coq `round_round_div_aux1` with the integer-grid endpoint arithmetic
packaged from `generic_format`.

This wrapper performs the same split as the Coq proof on
`fexp1 (mag x) - fexp1 (mag (x / y)) - fexp1 (mag y)`. In the nonnegative
branch the numerator exponent carries the offset over
`cexp (x / y) + cexp y`; in the negative branch the right endpoint carries the
offset over the numerator exponent. -/
theorem round_round_div_aux1_from_generic_grids
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        FloatSpec.Core.Raux.mag beta (x / y)) :
    ¬ (midp beta fexp1 (x / y) -
          (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y ∧
        x / y < midp beta fexp1 (x / y)) := by
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hxy_ne : x / y ≠ 0 := ne_of_gt hxy_pos
  have hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp1) x
    simpa [wp, PostCond.noThrow, Id.run, pure] using
      htrip ⟨hβ, hx_ne, hx_fmt⟩
  have hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp1) y
    simpa [wp, PostCond.noThrow, Id.run, pure] using
      htrip ⟨hβ, hy_ne, hy_fmt⟩
  have hdisj :=
    mag_div_disj (beta := beta) (x := x) (y := y) hβ hx_pos hy_pos
  apply round_round_div_aux1_from_floor_gap (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (z := x / y)
  by_cases hsplit :
      0 ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
          fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
          fexp1 (FloatSpec.Core.Raux.mag beta y)
  · let d : Nat :=
      Int.toNat
        (fexp1 (FloatSpec.Core.Raux.mag beta x) -
          fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
          fexp1 (FloatSpec.Core.Raux.mag beta y))
    have hcexp_x :
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 x =
          (d : Int) +
            (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
              FloatSpec.Core.Generic_fmt.cexp beta fexp1 y) := by
      have hto :
          (d : Int) =
            fexp1 (FloatSpec.Core.Raux.mag beta x) -
              fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
              fexp1 (FloatSpec.Core.Raux.mag beta y) := by
        simpa [d] using Int.toNat_of_nonneg hsplit
      simp [FloatSpec.Core.Generic_fmt.cexp]
      omega
    have hgap_bound :=
      round_round_div_ulp_lt_first_gap_low (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (hβ := hβ) (hexp := hexp) (x := x) (y := y)
        hx_pos hy_pos hfx hfy hf1 hdisj
    exact round_round_div_aux1_floor_gap_contra_from_generic_grids
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (fexpX := fexp1) (fexpY := fexp1)
      (x := x) (y := y)
      (gap := (beta : ℝ) ^
        (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
          FloatSpec.Core.Generic_fmt.cexp beta fexp1 y))
      (d := d) hβ hy_pos hxy_ne
      (zpow_pos (by exact_mod_cast (lt_trans Int.zero_lt_one hβ) : (0 : ℝ) < beta) _)
      hx_fmt hy_fmt rfl hcexp_x
      (by simpa [FloatSpec.Core.Generic_fmt.cexp] using hgap_bound)
  · have hsplit_lt :
      fexp1 (FloatSpec.Core.Raux.mag beta x) -
          fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
          fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 :=
      lt_of_not_ge hsplit
    let d : Nat :=
      Int.toNat
        (fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) +
          fexp1 (FloatSpec.Core.Raux.mag beta y) -
          fexp1 (FloatSpec.Core.Raux.mag beta x))
    have hright_cexp :
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
            FloatSpec.Core.Generic_fmt.cexp beta fexp1 y =
          (d : Int) + FloatSpec.Core.Generic_fmt.cexp beta fexp1 x := by
      have hnonneg :
          0 ≤
            fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) +
              fexp1 (FloatSpec.Core.Raux.mag beta y) -
              fexp1 (FloatSpec.Core.Raux.mag beta x) := by
        omega
      have hto :
          (d : Int) =
            fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) +
              fexp1 (FloatSpec.Core.Raux.mag beta y) -
              fexp1 (FloatSpec.Core.Raux.mag beta x) := by
        simpa [d] using Int.toNat_of_nonneg hnonneg
      simp [FloatSpec.Core.Generic_fmt.cexp]
      omega
    have hgap_bound :=
      round_round_div_ulp_lt_second_gap_low (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (hβ := hβ) (hexp := hexp) (x := x) (y := y)
        hx_pos hy_pos hfx hfy hf1 hdisj
    exact round_round_div_aux1_floor_gap_contra_from_generic_grids_right_offset
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (fexpX := fexp1) (fexpY := fexp1)
      (x := x) (y := y)
      (gap := (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 x)
      (d := d) hβ hy_pos hxy_ne
      (zpow_pos (by exact_mod_cast (lt_trans Int.zero_lt_one hβ) : (0 : ℝ) < beta) _)
      hx_fmt hy_fmt rfl hright_cexp
      (by simpa [FloatSpec.Core.Generic_fmt.cexp] using hgap_bound)

/-- Coq `round_round_div_aux2` with the integer-grid endpoint arithmetic
packaged from `generic_format`.

This is the upper-midpoint analogue of
`round_round_div_aux1_from_generic_grids`. -/
theorem round_round_div_aux2_from_generic_grids
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        FloatSpec.Core.Raux.mag beta (x / y)) :
    ¬ (midp beta fexp1 (x / y) < x / y ∧
        x / y ≤ midp beta fexp1 (x / y) +
          (1 / 2) * ulp beta fexp2 (x / y)) := by
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hxy_ne : x / y ≠ 0 := ne_of_gt hxy_pos
  have hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp1) x
    simpa [wp, PostCond.noThrow, Id.run, pure] using
      htrip ⟨hβ, hx_ne, hx_fmt⟩
  have hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp1) y
    simpa [wp, PostCond.noThrow, Id.run, pure] using
      htrip ⟨hβ, hy_ne, hy_fmt⟩
  have hdisj :=
    mag_div_disj (beta := beta) (x := x) (y := y) hβ hx_pos hy_pos
  apply round_round_div_aux2_from_floor_gap (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (z := x / y)
  by_cases hsplit :
      0 ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
          fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
          fexp1 (FloatSpec.Core.Raux.mag beta y)
  · let d : Nat :=
      Int.toNat
        (fexp1 (FloatSpec.Core.Raux.mag beta x) -
          fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
          fexp1 (FloatSpec.Core.Raux.mag beta y))
    have hcexp_x :
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 x =
          (d : Int) +
            (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
              FloatSpec.Core.Generic_fmt.cexp beta fexp1 y) := by
      have hto :
          (d : Int) =
            fexp1 (FloatSpec.Core.Raux.mag beta x) -
              fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
              fexp1 (FloatSpec.Core.Raux.mag beta y) := by
        simpa [d] using Int.toNat_of_nonneg hsplit
      simp [FloatSpec.Core.Generic_fmt.cexp]
      omega
    have hgap_bound :=
      round_round_div_ulp_lt_first_gap_low (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (hβ := hβ) (hexp := hexp) (x := x) (y := y)
        hx_pos hy_pos hfx hfy hf1 hdisj
    exact round_round_div_aux2_floor_gap_contra_from_generic_grids
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (fexpX := fexp1) (fexpY := fexp1)
      (x := x) (y := y)
      (gap := (beta : ℝ) ^
        (FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
          FloatSpec.Core.Generic_fmt.cexp beta fexp1 y))
      (d := d) hβ hy_pos hxy_ne
      (zpow_pos (by exact_mod_cast (lt_trans Int.zero_lt_one hβ) : (0 : ℝ) < beta) _)
      hx_fmt hy_fmt rfl hcexp_x
      (by simpa [FloatSpec.Core.Generic_fmt.cexp] using hgap_bound)
  · have hsplit_lt :
      fexp1 (FloatSpec.Core.Raux.mag beta x) -
          fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
          fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 :=
      lt_of_not_ge hsplit
    let d : Nat :=
      Int.toNat
        (fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) +
          fexp1 (FloatSpec.Core.Raux.mag beta y) -
          fexp1 (FloatSpec.Core.Raux.mag beta x))
    have hright_cexp :
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 (x / y) +
            FloatSpec.Core.Generic_fmt.cexp beta fexp1 y =
          (d : Int) + FloatSpec.Core.Generic_fmt.cexp beta fexp1 x := by
      have hnonneg :
          0 ≤
            fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) +
              fexp1 (FloatSpec.Core.Raux.mag beta y) -
              fexp1 (FloatSpec.Core.Raux.mag beta x) := by
        omega
      have hto :
          (d : Int) =
            fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) +
              fexp1 (FloatSpec.Core.Raux.mag beta y) -
              fexp1 (FloatSpec.Core.Raux.mag beta x) := by
        simpa [d] using Int.toNat_of_nonneg hnonneg
      simp [FloatSpec.Core.Generic_fmt.cexp]
      omega
    have hgap_bound :=
      round_round_div_ulp_lt_second_gap_low (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (hβ := hβ) (hexp := hexp) (x := x) (y := y)
        hx_pos hy_pos hfx hfy hf1 hdisj
    exact round_round_div_aux2_floor_gap_contra_from_generic_grids_right_offset
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
      (fexpX := fexp1) (fexpY := fexp1)
      (x := x) (y := y)
      (gap := (beta : ℝ) ^ FloatSpec.Core.Generic_fmt.cexp beta fexp1 x)
      (d := d) hβ hy_pos hxy_ne
      (zpow_pos (by exact_mod_cast (lt_trans Int.zero_lt_one hβ) : (0 : ℝ) < beta) _)
      hx_fmt hy_fmt rfl hright_cexp
      (by simpa [FloatSpec.Core.Generic_fmt.cexp] using hgap_bound)

/-- First non-top branch of Coq `round_round_div_aux2` after the mantissa
scaled inequality has been established. -/
theorem round_round_div_aux2_first_low_from_scaled
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        FloatSpec.Core.Raux.mag beta (x / y))
    (hdisj :
      FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
        FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1)
    (hscaled :
      2 *
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) * y +
          ulp beta fexp1 (x / y) * y +
            (beta : ℝ) ^
              (fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) +
                fexp1 (FloatSpec.Core.Raux.mag beta y)) ≤
        2 * x) :
    (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y)) <
      x / y -
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
          FloatSpec.Core.Generic_fmt.rnd_floor (x / y) := by
  have hgap :=
    round_round_div_ulp_lt_first_gap_low (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (hβ := hβ) (hexp := hexp)
      (x := x) (y := y) hx_pos hy_pos hfx hfy hf1 hdisj
  exact round_round_div_aux2_floor_gap_lower_from_scaled_branch (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := (beta : ℝ) ^
      (fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) +
        fexp1 (FloatSpec.Core.Raux.mag beta y)))
    hy_pos hgap hscaled

/-- Second non-top branch of Coq `round_round_div_aux2` after the mantissa
scaled inequality has been established. -/
theorem round_round_div_aux2_second_low_from_scaled
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hfx :
      fexp1 (FloatSpec.Core.Raux.mag beta x) <
        FloatSpec.Core.Raux.mag beta x)
    (hfy :
      fexp1 (FloatSpec.Core.Raux.mag beta y) <
        FloatSpec.Core.Raux.mag beta y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        FloatSpec.Core.Raux.mag beta (x / y))
    (hdisj :
      FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y ∨
        FloatSpec.Core.Raux.mag beta (x / y) =
          FloatSpec.Core.Raux.mag beta x - FloatSpec.Core.Raux.mag beta y + 1)
    (hscaled :
      2 *
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) * y +
          ulp beta fexp1 (x / y) * y +
            (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        2 * x) :
    (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y)) <
      x / y -
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
          FloatSpec.Core.Generic_fmt.rnd_floor (x / y) := by
  have hgap :=
    round_round_div_ulp_lt_second_gap_low (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (hβ := hβ) (hexp := hexp)
      (x := x) (y := y) hx_pos hy_pos hfx hfy hf1 hdisj
  exact round_round_div_aux2_floor_gap_lower_from_scaled_branch (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (gap := (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x))
    hy_pos hgap hscaled

/-- Coq `round_round_div_aux2` exponent split after the first `cut`.

The two branches correspond to the same integer split as aux1, but each branch
now proves that the floor gap is strictly above the upper endpoint
`1/2 * (ulp1 + ulp2)`. -/
theorem round_round_div_aux2_floor_gap_from_exponent_split
    (fexp1 fexp2 : Int → Int)
    (x y z : ℝ)
    (hfirst :
      0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            fexp1 (FloatSpec.Core.Raux.mag beta z) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        (1 / 2) * (ulp beta fexp1 z + ulp beta fexp2 z) <
          z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z)
    (hsecond :
      fexp1 (FloatSpec.Core.Raux.mag beta x) -
          fexp1 (FloatSpec.Core.Raux.mag beta z) -
          fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        (1 / 2) * (ulp beta fexp1 z + ulp beta fexp2 z) <
          z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z) :
    ¬ ((1 / 2) * ulp beta fexp1 z <
          z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z ∧
        z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z ≤
          (1 / 2) * (ulp beta fexp1 z + ulp beta fexp2 z)) := by
  by_cases hsplit :
      0 ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
          fexp1 (FloatSpec.Core.Raux.mag beta z) -
          fexp1 (FloatSpec.Core.Raux.mag beta y)
  · exact round_round_div_aux2_floor_gap_contra_from_lower (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (z := z) (hfirst hsplit)
  · exact round_round_div_aux2_floor_gap_contra_from_lower (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (z := z)
      (hsecond (lt_of_not_ge hsplit))

/-- Coq `round_round_div_aux2` reduced to its two exponent-split arithmetic
branches. -/
theorem round_round_div_aux2_from_exponent_split
    (fexp1 fexp2 : Int → Int)
    (x y z : ℝ)
    (hfirst :
      0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            fexp1 (FloatSpec.Core.Raux.mag beta z) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        (1 / 2) * (ulp beta fexp1 z + ulp beta fexp2 z) <
          z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z)
    (hsecond :
      fexp1 (FloatSpec.Core.Raux.mag beta x) -
          fexp1 (FloatSpec.Core.Raux.mag beta z) -
          fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        (1 / 2) * (ulp beta fexp1 z + ulp beta fexp2 z) <
          z -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor z) :
    ¬ (midp beta fexp1 z < z ∧
        z ≤ midp beta fexp1 z +
          (1 / 2) * ulp beta fexp2 z) := by
  exact round_round_div_aux2_from_floor_gap (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (z := z)
    (round_round_div_aux2_floor_gap_from_exponent_split (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y) (z := z)
      hfirst hsecond)

/-- Positive division wrapper with Coq `round_round_div_aux0` fully restored.

The restored aux0 theorem closes the top-binade branch directly. The only
remaining arithmetic premises are the lower and upper midpoint exclusions,
corresponding to upstream `round_round_div_aux1` and `round_round_div_aux2`. -/
theorem round_round_div_pos_from_aux0_even
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hlow :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        ¬ (midp beta fexp1 (x / y) -
              (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y ∧
            x / y < midp beta fexp1 (x / y)))
    (hhigh :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        ¬ (midp beta fexp1 (x / y) < x / y ∧
            x / y ≤ midp beta fexp1 (x / y) +
              (1 / 2) * ulp beta fexp2 (x / y))) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  exact round_round_div_pos_from_branch_exclusions_even (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ) (heven := heven) (hexp := hexp)
    (x := x) (y := y) hx_pos hy_pos hx_fmt hy_fmt
    (round_round_div_aux0_from_format (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      hβ hexp x y hx_pos hy_pos hx_fmt hy_fmt)
    hlow hhigh

/-- Positive division wrapper with Coq `round_round_div_aux0` reduced to gap cases.

After `round_round_div_aux0_from_gap_cases`, the top-binade branch of the
positive division proof is closed by the aux0 mantissa-gap disjunction. The
ordinary lower and upper midpoint exclusions remain the two arithmetic payloads
corresponding to Coq `round_round_div_aux1` and `round_round_div_aux2`. -/
theorem round_round_div_pos_from_gap_cases_even
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hgap :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
          FloatSpec.Core.Raux.mag beta (x / y) + 1 →
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
            (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y →
        x ≤
            (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
              (beta : ℝ) ^
                (FloatSpec.Core.Raux.mag beta (x / y) +
                  fexp1 (FloatSpec.Core.Raux.mag beta y)) ∨
          x ≤
            (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
              (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x))
    (hlow :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        ¬ (midp beta fexp1 (x / y) -
              (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y ∧
            x / y < midp beta fexp1 (x / y)))
    (hhigh :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        ¬ (midp beta fexp1 (x / y) < x / y ∧
            x / y ≤ midp beta fexp1 (x / y) +
              (1 / 2) * ulp beta fexp2 (x / y))) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  exact round_round_div_pos_from_branch_exclusions_even (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ) (heven := heven) (hexp := hexp)
    (x := x) (y := y) hx_pos hy_pos hx_fmt hy_fmt
    (round_round_div_aux0_from_gap_cases (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      hβ hexp x y hx_pos hy_pos hx_fmt hy_fmt hgap)
    hlow hhigh

/-- Positive division wrapper with Coq `round_round_div_aux0` split branches.

This is the same dispatcher as `round_round_div_pos_from_gap_cases_even`, but
with the aux0 top-binade premise exposed as the two integer-split branches from
the upstream proof. -/
theorem round_round_div_pos_from_exponent_split_even
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hfirst :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
          FloatSpec.Core.Raux.mag beta (x / y) + 1 →
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
            (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y →
        0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            FloatSpec.Core.Raux.mag beta (x / y) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        x ≤
          (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
            (beta : ℝ) ^
              (FloatSpec.Core.Raux.mag beta (x / y) +
                fexp1 (FloatSpec.Core.Raux.mag beta y)))
    (hsecond :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
          FloatSpec.Core.Raux.mag beta (x / y) + 1 →
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
            (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y →
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
            FloatSpec.Core.Raux.mag beta (x / y) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        x ≤
          (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
            (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x))
    (hlow :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        ¬ (midp beta fexp1 (x / y) -
              (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y ∧
            x / y < midp beta fexp1 (x / y)))
    (hhigh :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        ¬ (midp beta fexp1 (x / y) < x / y ∧
            x / y ≤ midp beta fexp1 (x / y) +
              (1 / 2) * ulp beta fexp2 (x / y))) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  exact round_round_div_pos_from_gap_cases_even (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ) (heven := heven) (hexp := hexp)
    (x := x) (y := y) hx_pos hy_pos hx_fmt hy_fmt
    (by
      intro htop hband
      exact round_round_div_aux0_gap_cases_from_exponent_split (beta := beta)
        (fexp1 := fexp1) (x := x) (y := y)
        (hfirst htop hband) (hsecond htop hband))
    hlow hhigh

/-- Positive division wrapper with all Coq `round_round_div_aux*` integer
splits exposed.

This packages the restored aux0 dispatcher together with the aux1 and aux2
floor-gap reductions. The only remaining premises are the arithmetic branch
inequalities from the three upstream `Zle_or_lt` splits. -/
theorem round_round_div_pos_from_all_exponent_splits_even
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (htop_first :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
          FloatSpec.Core.Raux.mag beta (x / y) + 1 →
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
            (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y →
        0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            FloatSpec.Core.Raux.mag beta (x / y) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        x ≤
          (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
            (beta : ℝ) ^
              (FloatSpec.Core.Raux.mag beta (x / y) +
                fexp1 (FloatSpec.Core.Raux.mag beta y)))
    (htop_second :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
          FloatSpec.Core.Raux.mag beta (x / y) + 1 →
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
            (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y →
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
            FloatSpec.Core.Raux.mag beta (x / y) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        x ≤
          (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
            (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x))
    (hlow_first :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
          (1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)))
    (hlow_second :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
            fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
          (1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)))
    (hhigh_first :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y)) <
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y))
    (hhigh_second :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
          FloatSpec.Core.Raux.mag beta (x / y) →
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
            fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y)) <
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y)) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  exact round_round_div_pos_from_exponent_split_even (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ) (heven := heven) (hexp := hexp)
    (x := x) (y := y) hx_pos hy_pos hx_fmt hy_fmt
    htop_first htop_second
    (by
      intro hf1
      exact round_round_div_aux1_from_exponent_split (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (x := x) (y := y) (z := x / y)
        (hlow_first hf1) (hlow_second hf1))
    (by
      intro hf1
      exact round_round_div_aux2_from_exponent_split (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (x := x) (y := y) (z := x / y)
        (hhigh_first hf1) (hhigh_second hf1))

/-- Positive division wrapper with the restored Coq `round_round_div_aux1` and
`round_round_div_aux2` payloads derived directly from formatted inputs.

The top-binade aux0 branch is already discharged by
`round_round_div_aux0_from_format`; the lower and upper midpoint exclusions are
now supplied by the generic-grid aux1/aux2 wrappers. -/
theorem round_round_div_pos_from_generic_grids_even
    (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  exact round_round_div_pos_from_aux0_even (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ) (heven := heven) (hexp := hexp)
    (x := x) (y := y) hx_pos hy_pos hx_fmt hy_fmt
    (by
      intro hf1
      exact round_round_div_aux1_from_generic_grids (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (hβ := hβ) (hexp := hexp)
        (x := x) (y := y) hx_pos hy_pos hx_fmt hy_fmt hf1)
    (by
      intro hf1
      exact round_round_div_aux2_from_generic_grids (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (hβ := hβ) (hexp := hexp)
        (x := x) (y := y) hx_pos hy_pos hx_fmt hy_fmt hf1)

private theorem round_round_eq_opp_for_div (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (x : ℝ)
    (h :
      round_round_eq beta fexp1 fexp2
        (fun t => ! choice1 (-(t + 1)))
        (fun t => ! choice2 (-(t + 1))) x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (-x) := by
  unfold round_round_eq at h ⊢
  rw [FloatSpec.Core.Generic_fmt.round_N_opp
    (beta := beta) (fexp := fexp2) (choice := choice2) (x := x)]
  rw [FloatSpec.Core.Generic_fmt.round_N_opp
    (beta := beta) (fexp := fexp1) (choice := choice1)
    (x :=
      FloatSpec.Core.Generic_fmt.roundR beta fexp2
        (FloatSpec.Core.Generic_fmt.Znearest
          (fun t => ! choice2 (-(t + 1)))) x)]
  rw [FloatSpec.Core.Generic_fmt.round_N_opp
    (beta := beta) (fexp := fexp1) (choice := choice1) (x := x)]
  exact congrArg Neg.neg h

/-- Coq `round_round_div`, factored at the missing positive-input arithmetic
lemma `round_round_div_aux`.

The assumed `haux` is the positive `0 < x`, `0 < y` division payload. This
theorem proves the remaining sign and zero wrapper logic. -/
theorem round_round_div_from_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (haux :
      ∀ (choice1 choice2 : Int → Bool) (x y : ℝ),
        0 < x → 0 < y →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
        round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y)) :
    ∀ x y : ℝ,
      y ≠ 0 →
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
      round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  classical
  intro x y hy_ne hx_fmt hy_fmt
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
    · have hx_opp_pos : 0 < -x := by linarith
      have hy_opp_pos : 0 < -y := by linarith
      have hx_opp_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-x) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := fexp1) (x := x)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hx_fmt
      have hy_opp_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-y) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := fexp1) (x := y)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hy_fmt
      have hcore :=
        haux choice1 choice2 (-x) (-y)
          hx_opp_pos hy_opp_pos hx_opp_fmt hy_opp_fmt
      have hdiv : x / y = (-x) / (-y) := by
        field_simp [hy_ne]
      rw [hdiv]
      exact hcore
    · exact False.elim (hy_ne hy_zero)
    · have hx_opp_pos : 0 < -x := by linarith
      have hx_opp_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-x) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := fexp1) (x := x)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hx_fmt
      have hcore :
          round_round_eq beta fexp1 fexp2
            (fun t => ! choice1 (-(t + 1)))
            (fun t => ! choice2 (-(t + 1))) ((-x) / y) :=
        haux (fun t => ! choice1 (-(t + 1)))
          (fun t => ! choice2 (-(t + 1))) (-x) y
          hx_opp_pos hy_pos hx_opp_fmt hy_fmt
      have hneg := round_round_eq_opp_for_div (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        (x := (-x) / y) hcore
      have hdiv : x / y = -((-x) / y) := by
        field_simp [hy_ne]
      rw [hdiv]
      exact hneg
  · have hdiv : x / y = 0 := by simp [hx_zero]
    have hzero_fmt1 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 0 :=
      FloatSpec.Core.Generic_fmt.generic_format_0_run
        (beta := beta) (fexp := fexp1)
    have hzero_fmt2 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 0 :=
      FloatSpec.Core.Generic_fmt.generic_format_0_run
        (beta := beta) (fexp := fexp2)
    have hinner0 :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) 0 = 0 :=
      FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2) (x := 0) hβ hzero_fmt2
    have houter0 :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            (FloatSpec.Core.Generic_fmt.Znearest choice1) 0 = 0 :=
      FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp1)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice1) (x := 0) hβ hzero_fmt1
    simpa [round_round_eq, hdiv, hinner0, houter0]
  · rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
    · have hy_opp_pos : 0 < -y := by linarith
      have hy_opp_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-y) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := fexp1) (x := y)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hy_fmt
      have hcore :
          round_round_eq beta fexp1 fexp2
            (fun t => ! choice1 (-(t + 1)))
            (fun t => ! choice2 (-(t + 1))) (x / (-y)) :=
        haux (fun t => ! choice1 (-(t + 1)))
          (fun t => ! choice2 (-(t + 1))) x (-y)
          hx_pos hy_opp_pos hx_fmt hy_opp_fmt
      have hneg := round_round_eq_opp_for_div (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        (x := x / (-y)) hcore
      have hdiv : x / y = -(x / (-y)) := by
        field_simp [hy_ne]
      rw [hdiv]
      exact hneg
    · exact False.elim (hy_ne hy_zero)
    · exact haux choice1 choice2 x y hx_pos hy_pos hx_fmt hy_fmt

/-- Coq `round_round_div`, with the positive arithmetic payload restored from
generic-format inputs.

This closes the sign and zero cases by reusing `round_round_div_from_aux`; the
positive case is now `round_round_div_pos_from_generic_grids_even`, which
packages the restored aux0/aux1/aux2 division proof obligations. -/
theorem round_round_div_from_generic_grids_even (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hexp : round_round_div_hyp fexp1 fexp2) :
    ∀ x y : ℝ,
      y ≠ 0 →
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
      round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  exact round_round_div_from_aux (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (hβ := hβ)
    (by
      intro choice1 choice2 x y hx_pos hy_pos hx_fmt hy_fmt
      exact round_round_div_pos_from_generic_grids_even (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        (hβ := hβ) (heven := heven) (hexp := hexp)
        (x := x) (y := y) hx_pos hy_pos hx_fmt hy_fmt)

/-- Coq: `round_round_div_aux0`.

The Coq statement carries the nearest-rounding choices even though this
top-binade exclusion does not inspect them. -/
theorem round_round_div_aux0 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (_choice1 _choice2 : Int → Bool) (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
        FloatSpec.Core.Raux.mag beta (x / y) + 1) :
    ¬ ((beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
        (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y) := by
  exact round_round_div_aux0_from_format (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) hβ hexp x y
    hx_pos hy_pos hx_fmt hy_fmt hf1

/-- Coq: `round_round_div_aux1`. -/
theorem round_round_div_aux1 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (_choice1 _choice2 : Int → Bool) (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        FloatSpec.Core.Raux.mag beta (x / y)) :
    ¬ (midp beta fexp1 (x / y) -
          (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y ∧
        x / y < midp beta fexp1 (x / y)) := by
  exact round_round_div_aux1_from_generic_grids (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) hβ hexp x y
    hx_pos hy_pos hx_fmt hy_fmt hf1

/-- Coq: `round_round_div_aux2`. -/
theorem round_round_div_aux2 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (_choice1 _choice2 : Int → Bool) (hβ : 1 < beta)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y)
    (hf1 :
      fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
        FloatSpec.Core.Raux.mag beta (x / y)) :
    ¬ (midp beta fexp1 (x / y) < x / y ∧
        x / y ≤ midp beta fexp1 (x / y) +
          (1 / 2) * ulp beta fexp2 (x / y)) := by
  exact round_round_div_aux2_from_generic_grids (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) hβ hexp x y
    hx_pos hy_pos hx_fmt hy_fmt hf1

/-- Coq: `round_round_div_aux`. -/
theorem round_round_div_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  exact round_round_div_pos_from_generic_grids_even (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ) (heven := heven) (hexp := hexp)
    (x := x) (y := y) hx_pos hy_pos hx_fmt hy_fmt

/-- Coq: `round_round_div`. -/
theorem round_round_div (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hexp : round_round_div_hyp fexp1 fexp2) :
    ∀ x y : ℝ,
      y ≠ 0 →
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
      round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  exact round_round_div_from_generic_grids_even (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ) (heven := heven) (hexp := hexp)

/-- Coq `round_round_div`, with the positive `round_round_div_aux` arithmetic
exposed as concrete split obligations.

The sign and zero logic is handled by `round_round_div_from_aux`; the positive
case is handled by `round_round_div_pos_from_all_exponent_splits_even`. -/
theorem round_round_div_from_all_exponent_splits_even (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool) (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hexp : round_round_div_hyp fexp1 fexp2)
    (htop_first :
      ∀ x y : ℝ,
        0 < x → 0 < y →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
        fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
            FloatSpec.Core.Raux.mag beta (x / y) + 1 →
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
            (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y →
        0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            FloatSpec.Core.Raux.mag beta (x / y) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        x ≤
          (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
            (beta : ℝ) ^
              (FloatSpec.Core.Raux.mag beta (x / y) +
                fexp1 (FloatSpec.Core.Raux.mag beta y)))
    (htop_second :
      ∀ x y : ℝ,
        0 < x → 0 < y →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
        fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) =
            FloatSpec.Core.Raux.mag beta (x / y) + 1 →
        (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) -
            (1 / 2) * ulp beta fexp2 (x / y) ≤ x / y →
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
            FloatSpec.Core.Raux.mag beta (x / y) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        x ≤
          (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta (x / y) * y -
            (beta : ℝ) ^ fexp1 (FloatSpec.Core.Raux.mag beta x))
    (hlow_first :
      ∀ x y : ℝ,
        0 < x → 0 < y →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
        fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
            FloatSpec.Core.Raux.mag beta (x / y) →
        0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
          (1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)))
    (hlow_second :
      ∀ x y : ℝ,
        0 < x → 0 < y →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
        fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
            FloatSpec.Core.Raux.mag beta (x / y) →
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
            fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y) <
          (1 / 2) * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y)))
    (hhigh_first :
      ∀ x y : ℝ,
        0 < x → 0 < y →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
        fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
            FloatSpec.Core.Raux.mag beta (x / y) →
        0 ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) -
            fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) →
        (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y)) <
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y))
    (hhigh_second :
      ∀ x y : ℝ,
        0 < x → 0 < y →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
        fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) ≤
            FloatSpec.Core.Raux.mag beta (x / y) →
        fexp1 (FloatSpec.Core.Raux.mag beta x) -
            fexp1 (FloatSpec.Core.Raux.mag beta (x / y)) -
            fexp1 (FloatSpec.Core.Raux.mag beta y) < 0 →
        (1 / 2) * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y)) <
          x / y -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x / y)) :
    ∀ x y : ℝ,
      y ≠ 0 →
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x →
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y →
      round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) := by
  exact round_round_div_from_aux (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (hβ := hβ)
    (by
      intro choice1 choice2 x y hx_pos hy_pos hx_fmt hy_fmt
      exact round_round_div_pos_from_all_exponent_splits_even (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        (hβ := hβ) (heven := heven) (hexp := hexp)
        (x := x) (y := y) hx_pos hy_pos hx_fmt hy_fmt
        (htop_first x y hx_pos hy_pos hx_fmt hy_fmt)
        (htop_second x y hx_pos hy_pos hx_fmt hy_fmt)
        (hlow_first x y hx_pos hy_pos hx_fmt hy_fmt)
        (hlow_second x y hx_pos hy_pos hx_fmt hy_fmt)
        (hhigh_first x y hx_pos hy_pos hx_fmt hy_fmt)
        (hhigh_second x y hx_pos hy_pos hx_fmt hy_fmt))

/-- Coq: `FLX_round_round_div_hyp`. -/
theorem FLX_round_round_div_hyp (prec prec' : Int)
    [Prec_gt_0 prec]
    (hprec : 2 * prec ≤ prec') :
    round_round_div_hyp
      (FloatSpec.Core.FLX.FLX_exp prec)
      (FloatSpec.Core.FLX.FLX_exp prec') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  unfold round_round_div_hyp FloatSpec.Core.FLX.FLX_exp
  constructor
  · intro ex
    omega
  constructor
  · intro ex ey _ _ _
    omega
  constructor
  · intro ex ey _ _ _
    omega
  constructor
  · intro ex ey _ _ _
    omega
  · intro ex ey _ _ _
    omega

/-- Coq: `FLT_round_round_div_hyp`. -/
theorem FLT_round_round_div_hyp
    (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (hemin : emin' ≤ emin - prec - 2)
    (hprec : 2 * prec ≤ prec') :
    round_round_div_hyp
      (FloatSpec.Core.FLT.FLT_exp prec emin)
      (FloatSpec.Core.FLT.FLT_exp prec' emin') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec'_pos : 0 < prec' := (Prec_gt_0.pos : 0 < prec')
  unfold round_round_div_hyp FloatSpec.Core.FLT.FLT_exp
  constructor
  · intro ex
    grind
  constructor
  · intro ex ey hx hy hxy
    grind
  constructor
  · intro ex ey hx hy hxy
    grind
  constructor
  · intro ex ey hx hy hxy
    grind
  · intro ex ey hx hy hxy
    grind

/-- Coq: `FTZ_round_round_div_hyp`. -/
theorem FTZ_round_round_div_hyp
    (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (hemin : emin' + prec' ≤ emin - 1)
    (hprec : 2 * prec ≤ prec') :
    round_round_div_hyp
      (FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (FloatSpec.Core.FTZ.FTZ_exp prec' emin') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec'_pos : 0 < prec' := (Prec_gt_0.pos : 0 < prec')
  unfold round_round_div_hyp FloatSpec.Core.FTZ.FTZ_exp
  constructor
  · intro ex
    split_ifs <;> omega
  constructor
  · intro ex ey hx hy hxy
    split_ifs at hx hy hxy ⊢ <;> omega
  constructor
  · intro ex ey hx hy hxy
    split_ifs at hx hy hxy ⊢ <;> omega
  constructor
  · intro ex ey hx hy hxy
    split_ifs at hx hy hxy ⊢ <;> omega
  · intro ex ey hx hy hxy
    split_ifs at hx hy hxy ⊢ <;> omega

/-- Coq: `round_round_div_FLX`. -/
theorem round_round_div_FLX (prec prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hprec : 2 * prec ≤ prec')
    (x y : ℝ)
    (hy_ne : y ≠ 0)
    (hx : FloatSpec.Core.FLX.FLX_format prec beta x)
    (hy : FloatSpec.Core.FLX.FLX_format prec beta y) :
    round_round_eq beta
      (FloatSpec.Core.FLX.FLX_exp prec)
      (FloatSpec.Core.FLX.FLX_exp prec')
      choice1 choice2 (x / y) := by
  exact round_round_div_from_generic_grids_even (beta := beta)
    (fexp1 := FloatSpec.Core.FLX.FLX_exp prec)
    (fexp2 := FloatSpec.Core.FLX.FLX_exp prec')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ) (heven := heven)
    (hexp := FLX_round_round_div_hyp
      (prec := prec) (prec' := prec') hprec)
    (x := x) (y := y) hy_ne
    (by simpa [FloatSpec.Core.FLX.FLX_format] using hx)
    (by simpa [FloatSpec.Core.FLX.FLX_format] using hy)

/-- Coq: `round_round_div_FLT`. -/
theorem round_round_div_FLT (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hemin : emin' ≤ emin - prec - 2)
    (hprec : 2 * prec ≤ prec')
    (x y : ℝ)
    (hy_ne : y ≠ 0)
    (hx : FloatSpec.Core.FLT.FLT_format prec emin beta x)
    (hy : FloatSpec.Core.FLT.FLT_format prec emin beta y) :
    round_round_eq beta
      (FloatSpec.Core.FLT.FLT_exp prec emin)
      (FloatSpec.Core.FLT.FLT_exp prec' emin')
      choice1 choice2 (x / y) := by
  exact round_round_div_from_generic_grids_even (beta := beta)
    (fexp1 := FloatSpec.Core.FLT.FLT_exp prec emin)
    (fexp2 := FloatSpec.Core.FLT.FLT_exp prec' emin')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ) (heven := heven)
    (hexp := FLT_round_round_div_hyp
      (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
      hemin hprec)
    (x := x) (y := y) hy_ne
    (by simpa [FloatSpec.Core.FLT.FLT_format] using hx)
    (by simpa [FloatSpec.Core.FLT.FLT_format] using hy)

/-- Coq: `round_round_div_FTZ`. -/
theorem round_round_div_FTZ (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (heven : ∃ n : Int, beta = 2 * n)
    (hemin : emin' + prec' ≤ emin - 1)
    (hprec : 2 * prec ≤ prec')
    (x y : ℝ)
    (hy_ne : y ≠ 0)
    (hx : FloatSpec.Core.FTZ.FTZ_format prec emin beta x)
    (hy : FloatSpec.Core.FTZ.FTZ_format prec emin beta y) :
    round_round_eq beta
      (FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (FloatSpec.Core.FTZ.FTZ_exp prec' emin')
      choice1 choice2 (x / y) := by
  exact round_round_div_from_generic_grids_even (beta := beta)
    (fexp1 := FloatSpec.Core.FTZ.FTZ_exp prec emin)
    (fexp2 := FloatSpec.Core.FTZ.FTZ_exp prec' emin')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ) (heven := heven)
    (hexp := FTZ_round_round_div_hyp
      (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
      hemin hprec)
    (x := x) (y := y) hy_ne
    (by simpa [FloatSpec.Core.FTZ.FTZ_format] using hx)
    (by simpa [FloatSpec.Core.FTZ.FTZ_format] using hy)

/-- Coq: `round_round_plus_hyp`. -/
def round_round_plus_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex ey, fexp1 (ex + 1) - 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 (ex - 1) + 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey)

/-- Coq: `mag_plus_disj`. -/
theorem mag_plus_disj (x y : ℝ)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hylex : y ≤ x) :
    FloatSpec.Core.Raux.mag beta (x + y) = FloatSpec.Core.Raux.mag beta x ∨
      FloatSpec.Core.Raux.mag beta (x + y) = FloatSpec.Core.Raux.mag beta x + 1 := by
  have htrip := FloatSpec.Core.Raux.mag_plus (beta := beta) (x := x) (y := y)
    hβ hy_pos hylex
  have hbounds :
      FloatSpec.Core.Raux.mag beta x ≤ FloatSpec.Core.Raux.mag beta (x + y) ∧
        FloatSpec.Core.Raux.mag beta (x + y) ≤ FloatSpec.Core.Raux.mag beta x + 1 := by
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  omega

/-- Coq: `mag_plus_separated`. -/
theorem mag_plus_separated (fexp : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
    (x y : ℝ)
    (hβ : 1 < beta)
    (hx_pos : 0 < x)
    (hy_nonneg : 0 ≤ y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp x)
    (hsep : FloatSpec.Core.Raux.mag beta y ≤ fexp (FloatSpec.Core.Raux.mag beta x)) :
    FloatSpec.Core.Raux.mag beta (x + y) = FloatSpec.Core.Raux.mag beta x := by
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_lt_ulp : y < FloatSpec.Core.Ulp.ulp (beta := beta) (fexp := fexp) x := by
    have hulp := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp) (x := x) hx_ne
    have hulp_eq :
        FloatSpec.Core.Ulp.ulp (beta := beta) (fexp := fexp) x =
          (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp x) := by
      simpa [wp, PostCond.noThrow, Id.run, pure] using hulp True.intro
    by_cases hy0 : y = 0
    · have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
      have hpow_pos :
          0 < (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp x) :=
        zpow_pos hbposR _
      simpa [hy0, hulp_eq]
        using hpow_pos
    · have hy_abs : |y| = y := abs_of_nonneg hy_nonneg
      have hmag_upper := FloatSpec.Core.Raux.mag_upper_bound
        (beta := beta) (x := y) hβ hy0
      have hy_lt_mag :
          y < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := by
        simpa [FloatSpec.Core.Raux.abs_val, hy_abs, wp, PostCond.noThrow, Id.run, pure]
          using hmag_upper True.intro
      have hbpow_le := FloatSpec.Core.Raux.bpow_le beta
        (FloatSpec.Core.Raux.mag beta y)
        (fexp (FloatSpec.Core.Raux.mag beta x)) hβ hsep
      have hpow_le :
          (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) ≤
            (beta : ℝ) ^ (fexp (FloatSpec.Core.Raux.mag beta x)) := by
        simpa [FloatSpec.Core.Raux.bpow_le_check, wp, PostCond.noThrow, Id.run, pure]
          using hbpow_le True.intro
      have hy_lt_bpow :
          y < (beta : ℝ) ^ (fexp (FloatSpec.Core.Raux.mag beta x)) :=
        lt_of_lt_of_le hy_lt_mag hpow_le
      simpa [FloatSpec.Core.Generic_fmt.cexp, hulp_eq] using hy_lt_bpow
  have hmag := FloatSpec.Core.Ulp.mag_plus_eps
    (beta := beta) (fexp := fexp) (x := x) hx_pos hx_fmt
    (eps := y) ⟨hy_nonneg, hy_lt_ulp⟩
  simpa [wp, PostCond.noThrow, Id.run, pure] using hmag hβ

/-- Coq: `round_round_plus_aux0_aux_aux`.

If the canonical exponents of two formatted addends are ordered and the target
format is coarse enough at the sum magnitude for both addends, then the sum is
representable in the target format.
-/
theorem round_round_plus_aux0_aux_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x y : ℝ)
    (hβ : 1 < beta)
    (hxy :
      fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta y))
    (hlnx :
      fexp2 (FloatSpec.Core.Raux.mag beta (x + y)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x))
    (hlny :
      fexp2 (FloatSpec.Core.Raux.mag beta (x + y)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta y))
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x + y) := by
  classical
  by_cases hx0 : x = 0
  · have hy_to_fexp2 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 y :=
      FloatSpec.Core.Generic_fmt.generic_inclusion_mag
        (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
        (x := y) hβ (by
          intro hy_ne
          simpa [hx0] using hlny) hy_fmt
    simpa [hx0] using hy_to_fexp2
  · by_cases hy0 : y = 0
    · have hx_to_fexp2 :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp2 x :=
        FloatSpec.Core.Generic_fmt.generic_inclusion_mag
          (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
          (x := x) hβ (by
            intro hx_ne
            simpa [hy0] using hlnx) hx_fmt
      simpa [hy0] using hx_to_fexp2
    · let mx : Int :=
        FloatSpec.Core.Raux.Ztrunc
          (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 x)
      let my : Int :=
        FloatSpec.Core.Raux.Ztrunc
          (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp1 y)
      let ex : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp1 x
      let ey : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp1 y
      let fxy : FloatSpec.Core.Defs.FlocqFloat beta :=
        { Fnum := mx + my * beta ^ Int.toNat (ey - ex), Fexp := ex }
      have hx_eq : x = FloatSpec.Core.Defs.F2R
          ({ Fnum := mx, Fexp := ex } : FloatSpec.Core.Defs.FlocqFloat beta) := by
        simpa [FloatSpec.Core.Generic_fmt.generic_format, mx, ex] using hx_fmt
      have hy_eq : y = FloatSpec.Core.Defs.F2R
          ({ Fnum := my, Fexp := ey } : FloatSpec.Core.Defs.FlocqFloat beta) := by
        simpa [FloatSpec.Core.Generic_fmt.generic_format, my, ey] using hy_fmt
      have hdiff_nonneg : 0 ≤ ey - ex := by
        simpa [FloatSpec.Core.Generic_fmt.cexp, ex, ey] using hxy
      have hpow_toNat :
          (beta : ℝ) ^ (ey - ex) =
            (beta : ℝ) ^ Int.toNat (ey - ex) :=
        FloatSpec.Core.Generic_fmt.zpow_nonneg_toNat
          (a := (beta : ℝ)) (k := ey - ex) hdiff_nonneg
      have hpow_cast :
          (beta : ℝ) ^ Int.toNat (ey - ex) =
            ((beta ^ Int.toNat (ey - ex) : Int) : ℝ) := by
        simpa using (Int.cast_pow (R := ℝ) (x := beta) (n := Int.toNat (ey - ex)))
      have hpow_split :
          ((beta : ℝ) ^ Int.toNat (ey - ex)) * (beta : ℝ) ^ ex =
            (beta : ℝ) ^ ey := by
        have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
        have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
        have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
        calc
          ((beta : ℝ) ^ Int.toNat (ey - ex)) * (beta : ℝ) ^ ex
              = ((beta : ℝ) ^ (ey - ex)) * (beta : ℝ) ^ ex := by
                rw [hpow_toNat]
          _ = (beta : ℝ) ^ ((ey - ex) + ex) := by
                rw [← zpow_add₀ hbne]
          _ = (beta : ℝ) ^ ey := by ring_nf
      have hxy_eq : FloatSpec.Core.Defs.F2R fxy = x + y := by
        calc
          FloatSpec.Core.Defs.F2R fxy
              =
                ((mx : ℝ) + ((my : ℝ) * (beta : ℝ) ^ Int.toNat (ey - ex))) *
                  (beta : ℝ) ^ ex := by
                    simp only [fxy, FloatSpec.Core.Defs.F2R, Int.cast_add,
                      Int.cast_mul, Int.cast_pow]
          _ =
                (mx : ℝ) * (beta : ℝ) ^ ex +
                  (my : ℝ) * ((beta : ℝ) ^ Int.toNat (ey - ex) *
                    (beta : ℝ) ^ ex) := by
                    ring
          _ =
                FloatSpec.Core.Defs.F2R
                    ({ Fnum := mx, Fexp := ex } : FloatSpec.Core.Defs.FlocqFloat beta) +
                  FloatSpec.Core.Defs.F2R
                    ({ Fnum := my, Fexp := ey } : FloatSpec.Core.Defs.FlocqFloat beta) := by
                    simp [FloatSpec.Core.Defs.F2R, hpow_split]
          _ = x + y := by rw [← hx_eq, ← hy_eq]
      have hbound :
          x + y ≠ 0 →
            FloatSpec.Core.Generic_fmt.cexp beta fexp2 (x + y) ≤ fxy.Fexp := by
        intro hsum_ne
        simpa [FloatSpec.Core.Generic_fmt.cexp, fxy, ex] using hlnx
      have hpre :
          beta > 1 ∧ FloatSpec.Core.Defs.F2R fxy = x + y ∧
            (x + y ≠ 0 →
              FloatSpec.Core.Generic_fmt.cexp beta fexp2 (x + y) ≤ fxy.Fexp) :=
        ⟨hβ, hxy_eq, hbound⟩
      have htrip := FloatSpec.Core.Generic_fmt.generic_format_F2R'
        (beta := beta) (fexp := fexp2) (x := x + y) (f := fxy)
      simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hpre

/-- Coq: `round_round_plus_aux0_aux`. -/
theorem round_round_plus_aux0_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x y : ℝ)
    (hβ : 1 < beta)
    (hlnx :
      fexp2 (FloatSpec.Core.Raux.mag beta (x + y)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x))
    (hlny :
      fexp2 (FloatSpec.Core.Raux.mag beta (x + y)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta y))
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x + y) := by
  classical
  by_cases hxy :
      fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta y)
  · exact round_round_plus_aux0_aux_aux (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
      hβ hxy hlnx hlny hx_fmt hy_fmt
  · have hyx :
        fexp1 (FloatSpec.Core.Raux.mag beta y) ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) := le_of_lt (not_le.mp hxy)
    have hlny_comm :
        fexp2 (FloatSpec.Core.Raux.mag beta (y + x)) ≤
          fexp1 (FloatSpec.Core.Raux.mag beta y) := by
      simpa [add_comm] using hlny
    have hlnx_comm :
        fexp2 (FloatSpec.Core.Raux.mag beta (y + x)) ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) := by
      simpa [add_comm] using hlnx
    have hfmt_comm :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (y + x) :=
      round_round_plus_aux0_aux_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2) (x := y) (y := x)
        (hβ := hβ) (hxy := hyx) (hlnx := hlny_comm)
        (hlny := hlnx_comm) (hx_fmt := hy_fmt) (hy_fmt := hx_fmt)
    simpa [add_comm] using hfmt_comm

/-- Coq: `round_round_plus_aux0`. -/
theorem round_round_plus_aux0 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_plus_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x)
    (hy_pos : 0 < y)
    (hyx : y ≤ x)
    (hln : fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 ≤
      FloatSpec.Core.Raux.mag beta y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x + y) := by
  classical
  rcases hexp with ⟨_, hsmall, hsame, hmag⟩
  have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
  by_cases hle_sep :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x)
  · have hsum_mag :
        FloatSpec.Core.Raux.mag beta (x + y) =
          FloatSpec.Core.Raux.mag beta x :=
      mag_plus_separated (beta := beta) (fexp := fexp1)
        (x := x) (y := y) hβ hx_pos hy_nonneg hx_fmt hle_sep
    apply round_round_plus_aux0_aux (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y) hβ
    · rw [hsum_mag]
      exact hmag (FloatSpec.Core.Raux.mag beta x)
        (FloatSpec.Core.Raux.mag beta x) (by omega)
    · rw [hsum_mag]
      exact hsame (FloatSpec.Core.Raux.mag beta x)
        (FloatSpec.Core.Raux.mag beta y) hln
    · exact hx_fmt
    · exact hy_fmt

  · have hgt_sep :
        fexp1 (FloatSpec.Core.Raux.mag beta x) <
          FloatSpec.Core.Raux.mag beta y := not_le.mp hle_sep
    have hmag_y_le_x :
        FloatSpec.Core.Raux.mag beta y ≤
          FloatSpec.Core.Raux.mag beta x := by
      have hxy_abs : |y| ≤ |x| := by
        simpa [abs_of_nonneg hy_nonneg, abs_of_nonneg (le_of_lt hx_pos)]
          using hyx
      have htrip := FloatSpec.Core.Raux.mag_le (beta := beta)
        (x := y) (y := x) hβ (ne_of_gt hy_pos) hxy_abs
      simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
    apply round_round_plus_aux0_aux (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y) hβ
    · rcases mag_plus_disj (beta := beta) (x := x) (y := y)
        hβ hy_pos hyx with hsum_mag | hsum_mag
      · rw [hsum_mag]
        exact hmag (FloatSpec.Core.Raux.mag beta x)
          (FloatSpec.Core.Raux.mag beta x) (by omega)
      · rw [hsum_mag]
        exact hsmall (FloatSpec.Core.Raux.mag beta x + 1)
          (FloatSpec.Core.Raux.mag beta x) (by
            have hfx_add_one_le_y :
                fexp1 (FloatSpec.Core.Raux.mag beta x) + 1 ≤
                  FloatSpec.Core.Raux.mag beta y :=
              Int.add_one_le_iff.mpr hgt_sep
            have hfx_add_one_le_x :
                fexp1 (FloatSpec.Core.Raux.mag beta x) + 1 ≤
                  FloatSpec.Core.Raux.mag beta x :=
              le_trans hfx_add_one_le_y hmag_y_le_x
            simpa using hfx_add_one_le_x)
    · rcases mag_plus_disj (beta := beta) (x := x) (y := y)
        hβ hy_pos hyx with hsum_mag | hsum_mag
      · rw [hsum_mag]
        exact hsame (FloatSpec.Core.Raux.mag beta x)
          (FloatSpec.Core.Raux.mag beta y) hln
      · rw [hsum_mag]
        exact hsmall (FloatSpec.Core.Raux.mag beta x + 1)
          (FloatSpec.Core.Raux.mag beta y) (by
            have hfx_add_one_le_y :
                fexp1 (FloatSpec.Core.Raux.mag beta x) + 1 ≤
                  FloatSpec.Core.Raux.mag beta y :=
              Int.add_one_le_iff.mpr hgt_sep
            simpa using hfx_add_one_le_y)
    · exact hx_fmt
    · exact hy_fmt

/-- Coq: `round_round_plus_aux1_aux`.

If `y` is at least `k` beta-exponent places below `x`, then the floor-rounding
gap of `x + y` in the `fexp` format is strictly positive and bounded by the
corresponding beta power.
-/
theorem round_round_plus_aux1_aux (k : Int)
    (hk : 0 < k)
    (fexp : Int → Int)
    (x y : ℝ)
    (hβ : 1 < beta)
    (hx_pos : 0 < x)
    (hy_pos : 0 < y)
    (hln :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp (FloatSpec.Core.Raux.mag beta x) - k)
    (hsum_mag :
      FloatSpec.Core.Raux.mag beta (x + y) =
        FloatSpec.Core.Raux.mag beta x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp x) :
    0 <
        (x + y) -
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor (x + y) ∧
      (x + y) -
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor (x + y) <
        (beta : ℝ) ^ (fexp (FloatSpec.Core.Raux.mag beta x) - k) := by
  classical
  let ex : Int := fexp (FloatSpec.Core.Raux.mag beta x)
  let mx : Int :=
    FloatSpec.Core.Raux.Ztrunc
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)
  have hcexp_sum :
      FloatSpec.Core.Generic_fmt.cexp beta fexp (x + y) = ex := by
    simp [FloatSpec.Core.Generic_fmt.cexp, ex, hsum_mag]
  have hround_eval :
      FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_floor (x + y) =
        ((mx : ℝ) * (beta : ℝ) ^ ex) := by
    have hsm_sum :
        FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp (x + y) =
          (mx : ℝ) + y * (beta : ℝ) ^ (-ex) := by
      have hx_eq :
          x = (mx : ℝ) * (beta : ℝ) ^ ex := by
        simpa [FloatSpec.Core.Generic_fmt.generic_format,
          FloatSpec.Core.Generic_fmt.scaled_mantissa,
          FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Defs.F2R,
          ex, mx] using hx_fmt
      have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
      have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
      have hpow_cancel : (beta : ℝ) ^ ex * (beta : ℝ) ^ (-ex) = 1 := by
        calc
          (beta : ℝ) ^ ex * (beta : ℝ) ^ (-ex)
              = (beta : ℝ) ^ (ex + (-ex)) := by
                rw [← zpow_add₀ hbne]
          _ = 1 := by simp
      calc
        FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp (x + y)
            = (x + y) * (beta : ℝ) ^ (-ex) := by
              simp [FloatSpec.Core.Generic_fmt.scaled_mantissa, hcexp_sum]
        _ = ((mx : ℝ) * (beta : ℝ) ^ ex + y) * (beta : ℝ) ^ (-ex) := by
              rw [hx_eq]
        _ = (mx : ℝ) + y * (beta : ℝ) ^ (-ex) := by
              rw [add_mul, mul_assoc, hpow_cancel, mul_one]
    have hscaled_y_pos : 0 < y * (beta : ℝ) ^ (-ex) := by
      have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
      exact mul_pos hy_pos (zpow_pos hbposR (-ex))
    have hscaled_y_lt_one : y * (beta : ℝ) ^ (-ex) < 1 := by
      have hy_ne : y ≠ 0 := ne_of_gt hy_pos
      have hy_lt_mag :
          y < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := by
        have htrip := FloatSpec.Core.Raux.mag_upper_bound
          (beta := beta) (x := y) hβ hy_ne
        simpa [FloatSpec.Core.Raux.abs_val, abs_of_pos hy_pos, wp,
          PostCond.noThrow, Id.run, pure] using htrip True.intro
      have hbpow_le := FloatSpec.Core.Raux.bpow_le beta
        (FloatSpec.Core.Raux.mag beta y) (ex - k) hβ (by
          simpa [ex] using hln)
      have hy_lt_ex_sub_k : y < (beta : ℝ) ^ (ex - k) := by
        exact lt_of_lt_of_le hy_lt_mag
          (by
            simpa [FloatSpec.Core.Raux.bpow_le_check, wp,
              PostCond.noThrow, Id.run, pure] using hbpow_le True.intro)
      have hpow_cancel :
          (beta : ℝ) ^ (ex - k) * (beta : ℝ) ^ (-ex) =
            (beta : ℝ) ^ (-k) := by
        have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
        have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
        have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
        calc
          (beta : ℝ) ^ (ex - k) * (beta : ℝ) ^ (-ex)
              = (beta : ℝ) ^ ((ex - k) + (-ex)) := by
                rw [← zpow_add₀ hbne]
          _ = (beta : ℝ) ^ (-k) := by ring_nf
      have hbpow_neg_k_le_one : (beta : ℝ) ^ (-k) ≤ 1 := by
        have hle := FloatSpec.Core.Raux.bpow_le beta (-k) 0 hβ (by omega)
        simpa [FloatSpec.Core.Raux.bpow_le_check, wp, PostCond.noThrow, Id.run,
          pure, zpow_zero] using hle True.intro
      have hscale_pos : 0 < (beta : ℝ) ^ (-ex) := by
        have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
        have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
        exact zpow_pos hbposR (-ex)
      have hy_scaled_lt :
          y * (beta : ℝ) ^ (-ex) <
            (beta : ℝ) ^ (ex - k) * (beta : ℝ) ^ (-ex) :=
        mul_lt_mul_of_pos_right hy_lt_ex_sub_k hscale_pos
      calc
        y * (beta : ℝ) ^ (-ex)
            < (beta : ℝ) ^ (ex - k) * (beta : ℝ) ^ (-ex) := hy_scaled_lt
        _ = (beta : ℝ) ^ (-k) := hpow_cancel
        _ ≤ 1 := hbpow_neg_k_le_one
    have hfloor :
        FloatSpec.Core.Generic_fmt.rnd_floor
            ((mx : ℝ) + y * (beta : ℝ) ^ (-ex)) = mx := by
      unfold FloatSpec.Core.Generic_fmt.rnd_floor FloatSpec.Core.Raux.Zfloor
      exact (Int.floor_eq_iff).2
        ⟨by linarith [hscaled_y_pos],
         by linarith [hscaled_y_lt_one]⟩
    calc
      FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_floor (x + y)
          =
            ((FloatSpec.Core.Generic_fmt.rnd_floor
                (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp (x + y)) :
              Int) : ℝ) * (beta : ℝ) ^ ex := by
              simp [FloatSpec.Core.Generic_fmt.roundR, hcexp_sum]
      _ =
            ((FloatSpec.Core.Generic_fmt.rnd_floor
                ((mx : ℝ) + y * (beta : ℝ) ^ (-ex)) : Int) : ℝ) *
              (beta : ℝ) ^ ex := by
              rw [hsm_sum]
      _ = (mx : ℝ) * (beta : ℝ) ^ ex := by
              rw [hfloor]
  have hdiff_eq :
      (x + y) -
          FloatSpec.Core.Generic_fmt.roundR beta fexp
            FloatSpec.Core.Generic_fmt.rnd_floor (x + y) = y := by
    have hx_eq :
        x = (mx : ℝ) * (beta : ℝ) ^ ex := by
      simpa [FloatSpec.Core.Generic_fmt.generic_format,
        FloatSpec.Core.Generic_fmt.scaled_mantissa,
        FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Defs.F2R,
        ex, mx] using hx_fmt
    rw [hround_eval, hx_eq]
    ring
  constructor
  · simpa [hdiff_eq] using hy_pos
  · have hy_ne : y ≠ 0 := ne_of_gt hy_pos
    have hy_lt_mag :
        y < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := by
      have htrip := FloatSpec.Core.Raux.mag_upper_bound
        (beta := beta) (x := y) hβ hy_ne
      simpa [FloatSpec.Core.Raux.abs_val, abs_of_pos hy_pos, wp,
        PostCond.noThrow, Id.run, pure] using htrip True.intro
    have hbpow_le := FloatSpec.Core.Raux.bpow_le beta
      (FloatSpec.Core.Raux.mag beta y) (ex - k) hβ (by
        simpa [ex] using hln)
    have hy_lt_bound : y < (beta : ℝ) ^ (ex - k) :=
      lt_of_lt_of_le hy_lt_mag
        (by
          simpa [FloatSpec.Core.Raux.bpow_le_check, wp,
            PostCond.noThrow, Id.run, pure] using hbpow_le True.intro)
    simpa [hdiff_eq, ex] using hy_lt_bound

/-- Coq: `round_round_plus_aux1`.

If `y` is at least two beta-exponent places below a positive formatted `x`, then
rounding `x + y` to the coarser format after the finer nearest rounding agrees
with direct nearest rounding to the coarser format.
-/
theorem round_round_plus_aux1 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hexp : round_round_plus_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x)
    (hy_pos : 0 < y)
    (hln :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 2)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) := by
  classical
  let e : Int := fexp1 (FloatSpec.Core.Raux.mag beta x)
  have hsum_pos : 0 < x + y := add_pos hx_pos hy_pos
  have hsum_ne : x + y ≠ 0 := ne_of_gt hsum_pos
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hsum_mag :
      FloatSpec.Core.Raux.mag beta (x + y) =
        FloatSpec.Core.Raux.mag beta x := by
    apply mag_plus_separated (beta := beta) (fexp := fexp1)
      (x := x) (y := y) hβ hx_pos (le_of_lt hy_pos) hx_fmt
    omega
  rcases hexp with ⟨_, _, _, hmag⟩
  have hf21 :
      fexp2 (FloatSpec.Core.Raux.mag beta (x + y)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (x + y)) := by
    rw [hsum_mag]
    exact hmag (FloatSpec.Core.Raux.mag beta x)
      (FloatSpec.Core.Raux.mag beta x) (by omega)
  have hf1_le_mag :
      fexp1 (FloatSpec.Core.Raux.mag beta (x + y)) ≤
        FloatSpec.Core.Raux.mag beta (x + y) := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp1) x
    have hx_cexp_le :
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 x ≤
          FloatSpec.Core.Raux.mag beta x := by
      have hlt :
          FloatSpec.Core.Generic_fmt.cexp beta fexp1 x <
            FloatSpec.Core.Raux.mag beta x := by
        simpa [wp, PostCond.noThrow, Id.run, pure] using
          htrip ⟨hβ, hx_ne, hx_fmt⟩
      exact le_of_lt hlt
    simpa [FloatSpec.Core.Generic_fmt.cexp, hsum_mag] using hx_cexp_le
  have hgap := round_round_plus_aux1_aux (beta := beta) (k := 2)
    (hk := by omega) (fexp := fexp1) (x := x) (y := y)
    (hβ := hβ) (hx_pos := hx_pos) (hy_pos := hy_pos)
    (hln := hln) (hsum_mag := hsum_mag) (hx_fmt := hx_fmt)
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hb2ℤ : (2 : Int) ≤ beta := by omega
  have hb2R : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hb2ℤ
  have hpow_two_nonneg : 0 ≤ (beta : ℝ) ^ (e - 2) :=
    le_of_lt (zpow_pos hbposR (e - 2))
  have hpow_two_to_half :
      (beta : ℝ) ^ (e - 2) ≤
        (1 / 2 : ℝ) * ((beta : ℝ) ^ e) := by
    have hbeta_sq_ge_two : (2 : ℝ) ≤ (beta : ℝ) ^ (2 : Int) := by
      norm_num [zpow_ofNat]
      nlinarith
    have hneg_two_le_half :
        (beta : ℝ) ^ (-(2 : Int)) ≤ (1 / 2 : ℝ) := by
      have hinv_le :
          1 / ((beta : ℝ) ^ (2 : Int)) ≤ (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) hbeta_sq_ge_two
      simpa [one_div, zpow_neg] using hinv_le
    have hpow_cancel :
        (beta : ℝ) ^ (e - 2) =
          (beta : ℝ) ^ e * (beta : ℝ) ^ (-(2 : Int)) := by
      calc
        (beta : ℝ) ^ (e - 2)
            = (beta : ℝ) ^ (e + (-(2 : Int))) := by ring_nf
        _ = (beta : ℝ) ^ e * (beta : ℝ) ^ (-(2 : Int)) := by
              rw [zpow_add₀ hbne]
    rw [hpow_cancel]
    have hmul := mul_le_mul_of_nonneg_left hneg_two_le_half
      (le_of_lt (zpow_pos hbposR e))
    nlinarith
  have hpow_two_to_half_diff :
      (beta : ℝ) ^ (e - 2) ≤
        (1 / 2 : ℝ) * ((beta : ℝ) ^ e - (beta : ℝ) ^ (e - 1)) := by
    have hpow_e_split :
        (beta : ℝ) ^ e =
          (beta : ℝ) ^ (e - 2) * (beta : ℝ) ^ (2 : Int) := by
      calc
        (beta : ℝ) ^ e = (beta : ℝ) ^ ((e - 2) + 2) := by ring_nf
        _ = (beta : ℝ) ^ (e - 2) * (beta : ℝ) ^ (2 : Int) := by
              rw [zpow_add₀ hbne]
    have hpow_em1_split :
        (beta : ℝ) ^ (e - 1) =
          (beta : ℝ) ^ (e - 2) * (beta : ℝ) := by
      calc
        (beta : ℝ) ^ (e - 1) = (beta : ℝ) ^ ((e - 2) + 1) := by ring_nf
        _ = (beta : ℝ) ^ (e - 2) * (beta : ℝ) ^ (1 : Int) := by
              rw [zpow_add₀ hbne]
        _ = (beta : ℝ) ^ (e - 2) * (beta : ℝ) := by simp
    have hfactor : (1 : ℝ) ≤ (1 / 2 : ℝ) *
        ((beta : ℝ) ^ (2 : Int) - (beta : ℝ)) := by
      norm_num [zpow_ofNat]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hfactor hpow_two_nonneg
    rw [hpow_e_split, hpow_em1_split]
    nlinarith
  have hulp1 :
      ulp beta fexp1 (x + y) = (beta : ℝ) ^ e := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := x + y) hsum_ne
    simpa [e, hsum_mag, FloatSpec.Core.Generic_fmt.cexp, wp,
      PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hx_mid :
      x + y < midp beta fexp1 (x + y) := by
    have hgap_half :
        (x + y) -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x + y) <
          (1 / 2 : ℝ) * ulp beta fexp1 (x + y) :=
      lt_of_lt_of_le hgap.2 (by simpa [hulp1, e] using hpow_two_to_half)
    unfold midp
    linarith
  apply round_round_lt_mid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (x := x + y) hβ
  · exact hsum_pos
  · exact hf21
  · exact hf1_le_mag
  · exact hx_mid
  · intro hfurther
    let e2 : Int := fexp2 (FloatSpec.Core.Raux.mag beta (x + y))
    have hulp2 :
        ulp beta fexp2 (x + y) = (beta : ℝ) ^ e2 := by
      have htrip := FloatSpec.Core.Ulp.ulp_neq_0
        (beta := beta) (fexp := fexp2) (x := x + y) hsum_ne
      simpa [e2, FloatSpec.Core.Generic_fmt.cexp, wp,
        PostCond.noThrow, Id.run, pure] using htrip True.intro
    have hpow_e2_le :
        (beta : ℝ) ^ e2 ≤ (beta : ℝ) ^ (e - 1) := by
      have htrip := FloatSpec.Core.Raux.bpow_le (beta := beta)
        (e1 := e2) (e2 := e - 1) hβ (by simpa [e, e2, hsum_mag] using hfurther)
      simpa [FloatSpec.Core.Raux.bpow_le_check, wp, PostCond.noThrow, Id.run,
        pure] using htrip True.intro
    have hpow_to_diff :
        (beta : ℝ) ^ (e - 2) ≤
          (1 / 2 : ℝ) * ((beta : ℝ) ^ e - (beta : ℝ) ^ e2) := by
      have hsub :
          (beta : ℝ) ^ e - (beta : ℝ) ^ (e - 1) ≤
            (beta : ℝ) ^ e - (beta : ℝ) ^ e2 := by
        linarith
      have hhalf := mul_le_mul_of_nonneg_left hsub (by norm_num : (0 : ℝ) ≤ 1 / 2)
      exact le_trans hpow_two_to_half_diff (by exact hhalf)
    have hgap_further :
        (x + y) -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x + y) <
          (1 / 2 : ℝ) * (ulp beta fexp1 (x + y) - ulp beta fexp2 (x + y)) := by
      exact lt_of_lt_of_le hgap.2 (by
        simpa [hulp1, hulp2, e] using hpow_to_diff)
    unfold midp
    linarith

/-- Coq: `round_round_plus_aux2`.

Combines the separated small-addend case `round_round_plus_aux1` with the exact
addition case `round_round_plus_aux0`.
-/
theorem round_round_plus_aux2 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hexp : round_round_plus_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x)
    (hy_pos : 0 < y)
    (hyx : y ≤ x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) := by
  classical
  by_cases hsmall :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 2
  · exact round_round_plus_aux1 (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2) (hβ := hβ)
      (hexp := hexp) (x := x) (y := y) (hx_pos := hx_pos)
      (hy_pos := hy_pos) (hln := hsmall) (hx_fmt := hx_fmt)
  · have hlarge :
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 ≤
          FloatSpec.Core.Raux.mag beta y := by
      omega
    have hsum_fmt :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x + y) :=
      round_round_plus_aux0 (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2) (hβ := hβ)
        (hexp := hexp) (x := x) (y := y) (hx_pos := hx_pos)
        (hy_pos := hy_pos) (hyx := hyx) (hln := hlarge)
        (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)
    have hinner :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) (x + y) =
          x + y := by
      exact FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
        (x := x + y) hβ hsum_fmt
    simpa [round_round_eq, hinner]

/-- Coq: `round_round_plus_aux`.

Nonnegative-input wrapper around `round_round_plus_aux2`; exact zero addends
are handled by inclusion into the coarser format.
-/
theorem round_round_plus_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hexp : round_round_plus_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hy_nonneg : 0 ≤ y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) := by
  classical
  rcases hexp with ⟨hplus, hminus, hsame, hmag⟩
  by_cases hx0 : x = 0
  · have hy_fmt2 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 y :=
      FloatSpec.Core.Generic_fmt.generic_inclusion_mag
        (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
        (x := y) hβ (by
          intro hy_ne
          exact hmag (FloatSpec.Core.Raux.mag beta y)
            (FloatSpec.Core.Raux.mag beta y) (by omega)) hy_fmt
    have hinner :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) y = y :=
      FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
        (x := y) hβ hy_fmt2
    simpa [round_round_eq, hx0, hinner]
  · by_cases hy0 : y = 0
    · have hx_fmt2 :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp2 x :=
        FloatSpec.Core.Generic_fmt.generic_inclusion_mag
          (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
          (x := x) hβ (by
            intro hx_ne
            exact hmag (FloatSpec.Core.Raux.mag beta x)
              (FloatSpec.Core.Raux.mag beta x) (by omega)) hx_fmt
      have hinner :
          FloatSpec.Core.Generic_fmt.roundR beta fexp2
              (FloatSpec.Core.Generic_fmt.Znearest choice2) x = x :=
        FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := beta) (fexp := fexp2)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
          (x := x) hβ hx_fmt2
      simpa [round_round_eq, hy0, hinner]
    · have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
      have hy_pos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hy0)
      by_cases hxy : x < y
      · have hres := round_round_plus_aux2 (beta := beta)
          (fexp1 := fexp1) (fexp2 := fexp2)
          (choice1 := choice1) (choice2 := choice2) (hβ := hβ)
          (hexp := ⟨hplus, hminus, hsame, hmag⟩)
          (x := y) (y := x) (hx_pos := hy_pos) (hy_pos := hx_pos)
          (hyx := le_of_lt hxy) (hx_fmt := hy_fmt) (hy_fmt := hx_fmt)
        simpa [add_comm] using hres
      · exact round_round_plus_aux2 (beta := beta)
          (fexp1 := fexp1) (fexp2 := fexp2)
          (choice1 := choice1) (choice2 := choice2) (hβ := hβ)
          (hexp := ⟨hplus, hminus, hsame, hmag⟩)
          (x := x) (y := y) (hx_pos := hx_pos) (hy_pos := hy_pos)
          (hyx := le_of_not_gt hxy) (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)

/-- Coq: `round_round_minus_aux0_aux`. -/
theorem round_round_minus_aux0_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (x y : ℝ)
    (hβ : 1 < beta)
    (hlnx :
      fexp2 (FloatSpec.Core.Raux.mag beta (x - y)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x))
    (hlny :
      fexp2 (FloatSpec.Core.Raux.mag beta (x - y)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta y))
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x - y) := by
  have hmag_opp :
      FloatSpec.Core.Raux.mag beta (-y) = FloatSpec.Core.Raux.mag beta y := by
    have htrip := FloatSpec.Core.Raux.mag_opp (beta := beta) (x := y) hβ
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hy_opp_fmt :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-y) := by
    have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := fexp1) (x := y)
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hy_fmt
  have hfmt_add :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x + (-y)) :=
    round_round_plus_aux0_aux (beta := beta) (fexp1 := fexp1)
      (fexp2 := fexp2) (x := x) (y := -y) (hβ := hβ)
      (hlnx := by simpa [sub_eq_add_neg] using hlnx)
      (hlny := by simpa [sub_eq_add_neg, hmag_opp] using hlny)
      (hx_fmt := hx_fmt) (hy_fmt := hy_opp_fmt)
  simpa [sub_eq_add_neg] using hfmt_add

/-- Coq: `round_round_minus_aux0`.

When two positive `fexp1`-format numbers are close in magnitude, their
difference is exactly representable in the wider `fexp2` format. -/
theorem round_round_minus_aux0 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_plus_hyp fexp1 fexp2)
    (x y : ℝ)
    (hy_pos : 0 < y)
    (hyx : y < x)
    (hln :
      fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 ≤
        FloatSpec.Core.Raux.mag beta y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x - y) := by
  classical
  rcases hexp with ⟨hplus, _, hsame, hmag⟩
  have hx_pos : 0 < x := lt_trans hy_pos hyx
  have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hmxy_le_mx :
      FloatSpec.Core.Raux.mag beta (x - y) ≤
        FloatSpec.Core.Raux.mag beta x := by
    have htrip := FloatSpec.Core.Raux.mag_minus
      (beta := beta) (x := x) (y := y) hβ hy_pos hyx
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hmy_le_mx :
      FloatSpec.Core.Raux.mag beta y ≤
        FloatSpec.Core.Raux.mag beta x := by
    have hy_abs_le_x : |y| ≤ |x| := by
      simpa [abs_of_nonneg hy_nonneg, abs_of_nonneg hx_nonneg]
        using le_of_lt hyx
    have htrip := FloatSpec.Core.Raux.mag_le
      (beta := beta) (x := y) (y := x) hβ (ne_of_gt hy_pos) hy_abs_le_x
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  by_cases hclose :
      FloatSpec.Core.Raux.mag beta x - 2 <
        FloatSpec.Core.Raux.mag beta y
  · have hcases :
        FloatSpec.Core.Raux.mag beta y = FloatSpec.Core.Raux.mag beta x ∨
          FloatSpec.Core.Raux.mag beta y =
            FloatSpec.Core.Raux.mag beta x - 1 := by
      omega
    rcases hcases with hmy_eq | hmy_eq
    · apply round_round_minus_aux0_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
        (hβ := hβ)
      · exact hmag (FloatSpec.Core.Raux.mag beta (x - y))
          (FloatSpec.Core.Raux.mag beta x) (by omega)
      · rw [hmy_eq]
        exact hmag (FloatSpec.Core.Raux.mag beta (x - y))
          (FloatSpec.Core.Raux.mag beta x) (by omega)
      · exact hx_fmt
      · exact hy_fmt
    · apply round_round_minus_aux0_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
        (hβ := hβ)
      · exact hmag (FloatSpec.Core.Raux.mag beta (x - y))
          (FloatSpec.Core.Raux.mag beta x) (by omega)
      · rw [hmy_eq]
        exact hmag (FloatSpec.Core.Raux.mag beta (x - y))
          (FloatSpec.Core.Raux.mag beta x - 1) (by omega)
      · exact hx_fmt
      · exact hy_fmt
  · have hmy_small :
        FloatSpec.Core.Raux.mag beta y ≤
          FloatSpec.Core.Raux.mag beta x - 2 := by
      omega
    have hmx_sub_one_le_mxy :
        FloatSpec.Core.Raux.mag beta x - 1 ≤
          FloatSpec.Core.Raux.mag beta (x - y) := by
      have htrip := FloatSpec.Core.Raux.mag_minus_lb
        (beta := beta) (x := x) (y := y) hβ hx_pos hy_pos hmy_small
      simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
    have hcases :
        FloatSpec.Core.Raux.mag beta (x - y) =
            FloatSpec.Core.Raux.mag beta x ∨
          FloatSpec.Core.Raux.mag beta (x - y) =
            FloatSpec.Core.Raux.mag beta x - 1 := by
      omega
    rcases hcases with hmxy_eq | hmxy_eq
    · apply round_round_minus_aux0_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
        (hβ := hβ)
      · rw [hmxy_eq]
        exact hmag (FloatSpec.Core.Raux.mag beta x)
          (FloatSpec.Core.Raux.mag beta x) (by omega)
      · rw [hmxy_eq]
        exact hsame (FloatSpec.Core.Raux.mag beta x)
          (FloatSpec.Core.Raux.mag beta y) hln
      · exact hx_fmt
      · exact hy_fmt
    · apply round_round_minus_aux0_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
        (hβ := hβ)
      · rw [hmxy_eq]
        have hcond :
            fexp1 (FloatSpec.Core.Raux.mag beta x - 1 + 1) - 1 ≤
              FloatSpec.Core.Raux.mag beta x := by
          have hcond' :
              fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 ≤
                FloatSpec.Core.Raux.mag beta x := le_trans hln hmy_le_mx
          simpa using hcond'
        exact hplus (FloatSpec.Core.Raux.mag beta x - 1)
          (FloatSpec.Core.Raux.mag beta x) hcond
      · rw [hmxy_eq]
        have hcond :
            fexp1 (FloatSpec.Core.Raux.mag beta x - 1 + 1) - 1 ≤
              FloatSpec.Core.Raux.mag beta y := by
          simpa using hln
        exact hplus (FloatSpec.Core.Raux.mag beta x - 1)
          (FloatSpec.Core.Raux.mag beta y) hcond
      · exact hx_fmt
      · exact hy_fmt

/-- Coq: `round_round_minus_aux1`.

If the subtrahend is well below `x`, but still high enough relative to the
difference's canonical exponent, the subtraction is exact in `fexp2`. -/
theorem round_round_minus_aux1 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_plus_hyp fexp1 fexp2)
    (x y : ℝ)
    (hy_pos : 0 < y)
    (hyx : y < x)
    (_hln :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 2)
    (hln' :
      fexp1 (FloatSpec.Core.Raux.mag beta (x - y)) - 1 ≤
        FloatSpec.Core.Raux.mag beta y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x - y) := by
  rcases hexp with ⟨_, _, hsame, hmag⟩
  have hmxy_le_mx :
      FloatSpec.Core.Raux.mag beta (x - y) ≤
        FloatSpec.Core.Raux.mag beta x := by
    have htrip := FloatSpec.Core.Raux.mag_minus
      (beta := beta) (x := x) (y := y) hβ hy_pos hyx
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  exact round_round_minus_aux0_aux (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (hβ := hβ)
    (hlnx := hmag (FloatSpec.Core.Raux.mag beta (x - y))
      (FloatSpec.Core.Raux.mag beta x) (by omega))
    (hlny := hsame (FloatSpec.Core.Raux.mag beta (x - y))
      (FloatSpec.Core.Raux.mag beta y) hln')
    (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)

/-- Coq: `round_round_minus_aux2_aux`.

The upward concrete rounding of `x - y` stays within `y` of the exact
difference when `x` is already generic and `0 < y < x`. -/
theorem round_round_minus_aux2_aux (fexp : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
    (hβ : 1 < beta)
    (x y : ℝ)
    (hy_pos : 0 < y)
    (_hyx : y < x)
    (_hly :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp (FloatSpec.Core.Raux.mag beta x) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp x)
    (_hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp y) :
    FloatSpec.Core.Generic_fmt.roundR beta fexp
        FloatSpec.Core.Generic_fmt.rnd_ceil (x - y) - (x - y) ≤ y := by
  have hle : x - y ≤ x := by linarith [le_of_lt hy_pos]
  have hround_le_x :
      FloatSpec.Core.Generic_fmt.roundR beta fexp
          FloatSpec.Core.Generic_fmt.rnd_ceil (x - y) ≤ x :=
    FloatSpec.Core.Generic_fmt.roundR_le_generic
      (beta := beta) (fexp := fexp)
      (rnd := FloatSpec.Core.Generic_fmt.rnd_ceil)
      (x := x - y) (y := x) hβ hx_fmt hle
  linarith

/-- Coq: `round_round_minus_aux2`.

If the subtrahend is at least two exponent places below both `x` and `x-y`,
then `round_round_gt_mid` applies to the positive difference. -/
theorem round_round_minus_aux2 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hexp : round_round_plus_hyp fexp1 fexp2)
    (x y : ℝ)
    (hy_pos : 0 < y)
    (hyx : y < x)
    (hly :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 2)
    (hly' :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (x - y)) - 2)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) := by
  classical
  rcases hexp with ⟨_, _, _, hmag⟩
  set z : ℝ := x - y with hz
  set mz : Int := FloatSpec.Core.Raux.mag beta z with hmz
  set e1 : Int := fexp1 mz with he1
  have hz_pos : 0 < z := by
    simpa [z, hz] using sub_pos.mpr hyx
  have hz_ne : z ≠ 0 := ne_of_gt hz_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hceil_err :
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          FloatSpec.Core.Generic_fmt.rnd_ceil z - z ≤ y := by
    simpa [z, hz] using
      round_round_minus_aux2_aux (beta := beta) (fexp := fexp1)
        (hβ := hβ) (x := x) (y := y) (hy_pos := hy_pos)
        (_hyx := hyx) (_hly := by omega) (hx_fmt := hx_fmt)
        (_hy_fmt := hy_fmt)
  have hf21 :
      fexp2 (FloatSpec.Core.Raux.mag beta z) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta z) := by
    simpa [mz, hmz, e1, he1] using
      hmag mz mz (by omega)
  have hf1_y_le_my :
      fexp1 (FloatSpec.Core.Raux.mag beta y) ≤
        FloatSpec.Core.Raux.mag beta y := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp1) y
    have hlt :
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 y <
          FloatSpec.Core.Raux.mag beta y := by
      simpa [wp, PostCond.noThrow, Id.run, pure] using
        htrip ⟨hβ, hy_ne, hy_fmt⟩
    simpa [FloatSpec.Core.Generic_fmt.cexp] using le_of_lt hlt
  have hf1_le_mz :
      fexp1 (FloatSpec.Core.Raux.mag beta z) ≤
        FloatSpec.Core.Raux.mag beta z := by
    by_contra hnot
    have hmz_lt_e1 : mz < e1 := by
      exact lt_of_not_ge (by simpa [mz, hmz, e1, he1] using hnot)
    have hsmall : mz ≤ fexp1 mz := le_of_lt hmz_lt_e1
    have hconst :=
      (FloatSpec.Core.Generic_fmt.Valid_exp.valid_exp
        (beta := beta) (fexp := fexp1) mz).right hsmall |>.right
    have hfy_eq : fexp1 (FloatSpec.Core.Raux.mag beta y) = e1 := by
      have hle : FloatSpec.Core.Raux.mag beta y ≤ fexp1 mz := by
        have hle' : FloatSpec.Core.Raux.mag beta y ≤ e1 - 2 := by
          simpa [mz, hmz, e1, he1, z, hz] using hly'
        omega
      simpa [e1, he1] using hconst (FloatSpec.Core.Raux.mag beta y) hle
    have hmy_lt_e1 : FloatSpec.Core.Raux.mag beta y < e1 := by
      have hle : FloatSpec.Core.Raux.mag beta y ≤ e1 - 2 := by
        simpa [mz, hmz, e1, he1, z, hz] using hly'
      omega
    omega
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hb2ℤ : (2 : Int) ≤ beta := by omega
  have hb2R : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hb2ℤ
  have hpow_two_nonneg : 0 ≤ (beta : ℝ) ^ (e1 - 2) :=
    le_of_lt (zpow_pos hbposR (e1 - 2))
  have hy_lt_mag :
      y < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := y) hβ hy_ne
    simpa [FloatSpec.Core.Raux.abs_val, abs_of_pos hy_pos, wp,
      PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hy_lt_e1_sub2 : y < (beta : ℝ) ^ (e1 - 2) := by
    have hpow_le :
        (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) ≤
          (beta : ℝ) ^ (e1 - 2) := by
      have htrip := FloatSpec.Core.Raux.bpow_le (beta := beta)
        (e1 := FloatSpec.Core.Raux.mag beta y) (e2 := e1 - 2) hβ
        (by simpa [mz, hmz, e1, he1, z, hz] using hly')
      simpa [FloatSpec.Core.Raux.bpow_le_check, wp, PostCond.noThrow, Id.run,
        pure] using htrip True.intro
    exact lt_of_lt_of_le hy_lt_mag hpow_le
  have hulp1 :
      ulp beta fexp1 z = (beta : ℝ) ^ e1 := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := z) hz_ne
    simpa [wp, PostCond.noThrow, Id.run, pure, e1, he1, mz, hmz,
      FloatSpec.Core.Generic_fmt.cexp] using htrip True.intro
  have hpow_two_to_half :
      (beta : ℝ) ^ (e1 - 2) ≤
        (1 / 2 : ℝ) * ((beta : ℝ) ^ e1) := by
    have hbeta_sq_ge_two : (2 : ℝ) ≤ (beta : ℝ) ^ (2 : Int) := by
      norm_num [zpow_ofNat]
      nlinarith
    have hneg_two_le_half :
        (beta : ℝ) ^ (-(2 : Int)) ≤ (1 / 2 : ℝ) := by
      have hinv_le :
          1 / ((beta : ℝ) ^ (2 : Int)) ≤ (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) hbeta_sq_ge_two
      simpa [one_div, zpow_neg] using hinv_le
    have hpow_cancel :
        (beta : ℝ) ^ (e1 - 2) =
          (beta : ℝ) ^ e1 * (beta : ℝ) ^ (-(2 : Int)) := by
      calc
        (beta : ℝ) ^ (e1 - 2)
            = (beta : ℝ) ^ (e1 + (-(2 : Int))) := by ring_nf
        _ = (beta : ℝ) ^ e1 * (beta : ℝ) ^ (-(2 : Int)) := by
              rw [zpow_add₀ hbne]
    rw [hpow_cancel]
    have hmul := mul_le_mul_of_nonneg_left hneg_two_le_half
      (le_of_lt (zpow_pos hbposR e1))
    nlinarith
  have hx_mid :
      midp' beta fexp1 z < z := by
    have hgap_half :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            FloatSpec.Core.Generic_fmt.rnd_ceil z - z <
          (1 / 2 : ℝ) * ulp beta fexp1 z :=
      lt_of_le_of_lt hceil_err
        (lt_of_lt_of_le hy_lt_e1_sub2 (by simpa [hulp1] using hpow_two_to_half))
    unfold midp'
    linarith
  apply round_round_gt_mid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (x := z) hβ
  · exact hz_pos
  · simpa [z, hz] using hf21
  · simpa [z, hz] using hf1_le_mz
  · exact hx_mid
  · intro hfurther
    set e2 : Int := fexp2 mz with he2
    have hfurther' : e2 ≤ e1 - 1 := by
      simpa [e1, he1, e2, he2, mz, hmz] using hfurther
    have hulp2 :
        ulp beta fexp2 z = (beta : ℝ) ^ e2 := by
      have htrip := FloatSpec.Core.Ulp.ulp_neq_0
        (beta := beta) (fexp := fexp2) (x := z) hz_ne
      simpa [wp, PostCond.noThrow, Id.run, pure, e2, he2, mz, hmz,
        FloatSpec.Core.Generic_fmt.cexp] using htrip True.intro
    have hpow_e2_le :
        (beta : ℝ) ^ e2 ≤ (beta : ℝ) ^ (e1 - 1) := by
      have htrip := FloatSpec.Core.Raux.bpow_le (beta := beta)
        (e1 := e2) (e2 := e1 - 1) hβ hfurther'
      simpa [FloatSpec.Core.Raux.bpow_le_check, wp, PostCond.noThrow, Id.run,
        pure] using htrip True.intro
    have hpow_two_to_half_diff :
        (beta : ℝ) ^ (e1 - 2) ≤
          (1 / 2 : ℝ) * ((beta : ℝ) ^ e1 - (beta : ℝ) ^ e2) := by
      have hpow_e_split :
          (beta : ℝ) ^ e1 =
            (beta : ℝ) ^ (e1 - 2) * (beta : ℝ) ^ (2 : Int) := by
        calc
          (beta : ℝ) ^ e1 = (beta : ℝ) ^ ((e1 - 2) + 2) := by ring_nf
          _ = (beta : ℝ) ^ (e1 - 2) * (beta : ℝ) ^ (2 : Int) := by
                rw [zpow_add₀ hbne]
      have hpow_em1_split :
          (beta : ℝ) ^ (e1 - 1) =
            (beta : ℝ) ^ (e1 - 2) * (beta : ℝ) := by
        calc
          (beta : ℝ) ^ (e1 - 1) = (beta : ℝ) ^ ((e1 - 2) + 1) := by ring_nf
          _ = (beta : ℝ) ^ (e1 - 2) * (beta : ℝ) ^ (1 : Int) := by
                rw [zpow_add₀ hbne]
          _ = (beta : ℝ) ^ (e1 - 2) * (beta : ℝ) := by simp
      have hfactor : (1 : ℝ) ≤ (1 / 2 : ℝ) *
          ((beta : ℝ) ^ (2 : Int) - (beta : ℝ)) := by
        norm_num [zpow_ofNat]
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hfactor hpow_two_nonneg
      have hbase :
          (beta : ℝ) ^ (e1 - 2) ≤
            (1 / 2 : ℝ) *
              ((beta : ℝ) ^ e1 - (beta : ℝ) ^ (e1 - 1)) := by
        rw [hpow_e_split, hpow_em1_split]
        nlinarith
      have hsub :
          (beta : ℝ) ^ e1 - (beta : ℝ) ^ (e1 - 1) ≤
            (beta : ℝ) ^ e1 - (beta : ℝ) ^ e2 := by
        linarith
      have hhalf := mul_le_mul_of_nonneg_left hsub
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
      exact le_trans hbase hhalf
    have hgap_further :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            FloatSpec.Core.Generic_fmt.rnd_ceil z - z <
          (1 / 2 : ℝ) * (ulp beta fexp1 z - ulp beta fexp2 z) :=
      lt_of_le_of_lt hceil_err
        (lt_of_lt_of_le hy_lt_e1_sub2
          (by simpa [hulp1, hulp2] using hpow_two_to_half_diff))
    unfold midp'
    linarith

/-- Coq: `round_round_minus_aux3`.

Combines the exact-difference and midpoint cases for positive `y ≤ x`. -/
theorem round_round_minus_aux3 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hexp : round_round_plus_hyp fexp1 fexp2)
    (x y : ℝ)
    (hy_pos : 0 < y)
    (hyx : y ≤ x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) := by
  classical
  by_cases hxy_eq : y = x
  · have hdiff : x - y = 0 := by linarith
    have hfmt0 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (0 : ℝ) :=
      FloatSpec.Core.Generic_fmt.generic_format_0_run
        (beta := beta) (fexp := fexp2)
    have hinner :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) (x - y) =
          x - y := by
      rw [hdiff]
      exact FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
        (x := 0) hβ hfmt0
    simpa [round_round_eq, hinner]
  · have hyx_lt : y < x := lt_of_le_of_ne hyx hxy_eq
    by_cases hly :
        FloatSpec.Core.Raux.mag beta y ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) - 2
    · by_cases hly' :
        FloatSpec.Core.Raux.mag beta y ≤
          fexp1 (FloatSpec.Core.Raux.mag beta (x - y)) - 2
      · exact round_round_minus_aux2 (beta := beta)
          (fexp1 := fexp1) (fexp2 := fexp2)
          (choice1 := choice1) (choice2 := choice2)
          (hβ := hβ) (hexp := hexp) (x := x) (y := y)
          (hy_pos := hy_pos) (hyx := hyx_lt)
          (hly := hly) (hly' := hly')
          (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)
      · have hlarge' :
          fexp1 (FloatSpec.Core.Raux.mag beta (x - y)) - 1 ≤
            FloatSpec.Core.Raux.mag beta y := by
          omega
        have hfmt2 :
            FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x - y) :=
          round_round_minus_aux1 (beta := beta)
            (fexp1 := fexp1) (fexp2 := fexp2)
            (hβ := hβ) (hexp := hexp) (x := x) (y := y)
            (hy_pos := hy_pos) (hyx := hyx_lt)
            (_hln := hly) (hln' := hlarge')
            (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)
        have hinner :
            FloatSpec.Core.Generic_fmt.roundR beta fexp2
                (FloatSpec.Core.Generic_fmt.Znearest choice2) (x - y) =
              x - y :=
          FloatSpec.Core.Generic_fmt.roundR_generic
            (beta := beta) (fexp := fexp2)
            (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
            (x := x - y) hβ hfmt2
        simpa [round_round_eq, hinner]
    · have hlarge :
          fexp1 (FloatSpec.Core.Raux.mag beta x) - 1 ≤
            FloatSpec.Core.Raux.mag beta y := by
        omega
      have hfmt2 :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x - y) :=
        round_round_minus_aux0 (beta := beta)
          (fexp1 := fexp1) (fexp2 := fexp2)
          (hβ := hβ) (hexp := hexp) (x := x) (y := y)
          (hy_pos := hy_pos) (hyx := hyx_lt) (hln := hlarge)
          (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)
      have hinner :
          FloatSpec.Core.Generic_fmt.roundR beta fexp2
              (FloatSpec.Core.Generic_fmt.Znearest choice2) (x - y) =
            x - y :=
        FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := beta) (fexp := fexp2)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
          (x := x - y) hβ hfmt2
      simpa [round_round_eq, hinner]

/-- Rounding-to-nearest double-rounding commutes with negation, with the
Flocq `round_N_opp` transformation on tie-breaking choices. -/
private theorem round_round_eq_opp (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (x : ℝ)
    (h :
      round_round_eq beta fexp1 fexp2
        (fun t => ! choice1 (-(t + 1)))
        (fun t => ! choice2 (-(t + 1))) x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (-x) := by
  unfold round_round_eq at h ⊢
  rw [FloatSpec.Core.Generic_fmt.round_N_opp
    (beta := beta) (fexp := fexp2) (choice := choice2) (x := x)]
  rw [FloatSpec.Core.Generic_fmt.round_N_opp
    (beta := beta) (fexp := fexp1) (choice := choice1)
    (x :=
      FloatSpec.Core.Generic_fmt.roundR beta fexp2
        (FloatSpec.Core.Generic_fmt.Znearest
          (fun t => ! choice2 (-(t + 1)))) x)]
  rw [FloatSpec.Core.Generic_fmt.round_N_opp
    (beta := beta) (fexp := fexp1) (choice := choice1) (x := x)]
  exact congrArg Neg.neg h

/-- Coq: `round_round_minus_aux`.

Nonnegative-input subtraction wrapper. The reversed-order case is reduced to
the positive subtraction theorem by `round_N_opp`, which also transforms the
nearest tie-breaking choices exactly as in Flocq. -/
theorem round_round_minus_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hexp : round_round_plus_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hy_nonneg : 0 ≤ y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) := by
  classical
  let include_format :
      ∀ z : ℝ,
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 z →
          FloatSpec.Core.Generic_fmt.generic_format beta fexp2 z := by
    intro z hz_fmt
    exact FloatSpec.Core.Generic_fmt.generic_inclusion_mag
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2) (x := z)
      hβ
      (by
        intro _hz
        exact hexp.2.2.2 (FloatSpec.Core.Raux.mag beta z)
          (FloatSpec.Core.Raux.mag beta z) (by omega))
      hz_fmt
  by_cases hx0 : x = 0
  · have hy_fmt2 : FloatSpec.Core.Generic_fmt.generic_format beta fexp2 y :=
      include_format y hy_fmt
    have hneg_trip := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := fexp2) (x := y)
    have hy_neg_fmt2 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (-y) := by
      simpa [wp, PostCond.noThrow, Id.run, pure] using
        hneg_trip hy_fmt2
    have hinner :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) (x - y) =
          x - y := by
      exact FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
        (x := x - y) hβ (by simpa [hx0] using hy_neg_fmt2)
    simpa [round_round_eq, hinner]
  by_cases hy0 : y = 0
  · have hx_fmt2 : FloatSpec.Core.Generic_fmt.generic_format beta fexp2 x :=
      include_format x hx_fmt
    have hinner :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) (x - y) =
          x - y := by
      exact FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
        (x := x - y) hβ (by simpa [hy0] using hx_fmt2)
    simpa [round_round_eq, hinner]
  have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
  have hy_pos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hy0)
  by_cases hxy : x < y
  · have hcore :
        round_round_eq beta fexp1 fexp2
          (fun t => ! choice1 (-(t + 1)))
          (fun t => ! choice2 (-(t + 1))) (y - x) :=
      round_round_minus_aux3 (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := fun t => ! choice1 (-(t + 1)))
        (choice2 := fun t => ! choice2 (-(t + 1)))
        (hβ := hβ) (hexp := hexp)
        (x := y) (y := x)
        (hy_pos := hx_pos) (hyx := le_of_lt hxy)
        (hx_fmt := hy_fmt) (hy_fmt := hx_fmt)
    have hneg := round_round_eq_opp (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2)
      (x := y - x) hcore
    have hsub : x - y = -(y - x) := by ring
    rw [hsub]
    exact hneg
  · exact round_round_minus_aux3 (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2)
      (hβ := hβ) (hexp := hexp)
      (x := x) (y := y)
      (hy_pos := hy_pos) (hyx := le_of_not_gt hxy)
      (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)

/-- Coq: `round_round_plus`. -/
theorem round_round_plus (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hexp : round_round_plus_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) := by
  classical
  by_cases hx_neg : x < 0
  · by_cases hy_neg : y < 0
    · have hx_opp_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-x) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := fexp1) (x := x)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hx_fmt
      have hy_opp_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-y) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := fexp1) (x := y)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hy_fmt
      have hx_opp_nonneg : 0 ≤ -x := by linarith
      have hy_opp_nonneg : 0 ≤ -y := by linarith
      have hcore :
          round_round_eq beta fexp1 fexp2
            (fun t => ! choice1 (-(t + 1)))
            (fun t => ! choice2 (-(t + 1))) ((-x) + (-y)) :=
        round_round_plus_aux (beta := beta)
          (fexp1 := fexp1) (fexp2 := fexp2)
          (choice1 := fun t => ! choice1 (-(t + 1)))
          (choice2 := fun t => ! choice2 (-(t + 1)))
          (hβ := hβ) (hexp := hexp)
          (x := -x) (y := -y)
          (hx_nonneg := hx_opp_nonneg) (hy_nonneg := hy_opp_nonneg)
          (hx_fmt := hx_opp_fmt) (hy_fmt := hy_opp_fmt)
      have hneg := round_round_eq_opp (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        (x := (-x) + (-y)) hcore
      have hsum : x + y = -((-x) + (-y)) := by ring
      rw [hsum]
      exact hneg
    · have hx_opp_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-x) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := fexp1) (x := x)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hx_fmt
      have hx_opp_nonneg : 0 ≤ -x := by linarith
      have hy_nonneg : 0 ≤ y := le_of_not_gt hy_neg
      have hcore := round_round_minus_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        (hβ := hβ) (hexp := hexp)
        (x := y) (y := -x)
        (hx_nonneg := hy_nonneg) (hy_nonneg := hx_opp_nonneg)
        (hx_fmt := hy_fmt) (hy_fmt := hx_opp_fmt)
      have hsum : x + y = y - (-x) := by ring
      rw [hsum]
      exact hcore
  · by_cases hy_neg : y < 0
    · have hy_opp_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-y) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := fexp1) (x := y)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hy_fmt
      have hx_nonneg : 0 ≤ x := le_of_not_gt hx_neg
      have hy_opp_nonneg : 0 ≤ -y := by linarith
      have hcore := round_round_minus_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        (hβ := hβ) (hexp := hexp)
        (x := x) (y := -y)
        (hx_nonneg := hx_nonneg) (hy_nonneg := hy_opp_nonneg)
        (hx_fmt := hx_fmt) (hy_fmt := hy_opp_fmt)
      have hsum : x + y = x - (-y) := by ring
      rw [hsum]
      exact hcore
    · exact round_round_plus_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        (hβ := hβ) (hexp := hexp)
        (x := x) (y := y)
        (hx_nonneg := le_of_not_gt hx_neg)
        (hy_nonneg := le_of_not_gt hy_neg)
        (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)

/-- Coq: `round_round_minus`. -/
theorem round_round_minus (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hexp : round_round_plus_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) := by
  have hy_opp_fmt :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-y) := by
    have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := fexp1) (x := y)
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hy_fmt
  have hplus := round_round_plus (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ) (hexp := hexp)
    (x := x) (y := -y)
    (hx_fmt := hx_fmt) (hy_fmt := hy_opp_fmt)
  simpa [sub_eq_add_neg] using hplus

/-- Coq: `FLX_round_round_plus_hyp`. -/
theorem FLX_round_round_plus_hyp (prec prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (hprec : 2 * prec + 1 ≤ prec') :
    round_round_plus_hyp
      (FloatSpec.Core.FLX.FLX_exp prec)
      (FloatSpec.Core.FLX.FLX_exp prec') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  unfold round_round_plus_hyp FloatSpec.Core.FLX.FLX_exp
  constructor
  · intro ex ey _
    grind
  constructor
  · intro ex ey _
    grind
  constructor
  · intro ex ey _
    grind
  · intro ex ey _
    grind

/-- Coq: `round_round_plus_FLX`. -/
theorem round_round_plus_FLX (prec prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hprec : 2 * prec + 1 ≤ prec')
    (x y : ℝ)
    (hx : FloatSpec.Core.FLX.FLX_format prec beta x)
    (hy : FloatSpec.Core.FLX.FLX_format prec beta y) :
    round_round_eq beta
      (FloatSpec.Core.FLX.FLX_exp prec)
      (FloatSpec.Core.FLX.FLX_exp prec')
      choice1 choice2 (x + y) := by
  exact round_round_plus (beta := beta)
    (fexp1 := FloatSpec.Core.FLX.FLX_exp prec)
    (fexp2 := FloatSpec.Core.FLX.FLX_exp prec')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ)
    (hexp := FLX_round_round_plus_hyp
      (prec := prec) (prec' := prec') hprec)
    (x := x) (y := y)
    (hx_fmt := by simpa [FloatSpec.Core.FLX.FLX_format] using hx)
    (hy_fmt := by simpa [FloatSpec.Core.FLX.FLX_format] using hy)

/-- Coq: `round_round_minus_FLX`. -/
theorem round_round_minus_FLX (prec prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hprec : 2 * prec + 1 ≤ prec')
    (x y : ℝ)
    (hx : FloatSpec.Core.FLX.FLX_format prec beta x)
    (hy : FloatSpec.Core.FLX.FLX_format prec beta y) :
    round_round_eq beta
      (FloatSpec.Core.FLX.FLX_exp prec)
      (FloatSpec.Core.FLX.FLX_exp prec')
      choice1 choice2 (x - y) := by
  exact round_round_minus (beta := beta)
    (fexp1 := FloatSpec.Core.FLX.FLX_exp prec)
    (fexp2 := FloatSpec.Core.FLX.FLX_exp prec')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ)
    (hexp := FLX_round_round_plus_hyp
      (prec := prec) (prec' := prec') hprec)
    (x := x) (y := y)
    (hx_fmt := by simpa [FloatSpec.Core.FLX.FLX_format] using hx)
    (hy_fmt := by simpa [FloatSpec.Core.FLX.FLX_format] using hy)

/-- Coq: `FLT_round_round_plus_hyp`. -/
theorem FLT_round_round_plus_hyp (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (hemin : emin' ≤ emin)
    (hprec : 2 * prec + 1 ≤ prec') :
    round_round_plus_hyp
      (FloatSpec.Core.FLT.FLT_exp prec emin)
      (FloatSpec.Core.FLT.FLT_exp prec' emin') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  unfold round_round_plus_hyp FloatSpec.Core.FLT.FLT_exp
  constructor
  · intro ex ey h
    grind
  constructor
  · intro ex ey h
    grind
  constructor
  · intro ex ey h
    grind
  · intro ex ey h
    grind

/-- Coq: `round_round_plus_FLT`. -/
theorem round_round_plus_FLT (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hemin : emin' ≤ emin)
    (hprec : 2 * prec + 1 ≤ prec')
    (x y : ℝ)
    (hx : FloatSpec.Core.FLT.FLT_format prec emin beta x)
    (hy : FloatSpec.Core.FLT.FLT_format prec emin beta y) :
    round_round_eq beta
      (FloatSpec.Core.FLT.FLT_exp prec emin)
      (FloatSpec.Core.FLT.FLT_exp prec' emin')
      choice1 choice2 (x + y) := by
  exact round_round_plus (beta := beta)
    (fexp1 := FloatSpec.Core.FLT.FLT_exp prec emin)
    (fexp2 := FloatSpec.Core.FLT.FLT_exp prec' emin')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ)
    (hexp := FLT_round_round_plus_hyp
      (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
      hemin hprec)
    (x := x) (y := y)
    (hx_fmt := by simpa [FloatSpec.Core.FLT.FLT_format] using hx)
    (hy_fmt := by simpa [FloatSpec.Core.FLT.FLT_format] using hy)

/-- Coq: `round_round_minus_FLT`. -/
theorem round_round_minus_FLT (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hemin : emin' ≤ emin)
    (hprec : 2 * prec + 1 ≤ prec')
    (x y : ℝ)
    (hx : FloatSpec.Core.FLT.FLT_format prec emin beta x)
    (hy : FloatSpec.Core.FLT.FLT_format prec emin beta y) :
    round_round_eq beta
      (FloatSpec.Core.FLT.FLT_exp prec emin)
      (FloatSpec.Core.FLT.FLT_exp prec' emin')
      choice1 choice2 (x - y) := by
  exact round_round_minus (beta := beta)
    (fexp1 := FloatSpec.Core.FLT.FLT_exp prec emin)
    (fexp2 := FloatSpec.Core.FLT.FLT_exp prec' emin')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ)
    (hexp := FLT_round_round_plus_hyp
      (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
      hemin hprec)
    (x := x) (y := y)
    (hx_fmt := by simpa [FloatSpec.Core.FLT.FLT_format] using hx)
    (hy_fmt := by simpa [FloatSpec.Core.FLT.FLT_format] using hy)

/-- Coq: `FTZ_round_round_plus_hyp`. -/
theorem FTZ_round_round_plus_hyp (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (hemin : emin' + prec' ≤ emin + 1)
    (hprec : 2 * prec + 1 ≤ prec') :
    round_round_plus_hyp
      (FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (FloatSpec.Core.FTZ.FTZ_exp prec' emin') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  unfold round_round_plus_hyp FloatSpec.Core.FTZ.FTZ_exp
  constructor
  · intro ex ey h
    split_ifs at h ⊢ <;> omega
  constructor
  · intro ex ey h
    split_ifs at h ⊢ <;> omega
  constructor
  · intro ex ey h
    split_ifs at h ⊢ <;> omega
  · intro ex ey h
    split_ifs at h ⊢ <;> omega

/-- Coq: `round_round_plus_FTZ`. -/
theorem round_round_plus_FTZ (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hemin : emin' + prec' ≤ emin + 1)
    (hprec : 2 * prec + 1 ≤ prec')
    (x y : ℝ)
    (hx : FloatSpec.Core.FTZ.FTZ_format prec emin beta x)
    (hy : FloatSpec.Core.FTZ.FTZ_format prec emin beta y) :
    round_round_eq beta
      (FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (FloatSpec.Core.FTZ.FTZ_exp prec' emin')
      choice1 choice2 (x + y) := by
  exact round_round_plus (beta := beta)
    (fexp1 := FloatSpec.Core.FTZ.FTZ_exp prec emin)
    (fexp2 := FloatSpec.Core.FTZ.FTZ_exp prec' emin')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ)
    (hexp := FTZ_round_round_plus_hyp
      (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
      hemin hprec)
    (x := x) (y := y)
    (hx_fmt := by simpa [FloatSpec.Core.FTZ.FTZ_format] using hx)
    (hy_fmt := by simpa [FloatSpec.Core.FTZ.FTZ_format] using hy)

/-- Coq: `round_round_minus_FTZ`. -/
theorem round_round_minus_FTZ (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 1 < beta)
    (hemin : emin' + prec' ≤ emin + 1)
    (hprec : 2 * prec + 1 ≤ prec')
    (x y : ℝ)
    (hx : FloatSpec.Core.FTZ.FTZ_format prec emin beta x)
    (hy : FloatSpec.Core.FTZ.FTZ_format prec emin beta y) :
    round_round_eq beta
      (FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (FloatSpec.Core.FTZ.FTZ_exp prec' emin')
      choice1 choice2 (x - y) := by
  exact round_round_minus (beta := beta)
    (fexp1 := FloatSpec.Core.FTZ.FTZ_exp prec emin)
    (fexp2 := FloatSpec.Core.FTZ.FTZ_exp prec' emin')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ)
    (hexp := FTZ_round_round_plus_hyp
      (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
      hemin hprec)
    (x := x) (y := y)
    (hx_fmt := by simpa [FloatSpec.Core.FTZ.FTZ_format] using hx)
    (hy_fmt := by simpa [FloatSpec.Core.FTZ.FTZ_format] using hy)

/-- Coq: `round_round_plus_radix_ge_3_hyp`. -/
def round_round_plus_radix_ge_3_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex ey, fexp1 (ex + 1) ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 (ex - 1) + 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 ex ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey)

/-- Coq: `round_round_plus_radix_ge_3_aux0`. -/
theorem round_round_plus_radix_ge_3_aux0 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
    (x y : ℝ)
    (hy_pos : 0 < y)
    (hyx : y ≤ x)
    (hln :
      fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        FloatSpec.Core.Raux.mag beta y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x + y) := by
  classical
  rcases hexp with ⟨_, hsmall, hsame, hmag⟩
  have hx_pos : 0 < x := lt_of_lt_of_le hy_pos hyx
  have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
  by_cases hle_sep :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x)
  · have hsum_mag :
        FloatSpec.Core.Raux.mag beta (x + y) =
          FloatSpec.Core.Raux.mag beta x :=
      mag_plus_separated (beta := beta) (fexp := fexp1)
        (x := x) (y := y) hβ hx_pos hy_nonneg hx_fmt hle_sep
    apply round_round_plus_aux0_aux (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y) hβ
    · rw [hsum_mag]
      exact hmag (FloatSpec.Core.Raux.mag beta x)
        (FloatSpec.Core.Raux.mag beta x) (by omega)
    · rw [hsum_mag]
      exact hsame (FloatSpec.Core.Raux.mag beta x)
        (FloatSpec.Core.Raux.mag beta y) hln
    · exact hx_fmt
    · exact hy_fmt
  · have hgt_sep :
        fexp1 (FloatSpec.Core.Raux.mag beta x) <
          FloatSpec.Core.Raux.mag beta y := not_le.mp hle_sep
    have hmag_y_le_x :
        FloatSpec.Core.Raux.mag beta y ≤
          FloatSpec.Core.Raux.mag beta x := by
      have hxy_abs : |y| ≤ |x| := by
        simpa [abs_of_nonneg hy_nonneg, abs_of_nonneg (le_of_lt hx_pos)]
          using hyx
      have htrip := FloatSpec.Core.Raux.mag_le (beta := beta)
        (x := y) (y := x) hβ (ne_of_gt hy_pos) hxy_abs
      simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
    apply round_round_plus_aux0_aux (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y) hβ
    · rcases mag_plus_disj (beta := beta) (x := x) (y := y)
        hβ hy_pos hyx with hsum_mag | hsum_mag
      · rw [hsum_mag]
        exact hmag (FloatSpec.Core.Raux.mag beta x)
          (FloatSpec.Core.Raux.mag beta x) (by omega)
      · rw [hsum_mag]
        exact hsmall (FloatSpec.Core.Raux.mag beta x + 1)
          (FloatSpec.Core.Raux.mag beta x) (by
            have hfx_add_one_le_y :
                fexp1 (FloatSpec.Core.Raux.mag beta x) + 1 ≤
                  FloatSpec.Core.Raux.mag beta y :=
              Int.add_one_le_iff.mpr hgt_sep
            have hfx_add_one_le_x :
                fexp1 (FloatSpec.Core.Raux.mag beta x) + 1 ≤
                  FloatSpec.Core.Raux.mag beta x :=
              le_trans hfx_add_one_le_y hmag_y_le_x
            simpa using hfx_add_one_le_x)
    · rcases mag_plus_disj (beta := beta) (x := x) (y := y)
        hβ hy_pos hyx with hsum_mag | hsum_mag
      · rw [hsum_mag]
        exact hsame (FloatSpec.Core.Raux.mag beta x)
          (FloatSpec.Core.Raux.mag beta y) hln
      · rw [hsum_mag]
        exact hsmall (FloatSpec.Core.Raux.mag beta x + 1)
          (FloatSpec.Core.Raux.mag beta y) (by
            have hfx_add_one_le_y :
                fexp1 (FloatSpec.Core.Raux.mag beta x) + 1 ≤
                  FloatSpec.Core.Raux.mag beta y :=
              Int.add_one_le_iff.mpr hgt_sep
            simpa using hfx_add_one_le_y)
    · exact hx_fmt
    · exact hy_fmt

/-- Coq: `round_round_plus_radix_ge_3_aux1`. -/
theorem round_round_plus_radix_ge_3_aux1 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_pos : 0 < x)
    (hy_pos : 0 < y)
    (hln :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) := by
  classical
  let e : Int := fexp1 (FloatSpec.Core.Raux.mag beta x)
  have hβ1 : 1 < beta := by omega
  have hsum_pos : 0 < x + y := add_pos hx_pos hy_pos
  have hsum_ne : x + y ≠ 0 := ne_of_gt hsum_pos
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hsum_mag :
      FloatSpec.Core.Raux.mag beta (x + y) =
        FloatSpec.Core.Raux.mag beta x := by
    apply mag_plus_separated (beta := beta) (fexp := fexp1)
      (x := x) (y := y) hβ1 hx_pos (le_of_lt hy_pos) hx_fmt
    omega
  rcases hexp with ⟨_, _, _, hmag⟩
  have hf21 :
      fexp2 (FloatSpec.Core.Raux.mag beta (x + y)) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (x + y)) := by
    rw [hsum_mag]
    exact hmag (FloatSpec.Core.Raux.mag beta x)
      (FloatSpec.Core.Raux.mag beta x) (by omega)
  have hf1_le_mag :
      fexp1 (FloatSpec.Core.Raux.mag beta (x + y)) ≤
        FloatSpec.Core.Raux.mag beta (x + y) := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp1) x
    have hx_cexp_le :
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 x ≤
          FloatSpec.Core.Raux.mag beta x := by
      have hlt :
          FloatSpec.Core.Generic_fmt.cexp beta fexp1 x <
            FloatSpec.Core.Raux.mag beta x := by
        simpa [wp, PostCond.noThrow, Id.run, pure] using
          htrip ⟨hβ1, hx_ne, hx_fmt⟩
      exact le_of_lt hlt
    simpa [FloatSpec.Core.Generic_fmt.cexp, hsum_mag] using hx_cexp_le
  have hgap := round_round_plus_aux1_aux (beta := beta) (k := 1)
    (hk := by omega) (fexp := fexp1) (x := x) (y := y)
    (hβ := hβ1) (hx_pos := hx_pos) (hy_pos := hy_pos)
    (hln := hln) (hsum_mag := hsum_mag) (hx_fmt := hx_fmt)
  have hbposℤ : (0 : Int) < beta := by omega
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hpow_one_to_half :
      (beta : ℝ) ^ (e - 1) ≤
        (1 / 2 : ℝ) * ((beta : ℝ) ^ e) := by
    have hpow_cancel :
        (beta : ℝ) ^ (e - 1) =
          (beta : ℝ) ^ e * (beta : ℝ) ^ (-(1 : Int)) := by
      calc
        (beta : ℝ) ^ (e - 1)
            = (beta : ℝ) ^ (e + (-(1 : Int))) := by ring_nf
        _ = (beta : ℝ) ^ e * (beta : ℝ) ^ (-(1 : Int)) := by
              rw [zpow_add₀ hbne]
    have hinv_le_half :
        (beta : ℝ) ^ (-(1 : Int)) ≤ (1 / 2 : ℝ) := by
      have h2ℤ : (2 : Int) ≤ beta := by omega
      have h2R : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast h2ℤ
      have hinv : 1 / (beta : ℝ) ≤ (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) h2R
      simpa [zpow_neg, one_div] using hinv
    rw [hpow_cancel]
    have hmul := mul_le_mul_of_nonneg_left hinv_le_half
      (le_of_lt (zpow_pos hbposR e))
    calc
      (beta : ℝ) ^ e * (beta : ℝ) ^ (-(1 : Int))
          ≤ (beta : ℝ) ^ e * (1 / 2 : ℝ) := hmul
      _ = (1 / 2 : ℝ) * ((beta : ℝ) ^ e) := by ring
  have hpow_one_to_half_diff :
      (beta : ℝ) ^ (e - 1) ≤
        (1 / 2 : ℝ) * ((beta : ℝ) ^ e - (beta : ℝ) ^ (e - 1)) := by
    have hpow_e_split :
        (beta : ℝ) ^ e =
          (beta : ℝ) ^ (e - 1) * (beta : ℝ) := by
      calc
        (beta : ℝ) ^ e = (beta : ℝ) ^ ((e - 1) + 1) := by ring_nf
        _ = (beta : ℝ) ^ (e - 1) * (beta : ℝ) ^ (1 : Int) := by
              rw [zpow_add₀ hbne]
        _ = (beta : ℝ) ^ (e - 1) * (beta : ℝ) := by simp
    have hfactor : (1 : ℝ) ≤ (1 / 2 : ℝ) * ((beta : ℝ) - 1) := by
      have hβR : (3 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hβ
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hfactor
      (le_of_lt (zpow_pos hbposR (e - 1)))
    rw [hpow_e_split]
    nlinarith
  have hulp1 :
      ulp beta fexp1 (x + y) = (beta : ℝ) ^ e := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := x + y) hsum_ne
    simpa [e, hsum_mag, FloatSpec.Core.Generic_fmt.cexp, wp,
      PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hx_mid :
      x + y < midp beta fexp1 (x + y) := by
    have hgap_half :
        (x + y) -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x + y) <
          (1 / 2 : ℝ) * ulp beta fexp1 (x + y) :=
      lt_of_lt_of_le hgap.2 (by simpa [hulp1, e] using hpow_one_to_half)
    unfold midp
    linarith
  apply round_round_lt_mid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (x := x + y) hβ1
  · exact hsum_pos
  · exact hf21
  · exact hf1_le_mag
  · exact hx_mid
  · intro hfurther
    let e2 : Int := fexp2 (FloatSpec.Core.Raux.mag beta (x + y))
    have hulp2 :
        ulp beta fexp2 (x + y) = (beta : ℝ) ^ e2 := by
      have htrip := FloatSpec.Core.Ulp.ulp_neq_0
        (beta := beta) (fexp := fexp2) (x := x + y) hsum_ne
      simpa [e2, FloatSpec.Core.Generic_fmt.cexp, wp,
        PostCond.noThrow, Id.run, pure] using htrip True.intro
    have hpow_e2_le :
        (beta : ℝ) ^ e2 ≤ (beta : ℝ) ^ (e - 1) := by
      have htrip := FloatSpec.Core.Raux.bpow_le (beta := beta)
        (e1 := e2) (e2 := e - 1) hβ1
        (by simpa [e, e2, hsum_mag] using hfurther)
      simpa [FloatSpec.Core.Raux.bpow_le_check, wp, PostCond.noThrow, Id.run,
        pure] using htrip True.intro
    have hpow_to_diff :
        (beta : ℝ) ^ (e - 1) ≤
          (1 / 2 : ℝ) * ((beta : ℝ) ^ e - (beta : ℝ) ^ e2) := by
      have hsub :
          (beta : ℝ) ^ e - (beta : ℝ) ^ (e - 1) ≤
            (beta : ℝ) ^ e - (beta : ℝ) ^ e2 := by
        linarith
      have hhalf := mul_le_mul_of_nonneg_left hsub
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
      exact le_trans hpow_one_to_half_diff hhalf
    have hgap_further :
        (x + y) -
            FloatSpec.Core.Generic_fmt.roundR beta fexp1
              FloatSpec.Core.Generic_fmt.rnd_floor (x + y) <
          (1 / 2 : ℝ) * (ulp beta fexp1 (x + y) - ulp beta fexp2 (x + y)) := by
      exact lt_of_lt_of_le hgap.2 (by
        simpa [hulp1, hulp2, e] using hpow_to_diff)
    unfold midp
    linarith

/-- Coq: `round_round_plus_radix_ge_3_aux2`. -/
theorem round_round_plus_radix_ge_3_aux2 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
    (x y : ℝ)
    (hy_pos : 0 < y)
    (hyx : y ≤ x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) := by
  classical
  have hβ1 : 1 < beta := by omega
  have hx_pos : 0 < x := lt_of_lt_of_le hy_pos hyx
  by_cases hsmall :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 1
  · exact round_round_plus_radix_ge_3_aux1 (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2)
      (hβ := hβ) (hexp := hexp) (x := x) (y := y)
      (hx_pos := hx_pos) (hy_pos := hy_pos) (hln := hsmall)
      (hx_fmt := hx_fmt)
  · have hlarge :
        fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
          FloatSpec.Core.Raux.mag beta y := by
      omega
    have hsum_fmt :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x + y) :=
      round_round_plus_radix_ge_3_aux0 (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (hβ := hβ1) (hexp := hexp) (x := x) (y := y)
        (hy_pos := hy_pos) (hyx := hyx) (hln := hlarge)
        (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)
    have hinner :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) (x + y) =
          x + y := by
      exact FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
        (x := x + y) hβ1 hsum_fmt
    simpa [round_round_eq, hinner]

/-- Coq: `round_round_plus_radix_ge_3_aux`. -/
theorem round_round_plus_radix_ge_3_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hy_nonneg : 0 ≤ y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) := by
  classical
  have hβ1 : 1 < beta := by omega
  rcases hexp with ⟨hplus, hsmall, hsame, hmag⟩
  by_cases hx0 : x = 0
  · have hy_fmt2 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 y :=
      FloatSpec.Core.Generic_fmt.generic_inclusion_mag
        (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
        (x := y) hβ1 (by
          intro hy_ne
          exact hmag (FloatSpec.Core.Raux.mag beta y)
            (FloatSpec.Core.Raux.mag beta y) (by omega)) hy_fmt
    have hinner :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) y = y :=
      FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
        (x := y) hβ1 hy_fmt2
    simpa [round_round_eq, hx0, hinner]
  · by_cases hy0 : y = 0
    · have hx_fmt2 :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp2 x :=
        FloatSpec.Core.Generic_fmt.generic_inclusion_mag
          (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2)
          (x := x) hβ1 (by
            intro hx_ne
            exact hmag (FloatSpec.Core.Raux.mag beta x)
              (FloatSpec.Core.Raux.mag beta x) (by omega)) hx_fmt
      have hinner :
          FloatSpec.Core.Generic_fmt.roundR beta fexp2
              (FloatSpec.Core.Generic_fmt.Znearest choice2) x = x :=
        FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := beta) (fexp := fexp2)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
          (x := x) hβ1 hx_fmt2
      simpa [round_round_eq, hy0, hinner]
    · have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
      have hy_pos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hy0)
      by_cases hxy : x < y
      · have hres := round_round_plus_radix_ge_3_aux2 (beta := beta)
          (fexp1 := fexp1) (fexp2 := fexp2)
          (choice1 := choice1) (choice2 := choice2) (hβ := hβ)
          (hexp := ⟨hplus, hsmall, hsame, hmag⟩)
          (x := y) (y := x) (hy_pos := hx_pos)
          (hyx := le_of_lt hxy) (hx_fmt := hy_fmt) (hy_fmt := hx_fmt)
        simpa [add_comm] using hres
      · exact round_round_plus_radix_ge_3_aux2 (beta := beta)
          (fexp1 := fexp1) (fexp2 := fexp2)
          (choice1 := choice1) (choice2 := choice2) (hβ := hβ)
          (hexp := ⟨hplus, hsmall, hsame, hmag⟩)
          (x := x) (y := y) (hy_pos := hy_pos)
          (hyx := le_of_not_gt hxy) (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)

/-- Coq: `round_round_minus_radix_ge_3_aux0`. -/
theorem round_round_minus_radix_ge_3_aux0 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
    (x y : ℝ)
    (hy_pos : 0 < y)
    (hyx : y < x)
    (hln :
      fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
        FloatSpec.Core.Raux.mag beta y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x - y) := by
  classical
  rcases hexp with ⟨hplus, _, hsame, hmag⟩
  have hx_pos : 0 < x := lt_trans hy_pos hyx
  have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hmxy_le_mx :
      FloatSpec.Core.Raux.mag beta (x - y) ≤
        FloatSpec.Core.Raux.mag beta x := by
    have htrip := FloatSpec.Core.Raux.mag_minus
      (beta := beta) (x := x) (y := y) hβ hy_pos hyx
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hmy_le_mx :
      FloatSpec.Core.Raux.mag beta y ≤
        FloatSpec.Core.Raux.mag beta x := by
    have hy_abs_le_x : |y| ≤ |x| := by
      simpa [abs_of_nonneg hy_nonneg, abs_of_nonneg hx_nonneg]
        using le_of_lt hyx
    have htrip := FloatSpec.Core.Raux.mag_le
      (beta := beta) (x := y) (y := x) hβ (ne_of_gt hy_pos) hy_abs_le_x
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
  by_cases hclose :
      FloatSpec.Core.Raux.mag beta x - 2 <
        FloatSpec.Core.Raux.mag beta y
  · have hcases :
        FloatSpec.Core.Raux.mag beta y = FloatSpec.Core.Raux.mag beta x ∨
          FloatSpec.Core.Raux.mag beta y =
            FloatSpec.Core.Raux.mag beta x - 1 := by
      omega
    rcases hcases with hmy_eq | hmy_eq
    · apply round_round_minus_aux0_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
        (hβ := hβ)
      · exact hmag (FloatSpec.Core.Raux.mag beta (x - y))
          (FloatSpec.Core.Raux.mag beta x) (by omega)
      · rw [hmy_eq]
        exact hmag (FloatSpec.Core.Raux.mag beta (x - y))
          (FloatSpec.Core.Raux.mag beta x) (by omega)
      · exact hx_fmt
      · exact hy_fmt
    · apply round_round_minus_aux0_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
        (hβ := hβ)
      · exact hmag (FloatSpec.Core.Raux.mag beta (x - y))
          (FloatSpec.Core.Raux.mag beta x) (by omega)
      · rw [hmy_eq]
        exact hmag (FloatSpec.Core.Raux.mag beta (x - y))
          (FloatSpec.Core.Raux.mag beta x - 1) (by omega)
      · exact hx_fmt
      · exact hy_fmt
  · have hmy_small :
        FloatSpec.Core.Raux.mag beta y ≤
          FloatSpec.Core.Raux.mag beta x - 2 := by
      omega
    have hmx_sub_one_le_mxy :
        FloatSpec.Core.Raux.mag beta x - 1 ≤
          FloatSpec.Core.Raux.mag beta (x - y) := by
      have htrip := FloatSpec.Core.Raux.mag_minus_lb
        (beta := beta) (x := x) (y := y) hβ hx_pos hy_pos hmy_small
      simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
    have hcases :
        FloatSpec.Core.Raux.mag beta (x - y) =
            FloatSpec.Core.Raux.mag beta x ∨
          FloatSpec.Core.Raux.mag beta (x - y) =
            FloatSpec.Core.Raux.mag beta x - 1 := by
      omega
    rcases hcases with hmxy_eq | hmxy_eq
    · apply round_round_minus_aux0_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
        (hβ := hβ)
      · rw [hmxy_eq]
        exact hmag (FloatSpec.Core.Raux.mag beta x)
          (FloatSpec.Core.Raux.mag beta x) (by omega)
      · rw [hmxy_eq]
        exact hsame (FloatSpec.Core.Raux.mag beta x)
          (FloatSpec.Core.Raux.mag beta y) hln
      · exact hx_fmt
      · exact hy_fmt
    · apply round_round_minus_aux0_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
        (hβ := hβ)
      · rw [hmxy_eq]
        have hcond :
            fexp1 (FloatSpec.Core.Raux.mag beta x - 1 + 1) ≤
              FloatSpec.Core.Raux.mag beta x := by
          have hcond' :
              fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
                FloatSpec.Core.Raux.mag beta x := le_trans hln hmy_le_mx
          simpa using hcond'
        exact hplus (FloatSpec.Core.Raux.mag beta x - 1)
          (FloatSpec.Core.Raux.mag beta x) hcond
      · rw [hmxy_eq]
        have hcond :
            fexp1 (FloatSpec.Core.Raux.mag beta x - 1 + 1) ≤
              FloatSpec.Core.Raux.mag beta y := by
          simpa using hln
        exact hplus (FloatSpec.Core.Raux.mag beta x - 1)
          (FloatSpec.Core.Raux.mag beta y) hcond
      · exact hx_fmt
      · exact hy_fmt

/-- Coq: `round_round_minus_radix_ge_3_aux1`. -/
theorem round_round_minus_radix_ge_3_aux1 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (hβ : 1 < beta)
    (hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
    (x y : ℝ)
    (hy_pos : 0 < y)
    (hyx : y < x)
    (_hln :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 1)
    (hln' :
      fexp1 (FloatSpec.Core.Raux.mag beta (x - y)) ≤
        FloatSpec.Core.Raux.mag beta y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x - y) := by
  rcases hexp with ⟨_, _, hsame, hmag⟩
  exact round_round_minus_aux0_aux (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2) (x := x) (y := y)
    (hβ := hβ)
    (hlnx := hmag (FloatSpec.Core.Raux.mag beta (x - y))
      (FloatSpec.Core.Raux.mag beta x) (by
        have hmxy_le_mx :
            FloatSpec.Core.Raux.mag beta (x - y) ≤
              FloatSpec.Core.Raux.mag beta x := by
          have htrip := FloatSpec.Core.Raux.mag_minus
            (beta := beta) (x := x) (y := y) hβ hy_pos hyx
          simpa [wp, PostCond.noThrow, Id.run, pure] using htrip True.intro
        omega))
    (hlny := hsame (FloatSpec.Core.Raux.mag beta (x - y))
      (FloatSpec.Core.Raux.mag beta y) hln')
    (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)

/-- Coq: `round_round_minus_radix_ge_3_aux2`. -/
theorem round_round_minus_radix_ge_3_aux2 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
    (x y : ℝ)
    (hy_pos : 0 < y)
    (hyx : y < x)
    (hly :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp1 (FloatSpec.Core.Raux.mag beta x) - 1)
    (hly' :
      FloatSpec.Core.Raux.mag beta y ≤
        fexp1 (FloatSpec.Core.Raux.mag beta (x - y)) - 1)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) := by
  classical
  have hβ1 : 1 < beta := by omega
  rcases hexp with ⟨_, _, _, hmag⟩
  set z : ℝ := x - y with hz
  set mz : Int := FloatSpec.Core.Raux.mag beta z with hmz
  set e1 : Int := fexp1 mz with he1
  have hz_pos : 0 < z := by
    simpa [z, hz] using sub_pos.mpr hyx
  have hz_ne : z ≠ 0 := ne_of_gt hz_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hceil_err :
      FloatSpec.Core.Generic_fmt.roundR beta fexp1
          FloatSpec.Core.Generic_fmt.rnd_ceil z - z ≤ y := by
    simpa [z, hz] using
      round_round_minus_aux2_aux (beta := beta) (fexp := fexp1)
        (hβ := hβ1) (x := x) (y := y) (hy_pos := hy_pos)
        (_hyx := hyx) (_hly := hly) (hx_fmt := hx_fmt)
        (_hy_fmt := hy_fmt)
  have hf21 :
      fexp2 (FloatSpec.Core.Raux.mag beta z) ≤
        fexp1 (FloatSpec.Core.Raux.mag beta z) := by
    simpa [mz, hmz, e1, he1] using
      hmag mz mz (by omega)
  have hf1_y_le_my :
      fexp1 (FloatSpec.Core.Raux.mag beta y) ≤
        FloatSpec.Core.Raux.mag beta y := by
    have htrip := FloatSpec.Core.Generic_fmt.mag_generic_gt
      (beta := beta) (fexp := fexp1) y
    have hlt :
        FloatSpec.Core.Generic_fmt.cexp beta fexp1 y <
          FloatSpec.Core.Raux.mag beta y := by
      simpa [wp, PostCond.noThrow, Id.run, pure] using
        htrip ⟨hβ1, hy_ne, hy_fmt⟩
    simpa [FloatSpec.Core.Generic_fmt.cexp] using le_of_lt hlt
  have hf1_le_mz :
      fexp1 (FloatSpec.Core.Raux.mag beta z) ≤
        FloatSpec.Core.Raux.mag beta z := by
    by_contra hnot
    have hmz_lt_e1 : mz < e1 := by
      exact lt_of_not_ge (by simpa [mz, hmz, e1, he1] using hnot)
    have hsmall : mz ≤ fexp1 mz := le_of_lt hmz_lt_e1
    have hconst :=
      (FloatSpec.Core.Generic_fmt.Valid_exp.valid_exp
        (beta := beta) (fexp := fexp1) mz).right hsmall |>.right
    have hfy_eq : fexp1 (FloatSpec.Core.Raux.mag beta y) = e1 := by
      have hle : FloatSpec.Core.Raux.mag beta y ≤ fexp1 mz := by
        have hle' : FloatSpec.Core.Raux.mag beta y ≤ e1 - 1 := by
          simpa [mz, hmz, e1, he1, z, hz] using hly'
        omega
      simpa [e1, he1] using hconst (FloatSpec.Core.Raux.mag beta y) hle
    have hmy_lt_e1 : FloatSpec.Core.Raux.mag beta y < e1 := by
      have hle : FloatSpec.Core.Raux.mag beta y ≤ e1 - 1 := by
        simpa [mz, hmz, e1, he1, z, hz] using hly'
      omega
    omega
  have hbposℤ : (0 : Int) < beta := by omega
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hpow_one_nonneg : 0 ≤ (beta : ℝ) ^ (e1 - 1) :=
    le_of_lt (zpow_pos hbposR (e1 - 1))
  have hy_lt_mag :
      y < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := by
    have htrip := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := y) hβ1 hy_ne
    simpa [FloatSpec.Core.Raux.abs_val, abs_of_pos hy_pos, wp,
      PostCond.noThrow, Id.run, pure] using htrip True.intro
  have hy_lt_e1_sub1 : y < (beta : ℝ) ^ (e1 - 1) := by
    have hpow_le :
        (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) ≤
          (beta : ℝ) ^ (e1 - 1) := by
      have htrip := FloatSpec.Core.Raux.bpow_le (beta := beta)
        (e1 := FloatSpec.Core.Raux.mag beta y) (e2 := e1 - 1) hβ1
        (by simpa [mz, hmz, e1, he1, z, hz] using hly')
      simpa [FloatSpec.Core.Raux.bpow_le_check, wp, PostCond.noThrow, Id.run,
        pure] using htrip True.intro
    exact lt_of_lt_of_le hy_lt_mag hpow_le
  have hulp1 :
      ulp beta fexp1 z = (beta : ℝ) ^ e1 := by
    have htrip := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp1) (x := z) hz_ne
    simpa [wp, PostCond.noThrow, Id.run, pure, e1, he1, mz, hmz,
      FloatSpec.Core.Generic_fmt.cexp] using htrip True.intro
  have hpow_one_to_half :
      (beta : ℝ) ^ (e1 - 1) ≤
        (1 / 2 : ℝ) * ((beta : ℝ) ^ e1) := by
    have hpow_cancel :
        (beta : ℝ) ^ (e1 - 1) =
          (beta : ℝ) ^ e1 * (beta : ℝ) ^ (-(1 : Int)) := by
      calc
        (beta : ℝ) ^ (e1 - 1)
            = (beta : ℝ) ^ (e1 + (-(1 : Int))) := by ring_nf
        _ = (beta : ℝ) ^ e1 * (beta : ℝ) ^ (-(1 : Int)) := by
              rw [zpow_add₀ hbne]
    have hinv_le_half :
        (beta : ℝ) ^ (-(1 : Int)) ≤ (1 / 2 : ℝ) := by
      have h2ℤ : (2 : Int) ≤ beta := by omega
      have h2R : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast h2ℤ
      have hinv : 1 / (beta : ℝ) ≤ (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) h2R
      simpa [zpow_neg, one_div] using hinv
    rw [hpow_cancel]
    have hmul := mul_le_mul_of_nonneg_left hinv_le_half
      (le_of_lt (zpow_pos hbposR e1))
    calc
      (beta : ℝ) ^ e1 * (beta : ℝ) ^ (-(1 : Int))
          ≤ (beta : ℝ) ^ e1 * (1 / 2 : ℝ) := hmul
      _ = (1 / 2 : ℝ) * ((beta : ℝ) ^ e1) := by ring
  have hx_mid :
      midp' beta fexp1 z < z := by
    have hgap_half :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            FloatSpec.Core.Generic_fmt.rnd_ceil z - z <
          (1 / 2 : ℝ) * ulp beta fexp1 z :=
      lt_of_le_of_lt hceil_err
        (lt_of_lt_of_le hy_lt_e1_sub1 (by simpa [hulp1] using hpow_one_to_half))
    unfold midp'
    linarith
  apply round_round_gt_mid (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2) (x := z) hβ1
  · exact hz_pos
  · simpa [z, hz] using hf21
  · simpa [z, hz] using hf1_le_mz
  · exact hx_mid
  · intro hfurther
    set e2 : Int := fexp2 mz with he2
    have hfurther' : e2 ≤ e1 - 1 := by
      simpa [e1, he1, e2, he2, mz, hmz] using hfurther
    have hulp2 :
        ulp beta fexp2 z = (beta : ℝ) ^ e2 := by
      have htrip := FloatSpec.Core.Ulp.ulp_neq_0
        (beta := beta) (fexp := fexp2) (x := z) hz_ne
      simpa [wp, PostCond.noThrow, Id.run, pure, e2, he2, mz, hmz,
        FloatSpec.Core.Generic_fmt.cexp] using htrip True.intro
    have hpow_e2_le :
        (beta : ℝ) ^ e2 ≤ (beta : ℝ) ^ (e1 - 1) := by
      have htrip := FloatSpec.Core.Raux.bpow_le (beta := beta)
        (e1 := e2) (e2 := e1 - 1) hβ1 hfurther'
      simpa [FloatSpec.Core.Raux.bpow_le_check, wp, PostCond.noThrow, Id.run,
        pure] using htrip True.intro
    have hpow_one_to_half_diff :
        (beta : ℝ) ^ (e1 - 1) ≤
          (1 / 2 : ℝ) * ((beta : ℝ) ^ e1 - (beta : ℝ) ^ e2) := by
      have hpow_e_split :
          (beta : ℝ) ^ e1 =
            (beta : ℝ) ^ (e1 - 1) * (beta : ℝ) := by
        calc
          (beta : ℝ) ^ e1 = (beta : ℝ) ^ ((e1 - 1) + 1) := by ring_nf
          _ = (beta : ℝ) ^ (e1 - 1) * (beta : ℝ) ^ (1 : Int) := by
                rw [zpow_add₀ hbne]
          _ = (beta : ℝ) ^ (e1 - 1) * (beta : ℝ) := by simp
      have hfactor : (1 : ℝ) ≤ (1 / 2 : ℝ) * ((beta : ℝ) - 1) := by
        have hβR : (3 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hβ
        nlinarith
      have hbase :
          (beta : ℝ) ^ (e1 - 1) ≤
            (1 / 2 : ℝ) *
              ((beta : ℝ) ^ e1 - (beta : ℝ) ^ (e1 - 1)) := by
        rw [hpow_e_split]
        have hmul := mul_le_mul_of_nonneg_left hfactor hpow_one_nonneg
        nlinarith
      have hsub :
          (beta : ℝ) ^ e1 - (beta : ℝ) ^ (e1 - 1) ≤
            (beta : ℝ) ^ e1 - (beta : ℝ) ^ e2 := by
        linarith
      have hhalf := mul_le_mul_of_nonneg_left hsub
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
      exact le_trans hbase hhalf
    have hgap_further :
        FloatSpec.Core.Generic_fmt.roundR beta fexp1
            FloatSpec.Core.Generic_fmt.rnd_ceil z - z <
          (1 / 2 : ℝ) * (ulp beta fexp1 z - ulp beta fexp2 z) :=
      lt_of_le_of_lt hceil_err
        (lt_of_lt_of_le hy_lt_e1_sub1
          (by simpa [hulp1, hulp2] using hpow_one_to_half_diff))
    unfold midp'
    linarith

/-- Coq: `round_round_minus_radix_ge_3_aux3`. -/
theorem round_round_minus_radix_ge_3_aux3 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
    (x y : ℝ)
    (hy_pos : 0 < y)
    (hyx : y ≤ x)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) := by
  classical
  have hβ1 : 1 < beta := by omega
  by_cases hxy_eq : y = x
  · have hdiff : x - y = 0 := by linarith
    have hfmt0 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (0 : ℝ) :=
      FloatSpec.Core.Generic_fmt.generic_format_0_run
        (beta := beta) (fexp := fexp2)
    have hinner :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) (x - y) =
          x - y := by
      rw [hdiff]
      exact FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
        (x := 0) hβ1 hfmt0
    simpa [round_round_eq, hinner]
  · have hyx_lt : y < x := lt_of_le_of_ne hyx hxy_eq
    by_cases hly :
        FloatSpec.Core.Raux.mag beta y ≤
          fexp1 (FloatSpec.Core.Raux.mag beta x) - 1
    · by_cases hly' :
        FloatSpec.Core.Raux.mag beta y ≤
          fexp1 (FloatSpec.Core.Raux.mag beta (x - y)) - 1
      · exact round_round_minus_radix_ge_3_aux2 (beta := beta)
          (fexp1 := fexp1) (fexp2 := fexp2)
          (choice1 := choice1) (choice2 := choice2)
          (hβ := hβ) (hexp := hexp) (x := x) (y := y)
          (hy_pos := hy_pos) (hyx := hyx_lt)
          (hly := hly) (hly' := hly')
          (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)
      · have hlarge' :
          fexp1 (FloatSpec.Core.Raux.mag beta (x - y)) ≤
            FloatSpec.Core.Raux.mag beta y := by
          omega
        have hfmt2 :
            FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x - y) :=
          round_round_minus_radix_ge_3_aux1 (beta := beta)
            (fexp1 := fexp1) (fexp2 := fexp2)
            (hβ := hβ1) (hexp := hexp) (x := x) (y := y)
            (hy_pos := hy_pos) (hyx := hyx_lt)
            (_hln := hly) (hln' := hlarge')
            (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)
        have hinner :
            FloatSpec.Core.Generic_fmt.roundR beta fexp2
                (FloatSpec.Core.Generic_fmt.Znearest choice2) (x - y) =
              x - y :=
          FloatSpec.Core.Generic_fmt.roundR_generic
            (beta := beta) (fexp := fexp2)
            (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
            (x := x - y) hβ1 hfmt2
        simpa [round_round_eq, hinner]
    · have hlarge :
          fexp1 (FloatSpec.Core.Raux.mag beta x) ≤
            FloatSpec.Core.Raux.mag beta y := by
        omega
      have hfmt2 :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x - y) :=
        round_round_minus_radix_ge_3_aux0 (beta := beta)
          (fexp1 := fexp1) (fexp2 := fexp2)
          (hβ := hβ1) (hexp := hexp) (x := x) (y := y)
          (hy_pos := hy_pos) (hyx := hyx_lt) (hln := hlarge)
          (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)
      have hinner :
          FloatSpec.Core.Generic_fmt.roundR beta fexp2
              (FloatSpec.Core.Generic_fmt.Znearest choice2) (x - y) =
            x - y :=
        FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := beta) (fexp := fexp2)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
          (x := x - y) hβ1 hfmt2
      simpa [round_round_eq, hinner]

/-- Coq: `round_round_minus_radix_ge_3_aux`. -/
theorem round_round_minus_radix_ge_3_aux (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hy_nonneg : 0 ≤ y)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) := by
  classical
  have hβ1 : 1 < beta := by omega
  let include_format :
      ∀ z : ℝ,
        FloatSpec.Core.Generic_fmt.generic_format beta fexp1 z →
          FloatSpec.Core.Generic_fmt.generic_format beta fexp2 z := by
    intro z hz_fmt
    exact FloatSpec.Core.Generic_fmt.generic_inclusion_mag
      (beta := beta) (fexp1 := fexp1) (fexp2 := fexp2) (x := z)
      hβ1
      (by
        intro _hz
        exact hexp.2.2.2 (FloatSpec.Core.Raux.mag beta z)
          (FloatSpec.Core.Raux.mag beta z) (by omega))
      hz_fmt
  by_cases hx0 : x = 0
  · have hy_fmt2 : FloatSpec.Core.Generic_fmt.generic_format beta fexp2 y :=
      include_format y hy_fmt
    have hneg_trip := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := fexp2) (x := y)
    have hy_neg_fmt2 :
        FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (-y) := by
      simpa [wp, PostCond.noThrow, Id.run, pure] using
        hneg_trip hy_fmt2
    have hinner :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) (x - y) =
          x - y := by
      exact FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
        (x := x - y) hβ1 (by simpa [hx0] using hy_neg_fmt2)
    simpa [round_round_eq, hinner]
  by_cases hy0 : y = 0
  · have hx_fmt2 : FloatSpec.Core.Generic_fmt.generic_format beta fexp2 x :=
      include_format x hx_fmt
    have hinner :
        FloatSpec.Core.Generic_fmt.roundR beta fexp2
            (FloatSpec.Core.Generic_fmt.Znearest choice2) (x - y) =
          x - y := by
      exact FloatSpec.Core.Generic_fmt.roundR_generic
        (beta := beta) (fexp := fexp2)
        (rnd := FloatSpec.Core.Generic_fmt.Znearest choice2)
        (x := x - y) hβ1 (by simpa [hy0] using hx_fmt2)
    simpa [round_round_eq, hinner]
  have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
  have hy_pos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hy0)
  by_cases hxy : x < y
  · have hcore :
        round_round_eq beta fexp1 fexp2
          (fun t => ! choice1 (-(t + 1)))
          (fun t => ! choice2 (-(t + 1))) (y - x) :=
      round_round_minus_radix_ge_3_aux3 (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := fun t => ! choice1 (-(t + 1)))
        (choice2 := fun t => ! choice2 (-(t + 1)))
        (hβ := hβ) (hexp := hexp)
        (x := y) (y := x)
        (hy_pos := hx_pos) (hyx := le_of_lt hxy)
        (hx_fmt := hy_fmt) (hy_fmt := hx_fmt)
    have hneg := round_round_eq_opp (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2)
      (x := y - x) hcore
    have hsub : x - y = -(y - x) := by ring
    rw [hsub]
    exact hneg
  · exact round_round_minus_radix_ge_3_aux3 (beta := beta)
      (fexp1 := fexp1) (fexp2 := fexp2)
      (choice1 := choice1) (choice2 := choice2)
      (hβ := hβ) (hexp := hexp)
      (x := x) (y := y)
      (hy_pos := hy_pos) (hyx := le_of_not_gt hxy)
      (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)

/-- Coq: `round_round_plus_radix_ge_3`. -/
theorem round_round_plus_radix_ge_3 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) := by
  classical
  have hβ1 : 1 < beta := by omega
  by_cases hx_neg : x < 0
  · by_cases hy_neg : y < 0
    · have hx_opp_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-x) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := fexp1) (x := x)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hx_fmt
      have hy_opp_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-y) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := fexp1) (x := y)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hy_fmt
      have hcore :
          round_round_eq beta fexp1 fexp2
            (fun t => ! choice1 (-(t + 1)))
            (fun t => ! choice2 (-(t + 1))) ((-x) + (-y)) :=
        round_round_plus_radix_ge_3_aux (beta := beta)
          (fexp1 := fexp1) (fexp2 := fexp2)
          (choice1 := fun t => ! choice1 (-(t + 1)))
          (choice2 := fun t => ! choice2 (-(t + 1)))
          (hβ := hβ) (hexp := hexp)
          (x := -x) (y := -y)
          (hx_nonneg := le_of_lt (neg_pos.mpr hx_neg))
          (hy_nonneg := le_of_lt (neg_pos.mpr hy_neg))
          (hx_fmt := hx_opp_fmt) (hy_fmt := hy_opp_fmt)
      have hneg := round_round_eq_opp (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        (x := (-x) + (-y)) hcore
      have hsum : x + y = -((-x) + (-y)) := by ring
      rw [hsum]
      exact hneg
    · have hx_opp_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-x) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := fexp1) (x := x)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hx_fmt
      have hcore := round_round_minus_radix_ge_3_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        (hβ := hβ) (hexp := hexp)
        (x := y) (y := -x)
        (hx_nonneg := le_of_not_gt hy_neg)
        (hy_nonneg := le_of_lt (neg_pos.mpr hx_neg))
        (hx_fmt := hy_fmt) (hy_fmt := hx_opp_fmt)
      have hsum : x + y = y - (-x) := by ring
      rw [hsum]
      exact hcore
  · by_cases hy_neg : y < 0
    · have hy_opp_fmt :
          FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-y) := by
        have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
          (beta := beta) (fexp := fexp1) (x := y)
        simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hy_fmt
      have hcore := round_round_minus_radix_ge_3_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        (hβ := hβ) (hexp := hexp)
        (x := x) (y := -y)
        (hx_nonneg := le_of_not_gt hx_neg)
        (hy_nonneg := le_of_lt (neg_pos.mpr hy_neg))
        (hx_fmt := hx_fmt) (hy_fmt := hy_opp_fmt)
      have hsum : x + y = x - (-y) := by ring
      rw [hsum]
      exact hcore
    · exact round_round_plus_radix_ge_3_aux (beta := beta)
        (fexp1 := fexp1) (fexp2 := fexp2)
        (choice1 := choice1) (choice2 := choice2)
        (hβ := hβ) (hexp := hexp)
        (x := x) (y := y)
        (hx_nonneg := le_of_not_gt hx_neg)
        (hy_nonneg := le_of_not_gt hy_neg)
        (hx_fmt := hx_fmt) (hy_fmt := hy_fmt)

/-- Coq: `round_round_minus_radix_ge_3`. -/
theorem round_round_minus_radix_ge_3 (fexp1 fexp2 : Int → Int)
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
    [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hexp : round_round_plus_radix_ge_3_hyp fexp1 fexp2)
    (x y : ℝ)
    (hx_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy_fmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) := by
  have hy_opp_fmt :
      FloatSpec.Core.Generic_fmt.generic_format beta fexp1 (-y) := by
    have htrip := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := fexp1) (x := y)
    simpa [wp, PostCond.noThrow, Id.run, pure] using htrip hy_fmt
  have hcore := round_round_plus_radix_ge_3 (beta := beta)
    (fexp1 := fexp1) (fexp2 := fexp2)
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ) (hexp := hexp)
    (x := x) (y := -y)
    (hx_fmt := hx_fmt) (hy_fmt := hy_opp_fmt)
  simpa [sub_eq_add_neg] using hcore

/-- Coq: `FLX_round_round_plus_radix_ge_3_hyp`. -/
theorem FLX_round_round_plus_radix_ge_3_hyp (prec prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (hprec : 2 * prec ≤ prec') :
    round_round_plus_radix_ge_3_hyp
      (FloatSpec.Core.FLX.FLX_exp prec)
      (FloatSpec.Core.FLX.FLX_exp prec') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  unfold round_round_plus_radix_ge_3_hyp FloatSpec.Core.FLX.FLX_exp
  constructor
  · intro ex ey _
    omega
  constructor
  · intro ex ey _
    omega
  constructor
  · intro ex ey _
    omega
  · intro ex ey _
    omega

/-- Coq: `round_round_plus_radix_ge_3_FLX`. -/
theorem round_round_plus_radix_ge_3_FLX (prec prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hprec : 2 * prec ≤ prec')
    (x y : ℝ)
    (hx : FloatSpec.Core.FLX.FLX_format prec beta x)
    (hy : FloatSpec.Core.FLX.FLX_format prec beta y) :
    round_round_eq beta
      (FloatSpec.Core.FLX.FLX_exp prec)
      (FloatSpec.Core.FLX.FLX_exp prec')
      choice1 choice2 (x + y) := by
  exact round_round_plus_radix_ge_3 (beta := beta)
    (fexp1 := FloatSpec.Core.FLX.FLX_exp prec)
    (fexp2 := FloatSpec.Core.FLX.FLX_exp prec')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ)
    (hexp := FLX_round_round_plus_radix_ge_3_hyp
      (prec := prec) (prec' := prec') hprec)
    (x := x) (y := y)
    (hx_fmt := by simpa [FloatSpec.Core.FLX.FLX_format] using hx)
    (hy_fmt := by simpa [FloatSpec.Core.FLX.FLX_format] using hy)

/-- Coq: `round_round_minus_radix_ge_3_FLX`. -/
theorem round_round_minus_radix_ge_3_FLX (prec prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hprec : 2 * prec ≤ prec')
    (x y : ℝ)
    (hx : FloatSpec.Core.FLX.FLX_format prec beta x)
    (hy : FloatSpec.Core.FLX.FLX_format prec beta y) :
    round_round_eq beta
      (FloatSpec.Core.FLX.FLX_exp prec)
      (FloatSpec.Core.FLX.FLX_exp prec')
      choice1 choice2 (x - y) := by
  exact round_round_minus_radix_ge_3 (beta := beta)
    (fexp1 := FloatSpec.Core.FLX.FLX_exp prec)
    (fexp2 := FloatSpec.Core.FLX.FLX_exp prec')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ)
    (hexp := FLX_round_round_plus_radix_ge_3_hyp
      (prec := prec) (prec' := prec') hprec)
    (x := x) (y := y)
    (hx_fmt := by simpa [FloatSpec.Core.FLX.FLX_format] using hx)
    (hy_fmt := by simpa [FloatSpec.Core.FLX.FLX_format] using hy)

/-- Coq: `FLT_round_round_plus_radix_ge_3_hyp`. -/
theorem FLT_round_round_plus_radix_ge_3_hyp
    (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (hemin : emin' ≤ emin)
    (hprec : 2 * prec ≤ prec') :
    round_round_plus_radix_ge_3_hyp
      (FloatSpec.Core.FLT.FLT_exp prec emin)
      (FloatSpec.Core.FLT.FLT_exp prec' emin') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  unfold round_round_plus_radix_ge_3_hyp FloatSpec.Core.FLT.FLT_exp
  constructor
  · intro ex ey h
    grind
  constructor
  · intro ex ey h
    grind
  constructor
  · intro ex ey h
    grind
  · intro ex ey h
    grind

/-- Coq: `round_round_plus_radix_ge_3_FLT`. -/
theorem round_round_plus_radix_ge_3_FLT (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hemin : emin' ≤ emin)
    (hprec : 2 * prec ≤ prec')
    (x y : ℝ)
    (hx : FloatSpec.Core.FLT.FLT_format prec emin beta x)
    (hy : FloatSpec.Core.FLT.FLT_format prec emin beta y) :
    round_round_eq beta
      (FloatSpec.Core.FLT.FLT_exp prec emin)
      (FloatSpec.Core.FLT.FLT_exp prec' emin')
      choice1 choice2 (x + y) := by
  exact round_round_plus_radix_ge_3 (beta := beta)
    (fexp1 := FloatSpec.Core.FLT.FLT_exp prec emin)
    (fexp2 := FloatSpec.Core.FLT.FLT_exp prec' emin')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ)
    (hexp := FLT_round_round_plus_radix_ge_3_hyp
      (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
      hemin hprec)
    (x := x) (y := y)
    (hx_fmt := by simpa [FloatSpec.Core.FLT.FLT_format] using hx)
    (hy_fmt := by simpa [FloatSpec.Core.FLT.FLT_format] using hy)

/-- Coq: `round_round_minus_radix_ge_3_FLT`. -/
theorem round_round_minus_radix_ge_3_FLT (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hemin : emin' ≤ emin)
    (hprec : 2 * prec ≤ prec')
    (x y : ℝ)
    (hx : FloatSpec.Core.FLT.FLT_format prec emin beta x)
    (hy : FloatSpec.Core.FLT.FLT_format prec emin beta y) :
    round_round_eq beta
      (FloatSpec.Core.FLT.FLT_exp prec emin)
      (FloatSpec.Core.FLT.FLT_exp prec' emin')
      choice1 choice2 (x - y) := by
  exact round_round_minus_radix_ge_3 (beta := beta)
    (fexp1 := FloatSpec.Core.FLT.FLT_exp prec emin)
    (fexp2 := FloatSpec.Core.FLT.FLT_exp prec' emin')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ)
    (hexp := FLT_round_round_plus_radix_ge_3_hyp
      (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
      hemin hprec)
    (x := x) (y := y)
    (hx_fmt := by simpa [FloatSpec.Core.FLT.FLT_format] using hx)
    (hy_fmt := by simpa [FloatSpec.Core.FLT.FLT_format] using hy)

/-- Coq: `FTZ_round_round_plus_radix_ge_3_hyp`. -/
theorem FTZ_round_round_plus_radix_ge_3_hyp
    (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (hemin : emin' + prec' ≤ emin + 1)
    (hprec : 2 * prec ≤ prec') :
    round_round_plus_radix_ge_3_hyp
      (FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (FloatSpec.Core.FTZ.FTZ_exp prec' emin') := by
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec'_pos : 0 < prec' := (Prec_gt_0.pos : 0 < prec')
  unfold round_round_plus_radix_ge_3_hyp FloatSpec.Core.FTZ.FTZ_exp
  constructor
  · intro ex ey h
    split_ifs at h ⊢ <;> omega
  constructor
  · intro ex ey h
    split_ifs at h ⊢ <;> omega
  constructor
  · intro ex ey h
    split_ifs at h ⊢ <;> omega
  · intro ex ey h
    split_ifs at h ⊢ <;> omega

/-- Coq: `round_round_plus_radix_ge_3_FTZ`. -/
theorem round_round_plus_radix_ge_3_FTZ (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hemin : emin' + prec' ≤ emin + 1)
    (hprec : 2 * prec ≤ prec')
    (x y : ℝ)
    (hx : FloatSpec.Core.FTZ.FTZ_format prec emin beta x)
    (hy : FloatSpec.Core.FTZ.FTZ_format prec emin beta y) :
    round_round_eq beta
      (FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (FloatSpec.Core.FTZ.FTZ_exp prec' emin')
      choice1 choice2 (x + y) := by
  exact round_round_plus_radix_ge_3 (beta := beta)
    (fexp1 := FloatSpec.Core.FTZ.FTZ_exp prec emin)
    (fexp2 := FloatSpec.Core.FTZ.FTZ_exp prec' emin')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ)
    (hexp := FTZ_round_round_plus_radix_ge_3_hyp
      (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
      hemin hprec)
    (x := x) (y := y)
    (hx_fmt := by simpa [FloatSpec.Core.FTZ.FTZ_format] using hx)
    (hy_fmt := by simpa [FloatSpec.Core.FTZ.FTZ_format] using hy)

/-- Coq: `round_round_minus_radix_ge_3_FTZ`. -/
theorem round_round_minus_radix_ge_3_FTZ (emin prec emin' prec' : Int)
    [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool)
    (hβ : 3 ≤ beta)
    (hemin : emin' + prec' ≤ emin + 1)
    (hprec : 2 * prec ≤ prec')
    (x y : ℝ)
    (hx : FloatSpec.Core.FTZ.FTZ_format prec emin beta x)
    (hy : FloatSpec.Core.FTZ.FTZ_format prec emin beta y) :
    round_round_eq beta
      (FloatSpec.Core.FTZ.FTZ_exp prec emin)
      (FloatSpec.Core.FTZ.FTZ_exp prec' emin')
      choice1 choice2 (x - y) := by
  exact round_round_minus_radix_ge_3 (beta := beta)
    (fexp1 := FloatSpec.Core.FTZ.FTZ_exp prec emin)
    (fexp2 := FloatSpec.Core.FTZ.FTZ_exp prec' emin')
    (choice1 := choice1) (choice2 := choice2)
    (hβ := hβ)
    (hexp := FTZ_round_round_plus_radix_ge_3_hyp
      (emin := emin) (prec := prec) (emin' := emin') (prec' := prec')
      hemin hprec)
    (x := x) (y := y)
    (hx_fmt := by simpa [FloatSpec.Core.FTZ.FTZ_format] using hx)
    (hy_fmt := by simpa [FloatSpec.Core.FTZ.FTZ_format] using hy)
