import FloatSpec.src.Core
import FloatSpec.src.Core.FTZ
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import Mathlib.Data.Real.Basic

open Std.Do

-- Double rounding properties
-- Translated from Coq file: flocq/src/Prop/Double_rounding.v

variable (beta : Int)

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
    simpa [FloatSpec.Core.Generic_fmt.Znearest_imp_check, wp,
      PostCond.noThrow, Id.run, pure] using h
  have hZ2 :
      FloatSpec.Core.Generic_fmt.Znearest choice2
          (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 x) = n := by
    simpa [hsm2] using
      (by
        have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice2 sm n) hdist_floor
        simpa [FloatSpec.Core.Generic_fmt.Znearest_imp_check, wp,
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
    simpa [FloatSpec.Core.Generic_fmt.Znearest_imp_check, wp,
      PostCond.noThrow, Id.run, pure] using h
  have hZ2 :
      FloatSpec.Core.Generic_fmt.Znearest choice2
          (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp2 x) = n := by
    simpa [hsm2] using
      (by
        have h := (FloatSpec.Core.Generic_fmt.Znearest_imp choice2 sm n) hdist_ceil
        simpa [FloatSpec.Core.Generic_fmt.Znearest_imp_check, wp,
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
    simpa [FloatSpec.Core.Generic_fmt.Znearest_imp_check, wp,
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
      simpa [FloatSpec.Core.Generic_fmt.Znearest_imp_check, wp,
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
      simpa [FloatSpec.Core.Generic_fmt.Znearest_imp_check, wp,
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
      simpa [FloatSpec.Core.Generic_fmt.Znearest_imp_check, wp,
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
    simpa [FloatSpec.Core.Generic_fmt.Znearest_imp_check, wp,
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
      simpa [FloatSpec.Core.Generic_fmt.Znearest_imp_check, wp,
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
      simpa [FloatSpec.Core.Generic_fmt.Znearest_imp_check, wp,
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

/-! Structural hypotheses used by the omitted Flocq double-rounding lemmas. -/

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

/-- Coq: `round_round_sqrt_radix_ge_4_hyp`. -/
def round_round_sqrt_radix_ge_4_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex)) ∧
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1)) ∧
  (∀ ex, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - 1)

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
      simpa [wp, PostCond.noThrow, Id.run, pure] using
        htrip ⟨hβ, hx_ne, hx_fmt⟩
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

/-- Coq: `round_round_plus_radix_ge_3_hyp`. -/
def round_round_plus_radix_ge_3_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex ey, fexp1 (ex + 1) ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 (ex - 1) + 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, fexp1 ex ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
  (∀ ex ey, ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey)
