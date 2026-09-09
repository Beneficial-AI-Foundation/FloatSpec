import FloatSpec.src.Core
import FloatSpec.src.Compat
import Mathlib.Data.Real.Basic

-- Sterbenz conditions for exact subtraction
-- Translated from Coq file: flocq/src/Prop/Sterbenz.v

open Real
open Std.Do

variable (beta : Int) [ValidRadix beta]
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp fexp]
variable [FloatSpec.Core.Generic_fmt.Monotone_exp fexp]

/-- Generic format plus exact under magnitude condition -/
theorem generic_format_plus (x y : ℝ)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (hβ : 1 < beta)
  (h_bound : |x + y| ≤ (beta : ℝ) ^ (min (mag beta x) (mag beta y))) :
  generic_format beta fexp (x + y) := by
  classical
  by_cases hz : x + y = 0
  · simpa [generic_format, hz] using
      (FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp))
  by_cases hx0 : x = 0
  · simpa [hx0, zero_add] using hy
  by_cases hy0 : y = 0
  · simpa [hy0, add_zero] using hx

  let fx : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Raux.Ztrunc
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x))
      (FloatSpec.Core.Generic_fmt.cexp beta fexp x)
  let fy : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Raux.Ztrunc
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp y))
      (FloatSpec.Core.Generic_fmt.cexp beta fexp y)

  have hx_repr : FloatSpec.Core.Defs.F2R fx = x := by
    simpa [fx, generic_format, F2R] using hx.symm
  have hy_repr : FloatSpec.Core.Defs.F2R fy = y := by
    simpa [fy, generic_format, F2R] using hy.symm

  set e : Int := min (mag beta x) (mag beta y) with he
  have hfmt_bpow : generic_format beta fexp ((beta : ℝ) ^ e) := by
    have hfe : fexp e ≤ e := by
      rcases min_choice (mag beta x) (mag beta y) with hmin | hmin
      · have hx_cexp_le :
            FloatSpec.Core.Generic_fmt.cexp beta fexp x ≤ mag beta x := by
          have h :=
            FloatSpec.Core.Generic_fmt.mag_generic_gt (beta := beta) (fexp := fexp) x
              ⟨hβ, hx0, by simpa [generic_format] using hx⟩
          simpa [Std.Do.PostCond.noThrow, wp, pure] using (le_of_lt h)
        simpa [e, he, hmin, FloatSpec.Core.Generic_fmt.cexp] using hx_cexp_le
      · have hy_cexp_le :
            FloatSpec.Core.Generic_fmt.cexp beta fexp y ≤ mag beta y := by
          have h :=
            FloatSpec.Core.Generic_fmt.mag_generic_gt (beta := beta) (fexp := fexp) y
              ⟨hβ, hy0, by simpa [generic_format] using hy⟩
          simpa [Std.Do.PostCond.noThrow, wp, pure] using (le_of_lt h)
        simpa [e, he, hmin, FloatSpec.Core.Generic_fmt.cexp] using hy_cexp_le
    have h :=
      FloatSpec.Core.Generic_fmt.generic_format_bpow' (beta := beta) (fexp := fexp) e
        ⟨hβ, hfe⟩
    simpa [generic_format] using h

  rcases lt_or_eq_of_le h_bound with hlt | heq_abs
  · let fxy : FloatSpec.Core.Defs.FlocqFloat beta :=
      FloatSpec.Calc.Operations.Fplus beta fx fy
    have hFplus :
        FloatSpec.Core.Defs.F2R fxy =
          FloatSpec.Core.Defs.F2R fx + FloatSpec.Core.Defs.F2R fy := by
      have h := (FloatSpec.Calc.Operations.F2R_plus (beta := beta) fx fy) hβ
      simpa [fxy, Std.Do.PostCond.noThrow, wp, pure] using h
    have hfxy_eq : FloatSpec.Core.Defs.F2R fxy = x + y := by
      calc
        FloatSpec.Core.Defs.F2R fxy =
            FloatSpec.Core.Defs.F2R fx + FloatSpec.Core.Defs.F2R fy := hFplus
        _ = x + y := by rw [hx_repr, hy_repr]
    have hfxy_exp :
        fxy.Fexp =
          min (FloatSpec.Core.Generic_fmt.cexp beta fexp x)
              (FloatSpec.Core.Generic_fmt.cexp beta fexp y) := by
      have h :=
        (FloatSpec.Calc.Operations.Fexp_Fplus_spec (beta := beta) fx fy) trivial
      simpa [fxy, fx, fy, FloatSpec.Calc.Operations.Fexp_Fplus,
        Std.Do.PostCond.noThrow, wp, pure] using h
    have hmag_xy : mag beta (x + y) ≤ e := by
      have htrip :=
        FloatSpec.Core.Raux.mag_le_bpow (beta := beta) (x := x + y) (e := e)
          hβ hz (by simpa [e, he] using hlt)
      simpa [Std.Do.PostCond.noThrow, wp, pure] using htrip trivial
    have hcexp_le :
        FloatSpec.Core.Generic_fmt.cexp beta fexp (x + y) ≤ fxy.Fexp := by
      have hmono_xy :
          fexp (mag beta (x + y)) ≤ fexp e :=
        FloatSpec.Core.Generic_fmt.Monotone_exp.mono (fexp := fexp) hmag_xy
      have he_le_x : e ≤ mag beta x := by simpa [e, he] using min_le_left (mag beta x) (mag beta y)
      have he_le_y : e ≤ mag beta y := by simpa [e, he] using min_le_right (mag beta x) (mag beta y)
      have hmono_x :
          fexp e ≤ FloatSpec.Core.Generic_fmt.cexp beta fexp x := by
        simpa [FloatSpec.Core.Generic_fmt.cexp] using
          (FloatSpec.Core.Generic_fmt.Monotone_exp.mono (fexp := fexp) he_le_x)
      have hmono_y :
          fexp e ≤ FloatSpec.Core.Generic_fmt.cexp beta fexp y := by
        simpa [FloatSpec.Core.Generic_fmt.cexp] using
          (FloatSpec.Core.Generic_fmt.Monotone_exp.mono (fexp := fexp) he_le_y)
      have hmin :
          fexp e ≤
            min (FloatSpec.Core.Generic_fmt.cexp beta fexp x)
                (FloatSpec.Core.Generic_fmt.cexp beta fexp y) :=
        le_min hmono_x hmono_y
      unfold FloatSpec.Core.Generic_fmt.cexp
      exact le_trans hmono_xy (by simpa [hfxy_exp] using hmin)
    have hfmt :=
      (FloatSpec.Core.Generic_fmt.generic_format_F2R' (beta := beta) (fexp := fexp)
        (x := x + y) (f := fxy)) ⟨hβ, hfxy_eq, fun _ => hcexp_le⟩
    simpa [generic_format, Std.Do.PostCond.noThrow, wp, pure] using hfmt
  · have h_abs_fmt : generic_format beta fexp |x + y| := by
      rw [heq_abs]
      exact hfmt_bpow
    exact
      (FloatSpec.Core.Generic_fmt.generic_format_abs_inv (beta := beta) (fexp := fexp)
        (x := x + y)) h_abs_fmt

/-- Generic format plus weak condition -/
theorem generic_format_plus_weak (x y : ℝ)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (hβ : 1 < beta)
  (h_bound : |x + y| ≤ min (|x|) (|y|)) :
  generic_format beta fexp (x + y) := by
  classical
  by_cases hx0 : x = 0
  · simpa [hx0, zero_add] using hy
  by_cases hy0 : y = 0
  · simpa [hy0, add_zero] using hx
  refine generic_format_plus (beta := beta) (fexp := fexp) x y hx hy hβ ?_
  by_cases hxy_abs : |x| ≤ |y|
  · have hmag_xy : mag beta x ≤ mag beta y := by
      exact FloatSpec.Core.Raux.mag_le_abs beta x y hβ hx0 hxy_abs
    have hmin_mag : min (mag beta x) (mag beta y) = mag beta x :=
      min_eq_left hmag_xy
    have hx_upper : |x| ≤ (beta : ℝ) ^ (min (mag beta x) (mag beta y)) := by
      have h :=
        FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := x) hβ hx0
      have hx_lt : |x| < (beta : ℝ) ^ (mag beta x) := by
        simpa [FloatSpec.Core.Raux.abs_val, Std.Do.PostCond.noThrow, wp, pure]
          using h trivial
      simpa [hmin_mag] using le_of_lt hx_lt
    have hmin_abs : min |x| |y| = |x| := min_eq_left hxy_abs
    exact le_trans h_bound (by simpa [hmin_abs] using hx_upper)
  · have hyx_abs : |y| ≤ |x| := le_of_lt (lt_of_not_ge hxy_abs)
    have hmag_yx : mag beta y ≤ mag beta x := by
      exact FloatSpec.Core.Raux.mag_le_abs beta y x hβ hy0 hyx_abs
    have hmin_mag : min (mag beta x) (mag beta y) = mag beta y :=
      min_eq_right hmag_yx
    have hy_upper : |y| ≤ (beta : ℝ) ^ (min (mag beta x) (mag beta y)) := by
      have h :=
        FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := y) hβ hy0
      have hy_lt : |y| < (beta : ℝ) ^ (mag beta y) := by
        simpa [FloatSpec.Core.Raux.abs_val, Std.Do.PostCond.noThrow, wp, pure]
          using h trivial
      simpa [hmin_mag] using le_of_lt hy_lt
    have hmin_abs : min |x| |y| = |y| := min_eq_right hyx_abs
    exact le_trans h_bound (by simpa [hmin_abs] using hy_upper)

/-- Sterbenz auxiliary lemma -/
lemma sterbenz_aux (x y : ℝ)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (hβ : 1 < beta)
  (h_bound : y ≤ x ∧ x ≤ 2 * y) :
  generic_format beta fexp (x - y) := by
  classical
  have hy_nonneg : 0 ≤ y := by
    have hy_le_2y : y ≤ 2 * y := le_trans h_bound.1 h_bound.2
    nlinarith
  have hx_nonneg : 0 ≤ x := le_trans hy_nonneg h_bound.1
  have hsub_nonneg : 0 ≤ x - y := sub_nonneg.mpr h_bound.1
  have hsub_le_y : x - y ≤ y := by nlinarith [h_bound.2]
  have hsub_le_x : x - y ≤ x := by nlinarith [hy_nonneg]
  have hy_opp : generic_format beta fexp (-y) := by
    have h := FloatSpec.Core.Generic_fmt.generic_format_opp
      (beta := beta) (fexp := fexp) (x := y)
    simpa [Std.Do.PostCond.noThrow, wp, pure] using h hy
  have hweak : |x + -y| ≤ min |x| |-y| := by
    have hsub_abs : |x + -y| = x - y := by
      simpa [sub_eq_add_neg] using abs_of_nonneg hsub_nonneg
    have hx_abs : |x| = x := abs_of_nonneg hx_nonneg
    have hy_abs : |-y| = y := by
      simpa [abs_neg] using abs_of_nonneg hy_nonneg
    exact le_min (by simpa [hsub_abs, hx_abs] using hsub_le_x)
      (by simpa [hsub_abs, hy_abs] using hsub_le_y)
  simpa [sub_eq_add_neg] using
    generic_format_plus_weak (beta := beta) (fexp := fexp) x (-y) hx hy_opp hβ hweak

/-- Sterbenz theorem for exact subtraction -/
theorem sterbenz (x y : ℝ)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (hβ : 1 < beta)
  (h_bound : y / 2 ≤ x ∧ x ≤ 2 * y) :
  generic_format beta fexp (x - y) := by
  classical
  rcases le_total x y with hxy | hyx
  · have hy_le_2x : y ≤ 2 * x := by
      nlinarith [h_bound.1]
    have hfmt_yx : generic_format beta fexp (y - x) :=
      sterbenz_aux (beta := beta) (fexp := fexp) y x hy hx hβ ⟨hxy, hy_le_2x⟩
    have hfmt_neg : generic_format beta fexp (-(y - x)) := by
      have h := FloatSpec.Core.Generic_fmt.generic_format_opp
        (beta := beta) (fexp := fexp) (x := y - x)
      simpa [Std.Do.PostCond.noThrow, wp, pure] using h hfmt_yx
    simpa [sub_eq_add_neg] using hfmt_neg
  · exact sterbenz_aux (beta := beta) (fexp := fexp) x y hx hy hβ ⟨hyx, h_bound.2⟩
