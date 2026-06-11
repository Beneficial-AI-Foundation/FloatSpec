import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Operations
import FloatSpec.src.Calc.Round
import FloatSpec.src.Prop.Relative
import FloatSpec.src.Prop.Sterbenz
import FloatSpec.src.Prop.Mult_error
import FloatSpec.src.Prop.Plus_error
import Mathlib.Data.Real.Basic

-- Remainder of the division and square root are in the FLX format
-- Translated from Coq file: flocq/src/Prop/Div_sqrt_error.v

open Real
open Std.Do

variable (beta : Int)
variable (prec : Int)
variable [Prec_gt_0 prec]

/-- Generic format plus with precision bound.

This mirrors Flocq `Div_sqrt_error.v` `generic_format_plus_prec`: the
two magnitude bounds are over signed `bpow` exponents, not `natAbs`
exponents. -/
lemma generic_format_plus_prec (fexp : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
  (h_bound : ∀ e, fexp e ≤ e - prec)
  (hβ : 1 < beta)
  (x y : ℝ) (fx fy : FloatSpec.Core.Defs.FlocqFloat beta)
  (hx : x = _root_.F2R fx) (hy : y = _root_.F2R fy)
  (h1 : |x + y| < (beta : ℝ) ^ (prec + fx.Fexp))
  (h2 : |x + y| < (beta : ℝ) ^ (prec + fy.Fexp)) :
  generic_format beta fexp (x + y) := by
  by_cases hz : x + y = 0
  · simpa [generic_format, hz] using
      (FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp))
  · let fxy : FloatSpec.Core.Defs.FlocqFloat beta :=
      FloatSpec.Calc.Operations.Fplus beta fx fy
    have hFplus :
        FloatSpec.Core.Defs.F2R fxy =
          FloatSpec.Core.Defs.F2R fx + FloatSpec.Core.Defs.F2R fy := by
      have h :=
        (FloatSpec.Calc.Operations.F2R_plus (beta := beta) fx fy) hβ
      simpa [fxy, Std.Do.PostCond.noThrow, wp, pure] using h
    have hfxy_eq : FloatSpec.Core.Defs.F2R fxy = x + y := by
      simpa [F2R, hx, hy] using hFplus
    have hfxy_exp : fxy.Fexp = min fx.Fexp fy.Fexp := by
      have h :=
        (FloatSpec.Calc.Operations.Fexp_Fplus_spec (beta := beta) fx fy) trivial
      simpa [fxy, FloatSpec.Calc.Operations.Fexp_Fplus,
        Std.Do.PostCond.noThrow, wp, pure] using h
    have hmag_x :
        FloatSpec.Core.Raux.mag beta (x + y) ≤ prec + fx.Fexp := by
      have htrip :=
        FloatSpec.Core.Raux.mag_le_bpow (beta := beta) (x := x + y)
          (e := prec + fx.Fexp) hβ hz h1
      simpa [Std.Do.PostCond.noThrow, wp, pure] using htrip trivial
    have hmag_y :
        FloatSpec.Core.Raux.mag beta (x + y) ≤ prec + fy.Fexp := by
      have htrip :=
        FloatSpec.Core.Raux.mag_le_bpow (beta := beta) (x := x + y)
          (e := prec + fy.Fexp) hβ hz h2
      simpa [Std.Do.PostCond.noThrow, wp, pure] using htrip trivial
    have hcexp_le :
        FloatSpec.Core.Generic_fmt.cexp beta fexp (x + y) ≤ fxy.Fexp := by
      have hx_exp : FloatSpec.Core.Raux.mag beta (x + y) - prec ≤ fx.Fexp := by
        grind
      have hy_exp : FloatSpec.Core.Raux.mag beta (x + y) - prec ≤ fy.Fexp := by
        grind
      have hmin :
          FloatSpec.Core.Raux.mag beta (x + y) - prec ≤ min fx.Fexp fy.Fexp := by
        exact le_min hx_exp hy_exp
      unfold FloatSpec.Core.Generic_fmt.cexp
      exact le_trans (h_bound (FloatSpec.Core.Raux.mag beta (x + y)))
        (by simpa [hfxy_exp] using hmin)
    have hfmt :=
      (FloatSpec.Core.Generic_fmt.generic_format_F2R' (beta := beta) (fexp := fexp)
        (x := x + y) (f := fxy)) ⟨hβ, hfxy_eq, fun _ => hcexp_le⟩
    simpa [generic_format, Std.Do.PostCond.noThrow, wp, pure] using hfmt

variable (choice : Int → Bool)

/-- Remainder of the division in FLX -/
theorem div_error_FLX (rnd : ℝ → Int) [Valid_rnd rnd] (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLX_exp prec) x) (hy : generic_format beta (FLX_exp prec) y) :
  generic_format beta (FLX_exp prec)
    (x - FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd (x / y) * y) := by
  classical
  let fexp := FLX_exp prec
  let z := x / y
  let r := FloatSpec.Core.Generic_fmt.roundR beta fexp rnd z
  have hbpos : (0 : ℝ) < (beta : ℝ) := by
    have : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    exact_mod_cast this
  have hpow_pos (e : Int) : 0 < (beta : ℝ) ^ e := zpow_pos hbpos e
  have hprec_one : 1 ≤ prec := by
    exact (Int.add_one_le_iff).mpr (Prec_gt_0.pos : 0 < prec)
  have hround_zero :
      FloatSpec.Core.Generic_fmt.roundR beta fexp rnd 0 = 0 := by
    have hrnd0 : rnd (0 : ℝ) = (0 : Int) := by
      simpa using (FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int))
    simp [FloatSpec.Core.Generic_fmt.roundR, FloatSpec.Core.Generic_fmt.scaled_mantissa,
      hrnd0]
  by_cases hy0 : y = 0
  · simpa [r, z, fexp, hy0] using hx
  by_cases hx0 : x = 0
  · have hz0 : z = 0 := by simp [z, hx0]
    have hr0 : r = 0 := by simpa [r, hz0] using hround_zero
    have htarget :
        x - FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd (x / y) * y = 0 := by
      simp [hx0, hround_zero, fexp]
    simpa [htarget] using
      (FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp))
  have hz0 : z ≠ 0 := by
    intro hz
    have : x = 0 := by
      calc
        x = z * y := by
          simp [z, div_mul_cancel₀ x hy0]
        _ = 0 := by simp [hz]
    exact hx0 this
  let fx : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Raux.Ztrunc (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x))
      (FloatSpec.Core.Generic_fmt.cexp beta fexp x)
  let fy : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk
      (FloatSpec.Core.Raux.Ztrunc (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp y))
      (FloatSpec.Core.Generic_fmt.cexp beta fexp y)
  let fr : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk
      (rnd (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp z))
      (FloatSpec.Core.Generic_fmt.cexp beta fexp z)
  have hx_fx : x = _root_.F2R fx := by
    simpa [fx, generic_format, fexp] using hx
  have hy_fy : y = _root_.F2R fy := by
    simpa [fy, generic_format, fexp] using hy
  have hr_fr : r = _root_.F2R fr := by
    simp [r, fr, FloatSpec.Core.Generic_fmt.roundR, _root_.F2R,
      FloatSpec.Core.Defs.F2R]
  have hround_err :
      |r - z| < (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp z) := by
    let sm := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp z
    let c := FloatSpec.Core.Generic_fmt.cexp beta fexp z
    have hscaled :
        sm * (beta : ℝ) ^ c = z := by
      have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
        (beta := beta) (fexp := fexp) (x := z)
      simpa [sm, c, wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip hβ
    have hstep : |((rnd sm : Int) : ℝ) - sm| < (1 : ℝ) := by
      have hdu := FloatSpec.Core.Generic_fmt.Zrnd_DN_or_UP (rnd := rnd) sm
      have hcases : rnd sm = Int.floor sm ∨ rnd sm = Int.ceil sm := by
        simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using hdu True.intro
      rcases hcases with hfloor | hceil
      · have hle : ((Int.floor sm : Int) : ℝ) ≤ sm := Int.floor_le sm
        have hlt : sm < ((Int.floor sm : Int) : ℝ) + 1 := Int.lt_floor_add_one sm
        have hnonneg : 0 ≤ sm - ((Int.floor sm : Int) : ℝ) := by linarith
        have hlt1 : sm - ((Int.floor sm : Int) : ℝ) < 1 := by linarith
        calc
          |((rnd sm : Int) : ℝ) - sm|
              = |((Int.floor sm : Int) : ℝ) - sm| := by simp [hfloor]
          _ = sm - ((Int.floor sm : Int) : ℝ) := by
            rw [abs_sub_comm, abs_of_nonneg hnonneg]
          _ < 1 := hlt1
      · have hle : sm ≤ ((Int.ceil sm : Int) : ℝ) := Int.le_ceil sm
        have hlt : ((Int.ceil sm : Int) : ℝ) < sm + 1 := Int.ceil_lt_add_one sm
        have hnonneg : 0 ≤ ((Int.ceil sm : Int) : ℝ) - sm := by linarith
        have hlt1 : ((Int.ceil sm : Int) : ℝ) - sm < 1 := by linarith
        calc
          |((rnd sm : Int) : ℝ) - sm|
              = |((Int.ceil sm : Int) : ℝ) - sm| := by simp [hceil]
          _ = ((Int.ceil sm : Int) : ℝ) - sm := by
            rw [abs_of_nonneg hnonneg]
          _ < 1 := hlt1
    have hpowc : 0 < (beta : ℝ) ^ c := hpow_pos c
    have herr_eq :
        r - z = (((rnd sm : Int) : ℝ) - sm) * (beta : ℝ) ^ c := by
      calc
        r - z
            = ((rnd sm : Int) : ℝ) * (beta : ℝ) ^ c
                - sm * (beta : ℝ) ^ c := by
                  simp [r, FloatSpec.Core.Generic_fmt.roundR, sm, c, hscaled]
        _ = (((rnd sm : Int) : ℝ) - sm) * (beta : ℝ) ^ c := by ring
    calc
      |r - z|
          = |(((rnd sm : Int) : ℝ) - sm) * (beta : ℝ) ^ c| := by rw [herr_eq]
      _ = |((rnd sm : Int) : ℝ) - sm| * (beta : ℝ) ^ c := by
        rw [abs_mul, abs_of_pos hpowc]
      _ < 1 * (beta : ℝ) ^ c := mul_lt_mul_of_pos_right hstep hpowc
      _ = (beta : ℝ) ^ c := by ring
  have hround_err_le_abs :
      |r - z| < |z| := by
    have hmag_lower :
        (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta z - 1) ≤ |z| := by
      have htrip := FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := z) hβ hz0
      simpa [FloatSpec.Core.Raux.abs_val, wp, Std.Do.PostCond.noThrow, Id.run, pure]
        using htrip True.intro
    have hcexp_le_mag_sub_one :
        FloatSpec.Core.Generic_fmt.cexp beta fexp z ≤ FloatSpec.Core.Raux.mag beta z - 1 := by
      simp [FloatSpec.Core.Generic_fmt.cexp, fexp, FLX_exp, FloatSpec.Core.FLX.FLX_exp]
      linarith
    have hpow_le :
        (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp z)
          ≤ (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta z - 1) := by
      have htrip := FloatSpec.Core.Raux.bpow_le (beta := beta)
        (e1 := FloatSpec.Core.Generic_fmt.cexp beta fexp z)
        (e2 := FloatSpec.Core.Raux.mag beta z - 1) hβ hcexp_le_mag_sub_one
      simpa [FloatSpec.Core.Raux.bpow_le_check, wp, Std.Do.PostCond.noThrow, Id.run, pure]
        using htrip True.intro
    exact lt_of_lt_of_le hround_err (le_trans hpow_le hmag_lower)
  have hrem_abs :
      |x + -(r * y)| = |r - z| * |y| := by
    have hxy : x = z * y := by
      simp [z, div_mul_cancel₀ x hy0]
    calc
      |x + -(r * y)| = |-(r - z) * y| := by
        rw [hxy]
        ring
      _ = |r - z| * |y| := by rw [abs_mul, abs_neg]
  have hx_bound :
      |x + -(r * y)| < (beta : ℝ) ^ (prec + fx.Fexp) := by
    have hy_abs_pos : 0 < |y| := abs_pos.mpr hy0
    have hlt_x : |x + -(r * y)| < |z| * |y| := by
      rw [hrem_abs]
      exact mul_lt_mul_of_pos_right hround_err_le_abs hy_abs_pos
    have hz_mul : |z| * |y| = |x| := by
      calc
        |z| * |y| = |z * y| := by rw [abs_mul]
        _ = |x| := by
          have hxy : z * y = x := by simp [z, div_mul_cancel₀ x hy0]
          rw [hxy]
    have hx_mag :
        |x| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) := by
      have htrip := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := x) hβ hx0
      simpa [FloatSpec.Core.Raux.abs_val, wp, Std.Do.PostCond.noThrow, Id.run, pure]
        using htrip True.intro
    have hx_exp :
        FloatSpec.Core.Generic_fmt.cexp beta fexp x ≤ fx.Fexp := by
      simp [fx]
    have hmag_to_fx :
        FloatSpec.Core.Raux.mag beta x ≤ prec + fx.Fexp := by
      simp [FloatSpec.Core.Generic_fmt.cexp, fexp, FLX_exp, FloatSpec.Core.FLX.FLX_exp] at hx_exp
      linarith
    have hpow_le :
        (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x)
          ≤ (beta : ℝ) ^ (prec + fx.Fexp) := by
      have htrip := FloatSpec.Core.Raux.bpow_le (beta := beta)
        (e1 := FloatSpec.Core.Raux.mag beta x) (e2 := prec + fx.Fexp) hβ hmag_to_fx
      simpa [FloatSpec.Core.Raux.bpow_le_check, wp, Std.Do.PostCond.noThrow, Id.run, pure]
        using htrip True.intro
    exact lt_of_lt_of_le (lt_of_lt_of_eq hlt_x hz_mul) (lt_of_lt_of_le hx_mag hpow_le).le
  have hy_bound :
      |x + -(r * y)| < (beta : ℝ) ^ (prec + (FloatSpec.Calc.Operations.Fopp beta
        (FloatSpec.Calc.Operations.Fmult beta fr fy)).Fexp) := by
    have hy_abs_pos : 0 < |y| := abs_pos.mpr hy0
    have hlt_y :
        |x + -(r * y)|
          < (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp z) * |y| := by
      rw [hrem_abs]
      exact mul_lt_mul_of_pos_right hround_err hy_abs_pos
    have hy_mag :
        |y| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := by
      have htrip := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := y) hβ hy0
      simpa [FloatSpec.Core.Raux.abs_val, wp, Std.Do.PostCond.noThrow, Id.run, pure]
        using htrip True.intro
    have hprod_lt :
        (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp z) * |y|
          < (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp z)
              * (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := by
      exact mul_lt_mul_of_pos_left hy_mag
        (hpow_pos (FloatSpec.Core.Generic_fmt.cexp beta fexp z))
    have hpow_eq :
        (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp z)
            * (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y)
          = (beta : ℝ) ^ (prec + (FloatSpec.Calc.Operations.Fopp beta
              (FloatSpec.Calc.Operations.Fmult beta fr fy)).Fexp) := by
      have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
      calc
        (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp z)
            * (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y)
            = (beta : ℝ) ^
                (FloatSpec.Core.Generic_fmt.cexp beta fexp z
                  + FloatSpec.Core.Raux.mag beta y) := by
                exact (zpow_add₀ hbne
                  (FloatSpec.Core.Generic_fmt.cexp beta fexp z)
                  (FloatSpec.Core.Raux.mag beta y)).symm
        _ = (beta : ℝ) ^ (prec + (FloatSpec.Calc.Operations.Fopp beta
              (FloatSpec.Calc.Operations.Fmult beta fr fy)).Fexp) := by
          congr 1
          simp [FloatSpec.Calc.Operations.Fopp, FloatSpec.Calc.Operations.Fmult, fr, fy,
            FloatSpec.Core.Generic_fmt.cexp, fexp, FLX_exp, FloatSpec.Core.FLX.FLX_exp]
          ring
    exact lt_of_lt_of_eq (lt_trans hlt_y hprod_lt) hpow_eq
  have hsecond :
      -(r * y) = _root_.F2R (FloatSpec.Calc.Operations.Fopp beta
        (FloatSpec.Calc.Operations.Fmult beta fr fy)) := by
    have hmult :
        _root_.F2R (FloatSpec.Calc.Operations.Fmult beta fr fy)
          = _root_.F2R fr * _root_.F2R fy := by
      have htrip := FloatSpec.Calc.Operations.F2R_mult (beta := beta) fr fy
      simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip hβ
    have hopp :
        _root_.F2R (FloatSpec.Calc.Operations.Fopp beta
          (FloatSpec.Calc.Operations.Fmult beta fr fy))
          = -_root_.F2R (FloatSpec.Calc.Operations.Fmult beta fr fy) := by
      have htrip := FloatSpec.Calc.Operations.F2R_opp (beta := beta)
        (FloatSpec.Calc.Operations.Fmult beta fr fy)
      simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip True.intro
    rw [hopp, hmult, ← hr_fr, ← hy_fy]
  have hfmt :=
    generic_format_plus_prec (beta := beta) (prec := prec) (fexp := fexp)
      (h_bound := by intro e; simp [fexp, FLX_exp, FloatSpec.Core.FLX.FLX_exp])
      hβ x (-(r * y)) fx
      (FloatSpec.Calc.Operations.Fopp beta (FloatSpec.Calc.Operations.Fmult beta fr fy))
      hx_fx hsecond hx_bound hy_bound
  simpa [sub_eq_add_neg, r, fexp] using hfmt

/-- Remainder of the square in FLX (with p > 1) and rounding to nearest -/
theorem sqrt_error_FLX_N (h_gt1 : 1 < prec) (x : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLX_exp prec) x) :
  generic_format beta (FLX_exp prec)
    (x - (FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec)
      (FloatSpec.Core.Generic_fmt.Znearest choice) (Real.sqrt x))^2) := by
  classical
  let fexp := FLX_exp prec
  let r := FloatSpec.Core.Generic_fmt.roundR beta fexp
    (FloatSpec.Core.Generic_fmt.Znearest choice) (Real.sqrt x)
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  have hround_zero :
      FloatSpec.Core.Generic_fmt.roundR beta fexp
        (FloatSpec.Core.Generic_fmt.Znearest choice) 0 = 0 := by
    have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
      unfold FloatSpec.Core.Generic_fmt.Znearest
      simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil,
        FloatSpec.Core.Raux.Rcompare]
    simp [FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, hZ0]
  by_cases hx_nonpos : x ≤ 0
  · have hsqrt0 : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos hx_nonpos
    have hr0 : r = 0 := by simpa [r, hsqrt0] using hround_zero
    have htarget :
        x - (FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec)
          (FloatSpec.Core.Generic_fmt.Znearest choice) (Real.sqrt x)) ^ 2 = x := by
      simp [r, fexp, hr0]
    simpa [htarget, fexp] using hx
  · have hxpos : 0 < x := lt_of_not_ge hx_nonpos
    have hxne : x ≠ 0 := ne_of_gt hxpos
    by_cases hr0 : r = 0
    · have htarget :
          x - (FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec)
            (FloatSpec.Core.Generic_fmt.Znearest choice) (Real.sqrt x)) ^ 2 = x := by
        simp [r, fexp, hr0]
      simpa [htarget, fexp] using hx
    · haveI : FloatSpec.Core.Ulp.Exp_not_FTZ fexp := by
        refine ⟨?_⟩
        intro e
        have hprec_nonneg : 0 ≤ prec := le_of_lt (lt_trans Int.zero_lt_one h_gt1)
        simp [fexp, FLX_exp, FloatSpec.Core.FLX.FLX_exp]
        omega
      haveI : FloatSpec.Core.Ulp.Monotone_exp fexp := by
        refine ⟨?_⟩
        intro a b hab
        simp [fexp, FLX_exp, FloatSpec.Core.FLX.FLX_exp]
        omega
      let fx : FloatSpec.Core.Defs.FlocqFloat beta :=
        FloatSpec.Core.Defs.FlocqFloat.mk
          (FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x))
          (FloatSpec.Core.Generic_fmt.cexp beta fexp x)
      let fr : FloatSpec.Core.Defs.FlocqFloat beta :=
        FloatSpec.Core.Defs.FlocqFloat.mk
          (FloatSpec.Core.Raux.Ztrunc
            (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp r))
          (FloatSpec.Core.Generic_fmt.cexp beta fexp r)
      have hx_fx : x = _root_.F2R fx := by
        simpa [fx, generic_format, fexp] using hx
      have hr_fmt : generic_format beta fexp r :=
        FloatSpec.Core.Generic_fmt.generic_format_roundR
          (beta := beta) (fexp := fexp)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice)
          (x := Real.sqrt x) hβ
      have hr_fr : r = _root_.F2R fr := by
        simpa [fr, generic_format, fexp] using hr_fmt
      have hsqrt_ne : Real.sqrt x ≠ 0 := by
        exact ne_of_gt (Real.sqrt_pos.2 hxpos)
      have hpow_le_quarter :
          (1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1) ≤ (1 / 4 : ℝ) := by
        have hle_exp : -prec + 1 ≤ (-1 : Int) := by omega
        have hpow_le :
            (beta : ℝ) ^ (-prec + 1) ≤ (beta : ℝ) ^ (-1 : Int) := by
          have htrip := FloatSpec.Core.Raux.bpow_le beta (-prec + 1) (-1) hβ hle_exp
          simpa [FloatSpec.Core.Raux.bpow_le_check, wp, Std.Do.PostCond.noThrow,
            Id.run, pure] using htrip True.intro
        have hβ2ℤ : (2 : Int) ≤ beta := by omega
        have hβ2 : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hβ2ℤ
        have hpow_neg_one : (beta : ℝ) ^ (-1 : Int) ≤ (1 / 2 : ℝ) := by
          rw [zpow_neg, zpow_one]
          simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hβ2)
        have hpow_half : (beta : ℝ) ^ (-prec + 1) ≤ (1 / 2 : ℝ) :=
          le_trans hpow_le hpow_neg_one
        nlinarith
      have hrel_bound :
          |r - Real.sqrt x| ≤
            ((1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1)) * |Real.sqrt x| := by
        set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp (Real.sqrt x) with he
        set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp (Real.sqrt x) with hsm
        set zn : Int := FloatSpec.Core.Generic_fmt.Znearest choice sm with hzn
        have hpow_nonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt (zpow_pos hbpos e)
        have hscaled : sm * (beta : ℝ) ^ e = Real.sqrt x := by
          have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
            (beta := beta) (fexp := fexp) (x := Real.sqrt x)
          simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, hsm, e, he]
            using htrip hβ
        have hround :
            r = (zn : ℝ) * (beta : ℝ) ^ e := by
          simp [r, FloatSpec.Core.Generic_fmt.roundR, sm, hsm, e, he, zn, hzn]
        have hnearest : |(zn : ℝ) - sm| ≤ (1 / 2 : ℝ) := by
          have htrip :=
            (FloatSpec.Core.Generic_fmt.Znearest_half_theorem choice sm) True.intro
          simpa [FloatSpec.Core.Generic_fmt.Znearest_half_check,
            FloatSpec.Core.Generic_fmt.Znearest_N_strict_check, zn, hzn,
            abs_sub_comm, wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip
        have hlocal :
            |r - Real.sqrt x| ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ e := by
          have hdiff : r - Real.sqrt x = ((zn : ℝ) - sm) * (beta : ℝ) ^ e := by
            rw [hround, ← hscaled]
            ring
          rw [hdiff, abs_mul, abs_of_nonneg hpow_nonneg]
          exact mul_le_mul_of_nonneg_right hnearest hpow_nonneg
        have hulp_sqrt :
            FloatSpec.Core.Ulp.ulp beta fexp (Real.sqrt x) = (beta : ℝ) ^ e := by
          have htrip := FloatSpec.Core.Ulp.ulp_neq_0
            (beta := beta) (fexp := fexp) (x := Real.sqrt x) hsqrt_ne
          simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure, e, he] using htrip True.intro
        have hpow_le_abs :
            (beta : ℝ) ^ e ≤ |Real.sqrt x| * (beta : ℝ) ^ (1 - prec) := by
          have htrip := FloatSpec.Core.FLX.ulp_FLX_le
            (prec := prec) (beta := beta) (x := Real.sqrt x)
          have hplain :
              FloatSpec.Core.Ulp.ulp beta fexp (Real.sqrt x)
                ≤ |Real.sqrt x| * (beta : ℝ) ^ (1 - prec) := by
            simpa [fexp, FLX_exp, wp, Std.Do.PostCond.noThrow, Id.run, pure]
              using htrip hβ
          simpa [hulp_sqrt] using hplain
        have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
        have hscaled_bound :
            (1 / 2 : ℝ) * (beta : ℝ) ^ e
              ≤ (1 / 2 : ℝ) * (|Real.sqrt x| * (beta : ℝ) ^ (1 - prec)) :=
          mul_le_mul_of_nonneg_left hpow_le_abs hhalf_nonneg
        exact le_trans hlocal (by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
            mul_left_comm, mul_assoc] using hscaled_bound)
      let eps : ℝ := (r - Real.sqrt x) / Real.sqrt x
      have heps : |eps| ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1) := by
        have hsqrt_abs_pos : 0 < |Real.sqrt x| := abs_pos.mpr hsqrt_ne
        have hdiv := div_le_div_of_nonneg_right hrel_bound (le_of_lt hsqrt_abs_pos)
        have hrhs :
            (((1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1)) * |Real.sqrt x|)
                / |Real.sqrt x|
              = (1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1) := by
          field_simp [ne_of_gt hsqrt_abs_pos]
        have hratio :
            |r - Real.sqrt x| / |Real.sqrt x|
              ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1) := by
          calc
            |r - Real.sqrt x| / |Real.sqrt x|
                ≤ (((1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1)) * |Real.sqrt x|)
                    / |Real.sqrt x| := hdiv
            _ = (1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1) := hrhs
        simpa [eps, abs_div] using hratio
      have hr_eps :
          r = Real.sqrt x * (1 + eps) := by
        calc
          r = Real.sqrt x + (r - Real.sqrt x) := by ring
          _ = Real.sqrt x * (1 + eps) := by
            simp [eps]
            field_simp [hsqrt_ne]
            ring
      have heps_quarter : |eps| ≤ (1 / 4 : ℝ) :=
        le_trans heps hpow_le_quarter
      have h_one_eps_abs : |1 + eps| ≤ (5 / 4 : ℝ) := by
        have htri : |1 + eps| ≤ (1 : ℝ) + |eps| := by
          simpa using (abs_add_le (1 : ℝ) eps)
        nlinarith [htri, heps_quarter]
      have h_one_eps_sq : (1 + eps) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := by
        have hfive : |(5 / 4 : ℝ)| = (5 / 4 : ℝ) := by norm_num
        exact sq_le_sq.mpr (by simpa [hfive] using h_one_eps_abs)
      have hsqrt_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hxpos)
      have hr_sq_le : r ^ 2 ≤ 2 * x := by
        have hr_sq_eq : r ^ 2 = x * (1 + eps) ^ 2 := by
          rw [hr_eps]
          rw [mul_pow, hsqrt_sq]
        calc
          r ^ 2 = x * (1 + eps) ^ 2 := hr_sq_eq
          _ ≤ x * (5 / 4 : ℝ) ^ 2 := by
            exact mul_le_mul_of_nonneg_left h_one_eps_sq (le_of_lt hxpos)
          _ ≤ 2 * x := by nlinarith
      have hrem_le_x :
          |x - r ^ 2| ≤ x := by
        rw [abs_le]
        constructor
        · nlinarith [hr_sq_le]
        · nlinarith [sq_nonneg r]
      have hx_bound :
          x < (beta : ℝ) ^ (prec + fx.Fexp) := by
        have hmag :=
          FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := x) hβ hxne
        have hmag_plain : |x| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) := by
          simpa [FloatSpec.Core.Raux.abs_val, wp, Std.Do.PostCond.noThrow,
            Id.run, pure] using hmag True.intro
        have hexp : prec + fx.Fexp = FloatSpec.Core.Raux.mag beta x := by
          simp [fx, FloatSpec.Core.Generic_fmt.cexp, fexp, FLX_exp,
            FloatSpec.Core.FLX.FLX_exp]
        simpa [abs_of_pos hxpos, hexp] using hmag_plain
      have hfirst :
          |x - r ^ 2| < (beta : ℝ) ^ (prec + fx.Fexp) :=
        lt_of_le_of_lt hrem_le_x hx_bound
      have hfr_abs_bound :
          |r| < (beta : ℝ) ^ (prec + fr.Fexp) := by
        have hmag :=
          FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := r) hβ hr0
        have hmag_plain : |r| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta r) := by
          simpa [FloatSpec.Core.Raux.abs_val, wp, Std.Do.PostCond.noThrow,
            Id.run, pure] using hmag True.intro
        have hexp : prec + fr.Fexp = FloatSpec.Core.Raux.mag beta r := by
          simp [fr, FloatSpec.Core.Generic_fmt.cexp, fexp, FLX_exp,
            FloatSpec.Core.FLX.FLX_exp]
        simpa [hexp] using hmag_plain
      have hsqrt_abs_bound :
          |Real.sqrt x| ≤ (beta : ℝ) ^ (prec + fr.Fexp) := by
        by_contra hnot
        have hgt :
            prec + fr.Fexp < FloatSpec.Core.Raux.mag beta (Real.sqrt x) := by
          by_contra hnot_gt
          have hle_exp :
              FloatSpec.Core.Raux.mag beta (Real.sqrt x) ≤ prec + fr.Fexp :=
            le_of_not_gt hnot_gt
          have hle_mag : |Real.sqrt x| <
              (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) := by
            have hmag := FloatSpec.Core.Raux.mag_upper_bound
              (beta := beta) (x := Real.sqrt x) hβ hsqrt_ne
            simpa [FloatSpec.Core.Raux.abs_val, wp, Std.Do.PostCond.noThrow,
              Id.run, pure] using hmag True.intro
          have hpow_le :
              (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta (Real.sqrt x))
                ≤ (beta : ℝ) ^ (prec + fr.Fexp) := by
            have htrip := FloatSpec.Core.Raux.bpow_le beta
              (FloatSpec.Core.Raux.mag beta (Real.sqrt x)) (prec + fr.Fexp) hβ hle_exp
            simpa [FloatSpec.Core.Raux.bpow_le_check, wp, Std.Do.PostCond.noThrow,
              Id.run, pure] using htrip True.intro
          exact hnot (le_trans (le_of_lt hle_mag) hpow_le)
        let g : ℝ :=
          (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta (Real.sqrt x) - 1)
        have hg_format : generic_format beta fexp g := by
          have hpre :
              fexp (FloatSpec.Core.Raux.mag beta (Real.sqrt x) - 1)
                ≤ FloatSpec.Core.Raux.mag beta (Real.sqrt x) - 1 := by
            have hprec_nonneg : 0 ≤ prec := le_of_lt (lt_trans Int.zero_lt_one h_gt1)
            simp [fexp, FLX_exp, FloatSpec.Core.FLX.FLX_exp]
            omega
          have htrip := FloatSpec.Core.Generic_fmt.generic_format_bpow'
            (beta := beta) (fexp := fexp)
            (e := FloatSpec.Core.Raux.mag beta (Real.sqrt x) - 1)
          simpa [g, wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip ⟨hβ, hpre⟩
        have hg_le_sqrt : g ≤ Real.sqrt x := by
          have hmag := FloatSpec.Core.Raux.mag_lower_bound
            (beta := beta) (x := Real.sqrt x) hβ hsqrt_ne
          have hplain :
              (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta (Real.sqrt x) - 1)
                ≤ |Real.sqrt x| := by
            simpa [FloatSpec.Core.Raux.abs_val, wp, Std.Do.PostCond.noThrow,
              Id.run, pure] using hmag True.intro
          simpa [g, abs_of_nonneg (Real.sqrt_nonneg x)] using hplain
        have hg_le_r : g ≤ r :=
          FloatSpec.Core.Generic_fmt.roundR_ge_generic
            (beta := beta) (fexp := fexp)
            (rnd := FloatSpec.Core.Generic_fmt.Znearest choice)
            (x := g) (y := Real.sqrt x) hβ hg_format hg_le_sqrt
        have hg_le_abs_r : g ≤ |r| := le_trans hg_le_r (le_abs_self r)
        have hbound_le_g :
            (beta : ℝ) ^ (prec + fr.Fexp) ≤ g := by
          have hle_exp : prec + fr.Fexp ≤
              FloatSpec.Core.Raux.mag beta (Real.sqrt x) - 1 := by omega
          have htrip := FloatSpec.Core.Raux.bpow_le beta
            (prec + fr.Fexp)
            (FloatSpec.Core.Raux.mag beta (Real.sqrt x) - 1) hβ hle_exp
          simpa [g, FloatSpec.Core.Raux.bpow_le_check, wp,
            Std.Do.PostCond.noThrow, Id.run, pure] using htrip True.intro
        have hlt_abs_g : |r| < g := lt_of_lt_of_le hfr_abs_bound hbound_le_g
        exact (not_lt_of_ge hg_le_abs_r) hlt_abs_g
      have hsum_lt :
          |r + Real.sqrt x| < 2 * (beta : ℝ) ^ (prec + fr.Fexp) := by
        have htri : |r + Real.sqrt x| ≤ |r| + |Real.sqrt x| := abs_add_le r (Real.sqrt x)
        nlinarith [hfr_abs_bound, hsqrt_abs_bound]
      have hulp_r :
          FloatSpec.Core.Ulp.ulp beta fexp r = (beta : ℝ) ^ fr.Fexp := by
        have htrip := FloatSpec.Core.Ulp.ulp_neq_0
          (beta := beta) (fexp := fexp) (x := r) hr0
        simpa [fr, wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip True.intro
      have herr_half :
          |r - Real.sqrt x| ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ fr.Fexp := by
        have htrip := FloatSpec.Core.Ulp.error_le_half_ulp_round
          (beta := beta) (fexp := fexp) (choice := choice)
          (x := Real.sqrt x) hβ
        simpa [r, fexp, hulp_r, wp, Std.Do.PostCond.noThrow, Id.run, pure]
          using htrip hβ
      have hsecond_bound :
          |x - r ^ 2| <
            (beta : ℝ) ^ (prec + (FloatSpec.Calc.Operations.Fopp beta
              (FloatSpec.Calc.Operations.Fmult beta fr fr)).Fexp) := by
        have hdiff :
            x - r ^ 2 = -((r - Real.sqrt x) * (r + Real.sqrt x)) := by
          nth_rewrite 1 [← hsqrt_sq]
          ring
        have hprod_le :
            |(r - Real.sqrt x) * (r + Real.sqrt x)|
              ≤ ((1 / 2 : ℝ) * (beta : ℝ) ^ fr.Fexp)
                  * |r + Real.sqrt x| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right herr_half (abs_nonneg _)
        have hleft_pos : 0 < (1 / 2 : ℝ) * (beta : ℝ) ^ fr.Fexp := by
          exact mul_pos (by norm_num) (zpow_pos hbpos fr.Fexp)
        have hprod_lt :
            ((1 / 2 : ℝ) * (beta : ℝ) ^ fr.Fexp) * |r + Real.sqrt x|
              < ((1 / 2 : ℝ) * (beta : ℝ) ^ fr.Fexp)
                  * (2 * (beta : ℝ) ^ (prec + fr.Fexp)) :=
          mul_lt_mul_of_pos_left hsum_lt hleft_pos
        have hpow_eq :
            ((1 / 2 : ℝ) * (beta : ℝ) ^ fr.Fexp)
                  * (2 * (beta : ℝ) ^ (prec + fr.Fexp))
              = (beta : ℝ) ^ (prec + (fr.Fexp + fr.Fexp)) := by
          calc
            ((1 / 2 : ℝ) * (beta : ℝ) ^ fr.Fexp)
                  * (2 * (beta : ℝ) ^ (prec + fr.Fexp))
                = (beta : ℝ) ^ fr.Fexp
                    * (beta : ℝ) ^ (prec + fr.Fexp) := by ring
            _ = (beta : ℝ) ^ (fr.Fexp + (prec + fr.Fexp)) := by
              exact (zpow_add₀ hbne fr.Fexp (prec + fr.Fexp)).symm
            _ = (beta : ℝ) ^ (prec + (fr.Fexp + fr.Fexp)) := by
              congr 1
              ring
        have hmain :
            |x - r ^ 2| <
              (beta : ℝ) ^ (prec + (fr.Fexp + fr.Fexp)) := by
          rw [hdiff, abs_neg]
          exact lt_of_le_of_lt hprod_le (by
            calc
              ((1 / 2 : ℝ) * (beta : ℝ) ^ fr.Fexp) * |r + Real.sqrt x|
                  < ((1 / 2 : ℝ) * (beta : ℝ) ^ fr.Fexp)
                      * (2 * (beta : ℝ) ^ (prec + fr.Fexp)) := hprod_lt
              _ = (beta : ℝ) ^ (prec + (fr.Fexp + fr.Fexp)) := hpow_eq)
        simpa [FloatSpec.Calc.Operations.Fopp, FloatSpec.Calc.Operations.Fmult]
          using hmain
      have hsecond :
          -(r * r) = _root_.F2R (FloatSpec.Calc.Operations.Fopp beta
            (FloatSpec.Calc.Operations.Fmult beta fr fr)) := by
        have hmult :
            _root_.F2R (FloatSpec.Calc.Operations.Fmult beta fr fr)
              = _root_.F2R fr * _root_.F2R fr := by
          have htrip := FloatSpec.Calc.Operations.F2R_mult (beta := beta) fr fr
          simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip hβ
        have hopp :
            _root_.F2R (FloatSpec.Calc.Operations.Fopp beta
              (FloatSpec.Calc.Operations.Fmult beta fr fr))
              = -_root_.F2R (FloatSpec.Calc.Operations.Fmult beta fr fr) := by
          have htrip := FloatSpec.Calc.Operations.F2R_opp (beta := beta)
            (FloatSpec.Calc.Operations.Fmult beta fr fr)
          simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip True.intro
        rw [hopp, hmult, ← hr_fr]
      have hfmt :=
        generic_format_plus_prec (beta := beta) (prec := prec) (fexp := fexp)
          (h_bound := by intro e; simp [fexp, FLX_exp, FloatSpec.Core.FLX.FLX_exp])
          hβ x (-(r * r)) fx
          (FloatSpec.Calc.Operations.Fopp beta (FloatSpec.Calc.Operations.Fmult beta fr fr))
          hx_fx hsecond
          (by simpa [pow_two, sub_eq_add_neg] using hfirst)
          (by simpa [pow_two, sub_eq_add_neg] using hsecond_bound)
      have htarget :
          x + -(r * r) =
            x - (FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec)
              (FloatSpec.Core.Generic_fmt.Znearest choice) (Real.sqrt x)) ^ 2 := by
        simp [r, fexp, pow_two]
        ring
      simpa [sub_eq_add_neg, r, fexp, pow_two] using hfmt

/-- Auxiliary decomposition for sqrt error in FLX: represent x as mu · β^(2e)
    with mu between 1 and β^2. -/
lemma sqrt_error_N_FLX_aux1 (x : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLX_exp prec) x) (px : 0 < x) :
  ∃ (mu : ℝ) (e : Int),
    generic_format beta (FLX_exp prec) mu ∧
    x = mu * (beta : ℝ) ^ (2 * e) ∧
    (1 ≤ mu ∧ mu < (beta : ℝ) ^ (2 : Int)) := by
  classical
  set m : Int := FloatSpec.Core.Raux.mag beta x with hm
  set e : Int := (m - 1) / 2 with he
  set mu : ℝ := x * (beta : ℝ) ^ (-2 * e) with hmu
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposℝ : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposℝ
  have hx_ne : x ≠ 0 := ne_of_gt px
  have hfmt_mu : generic_format beta (FLX_exp prec) mu := by
    have hfmt := mult_bpow_exact_FLX (beta := beta) (prec := prec)
      (x := x) (e := -2 * e) hβ hx
    simpa [mu, hmu, FloatSpec.Core.Raux.bpow] using hfmt
  refine ⟨mu, e, hfmt_mu, ?_, ?_⟩
  · calc
      x = x * 1 := by ring
      _ = x * ((beta : ℝ) ^ (-2 * e) * (beta : ℝ) ^ (2 * e)) := by
        rw [← zpow_add₀ hbne (-2 * e) (2 * e)]
        have hzero : -2 * e + 2 * e = 0 := by ring
        simp [hzero]
      _ = mu * (beta : ℝ) ^ (2 * e) := by
        simp [mu, hmu]
        ring
  · have hbp_pos : 0 < (beta : ℝ) ^ (2 * e) := zpow_pos hbposℝ _
    have hmu_mul :
        mu * (beta : ℝ) ^ (2 * e) = x := by
      exact (by
        calc
          mu * (beta : ℝ) ^ (2 * e)
              = x * ((beta : ℝ) ^ (-2 * e) * (beta : ℝ) ^ (2 * e)) := by
                simp [mu, hmu]
                ring
          _ = x * (beta : ℝ) ^ (-2 * e + 2 * e) := by
                rw [zpow_add₀ hbne (-2 * e) (2 * e)]
          _ = x := by
                have hzero : -2 * e + 2 * e = 0 := by ring
                simp [hzero])
    have hdecomp : 2 * ((m - 1) / 2) + (m - 1) % 2 = m - 1 :=
      Int.mul_ediv_add_emod (m - 1) 2
    have hmod_nonneg : 0 ≤ (m - 1) % 2 :=
      Int.emod_nonneg (m - 1) (by decide : (2 : Int) ≠ 0)
    have hmod_lt : (m - 1) % 2 < 2 :=
      Int.emod_lt_of_pos (m - 1) (by decide : (0 : Int) < 2)
    have h2e_le : 2 * e ≤ m - 1 := by
      have : 2 * e = 2 * ((m - 1) / 2) := by simp [e, he]
      omega
    have hm_le_2e_plus2 : m ≤ 2 + 2 * e := by
      have : 2 * e = 2 * ((m - 1) / 2) := by simp [e, he]
      omega
    have hlower_mag : (beta : ℝ) ^ (m - 1) ≤ x := by
      have htrip := FloatSpec.Core.Raux.mag_lower_bound
        (beta := beta) (x := x) hβ hx_ne
      have hrun : (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) ≤ |x| := by
        simpa [FloatSpec.Core.Raux.abs_val, wp, Std.Do.PostCond.noThrow,
          Id.run, pure] using htrip trivial
      simpa [hm, abs_of_pos px] using hrun
    have hupper_mag : x < (beta : ℝ) ^ m := by
      have htrip := FloatSpec.Core.Raux.mag_upper_bound
        (beta := beta) (x := x) hβ hx_ne
      have hrun : |x| < (beta : ℝ) ^ FloatSpec.Core.Raux.mag beta x := by
        simpa [FloatSpec.Core.Raux.abs_val, wp, Std.Do.PostCond.noThrow,
          Id.run, pure] using htrip trivial
      simpa [hm, abs_of_pos px] using hrun
    constructor
    · have hpow_le :
          (beta : ℝ) ^ (2 * e) ≤ (beta : ℝ) ^ (m - 1) := by
        have htrip := FloatSpec.Core.Raux.bpow_le beta (2 * e) (m - 1) hβ h2e_le
        simpa [FloatSpec.Core.Raux.bpow_le_check, wp, Std.Do.PostCond.noThrow,
          Id.run, pure] using htrip trivial
      have hmul_le : 1 * (beta : ℝ) ^ (2 * e) ≤ mu * (beta : ℝ) ^ (2 * e) := by
        calc
          1 * (beta : ℝ) ^ (2 * e) = (beta : ℝ) ^ (2 * e) := by ring
          _ ≤ (beta : ℝ) ^ (m - 1) := hpow_le
          _ ≤ x := hlower_mag
          _ = mu * (beta : ℝ) ^ (2 * e) := hmu_mul.symm
      exact le_of_mul_le_mul_right hmul_le hbp_pos
    · have hpow_upper :
          (beta : ℝ) ^ m ≤ (beta : ℝ) ^ (2 + 2 * e) := by
        have htrip := FloatSpec.Core.Raux.bpow_le beta m (2 + 2 * e) hβ hm_le_2e_plus2
        simpa [FloatSpec.Core.Raux.bpow_le_check, wp, Std.Do.PostCond.noThrow,
          Id.run, pure] using htrip trivial
      have hmul_lt : mu * (beta : ℝ) ^ (2 * e) <
          (beta : ℝ) ^ (2 : Int) * (beta : ℝ) ^ (2 * e) := by
        calc
          mu * (beta : ℝ) ^ (2 * e) = x := hmu_mul
          _ < (beta : ℝ) ^ m := hupper_mag
          _ ≤ (beta : ℝ) ^ (2 + 2 * e) := hpow_upper
          _ = (beta : ℝ) ^ (2 : Int) * (beta : ℝ) ^ (2 * e) := by
            rw [zpow_add₀ hbne (2 : Int) (2 * e)]
      exact lt_of_mul_lt_mul_right hmul_lt (le_of_lt hbp_pos)

/-- Auxiliary bound cases for sqrt error in FLX.
    If `x ≥ 1` and is in FLX format, then `x` is either exactly `1`, or exactly `1 + 2·u_ro`,
    or at least `1 + 4·u_ro`. -/
lemma sqrt_error_N_FLX_aux2 (x : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLX_exp prec) x) (hx_ge1 : 1 ≤ x) :
  x = 1 ∨ x = 1 + 2 * u_ro beta prec ∨ 1 + 4 * u_ro beta prec ≤ x := by
  classical
  have hu : 0 ≤ u_ro beta prec := u_ro_pos (beta := beta) (prec := prec) hβ
  rcases lt_or_eq_of_le hx_ge1 with hx_gt1 | hx_eq1
  · right
    have hF1 : generic_format beta (FLX_exp prec) (1 : ℝ) := by
      have htrip := FloatSpec.Core.FLX.generic_format_FLX_1 (prec := prec) (beta := beta)
      simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip hβ
    have h2u : 2 * u_ro beta prec = (beta : ℝ) ^ (1 - prec) := by
      unfold u_ro
      have hexp : -prec + 1 = 1 - prec := by ring
      rw [hexp]
      ring
    have hsucc1 :
        FloatSpec.Core.Ulp.succ beta (FLX_exp prec) 1 =
          1 + 2 * u_ro beta prec := by
      have htrip := FloatSpec.Core.FLX.succ_FLX_1 (prec := prec) (beta := beta)
      have hrun : FloatSpec.Core.Ulp.succ beta (FLX_exp prec) 1 =
          1 + (beta : ℝ) ^ (1 - prec) := by
        simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip hβ
      simpa [h2u] using hrun
    have hfirst_lower : 1 + 2 * u_ro beta prec ≤ x := by
      have htrip := FloatSpec.Core.Ulp.succ_le_lt
        (beta := beta) (fexp := FLX_exp prec) (x := 1) (y := x)
        hF1 hx hx_gt1
      simpa [hsucc1, wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip hβ
    rcases le_or_gt x (1 + 2 * u_ro beta prec) with hx_le_mid | hx_gt_mid
    · left
      exact le_antisymm hx_le_mid hfirst_lower
    · right
      have hmid_fmt : generic_format beta (FLX_exp prec) (1 + 2 * u_ro beta prec) := by
        have htrip := FloatSpec.Core.Ulp.generic_format_succ
          (beta := beta) (fexp := FLX_exp prec) (x := 1) hF1 hβ
        have hrun : generic_format beta (FLX_exp prec)
            (FloatSpec.Core.Ulp.succ beta (FLX_exp prec) 1) := by
          simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip trivial
        simpa [hsucc1] using hrun
      have hsucc_mid_le_x :
          FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (1 + 2 * u_ro beta prec) ≤ x := by
        have htrip := FloatSpec.Core.Ulp.succ_le_lt
          (beta := beta) (fexp := FLX_exp prec)
          (x := 1 + 2 * u_ro beta prec) (y := x)
          hmid_fmt hx hx_gt_mid
        simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip hβ
      have hulp1 : FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) 1 =
          2 * u_ro beta prec := by
        have htrip := FloatSpec.Core.FLX.ulp_FLX_1 (prec := prec) (beta := beta)
        have hrun : FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) 1 =
            (beta : ℝ) ^ (1 - prec) := by
          simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip hβ
        simpa [h2u] using hrun
      have hulp_le_mid :
          2 * u_ro beta prec ≤
            FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (1 + 2 * u_ro beta prec) := by
        haveI : FloatSpec.Core.Ulp.Monotone_exp (FLX_exp prec) := ⟨by
          intro a b hab
          simpa [FLX_exp, FloatSpec.Core.FLX.FLX_exp, sub_eq_add_neg]
            using sub_le_sub_right hab prec⟩
        have hmid_ge1 : (1 : ℝ) ≤ 1 + 2 * u_ro beta prec := by nlinarith
        have htrip := FloatSpec.Core.Ulp.ulp_le_pos
          (beta := beta) (fexp := FLX_exp prec)
          (x := 1) (y := 1 + 2 * u_ro beta prec)
          (by norm_num : (0 : ℝ) ≤ 1) hmid_ge1 hβ
        have hrun : FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) 1 ≤
            FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (1 + 2 * u_ro beta prec) := by
          simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip trivial
        simpa [hulp1] using hrun
      have hsucc_mid_ge :
          1 + 4 * u_ro beta prec ≤
            FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (1 + 2 * u_ro beta prec) := by
        have hmid_nonneg : 0 ≤ 1 + 2 * u_ro beta prec := by nlinarith
        have hsucc_eval :
            FloatSpec.Core.Ulp.succ beta (FLX_exp prec) (1 + 2 * u_ro beta prec) =
              (1 + 2 * u_ro beta prec) +
                FloatSpec.Core.Ulp.ulp beta (FLX_exp prec) (1 + 2 * u_ro beta prec) := by
          simp [FloatSpec.Core.Ulp.succ, hmid_nonneg]
        rw [hsucc_eval]
        nlinarith
      exact le_trans hsucc_mid_ge hsucc_mid_le_x
  · left
    exact hx_eq1.symm

-- Local notation for unit roundoff used below
local notation "uro" => u_ro beta prec

/-- Unit roundoff is bounded by one half for positive precision. -/
private lemma u_ro_le_half (hβ : 1 < beta) :
  u_ro beta prec ≤ (1 / 2 : ℝ) := by
  unfold u_ro
  have hbge1ℝ : (1 : ℝ) ≤ (beta : ℝ) := by
    have hbge1ℤ : (1 : Int) ≤ beta := le_of_lt hβ
    exact_mod_cast hbge1ℤ
  have hexp_nonpos : -prec + 1 ≤ 0 := by
    have hp : 1 ≤ prec := Int.add_one_le_iff.mpr (Prec_gt_0.pos : 0 < prec)
    omega
  have hpow_le_one : (beta : ℝ) ^ (-prec + 1) ≤ 1 := by
    simpa using
      (zpow_le_zpow_right₀ hbge1ℝ hexp_nonpos :
        (beta : ℝ) ^ (-prec + 1) ≤ (beta : ℝ) ^ (0 : Int))
  nlinarith [mul_le_mul_of_nonneg_left hpow_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))]


/-- Positivity helper. -/
lemma om1ds1p2u_ro_pos (hβ : 1 < beta) :
  0 ≤ 1 - 1 / Real.sqrt (1 + 2 * uro) := by
  have hu : 0 ≤ uro := u_ro_pos (beta := beta) (prec := prec) hβ
  have hs_ge1 : 1 ≤ Real.sqrt (1 + 2 * uro) := by
    rw [Real.one_le_sqrt]
    nlinarith
  have hs_pos : 0 < Real.sqrt (1 + 2 * uro) := lt_of_lt_of_le zero_lt_one hs_ge1
  have hinv_le : 1 / Real.sqrt (1 + 2 * uro) ≤ 1 := by
    simpa using one_div_le_one_div_of_le zero_lt_one hs_ge1
  linarith

/-- Monotone bound helper. -/
lemma om1ds1p2u_ro_le_u_rod1pu_ro (hβ : 1 < beta) :
  1 - 1 / Real.sqrt (1 + 2 * uro) ≤ uro / (1 + uro) := by
  have hu : 0 ≤ uro := u_ro_pos (beta := beta) (prec := prec) hβ
  have hs_pos : 0 < Real.sqrt (1 + 2 * uro) := by
    have hs_ge1 : 1 ≤ Real.sqrt (1 + 2 * uro) := by
      rw [Real.one_le_sqrt]
      nlinarith
    exact lt_of_lt_of_le zero_lt_one hs_ge1
  have hden_pos : 0 < 1 + uro := by linarith
  have hs_le : Real.sqrt (1 + 2 * uro) ≤ 1 + uro := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hinv :
      1 / (1 + uro) ≤ 1 / Real.sqrt (1 + 2 * uro) := by
    exact one_div_le_one_div_of_le hs_pos hs_le
  have hrewrite : 1 - 1 / (1 + uro) = uro / (1 + uro) := by
    field_simp [ne_of_gt hden_pos]
    ring
  linarith

/-- Nonnegativity helper. -/
lemma s1p2u_rom1_pos (hβ : 1 < beta) :
  0 ≤ Real.sqrt (1 + 2 * uro) - 1 := by
  have hu : 0 ≤ uro := u_ro_pos (beta := beta) (prec := prec) hβ
  have hs_ge1 : 1 ≤ Real.sqrt (1 + 2 * uro) := by
    rw [Real.one_le_sqrt]
    nlinarith
  linarith


/-- Auxiliary inequality for sqrt error. -/
lemma sqrt_error_N_FLX_aux3 (hβ : 1 < beta) :
  u_ro beta prec / Real.sqrt (1 + 4 * u_ro beta prec)
    ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) := by
  let u : ℝ := u_ro beta prec
  have hu_nonneg : 0 ≤ u := by
    simpa [u] using u_ro_pos (beta := beta) (prec := prec) hβ
  have hu_le_half : u ≤ (1 / 2 : ℝ) := by
    simpa [u] using u_ro_le_half (beta := beta) (prec := prec) hβ
  by_cases hu0 : u = 0
  · simp [u, hu0]
  have hu_pos : 0 < u := lt_of_le_of_ne hu_nonneg (Ne.symm hu0)
  set s : ℝ := Real.sqrt (1 + 2 * u) with hs
  set t : ℝ := Real.sqrt (1 + 4 * u) with ht
  have hs_nonneg : 0 ≤ s := by simpa [s] using Real.sqrt_nonneg (1 + 2 * u)
  have ht_nonneg : 0 ≤ t := by simpa [t] using Real.sqrt_nonneg (1 + 4 * u)
  have hs_pos : 0 < s := by
    have hs_ge1 : 1 ≤ s := by
      rw [hs, Real.one_le_sqrt]
      nlinarith
    linarith
  have ht_pos : 0 < t := by
    have ht_ge1 : 1 ≤ t := by
      rw [ht, Real.one_le_sqrt]
      nlinarith
    linarith
  have hs_sq : s ^ 2 = 1 + 2 * u := by
    rw [hs]
    exact Real.sq_sqrt (by nlinarith)
  have ht_sq : t ^ 2 = 1 + 4 * u := by
    rw [ht]
    exact Real.sq_sqrt (by nlinarith)
  have hpoly_aux : (1 + 2 * u) ^ 3 ≤ (1 + 5 * u - 2 * u ^ 2) ^ 2 := by
    have hu_sq_le : u ^ 2 ≤ u / 2 := by nlinarith [mul_nonneg hu_nonneg (by linarith : 0 ≤ (1 / 2 : ℝ) - u)]
    have hmain : 0 ≤ 4 * u ^ 4 - 28 * u ^ 3 + 9 * u ^ 2 + 4 * u := by
      have hu2_nonneg : 0 ≤ u ^ 2 := sq_nonneg u
      have hu3_nonneg : 0 ≤ u ^ 3 := by nlinarith [hu_nonneg, hu2_nonneg]
      have hu4_nonneg : 0 ≤ u ^ 4 := by nlinarith [hu2_nonneg, sq_nonneg (u ^ 2)]
      have hneg_quad : -28 * u ^ 2 ≥ -14 * u := by nlinarith [hu_sq_le]
      have hlinear : 0 ≤ 4 - 5 * u := by nlinarith
      nlinarith
    nlinarith
  have hB_nonneg : 0 ≤ 1 + 5 * u - 2 * u ^ 2 := by
    have hu_sq_le : u ^ 2 ≤ u / 2 := by nlinarith [mul_nonneg hu_nonneg (by linarith : 0 ≤ (1 / 2 : ℝ) - u)]
    nlinarith
  have hAs_le_B : (1 + 2 * u) * s ≤ 1 + 5 * u - 2 * u ^ 2 := by
    have hsq :
        ((1 + 2 * u) * s) ^ 2 ≤ (1 + 5 * u - 2 * u ^ 2) ^ 2 := by
      have hA_nonneg : 0 ≤ 1 + 2 * u := by nlinarith
      have hA_sq_nonneg : 0 ≤ (1 + 2 * u) ^ 2 := sq_nonneg (1 + 2 * u)
      calc
        ((1 + 2 * u) * s) ^ 2
            = (1 + 2 * u) ^ 2 * s ^ 2 := by ring
        _ = (1 + 2 * u) ^ 3 := by rw [hs_sq]; ring
        _ ≤ (1 + 5 * u - 2 * u ^ 2) ^ 2 := hpoly_aux
    exact le_of_sq_le_sq hsq hB_nonneg
  have hkey : s * (s + 1) ≤ 2 * t := by
    have hleft_nonneg : 0 ≤ s * (s + 1) := by nlinarith
    have hright_nonneg : 0 ≤ 2 * t := by nlinarith
    apply le_of_sq_le_sq ?_ hright_nonneg
    calc
      (s * (s + 1)) ^ 2
          = s ^ 2 * (s + 1) ^ 2 := by ring
      _ = (1 + 2 * u) * (s + 1) ^ 2 := by rw [hs_sq]
      _ = (1 + 2 * u) ^ 2 + (1 + 2 * u) + 2 * ((1 + 2 * u) * s) := by
        rw [show (s + 1) ^ 2 = s ^ 2 + 2 * s + 1 by ring, hs_sq]
        ring
      _ ≤ (1 + 2 * u) ^ 2 + (1 + 2 * u) + 2 * (1 + 5 * u - 2 * u ^ 2) := by
        nlinarith
      _ = 4 * (1 + 4 * u) := by ring
      _ = 4 * t ^ 2 := by rw [ht_sq]
      _ = (2 * t) ^ 2 := by
        ring
  have hden_pos : 0 < s * (s + 1) := by nlinarith
  have hfrac_le :
      u / t ≤ u / (s * (s + 1) / 2) := by
    have hden_half_pos : 0 < s * (s + 1) / 2 := by nlinarith
    have hhalf_le : s * (s + 1) / 2 ≤ t := by nlinarith
    exact div_le_div_of_nonneg_left hu_nonneg hden_half_pos hhalf_le
  have hrhs_eq : u / (s * (s + 1) / 2) = 1 - 1 / s := by
    field_simp [ne_of_gt hs_pos, ne_of_gt hden_pos]
    rw [show (s + 1) * (s - 1) = s ^ 2 - 1 by ring, hs_sq]
    ring
  calc
    u_ro beta prec / Real.sqrt (1 + 4 * u_ro beta prec)
        = u / t := by simp [u, t]
    _ ≤ u / (s * (s + 1) / 2) := hfrac_le
    _ = 1 - 1 / s := hrhs_eq
    _ = 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) := by simp [u, s]


/-/ Relative-error bound for rounding sqrt in FLX (nearest) -/
theorem sqrt_error_N_FLX (x : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLX_exp prec) x) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) - Real.sqrt x|
    ≤ (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * |Real.sqrt x| := by
  classical
  let fexp := FLX_exp prec
  let rnd : ℝ → Int := FloatSpec.Core.Generic_fmt.Znearest choice
  let t : ℝ := Real.sqrt x
  let rt : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp rnd t
  have hround_eq :
      FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) = rt := by
    simp [FloatSpec.Calc.Round.round, Znearest, FloatSpec.Compat.Scaffold.ZnearestMode,
      fexp, rnd, rt, t]
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposℝ : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposℝ
  have hu_nonneg : 0 ≤ u_ro beta prec := u_ro_pos (beta := beta) (prec := prec) hβ
  have hu_pos : 0 < u_ro beta prec := by
    unfold u_ro
    exact mul_pos (by norm_num) (zpow_pos hbposℝ (-prec + 1))
  have hb_nonneg :
      0 ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) :=
    om1ds1p2u_ro_pos (beta := beta) (prec := prec) hβ
  by_cases hx_nonpos : x ≤ 0
  · have ht0 : t = 0 := by simpa [t] using Real.sqrt_eq_zero_of_nonpos hx_nonpos
    have hrt0 : rt = 0 := by
      have hz : rnd 0 = 0 := by
        simp [rnd, FloatSpec.Core.Generic_fmt.Znearest, FloatSpec.Core.Raux.Zfloor,
          FloatSpec.Core.Raux.Zceil, FloatSpec.Core.Raux.Rcompare]
      simp [rt, t, ht0, fexp, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, hz]
    rw [hround_eq]
    change |rt - t| ≤ (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * |t|
    rw [ht0, hrt0]
    simp
  · have hxpos : 0 < x := lt_of_not_ge hx_nonpos
    rcases sqrt_error_N_FLX_aux1 (beta := beta) (prec := prec) x hβ hx hxpos with
      ⟨mu, e, hFmu, hmu, hmu_ge1, hmu_lt⟩
    have hmu_nonneg : 0 ≤ mu := le_trans (by norm_num) hmu_ge1
    have hbp_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposℝ e
    have hbp_nonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt hbp_pos
    have hsqrt_mu_nonneg : 0 ≤ Real.sqrt mu := Real.sqrt_nonneg mu
    have ht_eq : t = Real.sqrt mu * (beta : ℝ) ^ e := by
      have hsqrt_bpow :
          Real.sqrt ((beta : ℝ) ^ (2 * e)) = (beta : ℝ) ^ e := by
        have htrip := FloatSpec.Core.Raux.sqrt_bpow (beta := beta) (e := e) hβ
        simpa [FloatSpec.Core.Raux.sqrt_bpow_check, wp, Std.Do.PostCond.noThrow,
          Id.run, pure] using htrip trivial
      calc
        t = Real.sqrt (mu * (beta : ℝ) ^ (2 * e)) := by simpa [t, hmu]
        _ = Real.sqrt mu * Real.sqrt ((beta : ℝ) ^ (2 * e)) := by
          rw [Real.sqrt_mul hmu_nonneg]
        _ = Real.sqrt mu * (beta : ℝ) ^ e := by rw [hsqrt_bpow]
    have ht_pos : 0 < t := by simpa [t] using Real.sqrt_pos.2 hxpos
    have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
    have hFbp : generic_format beta fexp ((beta : ℝ) ^ e) := by
      have hpre : fexp e ≤ e := by
        have hp_nonneg : 0 ≤ prec := le_of_lt (Prec_gt_0.pos : 0 < prec)
        simp [fexp, FLX_exp, FloatSpec.Core.FLX.FLX_exp]
        omega
      have htrip := FloatSpec.Core.Generic_fmt.generic_format_bpow'
        (beta := beta) (fexp := fexp) (e := e)
      simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip ⟨hβ, hpre⟩
    haveI : Monotone_exp fexp := by
      refine ⟨?_⟩
      intro a b hab
      simp [fexp, FLX_exp, FloatSpec.Core.FLX.FLX_exp]
      omega
    have hN :
        FloatSpec.Core.Defs.Rnd_N_pt (fun y => generic_format beta fexp y) t rt := by
      simpa [rt, rnd] using
        (roundR_Znearest_N_pt (beta := beta) (fexp := fexp)
          (choice := choice) (x := t) hβ)
    rcases sqrt_error_N_FLX_aux2 (beta := beta) (prec := prec) mu hβ hFmu hmu_ge1 with
      hmu_eq1 | hcases
    · have ht_bpow : t = (beta : ℝ) ^ e := by
        rw [ht_eq, hmu_eq1]
        simp
      have hrt_bpow : rt = (beta : ℝ) ^ e := by
        have hfix := FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := beta) (fexp := fexp) (rnd := rnd)
          (x := (beta : ℝ) ^ e) hβ hFbp
        simpa [rt, t, ht_bpow, rnd] using hfix
      rw [hround_eq]
      change |rt - t| ≤ (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * |t|
      rw [ht_bpow, hrt_bpow]
      simpa using
        (mul_nonneg hb_nonneg
          (zpow_nonneg (abs_nonneg (beta : ℝ)) e))
    · rcases hcases with hmu_mid | hmu_tail
      · have hs_ge1 : 1 ≤ Real.sqrt mu := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt hmu_ge1
        have hs_pos : 0 < Real.sqrt mu := lt_of_lt_of_le zero_lt_one hs_ge1
        have herr_candidate :
            |rt - t| ≤ |(beta : ℝ) ^ e - t| :=
          hN.2 ((beta : ℝ) ^ e) hFbp
        have hdist :
            |(beta : ℝ) ^ e - t| =
              (Real.sqrt (1 + 2 * u_ro beta prec) - 1) * (beta : ℝ) ^ e := by
          have hle : (beta : ℝ) ^ e ≤ t := by
            rw [ht_eq]
            nlinarith
          have hnonpos : (beta : ℝ) ^ e - t ≤ 0 := sub_nonpos.mpr hle
          rw [abs_of_nonpos hnonpos, ht_eq, hmu_mid]
          ring
        have htarget :
            (Real.sqrt (1 + 2 * u_ro beta prec) - 1) * (beta : ℝ) ^ e =
              (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * |t| := by
          rw [ht_eq, hmu_mid]
          have hs_mid_pos : 0 < Real.sqrt (1 + 2 * u_ro beta prec) := by
            simpa [hmu_mid] using hs_pos
          have hprod_nonneg :
              0 ≤ Real.sqrt (1 + 2 * u_ro beta prec) * (beta : ℝ) ^ e :=
            mul_nonneg (Real.sqrt_nonneg _) hbp_nonneg
          rw [abs_of_nonneg hprod_nonneg]
          field_simp [ne_of_gt hs_mid_pos]
        calc
          |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) - Real.sqrt x|
              = |rt - t| := by simp [hround_eq, t]
          _ ≤ |(beta : ℝ) ^ e - t| := herr_candidate
          _ = (Real.sqrt (1 + 2 * u_ro beta prec) - 1) * (beta : ℝ) ^ e := hdist
          _ = (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * |t| := htarget
          _ = (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * |Real.sqrt x| := by rfl
      · have hs_gt1 : 1 < Real.sqrt mu := by
          have hlt : Real.sqrt (1 + 4 * u_ro beta prec) ≤ Real.sqrt mu := by
            exact Real.sqrt_le_sqrt hmu_tail
          have hgt : 1 < Real.sqrt (1 + 4 * u_ro beta prec) := by
            have hA_nonneg : 0 ≤ 1 + 4 * u_ro beta prec := by nlinarith
            have hsq : (1 : ℝ) ^ 2 < (Real.sqrt (1 + 4 * u_ro beta prec)) ^ 2 := by
              rw [Real.sq_sqrt hA_nonneg]
              nlinarith [hu_pos]
            exact (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
              (Real.sqrt_nonneg (1 + 4 * u_ro beta prec))).mp hsq
          exact lt_of_lt_of_le hgt hlt
        have hs_lt_beta : Real.sqrt mu < (beta : ℝ) := by
          have hβ_nonneg : 0 ≤ (beta : ℝ) := le_of_lt hbposℝ
          have hsq_lt : (Real.sqrt mu) ^ 2 < (beta : ℝ) ^ 2 := by
            rw [Real.sq_sqrt hmu_nonneg]
            have hzpow_two : (beta : ℝ) ^ (2 : Int) = (beta : ℝ) ^ 2 := by
              exact zpow_natCast (beta : ℝ) 2
            simpa [hzpow_two] using hmu_lt
          exact (sq_lt_sq₀ hsqrt_mu_nonneg hβ_nonneg).mp hsq_lt
        have hmag_t : FloatSpec.Core.Raux.mag beta t = e + 1 := by
          have hlow : (beta : ℝ) ^ ((e + 1) - 1) ≤ |t| := by
            rw [ht_eq]
            have hprod_nonneg : 0 ≤ Real.sqrt mu * (beta : ℝ) ^ e :=
              mul_nonneg hsqrt_mu_nonneg hbp_nonneg
            rw [abs_of_nonneg hprod_nonneg]
            have : (beta : ℝ) ^ e ≤ Real.sqrt mu * (beta : ℝ) ^ e := by
              nlinarith
            have hexp : (e + 1) - 1 = e := by ring
            simpa [hexp] using this
          have hupp : |t| < (beta : ℝ) ^ (e + 1) := by
            rw [ht_eq]
            have hprod_nonneg : 0 ≤ Real.sqrt mu * (beta : ℝ) ^ e :=
              mul_nonneg hsqrt_mu_nonneg hbp_nonneg
            rw [abs_of_nonneg hprod_nonneg]
            calc
              Real.sqrt mu * (beta : ℝ) ^ e
                  < (beta : ℝ) * (beta : ℝ) ^ e := by
                    exact mul_lt_mul_of_pos_right hs_lt_beta hbp_pos
              _ = (beta : ℝ) ^ (e + 1) := by
                    rw [show e + 1 = 1 + e by ring]
                    rw [zpow_add₀ hbne (1 : Int) e]
                    simp
          have htrip := FloatSpec.Core.Raux.mag_unique
            (beta := beta) (x := t) (e := e + 1) hβ hlow hupp
          simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip trivial
        have hcexp_t : FloatSpec.Core.Generic_fmt.cexp beta fexp t = e + 1 - prec := by
          simp [FloatSpec.Core.Generic_fmt.cexp, fexp, FLX_exp,
            FloatSpec.Core.FLX.FLX_exp, hmag_t]
        have herr_half :
            |rt - t| ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ (e + 1 - prec) := by
          set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp t with hsm
          set ce : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp t with hce
          set zn : Int := rnd sm with hzn
          have hpow_nonneg : 0 ≤ (beta : ℝ) ^ ce := le_of_lt (zpow_pos hbposℝ ce)
          have hscaled : sm * (beta : ℝ) ^ ce = t := by
            have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
              (beta := beta) (fexp := fexp) (x := t)
            simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, hsm, ce, hce]
              using htrip hβ
          have hround :
              rt = (zn : ℝ) * (beta : ℝ) ^ ce := by
            simp [rt, FloatSpec.Core.Generic_fmt.roundR, rnd, sm, hsm, ce, hce, zn, hzn]
          have hnearest : |(zn : ℝ) - sm| ≤ (1 / 2 : ℝ) := by
            have htrip :=
              (FloatSpec.Core.Generic_fmt.Znearest_half_theorem choice sm) True.intro
            simpa [FloatSpec.Core.Generic_fmt.Znearest_half_check,
              FloatSpec.Core.Generic_fmt.Znearest_N_strict_check, rnd, zn, hzn,
              abs_sub_comm, wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip
          have hdiff : rt - t = ((zn : ℝ) - sm) * (beta : ℝ) ^ ce := by
            rw [hround, ← hscaled]
            ring
          calc
            |rt - t| = |((zn : ℝ) - sm) * (beta : ℝ) ^ ce| := by rw [hdiff]
            _ = |(zn : ℝ) - sm| * (beta : ℝ) ^ ce := by
              simp [abs_mul, abs_of_nonneg hpow_nonneg]
            _ ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ ce :=
              mul_le_mul_of_nonneg_right hnearest hpow_nonneg
            _ = (1 / 2 : ℝ) * (beta : ℝ) ^ (e + 1 - prec) := by
              simp [ce, hce, hcexp_t]
        have hhalf_eq :
            (1 / 2 : ℝ) * (beta : ℝ) ^ (e + 1 - prec) =
              u_ro beta prec * (beta : ℝ) ^ e := by
          unfold u_ro
          calc
            (1 / 2 : ℝ) * (beta : ℝ) ^ (e + 1 - prec)
                = (1 / 2 : ℝ) * ((beta : ℝ) ^ (-prec + 1) * (beta : ℝ) ^ e) := by
                  have hexp : e + 1 - prec = (-prec + 1) + e := by ring
                  rw [hexp, zpow_add₀ hbne (-prec + 1) e]
            _ = ((1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1)) * (beta : ℝ) ^ e := by ring
        have hratio :
            u_ro beta prec * (beta : ℝ) ^ e ≤
              (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * |t| := by
          rw [ht_eq]
          have hprod_nonneg : 0 ≤ Real.sqrt mu * (beta : ℝ) ^ e :=
            mul_nonneg hsqrt_mu_nonneg hbp_nonneg
          rw [abs_of_nonneg hprod_nonneg]
          have haux3 := sqrt_error_N_FLX_aux3 (beta := beta) (prec := prec) hβ
          have hs_nonneg : 0 ≤ Real.sqrt mu := Real.sqrt_nonneg mu
          have hs_pos : 0 < Real.sqrt mu := lt_trans zero_lt_one hs_gt1
          have hden_le : Real.sqrt (1 + 4 * u_ro beta prec) ≤ Real.sqrt mu :=
            Real.sqrt_le_sqrt hmu_tail
          have hdiv_le :
              u_ro beta prec / Real.sqrt mu ≤
                u_ro beta prec / Real.sqrt (1 + 4 * u_ro beta prec) := by
            have hden_pos : 0 < Real.sqrt (1 + 4 * u_ro beta prec) := by
              have : 1 ≤ Real.sqrt (1 + 4 * u_ro beta prec) := by
                rw [Real.one_le_sqrt]
                nlinarith
              linarith
            exact div_le_div_of_nonneg_left hu_nonneg hden_pos hden_le
          have hmul_le :
              u_ro beta prec ≤
                (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * Real.sqrt mu := by
            have hdiv_bound :
                u_ro beta prec / Real.sqrt mu ≤
                  1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) :=
              le_trans hdiv_le haux3
            have := mul_le_mul_of_nonneg_right hdiv_bound hsqrt_mu_nonneg
            calc
              u_ro beta prec = (u_ro beta prec / Real.sqrt mu) * Real.sqrt mu := by
                field_simp [ne_of_gt hs_pos]
              _ ≤ (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * Real.sqrt mu := this
          simpa [mul_assoc] using mul_le_mul_of_nonneg_right hmul_le hbp_nonneg
        calc
          |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) - Real.sqrt x|
              = |rt - t| := by simp [hround_eq, t]
          _ ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ (e + 1 - prec) := herr_half
          _ = u_ro beta prec * (beta : ℝ) ^ e := hhalf_eq
          _ ≤ (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * |t| := hratio
          _ = (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * |Real.sqrt x| := by rfl

/-/ Existence form of the nearest-rounding sqrt error in FLX -/
theorem sqrt_error_N_FLX_ex (x : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLX_exp prec) x) :
  ∃ eps, |eps| ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) ∧
    FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x)
      = Real.sqrt x * (1 + eps) := by
  let b : ℝ := 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)
  let sx : ℝ := Real.sqrt x
  let rx : ℝ := FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) sx
  have hb_nonneg : 0 ≤ b := by
    simpa [b] using om1ds1p2u_ro_pos (beta := beta) (prec := prec) hβ
  have hbound : |rx - sx| ≤ b * |sx| := by
    simpa [rx, sx, b] using
      sqrt_error_N_FLX (beta := beta) (choice := choice) (prec := prec) x hβ hx
  by_cases hsx : sx = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa [b] using hb_nonneg
    · have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
        unfold FloatSpec.Core.Generic_fmt.Znearest
        simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
      have hrx0 : rx = 0 := by
        simp [rx, sx, hsx, FloatSpec.Calc.Round.round,
          FloatSpec.Core.Generic_fmt.roundR,
          FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
          FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
      simpa [rx, sx, hsx] using hrx0
  · refine ⟨(rx - sx) / sx, ?_, ?_⟩
    · have hsx_abs_pos : 0 < |sx| := abs_pos.mpr hsx
      have hdiv := div_le_div_of_nonneg_right hbound (le_of_lt hsx_abs_pos)
      have hrhs : (b * |sx|) / |sx| = b := by
        field_simp [ne_of_gt hsx_abs_pos]
      have hratio : |rx - sx| / |sx| ≤ b := by
        calc
          |rx - sx| / |sx| ≤ (b * |sx|) / |sx| := hdiv
          _ = b := hrhs
      simpa [abs_div, b] using hratio
    · field_simp [hsx]
      ring

/-- Derive symmetric existence bound from relative-error form -/
theorem sqrt_error_N_round_ex_derive (x rx : ℝ)
  (hβ : 1 < beta)
  (h : ∃ eps, |eps| ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) ∧ rx = x * (1 + eps)) :
  ∃ eps, |eps| ≤ Real.sqrt (1 + 2 * u_ro beta prec) - 1 ∧ x = rx * (1 + eps) := by
  rcases h with ⟨eps, heps, hrx⟩
  let s : ℝ := Real.sqrt (1 + 2 * u_ro beta prec)
  let b : ℝ := 1 - 1 / s
  let eps' : ℝ := -eps / (1 + eps)
  have hu : 0 ≤ u_ro beta prec := u_ro_pos (beta := beta) (prec := prec) hβ
  have hs_ge1 : 1 ≤ s := by
    dsimp [s]
    rw [Real.one_le_sqrt]
    nlinarith
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs_ge1
  have hinv_pos : 0 < 1 / s := one_div_pos.mpr hs_pos
  have hb_nonneg : 0 ≤ b := by
    simpa [b, s] using om1ds1p2u_ro_pos (beta := beta) (prec := prec) hβ
  have heps_upper : eps ≤ b := by
    have hle_abs : eps ≤ |eps| := le_abs_self eps
    exact le_trans hle_abs (by simpa [b, s] using heps)
  have heps_lower : -b ≤ eps := by
    have hneg_abs : -eps ≤ |eps| := neg_le_abs eps
    have : -eps ≤ b := le_trans hneg_abs (by simpa [b, s] using heps)
    linarith
  have hone_sub_b_pos : 0 < 1 - b := by
    have : 1 - b = 1 / s := by
      simp [b]
    linarith
  have hden_pos : 0 < 1 + eps := by
    have : 1 - b ≤ 1 + eps := by linarith
    exact lt_of_lt_of_le hone_sub_b_pos this
  have hden_lower : 1 / s ≤ 1 + eps := by
    have : 1 - b ≤ 1 + eps := by linarith
    simpa [b] using this
  refine ⟨eps', ?_, ?_⟩
  · have h_abs_eps' : |eps'| = |eps| / (1 + eps) := by
      simp [eps', abs_div, abs_of_pos hden_pos]
    have hstep1 : |eps| / (1 + eps) ≤ b / (1 + eps) := by
      exact div_le_div_of_nonneg_right (by simpa [b, s] using heps) (le_of_lt hden_pos)
    have hstep2 : b / (1 + eps) ≤ b / (1 / s) := by
      exact div_le_div_of_nonneg_left hb_nonneg hinv_pos hden_lower
    have hrewrite : b / (1 / s) = s - 1 := by
      simp [b]
      field_simp [ne_of_gt hs_pos]
    calc
      |eps'| = |eps| / (1 + eps) := h_abs_eps'
      _ ≤ b / (1 + eps) := hstep1
      _ ≤ b / (1 / s) := hstep2
      _ = Real.sqrt (1 + 2 * u_ro beta prec) - 1 := by simpa [s] using hrewrite
  · have hden_ne : 1 + eps ≠ 0 := ne_of_gt hden_pos
    rw [hrx]
    simp [eps']
    field_simp [hden_ne]
    ring

/-- Existence of nearest-rounding sqrt remainder decomposition (FLX) -/
theorem sqrt_error_N_FLX_round_ex (x : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLX_exp prec) x) :
  ∃ eps, |eps| ≤ Real.sqrt (1 + 2 * u_ro beta prec) - 1 ∧
    Real.sqrt x
      = FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) * (1 + eps) := by
  exact sqrt_error_N_round_ex_derive (beta := beta) (prec := prec)
    (x := Real.sqrt x)
    (rx := FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x))
    hβ
    (sqrt_error_N_FLX_ex (beta := beta) (choice := choice) (prec := prec) x hβ hx)

/-- Local magnitude lower bound in the form needed by Flocq's
    `round_FLT_FLX` threshold: from `β^e ≤ |x|`, `mag x` is at least `e+1`. -/
private lemma mag_gt_of_bpow_le (x : ℝ) (e : Int)
  (hβ : 1 < beta)
  (hbound : (beta : ℝ) ^ e ≤ |x|) :
  e + 1 ≤ FloatSpec.Core.Raux.mag beta x := by
  rcases lt_or_eq_of_le hbound with hlt | heq
  · have htrip := FloatSpec.Core.Raux.mag_ge_bpow
      (beta := beta) (x := x) (e := e + 1) hβ
      (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlt)
    simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip trivial
  · have hmag_abs := FloatSpec.Core.Raux.mag_abs (beta := beta) (x := x) hβ
    have hmag_abs_run :
        FloatSpec.Core.Raux.mag beta |x| = FloatSpec.Core.Raux.mag beta x := by
      simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using hmag_abs trivial
    have hmag_bpow := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := e) hβ
    have hmag_bpow_run :
        FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ e) = e + 1 := by
      simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using hmag_bpow trivial
    have hmag_x : e + 1 = FloatSpec.Core.Raux.mag beta x := by
      calc
        e + 1 = FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ e) := hmag_bpow_run.symm
        _ = FloatSpec.Core.Raux.mag beta |x| := by simpa [heq]
        _ = FloatSpec.Core.Raux.mag beta x := hmag_abs_run
    exact le_of_eq hmag_x

/-- Concrete-rounding version of Flocq `round_FLT_FLX` for the nearest operator
    used in this file. The lower bound is the Flocq one, `β^(emin+prec-1)`. -/
private lemma round_FLT_FLX_nearest
  (emin : Int) (x : ℝ) (hβ : 1 < beta)
  (hbound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x =
    FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x := by
  set M : Int := FloatSpec.Core.Raux.mag beta x with hM
  have hM_lower : emin + prec ≤ M := by
    have hmag := mag_gt_of_bpow_le (beta := beta) (x := x)
      (e := emin + prec - 1) hβ hbound
    have : emin + prec - 1 + 1 = emin + prec := by ring
    simpa [hM, this] using hmag
  have hcase : emin ≤ M - prec := by
    have := sub_le_sub_right hM_lower prec
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hcexp :
      FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp emin prec) x =
        FloatSpec.Core.Generic_fmt.cexp beta (FLX_exp prec) x := by
    have hEqExp : FLT_exp emin prec M = FLX_exp prec M := by
      simpa [FLT_exp, FloatSpec.Core.FLT.FLT_exp, FLX_exp, FloatSpec.Core.FLX.FLX_exp,
        max_eq_left hcase]
    unfold FloatSpec.Core.Generic_fmt.cexp
    rw [← hM]
    exact hEqExp
  unfold FloatSpec.Calc.Round.round FloatSpec.Core.Generic_fmt.roundR
  simp [FloatSpec.Core.Generic_fmt.scaled_mantissa, hcexp]

/-- Existence of nearest-rounding sqrt factorization under FLT (with emin bound) -/
theorem sqrt_error_N_FLT_ex (emin : Int) (emin_bound : emin ≤ 2 * (1 - prec)) (x : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLT_exp emin prec) x) :
  ∃ eps, |eps| ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (Real.sqrt x)
      = Real.sqrt x * (1 + eps) := by
  by_cases hx_nonpos : x ≤ 0
  · refine ⟨0, ?_, ?_⟩
    · simpa using om1ds1p2u_ro_pos (beta := beta) (prec := prec) hβ
    · have hsqrt0 : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos hx_nonpos
      have hround0 :
          FloatSpec.Calc.Round.round beta (FLT_exp emin prec)
            (Znearest choice) (Real.sqrt x) = 0 := by
        have htrip := FloatSpec.Calc.Round.round_0
          (beta := beta) (fexp := FLT_exp emin prec)
          (mode := ⟨FloatSpec.Core.Generic_fmt.Znearest choice, by
            unfold FloatSpec.Core.Generic_fmt.Znearest
            simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]⟩)
        simpa [hsqrt0, FloatSpec.Calc.Round.round, wp, Std.Do.PostCond.noThrow,
          Id.run, pure] using htrip trivial
      simpa [hsqrt0] using hround0
  · have hx_pos : 0 < x := lt_of_not_ge hx_nonpos
    have hx_flx : generic_format beta (FLX_exp prec) x := by
      have htrip := FloatSpec.Core.FLT.generic_format_FLX_FLT
        (prec := prec) (emin := emin) (beta := beta) (x := x)
      simpa [FLT_exp, FloatSpec.Core.FLT.FLT_exp, FLX_exp, FloatSpec.Core.FLX.FLX_exp,
        wp, Std.Do.PostCond.noThrow, Id.run, pure]
        using htrip ⟨hβ, hx⟩
    rcases sqrt_error_N_FLX_ex (beta := beta) (choice := choice)
      (prec := prec) x hβ hx_flx with ⟨eps, heps, hround_flx⟩
    refine ⟨eps, heps, ?_⟩
    have hx_lower : (beta : ℝ) ^ emin ≤ x := by
      have hge := FloatSpec.Core.Generic_fmt.generic_format_ge_bpow
        (beta := beta) (fexp := FLT_exp emin prec) (emin := emin)
      exact hge ⟨hβ, by
        intro e
        simp [FLT_exp, FloatSpec.Core.FLT.FLT_exp]⟩ x hx_pos hx
    have hsqrt_lower :
        (beta : ℝ) ^ (emin + prec - 1) ≤ |Real.sqrt x| := by
      have hsqrt_bpow :
          (beta : ℝ) ^ (emin / 2) ≤ Real.sqrt ((beta : ℝ) ^ emin) := by
        have htrip := FloatSpec.Core.Raux.sqrt_bpow_ge (beta := beta) (e := emin) hβ
        simpa [FloatSpec.Core.Raux.sqrt_bpow_ge_check, wp, Std.Do.PostCond.noThrow,
          Id.run, pure] using htrip trivial
      have hsqrt_mono :
          Real.sqrt ((beta : ℝ) ^ emin) ≤ Real.sqrt x := by
        exact Real.sqrt_le_sqrt hx_lower
      have hexp_le : emin + prec - 1 ≤ emin / 2 := by
        omega
      have hpow_le :
          (beta : ℝ) ^ (emin + prec - 1) ≤ (beta : ℝ) ^ (emin / 2) := by
        have h := FloatSpec.Core.Raux.bpow_le beta (emin + prec - 1) (emin / 2)
          hβ hexp_le
        simpa [FloatSpec.Core.Raux.bpow_le_check, wp, Std.Do.PostCond.noThrow,
          Id.run, pure] using h trivial
      have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
      calc
        (beta : ℝ) ^ (emin + prec - 1) ≤ (beta : ℝ) ^ (emin / 2) := hpow_le
        _ ≤ Real.sqrt ((beta : ℝ) ^ emin) := hsqrt_bpow
        _ ≤ Real.sqrt x := hsqrt_mono
        _ = |Real.sqrt x| := (abs_of_nonneg hsqrt_nonneg).symm
    have hround_eq :
        FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (Real.sqrt x) =
          FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) :=
      round_FLT_FLX_nearest (beta := beta) (choice := choice) (prec := prec)
        emin (Real.sqrt x) hβ hsqrt_lower
    simpa [hround_eq] using hround_flx

/-- Symmetric existence form for FLT nearest-rounding sqrt remainder -/
theorem sqrt_error_N_FLT_round_ex (emin : Int) (emin_bound : emin ≤ 2 * (1 - prec)) (x : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLT_exp emin prec) x) :
  ∃ eps, |eps| ≤ Real.sqrt (1 + 2 * u_ro beta prec) - 1 ∧
    Real.sqrt x
      = FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (Real.sqrt x) * (1 + eps) := by
  exact sqrt_error_N_round_ex_derive (beta := beta) (prec := prec)
    (x := Real.sqrt x)
    (rx := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (Real.sqrt x))
    hβ
    (sqrt_error_N_FLT_ex (beta := beta) (choice := choice) (prec := prec)
      emin emin_bound x hβ hx)

private lemma Ztrunc_eq_zero_of_abs_lt_half (z : ℝ)
  (hz : |z| < (1 / 2 : ℝ)) :
  FloatSpec.Core.Raux.Ztrunc z = 0 := by
  have hbounds : -(1 / 2 : ℝ) < z ∧ z < (1 / 2 : ℝ) := by
    simpa using (abs_lt.mp hz)
  by_cases hneg : z < 0
  · have hceil0 : Int.ceil z = 0 := by
      have hleft : ((0 : Int) : ℝ) - 1 < z := by
        norm_num
        nlinarith [hbounds.left]
      have hright : z ≤ ((0 : Int) : ℝ) := by
        simpa using (le_of_lt hneg : z ≤ (0 : ℝ))
      exact (Int.ceil_eq_iff).2 ⟨hleft, hright⟩
    simpa [FloatSpec.Core.Raux.Ztrunc, hneg, hceil0]
  · have hnonneg : 0 ≤ z := le_of_not_gt hneg
    have hfloor0 : Int.floor z = 0 := by
      have hleft : ((0 : Int) : ℝ) ≤ z := by simpa using hnonneg
      have hright : z < ((0 : Int) : ℝ) + 1 := by
        norm_num
        nlinarith [hbounds.right]
      exact (Int.floor_eq_iff).2 ⟨hleft, hright⟩
    simpa [FloatSpec.Core.Raux.Ztrunc, not_lt.mpr hnonneg, hfloor0]

private lemma Znearest_eq_zero_of_abs_lt_half (choice : Int → Bool) (z : ℝ)
  (hz : |z| < (1 / 2 : ℝ)) :
  FloatSpec.Core.Generic_fmt.Znearest choice z = 0 := by
  have hbounds : -(1 / 2 : ℝ) < z ∧ z < (1 / 2 : ℝ) := by
    simpa using (abs_lt.mp hz)
  by_cases hneg : z < 0
  · have hceil0 : FloatSpec.Core.Raux.Zceil z = 0 := by
      have hleft : ((0 : Int) : ℝ) - 1 < z := by
        norm_num
        nlinarith [hbounds.left]
      have hright : z ≤ ((0 : Int) : ℝ) := by
        simpa using (le_of_lt hneg : z ≤ (0 : ℝ))
      exact (Int.ceil_eq_iff).2 ⟨hleft, hright⟩
    have hfloor_neg_one : FloatSpec.Core.Raux.Zfloor z = -1 := by
      have hleft : ((-1 : Int) : ℝ) ≤ z := by
        norm_num
        nlinarith [hbounds.left]
      have hright : z < ((-1 : Int) : ℝ) + 1 := by
        norm_num
        exact hneg
      exact (Int.floor_eq_iff).2 ⟨hleft, hright⟩
    have hgt : (1 / 2 : ℝ) < z - ((FloatSpec.Core.Raux.Zfloor z : Int) : ℝ) := by
      rw [hfloor_neg_one]
      norm_num
      nlinarith [hbounds.left]
    simp [FloatSpec.Core.Generic_fmt.Znearest, hfloor_neg_one, hceil0,
      FloatSpec.Core.Raux.Rcompare]
    by_cases hlt : z + 1 < (2 : ℝ)⁻¹
    · norm_num at hlt hgt
      nlinarith
    · simp [hlt]
      by_cases heq : z + 1 = (2 : ℝ)⁻¹
      · norm_num at heq hgt
        nlinarith
      · simp [heq]
  · have hnonneg : 0 ≤ z := le_of_not_gt hneg
    have hfloor0 : FloatSpec.Core.Raux.Zfloor z = 0 := by
      have hleft : ((0 : Int) : ℝ) ≤ z := by simpa using hnonneg
      have hright : z < ((0 : Int) : ℝ) + 1 := by
        norm_num
        nlinarith [hbounds.right]
      exact (Int.floor_eq_iff).2 ⟨hleft, hright⟩
    have hlt : z - ((FloatSpec.Core.Raux.Zfloor z : Int) : ℝ) < (1 / 2 : ℝ) := by
      simpa [hfloor0] using hbounds.right
    simp [FloatSpec.Core.Generic_fmt.Znearest, hfloor0,
      FloatSpec.Core.Raux.Rcompare]
    have hlt' : z < (2 : ℝ)⁻¹ := by
      norm_num
      exact hbounds.right
    simp [hlt']

private lemma generic_format_neg (fexp : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp] (x : ℝ)
  (hx : generic_format beta fexp x) :
  generic_format beta fexp (-x) := by
  have h := FloatSpec.Core.Generic_fmt.generic_format_opp
    (beta := beta) (fexp := fexp) (x := x)
  simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using h hx

-- Section: format_REM (remainder formatting for general exponents)
section FormatREM
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
variable [Monotone_exp fexp]

private lemma valid_rnd_abs_sub_le_one
  (rnd : ℝ → Int) [Valid_rnd rnd] (z : ℝ) :
  |((rnd z : Int) : ℝ) - z| ≤ (1 : ℝ) := by
  classical
  set k : Int := Int.floor z with hk
  have hk_le_z : (k : ℝ) ≤ z := by simpa [k, hk] using Int.floor_le z
  have hz_lt_k1 : z < (k : ℝ) + 1 := by
    simpa [k, hk] using Int.lt_floor_add_one z
  have hz_le_k1 : z ≤ ((k + 1 : Int) : ℝ) := by
    have : z ≤ (k : ℝ) + 1 := le_of_lt hz_lt_k1
    simpa [Int.cast_add, Int.cast_one] using this
  have hk_le_n : k ≤ rnd z := by
    have h := FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_le
      (rnd := rnd) ((k : Int) : ℝ) z hk_le_z
    have hk_round := FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) k
    rw [hk_round] at h
    exact h
  have hn_le_k1 : rnd z ≤ k + 1 := by
    have h := FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_le
      (rnd := rnd) z (((k + 1 : Int) : ℝ)) hz_le_k1
    have hk1_round := FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (k + 1)
    rw [hk1_round] at h
    exact h
  have hk_le_nR : (k : ℝ) ≤ ((rnd z : Int) : ℝ) := by exact_mod_cast hk_le_n
  have hn_le_k1R : ((rnd z : Int) : ℝ) ≤ (k : ℝ) + 1 := by
    have h : ((rnd z : Int) : ℝ) ≤ ((k + 1 : Int) : ℝ) := by exact_mod_cast hn_le_k1
    simpa [Int.cast_add, Int.cast_one] using h
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- Auxiliary remainder formatting under generic exponent function. -/
theorem format_REM_aux
  (rnd : ℝ → Int) [Valid_rnd rnd]
  (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta fexp x)
  (hy : generic_format beta fexp y)
  (hx_nonneg : 0 ≤ x)
  (hy_pos : 0 < y)
  (rnd_small : (0 < x / y ∧ x / y < (1/2 : ℝ)) → rnd (x / y) = 0) :
  generic_format beta fexp (x - ((rnd (x / y) : Int) : ℝ) * y) := by
  classical
  let z : ℝ := x / y
  let n : Int := rnd z
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hz_nonneg : 0 ≤ z := by
    dsimp [z]
    exact div_nonneg hx_nonneg (le_of_lt hy_pos)
  have hn_nonneg : (0 : Int) ≤ n := by
    have h := FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_le
      (rnd := rnd) (0 : ℝ) z hz_nonneg
    have h0_round : rnd (0 : ℝ) = 0 := by
      simpa using FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int)
    rw [h0_round] at h
    simpa [n] using h
  by_cases hn0 : n = 0
  · have hrnd0 : rnd (x / y) = 0 := by simpa [n, z] using hn0
    simpa [hrnd0]
  · have hn_pos : (0 : Int) < n := lt_of_le_of_ne hn_nonneg (Ne.symm hn0)
    by_cases hn1 : n = 1
    · have hrnd1 : rnd (x / y) = 1 := by simpa [n, z] using hn1
      have hx_ne : x ≠ 0 := by
        intro hx0
        have hz0 : z = 0 := by simp [z, hx0]
        have hn_zero : n = 0 := by
          have h0_round : rnd (0 : ℝ) = 0 := by
            simpa using FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int)
          simpa [n, hz0] using h0_round
        exact hn0 hn_zero
      have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg hx_ne.symm
      have hz_pos : 0 < z := by
        dsimp [z]
        exact div_pos hx_pos hy_pos
      have hz_ge_half : (1 / 2 : ℝ) ≤ z := by
        by_contra hnot
        have hz_lt_half : z < (1 / 2 : ℝ) := lt_of_not_ge hnot
        have hsmall := rnd_small ⟨hz_pos, hz_lt_half⟩
        have : n = 0 := by simpa [n, z] using hsmall
        exact hn0 this
      have hz_le_two : z ≤ (2 : ℝ) := by
        by_contra hnot
        have htwo_lt : (2 : ℝ) < z := lt_of_not_ge hnot
        have htwo_le : (2 : ℝ) ≤ z := le_of_lt htwo_lt
        have h := FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_le
          (rnd := rnd) (2 : ℝ) z htwo_le
        have hn_ge_two : (2 : Int) ≤ n := by
          have h2_round : rnd (2 : ℝ) = 2 := by
            simpa using FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (2 : Int)
          rw [h2_round] at h
          simpa [n] using h
        omega
      have hbounds : y / 2 ≤ x ∧ x ≤ 2 * y := by
        constructor
        · have hmul := mul_le_mul_of_nonneg_right hz_ge_half (le_of_lt hy_pos)
          dsimp [z] at hmul
          have hxy : (x / y) * y = x := by field_simp [hy_ne]
          nlinarith
        · have hmul := mul_le_mul_of_nonneg_right hz_le_two (le_of_lt hy_pos)
          dsimp [z] at hmul
          have hxy : (x / y) * y = x := by field_simp [hy_ne]
          nlinarith
      have hfmt : generic_format beta fexp (x - y) :=
        sterbenz (beta := beta) (fexp := fexp) (x := x) (y := y)
          hx hy hβ hbounds
      have htarget :
          x - ((rnd (x / y) : Int) : ℝ) * y = x - y := by
        rw [hrnd1]
        norm_num
      simpa [htarget] using hfmt
    · have hn_ge_two : (2 : Int) ≤ n := by omega
      let r : ℝ := x - ((n : Int) : ℝ) * y
      have htarget_r :
          x - ((rnd (x / y) : Int) : ℝ) * y = r := by
        simp [r, n, z]
      have hz_abs_bound : |((n : Int) : ℝ) - z| ≤ (1 : ℝ) := by
        simpa [n] using valid_rnd_abs_sub_le_one (rnd := rnd) z
      have hr_abs_le_y : |r| ≤ y := by
        have hr_eq : r = -(((n : Int) : ℝ) - z) * y := by
          dsimp [r, z]
          field_simp [hy_ne]
          ring
        calc
          |r| = |(((n : Int) : ℝ) - z)| * y := by
            rw [hr_eq, abs_mul, abs_neg, abs_of_pos hy_pos]
          _ ≤ (1 : ℝ) * y := mul_le_mul_of_nonneg_right hz_abs_bound (le_of_lt hy_pos)
          _ = y := by ring
      let ex : Int := cexp beta fexp x
      let ey : Int := cexp beta fexp y
      by_cases hexy : ey ≤ ex
      · rcases generic_format_shift (beta := beta) (fexp := fexp)
            (x := x) (e := ey) hβ hx (by simpa [ex, ey] using hexy) with
          ⟨mx, hx_repr⟩
        rcases generic_format_shift (beta := beta) (fexp := fexp)
            (x := y) (e := ey) hβ hy (by simp [ey]) with
          ⟨my, hy_repr⟩
        let m : Int := mx - n * my
        let fr : FloatSpec.Core.Defs.FlocqFloat beta :=
          FloatSpec.Core.Defs.FlocqFloat.mk m ey
        have hr_repr : r = _root_.F2R fr := by
          simp [r, fr, m, hx_repr, hy_repr, _root_.F2R, FloatSpec.Core.Defs.F2R,
            Int.cast_sub, Int.cast_mul]
          ring
        have hcexp_le : r ≠ 0 → cexp beta fexp r ≤ ey := by
          intro hr_ne
          have h := FloatSpec.Core.Generic_fmt.cexp_mono_pos_ax
            (beta := beta) (fexp := fexp) r y hβ hr_ne hy_pos hr_abs_le_y
          simpa [ey] using h
        have hfmt_r : generic_format beta fexp r := by
          have htrip := FloatSpec.Core.Generic_fmt.generic_format_F2R'
            (beta := beta) (fexp := fexp) (x := r) (f := fr)
          simpa [wp, Std.Do.PostCond.noThrow, Id.run, pure] using
            htrip ⟨hβ, hr_repr.symm, by simpa [fr] using hcexp_le⟩
        simpa [htarget_r] using hfmt_r
      · have hex_lt_ey : ex < ey := lt_of_not_ge hexy
        have hx_ne : x ≠ 0 := by
          intro hx0
          have hz0 : z = 0 := by simp [z, hx0]
          have hn_zero : n = 0 := by
            have h0_round : rnd (0 : ℝ) = 0 := by
              simpa using FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int)
            simpa [n, hz0] using h0_round
          exact hn0 hn_zero
        have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg hx_ne.symm
        have hmag_lt : FloatSpec.Core.Raux.mag beta x < FloatSpec.Core.Raux.mag beta y := by
          by_contra hnot
          have hge : FloatSpec.Core.Raux.mag beta y ≤ FloatSpec.Core.Raux.mag beta x :=
            le_of_not_gt hnot
          have hmono := FloatSpec.Core.Generic_fmt.Monotone_exp.mono (fexp := fexp) hge
          have : ey ≤ ex := by
            simpa [ex, ey, FloatSpec.Core.Generic_fmt.cexp] using hmono
          exact (not_le_of_gt hex_lt_ey) this
        have hx_lt_y : x < y := by
          have hx_upper : |x| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) := by
            have htrip := FloatSpec.Core.Raux.mag_upper_bound
              (beta := beta) (x := x) hβ hx_ne
            simpa [FloatSpec.Core.Raux.abs_val, wp, Std.Do.PostCond.noThrow,
              Id.run, pure] using htrip trivial
          have hy_lower : (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y - 1) ≤ |y| := by
            have htrip := FloatSpec.Core.Raux.mag_lower_bound
              (beta := beta) (x := y) hβ hy_ne
            simpa [FloatSpec.Core.Raux.abs_val, wp, Std.Do.PostCond.noThrow,
              Id.run, pure] using htrip trivial
          have hpow_le :
              (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) ≤
                (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y - 1) := by
            have hle : FloatSpec.Core.Raux.mag beta x ≤ FloatSpec.Core.Raux.mag beta y - 1 :=
              Int.le_sub_one_iff.mpr hmag_lt
            have htrip := FloatSpec.Core.Raux.bpow_le beta
              (FloatSpec.Core.Raux.mag beta x)
              (FloatSpec.Core.Raux.mag beta y - 1) hβ hle
            simpa [FloatSpec.Core.Raux.bpow_le_check, wp, Std.Do.PostCond.noThrow,
              Id.run, pure] using htrip trivial
          calc
            x = |x| := (abs_of_nonneg hx_nonneg).symm
            _ < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) := hx_upper
            _ ≤ (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y - 1) := hpow_le
            _ ≤ |y| := hy_lower
            _ = y := abs_of_pos hy_pos
        have hz_lt_one : z < (1 : ℝ) := by
          dsimp [z]
          exact (div_lt_one hy_pos).mpr hx_lt_y
        have hn_le_one : n ≤ (1 : Int) := by
          have h := FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_le
            (rnd := rnd) z (1 : ℝ) (le_of_lt hz_lt_one)
          have h1_round : rnd (1 : ℝ) = 1 := by
            simpa using FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (1 : Int)
          rw [h1_round] at h
          simpa [n] using h
        omega

/-- Remainder formatting under a small-argument rounding hypothesis. -/
theorem format_REM
  (rnd : ℝ → Int) [Valid_rnd rnd]
  (x y : ℝ)
  (hβ : 1 < beta)
  (Hrnd0 : |x / y| < (1/2 : ℝ) → rnd (x / y) = 0)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  generic_format beta fexp (x - ((rnd (x / y) : Int) : ℝ) * y) := by
  have Hpos :
      ∀ (rnd' : ℝ → Int), Valid_rnd rnd' →
      ∀ x y : ℝ,
        (|x / y| < (1 / 2 : ℝ) → rnd' (x / y) = 0) →
        generic_format beta fexp x →
        generic_format beta fexp y →
        0 < y →
        generic_format beta fexp (x - ((rnd' (x / y) : Int) : ℝ) * y) := by
    intro rnd' _ x y Hrnd0' hx hy hy_pos
    by_cases hx_nonneg : 0 ≤ x
    · exact format_REM_aux (beta := beta) (fexp := fexp) (rnd := rnd')
        x y hβ hx hy hx_nonneg hy_pos
        (fun hk => Hrnd0' (by
          rw [abs_of_nonneg (le_of_lt hk.1)]
          exact hk.2))
    · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
      have hmx_nonneg : 0 ≤ -x := by linarith
      have hfmt_negx : generic_format beta fexp (-x) :=
        generic_format_neg (beta := beta) (fexp := fexp) x hx
      have haux : generic_format beta fexp
          (-x - ((FloatSpec.Core.Generic_fmt.Zrnd_opp rnd' ((-x) / y) : Int) : ℝ) * y) :=
        format_REM_aux (beta := beta) (fexp := fexp)
          (rnd := FloatSpec.Core.Generic_fmt.Zrnd_opp rnd')
          (-x) y hβ hfmt_negx hy hmx_nonneg hy_pos
          (fun hk => by
            unfold FloatSpec.Core.Generic_fmt.Zrnd_opp
            have harg : -((-x) / y) = x / y := by field_simp [ne_of_gt hy_pos]
            have hneg_xy : x / y < 0 := by
              have hrewrite : (-x) / y = -(x / y) := by field_simp [ne_of_gt hy_pos]
              nlinarith [hk.1, hrewrite]
            have habs : |x / y| = (-x) / y := by
              have hrewrite : -(x / y) = (-x) / y := by field_simp [ne_of_gt hy_pos]
              rw [abs_of_neg hneg_xy, hrewrite]
            have hr : rnd' (x / y) = 0 := Hrnd0' (by
              rw [habs]
              exact hk.2)
            rw [harg, hr]
            simp)
      have hneg_fmt : generic_format beta fexp
          (-(-x - ((FloatSpec.Core.Generic_fmt.Zrnd_opp rnd' ((-x) / y) : Int) : ℝ) * y)) :=
        generic_format_neg (beta := beta) (fexp := fexp)
          (-x - ((FloatSpec.Core.Generic_fmt.Zrnd_opp rnd' ((-x) / y) : Int) : ℝ) * y) haux
      have htarget :
          -(-x - ((FloatSpec.Core.Generic_fmt.Zrnd_opp rnd' ((-x) / y) : Int) : ℝ) * y)
            = x - ((rnd' (x / y) : Int) : ℝ) * y := by
        unfold FloatSpec.Core.Generic_fmt.Zrnd_opp
        have harg : -((-x) / y) = x / y := by field_simp [ne_of_gt hy_pos]
        rw [harg]
        norm_num
        ring
      simpa [htarget] using hneg_fmt
  by_cases hy_nonneg : 0 ≤ y
  · by_cases hy0 : y = 0
    · simpa [hy0] using hx
    · exact Hpos rnd inferInstance x y Hrnd0 hx hy
        (lt_of_le_of_ne hy_nonneg (Ne.symm hy0))
  · have hy_neg : y < 0 := lt_of_not_ge hy_nonneg
    have hmy_pos : 0 < -y := by linarith
    have hfmt_negy : generic_format beta fexp (-y) :=
      generic_format_neg (beta := beta) (fexp := fexp) y hy
    have haux : generic_format beta fexp
        (x - ((FloatSpec.Core.Generic_fmt.Zrnd_opp rnd (x / (-y)) : Int) : ℝ) * (-y)) :=
      Hpos (FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) inferInstance x (-y)
        (fun hsmall => by
          unfold FloatSpec.Core.Generic_fmt.Zrnd_opp
          have harg : -(x / (-y)) = x / y := by
            field_simp [ne_of_lt hy_neg]
          have hdiv : x / (-y) = -(x / y) := by
            field_simp [ne_of_lt hy_neg]
          have hr : rnd (x / y) = 0 := Hrnd0 (by
            simpa [hdiv, abs_neg] using hsmall)
          rw [harg, hr]
          simp)
        hx hfmt_negy hmy_pos
    have htarget :
        x + ((FloatSpec.Core.Generic_fmt.Zrnd_opp rnd (x / (-y)) : Int) : ℝ) * y
          = x - ((rnd (x / y) : Int) : ℝ) * y := by
      unfold FloatSpec.Core.Generic_fmt.Zrnd_opp
      have harg : -(x / (-y)) = x / y := by
        field_simp [ne_of_lt hy_neg]
      rw [harg]
      norm_num
      ring
    simpa [htarget] using haux

/-- Specialization: remainder formatting with truncation `Ztrunc`. -/
theorem format_REM_ZR
  (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  generic_format beta fexp (x - ((Ztrunc (x / y) : Int) : ℝ) * y) := by
  exact format_REM (beta := beta) (fexp := fexp)
    (rnd := FloatSpec.Core.Raux.Ztrunc) x y hβ
    (fun hsmall => Ztrunc_eq_zero_of_abs_lt_half (x / y) hsmall)
    hx hy

/-- Specialization: remainder formatting with nearest `Znearest`. -/
theorem format_REM_N
  (choice : Int → Bool)
  (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  generic_format beta fexp
    (x - ((FloatSpec.Core.Generic_fmt.Znearest choice (x / y) : Int) : ℝ) * y) := by
  exact format_REM (beta := beta) (fexp := fexp)
    (rnd := FloatSpec.Core.Generic_fmt.Znearest choice) x y hβ
    (fun hsmall => Znearest_eq_zero_of_abs_lt_half choice (x / y) hsmall)
    hx hy

end FormatREM
