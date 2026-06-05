import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Operations
import FloatSpec.src.Calc.Round
import FloatSpec.src.Prop.Relative
import FloatSpec.src.Prop.Sterbenz
import FloatSpec.src.Prop.Mult_error
import Mathlib.Data.Real.Basic

/-!
Tier 1 Scaffold / Tier 3 Excluded.

This property-analysis leaf preserves translated names for audit and future
porting. It is not re-exported by `FloatSpec.src.Prop` and is not part of the
trusted FloatSpec aggregate.
-/

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
  (h1 : |x + y| < FloatSpec.Core.Raux.bpow beta (prec + fx.Fexp))
  (h2 : |x + y| < FloatSpec.Core.Raux.bpow beta (prec + fy.Fexp)) :
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

/-- Square root error in FLX -/
theorem sqrt_error_FLX (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
  (hx : generic_format beta (FLX_exp prec) x) :
  generic_format beta (FLX_exp prec) (x - (FloatSpec.Calc.Round.round beta (FLX_exp prec) rnd (Real.sqrt x))^2) := by
  sorry

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
  (hx : generic_format beta (FLX_exp prec) x) (px : 0 < x) :
  ∃ (mu : ℝ) (e : Int),
    generic_format beta (FLX_exp prec) mu ∧
    x = mu * (beta : ℝ) ^ (2 * e) ∧
    (1 ≤ mu ∧ mu < (beta : ℝ) ^ (2 : Int)) := by
  sorry

/-- Auxiliary bound cases for sqrt error in FLX.
    If `x ≥ 1` and is in FLX format, then `x` is either exactly `1`, or exactly `1 + 2·u_ro`,
    or at least `1 + 4·u_ro`. -/
lemma sqrt_error_N_FLX_aux2 (x : ℝ)
  (hx : generic_format beta (FLX_exp prec) x) (hx_ge1 : 1 ≤ x) :
  x = 1 ∨ x = 1 + 2 * u_ro beta prec ∨ 1 + 4 * u_ro beta prec ≤ x := by
  sorry

-- Local notation for unit roundoff used below
local notation "uro" => u_ro beta prec


/-- Positivity helper. -/
lemma om1ds1p2u_ro_pos :
  0 ≤ 1 - 1 / Real.sqrt (1 + 2 * uro) := by
  sorry

/-- Monotone bound helper. -/
lemma om1ds1p2u_ro_le_u_rod1pu_ro :
  1 - 1 / Real.sqrt (1 + 2 * uro) ≤ uro / (1 + uro) := by
  sorry

/-- Nonnegativity helper. -/
lemma s1p2u_rom1_pos :
  0 ≤ Real.sqrt (1 + 2 * uro) - 1 := by
  sorry


/-- Auxiliary inequality for sqrt error. -/
lemma sqrt_error_N_FLX_aux3 :
  u_ro beta prec / Real.sqrt (1 + 4 * u_ro beta prec)
    ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) := by
  sorry


/-/ Relative-error bound for rounding sqrt in FLX (nearest) -/
theorem sqrt_error_N_FLX (x : ℝ)
  (hx : generic_format beta (FLX_exp prec) x) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) - Real.sqrt x|
    ≤ (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * |Real.sqrt x| := by
  sorry

/-/ Existence form of the nearest-rounding sqrt error in FLX -/
theorem sqrt_error_N_FLX_ex (x : ℝ)
  (hx : generic_format beta (FLX_exp prec) x) :
  ∃ eps, |eps| ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) ∧
    FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x)
      = Real.sqrt x * (1 + eps) := by
  sorry

/-- Derive symmetric existence bound from relative-error form -/
theorem sqrt_error_N_round_ex_derive (x rx : ℝ)
  (h : ∃ eps, |eps| ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) ∧ rx = x * (1 + eps)) :
  ∃ eps, |eps| ≤ Real.sqrt (1 + 2 * u_ro beta prec) - 1 ∧ x = rx * (1 + eps) := by
  sorry

/-- Existence of nearest-rounding sqrt remainder decomposition (FLX) -/
theorem sqrt_error_N_FLX_round_ex (x : ℝ)
  (hx : generic_format beta (FLX_exp prec) x) :
  ∃ eps, |eps| ≤ Real.sqrt (1 + 2 * u_ro beta prec) - 1 ∧
    Real.sqrt x
      = FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) * (1 + eps) := by
  sorry

/-- Existence of nearest-rounding sqrt factorization under FLT (with emin bound) -/
theorem sqrt_error_N_FLT_ex (emin : Int) (emin_bound : emin ≤ 2 * (1 - prec)) (x : ℝ)
  (hx : generic_format beta (FLT_exp emin prec) x) :
  ∃ eps, |eps| ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (Real.sqrt x)
      = Real.sqrt x * (1 + eps) := by
  sorry

/-- Symmetric existence form for FLT nearest-rounding sqrt remainder -/
theorem sqrt_error_N_FLT_round_ex (emin : Int) (emin_bound : emin ≤ 2 * (1 - prec)) (x : ℝ)
  (hx : generic_format beta (FLT_exp emin prec) x) :
  ∃ eps, |eps| ≤ Real.sqrt (1 + 2 * u_ro beta prec) - 1 ∧
    Real.sqrt x
      = FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (Real.sqrt x) * (1 + eps) := by
  sorry

-- Section: format_REM (remainder formatting for general exponents)
section FormatREM
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
variable [FloatSpec.Core.Generic_fmt.Monotone_exp fexp]

/-- Auxiliary remainder formatting under generic exponent function. -/
theorem format_REM_aux
  (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd]
  (x y : ℝ)
  (hx : generic_format beta fexp x)
  (hy : generic_format beta fexp y)
  (hx_nonneg : 0 ≤ x)
  (hy_pos : 0 < y)
  (rnd_small : (0 < x / y ∧ x / y < (1/2 : ℝ)) → rnd (x / y) = 0) :
  generic_format beta fexp (x - ((rnd (x / y) : Int) : ℝ) * y) := by
  sorry

/-- Remainder formatting under a small-argument rounding hypothesis. -/
theorem format_REM
  (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd]
  (x y : ℝ)
  (Hrnd0 : |x / y| < (1/2 : ℝ) → rnd (x / y) = 0)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  generic_format beta fexp (x - ((rnd (x / y) : Int) : ℝ) * y) := by
  sorry

/-- Specialization: remainder formatting with truncation `Ztrunc`. -/
theorem format_REM_ZR
  (x y : ℝ)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  generic_format beta fexp (x - ((Ztrunc (x / y) : Int) : ℝ) * y) := by
  sorry

/-- Specialization: remainder formatting with nearest `Znearest`. -/
theorem format_REM_N
  (choice : Int → Bool)
  (x y : ℝ)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  generic_format beta fexp
    (x - ((FloatSpec.Core.Generic_fmt.Znearest choice (x / y) : Int) : ℝ) * y) := by
  sorry

end FormatREM


/-- Division error in FLT -/
theorem div_error_FLT (emin : Int) (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x y : ℝ)
  (hx : generic_format beta (FLT_exp emin prec) x) (hy : generic_format beta (FLT_exp emin prec) y)
  (h_no_underflow : FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |x / y|) :
  generic_format beta (FLT_exp emin prec) (x - FloatSpec.Calc.Round.round beta (FLT_exp emin prec) rnd (x / y) * y) := by
  sorry

/-- Square root error in FLT -/
theorem sqrt_error_FLT (emin : Int) (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (h_no_underflow : FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |Real.sqrt x|) :
  generic_format beta (FLT_exp emin prec) (x - (FloatSpec.Calc.Round.round beta (FLT_exp emin prec) rnd (Real.sqrt x))^2) := by
  sorry
