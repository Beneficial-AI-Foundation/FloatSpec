import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import FloatSpec.src.Calc.Sqrt
import FloatSpec.src.Prop.Plus_error
import Mathlib.Data.Real.Basic

/-!
Tier 1 Scaffold / Tier 3 Excluded.

This property-analysis leaf preserves translated names for audit and future
porting. It is not re-exported by `FloatSpec.src.Prop` and is not part of the
trusted FloatSpec aggregate.
-/

-- Error of the multiplication is in the FLX/FLT format
-- Translated from Coq file: flocq/src/Prop/Mult_error.v

open Real
open FloatSpec.Core.Defs

variable (beta : Int)
variable (hβ : 1 < beta)
variable (prec : Int)
variable [Prec_gt_0 prec]

-- Section: FLX multiplication error

variable (rnd : ℝ → Int)
variable [Valid_rnd rnd]

private lemma valid_rnd_abs_sub_lt_one (t : ℝ) :
    |((rnd t : Int) : ℝ) - t| < 1 := by
  classical
  have hfloor_le_rnd : FloatSpec.Core.Raux.Zfloor t ≤ rnd t := by
    have hmono :=
      FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_le
        (rnd := rnd) ((FloatSpec.Core.Raux.Zfloor t : Int) : ℝ) t
        (by
          simpa [FloatSpec.Core.Raux.Zfloor] using Int.floor_le t)
    simpa [FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR,
      FloatSpec.Core.Raux.Zfloor] using hmono
  have hrnd_le_ceil : rnd t ≤ FloatSpec.Core.Raux.Zceil t := by
    have hmono :=
      FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_le
        (rnd := rnd) t ((FloatSpec.Core.Raux.Zceil t : Int) : ℝ)
        (by
          simpa [FloatSpec.Core.Raux.Zceil] using Int.le_ceil t)
    simpa [FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR,
      FloatSpec.Core.Raux.Zceil] using hmono
  have hlow : t - 1 < ((rnd t : Int) : ℝ) := by
    have hfloor_ub : t < ((FloatSpec.Core.Raux.Zfloor t : Int) : ℝ) + 1 := by
      simpa [FloatSpec.Core.Raux.Zfloor] using Int.lt_floor_add_one t
    have hfloor_gt : t - 1 < ((FloatSpec.Core.Raux.Zfloor t : Int) : ℝ) := by
      linarith
    have hfloor_real_le : ((FloatSpec.Core.Raux.Zfloor t : Int) : ℝ) ≤ ((rnd t : Int) : ℝ) := by
      exact_mod_cast hfloor_le_rnd
    exact lt_of_lt_of_le hfloor_gt hfloor_real_le
  have hhigh : ((rnd t : Int) : ℝ) < t + 1 := by
    have hceil_lt : ((FloatSpec.Core.Raux.Zceil t : Int) : ℝ) < t + 1 := by
      simpa [FloatSpec.Core.Raux.Zceil] using Int.ceil_lt_add_one t
    have hrnd_real_le : ((rnd t : Int) : ℝ) ≤ ((FloatSpec.Core.Raux.Zceil t : Int) : ℝ) := by
      exact_mod_cast hrnd_le_ceil
    exact lt_of_le_of_lt hrnd_real_le hceil_lt
  have hneg : -1 < ((rnd t : Int) : ℝ) - t := by linarith
  have hpos : ((rnd t : Int) : ℝ) - t < 1 := by linarith
  exact abs_lt.mpr ⟨hneg, hpos⟩

/-- Auxiliary result that provides the exponent for FLX multiplication error -/
lemma mult_error_FLX_aux (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLX_exp prec) x) (hy : generic_format beta (FLX_exp prec) y)
  (h_nonzero : FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd (x * y) - (x * y) ≠ 0) :
  ∃ f : FloatSpec.Core.Defs.FlocqFloat beta, _root_.F2R f = FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd (x * y) - (x * y) ∧
    cexp beta (FLX_exp prec) (_root_.F2R f) ≤ f.Fexp ∧
    f.Fexp = cexp beta (FLX_exp prec) x + cexp beta (FLX_exp prec) y := by
  classical
  set fexp : Int → Int := FLX_exp prec
  set z : ℝ := x * y
  set mx : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)
  set my : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp y)
  set ex : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x
  set ey : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp y
  set ez : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp z
  set ep : Int := ex + ey
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos_real
  have hz0 : z ≠ 0 := by
    intro hz0
    apply h_nonzero
    have hround0 :
        FloatSpec.Core.Generic_fmt.roundR beta fexp rnd z = 0 := by
      have hrnd0 : rnd 0 = 0 := by
        simpa using
          (FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) 0)
      simp [z, hz0, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, hrnd0]
    simpa [z, hz0, fexp] using hround0
  have hx0 : x ≠ 0 := by
    intro hx0
    exact hz0 (by simp [z, hx0])
  have hy0 : y ≠ 0 := by
    intro hy0
    exact hz0 (by simp [z, hy0])
  have hx_repr : x = (mx : ℝ) * (beta : ℝ) ^ ex := by
    simpa [mx, ex, fexp, generic_format] using hx
  have hy_repr : y = (my : ℝ) * (beta : ℝ) ^ ey := by
    simpa [my, ey, fexp, generic_format] using hy
  let fprod : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk (mx * my) ep
  have hz_repr : z = _root_.F2R fprod := by
    calc
      z = x * y := by simp [z]
      _ = ((mx : ℝ) * (beta : ℝ) ^ ex) *
            ((my : ℝ) * (beta : ℝ) ^ ey) := by
            rw [hx_repr, hy_repr]
      _ = ((mx * my : Int) : ℝ) *
            ((beta : ℝ) ^ ex * (beta : ℝ) ^ ey) := by
            norm_num [Int.cast_mul]
            ring
      _ = ((mx * my : Int) : ℝ) * (beta : ℝ) ^ ep := by
            rw [(_root_.zpow_add₀ hbne ex ey).symm]
      _ = _root_.F2R fprod := by
            simp [fprod, _root_.F2R, FloatSpec.Core.Defs.F2R]
  rcases round_repr_same_exp (beta := beta) (fexp := fexp)
      (rnd := rnd) hβ (m := mx * my) (e := ep) with ⟨n, hround_same⟩
  let ferr : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk (n - mx * my) ep
  have hround_z :
      FloatSpec.Core.Generic_fmt.roundR beta fexp rnd z =
        _root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk n ep :
          FloatSpec.Core.Defs.FlocqFloat beta) := by
    rw [hz_repr]
    simpa [fprod] using hround_same
  have herr_repr :
      _root_.F2R ferr =
        FloatSpec.Core.Generic_fmt.roundR beta fexp rnd z - z := by
    calc
      _root_.F2R ferr =
          (((n - mx * my : Int) : ℝ) * (beta : ℝ) ^ ep) := by
            simp [ferr, _root_.F2R, FloatSpec.Core.Defs.F2R]
      _ = (((n : Int) : ℝ) * (beta : ℝ) ^ ep) -
            (((mx * my : Int) : ℝ) * (beta : ℝ) ^ ep) := by
            norm_num [Int.cast_sub, Int.cast_mul]
            ring
      _ = FloatSpec.Core.Generic_fmt.roundR beta fexp rnd z - z := by
            rw [hround_z, hz_repr]
            simp [fprod, _root_.F2R, FloatSpec.Core.Defs.F2R]
  have hcexp_x : ex = FloatSpec.Core.Raux.mag beta x - prec := by
    simp [ex, fexp, FloatSpec.Core.Generic_fmt.cexp, FLX_exp,
      FloatSpec.Core.FLX.FLX_exp]
  have hcexp_y : ey = FloatSpec.Core.Raux.mag beta y - prec := by
    simp [ey, fexp, FloatSpec.Core.Generic_fmt.cexp, FLX_exp,
      FloatSpec.Core.FLX.FLX_exp]
  have hcexp_z : ez = FloatSpec.Core.Raux.mag beta z - prec := by
    simp [ez, fexp, FloatSpec.Core.Generic_fmt.cexp, FLX_exp,
      FloatSpec.Core.FLX.FLX_exp]
  have hx_lower : (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) ≤ |x| := by
    have h := FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := x) hβ hx0
    simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
  have hy_lower : (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y - 1) ≤ |y| := by
    have h := FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := y) hβ hy0
    simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
  have hz_upper : |z| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta z) := by
    have h := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := z) hβ hz0
    simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
  have hx_upper : |x| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) := by
    have h := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := x) hβ hx0
    simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
  have hy_upper : |y| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := by
    have h := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := y) hβ hy0
    simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
  have hpow_lower :
      (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x - 1) +
        (FloatSpec.Core.Raux.mag beta y - 1)) ≤ |z| := by
    have hypow_nonneg :
        0 ≤ (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y - 1) :=
      le_of_lt (zpow_pos hbpos_real _)
    have hmul := mul_le_mul hx_lower hy_lower hypow_nonneg (abs_nonneg x)
    calc
      (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x - 1) +
          (FloatSpec.Core.Raux.mag beta y - 1))
          = (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) *
              (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y - 1) := by
              rw [_root_.zpow_add₀ hbne]
      _ ≤ |x| * |y| := hmul
      _ = |z| := by simp [z, abs_mul]
  have hpow_upper :
      |z| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x +
        FloatSpec.Core.Raux.mag beta y) := by
    have hy_pos : 0 < |y| := abs_pos.mpr hy0
    have hx_pow_pos :
        0 < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) :=
      zpow_pos hbpos_real _
    have hmul :
        |x| * |y| <
          (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) *
            (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) :=
      lt_trans
        (mul_lt_mul_of_pos_right hx_upper hy_pos)
        (mul_lt_mul_of_pos_left hy_upper hx_pow_pos)
    calc
      |z| = |x| * |y| := by simp [z, abs_mul]
      _ < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) *
            (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := hmul
      _ = (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x +
            FloatSpec.Core.Raux.mag beta y) := by
            rw [(_root_.zpow_add₀ hbne
              (FloatSpec.Core.Raux.mag beta x)
              (FloatSpec.Core.Raux.mag beta y)).symm]
  have hmag_lower_lt :
      FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y - 2 <
        FloatSpec.Core.Raux.mag beta z := by
    have hpow_lt :
        (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x +
          FloatSpec.Core.Raux.mag beta y - 2) <
          (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta z) := by
      have hrewrite :
          FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y - 2 =
            (FloatSpec.Core.Raux.mag beta x - 1) +
              (FloatSpec.Core.Raux.mag beta y - 1) := by omega
      rw [hrewrite]
      exact lt_of_le_of_lt hpow_lower hz_upper
    have h := FloatSpec.Core.Raux.lt_bpow beta
      (FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y - 2)
      (FloatSpec.Core.Raux.mag beta z) hβ hpow_lt
    simpa using h True.intro
  have hmag_upper_le :
      FloatSpec.Core.Raux.mag beta z ≤
        FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y := by
    have h := FloatSpec.Core.Raux.mag_le_bpow (beta := beta) (x := z)
      (e := FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y)
      hβ hz0 hpow_upper
    simpa using h True.intro
  have h_ep_le_ez : ep ≤ ez := by
    have hprec : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    omega
  have h_ez_minus_prec_le_ep : ez - prec ≤ ep := by
    omega
  have hsm_scaled :
      FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp z *
          (beta : ℝ) ^ ez = z := by
    have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
      (beta := beta) (fexp := fexp) (x := z)
    simpa [ez, fexp] using h hβ
  have herr_lt :
      |FloatSpec.Core.Generic_fmt.roundR beta fexp rnd z - z| <
        (beta : ℝ) ^ ez := by
    set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp z
    have hmant := valid_rnd_abs_sub_lt_one (rnd := rnd) sm
    have hpow_pos : 0 < (beta : ℝ) ^ ez := zpow_pos hbpos_real _
    have hcalc :
        |(((rnd sm : Int) : ℝ) - sm) * (beta : ℝ) ^ ez| <
          1 * (beta : ℝ) ^ ez := by
      rw [abs_mul, abs_of_pos hpow_pos]
      exact mul_lt_mul_of_pos_right hmant hpow_pos
    have hround_eval :
        FloatSpec.Core.Generic_fmt.roundR beta fexp rnd z =
          ((rnd sm : Int) : ℝ) * (beta : ℝ) ^ ez := by
      simp [FloatSpec.Core.Generic_fmt.roundR, sm, ez]
    calc
      |FloatSpec.Core.Generic_fmt.roundR beta fexp rnd z - z|
          = |(((rnd sm : Int) : ℝ) - sm) * (beta : ℝ) ^ ez| := by
            rw [hround_eval, ← hsm_scaled]
            ring
      _ < 1 * (beta : ℝ) ^ ez := hcalc
      _ = (beta : ℝ) ^ ez := by ring
  have hcexp_err_le : cexp beta fexp (_root_.F2R ferr) ≤ ep := by
    have hferr_ne : _root_.F2R ferr ≠ 0 := by
      intro hf0
      apply h_nonzero
      simpa [herr_repr, fexp, z] using hf0
    have hmag_err_le : FloatSpec.Core.Raux.mag beta (_root_.F2R ferr) ≤ ez := by
      have h := FloatSpec.Core.Raux.mag_le_bpow (beta := beta)
        (x := _root_.F2R ferr) (e := ez) hβ hferr_ne
        (by simpa [herr_repr] using herr_lt)
      simpa using h True.intro
    have hcexp_err :
        cexp beta fexp (_root_.F2R ferr) =
          FloatSpec.Core.Raux.mag beta (_root_.F2R ferr) - prec := by
      simp [cexp, fexp, FloatSpec.Core.Generic_fmt.cexp, FLX_exp,
        FloatSpec.Core.FLX.FLX_exp]
    omega
  refine ⟨ferr, ?_, ?_, ?_⟩
  · simpa [fexp, z] using herr_repr
  · simpa [ferr] using hcexp_err_le
  · rfl

/-- Error of the multiplication in FLX -/
theorem mult_error_FLX (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLX_exp prec) x) (hy : generic_format beta (FLX_exp prec) y) :
  generic_format beta (FLX_exp prec) (FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd (x * y) - (x * y)) := by
  by_cases herr :
      FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd (x * y) - (x * y) = 0
  · simpa [herr] using
      (FloatSpec.Core.Generic_fmt.generic_format_0_run
        (beta := beta) (fexp := FLX_exp prec))
  · rcases mult_error_FLX_aux (beta := beta) (prec := prec)
      (rnd := rnd) x y hβ hx hy herr with ⟨f, hf_eq, hcexp_le, _hfexp⟩
    have hcexp_le' :
        FloatSpec.Core.Generic_fmt.cexp beta (FLX_exp prec)
            (FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd (x * y) - (x * y)) ≤
          f.Fexp := by
      simpa [hf_eq] using hcexp_le
    exact
      (FloatSpec.Core.Generic_fmt.generic_format_F2R'
        (beta := beta) (fexp := FLX_exp prec)
        (x := FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd (x * y) - (x * y))
        (f := f)) ⟨hβ, hf_eq, fun _ => hcexp_le'⟩

/-- Multiplication by power of beta is exact in FLX -/
lemma mult_bpow_exact_FLX (x : ℝ) (e : Int)
  (hβ : 1 < beta) (hx : generic_format beta (FLX_exp prec) x) :
  generic_format beta (FLX_exp prec) (x * FloatSpec.Core.Raux.bpow beta e) := by
  classical
  set fexp : Int → Int := FLX_exp prec
  by_cases hx0 : x = 0
  · subst x
    simpa using
      (FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp))
  · set n : Int := e
    set m : Int := FloatSpec.Core.Raux.Ztrunc
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)
    set ex : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x
    have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
    have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos_real
    have hpow : FloatSpec.Core.Raux.bpow beta e = (beta : ℝ) ^ n := by
      simp [FloatSpec.Core.Raux.bpow, n]
    have hx_repr : x = (m : ℝ) * (beta : ℝ) ^ ex := by
      simpa [m, ex, fexp, generic_format] using hx
    let f : FloatSpec.Core.Defs.FlocqFloat beta :=
      FloatSpec.Core.Defs.FlocqFloat.mk m (ex + n)
    have htarget :
        x * FloatSpec.Core.Raux.bpow beta e = _root_.F2R f := by
      calc
        x * FloatSpec.Core.Raux.bpow beta e
            = ((m : ℝ) * (beta : ℝ) ^ ex) * (beta : ℝ) ^ n := by
                rw [hx_repr, hpow]
        _ = (m : ℝ) * ((beta : ℝ) ^ ex * (beta : ℝ) ^ n) := by ring
        _ = (m : ℝ) * (beta : ℝ) ^ (ex + n) := by
                rw [(_root_.zpow_add₀ hbne ex n).symm]
        _ = _root_.F2R f := by
                simp [f, _root_.F2R, FloatSpec.Core.Defs.F2R]
    have hmag :
        FloatSpec.Core.Raux.mag beta
            (x * FloatSpec.Core.Raux.bpow beta e) =
          FloatSpec.Core.Raux.mag beta x + n := by
      rw [hpow]
      exact FloatSpec.Calc.Sqrt.mag_mult_bpow_eq beta x n hx0 hβ
    have hcexp :
        FloatSpec.Core.Generic_fmt.cexp beta fexp
            (x * FloatSpec.Core.Raux.bpow beta e) =
          ex + n := by
      calc
        FloatSpec.Core.Generic_fmt.cexp beta fexp
            (x * FloatSpec.Core.Raux.bpow beta e)
            = FloatSpec.Core.FLX.FLX_exp prec
                (FloatSpec.Core.Raux.mag beta
                  (x * FloatSpec.Core.Raux.bpow beta e)) := by
                simp [FloatSpec.Core.Generic_fmt.cexp, fexp, FLX_exp]
        _ = FloatSpec.Core.FLX.FLX_exp prec (FloatSpec.Core.Raux.mag beta x) + n := by
                rw [hmag]
                simp [FloatSpec.Core.FLX.FLX_exp]
                grind
        _ = ex + n := by
                simp [ex, fexp, FloatSpec.Core.Generic_fmt.cexp, FLX_exp]
    have hfmt := FloatSpec.Core.Generic_fmt.generic_format_F2R'
      (beta := beta) (fexp := fexp)
      (x := x * FloatSpec.Core.Raux.bpow beta e)
      (f := f) ⟨hβ, htarget.symm, by
        intro _
        simpa [f] using le_of_eq hcexp⟩
    simpa [fexp] using hfmt

-- Section: FLT multiplication error

variable (emin : Int)

/-- Error of the multiplication in FLT with underflow requirements -/
theorem mult_error_FLT (x y : ℝ)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLT_exp emin prec) x) (hy : generic_format beta (FLT_exp emin prec) y)
  (h_underflow : x * y ≠ 0 →
    FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |x * y|) :
  generic_format beta (FLT_exp emin prec) (FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x * y) - (x * y)) := by
  classical
  set z : ℝ := x * y
  by_cases herr :
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd z - z = 0
  · simpa [z, herr] using
      (FloatSpec.Core.Generic_fmt.generic_format_0_run
        (beta := beta) (fexp := FLT_exp emin prec))
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hz0 : z ≠ 0 := by
    intro hz0
    apply herr
    have hrnd0 : rnd 0 = 0 := by
      simpa using
        (FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) 0)
    have hround0 :
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd z = 0 := by
      simp [z, hz0, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, hrnd0]
    simpa [z, hz0] using hround0
  have hx0 : x ≠ 0 := by
    intro hx0
    exact hz0 (by simp [z, hx0])
  have hy0 : y ≠ 0 := by
    intro hy0
    exact hz0 (by simp [z, hy0])
  have hbound_under : FloatSpec.Core.Raux.bpow beta (emin + 2 * prec - 1) ≤ |z| := by
    simpa [z] using h_underflow (by simpa [z] using hz0)
  have hbound_cexp : (beta : ℝ) ^ (emin + prec) ≤ |z| := by
    have hprec : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    have hexp_le : emin + prec ≤ emin + 2 * prec - 1 := by omega
    have hbpow_le :
        (beta : ℝ) ^ (emin + prec) ≤
          (beta : ℝ) ^ (emin + 2 * prec - 1) := by
      have h := FloatSpec.Core.Raux.bpow_le beta (emin + prec)
        (emin + 2 * prec - 1) hβ hexp_le
      simpa [FloatSpec.Core.Raux.bpow] using h True.intro
    exact le_trans hbpow_le (by simpa [FloatSpec.Core.Raux.bpow] using hbound_under)
  have hcexp_eq :
      cexp beta (FLT_exp emin prec) z = cexp beta (FLX_exp prec) z := by
    have h := FloatSpec.Core.FLT.cexp_FLT_FLX
      (prec := prec) (emin := emin) (beta := beta) (x := z)
    have h' := h ⟨hβ, hbound_cexp⟩
    simpa [cexp, FLT_exp, FLX_exp] using h'
  have hround_eq :
      FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd z =
        FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd z := by
    have hcexp_eq_core :
        FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp emin prec) z =
          FloatSpec.Core.Generic_fmt.cexp beta (FLX_exp prec) z := by
      simpa [cexp] using hcexp_eq
    simp [FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, hcexp_eq_core]
  have hx_flx : generic_format beta (FLX_exp prec) x := by
    have h := FloatSpec.Core.FLT.generic_format_FLX_FLT
      (prec := prec) (emin := emin) (beta := beta) (x := x)
    have h' := h ⟨hβ, by simpa [FLT_exp] using hx⟩
    simpa [FLX_exp] using h'
  have hy_flx : generic_format beta (FLX_exp prec) y := by
    have h := FloatSpec.Core.FLT.generic_format_FLX_FLT
      (prec := prec) (emin := emin) (beta := beta) (x := y)
    have h' := h ⟨hβ, by simpa [FLT_exp] using hy⟩
    simpa [FLX_exp] using h'
  have herr_flx :
      FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd (x * y) - (x * y) ≠ 0 := by
    intro h0
    apply herr
    simpa [z, hround_eq] using h0
  rcases mult_error_FLX_aux (beta := beta) (prec := prec) (rnd := rnd)
      x y hβ hx_flx hy_flx herr_flx with ⟨f, hf_eq, hcexp_flx_le, hfexp⟩
  have hmag_sum_upper :
      FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y - 2 <
        FloatSpec.Core.Raux.mag beta z := by
    have hx_lower : (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) ≤ |x| := by
      have h := FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := x) hβ hx0
      simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
    have hy_lower : (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y - 1) ≤ |y| := by
      have h := FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := y) hβ hy0
      simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
    have hz_upper : |z| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta z) := by
      have h := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := z) hβ hz0
      simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos_real
    have hpow_lower :
        (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x - 1) +
          (FloatSpec.Core.Raux.mag beta y - 1)) ≤ |z| := by
      have hypow_nonneg :
          0 ≤ (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y - 1) :=
        le_of_lt (zpow_pos hbpos_real _)
      have hmul := mul_le_mul hx_lower hy_lower hypow_nonneg (abs_nonneg x)
      calc
        (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x - 1) +
            (FloatSpec.Core.Raux.mag beta y - 1))
            = (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) *
                (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y - 1) := by
                rw [_root_.zpow_add₀ hbne]
        _ ≤ |x| * |y| := hmul
        _ = |z| := by simp [z, abs_mul]
    have hpow_lt :
        (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x +
          FloatSpec.Core.Raux.mag beta y - 2) <
          (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta z) := by
      have hrewrite :
          FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y - 2 =
            (FloatSpec.Core.Raux.mag beta x - 1) +
              (FloatSpec.Core.Raux.mag beta y - 1) := by omega
      rw [hrewrite]
      exact lt_of_le_of_lt hpow_lower hz_upper
    have h := FloatSpec.Core.Raux.lt_bpow beta
      (FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y - 2)
      (FloatSpec.Core.Raux.mag beta z) hβ hpow_lt
    simpa using h True.intro
  have hemin_le_fexp : emin ≤ f.Fexp := by
    have hprec : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos_real
    have hx_upper : |x| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) := by
      have h := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := x) hβ hx0
      simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
    have hy_upper : |y| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := by
      have h := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := y) hβ hy0
      simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
    have hpow_upper :
        |z| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x +
          FloatSpec.Core.Raux.mag beta y) := by
      have hy_pos : 0 < |y| := abs_pos.mpr hy0
      have hx_pow_pos :
          0 < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) :=
        zpow_pos hbpos_real _
      have hmul :
          |x| * |y| <
            (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) *
              (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) :=
        lt_trans
          (mul_lt_mul_of_pos_right hx_upper hy_pos)
          (mul_lt_mul_of_pos_left hy_upper hx_pow_pos)
      calc
        |z| = |x| * |y| := by simp [z, abs_mul]
        _ < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) *
              (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := hmul
        _ = (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x +
              FloatSpec.Core.Raux.mag beta y) := by
              rw [(_root_.zpow_add₀ hbne
                (FloatSpec.Core.Raux.mag beta x)
                (FloatSpec.Core.Raux.mag beta y)).symm]
    have h_under_lt :
        emin + 2 * prec - 1 <
          FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y := by
      have hpow_lt :
          (beta : ℝ) ^ (emin + 2 * prec - 1) <
            (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x +
              FloatSpec.Core.Raux.mag beta y) :=
        lt_of_le_of_lt (by simpa [FloatSpec.Core.Raux.bpow] using hbound_under)
          hpow_upper
      have h := FloatSpec.Core.Raux.lt_bpow beta (emin + 2 * prec - 1)
        (FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y)
        hβ hpow_lt
      simpa using h True.intro
    have hfx :
        cexp beta (FLX_exp prec) x = FloatSpec.Core.Raux.mag beta x - prec := by
      simp [cexp, FLX_exp, FloatSpec.Core.Generic_fmt.cexp,
        FloatSpec.Core.FLX.FLX_exp]
    have hfy :
        cexp beta (FLX_exp prec) y = FloatSpec.Core.Raux.mag beta y - prec := by
      simp [cexp, FLX_exp, FloatSpec.Core.Generic_fmt.cexp,
        FloatSpec.Core.FLX.FLX_exp]
    omega
  have hflt_cexp_le :
      cexp beta (FLT_exp emin prec) (_root_.F2R f) ≤ f.Fexp := by
    have hflx_cexp :
        cexp beta (FLX_exp prec) (_root_.F2R f) =
          FloatSpec.Core.Raux.mag beta (_root_.F2R f) - prec := by
      simp [cexp, FLX_exp, FloatSpec.Core.Generic_fmt.cexp,
        FloatSpec.Core.FLX.FLX_exp]
    have hflt_cexp :
        cexp beta (FLT_exp emin prec) (_root_.F2R f) =
          max (FloatSpec.Core.Raux.mag beta (_root_.F2R f) - prec) emin := by
      simp [cexp, FLT_exp, FloatSpec.Core.Generic_fmt.cexp,
        FloatSpec.Core.FLT.FLT_exp]
    rw [hflt_cexp]
    exact max_le (by simpa [hflx_cexp] using hcexp_flx_le) hemin_le_fexp
  have hf_eq_flt :
      _root_.F2R f =
        FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x * y) - (x * y) := by
    calc
      _root_.F2R f =
          FloatSpec.Core.Generic_fmt.roundR beta (FLX_exp prec) rnd (x * y) - (x * y) := hf_eq
      _ = FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x * y) - (x * y) := by
            simpa [z] using congrArg (fun r => r - z) hround_eq.symm
  exact
    (FloatSpec.Core.Generic_fmt.generic_format_F2R'
      (beta := beta) (fexp := FLT_exp emin prec)
      (x := FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x * y) - (x * y))
      (f := f)) ⟨hβ, hf_eq_flt, fun _ => by
        simpa [hf_eq_flt] using hflt_cexp_le⟩

/-- F2R greater than or equal to power bound.

Upstream Flocq `F2R_ge` states:
`F2R y <> 0 -> bpow (Fexp y) <= Rabs (F2R y)`. -/
lemma F2R_ge (f : FloatSpec.Core.Defs.FlocqFloat beta) (h_nonzero : _root_.F2R f ≠ 0)
  (hbeta : 1 < beta) :
  FloatSpec.Core.Raux.bpow beta f.Fexp ≤ |_root_.F2R f| := by
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hbeta
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hbpow_pos : 0 < (beta : ℝ) ^ f.Fexp := zpow_pos hbpos_real _
  have hbpow_nonneg : 0 ≤ (beta : ℝ) ^ f.Fexp := le_of_lt hbpow_pos
  have hbpow_abs : |(beta : ℝ) ^ f.Fexp| = (beta : ℝ) ^ f.Fexp :=
    abs_of_nonneg hbpow_nonneg
  have hnum_ne : f.Fnum ≠ 0 := by
    intro hnum
    apply h_nonzero
    simp [_root_.F2R, FloatSpec.Core.Defs.F2R, hnum]
  have hnum_abs_one_int : (1 : Int) ≤ |f.Fnum| := Int.one_le_abs hnum_ne
  have hnum_abs_one : (1 : ℝ) ≤ |(f.Fnum : ℝ)| := by
    exact_mod_cast hnum_abs_one_int
  have hscaled :
      (1 : ℝ) * ((beta : ℝ) ^ f.Fexp) ≤
        |(f.Fnum : ℝ)| * ((beta : ℝ) ^ f.Fexp) :=
    mul_le_mul_of_nonneg_right hnum_abs_one hbpow_nonneg
  calc
    FloatSpec.Core.Raux.bpow beta f.Fexp
        = (1 : ℝ) * ((beta : ℝ) ^ f.Fexp) := by
            simp [FloatSpec.Core.Raux.bpow]
    _ ≤ |(f.Fnum : ℝ)| * ((beta : ℝ) ^ f.Fexp) := hscaled
    _ = |((f.Fnum : ℝ) * ((beta : ℝ) ^ f.Fexp))| := by
            rw [abs_mul, hbpow_abs]
    _ = |_root_.F2R f| := by
            simp [_root_.F2R, FloatSpec.Core.Defs.F2R]

/-- FLT multiplication error greater than or equal to power bound -/
theorem mult_error_FLT_ge_bpow (x y : ℝ) (e : Int)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLT_exp emin prec) x) (hy : generic_format beta (FLT_exp emin prec) y)
  (h_bound : FloatSpec.Core.Raux.bpow beta (e + 2 * prec - 1) ≤ |x * y|)
  (h_nonzero : FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x * y) - (x * y) ≠ 0) :
  FloatSpec.Core.Raux.bpow beta e ≤
    |FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x * y) - (x * y)| := by
  classical
  set fexp : Int → Int := FLT_exp emin prec
  set mx : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)
  set my : Int := FloatSpec.Core.Raux.Ztrunc
    (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp y)
  set ex : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x
  set ey : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp y
  set ep : Int := ex + ey
  have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos_real
  have hx0 : x ≠ 0 := by
    intro hx0
    have hpow_pos : 0 < FloatSpec.Core.Raux.bpow beta (e + 2 * prec - 1) := by
      simpa [FloatSpec.Core.Raux.bpow] using
        (zpow_pos hbpos_real (e + 2 * prec - 1))
    have hle0 : FloatSpec.Core.Raux.bpow beta (e + 2 * prec - 1) ≤ 0 := by
      simpa [hx0] using h_bound
    exact (not_lt_of_ge hle0) hpow_pos
  have hy0 : y ≠ 0 := by
    intro hy0
    have hpow_pos : 0 < FloatSpec.Core.Raux.bpow beta (e + 2 * prec - 1) := by
      simpa [FloatSpec.Core.Raux.bpow] using
        (zpow_pos hbpos_real (e + 2 * prec - 1))
    have hle0 : FloatSpec.Core.Raux.bpow beta (e + 2 * prec - 1) ≤ 0 := by
      simpa [hy0] using h_bound
    exact (not_lt_of_ge hle0) hpow_pos
  have hx_repr : x = (mx : ℝ) * (beta : ℝ) ^ ex := by
    simpa [mx, ex, fexp, generic_format] using hx
  have hy_repr : y = (my : ℝ) * (beta : ℝ) ^ ey := by
    simpa [my, ey, fexp, generic_format] using hy
  let fprod : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk (mx * my) ep
  have hprod_repr : x * y = _root_.F2R fprod := by
    calc
      x * y =
          ((mx : ℝ) * (beta : ℝ) ^ ex) *
            ((my : ℝ) * (beta : ℝ) ^ ey) := by
            rw [hx_repr, hy_repr]
      _ = ((mx * my : Int) : ℝ) *
            ((beta : ℝ) ^ ex * (beta : ℝ) ^ ey) := by
            norm_num [Int.cast_mul]
            ring
      _ = ((mx * my : Int) : ℝ) * (beta : ℝ) ^ ep := by
            rw [(_root_.zpow_add₀ hbne ex ey).symm]
      _ = _root_.F2R fprod := by
            simp [fprod, _root_.F2R, FloatSpec.Core.Defs.F2R]
  rcases round_repr_same_exp (beta := beta) (fexp := fexp)
      (rnd := rnd) hβ (m := mx * my) (e := ep) with ⟨n, hround_same⟩
  let ferr : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk (n - mx * my) ep
  have hround_prod :
      FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x * y) =
        _root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk n ep :
          FloatSpec.Core.Defs.FlocqFloat beta) := by
    rw [hprod_repr]
    simpa [fprod] using hround_same
  have herr_repr :
      _root_.F2R ferr =
        FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x * y) - (x * y) := by
    calc
      _root_.F2R ferr =
          (((n - mx * my : Int) : ℝ) * (beta : ℝ) ^ ep) := by
            simp [ferr, _root_.F2R, FloatSpec.Core.Defs.F2R]
      _ = (((n : Int) : ℝ) * (beta : ℝ) ^ ep) -
            (((mx * my : Int) : ℝ) * (beta : ℝ) ^ ep) := by
            norm_num [Int.cast_sub, Int.cast_mul]
            ring
      _ = FloatSpec.Core.Generic_fmt.roundR beta fexp rnd (x * y) - (x * y) := by
            rw [hround_prod, hprod_repr]
            simp [fprod, _root_.F2R, FloatSpec.Core.Defs.F2R]
  have hx_upper : |x| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) := by
    have h := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := x) hβ hx0
    simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
  have hy_upper : |y| < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := by
    have h := FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := y) hβ hy0
    simpa [FloatSpec.Core.Raux.abs_val] using h True.intro
  have hxy_upper :
      |x * y| < (beta : ℝ) ^
        (FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y) := by
    have hy_pos : 0 < |y| := abs_pos.mpr hy0
    have hx_pow_pos :
        0 < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) :=
      zpow_pos hbpos_real _
    have hmul :
        |x| * |y| <
          (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) *
            (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) :=
      lt_trans
        (mul_lt_mul_of_pos_right hx_upper hy_pos)
        (mul_lt_mul_of_pos_left hy_upper hx_pow_pos)
    calc
      |x * y| = |x| * |y| := abs_mul x y
      _ < (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x) *
            (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y) := hmul
      _ = (beta : ℝ) ^
            (FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y) := by
            rw [(_root_.zpow_add₀ hbne
              (FloatSpec.Core.Raux.mag beta x)
              (FloatSpec.Core.Raux.mag beta y)).symm]
  have hpow_lt :
      (beta : ℝ) ^ (e + 2 * prec - 1) <
        (beta : ℝ) ^
          (FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y) := by
    exact lt_of_le_of_lt (by simpa [FloatSpec.Core.Raux.bpow] using h_bound) hxy_upper
  have hexp_lt :
      e + 2 * prec - 1 <
        FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y := by
    have h := FloatSpec.Core.Raux.lt_bpow beta (e + 2 * prec - 1)
      (FloatSpec.Core.Raux.mag beta x + FloatSpec.Core.Raux.mag beta y) hβ hpow_lt
    simpa using h True.intro
  have he_le_ep : e ≤ ep := by
    have hex_le : FloatSpec.Core.Raux.mag beta x - prec ≤ ex := by
      simp [ex, fexp, FloatSpec.Core.Generic_fmt.cexp, FLT_exp,
        FloatSpec.Core.FLT.FLT_exp]
    have hey_le : FloatSpec.Core.Raux.mag beta y - prec ≤ ey := by
      simp [ey, fexp, FloatSpec.Core.Generic_fmt.cexp, FLT_exp,
        FloatSpec.Core.FLT.FLT_exp]
    omega
  have hbpow_le_ep :
      FloatSpec.Core.Raux.bpow beta e ≤ FloatSpec.Core.Raux.bpow beta ep := by
    have h := FloatSpec.Core.Raux.bpow_le beta e ep hβ he_le_ep
    simpa [FloatSpec.Core.Raux.bpow] using h True.intro
  have hferr_ge :
      FloatSpec.Core.Raux.bpow beta ferr.Fexp ≤ |_root_.F2R ferr| :=
    F2R_ge (beta := beta) (f := ferr)
      (by
        intro hzero
        apply h_nonzero
        simpa [herr_repr] using hzero)
      hβ
  calc
    FloatSpec.Core.Raux.bpow beta e ≤ FloatSpec.Core.Raux.bpow beta ep := hbpow_le_ep
    _ = FloatSpec.Core.Raux.bpow beta ferr.Fexp := by simp [ferr]
    _ ≤ |_root_.F2R ferr| := hferr_ge
    _ = |FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x * y) - (x * y)| := by
          simpa [herr_repr, fexp]

/-- Multiplication by power of beta is exact in FLT -/
lemma mult_bpow_exact_FLT (x : ℝ) (e : Int)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (h_bound : emin + prec - mag beta x ≤ e) :
  generic_format beta (FLT_exp emin prec) (x * FloatSpec.Core.Raux.bpow beta e) := by
  classical
  set fexp : Int → Int := FLT_exp emin prec
  by_cases hx0 : x = 0
  · subst x
    simpa using
      (FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp))
  · set n : Int := e
    set m : Int := FloatSpec.Core.Raux.Ztrunc
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)
    set ex : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x
    have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
    have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos_real
    have hpow : FloatSpec.Core.Raux.bpow beta e = (beta : ℝ) ^ n := by
      simp [FloatSpec.Core.Raux.bpow, n]
    have hx_repr : x = (m : ℝ) * (beta : ℝ) ^ ex := by
      simpa [m, ex, fexp, generic_format] using hx
    let f : FloatSpec.Core.Defs.FlocqFloat beta :=
      FloatSpec.Core.Defs.FlocqFloat.mk m (ex + n)
    have htarget :
        x * FloatSpec.Core.Raux.bpow beta e = _root_.F2R f := by
      calc
        x * FloatSpec.Core.Raux.bpow beta e
            = ((m : ℝ) * (beta : ℝ) ^ ex) * (beta : ℝ) ^ n := by
                rw [hx_repr, hpow]
        _ = (m : ℝ) * ((beta : ℝ) ^ ex * (beta : ℝ) ^ n) := by ring
        _ = (m : ℝ) * (beta : ℝ) ^ (ex + n) := by
                rw [(_root_.zpow_add₀ hbne ex n).symm]
        _ = _root_.F2R f := by
                simp [f, _root_.F2R, FloatSpec.Core.Defs.F2R]
    have hmag :
        FloatSpec.Core.Raux.mag beta
            (x * FloatSpec.Core.Raux.bpow beta e) =
          FloatSpec.Core.Raux.mag beta x + n := by
      rw [hpow]
      exact FloatSpec.Calc.Sqrt.mag_mult_bpow_eq beta x n hx0 hβ
    have hflt_left :
        emin ≤ FloatSpec.Core.FLT.FLT_exp prec emin
          (FloatSpec.Core.Raux.mag beta x + n) := by
      simp [FloatSpec.Core.FLT.FLT_exp]
    have hflt_right :
        FloatSpec.Core.Raux.mag beta x + n - prec ≤ ex + n := by
      have hleft : FloatSpec.Core.Raux.mag beta x - prec ≤ ex := by
        have hex_def :
            ex = max (FloatSpec.Core.Raux.mag beta x - prec) emin := by
          simp [ex, fexp, FloatSpec.Core.Generic_fmt.cexp, FLT_exp,
            FloatSpec.Core.FLT.FLT_exp]
        rw [hex_def]
        exact le_max_left _ _
      grind
    have hflt_bound :
        FloatSpec.Core.FLT.FLT_exp prec emin
            (FloatSpec.Core.Raux.mag beta x + n) ≤ ex + n := by
      have hemin_le : emin ≤ ex + n := by
        have hbound' : emin + prec - FloatSpec.Core.Raux.mag beta x ≤ n := by
          simpa [n] using h_bound
        grind
      simpa [FloatSpec.Core.FLT.FLT_exp] using
        (max_le hflt_right hemin_le)
    have hcexp :
        FloatSpec.Core.Generic_fmt.cexp beta fexp
            (x * FloatSpec.Core.Raux.bpow beta e) ≤
          ex + n := by
      calc
        FloatSpec.Core.Generic_fmt.cexp beta fexp
            (x * FloatSpec.Core.Raux.bpow beta e)
            = FloatSpec.Core.FLT.FLT_exp prec emin
                (FloatSpec.Core.Raux.mag beta
                  (x * FloatSpec.Core.Raux.bpow beta e)) := by
                simp [FloatSpec.Core.Generic_fmt.cexp, fexp, FLT_exp]
        _ = FloatSpec.Core.FLT.FLT_exp prec emin
              (FloatSpec.Core.Raux.mag beta x + n) := by
                rw [hmag]
        _ ≤ ex + n := hflt_bound
    have hfmt := FloatSpec.Core.Generic_fmt.generic_format_F2R'
      (beta := beta) (fexp := fexp)
      (x := x * FloatSpec.Core.Raux.bpow beta e)
      (f := f) ⟨hβ, htarget.symm, by
        intro _
        simpa [f] using hcexp⟩
    simpa [fexp] using hfmt

/-- Multiplication by positive power of beta is exact in FLT -/
lemma mult_bpow_pos_exact_FLT (x : ℝ) (e : Int)
  (hβ : 1 < beta)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (h_nonneg : 0 ≤ e) :
  generic_format beta (FLT_exp emin prec) (x * FloatSpec.Core.Raux.bpow beta e) := by
  classical
  set fexp : Int → Int := FLT_exp emin prec
  by_cases hx0 : x = 0
  · subst x
    simpa using
      (FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := fexp))
  · set n : Int := e
    set m : Int := FloatSpec.Core.Raux.Ztrunc
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)
    set ex : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x
    have hbpos_int : (0 : Int) < beta := lt_trans (by decide) hβ
    have hbpos_real : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos_real
    have hpow : FloatSpec.Core.Raux.bpow beta e = (beta : ℝ) ^ n := by
      simp [FloatSpec.Core.Raux.bpow, n]
    have hx_repr : x = (m : ℝ) * (beta : ℝ) ^ ex := by
      simpa [m, ex, fexp, generic_format] using hx
    let f : FloatSpec.Core.Defs.FlocqFloat beta :=
      FloatSpec.Core.Defs.FlocqFloat.mk m (ex + n)
    have htarget :
        x * FloatSpec.Core.Raux.bpow beta e = _root_.F2R f := by
      calc
        x * FloatSpec.Core.Raux.bpow beta e
            = ((m : ℝ) * (beta : ℝ) ^ ex) * (beta : ℝ) ^ n := by
                rw [hx_repr, hpow]
        _ = (m : ℝ) * ((beta : ℝ) ^ ex * (beta : ℝ) ^ n) := by ring
        _ = (m : ℝ) * (beta : ℝ) ^ (ex + n) := by
                rw [(_root_.zpow_add₀ hbne ex n).symm]
        _ = _root_.F2R f := by
                simp [f, _root_.F2R, FloatSpec.Core.Defs.F2R]
    have hmag :
        FloatSpec.Core.Raux.mag beta
            (x * FloatSpec.Core.Raux.bpow beta e) =
          FloatSpec.Core.Raux.mag beta x + n := by
      rw [hpow]
      exact FloatSpec.Calc.Sqrt.mag_mult_bpow_eq beta x n hx0 hβ
    have hflt_right :
        FloatSpec.Core.Raux.mag beta x + n - prec ≤ ex + n := by
      have hleft : FloatSpec.Core.Raux.mag beta x - prec ≤ ex := by
        have hex_def :
            ex = max (FloatSpec.Core.Raux.mag beta x - prec) emin := by
          simp [ex, fexp, FloatSpec.Core.Generic_fmt.cexp, FLT_exp,
            FloatSpec.Core.FLT.FLT_exp]
        rw [hex_def]
        exact le_max_left _ _
      grind
    have hflt_bound :
        FloatSpec.Core.FLT.FLT_exp prec emin
            (FloatSpec.Core.Raux.mag beta x + n) ≤ ex + n := by
      have hemin_le : emin ≤ ex + n := by
        have hex_def :
            ex = max (FloatSpec.Core.Raux.mag beta x - prec) emin := by
          simp [ex, fexp, FloatSpec.Core.Generic_fmt.cexp, FLT_exp,
            FloatSpec.Core.FLT.FLT_exp]
        have hemin_ex : emin ≤ ex := by
          rw [hex_def]
          exact le_max_right _ _
        have hex_exn : ex ≤ ex + n := by
          have hn : 0 ≤ n := by simpa [n] using h_nonneg
          grind
        exact le_trans hemin_ex hex_exn
      simpa [FloatSpec.Core.FLT.FLT_exp] using
        (max_le hflt_right hemin_le)
    have hcexp :
        FloatSpec.Core.Generic_fmt.cexp beta fexp
            (x * FloatSpec.Core.Raux.bpow beta e) ≤
          ex + n := by
      calc
        FloatSpec.Core.Generic_fmt.cexp beta fexp
            (x * FloatSpec.Core.Raux.bpow beta e)
            = FloatSpec.Core.FLT.FLT_exp prec emin
                (FloatSpec.Core.Raux.mag beta
                  (x * FloatSpec.Core.Raux.bpow beta e)) := by
                simp [FloatSpec.Core.Generic_fmt.cexp, fexp, FLT_exp]
        _ = FloatSpec.Core.FLT.FLT_exp prec emin
              (FloatSpec.Core.Raux.mag beta x + n) := by
                rw [hmag]
        _ ≤ ex + n := hflt_bound
    have hfmt := FloatSpec.Core.Generic_fmt.generic_format_F2R'
      (beta := beta) (fexp := fexp)
      (x := x * FloatSpec.Core.Raux.bpow beta e)
      (f := f) ⟨hβ, htarget.symm, by
        intro _
        simpa [f] using hcexp⟩
    simpa [fexp] using hfmt
