import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import Mathlib.Data.Real.Basic

-- Relative error of the roundings
-- Translated from Coq file: flocq/src/Prop/Relative.v

open Real

variable (beta : Int) [ValidRadix beta]

-- Section: Relative error conversions

variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp fexp]

/-- Relative error less than conversion -/
lemma relative_error_lt_conversion (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x b : ℝ)
  (h_pos : 0 < b)
  (h_bound : x ≠ 0 → |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| < b * |x|) :
  ∃ eps, |eps| < b ∧ FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x = x * (1 + eps) := by
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa using h_pos
    · subst x
      have hrnd0 : rnd (0 : ℝ) = 0 := by
        simpa using
          (FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) 0)
      have hround0 :
          FloatSpec.Calc.Round.round beta fexp
            (FloatSpec.Calc.Round.Mode.ofRnd rnd) 0 = 0 := by
        simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
          FloatSpec.Core.Generic_fmt.scaled_mantissa,
          FloatSpec.Calc.Round.Mode.ofRnd, hrnd0]
      simpa using hround0
  · refine ⟨(FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x) / x, ?_, ?_⟩
    · have h := h_bound hx
      have hx_abs_pos : 0 < |x| := abs_pos.mpr hx
      have hdiv := div_lt_div_of_pos_right h hx_abs_pos
      have hrhs : (b * |x|) / |x| = b := by
        field_simp [ne_of_gt hx_abs_pos]
      simpa [abs_div, hrhs] using hdiv
    · field_simp [hx]
      ring

/-- Relative error less than or equal conversion -/
lemma relative_error_le_conversion (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x b : ℝ)
  (h_nonneg : 0 ≤ b)
  (h_bound : |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| ≤ b * |x|) :
  ∃ eps, |eps| ≤ b ∧ FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x = x * (1 + eps) := by
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa using h_nonneg
    · subst x
      have hrnd0 : rnd (0 : ℝ) = 0 := by
        simpa using
          (FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) 0)
      have hround0 :
          FloatSpec.Calc.Round.round beta fexp
            (FloatSpec.Calc.Round.Mode.ofRnd rnd) 0 = 0 := by
        simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
          FloatSpec.Core.Generic_fmt.scaled_mantissa,
          FloatSpec.Calc.Round.Mode.ofRnd, hrnd0]
      simpa using hround0
  · refine ⟨(FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x) / x, ?_, ?_⟩
    · have hx_abs_pos : 0 < |x| := abs_pos.mpr hx
      have hdiv := div_le_div_of_nonneg_right h_bound (le_of_lt hx_abs_pos)
      have hrhs : (b * |x|) / |x| = b := by
        field_simp [ne_of_gt hx_abs_pos]
      simpa [abs_div, hrhs] using hdiv
    · field_simp [hx]
      ring

/-- Relative error less than or equal conversion inverse -/
lemma relative_error_le_conversion_inv_from_valid_rnd_payload
    (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x b : ℝ)
  (h_exists : ∃ eps, |eps| ≤ b ∧ FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x = x * (1 + eps)) :
  |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| ≤ b * |x| := by
  rcases h_exists with ⟨eps, heps, hround⟩
  rw [hround]
  have hcalc : x * (1 + eps) - x = eps * x := by ring
  rw [hcalc]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right heps (abs_nonneg x)

/-- Exact Coq contract: the converse is algebraic and accepts an arbitrary
integer rounding function. -/
lemma relative_error_le_conversion_inv (rnd : ℝ → Int) (x b : ℝ)
  (h_exists : ∃ eps, |eps| ≤ b ∧
    FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x = x * (1 + eps)) :
  |FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x - x| ≤ b * |x| := by
  rcases h_exists with ⟨eps, heps, hround⟩
  rw [hround]
  have hcalc : x * (1 + eps) - x = eps * x := by ring
  rw [hcalc, abs_mul]
  exact mul_le_mul_of_nonneg_right heps (abs_nonneg x)

/-- Relative error less than or equal conversion round inverse -/
lemma relative_error_le_conversion_round_inv_from_valid_rnd_payload
    (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x b : ℝ)
  (h_exists : ∃ eps, |eps| ≤ b ∧ x = FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x * (1 + eps)) :
  |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| ≤ b * |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x| := by
  rcases h_exists with ⟨eps, heps, hx⟩
  set rx : ℝ := FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x with hrx
  have hx' : x = rx * (1 + eps) := by
    simpa [hrx] using hx
  rw [hx']
  have hcalc : rx - rx * (1 + eps) = -(eps * rx) := by ring
  rw [hcalc]
  rw [abs_neg, abs_mul]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_right heps (abs_nonneg rx)

/-- Exact Coq contract: no `Valid_rnd` premise is exported. -/
lemma relative_error_le_conversion_round_inv (rnd : ℝ → Int) (x b : ℝ)
  (h_exists : ∃ eps, |eps| ≤ b ∧
    x = FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x * (1 + eps)) :
  |FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x - x| ≤
    b * |FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x| := by
  rcases h_exists with ⟨eps, heps, hx⟩
  set rx : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x
  have hx' : x = rx * (1 + eps) := by simpa [rx] using hx
  rw [hx']
  have hcalc : rx - rx * (1 + eps) = -(eps * rx) := by ring
  rw [hcalc, abs_neg, abs_mul]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_right heps (abs_nonneg rx)

-- Section: Generic relative error

variable (emin p : Int)
variable (h_min : ∀ k, emin < k → p ≤ k - fexp k)

private lemma valid_rnd_error_lt_one (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ) :
    |((rnd x : Int) : ℝ) - x| < (1 : ℝ) := by
  classical
  have hcases : rnd x = Int.floor x ∨ rnd x = Int.ceil x := by
    have h := (FloatSpec.Core.Generic_fmt.Zrnd_DN_or_UP rnd x) True.intro
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using h
  have hfloor_le : (Int.floor x : ℝ) ≤ x := Int.floor_le x
  have hx_lt_floor_add : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
  rcases hcases with hr | hr
  · have hnonpos : ((rnd x : Int) : ℝ) - x ≤ 0 := by
      rw [hr]
      exact sub_nonpos.mpr hfloor_le
    rw [abs_of_nonpos hnonpos, hr]
    linarith
  · have hx_le : x ≤ (Int.ceil x : ℝ) := Int.le_ceil x
    have hceil_le : (Int.ceil x : ℝ) ≤ (Int.floor x : ℝ) + 1 := by
      have hceil_int : Int.ceil x ≤ Int.floor x + 1 := by
        have hxle : x ≤ ((Int.floor x + 1 : Int) : ℝ) := by
          simpa [Int.cast_add, Int.cast_one] using le_of_lt hx_lt_floor_add
        exact (Int.ceil_le).mpr hxle
      exact_mod_cast hceil_int
    have hnonneg : 0 ≤ ((rnd x : Int) : ℝ) - x := by
      rw [hr]
      exact sub_nonneg.mpr hx_le
    rw [abs_of_nonneg hnonneg, hr]
    by_contra hnot
    have hge : (1 : ℝ) ≤ (Int.ceil x : ℝ) - x := le_of_not_gt hnot
    by_cases hint : x = (Int.floor x : ℝ)
    · rw [hint] at hge
      norm_num at hge
    · have hfloor_lt : (Int.floor x : ℝ) < x :=
        lt_of_le_of_ne hfloor_le (Ne.symm hint)
      have hceil_sub_le : (Int.ceil x : ℝ) - x ≤ ((Int.floor x : ℝ) + 1) - x :=
        sub_le_sub_right hceil_le x
      have hfloor_sub_lt : ((Int.floor x : ℝ) + 1) - x < 1 := by
        linarith
      linarith

/-- Relative error bound -/
theorem relative_error (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
  (hβ : 1 < beta)
  (h_min : ∀ k, emin < k → p ≤ k - fexp k)
  (h_bound : (beta : ℝ) ^ emin ≤ |x|) :
  |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| <
    (beta : ℝ) ^ (-p + 1) * |x| := by
  classical
  by_cases hx : x = 0
  · subst x
    have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    have hpow_pos : 0 < (beta : ℝ) ^ emin := zpow_pos hbpos emin
    have hbad : (beta : ℝ) ^ emin ≤ 0 := by simpa using h_bound
    exact False.elim ((not_le_of_gt hpow_pos) hbad)
  · let M : Int := FloatSpec.Core.Raux.mag beta x
    let e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x
    let sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x
    let rz : Int := rnd sm
    have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
    have hbge1 : (1 : ℝ) ≤ (beta : ℝ) := by
      have : (1 : Int) ≤ beta := le_of_lt hβ
      exact_mod_cast this
    have hM_lower : emin + 1 ≤ M := by
      rcases lt_or_eq_of_le h_bound with hlt | heq
      · have htrip := FloatSpec.Core.Raux.mag_ge_bpow
          (beta := beta) (x := x) (e := emin + 1) hβ
          (le_of_lt (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlt))
        simpa [M] using htrip
      · have hmag_abs := FloatSpec.Core.Raux.mag_abs (beta := beta) (x := x) hβ
        have hmag_abs_run :
            FloatSpec.Core.Raux.mag beta |x| = FloatSpec.Core.Raux.mag beta x := by
          simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using hmag_abs trivial
        have hmag_bpow := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := emin) hβ
        have hmag_bpow_run :
            FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ emin) = emin + 1 := by
          simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using hmag_bpow trivial
        have hmag_x : emin + 1 = M := by
          calc
            emin + 1 = FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ emin) := hmag_bpow_run.symm
            _ = FloatSpec.Core.Raux.mag beta |x| := by simpa [heq]
            _ = FloatSpec.Core.Raux.mag beta x := hmag_abs_run
            _ = M := by rfl
        exact le_of_eq hmag_x
    have hM_gt_emin : emin < M := by omega
    have he_eq : e = fexp M := by
      simp [e, M, FloatSpec.Core.Generic_fmt.cexp]
    have he_le : e ≤ M - p := by
      have hp := h_min M hM_gt_emin
      rw [he_eq]
      omega
    have hpow_le_mag : (beta : ℝ) ^ e ≤ (beta : ℝ) ^ (M - p) :=
      zpow_le_zpow_right₀ hbge1 he_le
    have hmag_low : (beta : ℝ) ^ (M - 1) ≤ |x| := by
      have h :=
        (FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := x) hβ hx)
          True.intro
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, M,
        FloatSpec.Core.Raux.abs_val] using h
    have hpow_factor :
        (beta : ℝ) ^ (M - p) = (beta : ℝ) ^ (-p + 1) * (beta : ℝ) ^ (M - 1) := by
      rw [← zpow_add₀ hbne]
      congr 1
      ring
    have hpow_le :
        (beta : ℝ) ^ e ≤ (beta : ℝ) ^ (-p + 1) * |x| := by
      calc
        (beta : ℝ) ^ e ≤ (beta : ℝ) ^ (M - p) := hpow_le_mag
        _ = (beta : ℝ) ^ (-p + 1) * (beta : ℝ) ^ (M - 1) := hpow_factor
        _ ≤ (beta : ℝ) ^ (-p + 1) * |x| := by
          exact mul_le_mul_of_nonneg_left hmag_low (le_of_lt (zpow_pos hbpos (-p + 1)))
    have hscaled : sm * (beta : ℝ) ^ e = x := by
      have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
        (beta := beta) (fexp := fexp) (x := x)
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, e] using htrip hβ
    have hround :
        FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x =
          (rz : ℝ) * (beta : ℝ) ^ e := by
      simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa,
        FloatSpec.Calc.Round.Mode.ofRnd, e, sm, rz]
    have hrnd_lt : |(rz : ℝ) - sm| < (1 : ℝ) := by
      simpa [rz] using valid_rnd_error_lt_one rnd sm
    have hdiff :
        FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x =
          ((rz : ℝ) - sm) * (beta : ℝ) ^ e := by
      rw [hround, ← hscaled]
      ring
    rw [hdiff, abs_mul, abs_of_pos (zpow_pos hbpos e)]
    have hlocal_lt :
        |(rz : ℝ) - sm| * (beta : ℝ) ^ e < (1 : ℝ) * (beta : ℝ) ^ e :=
      mul_lt_mul_of_pos_right hrnd_lt (zpow_pos hbpos e)
    calc
      |(rz : ℝ) - sm| * (beta : ℝ) ^ e
          < (1 : ℝ) * (beta : ℝ) ^ e := hlocal_lt
      _ = (beta : ℝ) ^ e := by ring
      _ ≤ (beta : ℝ) ^ (-p + 1) * |x| := hpow_le

/-- Relative error existence -/
theorem relative_error_ex (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
  (hβ : 1 < beta)
  (h_min : ∀ k, emin < k → p ≤ k - fexp k)
  (h_bound : (beta : ℝ) ^ emin ≤ |x|) :
  ∃ eps, |eps| < (beta : ℝ) ^ (-p + 1) ∧
    FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x = x * (1 + eps) := by
  have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  exact relative_error_lt_conversion (beta := beta) (fexp := fexp) (rnd := rnd)
    x ((beta : ℝ) ^ (-p + 1)) (zpow_pos hbpos (-p + 1))
    (fun _ => relative_error (beta := beta) (fexp := fexp) (emin := emin) (p := p)
      rnd x hβ h_min h_bound)

/-- Relative error F2R emin -/
theorem relative_error_F2R_emin (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (m : Int)
  (hβ : 1 < beta)
  (h_min : ∀ k, emin < k → p ≤ k - fexp k)
  (h_nonzero : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) ≠ 0) :
  |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| <
    (beta : ℝ) ^ (-p + 1) *
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| := by
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk m emin
  let x : ℝ := F2R f
  change |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| <
    (beta : ℝ) ^ (-p + 1) * |x|
  have hm_ne : m ≠ 0 := by
    intro hm
    apply h_nonzero
    simp [f, hm, _root_.F2R, FloatSpec.Core.Defs.F2R]
  have hm_abs_pos_nat : 0 < Int.natAbs m := Int.natAbs_pos.mpr hm_ne
  have hm_abs_pos : (0 : Int) < (Int.natAbs m : Int) := by
    exact_mod_cast hm_abs_pos_nat
  let fabs : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk (Int.natAbs m) emin
  have hFabs : |x| = F2R fabs := by
    have h := FloatSpec.Core.Float_prop.F2R_Zabs (beta := beta) f hβ
    change |FloatSpec.Core.Defs.F2R f| =
      FloatSpec.Core.Defs.F2R
        (FloatSpec.Core.Defs.FlocqFloat.mk (Int.natAbs m) emin :
          FloatSpec.Core.Defs.FlocqFloat beta)
    exact h
  have hlow_abs : (beta : ℝ) ^ emin ≤ F2R fabs :=
    FloatSpec.Core.Float_prop.bpow_le_F2R (beta := beta) (f := fabs) hβ hm_abs_pos
  have h_bound : (beta : ℝ) ^ emin ≤ |x| := by
    calc
      (beta : ℝ) ^ emin ≤ F2R fabs := hlow_abs
      _ = |x| := hFabs.symm
  exact relative_error (beta := beta) (fexp := fexp) (emin := emin) (p := p)
    rnd x hβ h_min h_bound

/-- Relative error F2R emin existence -/
theorem relative_error_F2R_emin_ex (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (m : Int)
  (hβ : 1 < beta)
  (h_min : ∀ k, emin < k → p ≤ k - fexp k) :
  ∃ eps, |eps| < (beta : ℝ) ^ (-p + 1) ∧
    FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) =
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) * (1 + eps) := by
  have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  exact relative_error_lt_conversion (beta := beta) (fexp := fexp) (rnd := rnd)
    (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta))
    ((beta : ℝ) ^ (-p + 1)) (zpow_pos hbpos (-p + 1))
    (fun hne => relative_error_F2R_emin (beta := beta) (fexp := fexp)
      (emin := emin) (p := p) rnd m hβ h_min hne)

-- Section: Nearest rounding relative error

variable (choice : Int → Bool)

/-- Relative error nearest -/
theorem relative_error_N (x : ℝ)
  (hβ : 1 < beta)
  (h_min : ∀ k, emin < k → p ≤ k - fexp k)
  (h_bound : (beta : ℝ) ^ emin ≤ |x|) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| ≤
    (1/2) * (beta : ℝ) ^ (-p + 1) * |x| := by
  classical
  by_cases hx : x = 0
  · subst x
    have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
      unfold FloatSpec.Core.Generic_fmt.Znearest
      simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
    simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
      FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
  · let M : Int := FloatSpec.Core.Raux.mag beta x
    let e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x
    let sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x
    let zn : Int := FloatSpec.Core.Generic_fmt.Znearest choice sm
    have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
    have hbge1 : (1 : ℝ) ≤ (beta : ℝ) := by
      have : (1 : Int) ≤ beta := le_of_lt hβ
      exact_mod_cast this
    have hM_lower : emin + 1 ≤ M := by
      rcases lt_or_eq_of_le h_bound with hlt | heq
      · have htrip := FloatSpec.Core.Raux.mag_ge_bpow
          (beta := beta) (x := x) (e := emin + 1) hβ
          (le_of_lt (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlt))
        simpa [M] using htrip
      · have hmag_abs := FloatSpec.Core.Raux.mag_abs (beta := beta) (x := x) hβ
        have hmag_abs_run :
            FloatSpec.Core.Raux.mag beta |x| = FloatSpec.Core.Raux.mag beta x := by
          simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using hmag_abs trivial
        have hmag_bpow := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := emin) hβ
        have hmag_bpow_run :
            FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ emin) = emin + 1 := by
          simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using hmag_bpow trivial
        have hmag_x : emin + 1 = M := by
          calc
            emin + 1 = FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ emin) := hmag_bpow_run.symm
            _ = FloatSpec.Core.Raux.mag beta |x| := by simpa [heq]
            _ = FloatSpec.Core.Raux.mag beta x := hmag_abs_run
            _ = M := by rfl
        exact le_of_eq hmag_x
    have hM_gt_emin : emin < M := by omega
    have he_eq : e = fexp M := by
      simp [e, M, FloatSpec.Core.Generic_fmt.cexp]
    have he_le : e ≤ M - p := by
      have hp := h_min M hM_gt_emin
      rw [he_eq]
      omega
    have hpow_le_mag : (beta : ℝ) ^ e ≤ (beta : ℝ) ^ (M - p) :=
      zpow_le_zpow_right₀ hbge1 he_le
    have hmag_low : (beta : ℝ) ^ (M - 1) ≤ |x| := by
      have h :=
        (FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := x) hβ hx)
          True.intro
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, M,
        FloatSpec.Core.Raux.abs_val] using h
    have hpow_factor :
        (beta : ℝ) ^ (M - p) = (beta : ℝ) ^ (-p + 1) * (beta : ℝ) ^ (M - 1) := by
      rw [← zpow_add₀ hbne]
      congr 1
      ring
    have hpow_le :
        (beta : ℝ) ^ e ≤ (beta : ℝ) ^ (-p + 1) * |x| := by
      calc
        (beta : ℝ) ^ e ≤ (beta : ℝ) ^ (M - p) := hpow_le_mag
        _ = (beta : ℝ) ^ (-p + 1) * (beta : ℝ) ^ (M - 1) := hpow_factor
        _ ≤ (beta : ℝ) ^ (-p + 1) * |x| := by
          exact mul_le_mul_of_nonneg_left hmag_low (le_of_lt (zpow_pos hbpos (-p + 1)))
    have hscaled : sm * (beta : ℝ) ^ e = x := by
      have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
        (beta := beta) (fexp := fexp) (x := x)
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, e] using htrip hβ
    have hround :
        FloatSpec.Calc.Round.round beta fexp (Znearest choice) x =
          (zn : ℝ) * (beta : ℝ) ^ e := by
      simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode, e, sm, zn]
    have hnearest : |(zn : ℝ) - sm| ≤ (1 / 2 : ℝ) := by
      have htrip := FloatSpec.Core.Generic_fmt.Znearest_half choice sm
      simpa [zn, abs_sub_comm,
        Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip
    have hdiff :
        FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x =
          ((zn : ℝ) - sm) * (beta : ℝ) ^ e := by
      rw [hround, ← hscaled]
      ring
    rw [hdiff, abs_mul, abs_of_pos (zpow_pos hbpos e)]
    calc
      |(zn : ℝ) - sm| * (beta : ℝ) ^ e
          ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ e :=
            mul_le_mul_of_nonneg_right hnearest (le_of_lt (zpow_pos hbpos e))
      _ ≤ (1 / 2 : ℝ) * ((beta : ℝ) ^ (-p + 1) * |x|) :=
            mul_le_mul_of_nonneg_left hpow_le (by norm_num)
      _ = (1 / 2 : ℝ) * (beta : ℝ) ^ (-p + 1) * |x| := by ring

/-- Relative error nearest existence -/
theorem relative_error_N_ex (x : ℝ)
  (hβ : 1 < beta)
  (h_min : ∀ k, emin < k → p ≤ k - fexp k)
  (h_bound : (beta : ℝ) ^ emin ≤ |x|) :
  ∃ eps, |eps| ≤ (1/2) * (beta : ℝ) ^ (-p + 1) ∧
    FloatSpec.Calc.Round.round beta fexp (Znearest choice) x = x * (1 + eps) := by
  let b : ℝ := (1 / 2 : ℝ) * (beta : ℝ) ^ (-p + 1)
  have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hb_nonneg : 0 ≤ b := by
    exact mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbpos (-p + 1)))
  have hbound :
      |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| ≤ b * |x| := by
    simpa [b] using
      (relative_error_N (beta := beta) (fexp := fexp) (emin := emin) (p := p)
        (choice := choice) x hβ h_min h_bound)
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa [b] using hb_nonneg
    · subst x
      have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
        unfold FloatSpec.Core.Generic_fmt.Znearest
        simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
      simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
  · refine ⟨(FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x) / x, ?_, ?_⟩
    · have hx_abs_pos : 0 < |x| := abs_pos.mpr hx
      have hdiv := div_le_div_of_nonneg_right hbound (le_of_lt hx_abs_pos)
      have hrhs : (b * |x|) / |x| = b := by
        field_simp [ne_of_gt hx_abs_pos]
      have hratio :
          |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| / |x| ≤ b := by
        calc
          |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| / |x|
              ≤ (b * |x|) / |x| := hdiv
          _ = b := hrhs
      simpa [abs_div, b] using hratio
    · field_simp [hx]
      ring

/-- Relative error nearest F2R emin -/
theorem relative_error_N_F2R_emin (m : Int) (hβ : 1 < beta)
  (h_min : ∀ k, emin < k → p ≤ k - fexp k) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| ≤
    (1/2) * (beta : ℝ) ^ (-p + 1) *
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| := by
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk m emin
  let x : ℝ := F2R f
  change |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| ≤
    (1 / 2) * (beta : ℝ) ^ (-p + 1) * |x|
  by_cases hx : x = 0
  · have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
      unfold FloatSpec.Core.Generic_fmt.Znearest
      simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
    have hround0 :
        FloatSpec.Calc.Round.round beta fexp (Znearest choice) x = 0 := by
      rw [hx]
      simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
    rw [hx] at hround0
    simpa [hx, hround0]
  · have hm_ne : m ≠ 0 := by
      intro hm
      apply hx
      simp [x, f, hm, _root_.F2R, FloatSpec.Core.Defs.F2R]
    have hm_abs_pos_nat : 0 < Int.natAbs m := Int.natAbs_pos.mpr hm_ne
    have hm_abs_pos : (0 : Int) < (Int.natAbs m : Int) := by
      exact_mod_cast hm_abs_pos_nat
    let fabs : FloatSpec.Core.Defs.FlocqFloat beta :=
      FloatSpec.Core.Defs.FlocqFloat.mk (Int.natAbs m) emin
    have hFabs :
        |x| = F2R fabs := by
      have h := FloatSpec.Core.Float_prop.F2R_Zabs (beta := beta) f hβ
      change |FloatSpec.Core.Defs.F2R f| =
        FloatSpec.Core.Defs.F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk (Int.natAbs m) emin :
            FloatSpec.Core.Defs.FlocqFloat beta)
      exact h
    have hlow_abs :
        (beta : ℝ) ^ emin ≤ F2R fabs :=
      FloatSpec.Core.Float_prop.bpow_le_F2R (beta := beta) (f := fabs) hβ hm_abs_pos
    have h_bound : (beta : ℝ) ^ emin ≤ |x| := by
      calc
        (beta : ℝ) ^ emin ≤ F2R fabs := hlow_abs
        _ = |x| := hFabs.symm
    exact relative_error_N (beta := beta) (fexp := fexp) (emin := emin) (p := p)
      (choice := choice) x hβ h_min h_bound

/-- Relative error nearest F2R emin existence -/
theorem relative_error_N_F2R_emin_ex (m : Int) (hβ : 1 < beta)
  (h_min : ∀ k, emin < k → p ≤ k - fexp k) :
  ∃ eps, |eps| ≤ (1/2) * (beta : ℝ) ^ (-p + 1) ∧
    FloatSpec.Calc.Round.round beta fexp (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) =
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) * (1 + eps) := by
  let x : ℝ :=
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)
  let b : ℝ := (1 / 2 : ℝ) * (beta : ℝ) ^ (-p + 1)
  have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hb_nonneg : 0 ≤ b :=
    mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbpos (-p + 1)))
  have hbound :
      |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| ≤ b * |x| := by
    simpa [x, b] using
      (relative_error_N_F2R_emin (beta := beta) (fexp := fexp)
        (emin := emin) (p := p) (choice := choice) m hβ h_min)
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa [b] using hb_nonneg
    · have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
        unfold FloatSpec.Core.Generic_fmt.Znearest
        simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
      simp [x, hx, FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
  · refine ⟨(FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x) / x, ?_, ?_⟩
    · have hx_abs_pos : 0 < |x| := abs_pos.mpr hx
      have hdiv := div_le_div_of_nonneg_right hbound (le_of_lt hx_abs_pos)
      have hrhs : (b * |x|) / |x| = b := by
        field_simp [ne_of_gt hx_abs_pos]
      have hratio :
          |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| / |x| ≤ b := by
        calc
          |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| / |x|
              ≤ (b * |x|) / |x| := hdiv
          _ = b := hrhs
      simpa [x, b, abs_div] using hratio
    · field_simp [hx]
      ring

/-- Relative error nearest round -/
theorem relative_error_N_round (h_pos : 0 < p) (x : ℝ)
  (hβ : 1 < beta)
  (h_min : ∀ k, emin < k → p ≤ k - fexp k)
  (h_bound : (beta : ℝ) ^ emin ≤ |x|) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| ≤
    (1/2) * (beta : ℝ) ^ (-p + 1) *
    |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x| := by
  classical
  by_cases hx0 : x = 0
  · subst x
    have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
      unfold FloatSpec.Core.Generic_fmt.Znearest
      simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
    simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
      FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
  · set rnd : ℝ → Int := FloatSpec.Core.Generic_fmt.Znearest choice
    set rx : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x
    set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexp x
    set ex : Int := FloatSpec.Core.Raux.mag beta x
    set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x
    set zn : Int := FloatSpec.Core.Generic_fmt.Znearest choice sm
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposℝ : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposℝ
    have hpow_nonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt (zpow_pos hbposℝ e)
    have hcalc_round :
        FloatSpec.Calc.Round.round beta fexp (Znearest choice) x = rx := by
      simp [rx, rnd, FloatSpec.Calc.Round.round, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode]
    rw [hcalc_round]
    have hscaled : sm * (beta : ℝ) ^ e = x := by
      have h :=
        (FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
          (beta := beta) (fexp := fexp) (x := x)) hβ
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, e] using h
    have hrx :
        rx = (zn : ℝ) * (beta : ℝ) ^ e := by
      simp [rx, rnd, zn, sm, e, FloatSpec.Core.Generic_fmt.roundR]
    have hnearest : |(zn : ℝ) - sm| ≤ (1 / 2 : ℝ) := by
      have h :=
        (FloatSpec.Core.Generic_fmt.Znearest_half choice sm)
      simpa [zn, abs_sub_comm,
        Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using h
    have hlocal : |rx - x| ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ e := by
      have hdiff : rx - x = ((zn : ℝ) - sm) * (beta : ℝ) ^ e := by
        rw [hrx, ← hscaled]
        ring
      rw [hdiff, abs_mul, abs_of_nonneg hpow_nonneg]
      exact mul_le_mul_of_nonneg_right hnearest hpow_nonneg
    have hmag_low : (beta : ℝ) ^ (ex - 1) ≤ |x| := by
      have h :=
        (FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := x) hβ hx0) True.intro
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
        FloatSpec.Core.Raux.abs_val, ex] using h
    have hmag_high : |x| < (beta : ℝ) ^ ex := by
      have h :=
        (FloatSpec.Core.Raux.mag_upper_bound (beta := beta) (x := x) hβ hx0) True.intro
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
        FloatSpec.Core.Raux.abs_val, ex] using h
    have hemin_lt_ex : emin < ex := by
      rcases lt_or_eq_of_le h_bound with hlt | heq
      · have hmag :=
          (FloatSpec.Core.Raux.mag_ge_bpow (beta := beta) (x := x) (e := emin + 1)
            hβ (le_of_lt (by simpa using hlt)))
        have hrun : emin + 1 ≤ ex := by
          simpa [ex] using hmag
        omega
      · have hmag_abs :=
          (FloatSpec.Core.Raux.mag_abs (beta := beta) (x := x) hβ) True.intro
        have hmag_abs_run :
            FloatSpec.Core.Raux.mag beta |x| = ex := by
          simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, ex] using hmag_abs
        have hmag_bpow :=
          (FloatSpec.Core.Raux.mag_bpow beta emin hβ) True.intro
        have hmag_bpow_run :
            FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ emin) = emin + 1 := by
          simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using hmag_bpow
        have hex : ex = emin + 1 := by
          rw [← hmag_abs_run, ← heq, hmag_bpow_run]
        omega
    have hfe_lt_ex : fexp ex < ex := by
      have hp_le : p ≤ ex - fexp ex := h_min ex hemin_lt_ex
      omega
    have hround_abs_low : (beta : ℝ) ^ (ex - 1) ≤ |rx| := by
      by_cases hx_nonneg : 0 ≤ x
      · have hx_low : (beta : ℝ) ^ (ex - 1) ≤ x := by
          simpa [abs_of_nonneg hx_nonneg] using hmag_low
        have hx_high : x < (beta : ℝ) ^ ex := by
          simpa [abs_of_nonneg hx_nonneg] using hmag_high
        have hbounds :=
          FloatSpec.Core.Generic_fmt.roundR_bounded_large_pos
            (beta := beta) (fexp := fexp) (rnd := rnd) (x := x) (ex := ex)
            ⟨hx_low, hx_high⟩ hfe_lt_ex hβ
        exact le_trans hbounds.1 (le_abs_self rx)
      · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
        set rndOpp : ℝ → Int := FloatSpec.Core.Generic_fmt.Zrnd_opp rnd
        set rneg : ℝ := FloatSpec.Core.Generic_fmt.roundR beta fexp rndOpp (-x)
        have hx_low : (beta : ℝ) ^ (ex - 1) ≤ -x := by
          simpa [abs_of_neg hx_neg] using hmag_low
        have hx_high : -x < (beta : ℝ) ^ ex := by
          simpa [abs_of_neg hx_neg] using hmag_high
        have hbounds :=
          FloatSpec.Core.Generic_fmt.roundR_bounded_large_pos
            (beta := beta) (fexp := fexp) (rnd := rndOpp) (x := -x) (ex := ex)
            ⟨hx_low, hx_high⟩ hfe_lt_ex hβ
        have hrx_neg : rx = -rneg := by
          have h :=
            FloatSpec.Core.Generic_fmt.roundR_opp
              (beta := beta) (fexp := fexp) (rnd := rnd) (x := -x) hβ
          simpa [rx, rneg, rndOpp, rnd] using h
        have hrneg_nonneg : 0 ≤ rneg :=
          le_trans (le_of_lt (zpow_pos hbposℝ (ex - 1))) hbounds.1
        have habs_rx : |rx| = rneg := by
          rw [hrx_neg, abs_neg, abs_of_nonneg hrneg_nonneg]
        simpa [habs_rx] using hbounds.1
    have hpow_e_le :
        (beta : ℝ) ^ e ≤ (beta : ℝ) ^ (-p + 1) * |rx| := by
      have he_def : e = fexp ex := by
        simp [e, ex, FloatSpec.Core.Generic_fmt.cexp]
      have he_le_exp : e ≤ ex - p := by
        have hp_le : p ≤ ex - fexp ex := h_min ex hemin_lt_ex
        omega
      have hpow_le_exp : (beta : ℝ) ^ e ≤ (beta : ℝ) ^ (ex - p) := by
        have h := (FloatSpec.Core.Raux.bpow_le beta e (ex - p) hβ he_le_exp) True.intro
        simpa [FloatSpec.Core.Raux.bpow_le_check, Std.Do.wp,
          Std.Do.PostCond.noThrow, Id.run, pure] using h
      have hprod_eq :
          (beta : ℝ) ^ (-p + 1) * (beta : ℝ) ^ (ex - 1) =
            (beta : ℝ) ^ (ex - p) := by
        have hsum : (-p + 1) + (ex - 1) = ex - p := by omega
        calc
          (beta : ℝ) ^ (-p + 1) * (beta : ℝ) ^ (ex - 1)
              = (beta : ℝ) ^ ((-p + 1) + (ex - 1)) := by
                rw [← zpow_add₀ hbne]
          _ = (beta : ℝ) ^ (ex - p) := by rw [hsum]
      have hright :
          (beta : ℝ) ^ (ex - p) ≤ (beta : ℝ) ^ (-p + 1) * |rx| := by
        have hcoeff_nonneg : 0 ≤ (beta : ℝ) ^ (-p + 1) :=
          le_of_lt (zpow_pos hbposℝ (-p + 1))
        have hmul :=
          mul_le_mul_of_nonneg_left hround_abs_low hcoeff_nonneg
        simpa [hprod_eq] using hmul
      exact le_trans hpow_le_exp hright
    exact le_trans hlocal
      (by
        have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hpow_e_le hhalf_nonneg))

/-- Relative error nearest round F2R emin -/
theorem relative_error_N_round_F2R_emin (h_pos : 0 < p) (m : Int) (hβ : 1 < beta)
  (h_min : ∀ k, emin < k → p ≤ k - fexp k) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| ≤
    (1/2) * (beta : ℝ) ^ (-p + 1) *
    |FloatSpec.Calc.Round.round beta fexp (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta))| := by
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk m emin
  let x : ℝ := F2R f
  change |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| ≤
    (1 / 2) * (beta : ℝ) ^ (-p + 1) *
      |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x|
  by_cases hx : x = 0
  · have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
      unfold FloatSpec.Core.Generic_fmt.Znearest
      simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
    have hround0 :
        FloatSpec.Calc.Round.round beta fexp (Znearest choice) x = 0 := by
      rw [hx]
      simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
    rw [hx] at hround0
    simpa [hx, hround0]
  · have hm_ne : m ≠ 0 := by
      intro hm
      apply hx
      simp [x, f, hm, _root_.F2R, FloatSpec.Core.Defs.F2R]
    have hm_abs_pos_nat : 0 < Int.natAbs m := Int.natAbs_pos.mpr hm_ne
    have hm_abs_pos : (0 : Int) < (Int.natAbs m : Int) := by
      exact_mod_cast hm_abs_pos_nat
    let fabs : FloatSpec.Core.Defs.FlocqFloat beta :=
      FloatSpec.Core.Defs.FlocqFloat.mk (Int.natAbs m) emin
    have hFabs :
        |x| = F2R fabs := by
      have h := FloatSpec.Core.Float_prop.F2R_Zabs (beta := beta) f hβ
      change |FloatSpec.Core.Defs.F2R f| =
        FloatSpec.Core.Defs.F2R
          (FloatSpec.Core.Defs.FlocqFloat.mk (Int.natAbs m) emin :
            FloatSpec.Core.Defs.FlocqFloat beta)
      exact h
    have hlow_abs :
        (beta : ℝ) ^ emin ≤ F2R fabs :=
      FloatSpec.Core.Float_prop.bpow_le_F2R (beta := beta) (f := fabs) hβ hm_abs_pos
    have h_bound : (beta : ℝ) ^ emin ≤ |x| := by
      calc
        (beta : ℝ) ^ emin ≤ F2R fabs := hlow_abs
        _ = |x| := hFabs.symm
    exact relative_error_N_round (beta := beta) (fexp := fexp) (emin := emin) (p := p)
        (choice := choice) h_pos x hβ h_min h_bound

/-- Relative error round -/
theorem relative_error_round (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (h_pos : 0 < p) (x : ℝ)
  (hβ : 1 < beta)
  (h_min : ∀ k, emin < k → p ≤ k - fexp k)
  (h_bound : (beta : ℝ) ^ emin ≤ |x|) :
  |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| <
    (beta : ℝ) ^ (-p + 1) *
    |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x| := by
  have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  have hbge1 : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (le_of_lt hβ)
  have hx : x ≠ 0 := by
    intro hx0
    have hpow_pos : 0 < (beta : ℝ) ^ emin := zpow_pos hbpos emin
    have hbad : (beta : ℝ) ^ emin ≤ 0 := by simpa [hx0] using h_bound
    exact (not_le_of_gt hpow_pos) hbad
  let M : Int := FloatSpec.Core.Raux.mag beta x
  have hM_gt : emin < M := by
    have hupp := FloatSpec.Core.Raux.mag_upper_bound
      (beta := beta) (x := x) hβ hx
    have hupp' : |x| < (beta : ℝ) ^ M := by
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, M,
        FloatSpec.Core.Raux.abs_val] using hupp True.intro
    by_contra hnot
    have hpow_le : (beta : ℝ) ^ M ≤ (beta : ℝ) ^ emin :=
      zpow_le_zpow_right₀ hbge1 (le_of_not_gt hnot)
    exact (not_lt_of_ge (le_trans hpow_le h_bound)) hupp'
  have hcexp_le : FloatSpec.Core.Generic_fmt.cexp beta fexp x ≤ M - p := by
    have hp := h_min M hM_gt
    simp only [FloatSpec.Core.Generic_fmt.cexp]
    change fexp M ≤ M - p
    omega
  have hpow_le :
      (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp x) ≤
        (beta : ℝ) ^ (M - p) :=
    zpow_le_zpow_right₀ hbge1 hcexp_le
  have hfactor :
      (beta : ℝ) ^ (M - p) =
        (beta : ℝ) ^ (-p + 1) * (beta : ℝ) ^ (M - 1) := by
    rw [← zpow_add₀ hbne]
    congr 1
    ring
  have hmag_low : (beta : ℝ) ^ (M - 1) ≤ |x| := by
    have h := FloatSpec.Core.Raux.mag_lower_bound
      (beta := beta) (x := x) hβ hx
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, M,
      FloatSpec.Core.Raux.abs_val] using h True.intro
  have hfmt : FloatSpec.Core.Generic_fmt.generic_format beta fexp
      ((beta : ℝ) ^ (M - 1)) := by
    have hfexp : fexp M ≤ M - 1 := by
      have hp := h_min M hM_gt
      omega
    have h := FloatSpec.Core.Generic_fmt.generic_format_bpow
      (beta := beta) (fexp := fexp) (e := M - 1)
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using
      h ⟨hβ, by simpa using hfexp⟩
  have hround_lower :
      (beta : ℝ) ^ (M - 1) ≤
        |FloatSpec.Calc.Round.round beta fexp
          (FloatSpec.Calc.Round.Mode.ofRnd rnd) x| := by
    have h := FloatSpec.Core.Generic_fmt.abs_round_ge_generic
      (beta := beta) (fexp := fexp) (rnd := rnd) hfmt hmag_low
    simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.Mode.ofRnd,
      FloatSpec.Core.Generic_fmt.round_to_generic] using h
  have herr :
      |FloatSpec.Calc.Round.round beta fexp
          (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| <
        FloatSpec.Core.Ulp.ulp beta fexp x := by
    have h := FloatSpec.Core.Ulp.error_lt_ulp
      (beta := beta) (fexp := fexp) (rnd := rnd) (x := x) hx hβ
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure,
      FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.Mode.ofRnd,
      FloatSpec.Core.Generic_fmt.round_to_generic] using h
  have hulp : FloatSpec.Core.Ulp.ulp beta fexp x =
      (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp x) := by
    have h := FloatSpec.Core.Ulp.ulp_neq_0
      (beta := beta) (fexp := fexp) (x := x) hx
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using h True.intro
  calc
    |FloatSpec.Calc.Round.round beta fexp
        (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x|
        < FloatSpec.Core.Ulp.ulp beta fexp x := herr
    _ = (beta : ℝ) ^ (FloatSpec.Core.Generic_fmt.cexp beta fexp x) := hulp
    _ ≤ (beta : ℝ) ^ (M - p) := hpow_le
    _ = (beta : ℝ) ^ (-p + 1) * (beta : ℝ) ^ (M - 1) := hfactor
    _ ≤ (beta : ℝ) ^ (-p + 1) *
        |FloatSpec.Calc.Round.round beta fexp
          (FloatSpec.Calc.Round.Mode.ofRnd rnd) x| :=
      mul_le_mul_of_nonneg_left hround_lower (le_of_lt (zpow_pos hbpos _))

/-- Relative error round F2R emin -/
theorem relative_error_round_F2R_emin (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (h_pos : 0 < p) (m : Int)
  (hβ : 1 < beta)
  (h_min : ∀ k, emin < k → p ≤ k - fexp k)
  (h_nonzero : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) ≠ 0) :
  |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| <
    (beta : ℝ) ^ (-p + 1) *
    |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta))| := by
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk m emin
  let x : ℝ := F2R f
  change |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| <
    (beta : ℝ) ^ (-p + 1) * |FloatSpec.Calc.Round.round beta fexp (FloatSpec.Calc.Round.Mode.ofRnd rnd) x|
  have hm_ne : m ≠ 0 := by
    intro hm
    apply h_nonzero
    simp [hm, _root_.F2R, FloatSpec.Core.Defs.F2R]
  have hm_abs_pos_nat : 0 < Int.natAbs m := Int.natAbs_pos.mpr hm_ne
  have hm_abs_pos : (0 : Int) < (Int.natAbs m : Int) := by
    exact_mod_cast hm_abs_pos_nat
  let fabs : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk (Int.natAbs m) emin
  have hFabs : |x| = F2R fabs := by
    have h := FloatSpec.Core.Float_prop.F2R_Zabs (beta := beta) f hβ
    change |FloatSpec.Core.Defs.F2R f| =
      FloatSpec.Core.Defs.F2R
        (FloatSpec.Core.Defs.FlocqFloat.mk (Int.natAbs m) emin :
          FloatSpec.Core.Defs.FlocqFloat beta)
    exact h
  have hlow_abs : (beta : ℝ) ^ emin ≤ F2R fabs :=
    FloatSpec.Core.Float_prop.bpow_le_F2R (beta := beta) (f := fabs) hβ hm_abs_pos
  have h_bound : (beta : ℝ) ^ emin ≤ |x| := by
    calc
      (beta : ℝ) ^ emin ≤ F2R fabs := hlow_abs
      _ = |x| := hFabs.symm
  exact relative_error_round (beta := beta) (fexp := fexp) (emin := emin)
    (p := p) rnd h_pos x hβ h_min h_bound

-- Section: FLX relative error

variable (prec : Int)
variable [Prec_gt_0 prec]

omit [Prec_gt_0 prec] in
/-- FLX relative error auxiliary -/
lemma relative_error_FLX_aux (k : Int) : prec ≤ k - FLX_exp prec k := by
  simp [FLX_exp, FloatSpec.Core.FLX.FLX_exp]

/-- FLX relative error -/
theorem relative_error_FLX (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
  (hβ : 1 < beta) (h_nonzero : x ≠ 0) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| <
    (beta : ℝ) ^ (-prec + 1) * |x| := by
  let ex : Int := FloatSpec.Core.Raux.mag beta x
  have hlow : (beta : ℝ) ^ (ex - 1) ≤ |x| := by
    have h :=
      (FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := x) hβ h_nonzero)
        True.intro
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, ex,
      FloatSpec.Core.Raux.abs_val] using h
  have hmin : ∀ k, ex - 1 < k → prec ≤ k - FLX_exp prec k := by
    intro k _
    exact relative_error_FLX_aux (prec := prec) k
  simpa [ex] using
    (relative_error (beta := beta) (fexp := FLX_exp prec) (emin := ex - 1)
      (p := prec) (rnd := rnd) x hβ hmin hlow)

/-- FLX relative error existence -/
theorem relative_error_FLX_ex (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ) (hβ : 1 < beta) :
  ∃ eps, |eps| < (beta : ℝ) ^ (-prec + 1) ∧
    FloatSpec.Calc.Round.round beta (FLX_exp prec) (FloatSpec.Calc.Round.Mode.ofRnd rnd) x = x * (1 + eps) := by
  have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  exact relative_error_lt_conversion (beta := beta) (fexp := FLX_exp prec) (rnd := rnd)
    x ((beta : ℝ) ^ (-prec + 1)) (zpow_pos hbpos (-prec + 1))
    (fun hne => relative_error_FLX (beta := beta) (prec := prec) rnd x hβ hne)

/-- FLX relative error round -/
theorem relative_error_FLX_round (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
  (hβ : 1 < beta) (h_nonzero : x ≠ 0) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| <
    (beta : ℝ) ^ (-prec + 1) *
    |FloatSpec.Calc.Round.round beta (FLX_exp prec) (FloatSpec.Calc.Round.Mode.ofRnd rnd) x| := by
  let ex : Int := FloatSpec.Core.Raux.mag beta x
  have hlow : (beta : ℝ) ^ (ex - 1) ≤ |x| := by
    have h :=
      (FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := x) hβ h_nonzero)
        True.intro
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, ex,
      FloatSpec.Core.Raux.abs_val] using h
  have hmin : ∀ k, ex - 1 < k → prec ≤ k - FLX_exp prec k := by
    intro k _
    exact relative_error_FLX_aux (prec := prec) k
  exact relative_error_round (beta := beta) (fexp := FLX_exp prec) (emin := ex - 1)
    (p := prec) (rnd := rnd) (x := x) (Prec_gt_0.pos : 0 < prec) hβ hmin hlow

/-- FLX relative error nearest -/
theorem relative_error_N_FLX (hβ : 1 < beta) (x : ℝ) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
    (1/2) * (beta : ℝ) ^ (-prec + 1) * |x| := by
  classical
  by_cases hx : x = 0
  · subst x
    have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
      unfold FloatSpec.Core.Generic_fmt.Znearest
      simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
    simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
      FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
  · set fexpFLX : Int → Int := FLX_exp prec
    set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexpFLX x
    set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpFLX x
    set zn : Int := FloatSpec.Core.Generic_fmt.Znearest choice sm
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    have hpow_nonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt (zpow_pos hbposR e)
    have hscaled : sm * (beta : ℝ) ^ e = x := by
      have h :=
        (FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
          (beta := beta) (fexp := fexpFLX) (x := x)) hβ
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, e] using h
    have hround :
        FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x =
          (zn : ℝ) * (beta : ℝ) ^ e := by
      simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode, fexpFLX, e, sm, zn]
    have hnearest : |(zn : ℝ) - sm| ≤ (1 / 2 : ℝ) := by
      have h :=
        (FloatSpec.Core.Generic_fmt.Znearest_half choice sm)
      simpa [zn, abs_sub_comm,
        Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using h
    have hlocal :
        |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
          (1 / 2 : ℝ) * (beta : ℝ) ^ e := by
      have hdiff :
          FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x =
            ((zn : ℝ) - sm) * (beta : ℝ) ^ e := by
        rw [hround, ← hscaled]
        ring
      rw [hdiff, abs_mul, abs_of_nonneg hpow_nonneg]
      exact mul_le_mul_of_nonneg_right hnearest hpow_nonneg
    have hulp_run :
        FloatSpec.Core.Ulp.ulp beta fexpFLX x = (beta : ℝ) ^ e := by
      unfold FloatSpec.Core.Ulp.ulp
      simp [hx, e]
    have hulp_le :
        FloatSpec.Core.Ulp.ulp beta fexpFLX x ≤ |x| * (beta : ℝ) ^ (1 - prec) := by
      have h :=
        (FloatSpec.Core.FLX.ulp_FLX_le (prec := prec) (beta := beta) (x := x)) hβ
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, fexpFLX] using h
    have hpow_le : (beta : ℝ) ^ e ≤ (beta : ℝ) ^ (-prec + 1) * |x| := by
      have hpow_le' : (beta : ℝ) ^ e ≤ |x| * (beta : ℝ) ^ (1 - prec) := by
        simpa [hulp_run] using hulp_le
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
        mul_left_comm, mul_assoc] using hpow_le'
    exact le_trans hlocal
      (by
        have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hpow_le hhalf_nonneg))

/-- Unit roundoff -/
noncomputable def u_ro : ℝ := (1/2) * (beta : ℝ) ^ (-prec + 1)

/-- Unit roundoff is positive -/
lemma u_ro_pos (hβ : 1 < beta) : 0 ≤ u_ro beta prec := by
  unfold u_ro
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposℝ : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  exact mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbposℝ (-prec + 1)))

/-- Unit roundoff is less than 1 -/
lemma u_ro_lt_1 (hβ : 1 < beta) : u_ro beta prec < 1 := by
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
  have hhalf_le : (1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1) ≤ (1 / 2 : ℝ) * 1 := by
    exact mul_le_mul_of_nonneg_left hpow_le_one (by norm_num)
  nlinarith

-- Unit roundoff divided by (1 + u_ro) is positive
lemma u_rod1pu_ro_pos (hβ : 1 < beta) : 0 ≤ u_ro beta prec / (1 + u_ro beta prec) := by
  exact div_nonneg (u_ro_pos (beta := beta) (prec := prec) hβ)
    (by linarith [u_ro_pos (beta := beta) (prec := prec) hβ])

/-- Unit roundoff divided by (1 + u_ro) is less than or equal to u_ro -/
lemma u_rod1pu_ro_le_u_ro (hβ : 1 < beta) : u_ro beta prec / (1 + u_ro beta prec) ≤ u_ro beta prec := by
  have hu : 0 ≤ u_ro beta prec := u_ro_pos (beta := beta) (prec := prec) hβ
  have hle_den : 1 ≤ 1 + u_ro beta prec := by linarith
  have hdiv_le : u_ro beta prec / (1 + u_ro beta prec) ≤ u_ro beta prec / 1 := by
    exact div_le_div_of_nonneg_left hu (by norm_num) hle_den
  simpa using hdiv_le

private lemma Znearest_error_le_scaled (choice : Int → Bool) (N : Int) (y : ℝ)
    (hNpos : 0 < N) (hyN : (N : ℝ) ≤ y) :
    |((FloatSpec.Core.Generic_fmt.Znearest choice y : Int) : ℝ) - y| ≤
      y / (2 * (N : ℝ) + 1) := by
  classical
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hden_pos : 0 < 2 * (N : ℝ) + 1 := by nlinarith
  have hcases :
      FloatSpec.Core.Generic_fmt.Znearest choice y = FloatSpec.Core.Raux.Zfloor y ∨
        FloatSpec.Core.Generic_fmt.Znearest choice y = FloatSpec.Core.Raux.Zceil y := by
    exact FloatSpec.Core.Generic_fmt.Znearest_DN_or_UP choice y
  have hhalf :
      |((FloatSpec.Core.Generic_fmt.Znearest choice y : Int) : ℝ) - y| ≤
        (1 / 2 : ℝ) := by
    have h := (FloatSpec.Core.Generic_fmt.Znearest_half choice y)
    simpa [abs_sub_comm,
      Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using h
  rcases hcases with hfloor | hceil
  · have hfloor_le : ((FloatSpec.Core.Raux.Zfloor y : Int) : ℝ) ≤ y := by
      simpa [FloatSpec.Core.Raux.Zfloor] using Int.floor_le y
    have hN_le_floor : N ≤ FloatSpec.Core.Raux.Zfloor y := by
      simpa [FloatSpec.Core.Raux.Zfloor] using (Int.le_floor.mpr hyN)
    have hN_le_floorR : (N : ℝ) ≤ (FloatSpec.Core.Raux.Zfloor y : ℝ) := by
      exact_mod_cast hN_le_floor
    have hdist_nonneg : 0 ≤ y - (FloatSpec.Core.Raux.Zfloor y : ℝ) := by
      exact sub_nonneg.mpr hfloor_le
    have hdist_half : y - (FloatSpec.Core.Raux.Zfloor y : ℝ) ≤ (1 / 2 : ℝ) := by
      have h' := hhalf
      rw [hfloor] at h'
      rw [abs_of_nonpos (sub_nonpos.mpr hfloor_le)] at h'
      linarith
    have hmul :
        (y - (FloatSpec.Core.Raux.Zfloor y : ℝ)) *
          (2 * (N : ℝ) + 1) ≤ y := by
      nlinarith
    have hdiv :
        y - (FloatSpec.Core.Raux.Zfloor y : ℝ) ≤
          y / (2 * (N : ℝ) + 1) :=
      (le_div_iff₀ hden_pos).mpr hmul
    rw [hfloor]
    rw [abs_of_nonpos (sub_nonpos.mpr hfloor_le)]
    linarith
  · have hy_le_ceil : y ≤ (FloatSpec.Core.Raux.Zceil y : ℝ) := by
      simpa [FloatSpec.Core.Raux.Zceil] using Int.le_ceil y
    by_cases hy_eq_N : y = (N : ℝ)
    · have hceilN : FloatSpec.Core.Raux.Zceil y = N := by
        rw [hy_eq_N]
        simpa [FloatSpec.Core.Raux.Zceil] using (Int.ceil_intCast (n := N))
      rw [hceil, hceilN, hy_eq_N]
      simp
      exact div_nonneg (le_of_lt hNposR) (le_of_lt hden_pos)
    · have hN_lt_y : (N : ℝ) < y := lt_of_le_of_ne hyN (Ne.symm hy_eq_N)
      have hceil_ge : N + 1 ≤ FloatSpec.Core.Raux.Zceil y := by
        have hceil_gt_N : N < FloatSpec.Core.Raux.Zceil y := by
          have hceil_gt_NR : (N : ℝ) < (FloatSpec.Core.Raux.Zceil y : ℝ) :=
            lt_of_lt_of_le hN_lt_y hy_le_ceil
          exact_mod_cast hceil_gt_NR
        omega
      have hceil_geR : (N : ℝ) + 1 ≤ (FloatSpec.Core.Raux.Zceil y : ℝ) := by
        exact_mod_cast hceil_ge
      have hdist_nonneg : 0 ≤ (FloatSpec.Core.Raux.Zceil y : ℝ) - y :=
        sub_nonneg.mpr hy_le_ceil
      have hdist_half : (FloatSpec.Core.Raux.Zceil y : ℝ) - y ≤ (1 / 2 : ℝ) := by
        have h' := hhalf
        rw [hceil] at h'
        rw [abs_of_nonneg hdist_nonneg] at h'
        exact h'
      have hmul :
          ((FloatSpec.Core.Raux.Zceil y : ℝ) - y) *
            (2 * (N : ℝ) + 1) ≤ y := by
        nlinarith
      have hdiv :
          (FloatSpec.Core.Raux.Zceil y : ℝ) - y ≤
            y / (2 * (N : ℝ) + 1) :=
        (le_div_iff₀ hden_pos).mpr hmul
      rw [hceil]
      rw [abs_of_nonneg hdist_nonneg]
      exact hdiv

private lemma relative_error_N_FLX'_pos (hβ : 1 < beta) {x : ℝ} (hxpos : 0 < x) :
    |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
      u_ro beta prec / (1 + u_ro beta prec) * |x| := by
  classical
  set fexpFLX : Int → Int := FLX_exp prec
  set M : Int := FloatSpec.Core.Raux.mag beta x
  set e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexpFLX x
  set sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpFLX x
  set zn : Int := FloatSpec.Core.Generic_fmt.Znearest choice sm
  set N : Int := beta ^ Int.natAbs (prec - 1)
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposℝ : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbneℝ : (beta : ℝ) ≠ 0 := ne_of_gt hbposℝ
  have hprec_nonneg : 0 ≤ prec - 1 := by
    have hp : 1 ≤ prec := Int.add_one_le_iff.mpr (Prec_gt_0.pos : 0 < prec)
    omega
  have hNpos : 0 < N := by
    dsimp [N]
    exact pow_pos hbposℤ _
  have hNposℝ : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hN_cast : (N : ℝ) = (beta : ℝ) ^ (prec - 1) := by
    have hk : ((Int.natAbs (prec - 1) : Int) = prec - 1) :=
      Int.natAbs_of_nonneg hprec_nonneg
    dsimp [N]
    rw [← hk, zpow_natCast]
    exact_mod_cast (rfl : beta ^ Int.natAbs (prec - 1) = beta ^ Int.natAbs (prec - 1))
  have hcexp : e = M - prec := by
    simp [e, M, fexpFLX, FloatSpec.Core.Generic_fmt.cexp]
    rfl
  have hscaled : sm * (beta : ℝ) ^ e = x := by
    have h :=
      (FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
        (beta := beta) (fexp := fexpFLX) (x := x)) hβ
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, e] using h
  have hsm_eval : sm = x * (beta : ℝ) ^ (-e) := by
    simpa [sm, FloatSpec.Core.Generic_fmt.scaled_mantissa, e]
  have hlow_abs : (beta : ℝ) ^ (M - 1) ≤ |x| := by
    have h :=
      (FloatSpec.Core.Raux.mag_lower_bound (beta := beta) (x := x) hβ
        (ne_of_gt hxpos)) True.intro
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, M,
      FloatSpec.Core.Raux.abs_val] using h
  have hlow_x : (beta : ℝ) ^ (M - 1) ≤ x := by
    simpa [abs_of_nonneg (le_of_lt hxpos)] using hlow_abs
  have hpow_nonneg_neg : 0 ≤ (beta : ℝ) ^ (-e) := le_of_lt (zpow_pos hbposℝ (-e))
  have hmul_low :
      (beta : ℝ) ^ (M - 1) * (beta : ℝ) ^ (-e) ≤ x * (beta : ℝ) ^ (-e) :=
    mul_le_mul_of_nonneg_right hlow_x hpow_nonneg_neg
  have hpow_scale :
      (beta : ℝ) ^ (M - 1) * (beta : ℝ) ^ (-e) =
        (beta : ℝ) ^ (prec - 1) := by
    rw [hcexp]
    rw [← zpow_add₀ hbneℝ]
    congr 1
    ring
  have hsm_lower : (N : ℝ) ≤ sm := by
    calc
      (N : ℝ) = (beta : ℝ) ^ (prec - 1) := hN_cast
      _ = (beta : ℝ) ^ (M - 1) * (beta : ℝ) ^ (-e) := hpow_scale.symm
      _ ≤ x * (beta : ℝ) ^ (-e) := hmul_low
      _ = sm := hsm_eval.symm
  have hnearest :=
    Znearest_error_le_scaled (choice := choice) (N := N) (y := sm) hNpos hsm_lower
  have hround :
      FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x =
        (zn : ℝ) * (beta : ℝ) ^ e := by
    simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
      FloatSpec.Compat.Scaffold.ZnearestMode, fexpFLX, e, sm, zn]
  have hdiff :
      FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x =
        ((zn : ℝ) - sm) * (beta : ℝ) ^ e := by
    rw [hround, ← hscaled]
    ring
  have hpow_nonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt (zpow_pos hbposℝ e)
  have hden_pos : 0 < 2 * (N : ℝ) + 1 := by nlinarith
  have hlocal :
      |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
        x / (2 * (N : ℝ) + 1) := by
    have hmul :
        |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
          sm / (2 * (N : ℝ) + 1) * (beta : ℝ) ^ e := by
      rw [hdiff, abs_mul, abs_of_nonneg hpow_nonneg]
      exact mul_le_mul_of_nonneg_right hnearest hpow_nonneg
    have hscale :
        sm / (2 * (N : ℝ) + 1) * (beta : ℝ) ^ e =
          x / (2 * (N : ℝ) + 1) := by
      field_simp [ne_of_gt hden_pos]
      exact hscaled
    exact le_trans hmul (le_of_eq hscale)
  have hpow_neg :
      (beta : ℝ) ^ (-prec + 1) = ((beta : ℝ) ^ (prec - 1))⁻¹ := by
    have hidx : -prec + 1 = -(prec - 1) := by ring
    rw [hidx, zpow_neg]
  have hu_eq : u_ro beta prec = 1 / (2 * (N : ℝ)) := by
    unfold u_ro
    rw [hpow_neg, ← hN_cast]
    field_simp [ne_of_gt hNposℝ]
  have hcoef : u_ro beta prec / (1 + u_ro beta prec) =
      1 / (2 * (N : ℝ) + 1) := by
    rw [hu_eq]
    field_simp [ne_of_gt hNposℝ, ne_of_gt hden_pos]
  calc
    |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x|
        ≤ x / (2 * (N : ℝ) + 1) := hlocal
    _ = u_ro beta prec / (1 + u_ro beta prec) * |x| := by
      rw [hcoef]
      rw [abs_of_nonneg (le_of_lt hxpos)]
      ring

/-- FLX relative error nearest alternative -/
theorem relative_error_N_FLX' (hβ : 1 < beta) (x : ℝ) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
    u_ro beta prec / (1 + u_ro beta prec) * |x| := by
  classical
  by_cases hx0 : x = 0
  · subst x
    have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
      unfold FloatSpec.Core.Generic_fmt.Znearest
      simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
    simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
      FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
      FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
  · by_cases hxpos : 0 < x
    · exact relative_error_N_FLX'_pos (beta := beta) (choice := choice)
        (prec := prec) hβ hxpos
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx0
      let choiceOpp : Int → Bool := fun t => ! choice (-(t + 1))
      have hpos :=
        relative_error_N_FLX'_pos (beta := beta) (choice := choiceOpp)
          (prec := prec) hβ (show 0 < -x by linarith)
      have hopp :
          FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x =
            - FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choiceOpp) (-x) := by
        have h :=
          FloatSpec.Core.Generic_fmt.round_N_opp
            (beta := beta) (fexp := FLX_exp prec) (choice := choice) (x := -x)
        simpa [FloatSpec.Calc.Round.round, choiceOpp, neg_neg] using h
      rw [hopp]
      have hrewrite :
          |(-FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choiceOpp) (-x)) - x| =
            |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choiceOpp) (-x) - (-x)| := by
        rw [abs_sub_comm]
        ring_nf
      rw [hrewrite]
      simpa [abs_neg, choiceOpp] using hpos

/-- FLX relative error nearest existence -/
theorem relative_error_N_FLX_ex (hβ : 1 < beta) (x : ℝ) :
  ∃ eps, |eps| ≤ (1/2) * (beta : ℝ) ^ (-prec + 1) ∧
    FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x = x * (1 + eps) := by
  let b : ℝ := (1 / 2) * (beta : ℝ) ^ (-prec + 1)
  have hb_nonneg : 0 ≤ b := by
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposℝ : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    exact mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbposℝ (-prec + 1)))
  have hbound :
      |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
        b * |x| := by
    simpa [b] using
      (relative_error_N_FLX (beta := beta) (choice := choice) (prec := prec) hβ x)
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa [b] using hb_nonneg
    · subst x
      have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
        unfold FloatSpec.Core.Generic_fmt.Znearest
        simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
      simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
  · refine ⟨(FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x) / x,
      ?_, ?_⟩
    · have hx_abs_pos : 0 < |x| := abs_pos.mpr hx
      have hdiv := div_le_div_of_nonneg_right hbound (le_of_lt hx_abs_pos)
      have hrhs : (b * |x|) / |x| = b := by
        field_simp [ne_of_gt hx_abs_pos]
      have hratio :
          |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| / |x| ≤ b := by
        calc
          |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| / |x|
              ≤ (b * |x|) / |x| := hdiv
          _ = b := hrhs
      simpa [abs_div, b] using hratio
    · field_simp [hx]
      ring

/-- FLX relative error nearest alternative existence -/
theorem relative_error_N_FLX'_ex (hβ : 1 < beta) (x : ℝ) :
  ∃ eps, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
    FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x = x * (1 + eps) := by
  let b : ℝ := u_ro beta prec / (1 + u_ro beta prec)
  have hb_nonneg : 0 ≤ b := by
    simpa [b] using u_rod1pu_ro_pos (beta := beta) (prec := prec) hβ
  have hbound :
      |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
        b * |x| := by
    simpa [b] using
      (relative_error_N_FLX' (beta := beta) (choice := choice) (prec := prec) hβ x)
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa [b] using hb_nonneg
    · subst x
      have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
        unfold FloatSpec.Core.Generic_fmt.Znearest
        simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
      simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
  · refine ⟨(FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x) / x,
      ?_, ?_⟩
    · have hx_abs_pos : 0 < |x| := abs_pos.mpr hx
      have hdiv := div_le_div_of_nonneg_right hbound (le_of_lt hx_abs_pos)
      have hrhs : (b * |x|) / |x| = b := by
        field_simp [ne_of_gt hx_abs_pos]
      have hratio :
          |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| / |x| ≤ b := by
        calc
          |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| / |x|
              ≤ (b * |x|) / |x| := hdiv
          _ = b := hrhs
      simpa [abs_div, b] using hratio
    · field_simp [hx]
      ring

/-- Relative error nearest round derivation -/
lemma relative_error_N_round_ex_derive (x rx : ℝ)
  (hβ : 1 < beta)
  (h_exists : ∃ eps, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧ rx = x * (1 + eps)) :
  ∃ eps, |eps| ≤ u_ro beta prec ∧ x = rx * (1 + eps) := by
  rcases h_exists with ⟨eps, heps, hrx⟩
  let u : ℝ := u_ro beta prec
  refine ⟨-eps / (1 + eps), ?_, ?_⟩
  · have hu_nonneg : 0 ≤ u := by
      simpa [u] using u_ro_pos (beta := beta) (prec := prec) hβ
    have hu_lt_one : u < 1 := by
      simpa [u] using u_ro_lt_1 (beta := beta) (prec := prec) hβ
    have hsmall_le : |eps| ≤ u / (1 + u) := by
      simpa [u] using heps
    have hden_u_pos : 0 < 1 + u := by linarith
    have hsmall_lt_one : |eps| < 1 := by
      calc
        |eps| ≤ u / (1 + u) := hsmall_le
        _ ≤ u := by
          have h := u_rod1pu_ro_le_u_ro (beta := beta) (prec := prec) hβ
          simpa [u] using h
        _ < 1 := hu_lt_one
    have heps_gt_neg_one : -1 < eps := by
      have hneg_abs : -|eps| ≤ eps := neg_abs_le eps
      linarith
    have hden_pos : 0 < 1 + eps := by linarith
    have hbound_mul : |eps| * (1 + u) ≤ u := by
      have h := mul_le_mul_of_nonneg_right hsmall_le (le_of_lt hden_u_pos)
      have hden_ne : (1 + u) ≠ 0 := ne_of_gt hden_u_pos
      simpa [div_mul_cancel₀, hden_ne] using h
    have hmain : |eps| ≤ u * (1 + eps) := by
      calc
        |eps| = |eps| * (1 + u) - |eps| * u := by ring
        _ ≤ u - |eps| * u := by linarith
        _ = u * (1 - |eps|) := by ring
        _ ≤ u * (1 + eps) := by
          exact mul_le_mul_of_nonneg_left (by linarith [neg_abs_le eps]) hu_nonneg
    have hdiv := div_le_div_of_nonneg_right hmain (le_of_lt hden_pos)
    have hden_ne : (1 + eps) ≠ 0 := ne_of_gt hden_pos
    have habs :
        |-eps / (1 + eps)| = |eps| / (1 + eps) := by
      rw [abs_div, abs_neg, abs_of_pos hden_pos]
    rw [habs]
    calc
      |eps| / (1 + eps) ≤ (u * (1 + eps)) / (1 + eps) := hdiv
      _ = u := by field_simp [hden_ne]
  · have hden_pos : 0 < 1 + eps := by
      have hu_lt_one : u_ro beta prec < 1 :=
        u_ro_lt_1 (beta := beta) (prec := prec) hβ
      have hsmall_lt_one : |eps| < 1 := by
        calc
          |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) := heps
          _ ≤ u_ro beta prec := u_rod1pu_ro_le_u_ro (beta := beta) (prec := prec) hβ
          _ < 1 := hu_lt_one
      have hneg_abs : -|eps| ≤ eps := neg_abs_le eps
      linarith
    have hden_ne : (1 + eps) ≠ 0 := ne_of_gt hden_pos
    rw [hrx]
    field_simp [hden_ne]
    ring

/-- FLX relative error nearest round existence -/
theorem relative_error_N_FLX_round_ex (hβ : 1 < beta) (x : ℝ) :
  ∃ eps, |eps| ≤ u_ro beta prec ∧
    x = FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x * (1 + eps) := by
  exact relative_error_N_round_ex_derive (beta := beta) (prec := prec)
    (x := x)
    (rx := FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x) hβ
    (relative_error_N_FLX'_ex (beta := beta) (choice := choice) (prec := prec) hβ x)

/-- FLX relative error nearest round -/
theorem relative_error_N_FLX_round (hβ : 1 < beta) (x : ℝ) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
    u_ro beta prec *
    |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x| := by
  rcases relative_error_N_FLX_round_ex (beta := beta) (choice := choice) (prec := prec) hβ x with
    ⟨eps, heps, hx⟩
  set rx : ℝ := FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x
  have hx' : x = rx * (1 + eps) := by
    simpa [rx] using hx
  rw [hx']
  have hcalc : rx - rx * (1 + eps) = -(eps * rx) := by ring
  rw [hcalc, abs_neg, abs_mul]
  exact mul_le_mul_of_nonneg_right heps (abs_nonneg rx)

-- Section: FLT relative error

variable (emin : Int)

omit [Prec_gt_0 prec] in
/-- FLT relative error auxiliary -/
lemma relative_error_FLT_aux (k : Int) (h_bound : emin + prec - 1 < k) :
  prec ≤ k - FLT_exp emin prec k := by
  simp [FLT_exp, FloatSpec.Core.FLT.FLT_exp]
  omega

/-- Local magnitude lower bound in the form used by Flocq's `round_FLT_FLX`
threshold: from `β^e ≤ |x|`, `mag x` is at least `e + 1`. -/
private lemma mag_gt_of_bpow_le (x : ℝ) (e : Int)
  (hβ : 1 < beta)
  (hbound : (beta : ℝ) ^ e ≤ |x|) :
  e + 1 ≤ FloatSpec.Core.Raux.mag beta x := by
  rcases lt_or_eq_of_le hbound with hlt | heq
  · have htrip := FloatSpec.Core.Raux.mag_ge_bpow
      (beta := beta) (x := x) (e := e + 1) hβ
      (le_of_lt (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlt))
    simpa using htrip
  · have hmag_abs := FloatSpec.Core.Raux.mag_abs (beta := beta) (x := x) hβ
    have hmag_abs_run :
        FloatSpec.Core.Raux.mag beta |x| = FloatSpec.Core.Raux.mag beta x := by
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using hmag_abs trivial
    have hmag_bpow := FloatSpec.Core.Raux.mag_bpow (beta := beta) (e := e) hβ
    have hmag_bpow_run :
        FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ e) = e + 1 := by
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using hmag_bpow trivial
    have hmag_x : e + 1 = FloatSpec.Core.Raux.mag beta x := by
      calc
        e + 1 = FloatSpec.Core.Raux.mag beta ((beta : ℝ) ^ e) := hmag_bpow_run.symm
        _ = FloatSpec.Core.Raux.mag beta |x| := by simpa [heq]
        _ = FloatSpec.Core.Raux.mag beta x := hmag_abs_run
    exact le_of_eq hmag_x

/-- Concrete nearest-rounding version of Flocq `round_FLT_FLX` at the
`β^(emin+prec-1)` lower bound. -/
private lemma round_FLT_FLX_nearest (x : ℝ) (hβ : 1 < beta)
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

/-- FLT relative error -/
theorem relative_error_FLT (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
  (hβ : 1 < beta)
  (h_bound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| <
    (beta : ℝ) ^ (-prec + 1) * |x| := by
  have hmin : ∀ k, emin + prec - 1 < k → prec ≤ k - FLT_exp emin prec k := by
    intro k hk
    exact relative_error_FLT_aux (emin := emin) (prec := prec) k hk
  exact relative_error (beta := beta) (fexp := FLT_exp emin prec)
    (emin := emin + prec - 1) (p := prec) (rnd := rnd) x hβ hmin h_bound

/-- FLT relative error F2R emin -/
theorem relative_error_FLT_F2R_emin (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (m : Int)
  (hβ : 1 < beta)
  (h_nonzero : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) ≠ 0) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (FloatSpec.Calc.Round.Mode.ofRnd rnd) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| <
    (beta : ℝ) ^ (-prec + 1) *
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| := by
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk m emin
  let x : ℝ := F2R f
  change |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (FloatSpec.Calc.Round.Mode.ofRnd rnd) x - x| <
    (beta : ℝ) ^ (-prec + 1) * |x|
  by_cases hxsmall : |x| < (beta : ℝ) ^ (emin + prec - 1)
  · have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    let fixExp : Int → Int := FloatSpec.Core.FIX.FIX_exp (emin := emin)
    have hfix : FloatSpec.Core.Generic_fmt.generic_format beta fixExp x := by
      have htrip :=
        FloatSpec.Core.Generic_fmt.generic_format_F2R'
          (beta := beta) (fexp := fixExp) (x := x) (f := f)
      have hfx : FloatSpec.Core.Defs.F2R f = x := by
        simp [x, _root_.F2R]
      exact htrip ⟨hβ, hfx, by
        intro _hne
        simp [fixExp, FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.FIX.FIX_exp, f]⟩
    have hthreshold :
        (beta : ℝ) ^ (emin + prec - 1) ≤ (beta : ℝ) ^ (emin + prec) := by
      have hpow :=
        (FloatSpec.Core.Raux.bpow_le (beta := beta) (e1 := emin + prec - 1)
          (e2 := emin + prec) hβ (by omega)) True.intro
      simpa [FloatSpec.Core.Raux.bpow_le_check, Std.Do.wp, Std.Do.PostCond.noThrow,
        Id.run, pure] using hpow
    have hle : |x| ≤ (beta : ℝ) ^ (emin + prec) :=
      le_trans (le_of_lt hxsmall) hthreshold
    have hflt : FloatSpec.Core.Generic_fmt.generic_format beta (FLT_exp emin prec) x := by
      have htrip :=
        FloatSpec.Core.FLT.generic_format_FLT_FIX
          (prec := prec) (emin := emin) (beta := beta) (x := x)
      simpa [fixExp] using htrip ⟨hβ, hle, hfix⟩
    have hround :
        FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (FloatSpec.Calc.Round.Mode.ofRnd rnd) x = x := by
      have h :=
        FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := beta) (fexp := FLT_exp emin prec)
          (rnd := rnd) (x := x) hβ hflt
      simpa [FloatSpec.Calc.Round.round, FloatSpec.Calc.Round.Mode.ofRnd] using h
    rw [hround]
    have hpow_pos : 0 < (beta : ℝ) ^ (-prec + 1) := zpow_pos hbpos (-prec + 1)
    have hx_abs_pos : 0 < |x| := by
      exact abs_pos.mpr (by simpa [x, f] using h_nonzero)
    simpa using mul_pos hpow_pos hx_abs_pos
  · have hbound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x| := le_of_not_gt hxsmall
    exact relative_error_FLT (beta := beta) (emin := emin) (prec := prec)
      rnd x hβ hbound

/-- FLT relative error F2R emin existence -/
theorem relative_error_FLT_F2R_emin_ex (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (m : Int)
  (hβ : 1 < beta) :
  ∃ eps, |eps| < (beta : ℝ) ^ (-prec + 1) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (FloatSpec.Calc.Round.Mode.ofRnd rnd) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) =
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) * (1 + eps) := by
  have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  exact relative_error_lt_conversion (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
    (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta))
    ((beta : ℝ) ^ (-prec + 1)) (zpow_pos hbpos (-prec + 1))
    (fun hne => relative_error_FLT_F2R_emin (beta := beta) (emin := emin)
      (prec := prec) rnd m hβ hne)

/-- FLT relative error existence -/
theorem relative_error_FLT_ex (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
  (hβ : 1 < beta)
  (h_bound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
  ∃ eps, |eps| < (beta : ℝ) ^ (-prec + 1) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (FloatSpec.Calc.Round.Mode.ofRnd rnd) x = x * (1 + eps) := by
  have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  exact relative_error_lt_conversion (beta := beta) (fexp := FLT_exp emin prec) (rnd := rnd)
    x ((beta : ℝ) ^ (-prec + 1)) (zpow_pos hbpos (-prec + 1))
    (fun _ => relative_error_FLT (beta := beta) (emin := emin) (prec := prec)
      rnd x hβ h_bound)

/-- FLT relative error nearest -/
theorem relative_error_N_FLT (x : ℝ)
  (hβ : 1 < beta)
  (h_bound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x| ≤
    (1/2) * (beta : ℝ) ^ (-prec + 1) * |x| := by
  have hmin : ∀ k, emin + prec - 1 < k → prec ≤ k - FLT_exp emin prec k := by
    intro k hk
    exact relative_error_FLT_aux (emin := emin) (prec := prec) k hk
  exact relative_error_N (beta := beta) (fexp := FLT_exp emin prec)
    (emin := emin + prec - 1) (p := prec) (choice := choice) x hβ hmin h_bound

/-- FLT relative error nearest existence -/
theorem relative_error_N_FLT_ex (x : ℝ)
  (hβ : 1 < beta)
  (h_bound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
  ∃ eps, |eps| ≤ (1/2) * (beta : ℝ) ^ (-prec + 1) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) := by
  have hmin : ∀ k, emin + prec - 1 < k → prec ≤ k - FLT_exp emin prec k := by
    intro k hk
    exact relative_error_FLT_aux (emin := emin) (prec := prec) k hk
  exact relative_error_N_ex (beta := beta) (fexp := FLT_exp emin prec)
    (emin := emin + prec - 1) (p := prec) (choice := choice) x hβ hmin h_bound

/-- FLT relative error nearest round -/
theorem relative_error_N_FLT_round (x : ℝ)
  (hβ : 1 < beta)
  (h_bound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x| ≤
    (1/2) * (beta : ℝ) ^ (-prec + 1) *
    |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x| := by
  have hmin : ∀ k, emin + prec - 1 < k → prec ≤ k - FLT_exp emin prec k := by
    intro k hk
    exact relative_error_FLT_aux (emin := emin) (prec := prec) k hk
  exact relative_error_N_round (beta := beta) (fexp := FLT_exp emin prec)
    (emin := emin + prec - 1) (p := prec) (choice := choice) (Prec_gt_0.pos : 0 < prec)
    x hβ hmin h_bound

/-- FLT relative error nearest F2R emin -/
theorem relative_error_N_FLT_F2R_emin (m : Int) (hβ : 1 < beta) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| ≤
    (1/2) * (beta : ℝ) ^ (-prec + 1) *
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| := by
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk m emin
  let x : ℝ := F2R f
  change |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x| ≤
    (1 / 2) * (beta : ℝ) ^ (-prec + 1) * |x|
  by_cases hxsmall : |x| < (beta : ℝ) ^ (emin + prec - 1)
  · have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
    let fixExp : Int → Int := FloatSpec.Core.FIX.FIX_exp (emin := emin)
    have hfix : FloatSpec.Core.Generic_fmt.generic_format beta fixExp x := by
      have htrip :=
        FloatSpec.Core.Generic_fmt.generic_format_F2R'
          (beta := beta) (fexp := fixExp) (x := x) (f := f)
      have hfx : FloatSpec.Core.Defs.F2R f = x := by
        simp [x, _root_.F2R]
      exact htrip ⟨hβ, hfx, by
        intro _hne
        simp [fixExp, FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.FIX.FIX_exp, f]⟩
    have hthreshold :
        (beta : ℝ) ^ (emin + prec - 1) ≤ (beta : ℝ) ^ (emin + prec) := by
      have hpow :=
        (FloatSpec.Core.Raux.bpow_le (beta := beta) (e1 := emin + prec - 1)
          (e2 := emin + prec) hβ (by omega)) True.intro
      simpa [FloatSpec.Core.Raux.bpow_le_check, Std.Do.wp, Std.Do.PostCond.noThrow,
        Id.run, pure] using hpow
    have hle : |x| ≤ (beta : ℝ) ^ (emin + prec) := by
      exact le_trans (le_of_lt hxsmall) hthreshold
    have hflt : FloatSpec.Core.Generic_fmt.generic_format beta (FLT_exp emin prec) x := by
      have htrip :=
        FloatSpec.Core.FLT.generic_format_FLT_FIX
          (prec := prec) (emin := emin) (beta := beta) (x := x)
      simpa [fixExp] using htrip ⟨hβ, hle, hfix⟩
    have hround :
        FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x := by
      have h :=
        FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := beta) (fexp := FLT_exp emin prec)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice) (x := x) hβ hflt
      simpa [FloatSpec.Calc.Round.round, Znearest, FloatSpec.Compat.Scaffold.ZnearestMode] using h
    rw [hround]
    have hcoeff_nonneg : 0 ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1) :=
      mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbpos (-prec + 1)))
    simpa using mul_nonneg hcoeff_nonneg (abs_nonneg x)
  · have hbound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x| := le_of_not_gt hxsmall
    exact relative_error_N_FLT (beta := beta) (choice := choice) (emin := emin)
      (prec := prec) x hβ hbound

/-- FLT relative error nearest F2R emin existence -/
theorem relative_error_N_FLT_F2R_emin_ex (m : Int) (hβ : 1 < beta) :
  ∃ eps, |eps| ≤ (1/2) * (beta : ℝ) ^ (-prec + 1) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) =
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) * (1 + eps) := by
  let x : ℝ :=
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)
  let b : ℝ := (1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1)
  have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  have hb_nonneg : 0 ≤ b :=
    mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbpos (-prec + 1)))
  have hbound :
      |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x| ≤
        b * |x| := by
    simpa [x, b] using
      (relative_error_N_FLT_F2R_emin (beta := beta) (choice := choice)
        (emin := emin) (prec := prec) m hβ)
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa [b] using hb_nonneg
    · have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
        unfold FloatSpec.Core.Generic_fmt.Znearest
        simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
      simp [x, hx, FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
  · refine ⟨(FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x) / x,
      ?_, ?_⟩
    · have hx_abs_pos : 0 < |x| := abs_pos.mpr hx
      have hdiv := div_le_div_of_nonneg_right hbound (le_of_lt hx_abs_pos)
      have hrhs : (b * |x|) / |x| = b := by
        field_simp [ne_of_gt hx_abs_pos]
      have hratio :
          |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x| / |x| ≤ b := by
        calc
          |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x| / |x|
              ≤ (b * |x|) / |x| := hdiv
          _ = b := hrhs
      simpa [x, b, abs_div] using hratio
    · field_simp [hx]
      ring

/-- FLT relative error nearest round F2R emin -/
theorem relative_error_N_FLT_round_F2R_emin (m : Int) (hβ : 1 < beta) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| ≤
    (1/2) * (beta : ℝ) ^ (-prec + 1) *
    |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta))| := by
  let f : FloatSpec.Core.Defs.FlocqFloat beta :=
    FloatSpec.Core.Defs.FlocqFloat.mk m emin
  let x : ℝ := F2R f
  change |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x| ≤
    (1 / 2) * (beta : ℝ) ^ (-prec + 1) *
      |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x|
  by_cases hxsmall : |x| < (beta : ℝ) ^ (emin + prec - 1)
  · have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
    let fixExp : Int → Int := FloatSpec.Core.FIX.FIX_exp (emin := emin)
    have hfix : FloatSpec.Core.Generic_fmt.generic_format beta fixExp x := by
      have htrip :=
        FloatSpec.Core.Generic_fmt.generic_format_F2R'
          (beta := beta) (fexp := fixExp) (x := x) (f := f)
      have hfx : FloatSpec.Core.Defs.F2R f = x := by
        simp [x, _root_.F2R]
      exact htrip ⟨hβ, hfx, by
        intro _hne
        simp [fixExp, FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.FIX.FIX_exp, f]⟩
    have hthreshold :
        (beta : ℝ) ^ (emin + prec - 1) ≤ (beta : ℝ) ^ (emin + prec) := by
      have hpow :=
        (FloatSpec.Core.Raux.bpow_le (beta := beta) (e1 := emin + prec - 1)
          (e2 := emin + prec) hβ (by omega)) True.intro
      simpa [FloatSpec.Core.Raux.bpow_le_check, Std.Do.wp, Std.Do.PostCond.noThrow,
        Id.run, pure] using hpow
    have hle : |x| ≤ (beta : ℝ) ^ (emin + prec) := by
      exact le_trans (le_of_lt hxsmall) hthreshold
    have hflt : FloatSpec.Core.Generic_fmt.generic_format beta (FLT_exp emin prec) x := by
      have htrip :=
        FloatSpec.Core.FLT.generic_format_FLT_FIX
          (prec := prec) (emin := emin) (beta := beta) (x := x)
      simpa [fixExp] using htrip ⟨hβ, hle, hfix⟩
    have hround :
        FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x := by
      have h :=
        FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := beta) (fexp := FLT_exp emin prec)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice) (x := x) hβ hflt
      simpa [FloatSpec.Calc.Round.round, Znearest, FloatSpec.Compat.Scaffold.ZnearestMode] using h
    rw [hround]
    have hcoeff_nonneg : 0 ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1) :=
      mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbpos (-prec + 1)))
    simpa using mul_nonneg hcoeff_nonneg (abs_nonneg x)
  · have hbound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x| := le_of_not_gt hxsmall
    exact relative_error_N_FLT_round (beta := beta) (choice := choice) (emin := emin)
      (prec := prec) x hβ hbound

/-- FLT error nearest auxiliary -/
lemma error_N_FLT_aux (x : ℝ) (hβ : 1 < beta) (h_pos : 0 < x) :
  ∃ eps eta, |eps| ≤ (1/2) * (beta : ℝ) ^ (-prec + 1) ∧
    |eta| ≤ (1/2) * (beta : ℝ) ^ emin ∧
    eps * eta = 0 ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
  by_cases hxlarge : (beta : ℝ) ^ (emin + prec) ≤ x
  · have hxabs : (beta : ℝ) ^ (emin + prec) ≤ |x| := by
      simpa [abs_of_pos h_pos] using hxlarge
    have hmin : ∀ k, emin + prec < k → prec ≤ k - FLT_exp emin prec k := by
      intro k hk
      have hk' : emin + prec - 1 < k := by omega
      exact relative_error_FLT_aux (emin := emin) (prec := prec) k hk'
    rcases relative_error_N_ex (beta := beta) (fexp := FLT_exp emin prec)
        (emin := emin + prec) (p := prec) (choice := choice) x hβ hmin hxabs with
      ⟨eps, heps, hround⟩
    refine ⟨eps, 0, heps, ?_, ?_, ?_⟩
    · have hrhs : 0 ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ emin :=
        mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbpos emin))
      simpa using hrhs
    · ring
    · rw [hround]
      ring
  · have hxsmall : x < (beta : ℝ) ^ (emin + prec) := lt_of_not_ge hxlarge
    have hxabs_small : |x| < (beta : ℝ) ^ (emin + prec) := by
      simpa [abs_of_pos h_pos] using hxsmall
    let fexpFLT : Int → Int := FLT_exp emin prec
    let e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexpFLT x
    let sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpFLT x
    let zn : Int := FloatSpec.Core.Generic_fmt.Znearest choice sm
    have hx_ne : x ≠ 0 := ne_of_gt h_pos
    have hmag_le : FloatSpec.Core.Raux.mag beta x ≤ emin + prec := by
      have htrip := FloatSpec.Core.Raux.mag_le_bpow
        (beta := beta) (x := x) (e := emin + prec) hβ hx_ne hxabs_small
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip trivial
    have hcexp : e = emin := by
      have hmax : max (FloatSpec.Core.Raux.mag beta x - prec) emin = emin := by
        apply max_eq_right
        omega
      simp [e, fexpFLT, FloatSpec.Core.Generic_fmt.cexp, FLT_exp,
        FloatSpec.Core.FLT.FLT_exp, hmax]
    have hscaled : sm * (beta : ℝ) ^ e = x := by
      have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
        (beta := beta) (fexp := fexpFLT) (x := x)
      simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, e] using htrip hβ
    have hround :
        FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x =
          (zn : ℝ) * (beta : ℝ) ^ e := by
      simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode, fexpFLT, e, sm, zn]
    have hnearest : |(zn : ℝ) - sm| ≤ (1 / 2 : ℝ) := by
      have htrip := FloatSpec.Core.Generic_fmt.Znearest_half choice sm
      simpa [zn, abs_sub_comm,
        Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip
    refine ⟨0, FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x,
      ?_, ?_, ?_, ?_⟩
    · have hrhs : 0 ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1) :=
        mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbpos (-prec + 1)))
      simpa using hrhs
    · have hdiff :
          FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x =
            ((zn : ℝ) - sm) * (beta : ℝ) ^ e := by
        rw [hround, ← hscaled]
        ring
      rw [hdiff, abs_mul, hcexp]
      have hpow_nonneg : 0 ≤ (beta : ℝ) ^ emin := le_of_lt (zpow_pos hbpos emin)
      have hmul := mul_le_mul_of_nonneg_right hnearest hpow_nonneg
      simpa [abs_of_nonneg hpow_nonneg, mul_assoc] using hmul
    · ring
    · ring

/-- FLT relative error nearest alternative existence -/
theorem relative_error_N_FLT'_ex (x : ℝ) (hβ : 1 < beta) :
  ∃ eps eta, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
    |eta| ≤ (1/2) * (beta : ℝ) ^ emin ∧
    eps * eta = 0 ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  by_cases hlarge : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|
  · rcases relative_error_N_FLX'_ex (beta := beta) (choice := choice) (prec := prec)
      hβ x with ⟨eps, heps, hround_flx⟩
    refine ⟨eps, 0, heps, ?_, ?_, ?_⟩
    · have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
      have hrhs : 0 ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ emin :=
        mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbpos emin))
      simpa using hrhs
    · ring
    · have hround_eq :
          FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x =
            FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x :=
        round_FLT_FLX_nearest (beta := beta) (choice := choice) (prec := prec)
          (emin := emin) x hβ hlarge
      rw [hround_eq, hround_flx]
      ring
  · have hsmall :
        |x| < (beta : ℝ) ^ (emin + prec - 1) := by
      exact lt_of_not_ge hlarge
    let fexpFLT : Int → Int := FLT_exp emin prec
    let e : Int := FloatSpec.Core.Generic_fmt.cexp beta fexpFLT x
    let sm : ℝ := FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexpFLT x
    let zn : Int := FloatSpec.Core.Generic_fmt.Znearest choice sm
    by_cases hx0 : x = 0
    · subst x
      refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
      · simpa using u_rod1pu_ro_pos (beta := beta) (prec := prec) hβ
      · have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
        have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
        have hrhs : 0 ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ emin :=
          mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbpos emin))
        simpa using hrhs
      · ring
      · have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
          unfold FloatSpec.Core.Generic_fmt.Znearest
          simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
        simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
          FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
          FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
    · have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
      have hpow_step :
          (beta : ℝ) ^ (emin + prec - 1) ≤ (beta : ℝ) ^ (emin + prec) := by
        have h := FloatSpec.Core.Raux.bpow_le (beta := beta)
          (e1 := emin + prec - 1) (e2 := emin + prec) hβ (by omega)
        simpa [FloatSpec.Core.Raux.bpow_le_check, Std.Do.wp,
          Std.Do.PostCond.noThrow, Id.run, pure] using h trivial
      have hxabs_small : |x| < (beta : ℝ) ^ (emin + prec) :=
        lt_of_lt_of_le hsmall hpow_step
      have hmag_le : FloatSpec.Core.Raux.mag beta x ≤ emin + prec := by
        have htrip := FloatSpec.Core.Raux.mag_le_bpow
          (beta := beta) (x := x) (e := emin + prec) hβ hx0 hxabs_small
        simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip trivial
      have hcexp : e = emin := by
        have hmax : max (FloatSpec.Core.Raux.mag beta x - prec) emin = emin := by
          apply max_eq_right
          omega
        simp [e, fexpFLT, FloatSpec.Core.Generic_fmt.cexp, FLT_exp,
          FloatSpec.Core.FLT.FLT_exp, hmax]
      have hscaled : sm * (beta : ℝ) ^ e = x := by
        have htrip := FloatSpec.Core.Generic_fmt.scaled_mantissa_mult_bpow
          (beta := beta) (fexp := fexpFLT) (x := x)
        simpa [Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure, sm, e] using htrip hβ
      have hround :
          FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x =
            (zn : ℝ) * (beta : ℝ) ^ e := by
        simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
          FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
          FloatSpec.Compat.Scaffold.ZnearestMode, fexpFLT, e, sm, zn]
      have hnearest : |(zn : ℝ) - sm| ≤ (1 / 2 : ℝ) := by
        have htrip := FloatSpec.Core.Generic_fmt.Znearest_half choice sm
        simpa [zn, abs_sub_comm,
          Std.Do.wp, Std.Do.PostCond.noThrow, Id.run, pure] using htrip
      refine ⟨0, FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x,
        ?_, ?_, ?_, ?_⟩
      · simpa using u_rod1pu_ro_pos (beta := beta) (prec := prec) hβ
      · have hdiff :
            FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x =
              ((zn : ℝ) - sm) * (beta : ℝ) ^ e := by
          rw [hround, ← hscaled]
          ring
        rw [hdiff, abs_mul, hcexp]
        have hpow_nonneg : 0 ≤ (beta : ℝ) ^ emin := le_of_lt (zpow_pos hbpos emin)
        have hmul := mul_le_mul_of_nonneg_right hnearest hpow_nonneg
        simpa [abs_of_nonneg hpow_nonneg, mul_assoc] using hmul
      · ring
      · ring

/-- FLT relative error nearest alternative separate -/
theorem relative_error_N_FLT'_ex_separate (x : ℝ) (hβ : 1 < beta) :
  ∃ x', FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x' =
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x ∧
    (∃ eta, |eta| ≤ (1/2) * (beta : ℝ) ^ emin ∧ x' = x + eta) ∧
    (∃ eps, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
      FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x' = x' * (1 + eps)) := by
  let rx : ℝ := FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x
  rcases relative_error_N_FLT'_ex (beta := beta) (choice := choice) (prec := prec)
      (emin := emin) x hβ with
    ⟨eps, eta, heps, heta, hprod, hround⟩
  rcases mul_eq_zero.mp hprod with heps0 | heta0
  · have hfmt :
        FloatSpec.Core.Generic_fmt.generic_format beta (FLT_exp emin prec) rx := by
      simpa [rx, FloatSpec.Calc.Round.round, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode] using
        (FloatSpec.Core.Generic_fmt.generic_format_roundR
          (beta := beta) (fexp := FLT_exp emin prec)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice) (x := x) hβ)
    have hfix :
        FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) rx = rx := by
      have h :=
        FloatSpec.Core.Generic_fmt.roundR_generic
          (beta := beta) (fexp := FLT_exp emin prec)
          (rnd := FloatSpec.Core.Generic_fmt.Znearest choice) (x := rx) hβ hfmt
      simpa [FloatSpec.Calc.Round.round, Znearest, FloatSpec.Compat.Scaffold.ZnearestMode] using h
    refine ⟨rx, ?_, ?_, ?_⟩
    ·
      simpa [rx] using hfix
    · refine ⟨eta, heta, ?_⟩
      calc
        rx = FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x := by rfl
        _ = x * (1 + eps) + eta := hround
        _ = x + eta := by rw [heps0]; ring
    · refine ⟨0, ?_, ?_⟩
      · simpa using u_rod1pu_ro_pos (beta := beta) (prec := prec) hβ
      · calc
          FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) rx = rx := hfix
          _ = rx * (1 + 0) := by ring
  · refine ⟨x, ?_, ?_, ?_⟩
    · rfl
    · refine ⟨0, ?_, by ring⟩
      have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
      have hrhs : 0 ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ emin :=
        mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbpos emin))
      simpa using hrhs
    · refine ⟨eps, heps, ?_⟩
      rw [hround, heta0]
      ring

/-- General FLT error nearest -/
theorem error_N_FLT_from_prec_instance_payload
    (emin prec : Int) [Prec_gt_0 prec] (hβ : 1 < beta) (h_pos : 0 < prec)
  (choice : Int → Bool) (x : ℝ) :
  ∃ eps eta, |eps| ≤ (1/2) * (beta : ℝ) ^ (-prec + 1) ∧
    |eta| ≤ (1/2) * (beta : ℝ) ^ emin ∧
    eps * eta = 0 ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · let choice' : Int → Bool := fun t => ! choice (-(t + 1))
    have hpos_neg : 0 < -x := by linarith
    rcases error_N_FLT_aux (beta := beta) (choice := choice') (prec := prec)
        (emin := emin) (-x) hβ hpos_neg with
      ⟨eps, eta, heps, heta, hprod, hround⟩
    refine ⟨eps, -eta, heps, ?_, ?_, ?_⟩
    · simpa [abs_neg] using heta
    · simpa using congrArg Neg.neg hprod
    · have hopp :
          FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x =
            - FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice') (-x) := by
        have h :=
          FloatSpec.Core.Generic_fmt.round_N_opp
            (beta := beta) (fexp := FLT_exp emin prec) (choice := choice) (x := -x)
        simpa [FloatSpec.Calc.Round.round, Znearest, FloatSpec.Compat.Scaffold.ZnearestMode,
          choice'] using h
      rw [hopp, hround]
      ring
  · subst x
    refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
    · have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
      have hrhs : 0 ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ (-prec + 1) :=
        mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbpos (-prec + 1)))
      simpa using hrhs
    · have hbpos_int : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbpos_int
      have hrhs : 0 ≤ (1 / 2 : ℝ) * (beta : ℝ) ^ emin :=
        mul_nonneg (by norm_num) (le_of_lt (zpow_pos hbpos emin))
      simpa using hrhs
    · ring
    · have hZ0 : FloatSpec.Core.Generic_fmt.Znearest choice 0 = 0 := by
        unfold FloatSpec.Core.Generic_fmt.Znearest
        simp [FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Rcompare]
      simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa, Znearest,
        FloatSpec.Compat.Scaffold.ZnearestMode, hZ0]
  · exact error_N_FLT_aux (beta := beta) (choice := choice) (prec := prec)
      (emin := emin) x hβ hx_pos

/-- Exact public contract exported by Coq `error_N_FLT`; the class instance is
derived from the source precision premise. -/
theorem error_N_FLT (emin prec : Int) (hβ : 1 < beta) (h_pos : 0 < prec)
    (choice : Int → Bool) (x : ℝ) :
  ∃ eps eta, |eps| ≤ (1/2) * (beta : ℝ) ^ (-prec + 1) ∧
    |eta| ≤ (1/2) * (beta : ℝ) ^ emin ∧
    eps * eta = 0 ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x =
      x * (1 + eps) + eta := by
  letI : Prec_gt_0 prec := ⟨h_pos⟩
  exact error_N_FLT_from_prec_instance_payload
    (beta := beta) (emin := emin) (prec := prec) hβ h_pos choice x
