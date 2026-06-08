import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import Mathlib.Data.Real.Basic

/-!
Tier 1 Scaffold / Tier 3 Excluded.

This property-analysis leaf preserves translated names for audit and future
porting. It is not re-exported by `FloatSpec.src.Prop` and is not part of the
trusted FloatSpec aggregate.
-/

-- Relative error of the roundings
-- Translated from Coq file: flocq/src/Prop/Relative.v

open Real

variable (beta : Int)

-- Section: Relative error conversions

variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Relative error less than conversion -/
lemma relative_error_lt_conversion (rnd : ℝ → Int) [Valid_rnd rnd] (x b : ℝ)
  (h_pos : 0 < b)
  (h_bound : x ≠ 0 → |FloatSpec.Calc.Round.round beta fexp () x - x| < b * |x|) :
  ∃ eps, |eps| < b ∧ FloatSpec.Calc.Round.round beta fexp () x = x * (1 + eps) := by
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa using h_pos
    · subst x
      have hround0 :
          FloatSpec.Calc.Round.round beta fexp FloatSpec.Calc.Round.nearestEvenMode 0 = 0 := by
        simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
          FloatSpec.Core.Generic_fmt.scaled_mantissa,
          FloatSpec.Calc.Round.nearestEvenMode.rnd_zero]
      simpa using hround0
  · refine ⟨(FloatSpec.Calc.Round.round beta fexp () x - x) / x, ?_, ?_⟩
    · have h := h_bound hx
      have hx_abs_pos : 0 < |x| := abs_pos.mpr hx
      have hdiv := div_lt_div_of_pos_right h hx_abs_pos
      have hrhs : (b * |x|) / |x| = b := by
        field_simp [ne_of_gt hx_abs_pos]
      simpa [abs_div, hrhs] using hdiv
    · field_simp [hx]
      ring

/-- Relative error less than or equal conversion -/
lemma relative_error_le_conversion (rnd : ℝ → Int) [Valid_rnd rnd] (x b : ℝ)
  (h_nonneg : 0 ≤ b)
  (h_bound : |FloatSpec.Calc.Round.round beta fexp () x - x| ≤ b * |x|) :
  ∃ eps, |eps| ≤ b ∧ FloatSpec.Calc.Round.round beta fexp () x = x * (1 + eps) := by
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa using h_nonneg
    · subst x
      have hround0 :
          FloatSpec.Calc.Round.round beta fexp FloatSpec.Calc.Round.nearestEvenMode 0 = 0 := by
        simp [FloatSpec.Calc.Round.round, FloatSpec.Core.Generic_fmt.roundR,
          FloatSpec.Core.Generic_fmt.scaled_mantissa,
          FloatSpec.Calc.Round.nearestEvenMode.rnd_zero]
      simpa using hround0
  · refine ⟨(FloatSpec.Calc.Round.round beta fexp () x - x) / x, ?_, ?_⟩
    · have hx_abs_pos : 0 < |x| := abs_pos.mpr hx
      have hdiv := div_le_div_of_nonneg_right h_bound (le_of_lt hx_abs_pos)
      have hrhs : (b * |x|) / |x| = b := by
        field_simp [ne_of_gt hx_abs_pos]
      simpa [abs_div, hrhs] using hdiv
    · field_simp [hx]
      ring

/-- Relative error less than or equal conversion inverse -/
lemma relative_error_le_conversion_inv (rnd : ℝ → Int) [Valid_rnd rnd] (x b : ℝ)
  (h_exists : ∃ eps, |eps| ≤ b ∧ FloatSpec.Calc.Round.round beta fexp () x = x * (1 + eps)) :
  |FloatSpec.Calc.Round.round beta fexp () x - x| ≤ b * |x| := by
  rcases h_exists with ⟨eps, heps, hround⟩
  rw [hround]
  have hcalc : x * (1 + eps) - x = eps * x := by ring
  rw [hcalc]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right heps (abs_nonneg x)

/-- Relative error less than or equal conversion round inverse -/
lemma relative_error_le_conversion_round_inv (rnd : ℝ → Int) [Valid_rnd rnd] (x b : ℝ)
  (h_exists : ∃ eps, |eps| ≤ b ∧ x = FloatSpec.Calc.Round.round beta fexp () x * (1 + eps)) :
  |FloatSpec.Calc.Round.round beta fexp () x - x| ≤ b * |FloatSpec.Calc.Round.round beta fexp () x| := by
  rcases h_exists with ⟨eps, heps, hx⟩
  set rx : ℝ := FloatSpec.Calc.Round.round beta fexp () x with hrx
  have hx' : x = rx * (1 + eps) := by
    simpa [hrx] using hx
  rw [hx']
  have hcalc : rx - rx * (1 + eps) = -(eps * rx) := by ring
  rw [hcalc]
  rw [abs_neg, abs_mul]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_right heps (abs_nonneg rx)

-- Section: Generic relative error

variable (emin p : Int)
variable (h_min : ∀ k, emin < k → p ≤ k - fexp k)

/-- Relative error bound -/
theorem relative_error (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ)
  (h_bound : (Int.natAbs beta : ℝ) ^ (Int.natAbs emin : Nat) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta fexp () x - x| <
    (Int.natAbs beta : ℝ) ^ (Int.natAbs (-p + 1) : Nat) * |x| := by
  sorry

/-- Relative error existence -/
theorem relative_error_ex (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ)
  (h_bound : (Int.natAbs beta : ℝ) ^ (Int.natAbs emin : Nat) ≤ |x|) :
  ∃ eps, |eps| < (Int.natAbs beta : ℝ) ^ (Int.natAbs (-p + 1) : Nat) ∧
    FloatSpec.Calc.Round.round beta fexp () x = x * (1 + eps) := by
  sorry

/-- Relative error F2R emin -/
theorem relative_error_F2R_emin (rnd : ℝ → Int) [Valid_rnd rnd] (m : Int)
  (h_nonzero : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) ≠ 0) :
  |FloatSpec.Calc.Round.round beta fexp () (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| <
    (Int.natAbs beta : ℝ) ^ (Int.natAbs (-p + 1) : Nat) *
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| := by
  sorry

/-- Relative error F2R emin existence -/
theorem relative_error_F2R_emin_ex (rnd : ℝ → Int) [Valid_rnd rnd] (m : Int) :
  ∃ eps, |eps| < (Int.natAbs beta : ℝ) ^ (Int.natAbs (-p + 1) : Nat) ∧
    FloatSpec.Calc.Round.round beta fexp () (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) =
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) * (1 + eps) := by
  sorry

/-- Relative error round -/
theorem relative_error_round (rnd : ℝ → Int) [Valid_rnd rnd] (h_pos : 0 < p) (x : ℝ)
  (h_bound : (Int.natAbs beta : ℝ) ^ (Int.natAbs emin : Nat) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta fexp () x - x| <
    (Int.natAbs beta : ℝ) ^ (Int.natAbs (-p + 1) : Nat) *
    |FloatSpec.Calc.Round.round beta fexp () x| := by
  sorry

/-- Relative error round F2R emin -/
theorem relative_error_round_F2R_emin (rnd : ℝ → Int) [Valid_rnd rnd] (h_pos : 0 < p) (m : Int)
  (h_nonzero : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) ≠ 0) :
  |FloatSpec.Calc.Round.round beta fexp () (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| <
    (Int.natAbs beta : ℝ) ^ (Int.natAbs (-p + 1) : Nat) *
    |FloatSpec.Calc.Round.round beta fexp () (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta))| := by
  sorry

-- Section: Nearest rounding relative error

variable (choice : Int → Bool)

/-- Relative error nearest -/
theorem relative_error_N (x : ℝ)
  (h_bound : (Int.natAbs beta : ℝ) ^ (Int.natAbs emin : Nat) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| ≤
    (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-p + 1) : Nat) * |x| := by
  sorry

/-- Relative error nearest existence -/
theorem relative_error_N_ex (x : ℝ)
  (h_bound : (Int.natAbs beta : ℝ) ^ (Int.natAbs emin : Nat) ≤ |x|) :
  ∃ eps, |eps| ≤ (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-p + 1) : Nat) ∧
    FloatSpec.Calc.Round.round beta fexp (Znearest choice) x = x * (1 + eps) := by
  sorry

/-- Relative error nearest F2R emin -/
theorem relative_error_N_F2R_emin (m : Int) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| ≤
    (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-p + 1) : Nat) *
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| := by
  sorry

/-- Relative error nearest F2R emin existence -/
theorem relative_error_N_F2R_emin_ex (m : Int) :
  ∃ eps, |eps| ≤ (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-p + 1) : Nat) ∧
    FloatSpec.Calc.Round.round beta fexp (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) =
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) * (1 + eps) := by
  sorry

/-- Relative error nearest round -/
theorem relative_error_N_round (h_pos : 0 < p) (x : ℝ)
  (h_bound : (Int.natAbs beta : ℝ) ^ (Int.natAbs emin : Nat) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| ≤
    (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-p + 1) : Nat) *
    |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x| := by
  sorry

/-- Relative error nearest round F2R emin -/
theorem relative_error_N_round_F2R_emin (h_pos : 0 < p) (m : Int) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| ≤
    (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-p + 1) : Nat) *
    |FloatSpec.Calc.Round.round beta fexp (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta))| := by
  sorry

-- Section: FLX relative error

variable (prec : Int)
variable [Prec_gt_0 prec]

/-- FLX relative error auxiliary -/
lemma relative_error_FLX_aux (k : Int) : prec ≤ k - FLX_exp prec k := by
  simp [FLX_exp, FloatSpec.Core.FLX.FLX_exp]

/-- FLX relative error -/
theorem relative_error_FLX (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ) (h_nonzero : x ≠ 0) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) () x - x| <
    (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) * |x| := by
  sorry

/-- FLX relative error existence -/
theorem relative_error_FLX_ex (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ) :
  ∃ eps, |eps| < (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    FloatSpec.Calc.Round.round beta (FLX_exp prec) () x = x * (1 + eps) := by
  sorry

/-- FLX relative error round -/
theorem relative_error_FLX_round (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ) (h_nonzero : x ≠ 0) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) () x - x| <
    (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) *
    |FloatSpec.Calc.Round.round beta (FLX_exp prec) () x| := by
  sorry

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
        (FloatSpec.Core.Generic_fmt.Znearest_half_theorem choice sm) True.intro
      simpa [FloatSpec.Core.Generic_fmt.Znearest_half_check,
        FloatSpec.Core.Generic_fmt.Znearest_N_strict_check, zn, abs_sub_comm,
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

/-- FLX relative error nearest alternative -/
theorem relative_error_N_FLX' (hβ : 1 < beta) (x : ℝ) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
    u_ro beta prec / (1 + u_ro beta prec) * |x| := by
  sorry

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
  sorry

/-- Relative error nearest round derivation -/
lemma relative_error_N_round_ex_derive (x rx : ℝ)
  (hβ : 1 < beta)
  (h_exists : ∃ eps, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧ rx = x * (1 + eps)) :
  ∃ eps, |eps| ≤ u_ro beta prec ∧ x = rx * (1 + eps) := by
  sorry

/-- FLX relative error nearest round existence -/
theorem relative_error_N_FLX_round_ex (hβ : 1 < beta) (x : ℝ) :
  ∃ eps, |eps| ≤ u_ro beta prec ∧
    x = FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x * (1 + eps) := by
  sorry

/-- FLX relative error nearest round -/
theorem relative_error_N_FLX_round (hβ : 1 < beta) (x : ℝ) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
    u_ro beta prec *
    |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x| := by
  sorry

-- Section: FLT relative error

variable (emin : Int)

/-- FLT relative error auxiliary -/
lemma relative_error_FLT_aux (k : Int) (h_bound : emin + prec - 1 < k) :
  prec ≤ k - FLT_exp emin prec k := by
  simp [FLT_exp, FloatSpec.Core.FLT.FLT_exp]
  omega

/-- FLT relative error -/
theorem relative_error_FLT (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ)
  (h_bound : (Int.natAbs beta : ℝ) ^ (Int.natAbs (emin + prec - 1) : Nat) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) () x - x| <
    (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) * |x| := by
  -- Ensure `Valid_exp` is available for the FLT exponent under the given `prec`.
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  -- Proof content not yet ported.
  sorry

/-- FLT relative error F2R emin -/
theorem relative_error_FLT_F2R_emin (rnd : ℝ → Int) [Valid_rnd rnd] (m : Int)
  (h_nonzero : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) ≠ 0) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) () (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| <
    (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) *
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| := by
  sorry

/-- FLT relative error F2R emin existence -/
theorem relative_error_FLT_F2R_emin_ex (rnd : ℝ → Int) [Valid_rnd rnd] (m : Int) :
  ∃ eps, |eps| < (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) () (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) =
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) * (1 + eps) := by
  sorry

/-- FLT relative error existence -/
theorem relative_error_FLT_ex (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ)
  (h_bound : (Int.natAbs beta : ℝ) ^ (Int.natAbs (emin + prec - 1) : Nat) ≤ |x|) :
  ∃ eps, |eps| < (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) () x = x * (1 + eps) := by
  sorry

/-- FLT relative error nearest -/
theorem relative_error_N_FLT (x : ℝ)
  (h_bound : (Int.natAbs beta : ℝ) ^ (Int.natAbs (emin + prec - 1) : Nat) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x| ≤
    (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) * |x| := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT relative error nearest existence -/
theorem relative_error_N_FLT_ex (x : ℝ)
  (h_bound : (Int.natAbs beta : ℝ) ^ (Int.natAbs (emin + prec - 1) : Nat) ≤ |x|) :
  ∃ eps, |eps| ≤ (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT relative error nearest round -/
theorem relative_error_N_FLT_round (x : ℝ)
  (h_bound : (Int.natAbs beta : ℝ) ^ (Int.natAbs (emin + prec - 1) : Nat) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x| ≤
    (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) *
    |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x| := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT relative error nearest F2R emin -/
theorem relative_error_N_FLT_F2R_emin (m : Int) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| ≤
    (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) *
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT relative error nearest F2R emin existence -/
theorem relative_error_N_FLT_F2R_emin_ex (m : Int) :
  ∃ eps, |eps| ≤ (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) =
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) * (1 + eps) := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT relative error nearest round F2R emin -/
theorem relative_error_N_FLT_round_F2R_emin (m : Int) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| ≤
    (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) *
    |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta))| := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT error nearest auxiliary -/
lemma error_N_FLT_aux (x : ℝ) (h_pos : 0 < x) :
  ∃ eps eta, |eps| ≤ (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    |eta| ≤ (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs emin : Nat) ∧
    eps * eta = 0 ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  sorry

/-- FLT relative error nearest alternative existence -/
theorem relative_error_N_FLT'_ex (x : ℝ) :
  ∃ eps eta, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
    |eta| ≤ (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs emin : Nat) ∧
    eps * eta = 0 ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT relative error nearest alternative separate -/
theorem relative_error_N_FLT'_ex_separate (x : ℝ) :
  ∃ x', FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x' =
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x ∧
    (∃ eta, |eta| ≤ (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs emin : Nat) ∧ x' = x + eta) ∧
    (∃ eps, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
      FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x' = x' * (1 + eps)) := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- General FLT error nearest -/
theorem error_N_FLT (emin prec : Int) [Prec_gt_0 prec] (h_pos : 0 < prec) (choice : Int → Bool) (x : ℝ) :
  ∃ eps eta, |eps| ≤ (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    |eta| ≤ (1/2) * (Int.natAbs beta : ℝ) ^ (Int.natAbs emin : Nat) ∧
    eps * eta = 0 ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  -- Provide the `Prec_gt_0` instance required for `Valid_exp` on `FLT_exp`.
  haveI : Prec_gt_0 prec := ⟨h_pos⟩
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry
