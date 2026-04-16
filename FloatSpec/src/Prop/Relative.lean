-- Relative error of the roundings
-- Translated from Coq file: flocq/src/Prop/Relative.v

import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import Mathlib.Data.Real.Basic

open Real

variable (beta : Int)

-- Section: Relative error conversions

variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Relative error less than conversion -/
lemma relative_error_lt_conversion (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x b : ℝ)
  (h_pos : 0 < b)
  (h_bound : x ≠ 0 → |FloatSpec.Calc.Round.round beta fexp rnd x - x| < b * |x|) :
  ∃ eps, |eps| < b ∧ FloatSpec.Calc.Round.round beta fexp rnd x = x * (1 + eps) := by
  sorry

/-- Relative error less than or equal conversion -/
lemma relative_error_le_conversion (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x b : ℝ)
  (h_nonneg : 0 ≤ b)
  (h_bound : |FloatSpec.Calc.Round.round beta fexp rnd x - x| ≤ b * |x|) :
  ∃ eps, |eps| ≤ b ∧ FloatSpec.Calc.Round.round beta fexp rnd x = x * (1 + eps) := by
  sorry

/-- Relative error less than or equal conversion inverse -/
lemma relative_error_le_conversion_inv (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x b : ℝ)
  (h_exists : ∃ eps, |eps| ≤ b ∧ FloatSpec.Calc.Round.round beta fexp rnd x = x * (1 + eps)) :
  |FloatSpec.Calc.Round.round beta fexp rnd x - x| ≤ b * |x| := by
  sorry

/-- Relative error less than or equal conversion round inverse -/
lemma relative_error_le_conversion_round_inv (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x b : ℝ)
  (h_exists : ∃ eps, |eps| ≤ b ∧ x = FloatSpec.Calc.Round.round beta fexp rnd x * (1 + eps)) :
  |FloatSpec.Calc.Round.round beta fexp rnd x - x| ≤ b * |FloatSpec.Calc.Round.round beta fexp rnd x| := by
  sorry

-- Section: Generic relative error

variable (emin p : Int)
variable (h_min : ∀ k, emin < k → p ≤ k - fexp k)

/-- Relative error bound -/
theorem relative_error (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
  (h_bound : (beta : ℝ) ^ emin ≤ |x|) :
  |FloatSpec.Calc.Round.round beta fexp rnd x - x| <
    (beta : ℝ) ^ (1 - p) * |x| := by
  sorry

/-- Relative error existence -/
theorem relative_error_ex (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
  (h_bound : (beta : ℝ) ^ emin ≤ |x|) :
  ∃ eps, |eps| < (beta : ℝ) ^ (1 - p) ∧
    FloatSpec.Calc.Round.round beta fexp rnd x = x * (1 + eps) := by
  sorry

/-- Relative error F2R emin -/
theorem relative_error_F2R_emin (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (m : Int)
  (h_nonzero : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) ≠ 0) :
  |FloatSpec.Calc.Round.round beta fexp rnd (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| <
    (beta : ℝ) ^ (1 - p) *
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| := by
  sorry

/-- Relative error F2R emin existence -/
theorem relative_error_F2R_emin_ex (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (m : Int) :
  ∃ eps, |eps| < (beta : ℝ) ^ (1 - p) ∧
    FloatSpec.Calc.Round.round beta fexp rnd (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) =
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) * (1 + eps) := by
  sorry

/-- Relative error round -/
theorem relative_error_round (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (h_pos : 0 < p) (x : ℝ)
  (h_bound : (beta : ℝ) ^ emin ≤ |x|) :
  |FloatSpec.Calc.Round.round beta fexp rnd x - x| <
    (beta : ℝ) ^ (1 - p) *
    |FloatSpec.Calc.Round.round beta fexp rnd x| := by
  sorry

/-- Relative error round F2R emin -/
theorem relative_error_round_F2R_emin (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (h_pos : 0 < p) (m : Int)
  (h_nonzero : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) ≠ 0) :
  |FloatSpec.Calc.Round.round beta fexp rnd (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| <
    (beta : ℝ) ^ (1 - p) *
    |FloatSpec.Calc.Round.round beta fexp rnd (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta))| := by
  sorry

-- Section: Nearest rounding relative error

variable (choice : Int → Bool)

/-- Relative error nearest -/
theorem relative_error_N (x : ℝ)
  (h_bound : (beta : ℝ) ^ emin ≤ |x|) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| ≤
    (1/2) * (beta : ℝ) ^ (1 - p) * |x| := by
  sorry

/-- Relative error nearest existence -/
theorem relative_error_N_ex (x : ℝ)
  (h_bound : (beta : ℝ) ^ emin ≤ |x|) :
  ∃ eps, |eps| ≤ (1/2) * (beta : ℝ) ^ (1 - p) ∧
    FloatSpec.Calc.Round.round beta fexp (Znearest choice) x = x * (1 + eps) := by
  sorry

/-- Relative error nearest F2R emin -/
theorem relative_error_N_F2R_emin (m : Int) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| ≤
    (1/2) * (beta : ℝ) ^ (1 - p) *
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| := by
  sorry

/-- Relative error nearest F2R emin existence -/
theorem relative_error_N_F2R_emin_ex (m : Int) :
  ∃ eps, |eps| ≤ (1/2) * (beta : ℝ) ^ (1 - p) ∧
    FloatSpec.Calc.Round.round beta fexp (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) =
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) * (1 + eps) := by
  sorry

/-- Relative error nearest round -/
theorem relative_error_N_round (h_pos : 0 < p) (x : ℝ)
  (h_bound : (beta : ℝ) ^ emin ≤ |x|) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x - x| ≤
    (1/2) * (beta : ℝ) ^ (1 - p) *
    |FloatSpec.Calc.Round.round beta fexp (Znearest choice) x| := by
  sorry

/-- Relative error nearest round F2R emin -/
theorem relative_error_N_round_F2R_emin (h_pos : 0 < p) (m : Int) :
  |FloatSpec.Calc.Round.round beta fexp (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| ≤
    (1/2) * (beta : ℝ) ^ (1 - p) *
    |FloatSpec.Calc.Round.round beta fexp (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta))| := by
  sorry

-- Section: FLX relative error

variable (prec : Int)
variable [Prec_gt_0 prec]

/-- FLX relative error auxiliary -/
lemma relative_error_FLX_aux (k : Int) : prec ≤ k - FLX_exp prec k := by
  sorry

/-- FLX relative error -/
theorem relative_error_FLX (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ) (h_nonzero : x ≠ 0) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) rnd x - x| <
    (beta : ℝ) ^ (1 - prec) * |x| := by
  sorry

/-- FLX relative error existence -/
theorem relative_error_FLX_ex (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ) :
  ∃ eps, |eps| < (beta : ℝ) ^ (1 - prec) ∧
    FloatSpec.Calc.Round.round beta (FLX_exp prec) rnd x = x * (1 + eps) := by
  sorry

/-- FLX relative error round -/
theorem relative_error_FLX_round (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ) (h_nonzero : x ≠ 0) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) rnd x - x| <
    (beta : ℝ) ^ (1 - prec) *
    |FloatSpec.Calc.Round.round beta (FLX_exp prec) rnd x| := by
  sorry

/-- FLX relative error nearest -/
theorem relative_error_N_FLX (x : ℝ) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
    (1/2) * (beta : ℝ) ^ (1 - prec) * |x| := by
  sorry

/-- Unit roundoff -/
noncomputable def u_ro : ℝ := (1/2) * (beta : ℝ) ^ (1 - prec)

/-- Unit roundoff is positive -/
lemma u_ro_pos : 0 ≤ u_ro beta prec := by
  sorry

/-- Unit roundoff is less than 1 -/
lemma u_ro_lt_1 : u_ro beta prec < 1 := by
  sorry

-- Unit roundoff divided by (1 + u_ro) is positive
lemma u_rod1pu_ro_pos : 0 ≤ u_ro beta prec / (1 + u_ro beta prec) := by
  sorry

/-- Unit roundoff divided by (1 + u_ro) is less than or equal to u_ro -/
lemma u_rod1pu_ro_le_u_ro : u_ro beta prec / (1 + u_ro beta prec) ≤ u_ro beta prec := by
  sorry

/-- FLX relative error nearest alternative -/
theorem relative_error_N_FLX' (x : ℝ) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
    u_ro beta prec / (1 + u_ro beta prec) * |x| := by
  sorry

/-- FLX relative error nearest existence -/
theorem relative_error_N_FLX_ex (x : ℝ) :
  ∃ eps, |eps| ≤ (1/2) * (beta : ℝ) ^ (1 - prec) ∧
    FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x = x * (1 + eps) := by
  sorry

/-- FLX relative error nearest alternative existence -/
theorem relative_error_N_FLX'_ex (x : ℝ) :
  ∃ eps, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
    FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x = x * (1 + eps) := by
  sorry

/-- Relative error nearest round derivation -/
lemma relative_error_N_round_ex_derive (x rx : ℝ)
  (h_exists : ∃ eps, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧ rx = x * (1 + eps)) :
  ∃ eps, |eps| ≤ u_ro beta prec ∧ x = rx * (1 + eps) := by
  sorry

/-- FLX relative error nearest round existence -/
theorem relative_error_N_FLX_round_ex (x : ℝ) :
  ∃ eps, |eps| ≤ u_ro beta prec ∧
    x = FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x * (1 + eps) := by
  sorry

/-- FLX relative error nearest round -/
theorem relative_error_N_FLX_round (x : ℝ) :
  |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x - x| ≤
    (1/2) * (beta : ℝ) ^ (1 - prec) *
    |FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) x| := by
  sorry

-- Section: FLT relative error

variable (emin : Int)

/-- FLT relative error auxiliary -/
lemma relative_error_FLT_aux (k : Int) (h_bound : emin + prec - 1 < k) :
  prec ≤ k - FLT_exp emin prec k := by
  sorry

/-- FLT relative error -/
theorem relative_error_FLT (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
  (h_bound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) rnd x - x| <
    (beta : ℝ) ^ (1 - prec) * |x| := by
  -- Ensure `Valid_exp` is available for the FLT exponent under the given `prec`.
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  -- Proof content not yet ported.
  sorry

/-- FLT relative error F2R emin -/
theorem relative_error_FLT_F2R_emin (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (m : Int)
  (h_nonzero : F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) ≠ 0) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) rnd (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| <
    (beta : ℝ) ^ (1 - prec) *
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| := by
  sorry

/-- FLT relative error F2R emin existence -/
theorem relative_error_FLT_F2R_emin_ex (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (m : Int) :
  ∃ eps, |eps| < (beta : ℝ) ^ (1 - prec) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) rnd (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) =
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) * (1 + eps) := by
  sorry

/-- FLT relative error existence -/
theorem relative_error_FLT_ex (rnd : ℝ → Int)
  [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
  (h_bound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
  ∃ eps, |eps| < (beta : ℝ) ^ (1 - prec) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) rnd x = x * (1 + eps) := by
  sorry

/-- FLT relative error nearest -/
theorem relative_error_N_FLT (x : ℝ)
  (h_bound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x| ≤
    (1/2) * (beta : ℝ) ^ (1 - prec) * |x| := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT relative error nearest existence -/
theorem relative_error_N_FLT_ex (x : ℝ)
  (h_bound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
  ∃ eps, |eps| ≤ (1/2) * (beta : ℝ) ^ (1 - prec) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT relative error nearest round -/
theorem relative_error_N_FLT_round (x : ℝ)
  (h_bound : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x - x| ≤
    (1/2) * (beta : ℝ) ^ (1 - prec) *
    |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x| := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT relative error nearest F2R emin -/
theorem relative_error_N_FLT_F2R_emin (m : Int) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| ≤
    (1/2) * (beta : ℝ) ^ (1 - prec) *
    |F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT relative error nearest F2R emin existence -/
theorem relative_error_N_FLT_F2R_emin_ex (m : Int) :
  ∃ eps, |eps| ≤ (1/2) * (beta : ℝ) ^ (1 - prec) ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) =
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta) * (1 + eps) := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT relative error nearest round F2R emin -/
theorem relative_error_N_FLT_round_F2R_emin (m : Int) :
  |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)) -
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta)| ≤
    (1/2) * (beta : ℝ) ^ (1 - prec) *
    |FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) (F2R (FloatSpec.Core.Defs.FlocqFloat.mk m emin : FloatSpec.Core.Defs.FlocqFloat beta))| := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT error nearest auxiliary -/
lemma error_N_FLT_aux (x : ℝ) (h_pos : 0 < x) :
  ∃ eps eta, |eps| ≤ (1/2) * (beta : ℝ) ^ (1 - prec) ∧
    |eta| ≤ (1/2) * (beta : ℝ) ^ emin ∧
    eps * eta = 0 ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  sorry

/-- FLT relative error nearest alternative existence -/
theorem relative_error_N_FLT'_ex (x : ℝ) :
  ∃ eps eta, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
    |eta| ≤ (1/2) * (beta : ℝ) ^ emin ∧
    eps * eta = 0 ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- FLT relative error nearest alternative separate -/
theorem relative_error_N_FLT'_ex_separate (x : ℝ) :
  ∃ x', FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x' =
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x ∧
    (∃ eta, |eta| ≤ (1/2) * (beta : ℝ) ^ emin ∧ x' = x + eta) ∧
    (∃ eps, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
      FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x' = x' * (1 + eps)) := by
  haveI : Prec_gt_0 prec := inferInstance
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry

/-- General FLT error nearest -/
theorem error_N_FLT (emin prec : Int) [Prec_gt_0 prec] (h_pos : 0 < prec) (choice : Int → Bool) (x : ℝ) :
  ∃ eps eta, |eps| ≤ (1/2) * (beta : ℝ) ^ (1 - prec) ∧
    |eta| ≤ (1/2) * (beta : ℝ) ^ emin ∧
    eps * eta = 0 ∧
    FloatSpec.Calc.Round.round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  -- Provide the `Prec_gt_0` instance required for `Valid_exp` on `FLT_exp`.
  haveI : Prec_gt_0 prec := ⟨h_pos⟩
  have _ := (inferInstance : FloatSpec.Core.Generic_fmt.Valid_exp beta (FLT_exp emin prec))
  sorry
