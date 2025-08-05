-- Relative error of the roundings
-- Translated from Coq file: flocq/src/Prop/Relative.v

import FloatSpec.src.Core

variable (beta : Int)

-- Section: Relative error conversions

variable (fexp : Int → Int)
variable [Valid_exp fexp]

/-- Relative error less than conversion -/
lemma relative_error_lt_conversion (rnd : Float → Int) [Valid_rnd rnd] (x b : Float) 
  (h_pos : 0 < b)
  (h_bound : x ≠ 0 → Float.abs (round beta fexp rnd x - x) < b * Float.abs x) :
  ∃ eps, Float.abs eps < b ∧ round beta fexp rnd x = x * (1 + eps) := by
  sorry

/-- Relative error less than or equal conversion -/
lemma relative_error_le_conversion (rnd : Float → Int) [Valid_rnd rnd] (x b : Float)
  (h_nonneg : 0 ≤ b)
  (h_bound : Float.abs (round beta fexp rnd x - x) ≤ b * Float.abs x) :
  ∃ eps, Float.abs eps ≤ b ∧ round beta fexp rnd x = x * (1 + eps) := by
  sorry

/-- Relative error less than or equal conversion inverse -/
lemma relative_error_le_conversion_inv (rnd : Float → Int) [Valid_rnd rnd] (x b : Float)
  (h_exists : ∃ eps, Float.abs eps ≤ b ∧ round beta fexp rnd x = x * (1 + eps)) :
  Float.abs (round beta fexp rnd x - x) ≤ b * Float.abs x := by
  sorry

/-- Relative error less than or equal conversion round inverse -/
lemma relative_error_le_conversion_round_inv (rnd : Float → Int) [Valid_rnd rnd] (x b : Float)
  (h_exists : ∃ eps, Float.abs eps ≤ b ∧ x = round beta fexp rnd x * (1 + eps)) :
  Float.abs (round beta fexp rnd x - x) ≤ b * Float.abs (round beta fexp rnd x) := by
  sorry

-- Section: Generic relative error

variable (emin p : Int)
variable (h_min : ∀ k, emin < k → p ≤ k - fexp k)

/-- Relative error bound -/
theorem relative_error (rnd : Float → Int) [Valid_rnd rnd] (x : Float)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs emin : Nat) ≤ Float.abs x) :
  Float.abs (round beta fexp rnd x - x) < 
    (Int.natAbs beta : Float) ^ (Int.natAbs (-p + 1) : Nat) * Float.abs x := by
  sorry

/-- Relative error existence -/
theorem relative_error_ex (rnd : Float → Int) [Valid_rnd rnd] (x : Float)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs emin : Nat) ≤ Float.abs x) :
  ∃ eps, Float.abs eps < (Int.natAbs beta : Float) ^ (Int.natAbs (-p + 1) : Nat) ∧
    round beta fexp rnd x = x * (1 + eps) := by
  sorry

/-- Relative error F2R emin -/
theorem relative_error_F2R_emin (rnd : Float → Int) [Valid_rnd rnd] (m : Int)
  (h_nonzero : F2R (FlocqFloat.mk m emin : FlocqFloat beta) ≠ 0) :
  Float.abs (round beta fexp rnd (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) - 
    F2R (FlocqFloat.mk m emin : FlocqFloat beta)) < 
    (Int.natAbs beta : Float) ^ (Int.natAbs (-p + 1) : Nat) * 
    Float.abs (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) := by
  sorry

/-- Relative error F2R emin existence -/
theorem relative_error_F2R_emin_ex (rnd : Float → Int) [Valid_rnd rnd] (m : Int) :
  ∃ eps, Float.abs eps < (Int.natAbs beta : Float) ^ (Int.natAbs (-p + 1) : Nat) ∧
    round beta fexp rnd (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) = 
    F2R (FlocqFloat.mk m emin : FlocqFloat beta) * (1 + eps) := by
  sorry

/-- Relative error round -/
theorem relative_error_round (rnd : Float → Int) [Valid_rnd rnd] (h_pos : 0 < p) (x : Float)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs emin : Nat) ≤ Float.abs x) :
  Float.abs (round beta fexp rnd x - x) < 
    (Int.natAbs beta : Float) ^ (Int.natAbs (-p + 1) : Nat) * 
    Float.abs (round beta fexp rnd x) := by
  sorry

/-- Relative error round F2R emin -/
theorem relative_error_round_F2R_emin (rnd : Float → Int) [Valid_rnd rnd] (h_pos : 0 < p) (m : Int)
  (h_nonzero : F2R (FlocqFloat.mk m emin : FlocqFloat beta) ≠ 0) :
  Float.abs (round beta fexp rnd (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) - 
    F2R (FlocqFloat.mk m emin : FlocqFloat beta)) < 
    (Int.natAbs beta : Float) ^ (Int.natAbs (-p + 1) : Nat) * 
    Float.abs (round beta fexp rnd (F2R (FlocqFloat.mk m emin : FlocqFloat beta))) := by
  sorry

-- Section: Nearest rounding relative error

variable (choice : Int → Bool)

/-- Relative error nearest -/
theorem relative_error_N (x : Float)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs emin : Nat) ≤ Float.abs x) :
  Float.abs (round beta fexp (Znearest choice) x - x) ≤ 
    (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-p + 1) : Nat) * Float.abs x := by
  sorry

/-- Relative error nearest existence -/
theorem relative_error_N_ex (x : Float)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs emin : Nat) ≤ Float.abs x) :
  ∃ eps, Float.abs eps ≤ (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-p + 1) : Nat) ∧
    round beta fexp (Znearest choice) x = x * (1 + eps) := by
  sorry

/-- Relative error nearest F2R emin -/
theorem relative_error_N_F2R_emin (m : Int) :
  Float.abs (round beta fexp (Znearest choice) (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) - 
    F2R (FlocqFloat.mk m emin : FlocqFloat beta)) ≤ 
    (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-p + 1) : Nat) * 
    Float.abs (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) := by
  sorry

/-- Relative error nearest F2R emin existence -/
theorem relative_error_N_F2R_emin_ex (m : Int) :
  ∃ eps, Float.abs eps ≤ (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-p + 1) : Nat) ∧
    round beta fexp (Znearest choice) (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) = 
    F2R (FlocqFloat.mk m emin : FlocqFloat beta) * (1 + eps) := by
  sorry

/-- Relative error nearest round -/
theorem relative_error_N_round (h_pos : 0 < p) (x : Float)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs emin : Nat) ≤ Float.abs x) :
  Float.abs (round beta fexp (Znearest choice) x - x) ≤ 
    (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-p + 1) : Nat) * 
    Float.abs (round beta fexp (Znearest choice) x) := by
  sorry

/-- Relative error nearest round F2R emin -/
theorem relative_error_N_round_F2R_emin (h_pos : 0 < p) (m : Int) :
  Float.abs (round beta fexp (Znearest choice) (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) - 
    F2R (FlocqFloat.mk m emin : FlocqFloat beta)) ≤ 
    (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-p + 1) : Nat) * 
    Float.abs (round beta fexp (Znearest choice) (F2R (FlocqFloat.mk m emin : FlocqFloat beta))) := by
  sorry

-- Section: FLX relative error

variable (prec : Int)
variable [Prec_gt_0 prec]

/-- FLX relative error auxiliary -/
lemma relative_error_FLX_aux (k : Int) : prec ≤ k - FLX_exp prec k := by
  sorry

/-- FLX relative error -/
theorem relative_error_FLX (rnd : Float → Int) [Valid_rnd rnd] (x : Float) (h_nonzero : x ≠ 0) :
  Float.abs (round beta (FLX_exp prec) rnd x - x) < 
    (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) * Float.abs x := by
  sorry

/-- FLX relative error existence -/
theorem relative_error_FLX_ex (rnd : Float → Int) [Valid_rnd rnd] (x : Float) :
  ∃ eps, Float.abs eps < (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    round beta (FLX_exp prec) rnd x = x * (1 + eps) := by
  sorry

/-- FLX relative error round -/
theorem relative_error_FLX_round (rnd : Float → Int) [Valid_rnd rnd] (x : Float) (h_nonzero : x ≠ 0) :
  Float.abs (round beta (FLX_exp prec) rnd x - x) < 
    (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) * 
    Float.abs (round beta (FLX_exp prec) rnd x) := by
  sorry

/-- FLX relative error nearest -/
theorem relative_error_N_FLX (x : Float) :
  Float.abs (round beta (FLX_exp prec) (Znearest choice) x - x) ≤ 
    (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) * Float.abs x := by
  sorry

/-- Unit roundoff -/
def u_ro : Float := (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat)

/-- Unit roundoff is positive -/
lemma u_ro_pos : 0 ≤ u_ro beta prec := by
  sorry

/-- Unit roundoff is less than 1 -/
lemma u_ro_lt_1 : u_ro beta prec < 1 := by
  sorry

/-- Unit roundoff divided by (1 + u_ro) is positive -/
lemma u_rod1pu_ro_pos : 0 ≤ u_ro beta prec / (1 + u_ro beta prec) := by
  sorry

/-- Unit roundoff divided by (1 + u_ro) is less than or equal to u_ro -/
lemma u_rod1pu_ro_le_u_ro : u_ro beta prec / (1 + u_ro beta prec) ≤ u_ro beta prec := by
  sorry

/-- FLX relative error nearest alternative -/
theorem relative_error_N_FLX' (x : Float) :
  Float.abs (round beta (FLX_exp prec) (Znearest choice) x - x) ≤ 
    u_ro beta prec / (1 + u_ro beta prec) * Float.abs x := by
  sorry

/-- FLX relative error nearest existence -/
theorem relative_error_N_FLX_ex (x : Float) :
  ∃ eps, Float.abs eps ≤ (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    round beta (FLX_exp prec) (Znearest choice) x = x * (1 + eps) := by
  sorry

/-- FLX relative error nearest alternative existence -/
theorem relative_error_N_FLX'_ex (x : Float) :
  ∃ eps, Float.abs eps ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
    round beta (FLX_exp prec) (Znearest choice) x = x * (1 + eps) := by
  sorry

/-- Relative error nearest round derivation -/
lemma relative_error_N_round_ex_derive (x rx : Float)
  (h_exists : ∃ eps, Float.abs eps ≤ u_ro beta prec / (1 + u_ro beta prec) ∧ rx = x * (1 + eps)) :
  ∃ eps, Float.abs eps ≤ u_ro beta prec ∧ x = rx * (1 + eps) := by
  sorry

/-- FLX relative error nearest round existence -/
theorem relative_error_N_FLX_round_ex (x : Float) :
  ∃ eps, Float.abs eps ≤ u_ro beta prec ∧
    x = round beta (FLX_exp prec) (Znearest choice) x * (1 + eps) := by
  sorry

/-- FLX relative error nearest round -/
theorem relative_error_N_FLX_round (x : Float) :
  Float.abs (round beta (FLX_exp prec) (Znearest choice) x - x) ≤ 
    (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) * 
    Float.abs (round beta (FLX_exp prec) (Znearest choice) x) := by
  sorry

-- Section: FLT relative error

variable (emin : Int)

/-- FLT relative error auxiliary -/
lemma relative_error_FLT_aux (k : Int) (h_bound : emin + prec - 1 < k) : 
  prec ≤ k - FLT_exp emin prec k := by
  sorry

/-- FLT relative error -/
theorem relative_error_FLT (rnd : Float → Int) [Valid_rnd rnd] (x : Float)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs (emin + prec - 1) : Nat) ≤ Float.abs x) :
  Float.abs (round beta (FLT_exp emin prec) rnd x - x) < 
    (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) * Float.abs x := by
  sorry

/-- FLT relative error F2R emin -/
theorem relative_error_FLT_F2R_emin (rnd : Float → Int) [Valid_rnd rnd] (m : Int)
  (h_nonzero : F2R (FlocqFloat.mk m emin : FlocqFloat beta) ≠ 0) :
  Float.abs (round beta (FLT_exp emin prec) rnd (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) - 
    F2R (FlocqFloat.mk m emin : FlocqFloat beta)) < 
    (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) * 
    Float.abs (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) := by
  sorry

/-- FLT relative error F2R emin existence -/
theorem relative_error_FLT_F2R_emin_ex (rnd : Float → Int) [Valid_rnd rnd] (m : Int) :
  ∃ eps, Float.abs eps < (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    round beta (FLT_exp emin prec) rnd (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) = 
    F2R (FlocqFloat.mk m emin : FlocqFloat beta) * (1 + eps) := by
  sorry

/-- FLT relative error existence -/
theorem relative_error_FLT_ex (rnd : Float → Int) [Valid_rnd rnd] (x : Float)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs (emin + prec - 1) : Nat) ≤ Float.abs x) :
  ∃ eps, Float.abs eps < (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    round beta (FLT_exp emin prec) rnd x = x * (1 + eps) := by
  sorry

/-- FLT relative error nearest -/
theorem relative_error_N_FLT (x : Float)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs (emin + prec - 1) : Nat) ≤ Float.abs x) :
  Float.abs (round beta (FLT_exp emin prec) (Znearest choice) x - x) ≤ 
    (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) * Float.abs x := by
  sorry

/-- FLT relative error nearest existence -/
theorem relative_error_N_FLT_ex (x : Float)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs (emin + prec - 1) : Nat) ≤ Float.abs x) :
  ∃ eps, Float.abs eps ≤ (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) := by
  sorry

/-- FLT relative error nearest round -/
theorem relative_error_N_FLT_round (x : Float)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs (emin + prec - 1) : Nat) ≤ Float.abs x) :
  Float.abs (round beta (FLT_exp emin prec) (Znearest choice) x - x) ≤ 
    (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) * 
    Float.abs (round beta (FLT_exp emin prec) (Znearest choice) x) := by
  sorry

/-- FLT relative error nearest F2R emin -/
theorem relative_error_N_FLT_F2R_emin (m : Int) :
  Float.abs (round beta (FLT_exp emin prec) (Znearest choice) (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) - 
    F2R (FlocqFloat.mk m emin : FlocqFloat beta)) ≤ 
    (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) * 
    Float.abs (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) := by
  sorry

/-- FLT relative error nearest F2R emin existence -/
theorem relative_error_N_FLT_F2R_emin_ex (m : Int) :
  ∃ eps, Float.abs eps ≤ (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    round beta (FLT_exp emin prec) (Znearest choice) (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) = 
    F2R (FlocqFloat.mk m emin : FlocqFloat beta) * (1 + eps) := by
  sorry

/-- FLT relative error nearest round F2R emin -/
theorem relative_error_N_FLT_round_F2R_emin (m : Int) :
  Float.abs (round beta (FLT_exp emin prec) (Znearest choice) (F2R (FlocqFloat.mk m emin : FlocqFloat beta)) - 
    F2R (FlocqFloat.mk m emin : FlocqFloat beta)) ≤ 
    (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) * 
    Float.abs (round beta (FLT_exp emin prec) (Znearest choice) (F2R (FlocqFloat.mk m emin : FlocqFloat beta))) := by
  sorry

/-- FLT error nearest auxiliary -/
lemma error_N_FLT_aux (x : Float) (h_pos : 0 < x) :
  ∃ eps eta, Float.abs eps ≤ (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    Float.abs eta ≤ (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs emin : Nat) ∧
    eps * eta = 0 ∧
    round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  sorry

/-- FLT relative error nearest alternative existence -/
theorem relative_error_N_FLT'_ex (x : Float) :
  ∃ eps eta, Float.abs eps ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
    Float.abs eta ≤ (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs emin : Nat) ∧
    eps * eta = 0 ∧
    round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  sorry

/-- FLT relative error nearest alternative separate -/
theorem relative_error_N_FLT'_ex_separate (x : Float) :
  ∃ x', round beta (FLT_exp emin prec) (Znearest choice) x' = 
    round beta (FLT_exp emin prec) (Znearest choice) x ∧
    (∃ eta, Float.abs eta ≤ (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs emin : Nat) ∧ x' = x + eta) ∧
    (∃ eps, Float.abs eps ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
      round beta (FLT_exp emin prec) (Znearest choice) x' = x' * (1 + eps)) := by
  sorry

/-- General FLT error nearest -/
theorem error_N_FLT (emin prec : Int) (h_pos : 0 < prec) (choice : Int → Bool) (x : Float) :
  ∃ eps eta, Float.abs eps ≤ (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs (-prec + 1) : Nat) ∧
    Float.abs eta ≤ (1/2) * (Int.natAbs beta : Float) ^ (Int.natAbs emin : Nat) ∧
    eps * eta = 0 ∧
    round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  sorry