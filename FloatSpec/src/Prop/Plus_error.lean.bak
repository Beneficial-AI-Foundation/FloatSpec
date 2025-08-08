-- Error of the rounded-to-nearest addition is representable
-- Translated from Coq file: flocq/src/Prop/Plus_error.v

import FloatSpec.src.Core
import FloatSpec.src.Prop.Relative

variable (beta : Int)
variable (fexp : Int → Int)
variable [Valid_exp fexp]

-- Section: Plus error representability

/-- Round representation with same exponent -/
theorem round_repr_same_exp (rnd : Float → Int) [Valid_rnd rnd] (m e : Int) :
  ∃ m', round beta fexp rnd (F2R (FlocqFloat.mk m e : FlocqFloat beta)) = 
        F2R (FlocqFloat.mk m' e : FlocqFloat beta) := by
  sorry

variable [Monotone_exp fexp]
variable (choice : Int → Bool)

/-- Plus error auxiliary lemma -/
lemma plus_error_aux (x y : Float) 
  (h_exp : cexp beta fexp x ≤ cexp beta fexp y)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  generic_format beta fexp (round beta fexp (Znearest choice) (x + y) - (x + y)) := by
  sorry

/-- Error of the addition -/
theorem plus_error (x y : Float)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  generic_format beta fexp (round beta fexp (Znearest choice) (x + y) - (x + y)) := by
  sorry

-- Section: Plus zero properties

variable [Exp_not_FTZ fexp]

/-- Round plus not equal to zero auxiliary -/
lemma round_plus_neq_0_aux (rnd : Float → Int) [Valid_rnd rnd] (x y : Float)
  (h_exp : cexp beta fexp x ≤ cexp beta fexp y)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_pos : 0 < x + y) :
  round beta fexp rnd (x + y) ≠ 0 := by
  sorry

/-- rnd(x+y)=0 → x+y ≠ 0 (provided this is not a FTZ format) -/
theorem round_plus_neq_0 (rnd : Float → Int) [Valid_rnd rnd] (x y : Float)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_nonzero : x + y ≠ 0) :
  round beta fexp rnd (x + y) ≠ 0 := by
  sorry

/-- rnd(x+y)=0 → x+y = 0 -/
theorem round_plus_eq_0 (rnd : Float → Int) [Valid_rnd rnd] (x y : Float)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_zero : round beta fexp rnd (x + y) = 0) :
  x + y = 0 := by
  sorry

-- Section: FLT format plus properties

variable (emin prec : Int)
variable [Prec_gt_0 prec]

/-- FLT format plus small -/
theorem FLT_format_plus_small (x y : Float)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (hy : generic_format beta (FLT_exp emin prec) y)
  (h_bound : Float.abs (x + y) ≤ (Int.natAbs beta : Float) ^ (Int.natAbs (prec + emin) : Nat)) :
  generic_format beta (FLT_exp emin prec) (x + y) := by
  sorry

/-- FLT plus error with nearest rounding existence -/
lemma FLT_plus_error_N_ex (x y : Float)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (hy : generic_format beta (FLT_exp emin prec) y) :
  ∃ eps, Float.abs eps ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
    round beta (FLT_exp emin prec) (Znearest choice) (x + y) = (x + y) * (1 + eps) := by
  sorry

/-- FLT plus error with round existence -/
lemma FLT_plus_error_N_round_ex (x y : Float)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (hy : generic_format beta (FLT_exp emin prec) y) :
  ∃ eps, Float.abs eps ≤ u_ro beta prec ∧
    x + y = round beta (FLT_exp emin prec) (Znearest choice) (x + y) * (1 + eps) := by
  sorry

-- Section: Plus mult ulp properties

variable (rnd : Float → Int)
variable [Valid_rnd rnd]

/-- Existence of shift representation -/
lemma ex_shift (x : Float) (e : Int) 
  (hx : generic_format beta fexp x) (h_exp : e ≤ cexp beta fexp x) :
  ∃ m : Int, x = (m : Float) * ((Int.natAbs beta : Float) ^ (Int.natAbs e : Nat)) := by
  sorry

/-- Magnitude minus one relation -/
lemma mag_minus1 (z : Float) (h_nonzero : z ≠ 0) :
  mag beta z - 1 = mag beta (z / (beta : Float)) := by
  sorry

/-- Round plus F2R representation -/
theorem round_plus_F2R (x y : Float) 
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) (h_nonzero : x ≠ 0) :
  ∃ m : Int, round beta fexp rnd (x + y) = 
    F2R (FlocqFloat.mk m (cexp beta fexp (x / (beta : Float))) : FlocqFloat beta) := by
  sorry

variable [Exp_not_FTZ fexp]

/-- Round plus greater equal ulp -/
theorem round_plus_ge_ulp (x y : Float)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_nonzero : round beta fexp rnd (x + y) ≠ 0) :
  ulp beta fexp (x / (beta : Float)) ≤ Float.abs (round beta fexp rnd (x + y)) := by
  sorry

-- Section: FLT plus bounds

/-- Round FLT plus greater equal bound -/
theorem round_FLT_plus_ge (x y : Float) (e : Int)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (hy : generic_format beta (FLT_exp emin prec) y)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs (e + prec) : Nat) ≤ Float.abs x)
  (h_nonzero : round beta (FLT_exp emin prec) rnd (x + y) ≠ 0) :
  (Int.natAbs beta : Float) ^ (Int.natAbs e : Nat) ≤ 
    Float.abs (round beta (FLT_exp emin prec) rnd (x + y)) := by
  sorry

/-- Round FLT plus greater equal bound (alternative) -/
lemma round_FLT_plus_ge' (x y : Float) (e : Int)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (hy : generic_format beta (FLT_exp emin prec) y)
  (h1 : x ≠ 0 → (Int.natAbs beta : Float) ^ (Int.natAbs (e + prec) : Nat) ≤ Float.abs x)
  (h2 : x = 0 → y ≠ 0 → (Int.natAbs beta : Float) ^ (Int.natAbs e : Nat) ≤ Float.abs y)
  (h_nonzero : round beta (FLT_exp emin prec) rnd (x + y) ≠ 0) :
  (Int.natAbs beta : Float) ^ (Int.natAbs e : Nat) ≤ 
    Float.abs (round beta (FLT_exp emin prec) rnd (x + y)) := by
  sorry

/-- Round FLX plus greater equal bound -/
theorem round_FLX_plus_ge (x y : Float) (e : Int)
  (hx : generic_format beta (FLX_exp prec) x)
  (hy : generic_format beta (FLX_exp prec) y)
  (h_bound : (Int.natAbs beta : Float) ^ (Int.natAbs (e + prec) : Nat) ≤ Float.abs x)
  (h_nonzero : round beta (FLX_exp prec) rnd (x + y) ≠ 0) :
  (Int.natAbs beta : Float) ^ (Int.natAbs e : Nat) ≤ 
    Float.abs (round beta (FLX_exp prec) rnd (x + y)) := by
  sorry

-- Section: Plus error bounds

/-- Plus error bounded by left operand -/
lemma plus_error_le_l (x y : Float)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  Float.abs (round beta fexp (Znearest choice) (x + y) - (x + y)) ≤ Float.abs x := by
  sorry

/-- Plus error bounded by right operand -/
lemma plus_error_le_r (x y : Float)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) :
  Float.abs (round beta fexp (Znearest choice) (x + y) - (x + y)) ≤ Float.abs y := by
  sorry