-- Remainder of the division and square root are in the FLX format
-- Translated from Coq file: flocq/src/Prop/Div_sqrt_error.v

import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import FloatSpec.src.Prop.Relative
import FloatSpec.src.Prop.Sterbenz
import FloatSpec.src.Prop.Mult_error
import Mathlib.Data.Real.Basic

open Real

variable (beta : Int)
variable (prec : Int)
variable [Prec_gt_0 prec]

/-- Generic format plus with precision bound -/
lemma generic_format_plus_prec (fexp : Int → Int) 
  (h_bound : ∀ e, fexp e ≤ e - prec)
  (x y : ℝ) (fx fy : FloatSpec.Core.Defs.FlocqFloat beta)
  (hx : x = _root_.F2R fx) (hy : y = _root_.F2R fy)
  (h1 : |x + y| < (Int.natAbs beta : ℝ) ^ (Int.natAbs (prec + fx.Fexp) : Nat))
  (h2 : |x + y| < (Int.natAbs beta : ℝ) ^ (Int.natAbs (prec + fy.Fexp) : Nat)) :
  generic_format beta fexp (x + y) := by
  sorry

variable (choice : Int → Bool)

/-- Remainder of the division in FLX -/
theorem div_error_FLX (rnd : ℝ → Int) [Valid_rnd rnd] (x y : ℝ)
  (hx : generic_format beta (FLX_exp prec) x) (hy : generic_format beta (FLX_exp prec) y) :
  generic_format beta (FLX_exp prec) (x - FloatSpec.Calc.Round.round beta (FLX_exp prec) () (x / y) * y) := by
  sorry

/-- Square root error in FLX -/
theorem sqrt_error_FLX (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ)
  (hx : generic_format beta (FLX_exp prec) x) :
  generic_format beta (FLX_exp prec) (x - (FloatSpec.Calc.Round.round beta (FLX_exp prec) () (Real.sqrt x))^2) := by
  sorry

/-- Remainder of the square in FLX (with p > 1) and rounding to nearest -/
theorem sqrt_error_FLX_N (h_gt1 : 1 < prec) (x : ℝ)
  (hx : generic_format beta (FLX_exp prec) x) :
  generic_format beta (FLX_exp prec)
    (x - (FloatSpec.Calc.Round.round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x))^2) := by
  sorry

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
variable [Monotone_exp fexp]

/-- Auxiliary remainder formatting under generic exponent function. -/
theorem format_REM_aux
  (rnd : ℝ → Int) [Valid_rnd rnd]
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
  (rnd : ℝ → Int) [Valid_rnd rnd]
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
theorem div_error_FLT (emin : Int) (rnd : ℝ → Int) [Valid_rnd rnd] (x y : ℝ)
  (hx : generic_format beta (FLT_exp emin prec) x) (hy : generic_format beta (FLT_exp emin prec) y)
  (h_no_underflow : (Int.natAbs beta : ℝ) ^ (Int.natAbs (emin + 2 * prec - 1) : Nat) ≤ |x / y|) :
  generic_format beta (FLT_exp emin prec) (x - FloatSpec.Calc.Round.round beta (FLT_exp emin prec) () (x / y) * y) := by
  sorry

/-- Square root error in FLT -/
theorem sqrt_error_FLT (emin : Int) (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (h_no_underflow : (Int.natAbs beta : ℝ) ^ (Int.natAbs (emin + 2 * prec - 1) : Nat) ≤ |Real.sqrt x|) :
  generic_format beta (FLT_exp emin prec) (x - (FloatSpec.Calc.Round.round beta (FLT_exp emin prec) () (Real.sqrt x))^2) := by
  sorry
