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
