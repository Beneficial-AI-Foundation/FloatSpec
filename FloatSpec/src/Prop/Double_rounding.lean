-- Double rounding properties
-- Translated from Coq file: flocq/src/Prop/Double_rounding.v

import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import FloatSpec.src.Core.Generic_fmt
import Mathlib.Data.Real.Basic

open Real

variable (beta : Int)

/-- Double rounding with two different precisions -/
theorem double_round_eq (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice1 choice2 : Int → Bool) (x : ℝ)
  (h_precision : ∀ e, fexp2 e ≤ fexp1 e) :
  FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) (FloatSpec.Calc.Round.round beta fexp1 (Znearest choice1) x) =
  FloatSpec.Calc.Round.round beta fexp2 (Znearest choice2) x := by
  sorry

/-- Double rounding property for FLX and FLT -/
theorem double_round_FLX_FLT (prec1 prec2 emin : Int) (choice1 choice2 : Int → Bool) (x : ℝ)
  (h_prec : prec2 ≤ prec1) :
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec2) (Znearest choice2)
    (FloatSpec.Calc.Round.round beta (FLX_exp prec1) (Znearest choice1) x) =
  FloatSpec.Calc.Round.round beta (FLT_exp emin prec2) (Znearest choice2) x := by
  sorry

/-- Double rounding for same format is identity -/
theorem double_round_same (fexp : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp] (choice : Int → Bool) (x : ℝ) :
  FloatSpec.Calc.Round.round beta fexp (Znearest choice) (FloatSpec.Calc.Round.round beta fexp (Znearest choice) x) =
  FloatSpec.Calc.Round.round beta fexp (Znearest choice) x := by
  sorry
