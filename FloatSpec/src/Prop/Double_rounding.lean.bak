-- Double rounding properties
-- Translated from Coq file: flocq/src/Prop/Double_rounding.v

import FloatSpec.src.Core

variable (beta : Int)

/-- Double rounding with two different precisions -/
theorem double_round_eq (fexp1 fexp2 : Int → Int) [Valid_exp fexp1] [Valid_exp fexp2]
  (choice1 choice2 : Int → Bool) (x : Float)
  (h_precision : ∀ e, fexp2 e ≤ fexp1 e) :
  round beta fexp2 (Znearest choice2) (round beta fexp1 (Znearest choice1) x) = 
  round beta fexp2 (Znearest choice2) x := by
  sorry

/-- Double rounding property for FLX and FLT -/
theorem double_round_FLX_FLT (prec1 prec2 emin : Int) (choice1 choice2 : Int → Bool) (x : Float)
  (h_prec : prec2 ≤ prec1) :
  round beta (FLT_exp emin prec2) (Znearest choice2) 
    (round beta (FLX_exp prec1) (Znearest choice1) x) = 
  round beta (FLT_exp emin prec2) (Znearest choice2) x := by
  sorry

/-- Double rounding for same format is identity -/
theorem double_round_same (fexp : Int → Int) [Valid_exp fexp] (choice : Int → Bool) (x : Float) :
  round beta fexp (Znearest choice) (round beta fexp (Znearest choice) x) = 
  round beta fexp (Znearest choice) x := by
  sorry