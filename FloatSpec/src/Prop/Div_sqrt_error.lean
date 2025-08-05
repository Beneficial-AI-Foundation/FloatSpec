-- Remainder of the division and square root are in the FLX format
-- Translated from Coq file: flocq/src/Prop/Div_sqrt_error.v

import FloatSpec.src.Core
import FloatSpec.src.Prop.Relative
import FloatSpec.src.Prop.Sterbenz
import FloatSpec.src.Prop.Mult_error

variable (beta : Int)
variable (prec : Int)
variable [Prec_gt_0 prec]

/-- Generic format plus with precision bound -/
lemma generic_format_plus_prec (fexp : Int → Int) 
  (h_bound : ∀ e, fexp e ≤ e - prec)
  (x y : Float) (fx fy : FlocqFloat beta)
  (hx : x = F2R fx) (hy : y = F2R fy)
  (h1 : Float.abs (x + y) < (Int.natAbs beta : Float) ^ (Int.natAbs (prec + fx.Fexp) : Nat))
  (h2 : Float.abs (x + y) < (Int.natAbs beta : Float) ^ (Int.natAbs (prec + fy.Fexp) : Nat)) :
  generic_format beta fexp (x + y) := by
  sorry

variable (choice : Int → Bool)

/-- Remainder of the division in FLX -/
theorem div_error_FLX (rnd : Float → Int) [Valid_rnd rnd] (x y : Float)
  (hx : generic_format beta (FLX_exp prec) x) (hy : generic_format beta (FLX_exp prec) y) :
  generic_format beta (FLX_exp prec) (x - round beta (FLX_exp prec) rnd (x / y) * y) := by
  sorry

/-- Square root error in FLX -/
theorem sqrt_error_FLX (rnd : Float → Int) [Valid_rnd rnd] (x : Float)
  (hx : generic_format beta (FLX_exp prec) x) :
  generic_format beta (FLX_exp prec) (x - (round beta (FLX_exp prec) rnd (Float.sqrt x))^2) := by
  sorry

/-- Division error in FLT -/
theorem div_error_FLT (emin : Int) (rnd : Float → Int) [Valid_rnd rnd] (x y : Float)
  (hx : generic_format beta (FLT_exp emin prec) x) (hy : generic_format beta (FLT_exp emin prec) y)
  (h_no_underflow : (Int.natAbs beta : Float) ^ (Int.natAbs (emin + 2 * prec - 1) : Nat) ≤ Float.abs (x / y)) :
  generic_format beta (FLT_exp emin prec) (x - round beta (FLT_exp emin prec) rnd (x / y) * y) := by
  sorry

/-- Square root error in FLT -/
theorem sqrt_error_FLT (emin : Int) (rnd : Float → Int) [Valid_rnd rnd] (x : Float)
  (hx : generic_format beta (FLT_exp emin prec) x)
  (h_no_underflow : (Int.natAbs beta : Float) ^ (Int.natAbs (emin + 2 * prec - 1) : Nat) ≤ Float.abs (Float.sqrt x)) :
  generic_format beta (FLT_exp emin prec) (x - (round beta (FLT_exp emin prec) rnd (Float.sqrt x))^2) := by
  sorry