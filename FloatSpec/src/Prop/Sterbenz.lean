-- Sterbenz conditions for exact subtraction
-- Translated from Coq file: flocq/src/Prop/Sterbenz.v

import FloatSpec.src.Core

variable (beta : Int)
variable (fexp : Int → Int)
variable [Valid_exp fexp]
variable [Monotone_exp fexp]

/-- Generic format plus exact under magnitude condition -/
theorem generic_format_plus (x y : Float)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) 
  (h_bound : Float.abs (x + y) ≤ (Int.natAbs beta : Float) ^ (Int.natAbs (min (mag beta x) (mag beta y)) : Nat)) :
  generic_format beta fexp (x + y) := by
  sorry

/-- Generic format plus weak condition -/
theorem generic_format_plus_weak (x y : Float)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_bound : Float.abs (x + y) ≤ min (Float.abs x) (Float.abs y)) :
  generic_format beta fexp (x + y) := by
  sorry

/-- Sterbenz auxiliary lemma -/
lemma sterbenz_aux (x y : Float)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_bound : y ≤ x ∧ x ≤ 2 * y) :
  generic_format beta fexp (x - y) := by
  sorry

/-- Sterbenz theorem for exact subtraction -/
theorem sterbenz (x y : Float)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_bound : y / 2 ≤ x ∧ x ≤ 2 * y) :
  generic_format beta fexp (x - y) := by
  sorry