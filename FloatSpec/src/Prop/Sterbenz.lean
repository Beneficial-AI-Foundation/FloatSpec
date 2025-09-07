-- Sterbenz conditions for exact subtraction
-- Translated from Coq file: flocq/src/Prop/Sterbenz.v

import FloatSpec.src.Core
import FloatSpec.src.Compat
import Mathlib.Data.Real.Basic

open Real

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]
variable [Monotone_exp fexp]

/-- Generic format plus exact under magnitude condition -/
theorem generic_format_plus (x y : ℝ)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y) 
  (h_bound : |x + y| ≤ (Int.natAbs beta : ℝ) ^ (Int.natAbs (min (mag beta x) (mag beta y)) : Nat)) :
  generic_format beta fexp (x + y) := by
  sorry

/-- Generic format plus weak condition -/
theorem generic_format_plus_weak (x y : ℝ)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_bound : |x + y| ≤ min (|x|) (|y|)) :
  generic_format beta fexp (x + y) := by
  sorry

/-- Sterbenz auxiliary lemma -/
lemma sterbenz_aux (x y : ℝ)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_bound : y ≤ x ∧ x ≤ 2 * y) :
  generic_format beta fexp (x - y) := by
  sorry

/-- Sterbenz theorem for exact subtraction -/
theorem sterbenz (x y : ℝ)
  (hx : generic_format beta fexp x) (hy : generic_format beta fexp y)
  (h_bound : y / 2 ≤ x ∧ x ≤ 2 * y) :
  generic_format beta fexp (x - y) := by
  sorry
