-- Round to odd properties
-- Translated from Coq file: flocq/src/Prop/Round_odd.v

import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc.Round
import Mathlib.Data.Real.Basic

open Real
open FloatSpec.Calc.Round

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

/-- Round to odd rounding mode -/
noncomputable def Zodd : ℝ → Int := fun x =>
  let n := Ztrunc x
  if n % 2 = 0 then
    if x = (n : ℝ) then n else n + 1
  else n

/-- Round to odd is a valid rounding -/
instance : Valid_rnd (Zodd) := by sorry

/-- Round to odd properties -/
theorem round_odd_ge_ulp (x : ℝ) :
  generic_format beta fexp x ∨ 
  ulp beta fexp x ≤ |FloatSpec.Calc.Round.round beta fexp () x - x| := by
  sorry

/-- Round to odd for double rounding -/
theorem round_odd_double_round (fexp1 fexp2 : Int → Int)
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp1]
  [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp2]
  (choice : Int → Bool) (x : ℝ)
  (h_precision : ∀ e, fexp2 e ≤ fexp1 e) :
  FloatSpec.Calc.Round.round beta fexp2 (Znearest choice) (FloatSpec.Calc.Round.round beta fexp1 () x) = 
  FloatSpec.Calc.Round.round beta fexp2 (Znearest choice) x := by
  sorry

/-- Round to odd maintains format when appropriate -/
theorem generic_format_round_odd (x : ℝ) :
  generic_format beta fexp (FloatSpec.Calc.Round.round beta fexp () x) := by
  sorry
