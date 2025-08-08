-- Round to odd properties
-- Translated from Coq file: flocq/src/Prop/Round_odd.v

import FloatSpec.src.Core

variable (beta : Int)
variable (fexp : Int → Int)
variable [Valid_exp fexp]

/-- Round to odd rounding mode -/
def Zodd : Float → Int := fun x =>
  let n := Ztrunc x in
  if n % 2 = 0 then
    if x = n then n else n + 1
  else n

/-- Round to odd is a valid rounding -/
instance : Valid_rnd (Zodd) := by sorry

/-- Round to odd properties -/
theorem round_odd_ge_ulp (x : Float) :
  generic_format beta fexp x ∨ 
  ulp beta fexp x ≤ Float.abs (round beta fexp Zodd x - x) := by
  sorry

/-- Round to odd for double rounding -/
theorem round_odd_double_round (fexp1 fexp2 : Int → Int) [Valid_exp fexp1] [Valid_exp fexp2]
  (choice : Int → Bool) (x : Float)
  (h_precision : ∀ e, fexp2 e ≤ fexp1 e) :
  round beta fexp2 (Znearest choice) (round beta fexp1 Zodd x) = 
  round beta fexp2 (Znearest choice) x := by
  sorry

/-- Round to odd maintains format when appropriate -/
theorem generic_format_round_odd (x : Float) :
  generic_format beta fexp (round beta fexp Zodd x) := by
  sorry