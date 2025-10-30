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

/-- If `x` is not exactly an integer (`Zfloor x`), then the result of
    rounding-to-odd (`Zodd x`) is odd. This mirrors Coq's `Zrnd_odd_Zodd`. -/
lemma Zrnd_odd_Zodd (x : ℝ)
  (hx : x ≠ (((FloatSpec.Core.Raux.Zfloor x).run : Int) : ℝ)) :
  (Zodd x) % 2 = 1 := by
  sorry

/-- Integer floor of a translated real: `Zfloor (n + y) = n + Zfloor y`. -/
lemma Zfloor_plus (n : Int) (y : ℝ) :
  (FloatSpec.Core.Raux.Zfloor ((n : ℝ) + y)).run =
    n + (FloatSpec.Core.Raux.Zfloor y).run := by
  sorry

/-- Integer ceil of a translated real: `Zceil (n + y) = n + Zceil y`. -/
lemma Zceil_plus (n : Int) (y : ℝ) :
  (FloatSpec.Core.Raux.Zceil ((n : ℝ) + y)).run =
    n + (FloatSpec.Core.Raux.Zceil y).run := by
  sorry

/-- Parity is invariant by absolute value: `(abs z)` is even iff `z` is even.
    Coq counterpart: `Zeven_abs`. -/
lemma Zeven_abs (z : Int) :
  ((Int.ofNat (Int.natAbs z)) % 2 = 0) ↔ (z % 2 = 0) := by
  sorry

/-- Sum with round-to-odd at an even integer point.
    Coq counterpart: `Zrnd_odd_plus`. -/
lemma Zrnd_odd_plus (x y : ℝ)
  (hx : x = (((FloatSpec.Core.Raux.Zfloor x).run : Int) : ℝ))
  (heven : ((FloatSpec.Core.Raux.Zfloor x).run : Int) % 2 = 0) :
  ((Zodd (x + y) : Int) : ℝ) = x + ((Zodd y : Int) : ℝ) := by
  sorry

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
