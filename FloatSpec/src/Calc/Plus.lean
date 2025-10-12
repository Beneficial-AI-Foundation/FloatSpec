/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Helper function and theorem for computing the rounded sum of two floating-point numbers
Translated from Coq file: flocq/src/Calc/Plus.v
-/

import FloatSpec.src.Core
import FloatSpec.src.Calc.Bracket
import FloatSpec.src.Calc.Operations
import FloatSpec.src.Calc.Round
import FloatSpec.src.Core.Digits
import FloatSpec.src.Core.Generic_fmt
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real FloatSpec.Calc.Bracket FloatSpec.Core.Digits FloatSpec.Core.Defs FloatSpec.Core.Generic_fmt
open FloatSpec.Core.Generic_fmt
open Std.Do

namespace FloatSpec.Calc.Plus

variable (beta : Int)
variable (fexp : Int → Int)

section CoreAddition

/-- Core addition function with precision control

    Performs addition with specified target exponent and location tracking
-/
def Fplus_core (m1 e1 m2 e2 e : Int) : Id (Int × Location) :=
  pure (
    let k := e - e2
    let (m2', _, l) :=
      if 0 < k then
        Round.truncate_aux (m2, e2, Location.loc_Exact) k
      else
        (m2 * beta ^ Int.natAbs (-k), e, Location.loc_Exact)
    let m1' := m1 * beta ^ Int.natAbs (e1 - e)
    (m1' + m2', l))

/-- Specification: Core addition correctness

    The core addition accurately represents the sum with location information
-/
theorem Fplus_core_correct (m1 e1 m2 e2 e : Int) (He1 : e ≤ e1) :
    ⦃⌜e ≤ e1⌝⦄
    Fplus_core beta m1 e1 m2 e2 e
    ⦃⇓result => let (m, l) := result
                ⌜inbetween_float beta m e
                  ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run +
                   (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run) l⌝⦄ := by
  sorry

end CoreAddition

section MainAddition

/-- Main addition function

    Adds two floats with intelligent exponent selection for precision
-/
def Fplus (f1 f2 : FlocqFloat beta) : Id (Int × Int × Location) :=
  let m1 := f1.Fnum
  let e1 := f1.Fexp
  let m2 := f2.Fnum
  let e2 := f2.Fexp
  if m1 = 0 then
    pure (m2, e2, Location.loc_Exact)
  else if m2 = 0 then
    pure (m1, e1, Location.loc_Exact)
  else
    Zdigits beta m1 >>= fun d1 =>
    Zdigits beta m2 >>= fun d2 =>
    let p1 := d1 + e1
    let p2 := d2 + e2
    if 2 ≤ Int.natAbs (p1 - p2) then
      let e := min (max e1 e2) (fexp (max p1 p2 - 1))
      Fplus_core beta (if e1 < e then m2 else m1)
                      (if e1 < e then e2 else e1)
                      (if e1 < e then m1 else m2)
                      (if e1 < e then e1 else e2) e >>= fun (m, l) =>
      pure (m, e, l)
    else
      let result_m := m1 * beta ^ Int.natAbs (e1 - min e1 e2) +
                     m2 * beta ^ Int.natAbs (e2 - min e1 e2)
      pure (result_m, min e1 e2, Location.loc_Exact)

/-- Specification: Addition correctness

    The addition result accurately represents the sum with proper location
-/
theorem Fplus_correct (x y : FlocqFloat beta) :
    ⦃⌜True⌝⦄
    Fplus beta fexp x y
    ⦃⇓result => let (m, e, l) := result
                ⌜l = Location.loc_Exact ∨
                 e ≤ (cexp beta fexp ((F2R x).run + (F2R y).run)).run ∧
                inbetween_float beta m e ((F2R x).run + (F2R y).run) l⌝⦄ := by
  sorry

end MainAddition

end FloatSpec.Calc.Plus
