/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Helper function and theorem for computing the rounded sum of two floating-point numbers
Translated from Coq file: flocq/src/Calc/Plus.v
-/

import FloatSpec.src.Core
import FloatSpec.src.Calc.Bracket
-- Note: avoid importing Operations here to reduce dependencies for building this module
import FloatSpec.src.Calc.Round
import FloatSpec.src.Core.Digits
import FloatSpec.src.Core.Generic_fmt
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do
import FloatSpec.src.SimprocWP

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
noncomputable def Fplus_core (m1 e1 m2 e2 e : Int) : (Int × Location) :=
  let k := e - e2
  let t :=
    if 0 < k then
      FloatSpec.Calc.Round.truncate_aux beta (m2, e2, Location.loc_Exact) k
    else
      (m2 * beta ^ Int.natAbs (-k), e, Location.loc_Exact)
  let m2' := t.1
  let l := t.2.2
  let m1' := m1 * beta ^ Int.natAbs (e1 - e)
  (m1' + m2', l)

/-- Scaffold marker for core addition correctness.

    The executable `Fplus_core` now follows the upstream truncation structure.
    The full semantic inbetween theorem is not ported here; this theorem is
    intentionally only a computational marker rather than a correctness
    claim.
-/
theorem Fplus_core_correct (m1 e1 m2 e2 e : Int) (He1 : e ≤ e1) :
    ⦃⌜1 < beta ∧ e ≤ e1 ∧ e ≤ e2⌝⦄
    (pure (Fplus_core beta m1 e1 m2 e2 e) : Id (Int × Location))
    ⦃⇓result => ⌜result = Fplus_core beta m1 e1 m2 e2 e⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure]

end CoreAddition

section MainAddition

/-- Main addition function

    Adds two floats with intelligent exponent selection for precision.
    This follows the Coq Flocq implementation structure.
-/
noncomputable def Fplus (f1 f2 : FlocqFloat beta) : (Int × Int × Location) :=
  let m1 := f1.Fnum
  let e1 := f1.Fexp
  let m2 := f2.Fnum
  let e2 := f2.Fexp
  if m1 = 0 then
    (m2, e2, Location.loc_Exact)
  else if m2 = 0 then
    (m1, e1, Location.loc_Exact)
  else
    -- Evaluate digit counts
    let d1 := Zdigits beta m1
    let d2 := Zdigits beta m2
    let p1 := d1 + e1
    let p2 := d2 + e2
    if 2 ≤ Int.natAbs (p1 - p2) then
      let e := min (max e1 e2) (fexp (max p1 p2 - 1))
      let (m, l) :=
        if e1 < e then
          Fplus_core beta m2 e2 m1 e1 e
        else
          Fplus_core beta m1 e1 m2 e2 e
      (m, e, l)
    else
      -- When |p1 - p2| < 2, compute exact sum at minimum exponent
      let e_min := min e1 e2
      let result_m := m1 * beta ^ Int.natAbs (e1 - e_min) +
                      m2 * beta ^ Int.natAbs (e2 - e_min)
      (result_m, e_min, Location.loc_Exact)

/-- The semantic obligation that remains for the upstream `Fplus_correct` port. -/
def Fplus_correct_obligation (x y : FlocqFloat beta) : Prop :=
  let result := Fplus beta fexp x y
  let m := result.1
  let e := result.2.1
  let l := result.2.2
  (l = Location.loc_Exact ∨ e ≤ cexp beta fexp ((F2R x) + (F2R y))) ∧
    inbetween_float beta m e ((F2R x) + (F2R y)) l

/-- Blocked marker for addition correctness.

    The old proof closed by showing `Fplus` always returned `loc_Exact`.
    `Fplus_core` now uses real truncation, so that argument is gone.  The
    inbetween proof is still an explicit obligation (`Fplus_correct_obligation`)
    rather than a correctness theorem.
-/
theorem Fplus_correct (x y : FlocqFloat beta) :
    ⦃⌜True⌝⦄
    (pure (Fplus beta fexp x y) : Id (Int × Int × Location))
    ⦃⇓result => ⌜result = Fplus beta fexp x y⌝⦄ := by
  intro _
  simp [wp, PostCond.noThrow, pure]

end MainAddition

end FloatSpec.Calc.Plus
