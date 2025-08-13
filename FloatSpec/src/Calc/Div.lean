/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Helper function and theorem for computing the rounded quotient of two floating-point numbers
Translated from Coq file: flocq/src/Calc/Div.v
-/

import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Round_generic
import FloatSpec.src.Core.Float_prop
import FloatSpec.src.Core.Digits
import FloatSpec.src.Calc.Bracket
import Mathlib.Data.Real.Basic
import Std.Do.Triple
import Std.Tactic.Do

open Real FloatSpec.Calc.Bracket FloatSpec.Core.Defs FloatSpec.Core.Digits FloatSpec.Core.Generic_fmt
open FloatSpec.Core.Round_generic
open Std.Do

namespace FloatSpec.Calc.Div

variable (beta : Int)
variable (fexp : Int → Int)

section MagnitudeBounds

/-- Compute magnitude bound for division

    Calculates the exponent range for the quotient of two floats
-/
def mag_div_F2R_compute (m1 e1 m2 e2 : Int) : Id Int :=
  Zdigits beta m1 >>= fun d1 =>
  Zdigits beta m2 >>= fun d2 =>
  pure ((d1 + e1) - (d2 + e2))

/-- Specification: Division magnitude bounds

    The magnitude of a quotient is bounded by the difference of magnitudes
-/
lemma mag_div_F2R (m1 e1 m2 e2 : Int) (Hm1 : 0 < m1) (Hm2 : 0 < m2) :
    ⦃⌜0 < m1 ∧ 0 < m2⌝⦄
    mag_div_F2R_compute beta m1 e1 m2 e2
    ⦃⇓e => e ≤ mag beta ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run /
                        (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run) ∧
           mag beta ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run /
                    (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run) ≤ e + 1⦄ := by
  sorry

end MagnitudeBounds

section CoreDivision

/-- Core division function with precision control

    Performs division by adjusting mantissas to achieve desired exponent
-/
def Fdiv_core (m1 e1 m2 e2 e : Int) : Id (Int × Location) :=
  pure (
    let (m1', m2') :=
      if e ≤ e1 - e2 then
        (m1 * beta ^ Int.natAbs (e1 - e2 - e), m2)
      else
        (m1, m2 * beta ^ Int.natAbs (e - (e1 - e2)))
    let q := m1' / m2'
    let r := m1' % m2'
    (q, if r = 0 then Location.loc_Exact else Location.loc_Inexact Ordering.lt))

/-- Specification: Core division correctness

    The computed quotient with location accurately represents the division
-/
theorem Fdiv_core_correct (m1 e1 m2 e2 e : Int) (Hm1 : 0 < m1) (Hm2 : 0 < m2) :
    ⦃⌜0 < m1 ∧ 0 < m2⌝⦄
    Fdiv_core beta m1 e1 m2 e2 e
    ⦃⇓result => let (m, l) := result
                inbetween_float beta m e
                  ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run /
                   (F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)).run) l⦄ := by
  sorry

end CoreDivision

section MainDivision

/-- Main division function

    Computes the quotient of two floats with automatic exponent selection
-/
def Fdiv (x y : FlocqFloat beta) : Id (Int × Int × Location) :=
  let m1 := x.Fnum
  let e1 := x.Fexp
  let m2 := y.Fnum
  let e2 := y.Fexp
  Zdigits beta m1 >>= fun d1 =>
  Zdigits beta m2 >>= fun d2 =>
  let e' := (d1 + e1) - (d2 + e2)
  let e := min (min (fexp e') (fexp (e' + 1))) (e1 - e2)
  Fdiv_core beta m1 e1 m2 e2 e >>= fun (m, l) =>
  pure (m, e, l)

/-- Specification: Division correctness

    The division result accurately represents the quotient with proper location
-/
theorem Fdiv_correct (x y : FlocqFloat beta)
    (Hx : 0 < (F2R x).run) (Hy : 0 < (F2R y).run) :
    ⦃⌜0 < (F2R x).run ∧ 0 < (F2R y).run⌝⦄
    Fdiv beta fexp x y
    ⦃⇓result => let (m, e, l) := result
                e ≤ (cexp beta fexp ((F2R x).run / (F2R y).run)).run ∧
                inbetween_float beta m e ((F2R x).run / (F2R y).run) l⦄ := by
  sorry

end MainDivision

end FloatSpec.Calc.Div
