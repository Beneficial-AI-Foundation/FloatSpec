/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Helper functions and theorems for computing the rounded square root of a floating-point number
Translated from Coq file: flocq/src/Calc/Sqrt.v
-/

import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Digits
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Round_generic
import FloatSpec.src.Core.Float_prop
import FloatSpec.src.Calc.Bracket
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Std.Do.Triple
import Std.Tactic.Do

open Real FloatSpec.Calc.Bracket FloatSpec.Core.Defs FloatSpec.Core.Digits FloatSpec.Core.Generic_fmt
open FloatSpec.Core.Round_generic
open Std.Do

namespace FloatSpec.Calc.Sqrt

variable (beta : Int)
variable (fexp : Int → Int)

section MagnitudeBounds

/-- Compute magnitude of square root

    Calculates the magnitude of the square root of a float
-/
def mag_sqrt_F2R_compute (m1 e1 : Int) : Id Int :=
  Zdigits beta m1 >>= fun d =>
  pure ((d + e1 + 1) / 2)

/-- Specification: Square root magnitude

    The magnitude of a square root is approximately half the original magnitude
-/
lemma mag_sqrt_F2R (m1 e1 : Int) (Hm1 : 0 < m1) :
    ⦃⌜0 < m1⌝⦄
    mag_sqrt_F2R_compute beta m1 e1
    ⦃⇓result => ⌜result = mag beta (Real.sqrt ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run))⌝⦄ := by
  sorry

end MagnitudeBounds

section CoreSquareRoot

/-- Core square root function

    Computes integer square root with remainder for location determination
-/
def Fsqrt_core (m1 e1 e : Int) : Id (Int × Location) :=
  Zdigits beta m1 >>= fun d1 =>
  pure (
    let m1' := m1 * beta ^ Int.natAbs (e1 - 2 * e)
    let q := Int.sqrt m1'
    let r := m1' - q * q
    let l := if r = 0 then Location.loc_Exact
             else Location.loc_Inexact (if r ≤ q then Ordering.lt else Ordering.gt)
    (q, l))

/-- Specification: Core square root correctness

    The computed square root with location accurately represents the value
-/
theorem Fsqrt_core_correct (m1 e1 e : Int) (Hm1 : 0 < m1) (He : 2 * e ≤ e1) :
    ⦃⌜0 < m1 ∧ 2 * e ≤ e1⌝⦄
    Fsqrt_core beta m1 e1 e
    ⦃⇓result => let (m, l) := result
                ⌜inbetween_float beta m e
                  (Real.sqrt ((F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta)).run)) l⌝⦄ := by
  sorry

end CoreSquareRoot

section MainSquareRoot

/-- Main square root function

    Computes the square root with automatic exponent selection
-/
def Fsqrt (x : FlocqFloat beta) : Id (Int × Int × Location) :=
  let m1 := x.Fnum
  let e1 := x.Fexp
  Zdigits beta m1 >>= fun d =>
  let e' := d + e1 + 1
  let e := min (fexp (e' / 2)) (e1 / 2)
  Fsqrt_core beta m1 e1 e >>= fun (m, l) =>
  pure (m, e, l)

/-- Specification: Square root correctness

    The square root result accurately represents the value with proper location
-/
theorem Fsqrt_correct (x : FlocqFloat beta) (Hx : 0 < (F2R x).run) :
    ⦃⌜0 < (F2R x).run⌝⦄
    Fsqrt beta fexp x
    ⦃⇓result => let (m, e, l) := result
                ⌜e ≤ (cexp beta fexp (Real.sqrt ((F2R x).run))).run ∧
                inbetween_float beta m e (Real.sqrt ((F2R x).run)) l⌝⦄ := by
  sorry

end MainSquareRoot

end FloatSpec.Calc.Sqrt
