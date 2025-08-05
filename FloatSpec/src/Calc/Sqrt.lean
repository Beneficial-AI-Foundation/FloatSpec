-- Helper functions and theorems for computing the rounded square root of a floating-point number
-- Translated from Coq file: flocq/src/Calc/Sqrt.v

import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Digits
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Float_prop
import FloatSpec.src.Calc.Bracket

variable (beta : Int)
variable (fexp : Int → Int)

-- Magnitude of square root of F2R
lemma mag_sqrt_F2R (m1 e1 : Int) (Hm1 : 0 < m1) :
    mag beta (Float.sqrt (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta))) = (Zdigits beta m1 + e1 + 1) / 2 := by
  sorry

-- Core square root function
def Fsqrt_core (m1 e1 e : Int) : Int × Location :=
  let d1 := Zdigits beta m1
  let m1' := m1 * beta ^ (e1 - 2 * e)
  let (q, r) := Int.sqrtRem m1'
  let l := if r = 0 then Location.loc_Exact
           else Location.loc_Inexact (if r ≤ q then Ordering.lt else Ordering.gt)
  (q, l)

-- Correctness of core square root
theorem Fsqrt_core_correct (m1 e1 e : Int) (Hm1 : 0 < m1) (He : 2 * e ≤ e1) :
    let (m, l) := Fsqrt_core beta m1 e1 e
    inbetween_float beta m e (Float.sqrt (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta))) l := by
  sorry

-- Main square root function
def Fsqrt (x : FlocqFloat beta) : Int × Int × Location :=
  let m1 := x.Fnum
  let e1 := x.Fexp
  let e' := Zdigits beta m1 + e1 + 1
  let e := min (fexp (e' / 2)) (e1 / 2)
  let (m, l) := Fsqrt_core beta m1 e1 e
  (m, e, l)

-- Correctness of square root
theorem Fsqrt_correct (x : FlocqFloat beta) (Hx : 0 < F2R x) :
    let (m, e, l) := Fsqrt beta fexp x
    e ≤ cexp beta fexp (Float.sqrt (F2R x)) ∧
    inbetween_float beta m e (Float.sqrt (F2R x)) l := by
  sorry