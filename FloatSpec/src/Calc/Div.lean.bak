-- Helper function and theorem for computing the rounded quotient of two floating-point numbers
-- Translated from Coq file: flocq/src/Calc/Div.v

import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Float_prop
import FloatSpec.src.Core.Digits
import FloatSpec.src.Calc.Bracket

variable (beta : Int)
variable (fexp : Int → Int)

-- Magnitude bound for division of F2R values
lemma mag_div_F2R (m1 e1 m2 e2 : Int) (Hm1 : 0 < m1) (Hm2 : 0 < m2) :
    let e := (Zdigits beta m1 + e1) - (Zdigits beta m2 + e2)
    e ≤ mag beta (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) / F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)) ∧
    mag beta (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) / F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)) ≤ e + 1 := by
  sorry

-- Core division function with precision control
def Fdiv_core (m1 e1 m2 e2 e : Int) : Int × Location :=
  let (m1', m2') := 
    if e ≤ e1 - e2 then
      (m1 * beta ^ (e1 - e2 - e), m2)
    else
      (m1, m2 * beta ^ (e - (e1 - e2)))
  let (q, r) := Int.divMod m1' m2'
  (q, new_location m2' r Location.loc_Exact)

-- Correctness of core division
theorem Fdiv_core_correct (m1 e1 m2 e2 e : Int) (Hm1 : 0 < m1) (Hm2 : 0 < m2) :
    let (m, l) := Fdiv_core beta m1 e1 m2 e2 e
    inbetween_float beta m e (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) / F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)) l := by
  sorry

-- Main division function
def Fdiv (x y : FlocqFloat beta) : Int × Int × Location :=
  let m1 := x.Fnum
  let e1 := x.Fexp
  let m2 := y.Fnum
  let e2 := y.Fexp
  let e' := (Zdigits beta m1 + e1) - (Zdigits beta m2 + e2)
  let e := min (min (fexp e') (fexp (e' + 1))) (e1 - e2)
  let (m, l) := Fdiv_core beta m1 e1 m2 e2 e
  (m, e, l)

-- Correctness of division
theorem Fdiv_correct (x y : FlocqFloat beta) 
    (Hx : 0 < F2R x) (Hy : 0 < F2R y) :
    let (m, e, l) := Fdiv beta fexp x y
    e ≤ cexp beta fexp (F2R x / F2R y) ∧
    inbetween_float beta m e (F2R x / F2R y) l := by
  sorry