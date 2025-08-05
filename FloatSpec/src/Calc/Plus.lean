-- Helper function and theorem for computing the rounded sum of two floating-point numbers
-- Translated from Coq file: flocq/src/Calc/Plus.v

import FloatSpec.src.Core
import FloatSpec.src.Calc.Bracket
import FloatSpec.src.Calc.Operations
import FloatSpec.src.Calc.Round

variable (beta : Int)
variable (fexp : Int → Int)
variable [Monotone_exp fexp]

-- Core addition function with precision control
def Fplus_core (m1 e1 m2 e2 e : Int) : Int × Location :=
  let k := e - e2
  let (m2', _, l) := 
    if 0 < k then truncate_aux beta (m2, e2, Location.loc_Exact) k
    else (m2 * beta ^ (-k), e, Location.loc_Exact)
  let m1' := m1 * beta ^ (e1 - e)
  (m1' + m2', l)

-- Correctness of core addition
theorem Fplus_core_correct (m1 e1 m2 e2 e : Int) (He1 : e ≤ e1) :
    let (m, l) := Fplus_core beta m1 e1 m2 e2 e
    inbetween_float beta m e (F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) + F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)) l := by
  sorry

-- Main addition function
def Fplus (f1 f2 : FlocqFloat beta) : Int × Int × Location :=
  let m1 := f1.Fnum
  let e1 := f1.Fexp
  let m2 := f2.Fnum
  let e2 := f2.Fexp
  if m1 = 0 then
    (m2, e2, Location.loc_Exact)
  else if m2 = 0 then
    (m1, e1, Location.loc_Exact)
  else
    let p1 := Zdigits beta m1 + e1
    let p2 := Zdigits beta m2 + e2
    if 2 ≤ Int.natAbs (p1 - p2) then
      let e := min (max e1 e2) (fexp (max p1 p2 - 1))
      let (m, l) := 
        if e1 < e then
          Fplus_core beta m2 e2 m1 e1 e
        else
          Fplus_core beta m1 e1 m2 e2 e
      (m, e, l)
    else
      let (m, e) := Operations.Fplus beta f1 f2
      (m.Fnum, m.Fexp, Location.loc_Exact)

-- Correctness of addition
theorem Fplus_correct (x y : FlocqFloat beta) :
    let (m, e, l) := Fplus beta fexp x y
    (l = Location.loc_Exact ∨ e ≤ cexp beta fexp (F2R x + F2R y)) ∧
    inbetween_float beta m e (F2R x + F2R y) l := by
  sorry