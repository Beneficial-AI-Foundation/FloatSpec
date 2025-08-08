-- Basic operations on floats: alignment, addition, multiplication
-- Translated from Coq file: flocq/src/Calc/Operations.v

import FloatSpec.src.Core.Zaux
import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Float_prop
import Mathlib.Data.Real.Basic

open Real

variable (beta : Int)

-- Float alignment operation
def Falign (f1 f2 : FlocqFloat beta) : Int × Int × Int :=
  let m1 := f1.Fnum
  let e1 := f1.Fexp
  let m2 := f2.Fnum
  let e2 := f2.Fexp
  if e1 ≤ e2 then
    (m1, m2 * beta ^ (e2 - e1), e1)
  else
    (m1 * beta ^ (e1 - e2), m2, e2)

-- Falign specification theorem
theorem Falign_spec (f1 f2 : FlocqFloat beta) :
    let (m1, m2, e) := Falign beta f1 f2
    F2R f1 = F2R (FlocqFloat.mk m1 e : FlocqFloat beta) ∧ 
    F2R f2 = F2R (FlocqFloat.mk m2 e : FlocqFloat beta) := by
  sorry

-- Falign exponent specification
theorem Falign_spec_exp (f1 f2 : FlocqFloat beta) :
    (Falign beta f1 f2).2.2 = min f1.Fexp f2.Fexp := by
  sorry

-- Float negation
def Fopp (f1 : FlocqFloat beta) : FlocqFloat beta :=
  FlocqFloat.mk (-f1.Fnum) f1.Fexp

-- F2R of negation theorem
theorem F2R_opp (f1 : FlocqFloat beta) :
    F2R (Fopp beta f1) = -(F2R f1) := by
  sorry

-- Float absolute value
def Fabs (f1 : FlocqFloat beta) : FlocqFloat beta :=
  FlocqFloat.mk (Int.natAbs f1.Fnum) f1.Fexp

-- F2R of absolute value theorem
theorem F2R_abs (f1 : FlocqFloat beta) :
    F2R (Fabs beta f1) = |F2R f1| := by
  sorry

-- Float addition
def Fplus (f1 f2 : FlocqFloat beta) : FlocqFloat beta :=
  let (m1, m2, e) := Falign beta f1 f2
  FlocqFloat.mk (m1 + m2) e

-- F2R of addition theorem
theorem F2R_plus (f1 f2 : FlocqFloat beta) :
    F2R (Fplus beta f1 f2) = F2R f1 + F2R f2 := by
  sorry

-- Addition with same exponent
theorem Fplus_same_exp (m1 m2 e : Int) :
    Fplus beta (FlocqFloat.mk m1 e) (FlocqFloat.mk m2 e) = FlocqFloat.mk (m1 + m2) e := by
  sorry

-- Exponent of addition
theorem Fexp_Fplus (f1 f2 : FlocqFloat beta) :
    (Fplus beta f1 f2).Fexp = min f1.Fexp f2.Fexp := by
  sorry

-- Float subtraction
def Fminus (f1 f2 : FlocqFloat beta) : FlocqFloat beta :=
  Fplus beta f1 (Fopp beta f2)

-- F2R of subtraction theorem
theorem F2R_minus (f1 f2 : FlocqFloat beta) :
    F2R (Fminus beta f1 f2) = F2R f1 - F2R f2 := by
  sorry

-- Subtraction with same exponent
theorem Fminus_same_exp (m1 m2 e : Int) :
    Fminus beta (FlocqFloat.mk m1 e) (FlocqFloat.mk m2 e) = FlocqFloat.mk (m1 - m2) e := by
  sorry

-- Float multiplication
def Fmult (f1 f2 : FlocqFloat beta) : FlocqFloat beta :=
  FlocqFloat.mk (f1.Fnum * f2.Fnum) (f1.Fexp + f2.Fexp)

-- F2R of multiplication theorem
theorem F2R_mult (f1 f2 : FlocqFloat beta) :
    F2R (Fmult beta f1 f2) = F2R f1 * F2R f2 := by
  sorry