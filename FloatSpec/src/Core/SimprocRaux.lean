import Lean
import Mathlib.Algebra.Order.Floor.Ring
import FloatSpec.src.Core.Raux
import Std.Do.Triple

open Lean Meta Simp
open Std.Do
open FloatSpec.Core.Raux

private def getNegArg? (e : Expr) : Option Expr :=
  if e.getAppFn.isConstOf ``Neg.neg then
    e.getAppArgs.back?
  else
    none

private def getAbsArg? (e : Expr) : Option Expr :=
  if e.getAppFn.isConstOf ``abs then
    e.getAppArgs.back?
  else
    none

private def getIntCastArg? (e : Expr) : Option Expr :=
  if e.getAppFn.isConstOf ``Int.cast then
    e.getAppArgs.back?
  else
    none

private theorem Ztrunc_int_val (z : Int) : Ztrunc (z : ℝ) = z := by
  unfold Ztrunc
  by_cases h : (z : ℝ) < 0
  · simp [h, Int.ceil_intCast]
  · simp [h, Int.floor_intCast]

private theorem Zfloor_int_val (z : Int) : Zfloor (z : ℝ) = z := by
  unfold Zfloor
  simp [Int.floor_intCast]

private theorem Zceil_int_val (z : Int) : Zceil (z : ℝ) = z := by
  unfold Zceil
  simp [Int.ceil_intCast]

private theorem Ztrunc_neg_val (x : ℝ) :
    Ztrunc (-x) = (-((Ztrunc x)) : Int) := by
  unfold Ztrunc
  by_cases hx : x < 0
  · have hneg : ¬ -x < 0 := by
      have : (0 : ℝ) ≤ -x := by exact le_of_lt (neg_pos.mpr hx)
      exact not_lt.mpr this
    -- Ztrunc(-x) = floor(-x) and Ztrunc(x) = ceil(x)
    simp [hx, hneg, Int.floor_neg]
  · have hx' : 0 ≤ x := (not_lt.mp hx)
    by_cases hneg : -x < 0
    · -- x > 0, so Ztrunc(-x) = ceil(-x) = -floor(x)
      simp [hx, hneg, Int.ceil_neg]
    · -- x = 0
      have hx0 : x = 0 := by
        have hneg' : 0 ≤ -x := (not_lt.mp hneg)
        have hx_le : x ≤ 0 := (neg_nonneg).1 hneg'
        exact le_antisymm hx_le hx'
      simp [hx0]

private theorem mag_neg_eq (beta : Int) (x : ℝ) : mag beta (-x) = mag beta x := by
  simp [mag, abs_neg]

private theorem mag_abs_eq (beta : Int) (x : ℝ) : mag beta (abs x) = mag beta x := by
  simp [mag, abs_abs]

@[simp] theorem mag_bpow_run (beta e : Int) (hβ : 1 < beta) :
    (mag beta ((beta : ℝ) ^ e)) = e + 1 := by
  have hspec := (mag_bpow (beta := beta) (e := e) hβ) (by trivial)
  simpa [wp, PostCond.noThrow, Id.run, pure] using hspec

/-- Definitional simproc: simplify truncation on integer-coerced inputs. -/
simproc [simp] reduceZtruncInt (Ztrunc _) := fun e => do
  unless e.isAppOfArity ``Ztrunc 1 do
    return .continue
  let arg := e.appArg!
  let some z := getIntCastArg? arg | return .continue
  let expr := z
  let proof := mkApp (mkConst ``Ztrunc_int_val) z
  return .done { expr := expr, proof? := some proof }

/-- Simplify floor on integer-coerced inputs. -/
simproc [simp] reduceZfloorInt (Zfloor _) := fun e => do
  unless e.isAppOfArity ``Zfloor 1 do
    return .continue
  let arg := e.appArg!
  let some z := getIntCastArg? arg | return .continue
  let expr := z
  let proof := mkApp (mkConst ``Zfloor_int_val) z
  return .done { expr := expr, proof? := some proof }

/-- Simplify ceil on integer-coerced inputs. -/
simproc [simp] reduceZceilInt (Zceil _) := fun e => do
  unless e.isAppOfArity ``Zceil 1 do
    return .continue
  let arg := e.appArg!
  let some z := getIntCastArg? arg | return .continue
  let expr := z
  let proof := mkApp (mkConst ``Zceil_int_val) z
  return .done { expr := expr, proof? := some proof }

/-- Simplify truncation under negation. -/
simproc [simp] reduceZtruncNeg (Ztrunc _) := fun e => do
  unless e.isAppOfArity ``Ztrunc 1 do
    return .continue
  let arg := e.appArg!
  let some x := getNegArg? arg | return .continue
  let expr := mkApp (mkConst ``Neg.neg) (mkApp (mkConst ``Ztrunc) x)
  let proof := mkApp (mkConst ``Ztrunc_neg_val) x
  return .done { expr := expr, proof? := some proof }

/-- Simplify magnitude under negation. -/
simproc [simp] reduceMagNeg (mag _ _) := fun e => do
  unless e.isAppOfArity ``mag 2 do
    return .continue
  let args := e.getAppArgs
  let beta := args[0]!
  let arg := args[1]!
  let some x := getNegArg? arg | return .continue
  let expr := mkApp2 (mkConst ``mag) beta x
  let proof := mkApp2 (mkConst ``mag_neg_eq) beta x
  return .done { expr := expr, proof? := some proof }

/-- Simplify magnitude under absolute value. -/
simproc [simp] reduceMagAbs (mag _ _) := fun e => do
  unless e.isAppOfArity ``mag 2 do
    return .continue
  let args := e.getAppArgs
  let beta := args[0]!
  let arg := args[1]!
  let some x := getAbsArg? arg | return .continue
  let expr := mkApp2 (mkConst ``mag) beta x
  let proof := mkApp2 (mkConst ``mag_abs_eq) beta x
  return .done { expr := expr, proof? := some proof }
