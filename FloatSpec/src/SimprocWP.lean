import Lean
import Std.Do.Triple
import Std.Do.WP
import Std.Do.PredTrans
import Std.Do.PostCond

open Lean Meta Simp
open Std.Do

/-- Defeq simproc: unfold {name}`wp` for {name}`Id` programs. -/
dsimproc [simp] reduceWpId (_) := fun e => do
  unless e.isAppOfArity ``Std.Do.wp 1 do
    return .continue
  let x := e.appArg!
  let xTy ← inferType x
  let_expr Id _ := xTy | return .continue
  let run := mkApp (mkConst ``Id.run) x
  let expr ← mkAppM ``Std.Do.PredTrans.pure #[run]
  return .done expr

/-- Defeq simproc: reduce {name}`wp` on {name}`Id` + {name}`PostCond.noThrow` to the postcondition. -/
dsimproc [simp] reduceWpIdNoThrow (_) := fun e => do
  unless e.isAppOfArity ``Std.Do.wp 2 do
    return .continue
  let args := e.getAppArgs
  let x := args[0]!
  let pc := args[1]!
  unless pc.isAppOfArity ``Std.Do.PostCond.noThrow 1 do
    return .continue
  let xTy ← inferType x
  let_expr Id _ := xTy | return .continue
  let Q := pc.appArg!
  let run := mkApp (mkConst ``Id.run) x
  return .done (mkApp Q run)

/-- Defeq simproc: unfold {name}`PostCond.noThrow`. -/
dsimproc [simp] reducePostCondNoThrow (PostCond.noThrow _) := fun e => do
  unless e.isAppOfArity ``Std.Do.PostCond.noThrow 1 do
    return .continue
  let p := e.appArg!
  let falseExpr ← mkAppM ``Std.Do.ExceptConds.false #[]
  let falseTy ← inferType falseExpr
  let eTy ← inferType e
  let eTyWhnf ← whnf eTy
  match eTyWhnf with
  | Expr.app (Expr.app (Expr.const ``Prod _) _) beta =>
      unless (← isDefEq falseTy beta) do
        return .continue
      let expr ← mkAppM ``Prod.mk #[p, falseExpr]
      return .done expr
  | _ =>
      return .continue

/-- Defeq simproc: unfold {name}`Id.run`. -/
dsimproc [simp] reduceIdRun (Id.run _) := fun e => do
  unless e.isAppOfArity ``Id.run 1 do
    return .continue
  return .done e.appArg!

-- Demo: `simp` now reduces Id Hoare triples without unfolding `wp`/`PostCond.noThrow`.
example :
    ⦃⌜True⌝⦄
    (pure (α := Nat) 3 : Id Nat)
    ⦃⇓r => ⌜r = 3⌝⦄ := by
  intro _
  simp

/-- Simplify {name}`wp` on {name}`Id` computations to the postcondition. -/
@[simp] theorem wp_id (x : Id α) (Q : α → Assertion PostShape.pure) :
    wp⟦x⟧ (PostCond.noThrow Q) = Q (Id.run x) := by
  simp [wp, PostCond.noThrow, PredTrans.pure]

/-- {name}`Id.run` is definitional; keep it in simp to avoid stuck terms. -/
@[simp] theorem id_run (x : α) : Id.run x = x := rfl

/-- {name}`pure` for {name}`Id` is definitional; keep it in simp. -/
@[simp] theorem id_pure (x : α) : (pure x : Id α) = x := rfl

/-- {name}`bind` for {name}`Id` is definitional; keep it in simp. -/
@[simp] theorem id_bind (x : α) (f : α → Id β) : (x >>= f) = f x := rfl
