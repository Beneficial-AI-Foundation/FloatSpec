/-
Copyright (c) 2025 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh

Linter that warns when `simp only` is used and suggests using `simp` instead.
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Parser.Syntax
public meta import Lean.Linter.Basic

public meta section

namespace FloatSpec.Linter
open Lean Elab Command Linter

/-- Enables the prefer-simp-over-simp-only linter. -/
register_option linter.preferSimp : Bool := {
  defValue := true
  descr := "enable the 'prefer simp over simp only' linter"
}

namespace PreferSimp

/-- Gets the value of the linter.preferSimp option. -/
def getLinterPreferSimp (o : LinterOptions) : Bool :=
  getLinterValue linter.preferSimp o

/-- Check if a syntax kind is a simp-related tactic. -/
def kindIsSimpTactic (k : SyntaxNodeKind) : Bool :=
  let kstr := k.toString
  -- Match common simp tactic kinds
  kstr.endsWith ".simp" || kstr.endsWith ".simp_all" ||
  kstr.endsWith "Parser.Tactic.simp" || kstr.endsWith "Parser.Tactic.simpAll" ||
  kstr == "simp" || kstr == "simp_all" ||
  kstr.endsWith "Tactic.simp" || kstr.endsWith "Tactic.simpAll"

/-- Check if syntax array contains the "only" modifier. -/
def hasOnlyModifier (args : Array Syntax) : Bool :=
  args.any fun arg =>
    match arg with
    | .atom _ val => val == "only"
    | .ident _ _ n _ => n == `only
    | .node _ k children =>
      -- Also check for only inside config nodes
      children.any fun c =>
        match c with
        | .atom _ val => val == "only"
        | .ident _ _ n _ => n == `only
        | _ => false
    | _ => false

/-- Recursively find all simp only usages in a syntax tree. -/
partial def findSimpOnlyUsages (stx : Syntax) (acc : List Syntax) : List Syntax :=
  match stx with
  | .node _info k args =>
    let acc' := if kindIsSimpTactic k && hasOnlyModifier args then stx :: acc else acc
    args.foldl (fun a s => findSimpOnlyUsages s a) acc'
  | _ => acc

/-- The prefer simp linter. -/
def preferSimpLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterPreferSimp (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return

  for simpOnly in findSimpOnlyUsages stx [] do
    logLint linter.preferSimp simpOnly
      "consider using `simp` instead of `simp only`. \
       Plain `simp` is more maintainable as the simp set evolves. \
       If you need precise control, you can suppress this warning with \
       `set_option linter.preferSimp false`."

initialize addLinter preferSimpLinter

end PreferSimp
end FloatSpec.Linter
