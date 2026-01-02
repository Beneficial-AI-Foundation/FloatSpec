/-
Copyright (c) 2025 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh

Linter that warns when omega is used and suggests grind instead.
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Parser.Syntax
public meta import Lean.Linter.Basic

public meta section

namespace FloatSpec.Linter
open Lean Elab Command Linter

/-- Enables the prefer-grind-over-omega linter. -/
register_option linter.preferGrind : Bool := {
  defValue := true
  descr := "enable the 'prefer grind over omega' linter"
}

namespace PreferGrind

/-- Gets the value of the linter.preferGrind option. -/
def getLinterPreferGrind (o : LinterOptions) : Bool :=
  getLinterValue linter.preferGrind o

/-- Check if a syntax kind name contains omega. -/
def kindContainsOmega (k : SyntaxNodeKind) : Bool :=
  let kstr := k.toString
  kstr.endsWith ".omega" || kstr == "omega" ||
  kstr.endsWith "Tactic.omega" || kstr.endsWith "Parser.Tactic.omega"

/-- Recursively find all omega tactic usages in a syntax tree. -/
partial def findOmegaUsages (stx : Syntax) (acc : List Syntax) : List Syntax :=
  match stx with
  | .node _ k args =>
    let acc' := if kindContainsOmega k then stx :: acc else acc
    args.foldl (fun a s => findOmegaUsages s a) acc'
  | .ident _ _ n _ =>
    if n == `omega then stx :: acc else acc
  | _ => acc

/-- The prefer grind linter. -/
def preferGrindLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterPreferGrind (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return

  for omega in findOmegaUsages stx [] do
    logLint linter.preferGrind omega
      "consider using `grind` instead of `omega`. \
       The `grind` tactic can solve integer arithmetic goals and more. \
       If `grind` fails, you can suppress this warning with \
       `set_option linter.preferGrind false`."

initialize addLinter preferGrindLinter

end PreferGrind
end FloatSpec.Linter
