/-!
Copyright (c) 2025 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh

Linter that warns when `def`/`abbrev` returns `Id _`.
Use `Id` only in Hoare triples (mvcgen) and keep definitions pure.
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Parser.Syntax
public meta import Lean.Linter.Basic

public meta section

namespace FloatSpec.Linter
open Lean Elab Command Linter

/-- Enables the no-Id-return linter. -/
register_option linter.noIdReturn : Bool := {
  defValue := true
  descr := "warn when a def/abbrev returns Id; keep Id only in mvcgen specs"
}

namespace NoIdReturn

/-- Gets the value of the linter.noIdReturn option. -/
def getLinterNoIdReturn (o : LinterOptions) : Bool :=
  getLinterValue linter.noIdReturn o

private def isIdName (n : Name) : Bool :=
  n == `Id || n == `Std.Id

/-- Check whether a syntax tree contains the identifier {lean}`Id`. -/
partial def containsId (stx : Syntax) : Bool :=
  match stx with
  | .ident _ _ n _ => isIdName n
  | .node _ _ args => args.any containsId
  | _ => false

/-- Find return-type syntax nodes containing {lean}`Id` in defs/abbrevs. -/
partial def findIdReturnTypes (stx : Syntax) (acc : List Syntax) : List Syntax :=
  if let `(command| def $_:ident $_* : $ty := $_) := stx then
    let acc' := if containsId ty.raw then ty.raw :: acc else acc
    acc'
  else if let `(command| abbrev $_:ident $_* : $ty := $_) := stx then
    let acc' := if containsId ty.raw then ty.raw :: acc else acc
    acc'
  else
    match stx with
    | .node _ _ args => args.foldl (fun a s => findIdReturnTypes s a) acc
    | _ => acc

/-- The no-Id-return linter. -/
def noIdReturnLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterNoIdReturn (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return

  for ty in findIdReturnTypes stx [] do
    logLint linter.noIdReturn ty
      "avoid returning `Id` from `def`/`abbrev`. \
       Keep definitions pure and use `(pure ...) : Id _` only inside mvcgen Hoare triples. \
       Disable with `set_option linter.noIdReturn false`."

initialize addLinter noIdReturnLinter

end NoIdReturn
end FloatSpec.Linter
