/-!
Copyright (c) 2025 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh

Linter that warns about trivial Hoare triples:
- preconditions that are not `True` (prefer explicit hypotheses)
- postconditions that are `True` (trivial spec)
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Parser.Syntax
public meta import Lean.Linter.Basic
public meta import Std.Do.PostCond
public meta import Std.Do.SPred.Notation
public meta import Std.Do.Triple.Basic

public meta section

namespace FloatSpec.Linter
open Lean Elab Command Linter
open scoped Std.Do

/-- Enables the Hoare-style linter. -/
register_option linter.hoareStyle : Bool := {
  defValue := true
  descr := "warn on non-True Hoare preconditions and trivial postconditions"
}

namespace HoareStyle

/-- Gets the value of the linter.hoareStyle option. -/
def getLinterHoareStyle (o : LinterOptions) : Bool :=
  getLinterValue linter.hoareStyle o

private def isTrueAssertion (stx : Syntax) : Bool :=
  match stx with
  | `(term| True) => true
  | `(term| ⌜True⌝) => true
  | _ => false

private def isTrivialPost (stx : Syntax) : Bool :=
  match stx with
  | `(term| ⇓ $_* => ⌜True⌝) => true
  | `(term| ⇓ $_* => True) => true
  | `(term| ⇓? $_* => ⌜True⌝) => true
  | `(term| ⇓? $_* => True) => true
  | _ => false

/-- Recursively find Hoare triples in a syntax tree. -/
partial def findHoareTriples (stx : Syntax) (acc : List (Syntax × Syntax)) :
    List (Syntax × Syntax) :=
  if let `(term| ⦃$P⦄ $_prog ⦃$Q⦄) := stx then
    let acc' := (P.raw, Q.raw) :: acc
    match stx with
    | .node _ _ args => args.foldl (fun a s => findHoareTriples s a) acc'
    | _ => acc'
  else
    match stx with
    | .node _ _ args => args.foldl (fun a s => findHoareTriples s a) acc
    | _ => acc

/-- The Hoare-style linter. -/
def hoareStyleLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterHoareStyle (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return

  for (pre, post) in findHoareTriples stx [] do
    unless isTrueAssertion pre do
      logLint linter.hoareStyle pre
        "prefer `⦃⌜True⌝⦄` preconditions for mvcgen specs; move assumptions to explicit hypotheses. \
         Disable with `set_option linter.hoareStyle false`."
    if isTrivialPost post then
      logLint linter.hoareStyle post
        "postcondition is `True`; this Hoare triple is trivial. \
         Prefer a plain lemma or strengthen the spec. \
         Disable with `set_option linter.hoareStyle false`."

initialize addLinter hoareStyleLinter

end HoareStyle
end FloatSpec.Linter
