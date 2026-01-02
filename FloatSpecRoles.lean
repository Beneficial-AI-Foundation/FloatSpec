/-
FloatSpec - Docstring Role Registration

This module registers the {coq} documentation role for Flocq references.
It must be in a separate lean_lib that compiles BEFORE FloatSpecLib.
-/

import Lean.Elab.DocString
import VersoCoq.Flocq

open Lean Doc Elab
open scoped Lean.Doc.Syntax

/-- Extract the code content from inline syntax. -/
private def onlyCode {M : Type → Type} [Monad M] [MonadError M] (xs : TSyntaxArray `inline) : M StrLit := do
  if h : xs.size = 1 then
    match xs[0] with
    | `(inline|code($s)) => return s
    | other => throwErrorAt other "Expected code"
  else
    throwError "Expected precisely 1 code argument"

/-- Role for Coq/Flocq references with auto-linking.

    Usage in docstrings: the role followed by backtick-code renders
    as a hyperlink to Flocq documentation.
-/
@[doc_role]
def _root_.coq (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let txt := TSyntax.getString s
  match VersoCoq.Flocq.inferUrl txt with
  | some url => return .link #[.code txt] url
  | none => return .code txt

/-- Plain code block for non-Lean snippets in docstrings. -/
@[doc_code_block]
def _root_.raw (str : StrLit) : DocM (Block ElabInline ElabBlock) := do
  return .code str.getString
