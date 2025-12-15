/-
FloatSpec Verso Extensions

Custom roles and directives for FloatSpec documentation.
-/

import Verso
import Verso.Doc.Elab

open Verso ArgParse Doc Elab
open Lean Elab
open Lean.Doc.Syntax

namespace FloatSpec.VersoExt

/-- Base URL for Flocq documentation -/
def flocqBaseUrl : String := "https://flocq.gitlabpages.inria.fr/html/Flocq."

/-- Infer Flocq doc URL from a Coq identifier name.

    Maps common Flocq module prefixes to their documentation URLs.
-/
def inferFlocqUrl (declName : String) : Option String :=
  -- Common prefix -> module mappings
  let prefixMap := [
    ("Z", "Core.Zaux"),
    ("FIX_", "Core.FIX"),
    ("FLX_", "Core.FLX"),
    ("FLT_", "Core.FLT"),
    ("FTZ_", "Core.FTZ"),
    ("ulp", "Core.Ulp"),
    ("generic_", "Core.Generic_fmt"),
    ("round", "Core.Round_pred"),
    ("bpow", "Core.Defs"),
    ("Rabs", "Core.Raux"),
    ("ln_beta", "Core.Raux"),
    ("mag", "Core.Raux")
  ]
  -- Find first matching prefix
  match prefixMap.find? (fun (p, _) => declName.startsWith p) with
  | some (_, module) => some s!"{flocqBaseUrl}{module}.html#{declName}"
  | none => none

/-- Arguments for the coq role -/
structure CoqArgs where
  /-- Optional explicit URL to Flocq documentation -/
  url? : Option String := none

instance : FromArgs CoqArgs DocElabM where
  fromArgs := CoqArgs.mk <$> (some <$> .positional `url .string <|> pure none)

/-- The coq role marks inline code as Coq syntax.

    This is used to annotate Coq code references in documentation,
    particularly when discussing the original Flocq library that
    FloatSpec is ported from.

    The role attempts to auto-infer Flocq documentation URLs based
    on common naming conventions. If no URL can be inferred, it
    renders as plain inline code.
-/
@[role coq]
def coq : RoleExpanderOf CoqArgs
  | args, #[arg] => do
    let `(inline|code( $code:str )) := arg
      | throwErrorAt arg "Expected code literal with Coq code"
    let codeStr := code.getString
    -- Try explicit URL, then auto-infer, then just render as code
    let _url? := args.url?.orElse fun () => inferFlocqUrl codeStr
    -- For now, just render as inline code
    -- Future: wrap in link if url? is some
    ``(Inline.code $(quote codeStr))
  | _, _ => throwError "Expected a single code element"

end FloatSpec.VersoExt
