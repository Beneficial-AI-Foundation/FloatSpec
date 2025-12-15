/-
FloatSpec Verso Extensions

Custom roles and directives for FloatSpec documentation.
-/

import Verso
import Verso.Doc.Elab
import Verso.Hover

open Verso ArgParse Doc Elab Hover
open Lean Elab
open Lean.Doc.Syntax

namespace FloatSpec.VersoExt

/-- Base URL for Flocq documentation -/
def flocqBaseUrl : String := "https://flocq.gitlabpages.inria.fr/html/Flocq."

/-- Infer Flocq module from a Coq identifier name.

    Maps common Flocq declaration prefixes to their modules.
-/
def inferFlocqModule (declName : String) : Option String :=
  -- Common prefix -> module mappings (order matters - more specific first)
  let prefixMap := [
    ("FIX_", "Core.FIX"),
    ("FLX_", "Core.FLX"),
    ("FLT_", "Core.FLT"),
    ("FTZ_", "Core.FTZ"),
    ("Ztrunc", "Core.Raux"),
    ("Zceil", "Core.Raux"),
    ("Zfloor", "Core.Raux"),
    ("Znearest", "Core.Generic_fmt"),
    ("Zrnd", "Core.Generic_fmt"),
    ("ulp", "Core.Ulp"),
    ("succ", "Core.Ulp"),
    ("pred", "Core.Ulp"),
    ("generic_format", "Core.Generic_fmt"),
    ("generic_", "Core.Generic_fmt"),
    ("round_", "Core.Generic_fmt"),
    ("scaled_mantissa", "Core.Generic_fmt"),
    ("cexp", "Core.Generic_fmt"),
    ("bpow", "Core.Defs"),
    ("Rabs", "Core.Raux"),
    ("ln_beta", "Core.Raux"),
    ("mag", "Core.Raux"),
    ("Z", "Core.Zaux")
  ]
  -- Find first matching prefix
  prefixMap.find? (fun (p, _) => declName.startsWith p) |>.map (·.2)

/-- Infer Flocq doc URL from a Coq identifier name. -/
def inferFlocqUrl (declName : String) : Option String :=
  inferFlocqModule declName |>.map fun module =>
    s!"{flocqBaseUrl}{module}.html#{declName}"

/-- Arguments for the coq role -/
structure CoqArgs where
  /-- Optional explicit URL to Flocq documentation -/
  url? : Option String := none

instance : FromArgs CoqArgs DocElabM where
  fromArgs := CoqArgs.mk <$> (some <$> .positional `url .string <|> pure none)

/-- The coq role marks inline code as Coq syntax from Flocq.

    This is used to annotate Coq code references in documentation,
    particularly when discussing the original Flocq library that
    FloatSpec is ported from.

    Usage: coq role with backtick code, optionally with url argument.

    Hover documentation: Hovering shows the Coq declaration name and
    a link to the Flocq documentation (if URL is provided or inferred).

    Auto-inference: The role infers Flocq documentation URLs based on
    common naming conventions (Ztrunc -> Core.Raux, FIX -> Core.FIX, etc).
-/
@[role coq]
def coq : RoleExpanderOf CoqArgs
  | args, #[arg] => do
    let `(inline|code( $code:str )) := arg
      | throwErrorAt arg "Expected code literal with Coq code"
    let codeStr := code.getString
    -- Try explicit URL, then auto-infer
    let url? := args.url?.orElse fun () => inferFlocqUrl codeStr
    let module? := inferFlocqModule codeStr
    -- Build hover documentation
    let hoverText := match url?, module? with
      | some url, some mod =>
        s!"**Coq (Flocq):** `{codeStr}`\n\n" ++
        s!"Module: `Flocq.{mod}`\n\n" ++
        s!"[View in Flocq documentation]({url})"
      | some url, none =>
        s!"**Coq (Flocq):** `{codeStr}`\n\n" ++
        s!"[View documentation]({url})"
      | none, some mod =>
        s!"**Coq (Flocq):** `{codeStr}`\n\n" ++
        s!"Module: `Flocq.{mod}`"
      | none, none =>
        s!"**Coq:** `{codeStr}`"
    -- Add hover info
    addCustomHover arg (.markdown hoverText)
    -- Render as inline code
    ``(Inline.code $(quote codeStr))
  | _, _ => throwError "Expected a single code element"

end FloatSpec.VersoExt
