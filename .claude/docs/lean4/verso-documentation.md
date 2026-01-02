# Verso Documentation System

## Overview

Verso is Lean 4's native documentation system. It provides:
- **Typed documentation** - Code in docs is actually typechecked
- **Goto-definition** - Navigate to definitions from doc code blocks
- **Extensible roles and directives** - Custom syntax for domain-specific docs
- **Multiple genres** - Textbooks, API docs, websites, blogs

Reference: https://github.com/leanprover/verso/

## Setup

### Enable in lakefile.lean

Add to your package options:

```lean
package MyPackage where
  leanOptions := #[
    ⟨`doc.verso, true⟩
  ]
```

### Add Dependency

```lean
require verso from git "https://github.com/leanprover/verso" @ "v4.27.0-rc1"
```

## Roles

Roles annotate inline code elements in docstrings:

### Built-in Roles

| Role | Purpose | Example |
|------|---------|---------|
| `{lean}` | Lean code reference | `{lean}\`myFunction\`` |
| `{name}` | Reference by name | `{name}\`MyType\`` |
| `{lit}` | Literal text (no checking) | `{lit}\`pseudo-code\`` |
| `{syntax term}` | Syntax reference | `{syntax term}\`match\`` |

### FloatSpec Custom Role: {coq}

The `{coq}` role marks Coq/Flocq code references with hover documentation:

```lean
import FloatSpec.VersoExt

/-- Coq ({lit}`FIX.v`): Theorem {coq}`round_FIX_IZR` -/
```

**Features:**
- **Hover docs**: Shows Coq decl name, Flocq module, and documentation link
- **Auto-inference**: Infers Flocq URLs from declaration names
- **Optional URL**: `{coq url="https://..."}\`myFunc\``

**Auto-inferred modules:**
| Prefix | Module |
|--------|--------|
| `Ztrunc`, `Zceil`, `Zfloor` | Core.Raux |
| `Znearest`, `Zrnd`, `generic_*`, `round_*` | Core.Generic_fmt |
| `ulp`, `succ`, `pred` | Core.Ulp |
| `FIX_*`, `FLX_*`, `FLT_*`, `FTZ_*` | Respective modules |
| `bpow` | Core.Defs |
| `Z*` (fallback) | Core.Zaux |

### Custom Roles

Define custom roles with `@[role name]`:

```lean
import Verso
import Verso.Doc.Elab

open Verso ArgParse Doc Elab
open Lean Elab
open Lean.Doc.Syntax

/-- Role for Coq code references -/
@[role coq]
def coq : RoleExpanderOf Unit
  | (), #[arg] => do
    let `(inline|code( $code:str )) := arg
      | throwErrorAt arg "Expected code literal"
    ``(Inline.code $(quote code.getString))
  | (), _ => throwError "Expected a single code element"
```

### Role with Arguments

```lean
structure MyRoleArgs where
  url? : Option String := none

instance : FromArgs MyRoleArgs DocElabM where
  fromArgs := MyRoleArgs.mk <$> (some <$> .positional `url .string <|> pure none)

@[role myRole]
def myRole : RoleExpanderOf MyRoleArgs
  | args, #[arg] => do
    let `(inline|code( $code:str )) := arg
      | throwErrorAt arg "Expected code literal"
    -- Use args.url? here
    ``(Inline.code $(quote code.getString))
  | _, _ => throwError "Expected a single code element"
```

## Directives

Block-level extensions use `@[directive]`:

```lean
@[directive]
def myBlock : DirectiveExpanderOf NoArgs
  | ⟨⟩, stxs => do
    let contents ← stxs.mapM elabBlock
    ``(Block.other MyBlockExt #[ $contents,* ])
```

## Genres

Verso supports different documentation genres:

- **Manual** - Reference documentation (VersoManual)
- **Blog** - Blog posts (VersoBlog)
- **Custom** - Create your own genre

### Starting a Custom Genre

See the [SimplePage example](https://github.com/leanprover/verso/tree/main/test-projects/custom-genre) in the Verso repo.

## Integration Features

### Goto Definition

Code in Verso docs is typechecked. In VS Code/Cursor:
- F12 or Ctrl+Click on code elements to go to definition
- Hover for type information
- When you annotate backticked code with the correct role (e.g. {lean}/{name}/{coq}),
  Lean's LSP can resolve it; agents can use hover/goto-definition here to reliably
  surface context without leaving the doc comment.

### Inline Extensions

Create custom inline elements:

```lean
inline_extension Inline.myInline (data : MyData) via withHighlighting where
  traverse := fun id data _ => pure none
  toHtml := some <| fun _ _ data _ => pure {{<span class="my-class">...</span>}}
```

### Block Extensions

Create custom block elements:

```lean
block_extension Block.myBlock where
  traverse := fun _ _ _ => pure none
  toHtml := some <| fun _ go _ _ content => do
    pure {{<div class="my-block">{{← content.mapM go}}</div>}}
```

## Code Element Warnings

If you see "Code element could be more specific", use an appropriate role:

- `{lean}` for Lean function/type references
- `{name}` for name references
- `{lit}` for literal text that shouldn't be checked
- `{coq}` (custom) for Coq code references

## Example Usage

In a docstring:

```lean
/-- Coq ({lit}`FIX.v`):
Theorem {coq}`round_FIX_IZR`: computes rounding for fixed-point.

Lean port uses {lean}`round_to_generic` with {lean}`FIX_exp`.
-/
theorem round_FIX_IZR : ... := ...
```

## Resources

- [Verso Repository](https://github.com/leanprover/verso)
- [Verso Templates](https://github.com/leanprover/verso-templates)
- [User's Guide](https://leanprover.github.io/verso/)
