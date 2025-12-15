# Coq Reference Annotation Guide

## Overview

This guide describes how to annotate Coq/Flocq references in FloatSpec docstrings using Verso roles.

## Required Import

Add to files containing Coq references:

```lean
import FloatSpec.VersoExt
```

## Annotation Pattern

### Before (unannnotated)

```lean
/-- Coq (FLX.v):
Theorem `ulp_FLX_0`: `ulp beta FLX_exp 0 = 0`.

Lean (spec): In FLX, `negligible_exp` is `none`, so `ulp` at zero is `0`.
-/
```

### After (annotated)

```lean
/-- Coq ({lit}`FLX.v`):
Theorem {coq}`ulp_FLX_0`: {lit}`ulp beta FLX_exp 0 = 0`.

Lean (spec): In FLX, {lean}`negligible_exp` is {lit}`none`, so {lean}`ulp` at zero is 0.
-/
```

## Role Selection Guide

| Content Type | Role | Example |
|--------------|------|---------|
| Coq file name | `{lit}` | `{lit}\`FLX.v\`` |
| Coq theorem/lemma name | `{coq}` | `{coq}\`ulp_FLX_0\`` |
| Coq code snippet | `{lit}` | `{lit}\`forall x, ...\`` |
| Lean function reference | `{lean}` | `{lean}\`negligible_exp\`` |
| Lean type reference | `{lean}` or `{name}` | `{lean}\`Option Int\`` |
| Mathematical notation | `{lit}` | `{lit}\`β^(-prec)\`` |
| Plain text values | no backticks | `0`, `none` |

## Files to Annotate

Priority order (by Coq reference density):

1. ✅ `FIX.lean` - Done
2. ✅ `FLX.lean` - Partially done (4 docstrings annotated)
3. `FLT.lean` - ~20 Coq references
4. `FTZ.lean` - ~10 Coq references
5. `Generic_fmt.lean` - ~100+ Coq references (largest file)
6. `Ulp.lean` - ~80 Coq references
7. `Raux.lean` - ~20 Coq references

## Annotation Process

1. Add `import FloatSpec.VersoExt` to the file
2. Find docstrings with `Coq (*.v):` patterns
3. Apply roles:
   - File names: `{lit}`
   - Coq theorem names: `{coq}`
   - Coq code: `{lit}`
   - Lean references: `{lean}`
4. Verify with LSP: `lean_diagnostic_messages`
5. Commit changes

## Block Comments vs Docstrings

- **Docstrings** (`/-- ... -/`): Can use roles, will get hover
- **Block comments** (`/- ... -/`): Cannot use roles (plain comments)

Only annotate docstrings. Block comments can be converted to docstrings if hover is desired.

## Hover Result

When hovering over `{coq}\`ulp_FLX_0\``, users see:

```
**Coq (Flocq):** `ulp_FLX_0`

Module: `Flocq.Core.Ulp`

[View in Flocq documentation](https://flocq.gitlabpages.inria.fr/html/Flocq.Core.Ulp.html#ulp_FLX_0)
```

## Notes

- The `{coq}` role auto-infers Flocq module URLs from declaration names
- Use `{coq url="..."}` for explicit URLs when auto-inference fails
- Avoid backticks in plain prose to prevent "code element could be more specific" warnings
