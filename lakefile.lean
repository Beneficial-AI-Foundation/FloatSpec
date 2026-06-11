import Lake
open Lake DSL

/-- Main FloatSpec package -/
package FloatSpec where
  -- Lean options (typechecked!)
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, false⟩,
    ⟨`linter.unnecessarySimpa, false⟩,
    ⟨`linter.unusedSimpArgs, false⟩,
    ⟨`linter.unusedVariables, false⟩,
    ⟨`weak.linter.unusedTactic, false⟩,
    ⟨`weak.linter.unreachableTactic, false⟩,
    ⟨`weak.linter.unusedSectionVars, false⟩,
    ⟨`weak.linter.unnecessarySeqFocus, false⟩,
    -- Product builds reject proof hygiene warnings.
    ⟨`warningAsError, true⟩,
    ⟨`doc.verso, false⟩,
    -- Prefer-grind is a style lint, not proof hygiene.
    ⟨`weak.linter.preferGrind, false⟩,
    -- Keep style-only lint out of product proof hygiene enforcement.
    ⟨`weak.linter.preferSimp, false⟩,
    -- Avoid returning Id in definitions; keep Id only in mvcgen specs
    ⟨`weak.linter.noIdReturn, true⟩,
    -- Hoare-style normalization is useful during pipeline work but too noisy
    -- for product proof hygiene enforcement.
    ⟨`weak.linter.hoareStyle, false⟩
  ]
  -- Cloud release configuration for pre-built artifacts
  releaseRepo := "https://github.com/Beneficial-AI-Foundation/FloatSpec"
  buildArchive := "FloatSpec-{OS}-{ARCH}.tar.gz"
  preferReleaseBuild := true

/-! Dependencies (order matters for compilation) -/

-- Used for documentation generation
require verso from git "https://github.com/leanprover/verso" @ "v4.27.0-rc1"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.27.0-rc1"

-- Coq/Flocq documentation roles for literate programming
require VersoCoq from git "https://github.com/alok/VersoCoq" @ "main"

-- Canonical proof search tactic
require Canonical from git "https://github.com/chasenorman/CanonicalLean" @ "master"

require cslib from git "https://github.com/leanprover/cslib" @ "main"

/-- Linters for FloatSpec (prefer grind over omega, etc).
    Stdlib only, provides linter.preferGrind option.
-/
lean_lib FloatSpecLinter where
  globs := #[.andSubmodules `FloatSpec.Linter]

/-- Verso roles - imports VersoCoq.Roles to register {coq} doc role. -/
lean_lib FloatSpecRoles where
  globs := #[.one `FloatSpecRoles]

/-- Main library. -/
@[default_target]
lean_lib FloatSpecLib where
  globs := #[
    .one `FloatSpec,
    .one `FloatSpec.VersoExt,
    .one `FloatSpec.src,
    .one `FloatSpec.src.SimprocWP,
    .one `FloatSpec.src.ErrorBound,
    .one `FloatSpec.src.Compat,
    .andSubmodules `FloatSpec.src.Core,
    .andSubmodules `FloatSpec.src.Calc,
    .andSubmodules `FloatSpec.src.Prop,
    .andSubmodules `FloatSpec.src.Pff,
    .andSubmodules `FloatSpec.src.IEEE754
  ]
  needs := #[FloatSpecLinter, FloatSpecRoles]

/-- Lightweight property tests (Plausible) and smoke checks. -/
lean_lib FloatSpecTests where
  globs := #[.andSubmodules `FloatSpec.Test]
  needs := #[FloatSpecLib]

/-- Executables -/
lean_exe floatspec where
  root := `Main

-- lean_exe floatspecmanual where
--   root := `FloatSpec.ManualMain
