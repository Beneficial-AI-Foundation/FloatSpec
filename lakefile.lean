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
  preferReleaseBuild := false

/-! Dependencies -/

require cslib from git "https://github.com/leanprover/cslib" @ "v4.34.0-rc2"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.0-rc2"

/-- Linters for FloatSpec (prefer grind over omega, etc).
    Stdlib only, provides linter.preferGrind option.
-/
lean_lib FloatSpecLinter where
  globs := #[.andSubmodules `FloatSpec.Linter]

/-- Stub for doc-role registration (Verso/VersoCoq removed in this fork). -/
lean_lib FloatSpecRoles where
  globs := #[.one `FloatSpecRoles]

/-- Main library. -/
@[default_target]
lean_lib FloatSpecLib where
  globs := #[.andSubmodules `FloatSpec.src, .one `FloatSpec, .one `FloatSpec.VersoExt]
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
