import Lake
open Lake DSL

/-- Main FloatSpec package -/
package FloatSpec where
  -- Lean options (typechecked!)
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩,
    ⟨`linter.unnecessarySimpa, false⟩,
    -- Allow work-in-progress files that use `sorry` to compile
    ⟨`warningAsError, false⟩,
    ⟨`doc.verso, true⟩
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

/-- Verso roles - imports VersoCoq.Roles to register {coq} doc role.

    Must compile BEFORE main library due to @[doc_role] attribute timing.
-/
lean_lib FloatSpecRoles where
  globs := #[.one `FloatSpecRoles]

/-- Main library -/
@[default_target]
lean_lib FloatSpecLib where
  -- Include the root module and all submodules
  globs := #[.submodules `FloatSpec.src, .one `FloatSpec]


/-- Executables -/
lean_exe floatspec where
  root := `Main

-- lean_exe floatspecmanual where
--   root := `FloatSpec.ManualMain
