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

/-- Main library -/
@[default_target]
lean_lib FloatSpecLib where
  -- Include the root module and all submodules
  globs := #[.andSubmodules `FloatSpec]

/-- Verso extensions for FloatSpec documentation -/
lean_lib VersoExt where
  roots := #[`FloatSpec.VersoExt]


/-- Executables -/
lean_exe floatspec where
  root := `Main

-- lean_exe floatspecmanual where
--   root := `FloatSpec.ManualMain
