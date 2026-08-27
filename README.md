# FloatSpec

Formally verified floating‑point library for Lean 4, ported from the Coq Flocq project. FloatSpec aims to provide a clear, modular formalization of IEEE 754 style arithmetic together with executable reference functions and machine‑checked specifications/proofs.


## Purpose

- Provide a Lean 4 formalization of floating‑point arithmetic that mirrors the structure and guarantees of Flocq (by Boldo & Melquiond), while integrating with Lean 4 tooling and Mathlib.
- Offer executable “reference” operations (alignment, plus, minus, multiply, sqrt, etc.) alongside Hoare‑triple style specifications to steadily close the gap to full proofs.
- Serve as a foundation for reasoning about rounding, ulp, error bounds, and IEEE 754 encodings/decodings in Lean 4.


## Architecture

The library is organized into layered modules. The top‑level aggregator `FloatSpec.lean` re‑exports the submodules for convenience.

- Core (`FloatSpec/src/Core`)
  - Basic definitions and helpers: `Defs.lean`, `Zaux.lean`, `Raux.lean`, `Digits.lean`
  - Generic formats and rounding: `Generic_fmt.lean`, `Round_pred.lean`, `Round_NE.lean`, `Ulp.lean`, `FIX.lean`, `FLX.lean`, `FLT.lean`, `FTZ.lean`
- Calc (`FloatSpec/src/Calc`)
  - Executable reference operations with specifications: `Operations.lean` (align, plus, neg, abs, mult), `Sqrt.lean`, `Div.lean`, `Plus.lean`, `Round.lean`, and bracketing utilities `Bracket.lean`
- Prop (`FloatSpec/src/Prop`)
  - Error bounds and classical theorems about rounding: `Plus_error.lean`, `Div_sqrt_error.lean`, `Double_rounding.lean`, `Relative.lean`, `Round_odd.lean`, `Sterbenz.lean`
- ErrorBound (`FloatSpec/src/ErrorBound`)
  - VCFloat-style error-bound integration scaffold: `Types.lean`, `RExpr.lean`, `MakeRounding.lean`, `Absolute.lean`, `Compose.lean`, `Examples/FPBench.lean`
- IEEE754 (`FloatSpec/src/IEEE754`)
  - Encodings/decodings, bit‑level operations, and a structured IEEE 754 view: `Binary.lean`, `BinarySingleNaN.lean`, `Bits.lean`, and a bridge to primitive floats `PrimFloat.lean`
- Compat (`FloatSpec/src/Compat.lean`)
  - Thin compatibility bridges exposing selected core functions under simpler names/signatures
- Pff (`FloatSpec/src/Pff`)
  - Legacy compatibility modules and conversion helpers from an older floating‑point formalization

Project configuration lives in `lakefile.lean` and `lean-toolchain` (Lean 4
`v4.29.0`). Mathlib and CSLib are pinned to compatible `v4.29.0` revisions.


## Current Progress

The project is actively under development. The integrated library compiles
without active `sorry`, `admit`, or project axioms. This syntactic trust result
does not replace source-semantic review: translated declarations are checked
against the pinned Flocq source and compatibility helpers are kept distinct
from source-facing APIs.

- Build: compiles with Lean 4 and Mathlib `v4.29.0`, with warnings treated as errors.
- Trust gates: `scripts/audit_placeholders.sh` and
  `scripts/status_report.sh` check active Lean syntax; generated status is under
  `FloatSpec/docs/status.{md,json}`.
- Source contracts: regression modules under `FloatSpec/Test` cover important
  representation, rounding-mode, primitive-float, Pff, and IEEE correctness-name mappings.
- ErrorBound support: `FloatSpec/src/ErrorBound/**` contains the VCFloat-style
  error-bound layer.
- VCFloat integration plan and tasks live in `FloatSpec/docs/vcfloat_integration/ARCHITECTURE_AND_PLAN.md` and `FloatSpec/docs/vcfloat_integration/TODOs.md`.
- Status artifacts:
  - Progress PDF: `FloatSpec_status.pdf`
  - Detailed Core status: `FloatSpec/src/Core/Status.md`
- Examples of completed or near‑complete components:
  - Executable alignment, negation, absolute value, addition, and multiplication with Hoare‑triple specifications: `FloatSpec/src/Calc/Operations.lean`
  - Executable square root core and top‑level structure theorem: `FloatSpec/src/Calc/Sqrt.lean`
  - Foundational definitions and simple structural specs: `FloatSpec/src/Core/Defs.lean`

Version: the library exposes `FloatSpec.version = "0.7.0"` (see `FloatSpec.lean`).


## Quick Start

Prerequisites

- Lean 4 toolchain: `leanprover/lean4:v4.29.0` (see `lean-toolchain`)
- Lake build tool (included with the toolchain)

Build locally

1) Update dependencies: `lake update`
2) Build: `lake build`
3) Run trust gates: `scripts/audit_placeholders.sh --json FloatSpec`

Lean-level tests (smoke/property checks)

- Build and run the lightweight Plausible-based tests: `lake build FloatSpecTests`
- Or use the helper script: `./scripts/test_lean.sh`

REPL and usage

- In a Lean file, import the library root or a specific area:
  - `import FloatSpec` (re‑exports) or
  - `import FloatSpec.src.Calc.Operations`
  - `import FloatSpec.src.ErrorBound` (VCFloat‑style error‑bound scaffold)
- Example (informal sketch):
  - Use `FloatSpec.Core.Defs.F2R` to interpret `FlocqFloat` as a real number
  - Use `FloatSpec.Calc.Operations.Falign`/`Fplus` to add two floats, with specs `Falign_spec`/`F2R_plus`

Use as a dependency (Lake)

If you want to depend on this repository, add a line like the following to your project’s `lakefile.lean` (pin to a commit or tag that you control):

```
require FloatSpec from git "https://github.com/Beneficial-AI-Foundation/FloatSpec" @ "<commit-or-tag>"
```


## Proof Style and Workflow

The code uses a lightweight monadic specification style with Hoare‑triple syntax from `Std.Do.Triple`. A concise playbook for developing proofs lives in `PIPELINE.md`.

- Preferred pattern: reduce executable specs to pure facts using small helper equalities, then discharge via `unfold`/`simp`/`calc`.
- Bool/Prop conversions: use `decide` when the spec relates boolean results to propositions.
- Tight loop: write one theorem, build fast, iterate.

See:

- `PIPELINE.md` – end‑to‑end notes, patterns, and pitfalls
- `FloatSpec/src/Core/Defs.lean` – small, self‑contained examples of specs and proofs
- `FloatSpec/src/Calc/Operations.lean` – alignment/arith operations with shape‑correct specs


## Roadmap

- Complete rounding and generic format lemmas in `Core/Generic_fmt.lean`, and ulp/rounding bridges in `Core/Ulp.lean`.
- Finish IEEE 754 bit‑level encodings/decodings and round‑trip theorems (`IEEE754/Bits.lean`, `IEEE754/Binary.lean`, `BinarySingleNaN.lean`).
- Close error‑bound theorems in `Prop` (`Plus_error`, `Div_sqrt_error`, `Double_rounding`, `Relative`, `Sterbenz`, `Round_odd`).
- Expand “calc” coverage (division, sqrt bracketing) from shape to fully verified correctness.
- Documentation and examples; add small sanity tests once more core proofs stabilize.
- VCFloat integration (ErrorBound): implement MVP per `docs/vcfloat_integration/TODOs.md` — Types/Knowledge, RExpr, make_rounding, absolute error lemmas, and two FPBench examples; then extend to relative lemmas and composition rules.


## Repository Layout

- `FloatSpec.lean` – root re‑exports and version
- `Main.lean` – placeholder executable entry point
- `FloatSpec/src/**` – library source (see Architecture)
- `FloatSpec/docs/vcfloat_integration/**` – design notes and TODOs for VCFloat‑style error‑bound integration
- `lakefile.lean`, `lean-toolchain` – build configuration
- `PIPELINE.md`, `CLAUDE.md` – proof workflow and notes
- `FloatSpec_status.pdf` – progress/status snapshot
- `LICENSE` – license information


## Contributing

Contributions are welcome. Please:

- Read `PIPELINE.md` first; follow the one‑proof‑at‑a‑time workflow and compile frequently.
- Keep changes focused; avoid broad refactors unless discussed.
- Prefer adding small helper lemmas over heavy `simp` configurations for arithmetic proofs.

Feel free to open issues with questions about proof strategies, missing lemmas, or module boundaries.


## License and Acknowledgments

- License: see `LICENSE` in the repository.
- Based on the Flocq project (Sylvie Boldo, Guillaume Melquiond). Ported and adapted to Lean 4 with Mathlib.
