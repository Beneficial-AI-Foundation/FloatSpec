# Integration Proof and Specification Audit

Date: 2026-08-27

Scope: the `integration` branch reconstructed from current `main` and the
reviewed `audit_fix` tree.

## Trust status

- Active `sorry`: 0
- Active `admit`: 0
- Project axioms: 0
- Recognized semantic placeholders: 0
- Lean files: generated in `status.md` and `status.json`

The counts are generated from active Lean syntax; comments are excluded from
placeholder matching.

## Resolved merge blockers

### Correctness names

Six same-name `Unit` declarations were removed. Two compatibility names are
now exact aliases of translated Flocq theorem contracts:

| Compatibility name | Flocq contract |
|---|---|
| `binary_add_correct` | `Bplus_correct` |
| `binary_mul_correct` | `Bmult_correct` |

Regression tests prove these two alias equalities definitionally.

The local theorems `binary_sub_correct`, `binary_fma_correct`,
`binary_div_correct`, and `binary_sqrt_correct` no longer occupy the Coq names
`Bminus_correct`, `Bfma_correct`, `Bdiv_correct`, and `Bsqrt_correct`. Targeted
source/target review found that the Coq contracts quantify over source
operations and NaN handlers that the local compatibility operations do not
model. Those source declarations therefore remain explicitly unported instead
of being reported as completed translations.

The root `binary_overflow` implementation now follows Coq's rounding-mode and
sign behavior, including the largest-finite result for RTZ overflow. This
removes the concrete RTZ counterexample that exposed the old always-infinity
implementation.

### Targeted semantic rerun

The v13 source/target judge was rerun after the fixes, using a freshly rebuilt
target index. This was a seven-item audit, not a full-repository score:

| Source item | Result | Evidence/interpretation |
|---|---|---|
| `canonical_bounded` | aligned | Three compiler-checked Coq/Lean proof observations; the exported interfaces no longer contain extra precision instances |
| `Bplus_correct` | aligned | Three compiler-checked Coq/Lean proof observations |
| `Bmult_correct` | uncertain | No mismatch found; the three-observation threshold was not completed |
| `Bminus_correct` | not judged | Deterministic matcher selected the wrong target; source contract remains unported |
| `Bfma_correct` | not judged | Deterministic matcher selected the local compatibility theorem; source contract remains unported |
| `Bdiv_correct` | not judged | Deterministic matcher selected the local compatibility theorem; source contract remains unported |
| `Bsqrt_correct` | not judged | Deterministic matcher selected the local compatibility theorem; source contract remains unported |

The target compiled during judging. The overall judge report is intentionally
`INCOMPLETE`, because only these seven jobs were requested from the 5,145-job
repository plan. In particular, the two aligned results must not be reported
as a repository-wide alignment score.

### `canonical_bounded`

The source-facing theorem now takes a Coq-shaped positive mantissa and the
`specFloat_bounded` predicate. The former Lean-only combination of range
boundedness, explicit positivity, and explicit canonicality is no longer
published under the Coq theorem name. Nat representation users have a separate
`canonical_bounded_nat` bridge.

### Repository hygiene

Generated `.log` history from `audit_fix` is not present. Integration commits
are split into toolchain, Core, Calc, Prop, IEEE754, Pff, tests, and
documentation/CI layers. Full model transcripts and judge evidence remain
external pipeline artifacts.

## Remaining trust boundary

Compilation, proof-hole scans, and alias regressions are necessary but not
sufficient evidence of semantic equivalence. The repository-level alignment
judge must still compare each translated declaration against the pinned Coq
source. The targeted judge confirmed the old overflow counterexample and
exposed the four incomplete source contracts; full-repository judging remains
required. Judge negatives require an executable or proof-checked
counterexample; unsupported cases remain uncertain.
