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
