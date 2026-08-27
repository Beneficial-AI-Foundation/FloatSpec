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

Six same-name `Unit` declarations were removed. The compatibility names now
alias the actual translated Flocq theorem contracts:

| Compatibility name | Flocq contract |
|---|---|
| `binary_add_correct` | `Bplus_correct` |
| `binary_mul_correct` | `Bmult_correct` |
| `binary_sub_correct` | `Bminus_correct` |
| `binary_fma_correct` | `Bfma_correct` |
| `binary_div_correct` | `Bdiv_correct` |
| `binary_sqrt_correct` | `Bsqrt_correct` |

Regression tests prove that each compatibility declaration is definitionally
the corresponding source theorem.

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
source. Judge negatives require an executable or proof-checked counterexample;
unsupported cases remain uncertain.
