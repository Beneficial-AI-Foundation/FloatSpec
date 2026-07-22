# Restore Exact Pff eqEqual Theorem

Commit: `3e206bb8230713be7fdb7f388b0c407f9a92657b`

## Summary

- Restored exact public `eqEqual` with the expanded upstream Flocq Veltkamp
  section assumptions and the full equality-or-boundary disjunction.
- Combined exact public `eqLe` and `eqGe`: exponent antisymmetry proves the
  equality branch, while the negative minimal-normal value and half-ulp
  residual branch is preserved unchanged.
- Updated the authoritative active-gap ledger from 81 to 80;
  `Veltkamp_aux_aux` is next.

## Verification

- `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with Lean exit status 0.
- `lake build`: passed, 3345 jobs.
- `scripts/status_report.sh --write`: 58 Lean files and zero sorry, axiom,
  admit, placeholder, weakening, or conclusion-as-hypothesis findings.
- `scripts/audit_placeholders.sh --json FloatSpec`: all 11 counters zero.
- `git diff --check`: passed.
- Active Pff ledger recount: 80.
- `scripts/check_diff_trust.sh`: absent from this checkout.

## Pipeline Record

The subscription harness attempt
`.change_log/codex_attempt_20260721_025037` produced the exact theorem and
passed its target check. The independently verified normalized classifier is
`.change_log/manual_attempt_20260721_eqEqual_proved/attempt.json`, recording
`result = proved`, `build = pass`, and `coq_alignment = checked`.
