# Complete eqLe Exact Theorem

Commit: `92468096fd1f094e03a0e4aeecfc7b2d118ab2c4`

## Summary

- Restored exact public `eqLe` with the expanded upstream Flocq Veltkamp
  section assumptions and the full exponent-or-boundary disjunction.
- Removed the non-upstream `TotalP Closest` premise from `pPos`, `qNeg`,
  `hxExact`, `eqLeep`, and `epLe`, deriving monotonicity and bounded-float
  projection directly from concrete `Closest`.
- Implemented the low-mantissa branch through the upstream normal comparison
  float and the `ClosestExp`/canonical-exponent bounds.
- Implemented the high-mantissa branch by proving the exact negative
  minimal-normal boundary value and both sides of the half-ulp residual bound.
- Updated the authoritative active-gap ledger from 83 to 82; `eqGe` is next.

## Verification

- `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `lake build`: passed, 3345 jobs.
- `scripts/status_report.sh --write`: 58 Lean files and zero sorry, axiom,
  admit, placeholder, weakening, or conclusion-as-hypothesis findings.
- `scripts/audit_placeholders.sh --json FloatSpec`: all 11 counters zero.
- `git diff --check`: passed.
- Active Pff ledger recount: 82.
- `scripts/check_diff_trust.sh`: absent from this checkout.

## Pipeline Record

The subscription harness attempt
`.change_log/codex_attempt_20260721_005450` correctly classified the original
target as blocked because the shared Veltkamp helper surface still exposed a
non-upstream totality premise and lacked the two branch packages. The
normalized manual classifier is
`.change_log/manual_attempt_20260721_eqLe_proved/attempt.json`.
