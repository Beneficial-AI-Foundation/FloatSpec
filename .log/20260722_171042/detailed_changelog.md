# Restore exact Flocq gaCorrect

## Summary

- Restored exact public `gaCorrect` in `FloatSpec/src/Pff/Pff.lean`.
- Preserved the upstream existential payload: a bounded float representing `F2R be1 - F2R r1 + F2R be2`.
- Reused `gatCorrect`, the zero-residual branch helpers, `Midpoint_aux`, `be2MuchSmaller`, `Expr1`, `Expbe1`, and `BoundedL`.
- Derived closest totality internally and omitted unused upstream section variables and hypotheses.
- Updated `MISSING_INFRASTRUCTURE.md` from 15 to 14 active gaps, or 241 of 255 resolved.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_164952`.
- Normalized classifier: `.change_log/manual_attempt_20260722_gaCorrect_proved/attempt.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- Full `lake build`: passed all 3345 jobs.
- Placeholder and status audits: zero findings.
- Added-hole scan and `git diff --check`: passed.
- `scripts/check_diff_trust.sh` is absent in this checkout.
