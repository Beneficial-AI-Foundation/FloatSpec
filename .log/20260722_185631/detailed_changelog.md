# Restore exact Flocq tBounded

## Summary

- Restored exact public `tBounded` in `FloatSpec/src/Pff/Pff.lean`.
- Preserved the upstream normal-or-zero payload and bounded witness for `F2R uh - F2R z`.
- Reused exact `tBounded_aux` directly for nonnegative inputs and through full negation transport for negative inputs.
- Preserved the upstream zero-valued `ph`, `z`, and `uh` fallback constructions.
- Derived closest-rounding totality internally without adding a public premise.
- Updated `MISSING_INFRASTRUCTURE.md` from 13 to 12 active gaps, or 243 of 255 resolved.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_183900`.
- Normalized classifier: `.change_log/codex_attempt_20260722_183900/attempt.verified.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- Full `lake build`: passed all 3345 jobs.
- Placeholder and status audits: zero findings.
- Added-hole scan and `git diff --check`: passed.
- `scripts/check_diff_trust.sh` is absent in this checkout.
