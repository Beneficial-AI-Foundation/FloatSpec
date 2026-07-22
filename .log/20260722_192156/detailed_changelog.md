# Restore exact Flocq ErrFmaApprox_1_aux

## Summary

- Restored exact public `ErrFmaApprox_1_aux` in `FloatSpec/src/Pff/Pff.lean`.
- Preserved the effective upstream exact-`uh` Case1 normal-`z`/normal-`w` error-bound payload.
- Used exact `tBounded` and rounded projector equality to recover the exact correction terms.
- Used `RoundedModeUlp`, `FcanonicFnormalizeEq`, and `FulpLe2` for the relative ulp bounds.
- Derived closest-rounding totality internally and exposed no intermediate proof premises.
- Updated `MISSING_INFRASTRUCTURE.md` from 12 to 11 active gaps, or 244 of 255 resolved.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_185832`.
- Normalized classifier: `.change_log/codex_attempt_20260722_185832/attempt.verified.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- Full `lake build`: passed all 3345 jobs.
- Placeholder and status audits: zero findings.
- Added-hole scan and `git diff --check`: passed.
- `scripts/check_diff_trust.sh` is absent in this checkout.
