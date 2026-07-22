# Restore exact Flocq tBounded_aux

## Summary

- Restored exact public `tBounded_aux` in `FloatSpec/src/Pff/Pff.lean`.
- Preserved the effective upstream payload: the FMA correction `F2R uh - F2R z` has a bounded float representation.
- Implemented the zero, small-residual Sterbenz, and complementary `BoundedL` branches without adding public premises.
- Derived closest-rounding totality internally from `MinEx`, `MaxEx`, and `ClosestTotal`.
- Updated `MISSING_INFRASTRUCTURE.md` from 14 to 13 active gaps, or 242 of 255 resolved.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_171329`.
- Normalized classifier: `.change_log/manual_attempt_20260722_tBounded_aux_proved/attempt.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- Full `lake build`: passed all 3345 jobs.
- Placeholder and status audits: zero findings.
- Added-hole scan and `git diff --check`: passed.
- `scripts/check_diff_trust.sh` is absent in this checkout.
