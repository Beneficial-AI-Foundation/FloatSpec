# Detailed Changelog

## Commit

- Hash: e75789b8
- Subject: Restore exact Pff Dekker2 theorem

## Changes

- Restored exact public `Dekker2` with the full upstream Algo2 section payload.
- Propagated zero `x` or `y` through every rounded split, product, and residual operation using `ClosestZero2`.
- Delegated the nonzero branch to exact `Dekker2_aux` without adding nonzero assumptions to the public wrapper.
- Added only the faithful `0 <= b.dExp` representation invariant required by the local signed exponent field.
- Updated the authoritative semantic-gap ledger from 31 to 30; `Twice_EvenClosest_Round` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_083458` using `gpt-5.5` with high reasoning.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_Dekker2_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
