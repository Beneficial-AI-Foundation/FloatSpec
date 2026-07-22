# Detailed Changelog

## Commit

- Hash: 8b31762d
- Subject: Restore yLe2x

## Changes

- Restored exact public GenericB lemma `yLe2x` as the symmetry wrapper over `yLe2x_aux`.
- Split on `|b| <= |a|` and swapped `a` and `b` with their matching error and canonicity facts.
- Preserved the reduced exported dependency set without unused even-radix, exponent, sign-transfer, or totality premises.
- Updated the authoritative semantic-gap ledger from 23 to 22; `Subexact` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_131848` using `gpt-5.5` with high reasoning.
- Independent `lake env lean -DmaxErrors=20 FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_yLe2x_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
