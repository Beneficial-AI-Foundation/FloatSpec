# Detailed Changelog

## Commit

- Hash: 56f812c5
- Subject: Restore Subexact

## Changes

- Restored exact public GenericB lemma `Subexact` with the full existential value, boundedness, and minimum-exponent payload.
- Derived nonzero `x` from normality and reused exact `xLe2y` and `yLe2x` for Sterbenz bounds.
- Implemented both upstream witnesses: direct subtraction for nonnegative `y` and negated subtraction of opposites for negative `y`.
- Updated the authoritative semantic-gap ledger from 22 to 21; `Midpoint_aux_aux` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_133425` using `gpt-5.5` with high reasoning.
- Independent `lake env lean -DmaxErrors=20 FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_Subexact_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
