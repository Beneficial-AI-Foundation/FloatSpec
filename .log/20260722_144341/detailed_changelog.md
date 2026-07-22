# Detailed Changelog

## Commit

- Hash: 3ce134e5
- Subject: Restore Midpoint_aux_aux

## Changes

- Restored exact public GenericC lemma `Midpoint_aux_aux` with the full closest-rounding disjunction and equivalent-representation exponent payload.
- Added private midpoint helpers for least-significant-bit witnesses, separated residual bounds, positive normal binade bounds, and strict closest uniqueness.
- Covered the canonical LSB witness, minimum-significand predecessor-spacing branch, and non-minimum normal branch without adding payload assumptions.
- Updated the authoritative semantic-gap ledger from 21 to 20; `Midpoint_aux` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_135515` using `gpt-5.5` with high reasoning; it made no changes and classified the attempt as failed.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_Midpoint_aux_aux_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
