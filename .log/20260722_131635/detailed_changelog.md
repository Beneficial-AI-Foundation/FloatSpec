# Detailed Changelog

## Commit

- Hash: a98f8c8e
- Subject: Restore xLe2y

## Changes

- Restored exact public GenericB lemma `xLe2y` as the symmetry wrapper over `xLe2y_aux2`.
- Split on `|b| <= |a|` and swapped `a` and `b` with the matching error, canonicity, and exponent facts in the other branch.
- Preserved the exact exported dependency set and omitted the unused GenericB sign-transfer hypothesis.
- Updated the authoritative semantic-gap ledger from 24 to 23; `yLe2x` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_130343` using `gpt-5.5` with high reasoning.
- Independent `lake env lean -DmaxErrors=20 FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_xLe2y_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
