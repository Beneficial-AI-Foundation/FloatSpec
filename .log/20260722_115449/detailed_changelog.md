# Detailed Changelog

## Commit

- Hash: b0f94d98
- Subject: Restore xLe2y_aux1

## Changes

- Restored exact public GenericA lemma `xLe2y_aux1` with the upstream exact-power branch payload.
- Proved the rounded value `x` equals the exactly representable sum by using positive or negative unit witnesses.
- Constructed the bounded even-radix half-unit witness and proved it lies below `|a + b + e|` from the canonical ulp error bound.
- Transferred the half-unit bound through closest absolute monotonicity to derive `|x| <= 2 * |y|`.
- Updated the authoritative semantic-gap ledger from 27 to 26; `xLe2y_aux2` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_112000` using `gpt-5.5` with high reasoning.
- Independent `lake env lean -DmaxErrors=20 FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_xLe2y_aux1_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
