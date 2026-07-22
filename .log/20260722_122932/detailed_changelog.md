# Detailed Changelog

## Commit

- Hash: 1e970050
- Subject: Restore xLe2y_aux2

## Changes

- Restored exact public GenericA lemma `xLe2y_aux2` with the full upstream zero, exact-power, and large-magnitude branch payload.
- Added private structural helpers for the canonical `Fplus` magnitude trichotomy and the precision-dependent relative-error factor bound.
- Reused exact `xLe2y_aux1`, normal closest-rounding bounds, `abeLeab`, and `UnMoinsPos` without weakening the public conclusion.
- Updated the authoritative semantic-gap ledger from 26 to 25; `yLe2x_aux` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_120120` using `gpt-5.5` with high reasoning.
- Independent `lake env lean -DmaxErrors=20 FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_xLe2y_aux2_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
