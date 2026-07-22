# Detailed Changelog

## Commit

- Hash: 304a2e3a
- Subject: Restore yLe2x_aux

## Changes

- Restored exact public GenericA lemma `yLe2x_aux` with the upstream zero-or-positive-unit branch payload.
- Proved the zero branch contradicts `F2R x != 0` and bounded the positive branch with the normal closest-rounding factors.
- Normalized the harness signature by removing the unused Coq section hypotheses `Even radix` and the strict exponent bound on `b`.
- Updated the authoritative semantic-gap ledger from 25 to 24; `xLe2y` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_123242` using `gpt-5.5` with high reasoning.
- Independent `lake env lean -DmaxErrors=20 FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_yLe2x_aux_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
