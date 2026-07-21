# Detailed Changelog

## Commit

- Hash: 79290ca5
- Subject: Restore exact Pff Dekker1 theorem

## Changes

- Restored exact public `Dekker1` with the full upstream Algo1 section payload.
- Mapped Coq's nonzero natural `dExp` premise to positive local integer `dExp`.
- Dispatched the normal/subnormal cases to exact `DekkerN`, `DekkerS1`, and `DekkerS2`.
- Updated the authoritative semantic-gap ledger from 35 to 34; `Veltkampb'` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_065543` using `gpt-5.5` with high reasoning.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Normalized classifier: `.change_log/manual_attempt_20260722_Dekker1_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
