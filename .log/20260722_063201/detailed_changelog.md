# Detailed Changelog

## Commit

- Hash: 1755c613
- Subject: Restore exact Pff DekkerS1 theorem

## Changes

- Restored exact public `DekkerS1` with the full upstream AlgoS1 section payload.
- Preserved both the zero-subnormal cascade and the nonzero `plusExp` normalization proof.
- Lifted every A/B/C/D closestness hypothesis with exact float-operation witnesses before applying `DekkerN`.
- Updated the authoritative semantic-gap ledger from 37 to 36; `DekkerS2` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_060750` using `gpt-5.5` with high reasoning.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Normalized classifier: `.change_log/manual_attempt_20260722_DekkerS1_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
