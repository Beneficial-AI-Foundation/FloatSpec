# Detailed Changelog

## Commit

- Hash: 0d52fea2
- Subject: Restore exact Pff DekkerS2 theorem

## Changes

- Restored exact public `DekkerS2` with the full upstream AlgoS2 section payload.
- Preserved the zero-subnormal cascade and the nonzero `plusExp` normalization of `x`.
- Lifted every A/B/C/D closestness hypothesis while preserving the upstream D3/D4 subtraction order.
- Updated the authoritative semantic-gap ledger from 36 to 35; `Dekker1` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_063431` using `gpt-5.5` with high reasoning.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Normalized classifier: `.change_log/manual_attempt_20260722_DekkerS2_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
