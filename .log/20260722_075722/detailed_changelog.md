# Detailed Changelog

## Commit

- Hash: 8bb5432e
- Subject: Restore exact Pff NormalbPrim theorem

## Changes

- Restored exact public `NormalbPrim` with the full upstream Algo2 normal-representative payload.
- Used `Fnormalize` under `Dekker_extendedBound` to prove normality, preserve `F2R`, and establish the required exponent lower bound.
- Added only the faithful `0 <= b.dExp` representation invariant required by the local signed exponent field.
- Updated the authoritative semantic-gap ledger from 33 to 32; `Dekker2_aux` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_073607` using `gpt-5.5` with high reasoning.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_NormalbPrim_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
