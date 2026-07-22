# Detailed Changelog

## Commit

- Hash: 7e8fcd4b
- Subject: Restore exact Pff Veltkampb' theorem

## Changes

- Restored exact public `Veltkampb'` with the full upstream Algo2 bound-extension payload.
- Built exact arithmetic-operation witnesses and lifted all four closestness statements through `Closestbbext`.
- Recorded and corrected the harness's stale post-edit target-line audit.
- Updated the authoritative semantic-gap ledger from 34 to 33; `NormalbPrim` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_071159` using `gpt-5.5` with high reasoning.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_Veltkampb_prime_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
