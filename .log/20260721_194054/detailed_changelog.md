# Detailed Changelog

## Commit

- Hash: 6cd8b712
- Subject: Restore exact Pff DekkerN theorem

## Changes

- Restored exact public `DekkerN` with the full upstream Algo section payload.
- Composed exact `Boundedx2y2` and `Dekker_aux` without adding a witness or conclusion premise.
- Updated the authoritative semantic-gap ledger from 38 to 37; `DekkerS1` is next.
- Corrected the older counterpart note for the restored Dekker theorem family.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260721_192803` using `gpt-5.5` with high reasoning.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
