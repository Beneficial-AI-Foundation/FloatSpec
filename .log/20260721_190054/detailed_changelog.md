# Detailed Changelog

## Commit

- Hash: d837c7ab
- Subject: Restore exact Pff Dekker_aux theorem

## Changes

- Restored the exact public Lean theorem `Dekker_aux` with the full upstream Flocq Algo section payload.
- Reused `VeltkampU`, `Boundedt1` through `Boundedt4`, and the exact bounded-product wrappers.
- Derived Closest projector equality directly, without adding a totality or conclusion premise.
- Updated the authoritative semantic-gap ledger from 40 to 39; `Boundedx2y2` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260721_183648` using `gpt-5.5` with high reasoning.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
