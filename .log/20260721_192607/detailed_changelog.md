# Detailed Changelog

## Commit

- Hash: 59de1409
- Subject: Restore exact Pff Boundedx2y2 theorem

## Changes

- Restored exact public `Boundedx2y2` with the upstream Algo section payload.
- Derived `s`, its bounds, and both branch product-width inequalities internally.
- Used `Veltkamp_tail2` for radix two and `VeltkampU` for even precision.
- Repaired the harness draft so no derived split assumptions or canonicity premise leak into the public theorem.
- Updated the authoritative semantic-gap ledger from 39 to 38; `DekkerN` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260721_190324` using `gpt-5.5` with high reasoning.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
