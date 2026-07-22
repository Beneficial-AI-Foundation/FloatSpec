# Detailed Changelog

## Commit

- Hash: e7c379fc
- Subject: Restore Midpoint_aux

## Changes

- Restored exact public GenericD lemma `Midpoint_aux` with the full upstream closest-rounding disjunction and no added positivity premise.
- Split on the sign of `F2R x1`, using `Midpoint_aux_aux` directly for positive `x1` and ruling out zero from normality.
- Transported the negative branch through `Fopp`, `ClosestOpp`, `MSB_opp`, `LSB_opp`, and `FnormalFop`, then mapped the equivalent-representation witness back.
- Updated the authoritative semantic-gap ledger from 20 to 19; `gatCorrect` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_144725` using `gpt-5.5` with high reasoning; it generated the exact declaration and proof.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_Midpoint_aux_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
