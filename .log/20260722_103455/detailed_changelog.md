# Detailed Changelog

## Commit

- Hash: 6bff2718
- Subject: Restore errorBoundedMultClosest_Can

## Changes

- Restored exact public `errorBoundedMultClosest_Can` with the complete upstream binary canonical residual payload and no additional premises.
- Derived the rounded product exponent bounds directly from closestness, explicit bounded endpoint floats, canonical exponent comparison, and the upstream product-magnitude premise.
- Re-expressed the exact multiplication residual at exponent `g.Fexp - precision` and proved its mantissa bound with `ClosestUlp` and `CanonicFulp`.
- Updated the authoritative semantic-gap ledger from 29 to 28; `cases` is next.
- Corrected stale ledger summary and counterpart-audit counts to match the active list.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_094154` using `gpt-5.5` with high reasoning; it timed out after adding a rejected non-upstream premise.
- Normalized exact proof classifier: `.change_log/manual_attempt_20260722_errorBoundedMultClosest_Can_proved/attempt.json`.
- Independent `lake env lean -DmaxErrors=20 FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
