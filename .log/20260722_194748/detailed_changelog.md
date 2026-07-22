# Restore ErrFmaApprox_1

## Summary

Restored the exact public Flocq `ErrFmaApprox_1` theorem in `FloatSpec/src/Pff/Pff.lean`.

The proof preserves the upstream normal-or-zero hypotheses for `z` and `w`. The all-normal branch delegates to the exact `ErrFmaApprox_1_aux` payload. The zero branches establish the required exact equalities and use the local closest-rounding lemmas to force the corresponding rounded values to zero.

## Ledger

- Removed `ErrFmaApprox_1` from the active exact-gap list.
- Reduced the authoritative ledger from 11 to 10 remaining gaps.
- Recorded `LeExp2` as the next active target.
- Current exact-gap progress: 245 of 255 resolved.

## Pipeline Evidence

- Harness: `.change_log/codex_attempt_20260722_192358`
- Verified classifier: `.change_log/codex_attempt_20260722_192358/attempt.verified.json`
- Provider: subscription
- Model: `gpt-5.5`
- Reasoning effort: high

## Verification

- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- Full `lake build`: passed, 3345 jobs.
- Added-hole scan: clean.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero placeholder findings.
- `git diff --check`: passed.
- `scripts/check_diff_trust.sh`: unavailable in this checkout.
