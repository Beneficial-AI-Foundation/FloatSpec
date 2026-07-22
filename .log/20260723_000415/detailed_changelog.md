# Restore ErrFmaApprox_2

## Summary

Restored the exact public `ErrFmaApprox_2` theorem in
`FloatSpec/src/Pff/Pff.lean`.

The theorem preserves the upstream normal-or-zero payload for `ph`, `uh`,
`z`, `v`, and `w`. It invokes exact `ErrFmaApprox_2_aux` in the
all-normal branch, proves the quantitative `w = 0` branch, derives
contradictions with nonzero `ul` in the `uh = 0`, `ph = 0`, and `z = 0`
branches, and proves exact zero error in the `v = 0` branch. No bounded
`pl`, pre-proved zero consequence, correction bound, or final error bound is
assumed.

## Ledger

Removed `ErrFmaApprox_2` from the authoritative active list. Overall exact-gap
progress is now 254/255, with only `ErrFmaApprox` remaining.

## Pipeline Evidence

- Harness: `.change_log/codex_attempt_20260722_234309`
- Verified classifier: `.change_log/codex_attempt_20260722_234309/attempt.verified.json`
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
