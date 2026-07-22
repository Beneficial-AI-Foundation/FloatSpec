# Restore ErrFmaApprox_2_aux

## Summary

Restored the exact public `ErrFmaApprox_2_aux` theorem in
`FloatSpec/src/Pff/Pff.lean`.

The theorem preserves the normal inexact-`uh` payload from upstream Flocq.
It derives `t` exactness from `tBounded` and closest projector equality,
rewrites the total FMA error into the `w` and `v` rounding errors, applies
`ClosestUlp` and `FulpLe2`, and combines exact `wLe` and `vLe` to prove
the exact coefficient `3 * radix / 2 + 1 / 2` and exponent
`2 - 2 * precision`. No pre-proved residual equality, correction magnitude,
or final error bound is assumed.

## Ledger

Removed `ErrFmaApprox_2_aux` from the authoritative active list. Overall
exact-gap progress is now 253/255, with 2 active gaps remaining and
`ErrFmaApprox_2` next.

## Pipeline Evidence

- Harness: `.change_log/codex_attempt_20260722_231847`
- Verified classifier: `.change_log/codex_attempt_20260722_231847/attempt.verified.json`
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
