# Restore wLe

## Summary

Restored the exact public `wLe` theorem in
`FloatSpec/src/Pff/Pff.lean`.

The theorem preserves the effective upstream `uhInexact` section payload and
adds the closest definitions of `t`, `v`, and `w`. It constructs the
bounded comparator float with mantissa `2 * radix + 1` and exponent
`z.Fexp`, applies `RoundAbsMonotoner` to the closest rounding of `t + v`,
and combines exact `tLe` and `vLe` through the triangle inequality. It
requires neither pre-proved correction bounds nor normality of `v` or `w`.

## Ledger

Removed `wLe` from the authoritative active list. Overall exact-gap progress
is now 252/255, with 3 active gaps remaining and `ErrFmaApprox_2_aux` next.

## Pipeline Evidence

- Harness: `.change_log/codex_attempt_20260722_225843`
- Verified classifier: `.change_log/codex_attempt_20260722_225843/attempt.verified.json`
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
