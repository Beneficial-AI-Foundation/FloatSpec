# Restore vLe

## Summary

Restored the exact public `vLe` theorem in `FloatSpec/src/Pff/Pff.lean`.

The theorem preserves the exact `vLe_aux` payload and adds only closest
rounding of `pl+ul` to `v`. It proves
`|v| <= radix^z.Fexp * radix` by deriving the bounded comparator float
`Float radix z.Fexp`, applying `RoundAbsMonotoner`, and supplying exact
`vLe_aux`. It does not require normality of `v`, a pre-proved output bound,
bounded `a`/`x`, canonical `b`, or unrelated `t`/`w` premises.

## Ledger

Removed `vLe` from the authoritative active list. Overall exact-gap progress
is now 250/255, with 5 active gaps remaining and `tLe` next.

## Pipeline Evidence

- Harness: `.change_log/codex_attempt_20260722_221259`
- Verified classifier: `.change_log/codex_attempt_20260722_221259/attempt.verified.json`
- Provider: subscription
- Model: `gpt-5.5`
- Reasoning effort: high

## Verification

- Focused `lake env lean -DmaxErrors=20 FloatSpec/src/Pff/Pff.lean`: passed.
- Full `lake build`: passed, 3345 jobs.
- Added-hole scan: clean.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero placeholder findings.
- `git diff --check`: passed.
- `scripts/check_diff_trust.sh`: unavailable in this checkout.
