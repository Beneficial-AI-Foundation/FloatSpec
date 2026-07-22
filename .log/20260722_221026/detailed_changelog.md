# Restore vLe_aux

## Summary

Restored the exact public `vLe_aux` theorem in
`FloatSpec/src/Pff/Pff.lean`.

The theorem preserves the effective upstream inexact-`uh` payload plus the
exact `pl = a*x-ph` residual and proves
`|pl+ul| <= radix^z.Fexp * radix`. It derives both residual bounds from
`ClosestUlp`, rewrites ulps with `CanonicFulp`, combines them through exact
`LeExp`, and applies the successor-power identity. It does not expose
pre-proved ulp or exponent bounds, bounded `a`/`x`, canonical `b`, or
unrelated `v`/`t`/`w` premises.

## Ledger

Removed `vLe_aux` from the authoritative active list. Overall exact-gap
progress is now 249/255, with 6 active gaps remaining and `vLe` next.

## Pipeline Evidence

- Harness: `.change_log/codex_attempt_20260722_214915`
- Verified classifier: `.change_log/codex_attempt_20260722_214915/attempt.verified.json`
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
