# Restore tLe

## Summary

Restored the exact public `tLe` theorem in
`FloatSpec/src/Pff/Pff.lean`.

The theorem preserves the effective upstream `uhInexact` section payload.
It derives `F2R t = F2R uh - F2R z` from `tBounded` and closest-rounding
projector equality, bounds the rounded FMA error with `RoundedModeUlp`, and
bounds the product and addition errors with `ClosestUlp`, `CanonicFulp`,
and exact `LeExp`. It concludes
`|F2R t| <= radix^z.Fexp * (radix + 1)` without a pre-proved value for
`t`, a desired output bound, or unrelated `v`/`w` premises.

## Ledger

Removed `tLe` from the authoritative active list. Overall exact-gap progress
is now 251/255, with 4 active gaps remaining and `wLe` next.

## Pipeline Evidence

- Harness: `.change_log/codex_attempt_20260722_223444`
- Verified classifier: `.change_log/codex_attempt_20260722_223444/attempt.verified.json`
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
