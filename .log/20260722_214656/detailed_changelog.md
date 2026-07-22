# Restore LeExp

## Summary

Restored the exact public `LeExp` theorem in `FloatSpec/src/Pff/Pff.lean`.

The theorem preserves the effective upstream inexact-`uh` section payload and
proves exactly
`radix^ph.Fexp + radix^uh.Fexp <= 2 * radix^(z.Fexp + 1)`.
It uses exact `LeExp1` and `LeExp2` for the weak exponent bounds and exact
`LeExp3` to eliminate the simultaneous equality corner. No exponent-order
premise, bounded `a`/`x`, canonical `b`, unrelated residual, or
conclusion-shaped assumption was added.

## Ledger

Removed `LeExp` from the authoritative active list. Overall exact-gap
progress is now 248/255, with 7 active gaps remaining and `vLe_aux` next.

## Pipeline Evidence

- Harness: `.change_log/codex_attempt_20260722_213255`
- Verified classifier: `.change_log/codex_attempt_20260722_213255/attempt.verified.json`
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
