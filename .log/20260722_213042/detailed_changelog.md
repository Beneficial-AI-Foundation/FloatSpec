# Restore LeExp3

## Summary

Restored the exact public `LeExp3` theorem in `FloatSpec/src/Pff/Pff.lean`.

The theorem preserves the effective upstream inexact-`uh` payload: integer
radix, natural precision, the mantissa-bound power equation, precision at least
four, the local bounded-exponent invariant, bounded `b`, normal
`ph`/`uh`/`z`, closest rounded values for the product, intermediate sum,
and final sum, the exact nonzero `ul` residual, and both one-exponent-gap
hypotheses. It concludes `False` without adding bounded `a`/`x`, canonical
`b`, unrelated residuals, or conclusion-shaped assumptions.

The proof derives `b.Fexp <= z.Fexp` from the bounded plus-error exponent and
strict closest-error exponent, applies exact-strength `RleRoundedAbs` to the
rounded product, and uses closest-rounding absolute monotonicity to contradict
the normal bounded mantissa of `z`.

## Ledger

Removed `LeExp3` from the authoritative active list. Overall exact-gap
progress is now 247/255, with 8 active gaps remaining and `LeExp` next.

## Pipeline Evidence

- Harness: `.change_log/codex_attempt_20260722_210800`
- Verified classifier: `.change_log/codex_attempt_20260722_210800/attempt.verified.json`
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
