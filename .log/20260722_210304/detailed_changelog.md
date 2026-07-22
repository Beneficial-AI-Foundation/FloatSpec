# Strengthen RleRoundedAbs

## Summary

Restored the upstream-strength public `RleRoundedAbs` theorem in `FloatSpec/src/Pff/Pff.lean`.

The theorem now uses the effective Flocq section payload: integer radix, natural precision, the mantissa-bound power equation, precision at least four, closestness, normality, and an exponent above the minimum boundary. It no longer exposes expanded `Closest` or `Fnormal` internals or the non-upstream premise `bo.vNum >= |f.Fnum| * radix`.

The minimum-normal branch derives its mantissa-product equality internally from `nNormMin`, `PosNormMin`, and the `vNum` equation. This clears the direct prerequisite blocker for exact `LeExp3`.

## Ledger

Recorded count-neutral prerequisite progress. The active exact-gap count remains 9, with `LeExp3` next.

## Pipeline Evidence

- Harness: `.change_log/codex_attempt_20260722_203914`
- Verified classifier: `.change_log/codex_attempt_20260722_203914/attempt.verified.json`
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
