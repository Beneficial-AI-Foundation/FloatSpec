# Restore ErrFmaApprox

## Summary

Restored the exact public `ErrFmaApprox` theorem in
`FloatSpec/src/Pff/Pff.lean`.

The theorem preserves the upstream Total-section payload without exposing
canonical `b`, bounded `pl`, or an `ul` case premise. It normalizes `b`
internally. In the `ul = 0` branch it obtains a bounded multiplication-error
witness from `errorBoundedMult` and invokes exact `ErrFmaApprox_1`; in the
nonzero branch it invokes exact `ErrFmaApprox_2`. The exact final coefficient
and exponent are preserved.

## Ledger

Removed the final active gap, `ErrFmaApprox`, from the authoritative list.
Overall exact-gap progress is 255/255, with zero active semantic-gap
candidates across every audited module.

## Pipeline Evidence

- Harness: `.change_log/codex_attempt_20260723_000712`
- Verified classifier: `.change_log/codex_attempt_20260723_000712/attempt.verified.json`
- Provider: subscription
- Model: `gpt-5.5`
- Reasoning effort: high

## Verification

- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- Full `lake build`: passed, 3345 jobs.
- Active semantic-gap bullets: zero.
- All active-module ledger headings: zero.
- Added-hole scan: clean.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero placeholder findings.
- `git diff --check`: passed.
- `scripts/check_diff_trust.sh`: unavailable in this checkout.
