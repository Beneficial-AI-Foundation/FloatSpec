# Restore LeExp2

## Summary

Restored the exact public Flocq `LeExp2` lemma in `FloatSpec/src/Pff/Pff.lean`.

The theorem preserves the effective upstream inexact-`uh` payload and proves `uh.Fexp <= z.Fexp + 1`. It combines the three closest-rounding ulp bounds, applies exact `LeExp1`, derives `|F2R uh| <= radix * |F2R z|`, and compares `uh` with a canonical one-exponent shift of `z`.

Unused Coq section assumptions are not exposed: the public theorem omits boundedness of `a` and `x`, canonicity of `b`, and the unused `pl` residual.

## Ledger

- Removed `LeExp2` from the active exact-gap list.
- Reduced the authoritative ledger from 10 to 9 remaining gaps.
- Recorded `LeExp3` as the next active target.
- Current exact-gap progress: 246 of 255 resolved.

## Pipeline Evidence

- Harness: `.change_log/codex_attempt_20260722_195131`
- Verified classifier: `.change_log/codex_attempt_20260722_195131/attempt.verified.json`
- Provider: subscription
- Model: `gpt-5.5`
- Reasoning effort: high

The harness generated the exact candidate proof. Its initial full build hit the full `/mnt/users` Ceph volume. The ignored `.lake/build` symlink was relocated to `/tmp`, after which the independent full build completed.

## Verification

- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- Full `lake build`: passed, 3345 jobs.
- Added-hole scan: clean.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero placeholder findings.
- `git diff --check`: passed.
- `scripts/check_diff_trust.sh`: unavailable in this checkout.
