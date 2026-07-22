# Restore exact Pff `Underf_Err3_bis`

Source commit: `1d5da8fb9b5afed3cf3255d4609d2f776f14cb30`

## Changes

- Added exact public `Underf_Err3_bis` as the upstream corollary of the
  restored exact `Underf_Err3`.
- Preserved both the expanded GenericDek section hypothesis
  `1 < precision` and the corollary-specific hypothesis `4 ≤ precision`.
- Derived the upstream budget bridge
  `7 ≤ radix ^ (precision - 1) - 1` from `1 < radix` and
  `4 ≤ precision`, then applied `Underf_Err3` with its unchanged
  underflow-error, bounded-difference, exponent, and closestness payload.
- Updated `MISSING_INFRASTRUCTURE.md` from 54 to 53 active semantic gaps and
  made `eLe` the next target.

## Verification

- Subscription harness attempt
  `.change_log/codex_attempt_20260721_132843`: classified proved.
- Manual fidelity review restored the explicit GenericDek
  `hprecision : 1 < precision` parameter omitted by the generated draft.
- Upstream statement and proof shape checked against
  `/mnt2/users/kaile/hantao/flocq-upstream/src/Pff/Pff.v:16899`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Direct live-hole search found no `sorry`, `axiom`, or `admit` declaration.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Full `lake build`: passed all 3345 jobs.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`,
  local target gate `pass`, model `gpt-5.5`, provider `subscription`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
