# Restore exact Pff `rExp`

Source commit: `2d353f5258eb5da38f859c6c35cf0c4b786be3fa`

## Changes

- Added exact public `rExp` with the upstream Sec1 radix, precision,
  normal-operand, product-range, and closest-rounding assumptions.
- Proved the minimum-normal product lower magnitude directly from `Fnormal`.
- Avoided the local `RoundAbsMonotonel` totality mismatch by applying
  `Closest` directly to signed bounded witnesses, without adding `boundR`
  or totality to the public theorem.
- Compared canonical exponents after normalization and transported the result
  back to the original rounded float.
- Updated `MISSING_INFRASTRUCTURE.md` from 52 to 51 active semantic gaps and
  made `Boundedt1` the next target.

## Pipeline Evidence

- Subscription attempt
  `.change_log/codex_attempt_20260721_142334`: classified blocked because the
  local rounded-mode route exposes forbidden `ClosestTotal`/`boundR`
  requirements.
- Manual repair retained the exact theorem API and cleared the local packaging
  blocker with direct closestness reasoning.
- Normalized classifier
  `.change_log/manual_attempt_20260721_rExp_proved/attempt.json`: `proved`,
  build `pass`, Coq alignment `checked`, local target gate `pass`, model
  `gpt-5.5`, provider `subscription`.

## Verification

- Upstream statement and proof checked against
  `/mnt2/users/kaile/hantao/flocq-upstream/src/Pff/Pff.v:17107`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with exit code 0.
- `git diff --check`: passed.
- Direct live-hole search found no `sorry`, `axiom`, or `admit`.
- Placeholder audit: all 11 categories reported zero findings.
- Status report: 58 Lean files with zero proof holes or weakening findings.
- Active-list recount: exactly 51 Pff bullets.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh` is absent from this checkout.
