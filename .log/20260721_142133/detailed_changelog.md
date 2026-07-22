# Restore exact Pff `eLe`

Source commit: `6daf94ec756b3282ab6c02628e887bb0e833e960`

## Changes

- Added exact public `eLe` with the Sec1 assumptions actually required by
  upstream: radix and precision bounds, normal operands, product exponent
  range, closest rounded product, and exact residual decomposition.
- Kept `Hst1`, `Hst2`, split operands, totality, `boundR`, canonicity,
  and conclusion premises out of the public theorem.
- Followed the upstream `ClosestUlp` proof route, bounding the product and
  normalized result exponent before deriving the half-ulp residual bound.
- Updated `MISSING_INFRASTRUCTURE.md` from 53 to 52 active semantic gaps and
  made `rExp` the next target.

## Pipeline Evidence

- Initial subscription attempt
  `.change_log/codex_attempt_20260721_135051`: correctly classified blocked
  because the deliberately reduced signature omitted necessary Sec1
  precision/range hypotheses and admitted a concrete radix-2 counterexample.
- Corrected subscription attempt
  `.change_log/codex_attempt_20260721_135903`: restored the exact theorem.
- Normalized classifier
  `.change_log/manual_attempt_20260721_eLe_proved/attempt.json`: `proved`,
  build `pass`, Coq alignment `checked`, local target gate `pass`, model
  `gpt-5.5`, provider `subscription`.

## Verification

- Upstream statement and proof checked against
  `/mnt2/users/kaile/hantao/flocq-upstream/src/Pff/Pff.v:17051`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with exit code 0.
- `git diff --check`: passed.
- Direct live-hole search found no `sorry`, `axiom`, or `admit`.
- Placeholder audit: all 11 categories reported zero findings.
- Status report: 58 Lean files with zero proof holes or weakening findings.
- Active-list recount: exactly 52 Pff bullets.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh` is absent from this checkout.
