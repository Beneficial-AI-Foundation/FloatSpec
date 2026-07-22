# Restore exact Pff `VeltkampS`

Source commit: `75fb87ee265358a4b4453bf68d6304cfaf6fd380`

## Changes

- Added exact public `VeltkampS` with the upstream subnormal input,
  three closest-rounding premises, half-ulp residual bound, and equal-value
  closest witness in `Veltkamp_reducedBound`, without additional premises.
- Handled zero inputs with a directly bounded zero witness.
- Normalized nonzero subnormal inputs under `plusExp`, transferred the three
  closestness premises, and reused exact `VeltkampN`.
- Restricted the reduced-bound closest witness directly when its exponent is
  in the original range, or re-encoded min/max witnesses at the input exponent
  before restriction.
- Updated `MISSING_INFRASTRUCTURE.md` from 66 to 65 active semantic gaps and
  made `VeltkampEvenS` the next target.

## Verification

- Subscription harness attempt: failed without changes or a build after Codex
  process/session persistence errors.
- Standalone scratch theorem: passed before transfer to the source module.
- Upstream statement and section assumptions: checked against
  `/tmp/flocq/src/Pff/Pff.v:15559`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Full `lake build`: passed all 3345 jobs; `Pff.lean` built in 98 seconds.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`,
  local target gate `pass`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
