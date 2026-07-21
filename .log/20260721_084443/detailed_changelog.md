# Restore exact Pff `VeltkampEvenS`

Source commit: `6e5f4dc2214118d584ba62c8e2c60d7bc7be321a`

## Changes

- Added exact public `VeltkampEvenS` with the upstream subnormal input and
  three nearest-even rounding premises, producing an equal-value nearest-even
  witness in `Veltkamp_reducedBound` at precision `t - s`.
- Constructed a normalized-even zero witness for the exact-zero branch.
- Normalized nonzero subnormal inputs under `plusExp`, transferred all three
  `EvenClosest` premises, and reused exact `VeltkampEvenN`.
- Re-encoded lower-exponent min/max witnesses at the input exponent and
  preserved parity through equality of normalized canonical representatives.
- Updated `MISSING_INFRASTRUCTURE.md` from 65 to 64 active semantic gaps and
  made `VeltkampEven` the next target.

## Verification

- Subscription harness attempt: failed without changes or a build after Codex
  process/session persistence errors.
- Standalone scratch theorem: passed before transfer to the source module.
- Upstream statement and section assumptions: checked against
  `/tmp/flocq/src/Pff/Pff.v:15734`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Full `lake build`: passed all 3345 jobs; `Pff.lean` built in 100 seconds.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`,
  local target gate `pass`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
