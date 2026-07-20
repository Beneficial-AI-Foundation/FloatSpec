# Restore exact Pff `Closestbbplus`

Source commit: `bb6bfe51e98942de6e6cf108f9603bb4f2e382fb`

## Changes

- Added exact public `Closestbbplus`, extending closestness from `b0` to
  `plusExp b0 t` with the upstream premises and no additions.
- Split competitors by whether they satisfy the original exponent bound.
- Proved the lower-exponent case using an interior radix threshold, an exact
  shifted representative, and signed threshold representatives.
- Updated `MISSING_INFRASTRUCTURE.md` from 70 to 69 active semantic gaps and
  made `EvenClosestbplusb` the next target.

## Verification

- Standalone scratch theorem: passed before transfer to the source module.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Full `lake build`: passed all 3345 jobs; `Pff.lean` built in 97 seconds.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`, local
  target gate `pass`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
