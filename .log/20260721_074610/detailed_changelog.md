# Restore exact Pff `ClosestClosest`

Source commit: `2b78eb5929b77bd9626a42ba5029aeef24337165`

## Changes

- Added exact public `ClosestClosest` with the upstream radix, precision,
  closestness, normality, and exponent-gap assumptions and no additions.
- Normalized the lower-exponent absolute-valued result and constructed its
  bounded normalized successor.
- Proved that successor lies strictly between the two closest values, then
  contradicted the appropriate closestness inequality relative to `|z|`.
- Updated `MISSING_INFRASTRUCTURE.md` from 68 to 67 active semantic gaps and
  made `EvenClosestbbplus` the next target.

## Verification

- Subscription harness attempt: failed without changes or a build after a
  local model-cache configuration error.
- Standalone scratch theorem: passed before transfer to the source module.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Full `lake build`: passed all 3345 jobs; `Pff.lean` built in 100 seconds.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`, local
  target gate `pass`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
