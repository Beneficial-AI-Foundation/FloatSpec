# Restore exact Pff `VeltkampEvenN_aux`

Source commit: `9a95892c0272fa8e59722f5d27ffe04536c7cf30`

## Changes

- Added exact public `VeltkampEvenN_aux` with the upstream Flocq payload and no
  additional premises.
- Reused `VeltkampEven_pos` for positive represented inputs after deriving
  nonzero from normality.
- Transported all three nearest-even rounding premises through float negation
  for negative inputs and negated the reduced witness back.
- Updated `MISSING_INFRASTRUCTURE.md` from 72 to 71 active semantic gaps and
  made `VeltkampEvenN` the next target.

## Verification

- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Full `lake build`: passed all 3345 jobs; `Pff.lean` built in 94 seconds.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`, local
  target gate `pass`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
