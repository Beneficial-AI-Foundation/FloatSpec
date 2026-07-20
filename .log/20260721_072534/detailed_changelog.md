# Restore exact Pff `EvenClosestbplusb`

Source commit: `7d71adebed73fcde6b6a2737338294347a3c93cc`

## Changes

- Added exact public `EvenClosestbplusb`, restricting nearest-even closestness
  from `plusExp b0 t` to `b0` with the upstream premises and no additions.
- Reused `Closestbplusb` for ordinary closestness and canonical uniqueness to
  transfer normalized parity in the normal branch.
- Used `ClosestUlp` and minimum-unit discreteness to force exactness and
  uniqueness in the subnormal branch.
- Updated `MISSING_INFRASTRUCTURE.md` from 69 to 68 active semantic gaps and
  made `ClosestClosest` the next target.

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
