# Restore exact Pff `VeltkampEven`

Source commit: `38dce9071504f4e07efc5a4912d0e7ce6d487b43`

## Changes

- Added exact public `VeltkampEven` for any bounded input and the three
  upstream nearest-even rounding premises.
- Normalized the input, proved its canonical representative, and split normal
  versus subnormal cases.
- Delegated to exact `VeltkampEvenN` and `VeltkampEvenS`, rewriting only by
  `FnormalizeCorrect`.
- Updated `MISSING_INFRASTRUCTURE.md` from 64 to 63 active semantic gaps and
  made `Veltkamp_tail_aux` the next target.

## Verification

- Subscription harness attempt: failed without changes or a build after Codex
  process/session persistence errors.
- Standalone scratch theorem: passed before transfer to the source module.
- Upstream statement and section assumptions: checked against
  `/tmp/flocq/src/Pff/Pff.v:15944`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Full `lake build`: passed all 3345 jobs; `Pff.lean` built in 98 seconds.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`,
  local target gate `pass`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
