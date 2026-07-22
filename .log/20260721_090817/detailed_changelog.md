# Restore exact Pff `Veltkamp_tail_aux`

Source commit: `8c7858a29a2a26cfa63c2192514ea8c0db92fe61`

## Changes

- Added exact public `Veltkamp_tail_aux` with the canonical-input and four
  upstream closest-rounding premises.
- Split the canonical input into normal and subnormal cases and reused exact
  `VeltkampN` and `VeltkampS` to construct an equal-value reduced witness.
- Proved the subtraction keeps the input exponent, then cancelled the positive
  radix scale in the residual bound to obtain the mantissa bound.
- Updated `MISSING_INFRASTRUCTURE.md` from 63 to 62 active semantic gaps and
  made `Veltkamp_tail2` the next target.

## Verification

- Subscription harness attempt: failed without changes or a build after Codex
  process/session persistence errors.
- Standalone scratch theorem: passed before transfer to the source module.
- Upstream statement and section assumptions: checked against
  `/tmp/flocq/src/Pff/Pff.v:16001`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Full `lake build`: passed all 3345 jobs; `Pff.lean` built in 100 seconds.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`,
  local target gate `pass`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
