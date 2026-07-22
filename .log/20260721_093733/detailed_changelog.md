# Restore exact Pff `Veltkamp_tail2`

Source commit: `0f0da7c959c86cc637de9d7b87acb61abf18e810`

## Changes

- Added exact public `Veltkamp_tail2` with the upstream binary-radix,
  bounded-input, and four closest-rounding premises.
- Normalized the input and reused exact `Veltkamp_tail_aux` to obtain the
  residual exponent and mantissa bound.
- Used `FboundedMbound2` and the binary identity
  `2 ^ s / 2 = 2 ^ (s - 1)` to construct the exact tail witness in the
  `s - 1` split bound while preserving the exponent lower bound.
- Used closest-rounding minimality to identify the constructed residual with
  `tx` by represented value.
- Updated `MISSING_INFRASTRUCTURE.md` from 62 to 61 active semantic gaps and
  made `VeltkampU` the next target.

## Verification

- Subscription harness attempt
  `.change_log/codex_attempt_20260721_091300`: proved the theorem and ran its
  nested focused check, audits, and full build.
- Upstream statement and section assumptions: checked against
  `/tmp/flocq/src/Pff/Pff.v:16157`.
- Independent focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with
  exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Direct live-hole search found no `sorry`, `axiom`, or `admit` declaration.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Full `lake build`: passed all 3345 jobs.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`,
  local target gate `pass`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
