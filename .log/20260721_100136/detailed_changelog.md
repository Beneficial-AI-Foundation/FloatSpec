# Restore exact Pff `VeltkampU`

Source commit: `38214439bbb7592ba004e22f6b2672066d0cb9b9`

## Changes

- Added exact public `VeltkampU` with the upstream canonical-input and four
  closest-rounding premises.
- Combined `VeltkampN` and `VeltkampS` to construct the reduced-bound high
  witness and preserve the conditional normal exponent bound.
- Reused `Veltkamp_tail_aux` to prove the residual is directly bounded by the
  `s`-digit split format and keeps exponent `x.Fexp`.
- Used closest-rounding minimality to identify the residual with `tx`, yielding
  both the exact decomposition and equal-value tail witness.
- Updated `MISSING_INFRASTRUCTURE.md` from 61 to 60 active semantic gaps and
  made `BoundedL` the next target.

## Verification

- Subscription harness attempt
  `.change_log/codex_attempt_20260721_094158`: proved the theorem and ran its
  nested focused check, audits, and full build.
- Upstream statement and section assumptions: checked against
  `/tmp/flocq/src/Pff/Pff.v:16270`.
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
