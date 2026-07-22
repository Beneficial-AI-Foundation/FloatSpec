# Restore exact Pff `BoundedL`

Source commit: `7513602b6ce177f570b4e7a41874c8dbb06362de`

## Changes

- Added exact public `BoundedL` under the expanded upstream GenericDek section
  assumptions.
- Constructed the equal-value witness by shifting the mantissa while lowering
  its exponent to the requested `e`.
- Cancelled the positive `radix ^ e` scale from the strict real-magnitude
  premise to establish the exact `Fbounded b` mantissa bound.
- Preserved the requested exponent and minimum-exponent side condition.
- Updated `MISSING_INFRASTRUCTURE.md` from 60 to 59 active semantic gaps and
  made `Closestbbext` the next target.

## Verification

- Subscription harness attempt
  `.change_log/codex_attempt_20260721_100600`: proved the theorem and ran its
  nested focused check, audits, and full build.
- Upstream statement and section assumptions: checked against
  `/mnt2/users/kaile/hantao/flocq-upstream/src/Pff/Pff.v:16329`.
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
