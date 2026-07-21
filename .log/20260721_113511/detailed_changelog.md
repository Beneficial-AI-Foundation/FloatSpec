# Restore exact Pff `Underf_Err1`

Source commit: `f10e179af7820b9602516c530c39766db21061ca`

## Changes

- Added exact public `Underf_Err1` under the expanded upstream GenericDek
  section assumptions and the existing exact `Underf_Err` predicate.
- Added private boundedness, minimum-normal magnitude, and closestness helpers
  needed to reproduce the upstream underflow argument without extra public
  premises.
- Proved exactness when the input exponent is above the original minimum and
  the exact half-minimum-unit error bound in the underflow branch using
  normalization, `Fcanonic_Rle_Zle`, and `ClosestUlp`.
- Updated `MISSING_INFRASTRUCTURE.md` from 58 to 57 active semantic gaps and
  made `Underf_Err2_aux` the next target.

## Verification

- Subscription harness attempt
  `.change_log/codex_attempt_20260721_110255`: proved the theorem and ran its
  nested focused check, audits, and full build.
- Upstream statement and section assumptions: checked against
  `/mnt2/users/kaile/hantao/flocq-upstream/src/Pff/Pff.v:16555`.
- Independent focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with
  exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Direct live-hole search found no `sorry`, `axiom`, or `admit`
  declaration.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Full `lake build`: passed all 3345 jobs.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`,
  local target gate `pass`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
