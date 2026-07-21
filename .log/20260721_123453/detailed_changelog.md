# Restore exact Pff `Underf_Err2`

Source commit: `cff9f5d2503daa5904cf7e62cee49fe900e98673`

## Changes

- Added exact public `Underf_Err2` under the expanded upstream GenericDek
  section assumptions and exact `Underf_Err2_aux` theorem.
- Normalized the original closest result internally and derived canonicity,
  boundedness, closestness, and represented-value preservation without adding
  a public canonicality premise.
- Applied `Underf_Err2_aux` to the canonical normalized representative and
  transported the exact `3/4` underflow-error payload back to the original
  representation.
- Updated `MISSING_INFRASTRUCTURE.md` from 56 to 55 active semantic gaps and
  made `Underf_Err3` the next target.

## Verification

- Subscription harness attempt
  `.change_log/codex_attempt_20260721_122007`: proved the exact target.
- Upstream statement and proof shape checked against
  `/mnt2/users/kaile/hantao/flocq-upstream/src/Pff/Pff.v:16750`.
- Independent focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with
  exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Direct live-hole search found no `sorry`, `axiom`, or `admit` declaration.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Independent full `lake build`: passed all 3345 jobs.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`,
  local target gate `pass`, model `gpt-5.5`, provider `subscription`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
