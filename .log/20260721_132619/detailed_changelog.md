# Restore exact Pff `Underf_Err3`

Source commit: `7c52d5c4393effd06adfff5316573482b3ade814`

## Changes

- Added exact public `Underf_Err3` under the expanded upstream GenericDek
  section assumptions and exact `Underf_Err` predicate.
- Added a private closest-rounding lattice lemma that aligns an exact sum at
  the result exponent and combines `ClosestUlp` with the nonzero integer
  mantissa gap to force exact rounding.
- Added a private magnitude-transfer lemma for closest results bounded by a
  symmetric representable upper value.
- Restored the high-exponent exactness branch and the low-exponent combined
  `epsx + epsy` error branch without public `dExp`, totality, `boundR`,
  canonicality, finite-box, or conclusion premises.
- Updated `MISSING_INFRASTRUCTURE.md` from 55 to 54 active semantic gaps and
  made `Underf_Err3_bis` the next target.

## Verification

- Subscription harness attempt
  `.change_log/codex_attempt_20260721_123937`: classified failed after
  producing a draft with non-upstream `hvNum_gt` and `hBoundExp` premises.
- The draft was repaired manually; both extra public premises were removed.
- Upstream statement and proof shape checked against
  `/mnt2/users/kaile/hantao/flocq-upstream/src/Pff/Pff.v:16774`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with exit code 0.
- `git diff --check`: passed.
- Placeholder audit: all 11 categories reported zero findings.
- Direct live-hole search found no `sorry`, `axiom`, or `admit` declaration.
- Status report: 58 Lean files with zero `sorry`, `axiom`, `admit`, or
  placeholder findings.
- Full `lake build`: passed all 3345 jobs.
- Normalized classifier: `proved`, build `pass`, Coq alignment `checked`,
  local target gate `pass`, model `gpt-5.5`, provider `subscription`.
- `scripts/check_diff_trust.sh` is absent from this checkout.
