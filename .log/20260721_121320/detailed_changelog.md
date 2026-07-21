# Restore exact Pff `Underf_Err2_aux`

Source commit: `6df4759195b7a818634ce12cab7280ad14e99d79`

## Changes

- Added exact public `Underf_Err2_aux` under the expanded upstream
  GenericDek section assumptions and exact `Underf_Err` predicate.
- Added a private canonical magnitude-gap lemma proving that a result strictly
  above the old minimum exponent has one ulp plus the minimum-normal magnitude
  available.
- Added the private arbitrary-real closest-transfer bridge that the required
  harness identified as missing.
- Constructed the extended-bound closest result internally with the closed
  `RND_Closest` correctness stack and proved the exact `3/4` minimum-unit
  bound from the original half-unit and extended quarter-unit estimates.
- Updated `MISSING_INFRASTRUCTURE.md` from 57 to 56 active semantic gaps and
  made `Underf_Err2` the next target.

## Verification

- Subscription harness attempt
  `.change_log/codex_attempt_20260721_114333`: classified the exact target as
  blocked without source edits on the arbitrary-real closest-transfer bridge.
- The blocker was repaired manually without adding totality, finite-box,
  conclusion, or other public premises.
- Upstream statement and proof shape: checked against
  `/mnt2/users/kaile/hantao/flocq-upstream/src/Pff/Pff.v:16610`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with exit code 0.
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
