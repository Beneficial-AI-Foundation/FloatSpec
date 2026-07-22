# Restore exact Pff Boundedt4_aux theorem

## Summary

Restored the exact public Lean counterpart of upstream Flocq `Pff.v:Boundedt4_aux` and reduced the active semantic-gap ledger from 47 to 46.

## Implementation

- Added `Boundedt4_aux` with the same narrow Sec1 payload as `Boundedt4`.
- Applied exact `errorBoundedMult`, negated its witness, and expanded `x * y` through the split equalities.
- Preserved boundedness with `oppBounded` and derived `xprime.Fexp = x.Fexp + y.Fexp` from the multiplication-error witness plus definitional `Fopp` exponent preservation.
- Omitted `Hst1`/`Hst2`, `e`/`eeq`, half-scale bounds, and all split exponent premises.
- Introduced no totality, `boundR`, canonicity, conclusion, or weakening assumptions.

## Pipeline And Verification

- Required subscription pipeline attempt: `.change_log/codex_attempt_20260721_161331`.
- Normalized classifier: `.change_log/manual_attempt_20260721_Boundedt4_aux_proved/attempt.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Direct added-hole scan: no `sorry`, `axiom`, or `admit`.
- Placeholder audit and generated status report: zero findings; 58 Lean files with no `sorry`, `axiom`, or `admit`.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.

## Ledger

The active list now contains 46 entries, with `Boundedx1y1_aux` next.
