# Restore exact Pff Boundedt4 theorem

## Summary

Restored the exact public Lean counterpart of upstream Flocq `Pff.v:Boundedt4` and reduced the active semantic-gap ledger from 48 to 47.

## Implementation

- Added `Boundedt4` with the narrower Sec1 payload actually consumed upstream.
- Required only radix/bound/precision data, `SLe`/`SGe`, normality of `x` and `y`, the product exponent lower bound, closestness, and the two split equalities.
- Omitted `Hst1`/`Hst2`, `e`/`eeq`, half-scale bounds, and all split exponent premises.
- Applied exact `errorBoundedMult`, negated its witness, expanded `x * y` through the split equalities, and preserved boundedness with `oppBounded`.
- Introduced no totality, `boundR`, canonicity, conclusion, or weakening assumptions.

## Pipeline And Verification

- Required subscription pipeline attempt: `.change_log/codex_attempt_20260721_155424`.
- Normalized classifier: `.change_log/manual_attempt_20260721_Boundedt4_proved/attempt.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Direct added-hole scan: no `sorry`, `axiom`, or `admit`.
- Placeholder audit and generated status report: zero findings; 58 Lean files with no `sorry`, `axiom`, or `admit`.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.

## Ledger

The active list now contains 47 entries, with `Boundedt4_aux` next.
