# Restore exact Pff Boundedx1y1_aux theorem

## Summary

Restored the exact public Lean counterpart of upstream Flocq `Pff.v:Boundedx1y1_aux` and reduced the active semantic-gap ledger from 46 to 45.

## Implementation

- Added `Boundedx1y1_aux` with the exact consumed Sec1 payload: radix facts, original product exponent lower bound, split leading exponents, two reduced bounds, and `t <= 2 * s`.
- Constructed `Fmult x1 y1`; reused `Fmult_correct` for the represented real product and retained the exact product exponent.
- Combined the two reduced mantissa bounds and `t <= 2 * s` to prove the product mantissa lies below the original `b.vNum` bound.
- Used the split exponent premises and original product lower bound to establish the bounded product exponent.
- Introduced no normality, rounding, residual, `Fx2`/`Fy2`, totality, `boundR`, canonicity, conclusion, or weakening assumptions.

## Pipeline And Verification

- Required subscription pipeline attempt: `.change_log/codex_attempt_20260721_163238` (proved after an approximately 18-minute provider run).
- Normalized classifier: `.change_log/manual_attempt_20260721_Boundedx1y1_aux_proved/attempt.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Direct added-hole scan: no `sorry`, `axiom`, or `admit`.
- Placeholder audit and generated status report: zero findings; 58 Lean files with no `sorry`, `axiom`, or `admit`.
- Full `lake build`: passed all 3345 jobs after recompiling the large `Pff.lean` and downstream Pff modules.
- `scripts/check_diff_trust.sh`: unavailable in this repository.

## Ledger

The active list now contains 45 entries, with `Boundedx1y1` next.
