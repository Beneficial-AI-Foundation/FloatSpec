# Restore exact Pff Boundedx2y1_aux theorem

## Summary

Restored the exact public Lean counterpart of upstream Flocq `Pff.v:Boundedx2y1_aux` and reduced the active semantic-gap ledger from 42 to 41.

## Implementation

- Added `Boundedx2y1_aux` with only the consumed Sec1 payload: radix and bound equations, `SGe`, `K`, `x2Exp`, `y1Exp`, `Fx2`, and `Fy1`.
- Constructed `Fmult x2 y1` and reused `Fmult_correct` for its represented real product.
- Combined the split `x2` mantissa bound and reduced `y1` mantissa bound, using `SGe` to fit their precision sum within `t`.
- Derived the bounded product exponent from `K`, `x2Exp`, and `y1Exp`, while preserving the exact multiplication exponent.
- Introduced no normality, rounding, residual, unrelated component, `Hst1`/`Hst2`/`Hst3`, totality, `boundR`, canonicity, or conclusion assumptions.

## Pipeline And Verification

- Required subscription attempt: `.change_log/codex_attempt_20260721_175413`; `gpt-5.5`, high reasoning, proved with a passing local target gate.
- Normalized classifier: `.change_log/manual_attempt_20260721_Boundedx2y1_aux_proved/attempt.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check` and direct added-Lean-hole scan: passed.
- Placeholder audit and generated status report: zero findings; 58 Lean files with no `sorry`, `axiom`, or `admit`.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.

## Ledger

The active list now contains 41 entries, with `Boundedx2y1` next.
