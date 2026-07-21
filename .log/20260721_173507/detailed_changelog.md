# Restore exact Pff Boundedx1y2_aux theorem

## Summary

Restored the exact public Lean counterpart of upstream Flocq `Pff.v:Boundedx1y2_aux` and reduced the active semantic-gap ledger from 44 to 43.

## Implementation

- Added `Boundedx1y2_aux` with only the consumed Sec1 payload: radix and bound equations, `SGe`, `K`, `x1Exp`, `y2Exp`, `Fx1`, and `Fy2`.
- Constructed `Fmult x1 y2` and reused `Fmult_correct` for its represented real product.
- Combined the reduced `x1` mantissa bound and split `y2` mantissa bound, using `SGe` to fit their precision sum within `t`.
- Derived the bounded product exponent from `K`, `x1Exp`, and `y2Exp`, while preserving the exact multiplication exponent.
- Introduced no normality, rounding, residual, unrelated split-factor, `Hst1`/`Hst2`/`Hst3`, totality, `boundR`, canonicity, or conclusion assumptions.

## Pipeline And Verification

- Required subscription attempt: `.change_log/codex_attempt_20260721_172132`; `gpt-5.5`, high reasoning, proved with a passing local target gate.
- Normalized classifier: `.change_log/manual_attempt_20260721_Boundedx1y2_aux_proved/attempt.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check` and direct added-Lean-hole scan: passed.
- Placeholder audit and generated status report: zero findings; 58 Lean files with no `sorry`, `axiom`, or `admit`.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.

## Ledger

The active list now contains 43 entries, with `Boundedx1y2` next.
