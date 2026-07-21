# Restore exact Pff Boundedt1 theorem

## Summary

Restored the exact public Lean counterpart of upstream Flocq `Pff.v:Boundedt1` and reduced the active semantic-gap ledger from 51 to 50.

## Implementation

- Added `Boundedt1` with the upstream Sec1 split/error payload.
- Kept `x1Exp` and `y1Exp`, which are required to bound the exponent of `Fminus r (Fmult x1 y1)`.
- Omitted unused `x2Exp` and `y2Exp` premises and introduced no totality, `boundR`, canonicity, conclusion, or weakening assumptions.
- Constructed the exact residual float and proved its magnitude and exponent bounds using `BoundedL`, `eLe`, `rExp`, `x2y2Le`, `x2y1Le`, `x1y2Le`, and `powerRZSumRle`.

## Pipeline And Verification

- Required subscription pipeline attempt: `.change_log/codex_attempt_20260721_144459`.
- Normalized classifier: `.change_log/manual_attempt_20260721_Boundedt1_proved/attempt.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Direct added-hole scan: no `sorry`, `axiom`, or `admit`.
- Placeholder audit and generated status report: zero findings; 58 Lean files with no `sorry`, `axiom`, or `admit`.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.

## Ledger

The active list now contains 50 entries, with `Boundedt2` next.
