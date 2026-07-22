# Restore exact Pff Boundedt2 theorem

## Summary

Restored the exact public Lean counterpart of upstream Flocq `Pff.v:Boundedt2` and reduced the active semantic-gap ledger from 50 to 49.

## Implementation

- Added `Boundedt2` with the upstream Sec1 split/error payload.
- Reused the exact `Boundedt1` witness, subtracted `x1 * y2`, and applied `BoundedL` at exponent `s + x.Fexp + y.Fexp`.
- Used the exact upstream premise `y2Exp : y.Fexp <= y2.Fexp`; the pipeline-generated stronger premise `s + y.Fexp <= y2.Fexp` was rejected and manually repaired.
- Omitted unused `x2Exp` and introduced no totality, `boundR`, canonicity, conclusion, or weakening assumptions.
- Proved the residual magnitude bound using `eLe`, `x2y1Le`, `x2y2Le`, and `powerRZSumRle`.

## Pipeline And Verification

- Required subscription pipeline attempt: `.change_log/codex_attempt_20260721_151121`.
- Normalized classifier: `.change_log/manual_attempt_20260721_Boundedt2_proved/attempt.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed after exact-premise repair.
- `git diff --check`: passed.
- Direct added-hole scan: no `sorry`, `axiom`, or `admit`.
- Placeholder audit and generated status report: zero findings; 58 Lean files with no `sorry`, `axiom`, or `admit`.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.

## Ledger

The active list now contains 49 entries, with `Boundedt3` next.
