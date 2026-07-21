# Restore exact Pff Boundedt3 theorem

## Summary

Restored the exact public Lean counterpart of upstream Flocq `Pff.v:Boundedt3` and reduced the active semantic-gap ledger from 49 to 48.

## Implementation

- Added `Boundedt3` with the upstream Sec1 split/error payload.
- Reused the exact `Boundedt2` witness, subtracted `x2 * y1`, and applied `BoundedL` at exponent `s + x.Fexp + y.Fexp`.
- Preserved the exact upstream low-part premises `x2Exp : x.Fexp <= x2.Fexp` and `y2Exp : y.Fexp <= y2.Fexp`.
- Introduced no totality, `boundR`, canonicity, conclusion, or weakening assumptions.
- Reduced the remaining real residual to `-e + x2 * y2` and bounded it using `eLe`, `x2y2Le`, and `powerRZSumRle`.

## Pipeline And Verification

- Required subscription pipeline attempt: `.change_log/codex_attempt_20260721_153344`.
- Normalized classifier: `.change_log/manual_attempt_20260721_Boundedt3_proved/attempt.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Direct added-hole scan: no `sorry`, `axiom`, or `admit`.
- Placeholder audit and generated status report: zero findings; 58 Lean files with no `sorry`, `axiom`, or `admit`.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.

## Ledger

The active list now contains 48 entries, with `Boundedt4` next.
