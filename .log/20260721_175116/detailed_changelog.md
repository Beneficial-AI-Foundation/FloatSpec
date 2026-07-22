# Restore exact Pff Boundedx1y2 theorem

## Summary

Restored the exact public Lean counterpart of upstream Flocq `Pff.v:Boundedx1y2` and reduced the active semantic-gap ledger from 43 to 42.

## Implementation

- Added `Boundedx1y2` with exactly the same consumed Sec1 payload as `Boundedx1y2_aux`.
- Eliminated the exact auxiliary theorem and projected its real-value and boundedness witnesses.
- Dropped only the auxiliary exponent-equality conjunct, matching the upstream Coq wrapper.
- Introduced no additional premise, helper-only payload, weakening, or conclusion assumption.

## Pipeline And Verification

- Required subscription attempt: `.change_log/codex_attempt_20260721_173809`; `gpt-5.5`, high reasoning, proved with a passing local target gate.
- Normalized classifier: `.change_log/manual_attempt_20260721_Boundedx1y2_proved/attempt.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check` and direct added-Lean-hole scan: passed.
- Placeholder audit and generated status report: zero findings; 58 Lean files with no `sorry`, `axiom`, or `admit`.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.

## Ledger

The active list now contains 42 entries, with `Boundedx2y1_aux` next.
