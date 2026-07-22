# Restore exact Pff Boundedx1y1 theorem

## Summary

Restored the exact public Lean counterpart of upstream Flocq `Pff.v:Boundedx1y1` and reduced the active semantic-gap ledger from 45 to 44.

## Implementation

- Added `Boundedx1y1` with exactly the same consumed Sec1 payload as `Boundedx1y1_aux`.
- Eliminated the exact auxiliary theorem and projected its real-value and boundedness witnesses.
- Dropped only the auxiliary exponent-equality conjunct, matching the upstream Coq wrapper.
- Introduced no additional premise, helper-only payload, weakening, or conclusion assumption.

## Pipeline And Verification

- Initial subscription attempt: `.change_log/codex_attempt_20260721_170359`; no changes because the installed CLI rejected its configured `gpt-5.6-sol` default as requiring a newer CLI.
- Compatible subscription attempt: `.change_log/codex_attempt_20260721_170512`; `gpt-5.5`, high reasoning, proved with a passing local target gate.
- Normalized classifier: `.change_log/manual_attempt_20260721_Boundedx1y1_proved/attempt.json`.
- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check` and direct added-hole scan: passed.
- Placeholder audit and generated status report: zero findings; 58 Lean files with no `sorry`, `axiom`, or `admit`.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: unavailable in this repository.

## Ledger

The active list now contains 44 entries, with `Boundedx1y2_aux` next.
