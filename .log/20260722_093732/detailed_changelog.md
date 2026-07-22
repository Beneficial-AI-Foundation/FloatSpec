# Detailed Changelog

## Commit

- Hash: fb55b763
- Subject: Restore Twice_EvenClosest_Round

## Changes

- Restored exact public `Twice_EvenClosest_Round` with the complete upstream radix-two nearest-even payload.
- Proved doubled closestness for ordinary competitors by bounded halving.
- Proved the minimum-exponent odd-mantissa boundary directly from the precision mantissa bound, normal lower magnitude, and `ClosestUlp`.
- Derived the uniqueness branch through absolute-value closest monotonicity, canonical exponent comparison, and `Half_Closest_Round`.
- Updated the authoritative semantic-gap ledger from 30 to 29; `errorBoundedMultClosest_Can` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_090004` using `gpt-5.5` with high reasoning.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_Twice_EvenClosest_Round_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
