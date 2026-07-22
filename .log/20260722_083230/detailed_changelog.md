# Detailed Changelog

## Commit

- Hash: f759a0cb
- Subject: Restore exact Pff Dekker2_aux theorem

## Changes

- Restored exact public `Dekker2_aux` with the full upstream Algo2 underflow-error payload.
- Normalized both nonzero canonical inputs under `Dekker_extendedBound`, reconstructed the extended-bound Dekker computation, and accumulated the exact product and residual underflow bounds.
- Derived total closestness and projector equalities from existing local infrastructure without adding semantic premises.
- Added only the faithful `0 <= b.dExp` representation invariant required by the local signed exponent field.
- Updated the authoritative semantic-gap ledger from 32 to 31; `Dekker2` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_080031` using `gpt-5.5` with high reasoning.
- Independent `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_Dekker2_aux_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
