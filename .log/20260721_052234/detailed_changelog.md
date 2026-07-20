# Restore Exact Pff VeltkampEven1 Theorem

Commit: `afa6b7705bf8ee56b2344fdb4c5f7e136f57399c`

## Summary

- Restored exact public `VeltkampEven1` with every expanded upstream Veltkamp
  section assumption and the same-value reduced-format `EvenClosest` witness.
- Added a private candidate construction that represents the reconstructed
  high part at exponent `s + Fexp x`, normalizes strict mantissas, and uses an
  even minimal-normal representative at the mantissa boundary.
- Added the exact midpoint argument: align `p` and `q` at the reduced exponent,
  use `ClosestImplyEven_int` with `pDefEven` and symmetric `qDefEven`, and prove
  the candidate mantissa even.
- Used `ImplyClosestStrict2` for the non-midpoint uniqueness branch and retained
  the upstream `hxDefEven` context even though the proof does not consume it.
- Updated the authoritative active-gap ledger from 78 to 77;
  `VeltkampEven2` is next and total progress is 68 of 145.

## Verification

- `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with Lean exit status 0.
- `lake build`: passed, 3345 jobs; `Pff.lean` built in 94 seconds.
- `scripts/status_report.sh --write`: 58 Lean files and zero sorry, axiom,
  admit, placeholder, weakening, or conclusion-as-hypothesis findings.
- `scripts/audit_placeholders.sh --json FloatSpec`: all 11 counters zero.
- `git diff --check`: passed before commit and after the ledger update.
- Active Pff ledger recount: 77.
- `scripts/check_diff_trust.sh`: absent from this checkout.

## Pipeline Record

The subscription harness attempt
`.change_log/codex_attempt_20260721_043449` made no source changes and did not
run a build. The manual repair completed the exact public theorem. The
normalized classifier is
`.change_log/manual_attempt_20260721_VeltkampEven1_proved/attempt.json`,
recording `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate.
