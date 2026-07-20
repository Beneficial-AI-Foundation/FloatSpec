# Restore Exact Pff Veltkamp_aux Theorem

Commit: `177ea9381896dacf33706ae91251c10a62c1d18a`

## Summary

- Restored exact public `Veltkamp_aux` with the expanded upstream Flocq
  Veltkamp section assumptions and the full conjunction/existential payload.
- Proved the half-ulp residual bound from `eqEqual`, `ClosestUlp`,
  `ClosestExp`, and `hxExact`.
- Constructed the reduced `t - s` representative by bounding the exact
  `Fplus p q` mantissa, applying `FboundedMbound`, and normalizing it.
- Proved reduced-format closestness with `Veltkamp_aux_aux` and
  `ImplyClosest`, then recovered the required exponent lower bound with
  `Fcanonic_Rle_Zle`.
- Updated the authoritative active-gap ledger from 79 to 78;
  `VeltkampEven1` is next.

## Verification

- `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with Lean exit status 0.
- `lake build`: passed, 3345 jobs.
- `scripts/status_report.sh --write`: 58 Lean files and zero sorry, axiom,
  admit, placeholder, weakening, or conclusion-as-hypothesis findings.
- `scripts/audit_placeholders.sh --json FloatSpec`: all 11 counters zero.
- `git diff --check`: passed.
- Active Pff ledger recount: 78.
- `scripts/check_diff_trust.sh`: absent from this checkout.

## Pipeline Record

The subscription harness attempt
`.change_log/codex_attempt_20260721_035252` correctly returned blocked without
retaining source changes and identified the missing reduced-bound sum witness.
The manual repair completed that exact witness and public theorem. The
independently verified normalized classifier is
`.change_log/manual_attempt_20260721_Veltkamp_aux_proved/attempt.json`,
recording `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate.
