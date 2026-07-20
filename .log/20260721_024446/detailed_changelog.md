# Restore Exact Pff eqGe Theorem

Commit: `c46fc460908e213677833b94b626850cc9358891`

## Summary

- Restored exact public `eqGe` with only the expanded upstream Flocq Veltkamp
  section assumptions and conclusion `(s : Int) + x.Fexp <= q.Fexp`.
- Implemented the upstream three-way mantissa split: a common two-error bound
  for large mantissas, a bounded three-term comparison float with concrete
  `ClosestMonotone` in the middle range, and exact representability at the
  minimal-normal boundary.
- Reduced each branch to a canonical comparison between the minimal-normal
  float at exponent `s + x.Fexp` and `Fopp q`, then applied
  `Fcanonic_Rle_Zle`.
- Updated the authoritative active-gap ledger from 82 to 81; `eqEqual` is
  next.

## Verification

- `lake env lean FloatSpec/src/Pff/Pff.lean`: passed with Lean exit status 0.
- `lake build`: passed, 3345 jobs.
- `scripts/status_report.sh --write`: 58 Lean files and zero sorry, axiom,
  admit, placeholder, weakening, or conclusion-as-hypothesis findings.
- `scripts/audit_placeholders.sh --json FloatSpec`: all 11 counters zero.
- `git diff --check`: passed.
- Active Pff ledger recount: 81.
- `scripts/check_diff_trust.sh`: absent from this checkout.

## Pipeline Record

The subscription harness attempt
`.change_log/codex_attempt_20260721_020438` correctly classified the original
target as blocked because the local helper surface did not package upstream's
full residual lower-bound comparison. The verified manual repair is classified
at `.change_log/manual_attempt_20260721_eqGe_proved/attempt.json` with
`result = proved`, `build = pass`, and `coq_alignment = checked`.
