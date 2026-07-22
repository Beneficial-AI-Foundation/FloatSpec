# Detailed Changelog

## Commit

- Hash: efa2efdb
- Subject: Restore exact cases theorem

## Changes

- Restored exact public `«cases»` with the upstream Discriminant7 zero-or-no-underflow disjunction.
- Preserved float-typed `dp` and `dq`, their conditional boundedness and residual equations, and all section rounding hypotheses.
- Derived the `p`, `q`, `v`, `t`, `u`, and branch-dependent `d` magnitude bounds from the current exact rounding and exponent helper stack.
- Replaced the superseded July 16 blocker classification and updated the authoritative semantic-gap ledger from 28 to 27; `xLe2y_aux1` is next.

## Verification

- Required subscription harness: `.change_log/codex_attempt_20260722_104151` using `gpt-5.5` with high reasoning.
- The harness proof strategy was normalized to restore the exact name and upstream float-typed `dp`/`dq` payload.
- Independent `lake env lean -DmaxErrors=20 FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Added-Lean-hole scan: passed.
- `scripts/audit_placeholders.sh --json FloatSpec`: zero findings.
- `scripts/status_report.sh --write`: zero holes and zero placeholder findings.
- `lake build`: passed all 3345 jobs.
- Correct-line classifier: `.change_log/manual_attempt_20260722_cases_proved/attempt.json`.
- `scripts/check_diff_trust.sh`: unavailable in this repository.
