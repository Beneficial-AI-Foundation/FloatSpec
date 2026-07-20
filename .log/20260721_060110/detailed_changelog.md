# Restore exact Pff Veltkamp_pos

## Summary

- Restored exact public `Veltkamp_pos` under only the upstream `VeltN`
  section assumptions.
- Added a private first-normal separation lemma for canonical closest results.
- Proved `p` normal from its positive scaled input and `q` normal through the
  upstream two-exponent shift and the canonical float `Fopp q`.
- Reused exact `Veltkamp_aux` for the residual bound and reduced closest
  witness, preserving the upstream conclusion.
- Removed `Veltkamp_pos` from the active semantic-gap ledger, leaving 75
  active names and making `VeltkampN_aux` the next target.

## Verification

- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Placeholder audit: all 11 finding categories zero.
- Generated status: 58 Lean files, zero `sorry`, `axiom`, and `admit`.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: absent from this checkout.
- Normalized classifier: proved, build passed, Coq alignment checked, and
  local target gate passed.
