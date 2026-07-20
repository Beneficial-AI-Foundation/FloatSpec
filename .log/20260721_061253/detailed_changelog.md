# Restore exact Pff VeltkampN_aux

## Summary

- Restored exact public `VeltkampN_aux` under only the upstream `VeltN`
  assumptions.
- Excluded the zero case from normality and reused `Veltkamp_pos` for
  nonnegative inputs.
- Transported negative inputs, all three rounding premises, the residual, and
  the reduced witness through exact float-negation symmetry.
- Removed `VeltkampN_aux` from the active semantic-gap ledger, leaving 74
  active names and making `VeltkampN` the next target.

## Verification

- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Placeholder audit: all 11 finding categories zero.
- Generated status: 58 Lean files, zero `sorry`, `axiom`, and `admit`.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: absent from this checkout.
- Normalized classifier: proved, build passed, Coq alignment checked, and
  local target gate passed.
