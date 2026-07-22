# Restore exact Pff VeltkampN

## Summary

- Restored exact public `VeltkampN` under only the upstream `VeltN`
  assumptions.
- Normalized the bounded closest outputs `p` and `q` into canonical
  representatives while preserving their real values.
- Reconstructed all three closest-rounding premises and reused exact
  `VeltkampN_aux` for the unchanged conclusion.
- Removed `VeltkampN` from the active semantic-gap ledger, leaving 73 active
  names and making `VeltkampEven_pos` the next target.

## Verification

- Focused `lake env lean FloatSpec/src/Pff/Pff.lean`: passed.
- `git diff --check`: passed.
- Placeholder audit: all 11 finding categories zero.
- Generated status: 58 Lean files, zero `sorry`, `axiom`, and `admit`.
- Full `lake build`: passed all 3345 jobs.
- `scripts/check_diff_trust.sh`: absent from this checkout.
- Normalized classifier: proved, build passed, Coq alignment checked, and
  local target gate passed.
