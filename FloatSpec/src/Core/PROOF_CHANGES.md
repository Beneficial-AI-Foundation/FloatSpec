# Proof Changes Log for Raux.lean

This log records intentional, minimal specification adjustments made during proof fixing.

## mag_le (monotonicity of `mag`)

- Location: `FloatSpec/src/Core/Raux.lean`
- Original spec (inaccurate under current `mag` definition):
  - Precondition: `1 < beta ∧ |x| ≤ |y|`
  - Claim: `mag beta x ≤ mag beta y`
- Issue: With `mag` defined as `if x = 0 then 0 else ⌈log(|x|)/log β⌉`, the statement fails when `x = 0` and `0 < |y| < 1`. Example (β = 2): `mag 0 = 0` but `mag 0.5 = -1`, so `0 ≤ -1` is false.
- Minimal fix: Strengthen the precondition to exclude the x = 0 counterexample:
  - New precondition: `1 < beta ∧ x ≠ 0 ∧ |x| ≤ |y|`.
  - This also implies `y ≠ 0`, since `|x| > 0` and `|x| ≤ |y|`.
- Rationale: Preserves intended monotonicity behavior of `⌈log(|·|)/log β⌉` on positive reals while respecting the special case `mag 0 = 0`.

