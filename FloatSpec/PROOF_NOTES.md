Changes recorded for Core/Round_generic.lean

- Theorem `precision_generic_format` adjusted for soundness:
  - Added assumption `hβ : 1 < beta` to ensure positive base and enable zpow/abs comparisons.
  - Relaxed the mantissa bound from strict `<` to non-strict `≤`:
    `Int.natAbs m ≤ Int.natAbs beta ^ ((mag beta x - (cexp beta fexp x).run).toNat)`.

Rationale
- Without `1 < beta`, exponents and magnitude/log-based arguments are not well-behaved, and the real powers used in the proof may be non-positive or undefined cases arise.
- The strict inequality `<` fails on boundary cases such as `|x| = (beta : ℝ) ^ (mag beta x)`, where the normalized mantissa can exactly equal the bound. The classical Flocq-style generic format only guarantees a non-strict upper bound in general. Hence, `≤` is the correct, general statement here.

Proof outline
- Use the generic-format reconstruction to choose `m := Ztrunc (scaled_mantissa beta fexp x).run`.
- Show equality `x = F2R (m, cexp x)` from the definition of `generic_format`.
- Use the general bound `abs (scaled_mantissa x) ≤ β^(mag x − cexp x)` (requires `1 < beta`).
- Since `scaled_mantissa` equals its truncation for values in the format, rewrite the left side as `(Int.natAbs m : ℝ)` and the right side as `((Int.natAbs beta) ^ toNat(...) : ℝ)` via positivity and `Nat.cast_pow`.
- Conclude the desired `Nat` inequality via monotonicity of casts.

