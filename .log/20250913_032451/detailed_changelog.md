# Detailed Changelog

## Summary
- Completed the proof for `scaled_mantissa_lt_bpow` in `FloatSpec/src/Core/Round_generic.lean`.
- Updated `CLAUDE.md` with a concrete proof-writing playbook, practical FloatSpec tips, and clarified that Lean LSP MCP tools are the primary fast feedback loop.

## Motivation
- The theorem previously had brittle steps around converting `log` inequalities to powers and handling `abs` with scaling factors; this could trigger type/shape mismatches in Lean.
- The documentation did not fully reflect the current developer flow (MCP LSP tools available) and repeatable proof strategies used in the repo.

## Technical Notes
- Rewrote the inequality chain to:
  1. Establish `log |x| ≤ log (β^e)` using the ceiling characterization of `mag`.
  2. Use `Real.log_le_iff_le_exp` and `Real.log_zpow` to move to exponentials, then explicitly show `exp (e * log β) = β^e` via `Real.exp_log`.
  3. Multiply by a nonnegative factor `((β : ℝ)^c)⁻¹` and collapse with `zpow_mul_sub` to reach `β^(e - c)`.
- Avoided fragile `simp` rewrites between `exp (e*log β)` and `β^e`.
- Handled absolute values by rewriting `|β^(-c)|` as `|(β^c)⁻¹| = |β^c|⁻¹` and used nonnegativity of `β^c`.

## Files Changed
- `FloatSpec/src/Core/Round_generic.lean`: finalized `scaled_mantissa_lt_bpow` proof.
- `CLAUDE.md`: added sections on proof playbook, FloatSpec-specific tips, plan/preambles guidance, and quality bar.

## Expected Impact
- Stronger, more maintainable proof avoiding brittle tactics.
- Clearer contributor guidelines to keep the feedback loop tight and use LSP MCP tools effectively.
