# Detailed Changelog

## Summary
- Added Ulp-side proof cleanups around `pred_ulp_0` boundary handling and UP/DN negation duality to reduce immediate errors.
- Introduced lightweight simprocs for `Ztrunc`/`mag` in `SimprocRaux` and `wp`/`Id` reductions in `SimprocWP` to unblock Hoare triple simplification.
- Added `FloatSpec.VersoExt` to register `{coq}` role imports in files that reference Coq identifiers.

## Details
- Ulp: removed over-aggressive simplification around `mag_le` (now apply the Hoare triple directly), refactored `pred_ulp_0_theorem` boundary proof to avoid simp loops, and fixed `round_UP_choose_eq_neg_round_DN_choose` to use the Rnd_UP/DN specs correctly.
- Ulp: rewrote `error_le_half_ulp` to use a `pure` Id program instead of a `do` block, eliminating WP inference failures.
- Simprocs: `SimprocRaux` now simplifies `Ztrunc (-x)` to `-Ztrunc x` without `Id.run`, and `SimprocWP` exposes Id `wp`/`PostCond.noThrow`/`Id.run` reductions.

## Impact
- `lake build` was run; it fails in `FloatSpec/src/Calc/Operations.lean` and `FloatSpec/src/Core/Ulp.lean` (type mismatches/WP synthesis).
- Ulp error count is reduced, but several mid/late-file proofs still require cleanup or sorries.
