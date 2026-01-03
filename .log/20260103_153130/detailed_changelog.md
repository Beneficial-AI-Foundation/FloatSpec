# Detailed Changelog

## Summary
- Refactored Calc/Operations to remove Id-style binds from definitions and wrap pure results explicitly in specs.

## Details
- `Falign`, `Falign_exp`, `Fplus`, `Fexp_Fplus`, and `Fminus` are now pure definitions (no `pure`/`>>=`).
- Hoare specs now wrap pure programs with `(pure ...) : Id _` to keep mvcgen usage explicit.
- Cleaned `simp` calls to remove `bind` references.

## Impact
- `FloatSpec/src/Calc/Operations.lean` now builds; remaining build failures are in `FloatSpec/src/Core/Ulp.lean`.
