# Detailed Changelog

## Summary
- Switched linter header comments from docstrings to plain block comments to keep imports valid.

## Details
- Updated `IdReturnLinter` and `HoareStyleLinter` top comments from `/-!` to `/-` so `public meta import` remains at the beginning of the file.

## Impact
- `lake build` was run and now gets past linter compilation. Remaining failures are in `FloatSpec/src/Calc/Operations.lean` (type mismatches / invalid specs / missing `Bind (Prod ℤ)`) and `FloatSpec/src/Core/Ulp.lean` (goal-state and WP errors around lines ~8973–9042).
