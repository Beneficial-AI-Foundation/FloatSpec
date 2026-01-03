# Detailed Changelog

## Summary
- Adjusted linter file headers to restore `module` placement for `public meta import` usage.

## Details
- Reordered top-of-file structure in `IdReturnLinter`/`HoareStyleLinter` to match the existing linter pattern.

## Impact
- `lake build` after this commit still failed: Lean reported `invalid 'import' command` because the linter doc comments were `/-!` (docstrings) before imports, and a PANIC occurred. The next commit changes them to non-doc comments.
