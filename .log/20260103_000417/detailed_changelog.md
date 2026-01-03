# Detailed Changelog

## Summary
- Introduced project-specific Hoare/Id linters and enabled weak linter options in `lakefile.lean`.
- Wired `FloatSpec/Linter.lean` to register the new linters.

## Details
- Added `FloatSpec/Linter/HoareStyleLinter.lean` to warn on non-`True` preconditions and trivial postconditions in Hoare triples.
- Expanded `FloatSpec/Linter/IdReturnLinter.lean` to warn when `def`/`abbrev` returns `Id _`.
- Enabled `weak.linter.*` settings in `lakefile.lean` for project-wide defaults.

## Impact
- `lake build` was run after this commit and failed because the linter module headers were misordered (Lean error: `public meta import` without a `module`). Follow-up commits address this.
