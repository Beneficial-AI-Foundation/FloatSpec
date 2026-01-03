# Detailed Changelog

## Summary
- Moved `1 < beta` preconditions into explicit hypotheses for the ULP-at-zero specs.
- Added Verso roles in the `generic_format_ulp_0` and `generic_format_bpow_ge_ulp_0` docstrings.

## Details
- `round_UP_DN_ulp` now takes `hβ : 1 < beta` explicitly and uses `⦃⌜True⌝⦄` with a pure tuple.
- `generic_format_ulp_0` and `generic_format_bpow_ge_ulp_0` now wrap results in `pure` and use `⦃⌜True⌝⦄`.
- Doc comments now mark Coq/Lean identifiers using `{coq}`, `{name}`, `{lean}`, and `{lit}` roles.

## Impact
- Aligns Hoare specs with the project’s mvcgen precondition style.
- Reduces documentation lint noise around the ULP-at-zero lemmas.
