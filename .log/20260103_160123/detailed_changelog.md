# Detailed Changelog

## Summary
- Simplified `pred_pos` branch rewrites using direct `simp` in `generic_format_pred_pos`.
- Fixed a malformed `{given}` role backtick in the `generic_format_ulp_0` doc comment.

## Details
- Replaced manual `unfold`/`rw`/`simp` sequences with a single `simp` in boundary and generic branches.
- Corrected the role markup to avoid a syntax error in the docstring.

## Impact
- Removes tactic failures in `generic_format_pred_pos` and restores parsing of the ULP-at-zero docstring.
