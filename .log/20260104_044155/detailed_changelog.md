# Detailed Changelog

## Summary
- Clarified Verso doc roles for several Round_pred doc blocks to eliminate “code element could be more specific” warnings.

## Details
- Added `{given -show}` declarations for the local binders in the round-down/up negation, DN/UP split, and nearest-rounding sections.
- Replaced backticked identifiers and expressions with `{lean}` and `{name}` roles so LSP can resolve them inside doc comments.

## Impact
- Improves doc comment hover/go-to-definition and reduces Verso role warnings in the updated sections.
