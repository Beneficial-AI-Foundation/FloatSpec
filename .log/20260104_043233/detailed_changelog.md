# Detailed Changelog

## Summary
- Clarified Verso doc roles in `Round_pred` and `SimprocGenericFmt` to make identifiers resolvable by Lean.

## Details
- Rewrote the MonotoneImplications doc comment in `Round_pred` with `{given}` and `{name}` roles for the binder and predicate identifiers.
- Updated `SimprocGenericFmt` docs to use `{name}` roles for `cexp`, `scaled_mantissa`, and `Id`/`pure` references.

## Impact
- Reduces “code element could be more specific” warnings and improves hover/go-to-definition in doc comments.
