# Detailed Changelog

## Summary
- Documented rounding predicate re-exports and nearest-choice helpers in Generic_fmt.
- Proved `generic_inclusion_mag`, showing format inclusion under the canonical exponent bound.

## Details
- Added docstrings for `Rnd_*_pt` abbrevs, `roundR`, `ZnearestA`, `Znearest0`, and `Znearest_le_ceil_check`.
- Added a docstring for `Monotone_exp.mono` and clarified wording in the rounding section header.
- Implemented the `generic_inclusion_mag` proof by rewriting the canonical float witness from `generic_format` and applying `generic_format_F2R'`.

## Impact
- Reduces docstring linter warnings for public declarations in `Generic_fmt.lean`.
- Removes a core `sorry`, enabling downstream inclusion lemmas to proceed.
