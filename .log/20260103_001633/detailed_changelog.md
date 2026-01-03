# Detailed Changelog

## Summary
- Fixed `mag_upper_bound`/`mag_lower_bound` usage to pass explicit hypotheses and unwrap Hoare triples correctly.
- Repaired an indentation/layout issue that was accidentally nesting unrelated goals inside the `hulp_pos` proof.

## Details
- Updated several blocks in `Ulp` to apply `mag_*_bound` with `hβ`/`hx_ne` arguments and `True.intro`, then rewrite via `hb`/`he`.
- Dedented `hsucc_pos'` and subsequent reasoning so it is no longer part of the `hulp_pos` proof.
- Adjusted the later `generic_format_pred_aux2` branch to use the same `mag_lower_bound` calling convention.

## Impact
- Local diagnostics around the affected ranges clear the earlier application/indentation errors.
- Larger Ulp proof obligations remain; the main failing blocks now are deeper in `generic_format_pred_aux2` and later sections.
