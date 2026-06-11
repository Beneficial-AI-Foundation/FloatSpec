# Missing Flocq Infrastructure

This document names the remaining infrastructure that blocks a product-grade
FloatSpec/Flocq translation. It focuses on concrete theorem and definition
names rather than broad labels.

## Calc/Round Placeholder Section

`FloatSpec/src/Calc/Round.lean` still contains a Coq theorem compatibility
section:

- Section: `CoqTheoremsPlaceholders`
- Audit namespace: `Audit`
- Example placeholder theorem: `truncate_aux_comp`

`truncate_aux_comp` is a representative example: it currently proves only a
tautological equality about both sides being their own expanded computations,
not the real Coq composition theorem for truncation.

Other names in this section that should be audited against Coq `Round.v`:

- `cexp_inbetween_float`
- `cexp_inbetween_float_loc_Exact`
- `inbetween_float_round`
- `inbetween_float_round_sign`
- `inbetween_int_DN`
- `inbetween_float_DN`
- `inbetween_int_DN_sign`
- `inbetween_float_DN_sign`
- `inbetween_int_UP`
- `inbetween_float_UP`
- `inbetween_int_ZR`
- `inbetween_float_ZR`
- `inbetween_int_N`
- `inbetween_int_N_sign`
- `inbetween_int_NE`
- `inbetween_float_NE`
- `inbetween_int_NE_sign`
- `inbetween_float_NE_sign`
- `inbetween_int_NA`
- `inbetween_float_NA`
- `inbetween_int_NA_sign`
- `inbetween_float_NA_sign`
- `truncate_aux_comp`
- `truncate_0`
- `generic_format_truncate`
- `truncate_correct_format`
- `truncate_correct_partial`
- `truncate_correct`
- `round_any_correct`
- `round_trunc_any_correct`
- `round_sign_any_correct`
- `round_trunc_sign_any_correct`
- `truncate_FIX_correct`

Why this matters: Core and IEEE rounding correctness eventually need the
integer/real inbetween lemmas to justify that a chosen integer mantissa and
exponent really correspond to the requested rounding mode. Without these, proofs
can only show that local helper functions execute, not that they implement the
Flocq rounding theorem.

## Core Generic Format Infrastructure

The following `Generic_fmt.lean` items are central to spacing, monotonicity, and
DN/UP neighbor correctness:

- `Znearest_eq_choice_of_eq_half`
- `Znearest_eq_if`
- `Znearest_DN_or_UP`
- `Znearest_ge_floor`
- `Znearest_le_ceil`
- `Znearest_N_strict`
- `Znearest_half_theorem`
- `Znearest_imp`
- `Znearest_opp`
- `round_DN_exists`
- `round_DN_exists_global`
- `round_UP_exists`
- `round_DN_pt`
- `round_DN_or_UP`
- `round_to_generic_monotone`
- `round_DN_opp`
- `round_DN_small_pos`
- `round_DN_UP_lt`

Items still needing Flocq-level alignment or stronger supporting lemmas:

- constructive spacing/discreteness proof behind `round_UP_exists`
- DN/UP adjacency used by `round_DN_or_UP`
- monotonicity proof obligations behind `round_to_generic_monotone`
- sign/duality bridge behind `round_DN_opp`
- small-value and boundary lemmas behind `round_DN_small_pos`
- strict DN/UP separation behind `round_DN_UP_lt`
- the remaining Znearest theorem family referenced near `Znearest`:
  `Znearest_N_strict`, `Znearest_half`, `Znearest_imp`, `Znearest_opp`

Why this matters: these are the format-level facts that make nearest, down, and
up rounding behave like adjacent representable points. ULP proofs, error bounds,
and IEEE operation correctness all depend on the same adjacency and monotonicity
properties.

## Core ULP Infrastructure

The following `Ulp.lean` items form the predecessor/successor, ULP stability,
and rounding-error stack:

- `succ_le`
- `succ_le_inv`
- `succ_le_plus_ulp_theorem`
- `succ_le_plus_ulp`
- `round_DN_ge_UP_gt`
- `ulp_round_pos_theorem`
- `ulp_round_pos`
- `ulp_round_theorem`
- `ulp_round`
- `error_lt_ulp_round`
- `error_le_ulp_round`
- `generic_format_pred_aux2`
- `generic_format_pred_aux1_theorem_early`
- `generic_format_pred_pos`
- `succ_le_lt_aux_pos_core`
- `succ_le_lt_aux`
- `succ_le_lt_theorem`
- `succ_le_lt`
- `round_DN_eq_theorem`
- `round_DN_eq`
- `generic_format_pred`
- `pred_succ_pos_theorem`
- `pred_succ_theorem`
- `pred_succ_pos`
- `pred_succ`
- `generic_format_pred_aux1_theorem`
- `generic_format_pred_aux1`
- `round_DN_plus_eps_pos_strict`
- `round_DN_plus_eps_pos`
- `round_DN_minus_eps_pos`
- `round_DN_minus_eps`
- `round_DN_plus_eps`
- `error_le_half_ulp_theorem`
- `error_le_half_ulp`
- `error_le_half_ulp_round`

Specific missing proof ingredients called out by the file:

- generic-format predecessor closure: `generic_format_pred_aux1`,
  `generic_format_pred_aux2`, `generic_format_pred_pos`, `generic_format_pred`
- predecessor/successor inverse facts: `pred_succ_pos`, `pred_succ`
- strict successor ordering: `succ_le_lt_aux`, `succ_le_lt`
- DN representative uniqueness: `round_DN_eq`
- ULP stability under rounding: `ulp_round_pos`, `ulp_round`
- rounding error bounds: `error_lt_ulp_round`, `error_le_ulp_round`,
  `error_le_half_ulp`, `error_le_half_ulp_round`
- epsilon stability for downward rounding: `round_DN_plus_eps_pos`,
  `round_DN_minus_eps_pos`, `round_DN_minus_eps`, `round_DN_plus_eps`

Why this matters: ULP reasoning is the bridge from abstract generic rounding to
quantitative error bounds. If these items are only local bridges or depend on
unported spacing facts, then the repository cannot honestly claim faithful
Flocq-style error bounds or IEEE operation correctness.

## Pff Infrastructure

The following Pff items remain lightweight or port-gap infrastructure:

- `Fulp`: currently a lightweight ulp model for floats.
- `Fnormalize`: identity-style normalization skeleton.
- `Fshift`: no-op local model over the stored representation.
- `digitAux`: local helper kept for audit names.
- `digitAuxLess`
- `digitAuxMore`
- public generic skeletons around `isMin`, `isMax`, `MonotoneP`, and
  `MinOrMaxP` that require float-specific hypotheses in downstream proofs.

Why this matters: Pff depends on canonical float normalization, boundedness, and
digit/shift reasoning. These are needed before Pff2Flocq and high-level error
theorems can be trusted as translations rather than executable sketches.

## IEEE Infrastructure

The IEEE layer still has explicit port-gap definitions for correctness payloads.

`Binary.lean`:

- `binary_add_correct`
- `binary_mul_correct`
- `binary_sqrt_correct`
- `binary_div_correct`
- `binary_fma_correct`
- `binary_sub_correct`
- `Bfma_correct`
- `Bminus_correct`
- `Bdiv_correct`
- `Bsqrt_correct`
- `Bnearbyint_correct`
- `Bldexp_correct`

`BinarySingleNaN.lean`:

- `B754_plus_correct`
- `B754_mult_correct`
- `Bldexp_Bopp_NE`
- `Bdiv_correct_aux`
- `Bfrexp_correct_aux`
- `Bsqrt_correct_aux`

`PrimFloat.lean`:

- `one_equiv`
- `two_equiv`
- primitive classifiers `prim_is_finite`, `prim_is_nan`,
  `prim_is_infinite` remain constant in the current bridge model.

Why this matters: the IEEE layer can build and run local models, but the
correctness theorems that connect those models to Flocq/IEEE semantics are not
ported. A product API should not expose these as trusted correctness results
until the Binary and SingleNaN rounding/normalization cores are ported.

## Suggested Repair Order

1. Finish `Calc/Round.lean` inbetween/truncate theorem payloads, starting with
   `truncate_aux_comp`, `generic_format_truncate`, and `truncate_correct`.
2. Finish `Generic_fmt.lean` DN/UP spacing and monotonicity:
   `round_UP_exists`, `round_DN_or_UP`, `round_to_generic_monotone`,
   `round_DN_opp`, `round_DN_small_pos`, `round_DN_UP_lt`.
3. Finish `Ulp.lean` predecessor/successor and ULP-stability stack:
   `generic_format_pred*`, `pred_succ*`, `succ_le_lt*`, `ulp_round*`,
   `error_*_ulp*`, and `round_DN_*_eps*`.
4. Replace Pff local models: `Fulp`, `Fnormalize`, `Fshift`, `digitAux`.
5. Port IEEE Binary/SingleNaN rounding and normalization cores, then restore
   correctness theorem statements in place of `Unit` port gaps.
