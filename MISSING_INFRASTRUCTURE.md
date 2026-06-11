# Missing Flocq Infrastructure

This document names the remaining infrastructure that blocks a product-grade
FloatSpec/Flocq translation. It focuses on concrete theorem and definition
names rather than broad labels.

## Branch Diff Audit

Audit basis:

- Current branch: `floatspec-pipeline-gpt55`
- Compared against branch base/main merge base:
  `f34f53be679ee6a963ebde7605679a5a03c8bb5c`
- Current checked head for this audit:
  `1b1a752cbbfe2e4e035dab30adf33f99d7f86a48`
- Flocq source checked locally under `/mnt2/users/kaile/hantao/flocq-upstream`.

The branch removes or demotes 147 theorem declarations relative to that merge
base. For product-grade FloatSpec, the following removed or demoted public
correctness theorems should be restored as theorem declarations with real
proofs, not as `Unit`, `True`, `by trivial`, or other payload-free definitions.

- `FloatSpec/src/IEEE754/Binary.lean`:
  - `binary_add_correct`, `binary_mul_correct`, `binary_sqrt_correct`,
    `binary_div_correct`, `binary_fma_correct`, `Bfma_correct`
  - `binary_sub_correct`, `Bminus_correct`, `Bdiv_correct`, `Bsqrt_correct`,
    `Bnearbyint_correct`, `Bldexp_correct`
  - `binary_round_aux_correct'`, `binary_round_correct`,
    `binary_normalize_correct`, `binary_round_aux_correct`
- `FloatSpec/src/IEEE754/BinarySingleNaN.lean`:
  - `B754_plus_correct`, `B754_mult_correct`, `Bldexp_Bopp_NE`,
    `Bdiv_correct_aux`, `Bfrexp_correct_aux`, `Bsqrt_correct_aux`
- `FloatSpec/src/IEEE754/PrimFloat.lean`:
  - `one_equiv`, `two_equiv`
- `FloatSpec/src/Pff/Pff.lean`:
  - `FnormalizeCanonic`, `RND_Min_Pos_bounded_aux`,
    `RND_Min_Pos_canonic`, `RND_Min_canonic`, `RND_Max_Pos_canonic`,
    `RND_Min_Pos_correct`
  - `RND_Max_Pos_correct`, `RND_Max_canonic`, `RND_Min_correct`,
    `RND_Max_correct`, `RND_EvenClosest_canonic`,
    `RND_EvenClosest_correct`
  - `EvenClosestTotal`, `ClosestTotal`, `ClosestMin`, `ClosestMax`,
    `ClosestMinOrMax`, `FboundedMboundPos`
  - `FboundedMbound`, `MinEx`, `MaxEx`, `ClosestMonotone`,
    `ClosestRoundedModeP`, `ClosestOpp`
  - `ClosestFabs`, `ClosestUlp`, `ClosestExp`, `ClosestSymmetric`,
    `EvenClosestMinOrMax`, `EvenClosestMonotone`
  - `EvenClosestSymmetric`, `EvenClosestRoundedModeP`, `RoundedProjector`,
    `RoundedModeBounded`, `PminPos`, `RoundedModeMult`
  - `RoundedModeMultLess`, `RoundedModeMultAbs`, `MinRoundedModeP`,
    `MaxRoundedModeP`, `firstNormalPosNormal`, `SterbenzAux`
  - `Sterbenz`, `digitAuxLess`, `digitAuxMore`
- `FloatSpec/src/Pff/Pff2Flocq.lean`:
  - `Fast2Sum_correct`, `TwoSum_correct`, `Veltkamp_Even`, `Veltkamp`,
    `Veltkamp_tail`, `underf_mult_aux`
  - `underf_mult_aux'`, `V1_Und3'`, `V1_Und3`, `Dekker`,
    `ErrFMA_bounded`, `ErrFMA_correct`
  - `ErrFMA_bounded_simpl`, `mult_error_FLT_ge_bpow'`, `V2_Und4`,
    `V2_Und2`, `V2_Und5`, `U3_discri1`
  - `U4_discri1`, `ErrFMA_correct_simpl`, `ErrFmaAppr_correct`,
    `U5_discri1_aux`, `U5_discri1`, `discri_correct_test`
  - `discri_fp_test`, `Axpy`
- `FloatSpec/src/Prop/Div_sqrt_error.lean`:
  - `sqrt_error_FLX`, `div_error_FLT`, `sqrt_error_FLT`
- `FloatSpec/src/Prop/Double_rounding.lean`:
  - `double_round_eq`, `round_round_lt_mid_further_place`,
    `round_round_mult`, `round_round_mult_FLX`, `round_round_mult_FLT`,
    `round_round_mult_FTZ`
  - `round_round_sqrt_FLX`, `round_round_sqrt_FLT`,
    `round_round_sqrt_radix_ge_4_FLX`,
    `round_round_sqrt_radix_ge_4_FLT`, `round_round_sqrt_FTZ`,
    `round_round_sqrt_radix_ge_4_FTZ`
  - `round_round_lt_mid_further_place'`, `round_round_lt_mid_same_place`,
    `round_round_lt_mid`, `round_round_div_FLX`, `round_round_div_FLT`,
    `round_round_div_FTZ`
  - `round_round_plus_radix_ge_3_FLX`,
    `round_round_minus_radix_ge_3_FLX`,
    `round_round_plus_radix_ge_3_FLT`,
    `round_round_minus_radix_ge_3_FLT`,
    `round_round_plus_radix_ge_3_FTZ`,
    `round_round_minus_radix_ge_3_FTZ`
  - `round_round_gt_mid_further_place'`,
    `round_round_gt_mid_further_place`, `round_round_gt_mid_same_place`,
    `round_round_gt_mid`, `double_round_FLX_FLT`, `double_round_same`
  - `round_round_plus_FLX`, `round_round_minus_FLX`,
    `round_round_plus_FLT`, `round_round_minus_FLT`,
    `round_round_plus_FTZ`, `round_round_minus_FTZ`
- `FloatSpec/src/Prop/Round_odd.lean`:
  - `round_odd_pt`, `Rnd_odd_pt_monotone`, `round_odd_ge_ulp`,
    `round_odd_double_round`, `mag_round_odd`, `fexp_round_odd`
  - `round_N_odd_pos`, `round_N_odd`

The following removed declarations should not be blindly reverted:

- `consecutive_scaled_mantissas_ax` and private
  `consecutive_scaled_mantissas`: these are Lean-local spacing bridges, not
  direct Flocq theorem names. Restoring an axiom is the wrong fix; replace them
  with proved spacing lemmas or proofs built from the aligned Flocq DN/UP
  infrastructure.
- private `ulp_roundN_eq_ulp_x_bridge` and
  private `round_DN_plus_eps_theorem`: these are Lean-local helper bridges, not
  direct public Flocq theorem names. Restore only if they are still needed as
  proved helper lemmas.
- `Prim2SF_placeholder`: this placeholder theorem name is branch/base-local and
  has no Flocq counterpart. It should be replaced by a faithful primitive-float
  bridge, not restored as a placeholder.

## Name Validation

I checked the theorem/definition names already listed in this file against both
the branch-base Lean declarations and the local Flocq clone.

No listed item is a pure hallucination in the sense of being absent from both
Lean and Flocq, except that two names are branch-local helpers and should not be
treated as Flocq infrastructure:

- `succ_le_lt_aux_pos_core`: introduced on this branch as a local Lean helper;
  it was not present at the merge base and is not a Flocq theorem name.
- `round_DN_plus_eps_pos_strict`: introduced on this branch as a local Lean
  helper; it was not present at the merge base and is not a Flocq theorem name.

Several listed names are real Lean support items present at the merge base but
are not direct Flocq theorem names. They should stay in this document only as
Lean proof infrastructure, not as missing upstream theorem imports:

- `Znearest_eq_choice_of_eq_half`, `Znearest_eq_if`,
  `Znearest_half_theorem`
- `round_DN_exists`, `round_DN_exists_global`, `round_UP_exists`,
  `round_to_generic_monotone`
- `succ_le_plus_ulp_theorem`, `ulp_round_pos_theorem`,
  `ulp_round_theorem`, `error_le_half_ulp_theorem`
- `generic_format_pred_aux1_theorem_early`,
  `succ_le_lt_theorem`, `round_DN_eq_theorem`,
  `pred_succ_pos_theorem`, `pred_succ_theorem`,
  `generic_format_pred_aux1_theorem`

The prose mention of `Znearest_half` refers to the upstream Flocq theorem in
`src/Core/Generic_fmt.v`; the branch-base Lean name for that payload is
`Znearest_half_theorem`.

I did not find a case where a listed theorem is both needed and absent from the
beginning of the branch-base translation while also being a direct Flocq theorem
that should have been imported. When a name is absent from the merge-base Lean
translation, it is either a current-branch local helper or a Coq source name
whose Lean translation uses a different local name.

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
