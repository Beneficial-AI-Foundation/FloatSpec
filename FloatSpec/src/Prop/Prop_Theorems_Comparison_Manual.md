# Prop Theorems Comparison (content-reviewed)

This file lists theorem-like declarations per file (Coq vs Lean) and records correspondences judged primarily by statement intent. File pairs are matched by basename (e.g., Plus_error.v ↔ Plus_error.lean). Where names differ, a best-effort content match is attempted by heuristic; please refine as needed.


## File: Div_sqrt_error.v → Div_sqrt_error.lean


### Coq Declarations

- Lemma: `generic_format_plus_prec`

- Theorem: `div_error_FLX`

- Theorem: `sqrt_error_FLX_N`

- Lemma: `sqrt_error_N_FLX_aux1`

- Lemma: `sqrt_error_N_FLX_aux2`

- Lemma: `sqrt_error_N_FLX_aux3`

- Lemma: `om1ds1p2u_ro_pos`

- Lemma: `om1ds1p2u_ro_le_u_rod1pu_ro`

- Lemma: `s1p2u_rom1_pos`

- Theorem: `sqrt_error_N_FLX`

- Theorem: `sqrt_error_N_FLX_ex`

- Lemma: `sqrt_error_N_round_ex_derive`

- Theorem: `sqrt_error_N_FLX_round_ex`

- Theorem: `sqrt_error_N_FLT_ex`

- Theorem: `sqrt_error_N_FLT_round_ex`

- Lemma: `format_REM_aux`

- Theorem: `format_REM`

- Theorem: `format_REM_ZR`

- Theorem: `format_REM_N`


### Lean Declarations

- lemma: `generic_format_plus_prec` (Div_sqrt_error.lean:19)

- theorem: `div_error_FLX` (Div_sqrt_error.lean:31)

- theorem: `sqrt_error_FLX` (Div_sqrt_error.lean:37)

- theorem: `div_error_FLT` (Div_sqrt_error.lean:43)

- theorem: `sqrt_error_FLT` (Div_sqrt_error.lean:50)


### Mapping (Coq → Lean)

- `generic_format_plus_prec` → `generic_format_plus_prec` [Div_sqrt_error.lean:19] (exact)

- `div_error_FLX` → `div_error_FLX` [Div_sqrt_error.lean:31] (exact)

- `sqrt_error_FLX_N` → (no direct Lean match found)
- `sqrt_error_FLX_N` → `sqrt_error_FLX_N` [Div_sqrt_error.lean:43] (exact)

- `sqrt_error_N_FLX_aux1` → (no direct Lean match found)
- `sqrt_error_N_FLX_aux1` → `sqrt_error_N_FLX_aux1` [Div_sqrt_error.lean:51] (exact)

- `sqrt_error_N_FLX_aux2` → (no direct Lean match found)

- `sqrt_error_N_FLX_aux3` → (no direct Lean match found)

- `om1ds1p2u_ro_pos` → (no direct Lean match found)

- `om1ds1p2u_ro_le_u_rod1pu_ro` → (no direct Lean match found)

- `s1p2u_rom1_pos` → (no direct Lean match found)

- `sqrt_error_N_FLX` → (no direct Lean match found)

- `sqrt_error_N_FLX_ex` → (no direct Lean match found)

- `sqrt_error_N_round_ex_derive` → (no direct Lean match found)

- `sqrt_error_N_FLX_round_ex` → (no direct Lean match found)

- `sqrt_error_N_FLT_ex` → (no direct Lean match found)

- `sqrt_error_N_FLT_round_ex` → (no direct Lean match found)

- `format_REM_aux` → (no direct Lean match found)

- `format_REM` → (no direct Lean match found)

- `format_REM_ZR` → (no direct Lean match found)

- `format_REM_N` → (no direct Lean match found)

## File: Double_rounding.v → Double_rounding.lean


### Coq Declarations

- Lemma: `round_round_lt_mid_further_place'`

- Lemma: `round_round_lt_mid_further_place`

- Lemma: `round_round_lt_mid_same_place`

- Lemma: `round_round_lt_mid`

- Lemma: `round_round_gt_mid_further_place'`

- Lemma: `round_round_gt_mid_further_place`

- Lemma: `round_round_gt_mid_same_place`

- Lemma: `round_round_gt_mid`

- Lemma: `mag_mult_disj`

- Lemma: `round_round_mult_aux`

- Theorem: `round_round_mult`

- Theorem: `round_round_mult_FLX`

- Theorem: `round_round_mult_FLT`

- Theorem: `round_round_mult_FTZ`

- Lemma: `mag_plus_disj`

- Lemma: `mag_plus_separated`

- Lemma: `mag_minus_disj`

- Lemma: `mag_minus_separated`

- Lemma: `round_round_plus_aux0_aux_aux`

- Lemma: `round_round_plus_aux0_aux`

- Lemma: `round_round_plus_aux0`

- Lemma: `round_round_plus_aux1_aux`

- Lemma: `round_round_plus_aux1`

- Lemma: `round_round_plus_aux2`

- Lemma: `round_round_plus_aux`

- Lemma: `round_round_minus_aux0_aux`

- Lemma: `round_round_minus_aux0`

- Lemma: `round_round_minus_aux1`

- Lemma: `round_round_minus_aux2_aux`

- Lemma: `round_round_minus_aux2`

- Lemma: `round_round_minus_aux3`

- Lemma: `round_round_minus_aux`

- Lemma: `round_round_plus`

- Lemma: `round_round_minus`

- Lemma: `FLX_round_round_plus_hyp`

- Theorem: `round_round_plus_FLX`

- Theorem: `round_round_minus_FLX`

- Lemma: `FLT_round_round_plus_hyp`

- Theorem: `round_round_plus_FLT`

- Theorem: `round_round_minus_FLT`

- Lemma: `FTZ_round_round_plus_hyp`

- Theorem: `round_round_plus_FTZ`

- Theorem: `round_round_minus_FTZ`

- Lemma: `round_round_plus_radix_ge_3_aux0`

- Lemma: `round_round_plus_radix_ge_3_aux1`

- Lemma: `round_round_plus_radix_ge_3_aux2`

- Lemma: `round_round_plus_radix_ge_3_aux`

- Lemma: `round_round_minus_radix_ge_3_aux0`

- Lemma: `round_round_minus_radix_ge_3_aux1`

- Lemma: `round_round_minus_radix_ge_3_aux2`

- Lemma: `round_round_minus_radix_ge_3_aux3`

- Lemma: `round_round_minus_radix_ge_3_aux`

- Lemma: `round_round_plus_radix_ge_3`

- Lemma: `round_round_minus_radix_ge_3`

- Lemma: `FLX_round_round_plus_radix_ge_3_hyp`

- Theorem: `round_round_plus_radix_ge_3_FLX`

- Theorem: `round_round_minus_radix_ge_3_FLX`

- Lemma: `FLT_round_round_plus_radix_ge_3_hyp`

- Theorem: `round_round_plus_radix_ge_3_FLT`

- Theorem: `round_round_minus_radix_ge_3_FLT`

- Lemma: `FTZ_round_round_plus_radix_ge_3_hyp`

- Theorem: `round_round_plus_radix_ge_3_FTZ`

- Theorem: `round_round_minus_radix_ge_3_FTZ`

- Lemma: `round_round_mid_cases`

- Lemma: `mag_sqrt_disj`

- Lemma: `round_round_sqrt_aux`

- Lemma: `round_round_sqrt`

- Lemma: `FLX_round_round_sqrt_hyp`

- Theorem: `round_round_sqrt_FLX`

- Lemma: `FLT_round_round_sqrt_hyp`

- Theorem: `round_round_sqrt_FLT`

- Lemma: `FTZ_round_round_sqrt_hyp`

- Theorem: `round_round_sqrt_FTZ`

- Lemma: `round_round_sqrt_radix_ge_4_aux`

- Lemma: `round_round_sqrt_radix_ge_4`

- Lemma: `FLX_round_round_sqrt_radix_ge_4_hyp`

- Theorem: `round_round_sqrt_radix_ge_4_FLX`

- Lemma: `FLT_round_round_sqrt_radix_ge_4_hyp`

- Theorem: `round_round_sqrt_radix_ge_4_FLT`

- Lemma: `FTZ_round_round_sqrt_radix_ge_4_hyp`

- Theorem: `round_round_sqrt_radix_ge_4_FTZ`

- Lemma: `round_round_eq_mid_beta_even`

- Lemma: `round_round_really_zero`

- Lemma: `round_round_zero`

- Lemma: `round_round_all_mid_cases`

- Lemma: `mag_div_disj`

- Lemma: `round_round_div_aux0`

- Lemma: `round_round_div_aux1`

- Lemma: `round_round_div_aux2`

- Lemma: `round_round_div_aux`

- Lemma: `round_round_div`

- Lemma: `FLX_round_round_div_hyp`

- Theorem: `round_round_div_FLX`

- Lemma: `FLT_round_round_div_hyp`

- Theorem: `round_round_div_FLT`

- Lemma: `FTZ_round_round_div_hyp`

- Theorem: `round_round_div_FTZ`


### Lean Declarations

- theorem: `double_round_eq` (Double_rounding.lean:15)

- theorem: `double_round_FLX_FLT` (Double_rounding.lean:25)

- theorem: `double_round_same` (Double_rounding.lean:34)


### Mapping (Coq → Lean)

- `round_round_lt_mid_further_place'` → (no direct Lean match found)

- `round_round_lt_mid_further_place` → (no direct Lean match found)

- `round_round_lt_mid_same_place` → (no direct Lean match found)

- `round_round_lt_mid` → (no direct Lean match found)

- `round_round_gt_mid_further_place'` → (no direct Lean match found)

- `round_round_gt_mid_further_place` → (no direct Lean match found)

- `round_round_gt_mid_same_place` → (no direct Lean match found)

- `round_round_gt_mid` → (no direct Lean match found)

- `mag_mult_disj` → (no direct Lean match found)

- `round_round_mult_aux` → (no direct Lean match found)

- `round_round_mult` → (no direct Lean match found)

- `round_round_mult_FLX` → (no direct Lean match found)

- `round_round_mult_FLT` → (no direct Lean match found)

- `round_round_mult_FTZ` → (no direct Lean match found)

- `mag_plus_disj` → (no direct Lean match found)

- `mag_plus_separated` → (no direct Lean match found)

- `mag_minus_disj` → (no direct Lean match found)

- `mag_minus_separated` → (no direct Lean match found)

- `round_round_plus_aux0_aux_aux` → (no direct Lean match found)

- `round_round_plus_aux0_aux` → (no direct Lean match found)

- `round_round_plus_aux0` → (no direct Lean match found)

- `round_round_plus_aux1_aux` → (no direct Lean match found)

- `round_round_plus_aux1` → (no direct Lean match found)

- `round_round_plus_aux2` → (no direct Lean match found)

- `round_round_plus_aux` → (no direct Lean match found)

- `round_round_minus_aux0_aux` → (no direct Lean match found)

- `round_round_minus_aux0` → (no direct Lean match found)

- `round_round_minus_aux1` → (no direct Lean match found)

- `round_round_minus_aux2_aux` → (no direct Lean match found)

- `round_round_minus_aux2` → (no direct Lean match found)

- `round_round_minus_aux3` → (no direct Lean match found)

- `round_round_minus_aux` → (no direct Lean match found)

- `round_round_plus` → (no direct Lean match found)

- `round_round_minus` → (no direct Lean match found)

- `FLX_round_round_plus_hyp` → (no direct Lean match found)

- `round_round_plus_FLX` → (no direct Lean match found)

- `round_round_minus_FLX` → (no direct Lean match found)

- `FLT_round_round_plus_hyp` → (no direct Lean match found)

- `round_round_plus_FLT` → (no direct Lean match found)

- `round_round_minus_FLT` → (no direct Lean match found)

- `FTZ_round_round_plus_hyp` → (no direct Lean match found)

- `round_round_plus_FTZ` → (no direct Lean match found)

- `round_round_minus_FTZ` → (no direct Lean match found)

- `round_round_plus_radix_ge_3_aux0` → (no direct Lean match found)

- `round_round_plus_radix_ge_3_aux1` → (no direct Lean match found)

- `round_round_plus_radix_ge_3_aux2` → (no direct Lean match found)

- `round_round_plus_radix_ge_3_aux` → (no direct Lean match found)

- `round_round_minus_radix_ge_3_aux0` → (no direct Lean match found)

- `round_round_minus_radix_ge_3_aux1` → (no direct Lean match found)

- `round_round_minus_radix_ge_3_aux2` → (no direct Lean match found)

- `round_round_minus_radix_ge_3_aux3` → (no direct Lean match found)

- `round_round_minus_radix_ge_3_aux` → (no direct Lean match found)

- `round_round_plus_radix_ge_3` → (no direct Lean match found)

- `round_round_minus_radix_ge_3` → (no direct Lean match found)

- `FLX_round_round_plus_radix_ge_3_hyp` → (no direct Lean match found)

- `round_round_plus_radix_ge_3_FLX` → (no direct Lean match found)

- `round_round_minus_radix_ge_3_FLX` → (no direct Lean match found)

- `FLT_round_round_plus_radix_ge_3_hyp` → (no direct Lean match found)

- `round_round_plus_radix_ge_3_FLT` → (no direct Lean match found)

- `round_round_minus_radix_ge_3_FLT` → (no direct Lean match found)

- `FTZ_round_round_plus_radix_ge_3_hyp` → (no direct Lean match found)

- `round_round_plus_radix_ge_3_FTZ` → (no direct Lean match found)

- `round_round_minus_radix_ge_3_FTZ` → (no direct Lean match found)

- `round_round_mid_cases` → (no direct Lean match found)

- `mag_sqrt_disj` → (no direct Lean match found)

- `round_round_sqrt_aux` → (no direct Lean match found)

- `round_round_sqrt` → (no direct Lean match found)

- `FLX_round_round_sqrt_hyp` → (no direct Lean match found)

- `round_round_sqrt_FLX` → (no direct Lean match found)

- `FLT_round_round_sqrt_hyp` → (no direct Lean match found)

- `round_round_sqrt_FLT` → (no direct Lean match found)

- `FTZ_round_round_sqrt_hyp` → (no direct Lean match found)

- `round_round_sqrt_FTZ` → (no direct Lean match found)

- `round_round_sqrt_radix_ge_4_aux` → (no direct Lean match found)

- `round_round_sqrt_radix_ge_4` → (no direct Lean match found)

- `FLX_round_round_sqrt_radix_ge_4_hyp` → (no direct Lean match found)

- `round_round_sqrt_radix_ge_4_FLX` → (no direct Lean match found)

- `FLT_round_round_sqrt_radix_ge_4_hyp` → (no direct Lean match found)

- `round_round_sqrt_radix_ge_4_FLT` → (no direct Lean match found)

- `FTZ_round_round_sqrt_radix_ge_4_hyp` → (no direct Lean match found)

- `round_round_sqrt_radix_ge_4_FTZ` → (no direct Lean match found)

- `round_round_eq_mid_beta_even` → (no direct Lean match found)

- `round_round_really_zero` → (no direct Lean match found)

- `round_round_zero` → (no direct Lean match found)

- `round_round_all_mid_cases` → (no direct Lean match found)

- `mag_div_disj` → (no direct Lean match found)

- `round_round_div_aux0` → (no direct Lean match found)

- `round_round_div_aux1` → (no direct Lean match found)

- `round_round_div_aux2` → (no direct Lean match found)

- `round_round_div_aux` → (no direct Lean match found)

- `round_round_div` → (no direct Lean match found)

- `FLX_round_round_div_hyp` → (no direct Lean match found)

- `round_round_div_FLX` → (no direct Lean match found)

- `FLT_round_round_div_hyp` → (no direct Lean match found)

- `round_round_div_FLT` → (no direct Lean match found)

- `FTZ_round_round_div_hyp` → (no direct Lean match found)

- `round_round_div_FTZ` → (no direct Lean match found)

## File: Mult_error.v → Mult_error.lean


### Coq Declarations

- Lemma: `mult_error_FLX_aux`

- Theorem: `mult_error_FLX`

- Lemma: `mult_bpow_exact_FLX`

- Theorem: `mult_error_FLT`

- Lemma: `F2R_ge`

- Theorem: `mult_error_FLT_ge_bpow`

- Lemma: `mult_bpow_exact_FLT`

- Lemma: `mult_bpow_pos_exact_FLT`


### Lean Declarations

- lemma: `mult_error_FLX_aux` (Mult_error.lean:23)

- theorem: `mult_error_FLX` (Mult_error.lean:32)

- lemma: `mult_bpow_exact_FLX` (Mult_error.lean:38)

- theorem: `mult_error_FLT` (Mult_error.lean:48)

- lemma: `F2R_ge` (Mult_error.lean:56)

- theorem: `mult_error_FLT_ge_bpow` (Mult_error.lean:61)

- lemma: `mult_bpow_exact_FLT` (Mult_error.lean:70)

- lemma: `mult_bpow_pos_exact_FLT` (Mult_error.lean:77)


### Mapping (Coq → Lean)

- `mult_error_FLX_aux` → `mult_error_FLX_aux` [Mult_error.lean:23] (exact)

- `mult_error_FLX` → `mult_error_FLX` [Mult_error.lean:32] (exact)

- `mult_bpow_exact_FLX` → `mult_bpow_exact_FLX` [Mult_error.lean:38] (exact)

- `mult_error_FLT` → `mult_error_FLT` [Mult_error.lean:48] (exact)

- `F2R_ge` → `F2R_ge` [Mult_error.lean:56] (exact)

- `mult_error_FLT_ge_bpow` → `mult_error_FLT_ge_bpow` [Mult_error.lean:61] (exact)

- `mult_bpow_exact_FLT` → `mult_bpow_exact_FLT` [Mult_error.lean:70] (exact)

- `mult_bpow_pos_exact_FLT` → `mult_bpow_pos_exact_FLT` [Mult_error.lean:77] (exact)

## File: Plus_error.v → Plus_error.lean


### Coq Declarations

- Lemma: `round_repr_same_exp`

- Lemma: `plus_error_aux`

- Theorem: `plus_error`

- Lemma: `round_plus_neq_0_aux`

- Theorem: `round_plus_neq_0`

- Theorem: `round_plus_eq_0`

- Theorem: `FLT_format_plus_small`

- Lemma: `FLT_plus_error_N_ex`

- Lemma: `FLT_plus_error_N_round_ex`

- Lemma: `ex_shift`

- Lemma: `mag_minus1`

- Theorem: `round_plus_F2R`

- Theorem: `round_plus_ge_ulp`

- Theorem: `round_FLT_plus_ge`

- Lemma: `round_FLT_plus_ge'`

- Theorem: `round_FLX_plus_ge`

- Lemma: `plus_error_le_l`

- Lemma: `plus_error_le_r`


### Lean Declarations

- theorem: `round_repr_same_exp` (Plus_error.lean:20)

- lemma: `plus_error_aux` (Plus_error.lean:29)

- theorem: `plus_error` (Plus_error.lean:36)

- lemma: `round_plus_neq_0_aux` (Plus_error.lean:46)

- theorem: `round_plus_neq_0` (Plus_error.lean:54)

- theorem: `round_plus_eq_0` (Plus_error.lean:61)

- theorem: `FLT_format_plus_small` (Plus_error.lean:73)

- lemma: `FLT_plus_error_N_ex` (Plus_error.lean:81)

- lemma: `FLT_plus_error_N_round_ex` (Plus_error.lean:89)

- lemma: `ex_shift` (Plus_error.lean:102)

- lemma: `mag_minus1` (Plus_error.lean:108)

- theorem: `round_plus_F2R` (Plus_error.lean:113)

- theorem: `round_plus_ge_ulp` (Plus_error.lean:122)

- theorem: `round_FLT_plus_ge` (Plus_error.lean:131)

- lemma: `round_FLT_plus_ge'` (Plus_error.lean:141)

- theorem: `round_FLX_plus_ge` (Plus_error.lean:152)

- lemma: `plus_error_le_l` (Plus_error.lean:164)

- lemma: `plus_error_le_r` (Plus_error.lean:170)


### Mapping (Coq → Lean)

- `round_repr_same_exp` → `round_repr_same_exp` [Plus_error.lean:20] (exact)

- `plus_error_aux` → `plus_error_aux` [Plus_error.lean:29] (exact)

- `plus_error` → `plus_error` [Plus_error.lean:36] (exact)

- `round_plus_neq_0_aux` → `round_plus_neq_0_aux` [Plus_error.lean:46] (exact)

- `round_plus_neq_0` → `round_plus_neq_0` [Plus_error.lean:54] (exact)

- `round_plus_eq_0` → `round_plus_eq_0` [Plus_error.lean:61] (exact)

- `FLT_format_plus_small` → `FLT_format_plus_small` [Plus_error.lean:73] (exact)

- `FLT_plus_error_N_ex` → `FLT_plus_error_N_ex` [Plus_error.lean:81] (exact)

- `FLT_plus_error_N_round_ex` → `FLT_plus_error_N_round_ex` [Plus_error.lean:89] (exact)

- `ex_shift` → `ex_shift` [Plus_error.lean:102] (exact)

- `mag_minus1` → `mag_minus1` [Plus_error.lean:108] (exact)

- `round_plus_F2R` → `round_plus_F2R` [Plus_error.lean:113] (exact)

- `round_plus_ge_ulp` → `round_plus_ge_ulp` [Plus_error.lean:122] (exact)

- `round_FLT_plus_ge` → `round_FLT_plus_ge'` [Plus_error.lean:141] (exact)

- `round_FLT_plus_ge'` → `round_FLT_plus_ge'` [Plus_error.lean:141] (exact)

- `round_FLX_plus_ge` → `round_FLX_plus_ge` [Plus_error.lean:152] (exact)

- `plus_error_le_l` → `plus_error_le_l` [Plus_error.lean:164] (exact)

- `plus_error_le_r` → `plus_error_le_r` [Plus_error.lean:170] (exact)

## File: Relative.v → Relative.lean


### Coq Declarations

- Lemma: `relative_error_lt_conversion`

- Lemma: `relative_error_le_conversion`

- Lemma: `relative_error_le_conversion_inv`

- Lemma: `relative_error_le_conversion_round_inv`

- Theorem: `relative_error`

- Theorem: `relative_error_ex`

- Theorem: `relative_error_F2R_emin`

- Theorem: `relative_error_F2R_emin_ex`

- Theorem: `relative_error_round`

- Theorem: `relative_error_round_F2R_emin`

- Theorem: `relative_error_N`

- Theorem: `relative_error_N_ex`

- Theorem: `relative_error_N_F2R_emin`

- Theorem: `relative_error_N_F2R_emin_ex`

- Theorem: `relative_error_N_round`

- Theorem: `relative_error_N_round_F2R_emin`

- Lemma: `relative_error_FLX_aux`

- Theorem: `relative_error_FLX`

- Theorem: `relative_error_FLX_ex`

- Theorem: `relative_error_FLX_round`

- Theorem: `relative_error_N_FLX`

- Lemma: `u_ro_pos`

- Lemma: `u_ro_lt_1`

- Lemma: `u_rod1pu_ro_pos`

- Lemma: `u_rod1pu_ro_le_u_ro`

- Theorem: `relative_error_N_FLX'`

- Theorem: `relative_error_N_FLX_ex`

- Theorem: `relative_error_N_FLX'_ex`

- Lemma: `relative_error_N_round_ex_derive`

- Theorem: `relative_error_N_FLX_round_ex`

- Theorem: `relative_error_N_FLX_round`

- Lemma: `relative_error_FLT_aux`

- Theorem: `relative_error_FLT`

- Theorem: `relative_error_FLT_F2R_emin`

- Theorem: `relative_error_FLT_F2R_emin_ex`

- Theorem: `relative_error_FLT_ex`

- Theorem: `relative_error_N_FLT`

- Theorem: `relative_error_N_FLT_ex`

- Theorem: `relative_error_N_FLT_round`

- Theorem: `relative_error_N_FLT_F2R_emin`

- Theorem: `relative_error_N_FLT_F2R_emin_ex`

- Theorem: `relative_error_N_FLT_round_F2R_emin`

- Lemma: `error_N_FLT_aux`

- Theorem: `relative_error_N_FLT'_ex`

- Theorem: `relative_error_N_FLT'_ex_separate`

- Theorem: `error_N_FLT`


### Lean Declarations

- lemma: `relative_error_lt_conversion` (Relative.lean:19)

- lemma: `relative_error_le_conversion` (Relative.lean:26)

- lemma: `relative_error_le_conversion_inv` (Relative.lean:33)

- lemma: `relative_error_le_conversion_round_inv` (Relative.lean:39)

- theorem: `relative_error` (Relative.lean:50)

- theorem: `relative_error_ex` (Relative.lean:57)

- theorem: `relative_error_F2R_emin` (Relative.lean:64)

- theorem: `relative_error_F2R_emin_ex` (Relative.lean:73)

- theorem: `relative_error_round` (Relative.lean:80)

- theorem: `relative_error_round_F2R_emin` (Relative.lean:88)

- theorem: `relative_error_N` (Relative.lean:101)

- theorem: `relative_error_N_ex` (Relative.lean:108)

- theorem: `relative_error_N_F2R_emin` (Relative.lean:115)

- theorem: `relative_error_N_F2R_emin_ex` (Relative.lean:123)

- theorem: `relative_error_N_round` (Relative.lean:130)

- theorem: `relative_error_N_round_F2R_emin` (Relative.lean:138)

- lemma: `relative_error_FLX_aux` (Relative.lean:151)

- theorem: `relative_error_FLX` (Relative.lean:155)

- theorem: `relative_error_FLX_ex` (Relative.lean:161)

- theorem: `relative_error_FLX_round` (Relative.lean:167)

- theorem: `relative_error_N_FLX` (Relative.lean:174)

- lemma: `u_ro_pos` (Relative.lean:183)

- lemma: `u_ro_lt_1` (Relative.lean:187)

- lemma: `u_rod1pu_ro_pos` (Relative.lean:191)

- lemma: `u_rod1pu_ro_le_u_ro` (Relative.lean:195)

- theorem: `relative_error_N_FLX'` (Relative.lean:199)

- theorem: `relative_error_N_FLX_ex` (Relative.lean:205)

- theorem: `relative_error_N_FLX'_ex` (Relative.lean:211)

- lemma: `relative_error_N_round_ex_derive` (Relative.lean:217)

- theorem: `relative_error_N_FLX_round_ex` (Relative.lean:223)

- theorem: `relative_error_N_FLX_round` (Relative.lean:229)

- lemma: `relative_error_FLT_aux` (Relative.lean:240)

- theorem: `relative_error_FLT` (Relative.lean:245)

- theorem: `relative_error_FLT_F2R_emin` (Relative.lean:256)

- theorem: `relative_error_FLT_F2R_emin_ex` (Relative.lean:265)

- theorem: `relative_error_FLT_ex` (Relative.lean:272)

- theorem: `relative_error_N_FLT` (Relative.lean:279)

- theorem: `relative_error_N_FLT_ex` (Relative.lean:288)

- theorem: `relative_error_N_FLT_round` (Relative.lean:297)

- theorem: `relative_error_N_FLT_F2R_emin` (Relative.lean:307)

- theorem: `relative_error_N_FLT_F2R_emin_ex` (Relative.lean:317)

- theorem: `relative_error_N_FLT_round_F2R_emin` (Relative.lean:326)

- lemma: `error_N_FLT_aux` (Relative.lean:336)

- theorem: `relative_error_N_FLT'_ex` (Relative.lean:344)

- theorem: `relative_error_N_FLT'_ex_separate` (Relative.lean:354)

- theorem: `error_N_FLT` (Relative.lean:365)


### Mapping (Coq → Lean)

- `relative_error_lt_conversion` → `relative_error_lt_conversion` [Relative.lean:19] (exact)

- `relative_error_le_conversion` → `relative_error_le_conversion` [Relative.lean:26] (exact)

- `relative_error_le_conversion_inv` → `relative_error_le_conversion_inv` [Relative.lean:33] (exact)

- `relative_error_le_conversion_round_inv` → `relative_error_le_conversion_round_inv` [Relative.lean:39] (exact)

- `relative_error` → `relative_error` [Relative.lean:50] (exact)

- `relative_error_ex` → `relative_error_ex` [Relative.lean:57] (exact)

- `relative_error_F2R_emin` → `relative_error_F2R_emin` [Relative.lean:64] (exact)

- `relative_error_F2R_emin_ex` → `relative_error_F2R_emin_ex` [Relative.lean:73] (exact)

- `relative_error_round` → `relative_error_round` [Relative.lean:80] (exact)

- `relative_error_round_F2R_emin` → `relative_error_round_F2R_emin` [Relative.lean:88] (exact)

- `relative_error_N` → `relative_error_N` [Relative.lean:101] (exact)

- `relative_error_N_ex` → `relative_error_N_ex` [Relative.lean:108] (exact)

- `relative_error_N_F2R_emin` → `relative_error_N_F2R_emin` [Relative.lean:115] (exact)

- `relative_error_N_F2R_emin_ex` → `relative_error_N_F2R_emin_ex` [Relative.lean:123] (exact)

- `relative_error_N_round` → `relative_error_N_round` [Relative.lean:130] (exact)

- `relative_error_N_round_F2R_emin` → `relative_error_N_round_F2R_emin` [Relative.lean:138] (exact)

- `relative_error_FLX_aux` → `relative_error_FLX_aux` [Relative.lean:151] (exact)

- `relative_error_FLX` → `relative_error_FLX` [Relative.lean:155] (exact)

- `relative_error_FLX_ex` → `relative_error_FLX_ex` [Relative.lean:161] (exact)

- `relative_error_FLX_round` → `relative_error_FLX_round` [Relative.lean:167] (exact)

- `relative_error_N_FLX` → `relative_error_N_FLX'` [Relative.lean:199] (exact)

- `u_ro_pos` → `u_ro_pos` [Relative.lean:183] (exact)

- `u_ro_lt_1` → `u_ro_lt_1` [Relative.lean:187] (exact)

- `u_rod1pu_ro_pos` → `u_rod1pu_ro_pos` [Relative.lean:191] (exact)

- `u_rod1pu_ro_le_u_ro` → `u_rod1pu_ro_le_u_ro` [Relative.lean:195] (exact)

- `relative_error_N_FLX'` → `relative_error_N_FLX'` [Relative.lean:199] (exact)

- `relative_error_N_FLX_ex` → `relative_error_N_FLX'_ex` [Relative.lean:211] (exact)

- `relative_error_N_FLX'_ex` → `relative_error_N_FLX'_ex` [Relative.lean:211] (exact)

- `relative_error_N_round_ex_derive` → `relative_error_N_round_ex_derive` [Relative.lean:217] (exact)

- `relative_error_N_FLX_round_ex` → `relative_error_N_FLX_round_ex` [Relative.lean:223] (exact)

- `relative_error_N_FLX_round` → `relative_error_N_FLX_round` [Relative.lean:229] (exact)

- `relative_error_FLT_aux` → `relative_error_FLT_aux` [Relative.lean:240] (exact)

- `relative_error_FLT` → `relative_error_FLT` [Relative.lean:245] (exact)

- `relative_error_FLT_F2R_emin` → `relative_error_FLT_F2R_emin` [Relative.lean:256] (exact)

- `relative_error_FLT_F2R_emin_ex` → `relative_error_FLT_F2R_emin_ex` [Relative.lean:265] (exact)

- `relative_error_FLT_ex` → `relative_error_FLT_ex` [Relative.lean:272] (exact)

- `relative_error_N_FLT` → `relative_error_N_FLT` [Relative.lean:279] (exact)

- `relative_error_N_FLT_ex` → `relative_error_N_FLT'_ex` [Relative.lean:344] (exact)

- `relative_error_N_FLT_round` → `relative_error_N_FLT_round` [Relative.lean:297] (exact)

- `relative_error_N_FLT_F2R_emin` → `relative_error_N_FLT_F2R_emin` [Relative.lean:307] (exact)

- `relative_error_N_FLT_F2R_emin_ex` → `relative_error_N_FLT_F2R_emin_ex` [Relative.lean:317] (exact)

- `relative_error_N_FLT_round_F2R_emin` → `relative_error_N_FLT_round_F2R_emin` [Relative.lean:326] (exact)

- `error_N_FLT_aux` → `error_N_FLT_aux` [Relative.lean:336] (exact)

- `relative_error_N_FLT'_ex` → `relative_error_N_FLT'_ex` [Relative.lean:344] (exact)

- `relative_error_N_FLT'_ex_separate` → `relative_error_N_FLT'_ex_separate` [Relative.lean:354] (exact)

- `error_N_FLT` → `error_N_FLT` [Relative.lean:365] (exact)

## File: Round_odd.v → Round_odd.lean


### Coq Declarations

- Lemma: `Zrnd_odd_Zodd`

- Lemma: `Zfloor_plus`

- Lemma: `Zceil_plus`

- Lemma: `Zeven_abs`

- Lemma: `Zrnd_odd_plus`

- Theorem: `Rnd_odd_pt_opp_inv`

- Theorem: `round_odd_opp`

- Theorem: `round_odd_pt`

- Theorem: `Rnd_odd_pt_unique`

- Theorem: `Rnd_odd_pt_monotone`

- Lemma: `generic_format_fexpe_fexp`

- Lemma: `exists_even_fexp_lt`

- Lemma: `d_eq`

- Lemma: `u_eq`

- Lemma: `d_ge_0`

- Lemma: `mag_d`

- Lemma: `Fexp_d`

- Lemma: `format_bpow_x`

- Lemma: `format_bpow_d`

- Lemma: `d_le_m`

- Lemma: `m_le_u`

- Lemma: `mag_m`

- Lemma: `mag_m_0`

- Lemma: `u'_eq`

- Lemma: `m_eq`

- Lemma: `m_eq_0`

- Lemma: `fexp_m_eq_0`

- Lemma: `Fm`

- Lemma: `Zm`

- Lemma: `DN_odd_d_aux`

- Lemma: `UP_odd_d_aux`

- Lemma: `round_N_odd_pos`

- Theorem: `round_N_odd`

- Lemma: `Zrnd_odd_plus'`

- Theorem: `mag_round_odd`

- Theorem: `fexp_round_odd`


### Lean Declarations

- theorem: `round_odd_ge_ulp` (Round_odd.lean:27)

- theorem: `round_odd_double_round` (Round_odd.lean:33)

- theorem: `generic_format_round_odd` (Round_odd.lean:43)


### Mapping (Coq → Lean)

- `Zrnd_odd_Zodd` → (no direct Lean match found)

- `Zfloor_plus` → (no direct Lean match found)

- `Zceil_plus` → (no direct Lean match found)

- `Zeven_abs` → (no direct Lean match found)

- `Zrnd_odd_plus` → (no direct Lean match found)

- `Rnd_odd_pt_opp_inv` → (no direct Lean match found)

- `round_odd_opp` → (no direct Lean match found)

- `round_odd_pt` → (no direct Lean match found)

- `Rnd_odd_pt_unique` → (no direct Lean match found)

- `Rnd_odd_pt_monotone` → (no direct Lean match found)

- `generic_format_fexpe_fexp` → (no direct Lean match found)

- `exists_even_fexp_lt` → (no direct Lean match found)

- `d_eq` → (no direct Lean match found)

- `u_eq` → (no direct Lean match found)

- `d_ge_0` → (no direct Lean match found)

- `mag_d` → (no direct Lean match found)

- `Fexp_d` → (no direct Lean match found)

- `format_bpow_x` → (no direct Lean match found)

- `format_bpow_d` → (no direct Lean match found)

- `d_le_m` → (no direct Lean match found)

- `m_le_u` → (no direct Lean match found)

- `mag_m` → (no direct Lean match found)

- `mag_m_0` → (no direct Lean match found)

- `u'_eq` → (no direct Lean match found)

- `m_eq` → (no direct Lean match found)

- `m_eq_0` → (no direct Lean match found)

- `fexp_m_eq_0` → (no direct Lean match found)

- `Fm` → (no direct Lean match found)

- `Zm` → (no direct Lean match found)

- `DN_odd_d_aux` → (no direct Lean match found)

- `UP_odd_d_aux` → (no direct Lean match found)

- `round_N_odd_pos` → (no direct Lean match found)

- `round_N_odd` → (no direct Lean match found)

- `Zrnd_odd_plus'` → (no direct Lean match found)

- `mag_round_odd` → (no direct Lean match found)

- `fexp_round_odd` → (no direct Lean match found)

## File: Sterbenz.v → Sterbenz.lean


### Coq Declarations

- Theorem: `generic_format_plus`

- Theorem: `generic_format_plus_weak`

- Lemma: `sterbenz_aux`

- Theorem: `sterbenz`


### Lean Declarations

- theorem: `generic_format_plus` (Sterbenz.lean:16)

- theorem: `generic_format_plus_weak` (Sterbenz.lean:23)

- lemma: `sterbenz_aux` (Sterbenz.lean:30)

- theorem: `sterbenz` (Sterbenz.lean:37)


### Mapping (Coq → Lean)

- `generic_format_plus` → `generic_format_plus` [Sterbenz.lean:16] (exact)

- `generic_format_plus_weak` → `generic_format_plus_weak` [Sterbenz.lean:23] (exact)

- `sterbenz_aux` → `sterbenz_aux` [Sterbenz.lean:30] (exact)

- `sterbenz` → `sterbenz` [Sterbenz.lean:37] (exact)
