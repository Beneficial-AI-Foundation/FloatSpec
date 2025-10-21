# Calc Theorems Comparison (content-reviewed)

This file lists theorem-like declarations per file (Coq vs Lean) and records correspondences judged by statement intent. Names may differ; matches are based on content. Where no Lean counterpart is listed, it has not been ported yet or is not present in the Calc Lean files.

## File: Bracket.v → Bracket.lean

### Coq Declarations
- Theorem: `inbetween_spec`
- Theorem: `inbetween_unique`
- Theorem: `inbetween_bounds`
- Theorem: `inbetween_bounds_not_Eq`
- Theorem: `inbetween_distance_inexact`
- Theorem: `inbetween_distance_inexact_abs`
- Theorem: `inbetween_ex`
- Lemma: `ordered_steps`
- Lemma: `middle_range`
- Lemma: `inbetween_step_not_Eq`
- Theorem: `inbetween_step_Lo`
- Theorem: `inbetween_step_Hi`
- Theorem: `inbetween_step_Lo_not_Eq`
- Lemma: `middle_odd`
- Theorem: `inbetween_step_any_Mi_odd`
- Theorem: `inbetween_step_Lo_Mi_Eq_odd`
- Theorem: `inbetween_step_Hi_Mi_even`
- Theorem: `inbetween_step_Mi_Mi_even`
- Theorem: `new_location_even_correct`
- Theorem: `new_location_odd_correct`
- Theorem: `new_location_correct`
- Theorem: `inbetween_plus_compat`
- Theorem: `inbetween_plus_reg`
- Theorem: `inbetween_mult_compat`
- Theorem: `inbetween_mult_reg`
- Theorem: `inbetween_float_bounds`
- Theorem: `inbetween_float_new_location`
- Theorem: `inbetween_float_new_location_single`
- Theorem: `inbetween_float_ex`
- Theorem: `inbetween_float_unique`

### Lean Declarations
- theorem: `inbetween_spec` (Bracket.lean:97)
- theorem: `inbetween_unique` (Bracket.lean:128)
- theorem: `inbetween_bounds` (Bracket.lean:185)
- theorem: `inbetween_bounds_not_Eq` (Bracket.lean:203)
- theorem: `inbetween_distance_inexact` (Bracket.lean:221)
- theorem: `inbetween_distance_inexact_abs` (Bracket.lean:239)
- theorem: `inbetween_ex` (Bracket.lean:267)
- lemma: `ordered_steps` (Bracket.lean:367)
- lemma: `middle_range` (Bracket.lean:384)
- theorem: `inbetween_step_not_Eq` (Bracket.lean:403)
- theorem: `inbetween_step_Lo` (Bracket.lean:425)
- theorem: `inbetween_step_Hi` (Bracket.lean:445)
- theorem: `new_location_even_correct` (Bracket.lean:476)
- theorem: `new_location_odd_correct` (Bracket.lean:507)
- theorem: `new_location_correct` (Bracket.lean:530)

### Mapping (Coq → Lean)
- `inbetween_spec` → `inbetween_spec [Bracket.lean:96]` (exact)
- `inbetween_unique` → `inbetween_unique [Bracket.lean:127]` (exact)
- `inbetween_bounds` → `inbetween_bounds [Bracket.lean:184]` (exact)
- `inbetween_bounds_not_Eq` → `inbetween_bounds_not_Eq [Bracket.lean:202]` (exact)
- `inbetween_distance_inexact` → `inbetween_distance_inexact [Bracket.lean:220]` (exact)
- `inbetween_distance_inexact_abs` → `inbetween_distance_inexact_abs [Bracket.lean:238]` (exact)
- `inbetween_ex` → `inbetween_ex [Bracket.lean:266]` (exact)
- `ordered_steps` → `ordered_steps [Bracket.lean:365]` (exact)
- `middle_range` → `middle_range [Bracket.lean:397]` (exact)
- `inbetween_step_not_Eq` → `inbetween_step_not_Eq [Bracket.lean:416]` (exact)
- `inbetween_step_Lo` → `inbetween_step_Lo [Bracket.lean:438]` (exact)
- `inbetween_step_Hi` → `inbetween_step_Hi [Bracket.lean:458]` (exact)
- `inbetween_step_Lo_not_Eq` → `inbetween_step_Lo_not_Eq [Bracket.lean:553]` (stubbed, placeholder proof)
- `middle_odd` → `middle_odd [Bracket.lean:562]` (stubbed, placeholder proof)
- `inbetween_step_any_Mi_odd` → `inbetween_step_any_Mi_odd [Bracket.lean:569]` (stubbed, placeholder proof)
- `inbetween_step_Lo_Mi_Eq_odd` → `inbetween_step_Lo_Mi_Eq_odd [Bracket.lean:577]` (stubbed, placeholder proof)
- `inbetween_step_Hi_Mi_even` → `inbetween_step_Hi_Mi_even [Bracket.lean:585]` (stubbed, placeholder proof)
- `inbetween_step_Mi_Mi_even` → `inbetween_step_Mi_Mi_even [Bracket.lean:594]` (stubbed, placeholder proof)
- `new_location_even_correct` → `new_location_even_correct [Bracket.lean:489]` (exact)
- `new_location_odd_correct` → `new_location_odd_correct [Bracket.lean:520]` (exact)
- `new_location_correct` → `new_location_correct [Bracket.lean:543]` (exact)
- `inbetween_plus_compat` → `inbetween_plus_compat [Bracket.lean:603]` (stubbed, placeholder proof)
- `inbetween_plus_reg` → `inbetween_plus_reg [Bracket.lean:607]` (stubbed, placeholder proof)
- `inbetween_mult_compat` → `inbetween_mult_compat [Bracket.lean:611]` (stubbed, placeholder proof)
- `inbetween_mult_reg` → `inbetween_mult_reg [Bracket.lean:616]` (stubbed, placeholder proof)
- `inbetween_float_bounds` → `inbetween_float_bounds [Bracket.lean:624]` (stubbed, placeholder proof)
- `inbetween_float_new_location` → `inbetween_float_new_location [Bracket.lean:637]` (stubbed, placeholder proof)
- `inbetween_float_new_location_single` → `inbetween_float_new_location_single [Bracket.lean:645]` (stubbed, placeholder proof)
- `inbetween_float_ex` → `inbetween_float_ex [Bracket.lean:651]` (stubbed, placeholder proof)
- `inbetween_float_unique` → `inbetween_float_unique [Bracket.lean:656]` (stubbed, placeholder proof)

## File: Operations.v → Operations.lean

### Coq Declarations
- Theorem: `Falign_spec`
- Theorem: `Falign_spec_exp`
- Theorem: `F2R_opp`
- Theorem: `F2R_abs`
- Theorem: `F2R_plus`
- Theorem: `Fplus_same_exp`
- Theorem: `Fexp_Fplus`
- Theorem: `F2R_minus`
- Theorem: `Fminus_same_exp`
- Theorem: `F2R_mult`

### Lean Declarations
- theorem: `Falign_spec` (Operations.lean:47)
- theorem: `Falign_spec_exp` (Operations.lean:85)
- theorem: `F2R_opp` (Operations.lean:108)
- theorem: `F2R_abs` (Operations.lean:132)
- theorem: `F2R_plus` (Operations.lean:161)
- theorem: `Fplus_same_exp_spec` (Operations.lean:270)
- theorem: `Fexp_Fplus_spec` (Operations.lean:289)
- theorem: `F2R_minus` (Operations.lean:313)
- theorem: `Fminus_same_exp_spec` (Operations.lean:424)
- theorem: `F2R_mult` (Operations.lean:447)

### Mapping (Coq → Lean)
- `Falign_spec` → `Falign_spec [Operations.lean:47]` (exact)
- `Falign_spec_exp` → `Falign_spec_exp [Operations.lean:85]` (exact)
- `F2R_opp` → `F2R_opp [Operations.lean:108]` (exact)
- `F2R_abs` → `F2R_abs [Operations.lean:132]` (exact)
- `F2R_plus` → `F2R_plus [Operations.lean:161]` (exact)
- `Fplus_same_exp` → `Fplus_same_exp_spec [Operations.lean:270]` (content-equivalent)
- `Fexp_Fplus` → `Fexp_Fplus_spec [Operations.lean:289]` (content-equivalent)
- `F2R_minus` → `F2R_minus [Operations.lean:313]` (exact)
- `Fminus_same_exp` → `Fminus_same_exp_spec [Operations.lean:424]` (content-equivalent)
- `F2R_mult` → `F2R_mult [Operations.lean:447]` (exact)

## File: Plus.v → Plus.lean

### Coq Declarations
- Theorem: `Fplus_core_correct`
- Theorem: `Fplus_correct`

### Lean Declarations
- theorem: `Fplus_core_correct` (Plus.lean:45)
- theorem: `Fplus_correct` (Plus.lean:214)

### Mapping (Coq → Lean)
- `Fplus_core_correct` → `Fplus_core_correct [Plus.lean:45]` (exact)
- `Fplus_correct` → `Fplus_correct [Plus.lean:214]` (exact)

## File: Div.v → Div.lean

### Coq Declarations
- Lemma: `mag_div_F2R`
- Theorem: `Fdiv_core_correct`
- Theorem: `Fdiv_correct`

### Lean Declarations
- lemma: `mag_div_F2R` (Div.lean:44)
- theorem: `Fdiv_core_correct` (Div.lean:112)
- theorem: `Fdiv_correct` (Div.lean:344)

### Mapping (Coq → Lean)
- `mag_div_F2R` → `mag_div_F2R [Div.lean:44]` (exact)
- `Fdiv_core_correct` → `Fdiv_core_correct [Div.lean:112]` (exact)
- `Fdiv_correct` → `Fdiv_correct [Div.lean:344]` (exact)

## File: Sqrt.v → Sqrt.lean

### Coq Declarations
- Lemma: `mag_sqrt_F2R`
- Theorem: `Fsqrt_core_correct`
- Theorem: `Fsqrt_correct`

### Lean Declarations
- lemma: `mag_sqrt_F2R` (Sqrt.lean:46)
- theorem: `Fsqrt_core_correct` (Sqrt.lean:82)
- theorem: `Fsqrt_correct` (Sqrt.lean:124)

### Mapping (Coq → Lean)
- `mag_sqrt_F2R` → `mag_sqrt_F2R [Sqrt.lean:46]` (exact)
- `Fsqrt_core_correct` → `Fsqrt_core_correct [Sqrt.lean:82]` (exact)
- `Fsqrt_correct` → `Fsqrt_correct [Sqrt.lean:124]` (exact)

## File: Round.v → Round.lean

### Coq Declarations
- Theorem: `cexp_inbetween_float`
- Theorem: `cexp_inbetween_float_loc_Exact`
- Theorem: `inbetween_float_round`
- Lemma: `le_cond_incr_le`
- Theorem: `inbetween_float_round_sign`
- Theorem: `inbetween_int_DN`
- Theorem: `inbetween_float_DN`
- Theorem: `inbetween_int_DN_sign`
- Theorem: `inbetween_float_DN_sign`
- Theorem: `inbetween_int_UP`
- Theorem: `inbetween_float_UP`
- Theorem: `inbetween_int_UP_sign`
- Theorem: `inbetween_float_UP_sign`
- Theorem: `inbetween_int_ZR`
- Theorem: `inbetween_float_ZR`
- Theorem: `inbetween_int_ZR_sign`
- Theorem: `inbetween_float_ZR_sign`
- Theorem: `inbetween_int_N`
- Theorem: `inbetween_int_N_sign`
- Theorem: `inbetween_int_NE`
- Theorem: `inbetween_float_NE`
- Theorem: `inbetween_int_NE_sign`
- Theorem: `inbetween_float_NE_sign`
- Theorem: `inbetween_int_NA`
- Theorem: `inbetween_float_NA`
- Theorem: `inbetween_int_NA_sign`
- Theorem: `inbetween_float_NA_sign`
- Theorem: `truncate_aux_comp`
- Theorem: `truncate_0`
- Theorem: `generic_format_truncate`
- Theorem: `truncate_correct_format`
- Theorem: `truncate_correct_partial'`
- Theorem: `truncate_correct_partial`
- Theorem: `truncate_correct'`
- Theorem: `truncate_correct`
- Theorem: `round_any_correct`
- Theorem: `round_trunc_any_correct`
- Theorem: `round_trunc_any_correct'`
- Theorem: `round_sign_any_correct`
- Theorem: `round_trunc_sign_any_correct'`
- Theorem: `round_trunc_sign_any_correct`
- Theorem: `truncate_FIX_correct`

### Lean Declarations
- theorem: `truncate_spec` (Round.lean:49)
- theorem: `Fround_spec` (Round.lean:72)
// Imported placeholders mirroring Coq theorems (to be proven)
- theorem: `cexp_inbetween_float` (Round.lean:103)
- theorem: `cexp_inbetween_float_loc_Exact` (Round.lean:117)
- theorem: `inbetween_float_round` (Round.lean:128)
- lemma: `le_cond_incr_le` (Round.lean:139)
- theorem: `inbetween_float_round_sign` (Round.lean:144)
- theorem: `inbetween_int_DN` (Round.lean:156)
- theorem: `inbetween_float_DN` (Round.lean:161)
- theorem: `inbetween_int_DN_sign` (Round.lean:170)
- theorem: `inbetween_float_DN_sign` (Round.lean:179)
- theorem: `inbetween_int_UP` (Round.lean:189)
- theorem: `inbetween_float_UP` (Round.lean:194)
- theorem: `inbetween_int_ZR` (Round.lean:202)
- theorem: `inbetween_float_ZR` (Round.lean:208)
- theorem: `inbetween_int_N` (Round.lean:215)
- theorem: `inbetween_int_N_sign` (Round.lean:218)
- theorem: `inbetween_int_NE` (Round.lean:221)
- theorem: `inbetween_float_NE` (Round.lean:224)
- theorem: `inbetween_int_NE_sign` (Round.lean:227)
- theorem: `inbetween_float_NE_sign` (Round.lean:230)
- theorem: `inbetween_int_NA` (Round.lean:233)
- theorem: `inbetween_float_NA` (Round.lean:236)
- theorem: `inbetween_int_NA_sign` (Round.lean:239)
- theorem: `inbetween_float_NA_sign` (Round.lean:242)
- theorem: `truncate_aux_comp` (Round.lean:245)
- theorem: `truncate_0` (Round.lean:248)
- theorem: `generic_format_truncate` (Round.lean:251)
- theorem: `truncate_correct_format` (Round.lean:254)
- theorem: `truncate_correct_partial'` (Round.lean:257)
- theorem: `truncate_correct_partial` (Round.lean:260)
- theorem: `truncate_correct'` (Round.lean:263)
- theorem: `truncate_correct` (Round.lean:266)
- theorem: `round_any_correct` (Round.lean:269)
- theorem: `round_trunc_any_correct` (Round.lean:272)
- theorem: `round_trunc_any_correct'` (Round.lean:275)
- theorem: `round_sign_any_correct` (Round.lean:278)
- theorem: `round_trunc_sign_any_correct'` (Round.lean:281)
- theorem: `round_trunc_sign_any_correct` (Round.lean:284)
- theorem: `truncate_FIX_correct` (Round.lean:287)

### Mapping (Coq → Lean)
- `cexp_inbetween_float` → `cexp_inbetween_float [Round.lean:103]` (stubbed)
- `cexp_inbetween_float_loc_Exact` → `cexp_inbetween_float_loc_Exact [Round.lean:117]` (stubbed)
- `inbetween_float_round` → `inbetween_float_round [Round.lean:128]` (stubbed)
- `le_cond_incr_le` → `le_cond_incr_le [Round.lean:139]` (stubbed)
- `inbetween_float_round_sign` → `inbetween_float_round_sign [Round.lean:144]` (stubbed)
- `inbetween_int_DN` → `inbetween_int_DN [Round.lean:156]` (stubbed)
- `inbetween_float_DN` → `inbetween_float_DN [Round.lean:161]` (stubbed)
- `inbetween_int_DN_sign` → `inbetween_int_DN_sign [Round.lean:170]` (stubbed)
- `inbetween_float_DN_sign` → `inbetween_float_DN_sign [Round.lean:179]` (stubbed)
- `inbetween_int_UP` → `inbetween_int_UP [Round.lean:189]` (stubbed)
- `inbetween_float_UP` → `inbetween_float_UP [Round.lean:194]` (stubbed)
- `inbetween_int_UP_sign` → (not added)
- `inbetween_float_UP_sign` → (not added)
- `inbetween_int_ZR` → `inbetween_int_ZR [Round.lean:202]` (stubbed)
- `inbetween_float_ZR` → `inbetween_float_ZR [Round.lean:208]` (stubbed)
- `inbetween_int_ZR_sign` → (not added)
- `inbetween_float_ZR_sign` → (not added)
- `inbetween_int_N` → `inbetween_int_N [Round.lean:215]` (stubbed)
- `inbetween_int_N_sign` → `inbetween_int_N_sign [Round.lean:218]` (stubbed)
- `inbetween_int_NE` → `inbetween_int_NE [Round.lean:221]` (stubbed)
- `inbetween_float_NE` → `inbetween_float_NE [Round.lean:224]` (stubbed)
- `inbetween_int_NE_sign` → `inbetween_int_NE_sign [Round.lean:227]` (stubbed)
- `inbetween_float_NE_sign` → `inbetween_float_NE_sign [Round.lean:230]` (stubbed)
- `inbetween_int_NA` → `inbetween_int_NA [Round.lean:233]` (stubbed)
- `inbetween_float_NA` → `inbetween_float_NA [Round.lean:236]` (stubbed)
- `inbetween_int_NA_sign` → `inbetween_int_NA_sign [Round.lean:239]` (stubbed)
- `inbetween_float_NA_sign` → `inbetween_float_NA_sign [Round.lean:242]` (stubbed)
- `truncate_aux_comp` → `truncate_aux_comp [Round.lean:245]` (stubbed)
- `truncate_0` → `truncate_0 [Round.lean:248]` (stubbed)
- `generic_format_truncate` → `generic_format_truncate [Round.lean:251]` (stubbed)
- `truncate_correct_format` → `truncate_correct_format [Round.lean:254]` (stubbed)
- `truncate_correct_partial'` → `truncate_correct_partial' [Round.lean:257]` (stubbed)
- `truncate_correct_partial` → `truncate_correct_partial [Round.lean:260]` (stubbed)
- `truncate_correct'` → `truncate_correct' [Round.lean:263]` (stubbed)
- `truncate_correct` → `truncate_correct [Round.lean:266]` (stubbed)
- `round_any_correct` → `round_any_correct [Round.lean:269]` (stubbed)
- `round_trunc_any_correct` → `round_trunc_any_correct [Round.lean:272]` (stubbed)
- `round_trunc_any_correct'` → `round_trunc_any_correct' [Round.lean:275]` (stubbed)
- `round_sign_any_correct` → `round_sign_any_correct [Round.lean:278]` (stubbed)
- `round_trunc_sign_any_correct'` → `round_trunc_sign_any_correct' [Round.lean:281]` (stubbed)
- `round_trunc_sign_any_correct` → `round_trunc_sign_any_correct [Round.lean:284]` (stubbed)
- `truncate_FIX_correct` → `truncate_FIX_correct [Round.lean:287]` (stubbed)
