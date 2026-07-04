# Missing Flocq Infrastructure

This document names the remaining infrastructure that blocks a product-grade
FloatSpec/Flocq translation. It focuses on concrete theorem and definition
names rather than broad labels.

The `Branch Diff Audit` section is the revert list. Later sections describe
supporting infrastructure; they should not be read as additional exact
branch-diff revert targets unless explicitly stated.

## Faithful Translation Completion Audit (2026-07-04)

This is the broad completion target for making FloatSpec a faithful Flocq
translation. It supersedes the older branch-diff/scaffold queue as the
definition of "done". The older queue only tracked active wrappers removed
or weakened by branch work; this audit checks every parsed public upstream
Flocq declaration name against all Lean declarations in `FloatSpec/**/*.lean`.

Audit basis:

- Upstream source: `/mnt2/users/kaile/hantao/flocq-upstream/src/**/*.v`.
- Lean source: `FloatSpec/**/*.lean`.
- Coq declarations parsed: `Theorem`, `Lemma`, `Definition`, `Fixpoint`,
  `Inductive`, `Record`, `Variant`, `CoInductive`, `Corollary`,
  `Proposition`, `Remark`, `Fact`, `Instance`, `Class`, `Axiom`, and
  `Parameter`, after stripping Coq comments.
- Local Coq declarations are excluded from the public-name count; duplicate
  upstream public names are counted once by first occurrence.
- Lean declarations parsed: `def`, `theorem`, `lemma`, `inductive`,
  `structure`, `abbrev`, `opaque`, `axiom`, `constant`, `class`, and
  `instance`, including common modifiers such as `public`, `private`,
  `protected`, and `noncomputable`.

Current broad exact-name result and counterpart-filtered status:

- Unique public upstream Flocq declarations scanned: 2378.
- Unique Lean declaration names scanned: 4257.
- Missing exact public upstream declaration names: 355.
- Counterpart-audited false semantic gaps removed from the active list so far:
  100.
- Active semantic gap candidates still listed below: 255.
- Files with at least one active listed candidate: 13.
- Counterpart audit coverage for the active list: 255/255 names have been
  explicitly checked and mentioned in the notes below; none of the remaining
  active names currently has a faithful exact, renamed, formatted, or split
  Lean counterpart in the current workspace.
- Current placeholder/trust audit remains a separate gate: 56 findings
  (`sorry = 0`, `axiom = 0`, `admit = 0`, but 40 placeholder-text
  findings, 13 `True`-definition findings, 2 `True`-relation findings,
  and 1 identity-hint finding).

Completion criteria for this document:

1. The active semantic gap list below reaches 0 entries after exact-name
   restoration or statement-level counterpart confirmation.
2. The placeholder/trust audit reaches 0 findings, or every remaining
   finding is explicitly classified as scanner/meta noise with a source
   reason and not a theorem/spec payload gap.
3. `rg -n "\b(sorry|axiom|admit)\b" FloatSpec --glob "*.lean"` has no
   live proof-hole declarations. Comment-only hits must be removed or
   explicitly classified.
4. `lake build` succeeds.
5. Same-name declarations that were previously weakened must be checked
   statement-by-statement against Flocq when touched; exact-name presence
   alone is not semantic proof of fidelity.

Next implementation goal:

Fix the remaining Flocq import gaps by working through the 255 active
semantic gap candidates below in dependency order. For each name, either add
the exact public Lean declaration with the upstream Flocq payload, or replace
the ledger entry with a statement-level proof that an existing Lean theorem,
definition, instance, or split theorem family is a faithful counterpart. Do
not count helper-only, weaker, reverse-direction, experimental, or
tautological declarations as complete. The goal is finished only when this
active list is empty, the placeholder/trust audit is clean or fully
classified, and `lake build` succeeds.

Why this was not imported earlier: the previous `Branch Diff Audit` was a
narrow active-wrapper/scaffold queue, not a full upstream declaration
inventory. It was useful for closing local build blockers, but it did not
ask whether every public declaration in every Flocq source file had an exact
Lean counterpart. This section is the broader inventory.

### Active Semantic Gap Candidates

This list starts from the broad exact-name scan, then removes checked names
whose Flocq payload is already faithfully represented in FloatSpec under a
different Lean name, anonymous instance, or split form. Unchecked entries stay
listed until inspected one by one.

#### `Core/Digits.v` (4)

- `Zdigit_ext` (Theorem, upstream line 290)
- `Zdigit_plus` (Theorem, upstream line 408)
- `Zdigit_scale` (Theorem, upstream line 447)
- `Zslice_div_pow_scale` (Theorem, upstream line 656)

#### `Core/FIX.v` (2)

- `FIX_exp_monotone` (Instance, upstream line 78)
- `exists_NE_FIX` (Instance, upstream line 96)

#### `Core/FLT.v` (1)

- `exists_NE_FLT` (Instance, upstream line 157)

#### `Core/FLX.v` (1)

- `exists_NE_FLX` (Instance, upstream line 363)

#### `Core/Generic_fmt.v` (3)

- `valid_rnd_AW` (Instance, upstream line 888)
- `valid_rnd_NA` (Instance, upstream line 1984)
- `valid_rnd_N0` (Instance, upstream line 2046)

#### `Core/Raux.v` (7)

- `Rabs_lt` (Theorem, upstream line 270)
- `Rabs_gt_inv` (Theorem, upstream line 300)
- `Rcompare_middle` (Theorem, upstream line 549)
- `Rcompare_floor_ceil_middle` (Theorem, upstream line 1181)
- `Rcompare_ceil_floor_middle` (Theorem, upstream line 1211)
- `cond_Ropp_Rlt_bool` (Theorem, upstream line 2198)
- `Rlt_bool_cond_Ropp` (Theorem, upstream line 2209)

#### `Core/Round_pred.v` (8)

- `satisfies_any_eq` (Theorem, upstream line 1386)
- `satisfies_any_imp_DN` (Theorem, upstream line 1412)
- `satisfies_any_imp_UP` (Theorem, upstream line 1423)
- `satisfies_any_imp_ZR` (Theorem, upstream line 1440)
- `NG_existence_prop` (Definition, upstream line 1477)
- `satisfies_any_imp_NG` (Theorem, upstream line 1480)
- `satisfies_any_imp_NA` (Theorem, upstream line 1622)
- `satisfies_any_imp_N0` (Theorem, upstream line 1658)

#### `Core/Zaux.v` (3)

- `eqbool_dep` (Definition, upstream line 52)
- `Zpos_div_eucl_aux1_correct` (Lemma, upstream line 873)
- `Zpos_div_eucl_aux_correct` (Lemma, upstream line 919)

#### `IEEE754/Binary.v` (18)

- `full_float` (Inductive, upstream line 32)
- `nan_pl` (Definition, upstream line 160)
- `binary_float` (Inductive, upstream line 180)
- `Bcompare` (Definition, upstream line 768)
- `Bmult` (Definition, upstream line 944)
- `Bmult_correct` (Theorem, upstream line 949)
- `Bplus` (Definition, upstream line 1046)
- `Bplus_correct` (Theorem, upstream line 1051)
- `Bminus` (Definition, upstream line 1083)
- `Bfma` (Definition, upstream line 1125)
- `Bdiv` (Definition, upstream line 1159)
- `Bsqrt` (Definition, upstream line 1190)
- `Bnearbyint` (Definition, upstream line 1209)
- `Btrunc` (Definition, upstream line 1228)
- `Bmax_float` (Definition, upstream line 1265)
- `Bnormfr_mantissa` (Definition, upstream line 1268)
- `Bulp` (Definition, upstream line 1365)
- `Bulp_correct` (Theorem, upstream line 1374)

#### `IEEE754/BinarySingleNaN.v` (54)

- `SF2B'` (Definition, upstream line 72)
- `SF2B'_B2SF` (Theorem, upstream line 248)
- `Bsign_SF2B` (Theorem, upstream line 342)
- `is_finite_SF2B` (Theorem, upstream line 363)
- `is_nan_SF2B` (Theorem, upstream line 409)
- `is_nan_Bopp` (Theorem, upstream line 469)
- `is_finite_strict_Bopp` (Theorem, upstream line 483)
- `is_nan_Babs` (Theorem, upstream line 512)
- `is_finite_strict_Babs` (Theorem, upstream line 526)
- `shr_m_shr_record_of_loc` (Theorem, upstream line 862)
- `loc_of_shr_record_of_loc` (Theorem, upstream line 871)
- `inbetween_shr_1` (Lemma, upstream line 878)
- `shr_nat` (Lemma, upstream line 913)
- `le_shr1_le` (Lemma, upstream line 924)
- `inbetween_shr` (Theorem, upstream line 934)
- `le_shr_le` (Lemma, upstream line 967)
- `shr_limit` (Lemma, upstream line 999)
- `shr_truncate` (Theorem, upstream line 1038)
- `choice_mode` (Definition, upstream line 1139)
- `le_choice_mode_le` (Lemma, upstream line 1148)
- `round_mode_choice_mode` (Lemma, upstream line 1154)
- `overflow_to_inf` (Definition, upstream line 1172)
- `is_nan_binary_overflow` (Theorem, upstream line 1185)
- `binary_overflow_correct` (Theorem, upstream line 1194)
- `binary_fit_aux` (Definition, upstream line 1228)
- `binary_fit_aux_correct` (Theorem, upstream line 1232)
- `Bmult_correct_aux` (Lemma, upstream line 1523)
- `shl_align_correct'` (Theorem, upstream line 1620)
- `shl_align_correct` (Theorem, upstream line 1643)
- `snd_shl_align` (Theorem, upstream line 1667)
- `is_nan_binary_round` (Theorem, upstream line 1735)
- `is_nan_binary_normalize` (Theorem, upstream line 1817)
- `Fplus_naive` (Definition, upstream line 1834)
- `Fplus_naive_correct` (Lemma, upstream line 1839)
- `sign_plus_overflow` (Lemma, upstream line 1863)
- `SFnearbyint_binary_aux` (Definition, upstream line 2507)
- `SFnearbyint_binary` (Definition, upstream line 2519)
- `Bnearbyint_correct_aux` (Lemma, upstream line 2530)
- `is_finite_strict_Bone` (Theorem, upstream line 2747)
- `is_nan_Bone` (Theorem, upstream line 2755)
- `Bmax_float_proof` (Lemma, upstream line 2781)
- `Bnormfr_mantissa_correct` (Lemma, upstream line 2821)
- `Ffrexp_core_binary` (Definition, upstream line 2924)
- `Bulp_correct_aux` (Lemma, upstream line 3083)
- `is_nan_Bulp` (Theorem, upstream line 3106)
- `is_finite_strict_Bulp` (Theorem, upstream line 3156)
- `Bulp'` (Definition, upstream line 3172)
- `Bulp'_correct` (Theorem, upstream line 3174)
- `is_nan_Bsucc` (Theorem, upstream line 3253)
- `is_nan_Bpred` (Theorem, upstream line 3413)
- `Bpred_pos'` (Definition, upstream line 3452)
- `Bpred_pos'_correct` (Theorem, upstream line 3464)
- `Bsucc'` (Definition, upstream line 3660)
- `Bsucc'_correct` (Theorem, upstream line 3670)

#### `IEEE754/Bits.v` (41)

- `bits_of_binary_float` (Definition, upstream line 219)
- `split_bits_of_binary_float` (Definition, upstream line 232)
- `binary_float_of_bits` (Definition, upstream line 490)
- `binary32` (Definition, upstream line 619)
- `default_nan_pl32` (Definition, upstream line 637)
- `unop_nan_pl32` (Definition, upstream line 640)
- `binop_nan_pl32` (Definition, upstream line 646)
- `ternop_nan_pl32` (Definition, upstream line 653)
- `b32_erase` (Definition, upstream line 661)
- `b32_opp` (Definition, upstream line 663)
- `b32_abs` (Definition, upstream line 664)
- `b32_pred` (Definition, upstream line 665)
- `b32_succ` (Definition, upstream line 666)
- `b32_sqrt` (Definition, upstream line 667)
- `b32_plus` (Definition, upstream line 668)
- `b32_minus` (Definition, upstream line 670)
- `b32_mult` (Definition, upstream line 671)
- `b32_div` (Definition, upstream line 672)
- `b32_fma` (Definition, upstream line 673)
- `b32_compare` (Definition, upstream line 675)
- `b32_of_bits` (Definition, upstream line 677)
- `bits_of_b32` (Definition, upstream line 678)
- `binary64` (Definition, upstream line 686)
- `default_nan_pl64` (Definition, upstream line 704)
- `unop_nan_pl64` (Definition, upstream line 707)
- `binop_nan_pl64` (Definition, upstream line 713)
- `ternop_nan_pl64` (Definition, upstream line 720)
- `b64_erase` (Definition, upstream line 728)
- `b64_opp` (Definition, upstream line 730)
- `b64_abs` (Definition, upstream line 731)
- `b64_pred` (Definition, upstream line 732)
- `b64_succ` (Definition, upstream line 733)
- `b64_sqrt` (Definition, upstream line 734)
- `b64_plus` (Definition, upstream line 735)
- `b64_minus` (Definition, upstream line 737)
- `b64_mult` (Definition, upstream line 738)
- `b64_div` (Definition, upstream line 739)
- `b64_fma` (Definition, upstream line 740)
- `b64_compare` (Definition, upstream line 742)
- `b64_of_bits` (Definition, upstream line 744)
- `bits_of_b64` (Definition, upstream line 745)

#### `IEEE754/PrimFloat.v` (9)

- `Prim2B` (Definition, upstream line 27)
- `B2Prim` (Definition, upstream line 32)
- `round_nearest_even_equiv` (Lemma, upstream line 125)
- `binary_round_aux_equiv` (Lemma, upstream line 133)
- `mul_equiv` (Theorem, upstream line 143)
- `binary_round_equiv` (Lemma, upstream line 161)
- `binary_normalize_equiv` (Lemma, upstream line 170)
- `add_equiv` (Theorem, upstream line 181)
- `normfr_mantissa_equiv` (Theorem, upstream line 258)

#### `Pff/Pff.v` (104)

- `errorBoundedMultClosest` (Theorem, upstream line 9057)
- `plusExact2Aux` (Theorem, upstream line 10274)
- `plusExact2` (Theorem, upstream line 10379)
- `plusExactExp` (Theorem, upstream line 10436)
- `UlpFlessuGe` (Theorem, upstream line 11675)
- `UlpFlessuGe2` (Theorem, upstream line 11885)
- `Axpy_opt` (Theorem, upstream line 12301)
- `ClosestSuccPred` (Theorem, upstream line 12521)
- `ImplyClosest` (Theorem, upstream line 12599)
- `ImplyClosestStrict` (Theorem, upstream line 12696)
- `ImplyClosestStrict2` (Theorem, upstream line 12788)
- `ClosestImplyEven` (Theorem, upstream line 12814)
- `ClosestImplyEven_int` (Theorem, upstream line 12888)
- `hxExact` (Lemma, upstream line 13055)
- `eqLeep` (Lemma, upstream line 13165)
- `epLe` (Lemma, upstream line 13182)
- `eqLe` (Lemma, upstream line 13220)
- `eqGe` (Lemma, upstream line 13547)
- `eqEqual` (Lemma, upstream line 13761)
- `Veltkamp_aux_aux` (Lemma, upstream line 13770)
- `Veltkamp_aux` (Lemma, upstream line 14021)
- `VeltkampEven1` (Lemma, upstream line 14188)
- `VeltkampEven2` (Lemma, upstream line 14483)
- `Veltkamp_pos` (Lemma, upstream line 14709)
- `VeltkampN_aux` (Lemma, upstream line 14788)
- `VeltkampN` (Lemma, upstream line 14832)
- `VeltkampEven_pos` (Lemma, upstream line 14856)
- `VeltkampEvenN_aux` (Lemma, upstream line 14942)
- `VeltkampEvenN` (Lemma, upstream line 15000)
- `bimplybplusNorm` (Lemma, upstream line 15051)
- `Closestbbplus` (Lemma, upstream line 15120)
- `EvenClosestbplusb` (Lemma, upstream line 15287)
- `ClosestClosest` (Lemma, upstream line 15367)
- `EvenClosestbbplus` (Lemma, upstream line 15448)
- `VeltkampS` (Lemma, upstream line 15559)
- `VeltkampEvenS` (Lemma, upstream line 15734)
- `VeltkampEven` (Theorem, upstream line 15944)
- `Veltkamp_tail_aux` (Theorem, upstream line 16001)
- `Veltkamp_tail2` (Theorem, upstream line 16157)
- `VeltkampU` (Theorem, upstream line 16270)
- `BoundedL` (Theorem, upstream line 16329)
- `Closestbbext` (Theorem, upstream line 16377)
- `Underf_Err1` (Theorem, upstream line 16555)
- `Underf_Err2_aux` (Theorem, upstream line 16610)
- `Underf_Err2` (Theorem, upstream line 16750)
- `Underf_Err3` (Theorem, upstream line 16774)
- `Underf_Err3_bis` (Theorem, upstream line 16899)
- `eLe` (Lemma, upstream line 17049)
- `rExp` (Lemma, upstream line 17107)
- `Boundedt1` (Lemma, upstream line 17177)
- `Boundedt2` (Lemma, upstream line 17248)
- `Boundedt3` (Lemma, upstream line 17288)
- `Boundedt4` (Lemma, upstream line 17329)
- `Boundedt4_aux` (Lemma, upstream line 17342)
- `Boundedx1y1_aux` (Lemma, upstream line 17388)
- `Boundedx1y1` (Lemma, upstream line 17413)
- `Boundedx1y2_aux` (Lemma, upstream line 17421)
- `Boundedx1y2` (Lemma, upstream line 17443)
- `Boundedx2y1_aux` (Lemma, upstream line 17448)
- `Boundedx2y1` (Lemma, upstream line 17470)
- `Dekker_aux` (Theorem, upstream line 17588)
- `Boundedx2y2` (Theorem, upstream line 17707)
- `DekkerN` (Theorem, upstream line 17819)
- `DekkerS1` (Theorem, upstream line 17877)
- `DekkerS2` (Theorem, upstream line 18130)
- `Dekker1` (Theorem, upstream line 18385)
- `Veltkampb'` (Theorem, upstream line 18421)
- `NormalbPrim` (Theorem, upstream line 18513)
- `Dekker2_aux` (Theorem, upstream line 18573)
- `Dekker2` (Theorem, upstream line 18822)
- `Twice_EvenClosest_Round` (Theorem, upstream line 19178)
- `errorBoundedMultClosest_Can` (Theorem, upstream line 19729)
- `AddExpGe1Underf` (Theorem, upstream line 22351)
- `AddExpGe1Underf2` (Theorem, upstream line 22416)
- `cases` (Theorem, upstream line 22504)
- `xLe2y_aux1` (Lemma, upstream line 23476)
- `xLe2y_aux2` (Lemma, upstream line 23522)
- `yLe2x_aux` (Lemma, upstream line 23595)
- `xLe2y` (Lemma, upstream line 23707)
- `yLe2x` (Lemma, upstream line 23717)
- `Subexact` (Lemma, upstream line 23726)
- `LSB_Pred` (Lemma, upstream line 23794)
- `Midpoint_aux_aux` (Lemma, upstream line 23846)
- `Midpoint_aux` (Lemma, upstream line 24208)
- `gatCorrect` (Lemma, upstream line 24295)
- `Expr1` (Lemma, upstream line 24443)
- `Expbe1` (Lemma, upstream line 24480)
- `be2MuchSmaller` (Lemma, upstream line 24522)
- `gaCorrect` (Lemma, upstream line 24617)
- `tBounded_aux` (Theorem, upstream line 25145)
- `tBounded` (Theorem, upstream line 25532)
- `ErrFmaApprox_1_aux` (Theorem, upstream line 25626)
- `ErrFmaApprox_1` (Theorem, upstream line 25719)
- `LeExp1` (Lemma, upstream line 25911)
- `LeExp2` (Lemma, upstream line 25920)
- `LeExp3` (Lemma, upstream line 26016)
- `LeExp` (Lemma, upstream line 26106)
- `vLe_aux` (Lemma, upstream line 26117)
- `vLe` (Lemma, upstream line 26137)
- `tLe` (Lemma, upstream line 26151)
- `wLe` (Lemma, upstream line 26187)
- `ErrFmaApprox_2_aux` (Theorem, upstream line 26217)
- `ErrFmaApprox_2` (Theorem, upstream line 26310)
- `ErrFmaApprox` (Theorem, upstream line 26490)

### Counterpart/Renaming Audit Progress

This subsection checks whether an exact-name gap is genuinely absent, already
present under a different Lean name, or only partially represented by a weaker
or split local theorem. Do not remove an item from the broad missing-name list
until it is either restored under the exact upstream name or explicitly judged
to be a faithful renamed counterpart with statement-level evidence.

Checked batch 1: core digit/exponent/rounding-instance names.

Confirmed faithful counterparts removed from the active semantic gap list:

- `FLT_exp_monotone`: represented by `FLT_exp_mono` in
  `FloatSpec/src/Core/FLT.lean`.
- `FLX_exp_monotone`: represented by `FLX_exp_mono` in
  `FloatSpec/src/Core/FLX.lean`.
- `valid_rnd_DN`: represented by `valid_rnd_floor` in
  `FloatSpec/src/Core/Generic_fmt.lean`.
- `valid_rnd_UP`: represented by `valid_rnd_ceil` in
  `FloatSpec/src/Core/Generic_fmt.lean`.
- `valid_rnd_ZR`: represented by `valid_rnd_Ztrunc` in
  `FloatSpec/src/Core/Generic_fmt.lean`.
- `monotone_exp_not_FTZ`: represented by `monotone_exp_not_FTZ_theorem` in
  `FloatSpec/src/Core/Ulp.lean`.
- `valid_rnd_odd`: represented by the anonymous
  `FloatSpec.Core.Generic_fmt.Valid_rnd Zodd` instance in
  `FloatSpec/src/Prop/Round_odd.lean`.

- `Core/Digits.v`
  - `Zdigit_ext`: not faithfully present under the exact statement. Lean has
    `Zdigit_ext_nonneg` in `FloatSpec/src/Core/Digits.lean`, but that theorem
    assumes both integers are nonnegative. Upstream `Zdigit_ext` is over all
    integers. Status: renamed/split but weaker; exact theorem still required.
  - `Zdigit_plus`: not faithfully present. Lean has `Zdigit_plus_nonneg`, but
    it gives a carry-form statement for nonnegative operands, while upstream
    `Zdigit_plus` proves exact digit additivity under the disjoint-digit
    hypothesis. Status: renamed/split but different payload; exact theorem
    still required.
  - `Zdigit_scale`: partially present as `Zdigit_scale_point`, but the Lean
    theorem has an extra precondition `(0 <= k || 0 <= n)` and is wrapped in a
    Hoare-style spec. Upstream only assumes `0 <= k'`. Status: renamed but
    weaker; exact theorem still required.
  - `Zslice_div_pow_scale`: partially present as
    `Zslice_div_pow_scale_nonnegKp`, but the local theorem has a different
    scaled/divided expression and extra nonnegativity/order assumptions.
    Status: renamed/split but not a faithful counterpart.
- `Core/FIX.v`
  - `FIX_exp_monotone`: no faithful same-payload counterpart found. Lean has
    `FIX_exp_valid`, proving `Valid_exp`, but no `Monotone_exp (FIX_exp emin)`
    instance/theorem with the upstream name. Status: absent, likely small.
  - `exists_NE_FIX`: no faithful counterpart found. Lean has the generic
    `Exists_NE` class in `Round_NE.lean`, but no FIX instance. Status: absent,
    likely small.
- `Core/FLT.v`
  - `FLT_exp_monotone`: faithfully represented under the renamed Lean instance
    `FLT_exp_mono`. Status: removed from active semantic gaps.
  - `exists_NE_FLT`: partially represented by private theorem
    `FLT_exp_exists_NE` in `Pff2FlocqAux.lean`, specialized to Pff bounds and
    strict precision. Upstream is a public instance for `FLT_exp` under
    `(Z.even beta = false \/ 1 < prec)`. Status: split/private/specialized;
    exact public instance still required.
- `Core/FLX.v`
  - `FLX_exp_monotone`: faithfully represented under the renamed Lean instance
    `FLX_exp_mono`. Status: removed from active semantic gaps.
  - `exists_NE_FLX`: no faithful public counterpart found. Lean has
    `Exists_NE` infrastructure, but no FLX instance matching the upstream
    `NE_prop` section hypothesis. Status: absent.
- `Core/Generic_fmt.v`
  - `valid_rnd_DN`, `valid_rnd_UP`, `valid_rnd_ZR`: present in substance under
    renamed instances `valid_rnd_floor`, `valid_rnd_ceil`, and
    `valid_rnd_Ztrunc`. Status: removed from active semantic gaps.
  - `valid_rnd_AW`: likely present in substance under `valid_rnd_opp`
    together with the away-from-zero rounding construction, but not yet
    statement-checked against upstream. Status: needs manual comparison.
  - `monotone_exp_not_FTZ`: present in substance as
    `monotone_exp_not_FTZ_theorem` in `FloatSpec/src/Core/Ulp.lean`, not in
    `Generic_fmt.lean`. Status: removed from active semantic gaps.
  - `valid_rnd_NA`, `valid_rnd_N0`: not faithfully present under exact names.
    Lean has generic `valid_rnd_N` and nearest predicates `Rnd_NA`/`Rnd_N0`,
    but no checked exact instances for the upstream `ZnearestA`/`Znearest0`
    modes. Status: likely small exact-name instance wrappers, but still
    unchecked.
- `Prop/Round_odd.v`
  - `valid_rnd_odd`: present in substance as an anonymous instance
    `FloatSpec.Core.Generic_fmt.Valid_rnd Zodd` in
    `FloatSpec/src/Prop/Round_odd.lean`. Status: removed from active semantic
    gaps.

Checked batch 2: `Core/Raux.v` auxiliary real/integer lemmas.

Confirmed faithful counterparts removed from the active semantic gap list:

- `Rabs_eq_Rabs`: represented by `Rabs_eq_Rabs_spec`.
- `Rabs_minus_le`: represented by `Rabs_minus_le_spec`.
- `Rabs_eq_R0`: represented by `Rabs_eq_R0_spec`, which proves the standard
  `|x| = 0 <-> x = 0` equivalence.
- `Rinv_lt`: represented by `Rinv_lt_spec`.
- `Rinv_le`: represented by `Rinv_le_spec`.
- `sqrt_neg`: represented by `sqrt_neg_spec`.
- `Rsqr_le_abs_0_alt`: represented by `Rsqr_le_abs_0_alt_spec`.
- `Rabs_le_inv`: represented by `Rabs_le_inv_spec`.
- `Rabs_ge`: represented by `Rabs_ge_spec`.
- `Rabs_ge_inv`: represented by `Rabs_ge_inv_spec`.
- `Rabs_lt_inv`: represented by `Rabs_lt_inv_spec`.
- `Rabs_gt`: represented by `Rabs_gt_inv_spec` after swapping the parameter
  order; it proves the Coq payload `y < -x \/ x < y -> x < |y|`.
- `IZR_le_lt`: represented by `IZR_le_lt_spec`.
- `le_lt_IZR`: represented by `le_lt_IZR_spec`.
- `Rcompare_Lt_inv`: represented by `Rcompare_Lt_inv_spec`.
- `Rcompare_half_l`: represented by `Rcompare_half_l_spec`.
- `Rcompare_half_r`: represented by `Rcompare_half_r_spec`.
- `Rcompare_sqr`: represented by `Rcompare_sqr_spec`.
- `Rmin_compare`: represented by `Rmin_compare_spec`.
- `eqb_false`: represented by `eqb_false_spec`, with the stronger premise
  `a != b`.
- `eqb_true`: represented by `eqb_true_spec`.
- `IZR_cond_Zopp`: represented by `IZR_cond_Zopp_spec`.
- `abs_cond_Ropp`: represented by `abs_cond_Ropp_spec`.
- `cond_Ropp_mult_l`: represented by `cond_Ropp_mult_l_spec`.
- `cond_Ropp_mult_r`: represented by `cond_Ropp_mult_r_spec`.
- `cond_Ropp_plus`: represented by `cond_Ropp_plus_spec`.

Still active after statement check:

- `Rabs_lt`: local `Rabs_lt_spec` only states a boolean equivalence for
  `|x| < y`; it does not by itself expose the Coq implication
  `-y < x < y -> |x| < y`.
- `Rabs_gt_inv`: no faithful counterpart found; local `Rabs_gt_inv_spec`
  actually covers the forward `Rabs_gt` direction after argument swap.
- `Rcompare_middle`: local `Rcompare_middle_spec` is not faithful; its carrier
  returns `(c, c)` where both components are already
  `Rcompare x ((d + u) / 2)`, so it does not prove the upstream comparison
  with `Rcompare (x - d) (u - x)`.
- `Rcompare_floor_ceil_middle`: local theorem compares floor/ceil codes
  directly, not the upstream midpoint expression
  `Rcompare (x - floor x) (1/2) =
   Rcompare (x - floor x) (ceil x - x)` under non-integrality.
- `Rcompare_ceil_floor_middle`: same issue as
  `Rcompare_floor_ceil_middle`, with the ceiling-side midpoint expression.
- `cond_Ropp_Rlt_bool`: local theorem compares two conditionally negated
  variables; upstream states `cond_Ropp (Rlt_bool m 0) m = |m|`.
- `Rlt_bool_cond_Ropp`: local theorem compares `x` with
  `cond_Ropp b y`; upstream states
  `0 < x -> Rlt_bool (cond_Ropp sx x) 0 = sx`.

Checked batch 3: `Core/Zaux.v` radix and boolean-comparison proof views.

Confirmed faithful counterparts removed from the active semantic gap list:

- `radix`: represented by the Lean `Radix` structure. The Lean field
  `prop : 2 <= val` is the proposition-level counterpart of upstream
  `radix_prop : Zle_bool 2 radix_val = true`.
- `Zeq_bool_prop`: represented by `Zeq_bool` plus `Zeq_bool_spec`, which
  exposes the equality/boolean relationship directly instead of the Coq
  inductive proof-view wrapper.
- `Zle_bool_prop`: represented by `Zle_bool` plus `Zle_bool_spec`, which
  exposes the less-or-equal/boolean relationship directly instead of the Coq
  inductive proof-view wrapper.
- `Zlt_bool_prop`: represented by `Zlt_bool` plus `Zlt_bool_spec`, which
  exposes the less-than/boolean relationship directly instead of the Coq
  inductive proof-view wrapper.
- `Zcompare_prop`: represented by `Zcompare` plus `Zcompare_spec`, whose
  postcondition states the three upstream comparison cases as equivalences.

Still active after statement check:

- `eqbool_dep`: this is a Coq proof-irrelevance helper used to prove
  `eqbool_irrelevance`. No explicit Lean declaration/counterpart was found.
  It may be a proof-engineering artifact rather than a semantic float theorem,
  but it stays active until the audit has a policy for excluding such names.
- `Zpos_div_eucl_aux1_correct`: Lean has
  `Zpos_div_eucl_aux1_correct_spec`, but the local carrier is direct
  `Int` division/modulo with statement `result = (a / b, a % b)`, while
  upstream proves equality between a recursive positive-integer helper and
  `Z.pos_div_eucl a (Zpos b)`. Status: not removed without a source-faithful
  wrapper or an explicit equivalence proof.
- `Zpos_div_eucl_aux_correct`: same issue as
  `Zpos_div_eucl_aux1_correct`; the local statement is useful but not the
  upstream positive-helper theorem.

Checked batch 4: `Core/Round_pred.v` rounding predicate lemmas.

Confirmed faithful counterparts removed from the active semantic gap list:

- `round_unique`: represented by `round_unique_spec`; the equality theorem is
  encoded as `round_unique_check = true` under the same monotonicity and
  point hypotheses.
- `Rnd_DN_pt_monotone`, `Rnd_UP_pt_monotone`, `Rnd_ZR_pt_monotone`,
  `Rnd_N_pt_monotone`, `Rnd_NG_pt_monotone`, `Rnd_NA_pt_monotone`, and
  `Rnd_N0_pt_monotone`: represented by the corresponding `_spec` theorems,
  which prove the same `round_pred_monotone` payload in Hoare/Bool form.
- `Rnd_DN_pt_unique`, `Rnd_DN_unique`, `Rnd_UP_pt_unique`,
  `Rnd_UP_unique`, `Rnd_N_pt_unique`, `Rnd_NG_pt_unique`,
  `Rnd_NG_unique`, `Rnd_NA_pt_unique`, `Rnd_NA_unique`,
  `Rnd_N0_pt_unique`, and `Rnd_N0_unique`: represented by the corresponding
  `_spec` theorems, which prove the same pointwise or functional equality
  payload under the upstream hypotheses.
- `Rnd_UP_pt_opp`, `Rnd_DN_pt_opp`, and `Rnd_DN_opp`: represented by
  corresponding `_spec` theorems; some hypotheses are Lean theorem parameters
  instead of Hoare preconditions, but the target negation/duality payload is
  the upstream one.
- `Rnd_DN_pt_refl`, `Rnd_DN_pt_idempotent`, `Rnd_UP_pt_refl`,
  `Rnd_UP_pt_idempotent`, `Rnd_N_pt_refl`, `Rnd_N_pt_idempotent`,
  `Rnd_N_pt_0`, `Rnd_NA_pt_refl`, `Rnd_NA_pt_idempotent`,
  `Rnd_N0_pt_refl`, and `Rnd_N0_pt_idempotent`: represented by the
  corresponding `_spec` theorems with the same representability/idempotence
  payloads.
- `Rnd_ZR_abs`, `Rnd_N_pt_ge_0`, `Rnd_N_pt_le_0`, `Rnd_N_pt_abs`,
  `Rnd_N_pt_DN_UP`, `Rnd_N_pt_DN`, `Rnd_N_pt_UP`, `Rnd_NA_NG_pt`,
  `Rnd_NA_pt_unique_prop`, `Rnd_NA_pt_N`, `Rnd_N0_NG_pt`,
  `Rnd_N0_pt_unique_prop`, and `Rnd_N0_pt_N`: represented by corresponding
  `_spec` theorems; these keep the upstream hypotheses and conclusion but use
  Hoare/Bool wrappers.
- `Rnd_NG_pt_unique_prop`: represented inline in `Rnd_NG_pt_unique_spec`,
  `Rnd_NG_pt_monotone_spec`, and `Rnd_NG_unique_spec` as the same
  tie-uniqueness proposition, rather than as a separate named definition.
- `round_pred_ge_0`, `round_pred_gt_0`, `round_pred_le_0`, and
  `round_pred_lt_0`: represented by corresponding `_spec` theorems with the
  same monotonicity, zero-point, point-membership, and sign hypotheses.
- `Rnd_DN_pt_equiv_format` and `Rnd_UP_pt_equiv_format`: represented by
  corresponding `_spec` theorems with the same interval equivalence and
  endpoint hypotheses.

Still active after statement check:

- `satisfies_any_eq`: local `satisfies_any_eq_spec` is over
  `Generic_fmt.satisfies_any`, which currently means only `∃ x, F x`.
  Upstream `Round_pred.satisfies_any` packages `F 0`, symmetry under
  negation, and DN totality. This is a real statement mismatch.
- `satisfies_any_imp_DN`: local `_spec` assumes
  `round_pred_total (Rnd_DN_pt F)` directly, instead of deriving
  `round_pred (Rnd_DN_pt F)` from upstream `satisfies_any F`.
- `satisfies_any_imp_UP`: local `_spec` assumes
  `round_pred_total (Rnd_UP_pt F)` directly, instead of deriving it via DN
  totality and symmetry from upstream `satisfies_any F`.
- `satisfies_any_imp_ZR`: local `_spec` assumes
  `round_pred_total (Rnd_ZR_pt F)` directly, instead of deriving it from
  upstream `satisfies_any F`.
- `NG_existence_prop`: no faithful counterpart found. The upstream proposition
  is `∀ x d u, ¬ F x -> Rnd_DN_pt F x d -> Rnd_UP_pt F x u ->
  P x u ∨ P x d`.
- `satisfies_any_imp_NG`: local `_spec` assumes NG totality plus
  tie-uniqueness; upstream assumes `satisfies_any F` plus
  `NG_existence_prop F P` and derives totality.
- `satisfies_any_imp_NA`: local `_spec` assumes `round_pred_total
  (Rnd_NA_pt F)` and `F 0`; upstream derives the full `round_pred` from
  `satisfies_any F`.
- `satisfies_any_imp_N0`: local `_spec` assumes `round_pred_total
  (Rnd_N0_pt F)` and `F 0`; upstream derives the full `round_pred` from
  `F 0` plus `satisfies_any F`.

Checked batch 5: `IEEE754/Binary.v` base binary model names.

Confirmed faithful counterparts removed from the active semantic gap list:

- `fexp_correct`: represented by the generic `FLT_exp_valid` instance for
  `FLT_exp prec emin`; upstream's local `fexp` is this FLT exponent function
  with `emin = 3 - emax - prec`.
- `is_finite_strict`: represented by `is_finite_strict_Bin`, the local
  strict-finiteness classifier for `Binary754`.
- `is_finite`: represented by `is_finite_B`, the local finiteness classifier
  for `Binary754`.
- `is_nan`: represented by `is_nan_B`, the local NaN classifier for
  `Binary754`.
- `Bone`: represented by `binary_one`; `Bone_correct`, `is_finite_Bone`, and
  `Bsign_Bone` expose the expected constant-one payloads.

Still active after statement check:

- `full_float`: a renamed `FullFloat` exists, but it uses `Nat` payloads where
  Coq uses `positive` for NaN payloads and finite mantissas. That admits extra
  zero-payload values, so this is not a faithful type counterpart yet.
- `nan_pl`: no faithful counterpart found. Lean has payload extractors such as
  `get_nan_pl`, but not the upstream bound check
  `Zlt_bool (Zpos (digits2_pos pl)) prec`.
- `binary_float`: a renamed `Binary754` exists, but its validity field is
  currently `is_finite_FF val = true -> True`; it does not enforce upstream
  `bounded m e = true` for finite values or `nan_pl pl = true` for NaNs.
- `Bcompare`: `Bcompare_correct` exists over `Bcompare_check`, but no faithful
  `Bcompare` definition was found. The local check always returns `some`
  real comparison under finite hypotheses and does not expose upstream's
  unordered `none` behavior as the operation.
- `Bmult` and `Bplus`: local `binary_mul`/`binary_add` helpers exist, but they
  do not match upstream signatures with NaN payload handlers and rounding
  mode arguments. Their local `binary_*_correct` declarations are explicit
  `Unit` port-gap markers.
- `Bmult_correct` and `Bplus_correct`: no faithful counterparts found; local
  `binary_mul_correct` and `binary_add_correct` are `Unit` port-gap markers,
  not the upstream IEEE postconditions.
- `Bminus`, `Bfma`, `Bdiv`, and `Bsqrt`: local helpers
  `binary_sub`, `binary_fma`, `binary_div`, and `binary_sqrt` exist, but they
  drop the upstream NaN payload handler parameters and are not faithful
  operation definitions.
- `Bnearbyint`: local `binary_nearbyint` exists, and
  `Bnearbyint_correct` has substantial local payload, but the operation
  still drops the upstream NaN payload handler parameter.
- `Btrunc`: local `binary_trunc` exists, but the exact same-name
  `Btrunc_correct` theorem is currently tautological
  (`result = Btrunc_correct_check ...`) instead of upstream's
  `IZR (Btrunc x) = round radix2 (FIX_exp 0) Ztrunc (B2R x)`.
- `Bmax_float`: no faithful counterpart found.
- `Bnormfr_mantissa`: no faithful counterpart found.
- `Bulp`: explicitly marked in the Lean source as reserved and not yet added.
- `Bulp_correct`: no faithful counterpart found because `Bulp` itself is
  absent.

Checked batch 6: `IEEE754/BinarySingleNaN.v` bridge and rounding-mode names.

Confirmed faithful counterparts removed from the active semantic gap list:

- `mode`: represented by the Lean `RoundingMode` inductive in
  `FloatSpec/src/IEEE754/Binary.lean`.
- `round_mode`: represented by `rnd_of_mode`, which maps each
  `RoundingMode` constructor to the corresponding integer rounding function.
- `valid_rnd_round_mode`: represented by the `valid_rnd_of_mode` instance.

Still active after statement check:

- `SF2B'` and `SF2B'_B2SF`: Lean has `SF2B`/`SF2B_B2SF`, but upstream
  `SF2B'` checks `bounded m e` and maps invalid finite standard floats to
  NaN. The local `SF2B` maps finite values directly into the weakened `B754`
  representation, so this is not a faithful counterpart.
- `Bsign_SF2B`, `is_finite_SF2B`, and `is_nan_SF2B`: no faithful theorem
  counterparts found for the upstream `SF2B` validity-argument form.
- `is_nan_Bopp`, `is_finite_strict_Bopp`, `is_nan_Babs`, and
  `is_finite_strict_Babs`: Lean has `Bopp_bsn`, but the corresponding BSN
  classifier theorems are absent; no `Babs` counterpart was found in the BSN
  file.
- The shift/truncation helper block from `shr_m_shr_record_of_loc` through
  `shr_truncate`: no faithful counterparts found. Some cross-reference hits
  point to unrelated helper names in other files, not the upstream statements.
- `choice_mode`, `le_choice_mode_le`, and `round_mode_choice_mode`: no
  faithful counterpart found for the upstream tie/shift choice function and
  its bridge to `round_mode`.
- `overflow_to_inf`, `is_nan_binary_overflow`, and
  `binary_overflow_correct`: local `bsn_binary_overflow` always returns an
  infinity, while upstream sometimes returns the largest finite value depending
  on mode and sign. The local helper is not faithful.
- `binary_fit_aux`, `binary_fit_aux_correct`, `Bmult_correct_aux`,
  `shl_align_correct'`, `shl_align_correct`, `snd_shl_align`,
  `is_nan_binary_round`, `is_nan_binary_normalize`, `Fplus_naive`,
  `Fplus_naive_correct`, `sign_plus_overflow`,
  `SFnearbyint_binary_aux`, `SFnearbyint_binary`, and
  `Bnearbyint_correct_aux`: no faithful counterparts found. The local
  `binary_round_aux`/`binary_round` helpers are explicitly documented as audit
  helpers, not ports of Flocq's algorithms.
- `is_finite_strict_Bone`, `is_nan_Bone`, `Bmax_float_proof`,
  `Bnormfr_mantissa_correct`, `Ffrexp_core_binary`, `Bulp_correct_aux`,
  `is_nan_Bulp`, `is_finite_strict_Bulp`, `Bulp'`, `Bulp'_correct`,
  `is_nan_Bsucc`, `is_nan_Bpred`, `Bpred_pos'`,
  `Bpred_pos'_correct`, `Bsucc'`, and `Bsucc'_correct`: no faithful
  counterparts found in the BSN file. Some related Binary-level successor,
  predecessor, and constant-one theorems exist, but they do not provide these
  upstream BSN declarations.

Checked batch 7: `IEEE754/Bits.v` bit-level API names.

No entries were removed from the active semantic gap list in this batch.

Still active after statement check:

- `bits_of_binary_float`, `split_bits_of_binary_float`, and
  `binary_float_of_bits`: Lean has `binary_to_bits`, `split_bits`, and
  `bits_to_binary`/`binary_float_of_bits_aux`, but these are built over the
  local weakened `Binary754` model and different width helpers. They are not
  confirmed faithful counterparts of the upstream API definitions.
- `binary32` and `binary64`: Lean has `Binary32` and `Binary64`, but they are
  defined as `Binary754 24 127` and `Binary754 53 1023`, while upstream uses
  `binary_float 24 128` and `binary_float 53 1024`. This may be a convention
  shift, but it is not removed without an explicit equivalence proof.
- The `default_nan_pl*`, `unop_nan_pl*`, `binop_nan_pl*`, and
  `ternop_nan_pl*` payload helpers: no faithful counterparts found.
- The `b32_*` and `b64_*` operation aliases, including bit conversion aliases:
  no faithful counterparts found under the upstream names. Some generic local
  helpers such as `erase`, `succ`, `pred`, `compare`, `binary_to_bits`, and
  `bits_to_binary` exist, but the specialized IEEE32/IEEE64 API layer is not
  present.

Checked batch 8: `IEEE754/PrimFloat.v` primitive-float bridge names.

No entries were removed from the active semantic gap list in this batch.

Still active after statement check:

- `Prim2B` and `B2Prim`: Lean has `prim_to_binary` and `binary_to_prim`, but
  the file explicitly uses an experimental opaque real-wrapper `PrimFloat` and
  states that it must not be counted as a faithful IEEE/PrimFloat equivalence
  result. These are not faithful counterparts of Coq's primitive `float`
  bridge.
- `round_nearest_even_equiv`, `binary_round_aux_equiv`,
  `binary_round_equiv`, and `binary_normalize_equiv`: no faithful
  counterparts found. Local `binary_round_aux`/`binary_round`/normalization
  helpers are documented as audit helpers rather than ports of the Flocq
  algorithms.
- `mul_equiv` and `add_equiv`: no faithful counterparts found. Local
  `prim_mul_correct` and `prim_add_correct` are reflexive tautologies over the
  local model, not the upstream equivalences between primitive operations and
  `Bmult`/`Bplus`.
- `normfr_mantissa_equiv`: no faithful counterpart found.

Checked batch 9: `Pff/Pff.v` initial counterpart triage.

No entries were removed from the active semantic gap list in this batch.

Initial status:

- The 104 listed Pff names are still active. The cross-reference pass found
  many related local helpers, but the visible candidates are mostly
  `*_from_*`, `*_aux`, `*_check`, or prerequisite payload names rather than
  faithful renamed counterparts of the upstream declarations.
- Examples that remain active despite nearby helpers include
  `errorBoundedMultClosest` versus
  `errorBoundedMultClosest_from_nonneg`/
  `errorBoundedMultClosest_from_minmax`, `UlpFlessuGe` versus
  `UlpFlessuGe_*` helper theorems, `Axpy_opt` versus
  `Axpy_opt_from_*`, and `Twice_EvenClosest_Round` versus
  `Twice_EvenClosest_Round_from_*`.
- Entries with no credible local candidate in the first triage, such as
  `plusExact2Aux`, `plusExact2`, many `Bounded*`/`Veltkamp*` lemmas, and the
  final `ErrFmaApprox*` family, remain active.
- This Pff pass is not yet a completed statement-by-statement audit of all 104
  entries. It only confirms that no obvious renamed/split counterpart was safe
  to remove without deeper theorem-payload comparison.

Checked batch 10: `Pff/Pff.v` plausible renamed-counterpart statement pass.

No entries were removed from the active semantic gap list in this batch.

Statement-level checks performed:

- `errorBoundedMultClosest`: Lean has
  `errorBoundedMultClosest_from_nonneg`,
  `errorBoundedMultClosest_nonneg_from_minmax`,
  `errorBoundedMultClosest_from_minmax`, and
  `errorBoundedMultClosest_aux`, but these either require the missing
  min/max arithmetic branches as premises or prove the stricter auxiliary
  exponent form. Upstream `errorBoundedMultClosest` proves the final
  existential over `r` and `s` with `Fexp s = Fexp r - precision`; no
  faithful renamed counterpart was found.
- `plusExact2Aux`, `plusExact2`, and `plusExactExp`: no faithful local
  counterpart was found. The local `AddExpGeUnderf` comment explicitly treats
  the key content of `plusExactExp` as an extra hypothesis, so this family is
  still real missing infrastructure rather than a hidden split port.
- `UlpFlessuGe` and `UlpFlessuGe2`: Lean has `UlpFlessuGe_aux`,
  `UlpFlessuGe_final_scale`,
  `UlpFlessuGe_from_abs_sub_fulp`,
  `UlpFlessuGe_from_general_fulp_bound`, and
  `UlpFlessuGe2_from_general_bound`. These are prerequisite/reduction
  theorems; the comments and statements leave the large coefficient
  arithmetic bound as a premise. Upstream `UlpFlessuGe` and
  `UlpFlessuGe2` prove those displayed coefficient inequalities, so both
  remain active.
- `Axpy_opt`: Lean has `Axpy_opt_from_strict_bound` and
  `Axpy_opt_from_general_bound`, but both keep additional premises for the
  strict coefficient estimate and predecessor side cases. Upstream
  `Axpy_opt` proves `MinOrMax` directly from the two displayed user
  hypotheses, so the local helpers are not faithful replacements.
- `Dekker1` and `Dekker2`: Lean has `Dekker1_FTS` and `Dekker2_FTS`, but
  these are Fast2Sum/Dekker support theorems over abstract `Iplus`/`Iminus`.
  They do not match the upstream Pff `Dekker1`/`Dekker2` section payloads,
  which prove the concrete long product decomposition equation
  `x * y = r - t4` under the section's rounded intermediate hypotheses.
- `Twice_EvenClosest_Round`: Lean has
  `Twice_EvenClosest_Round_from_closest` and
  `Twice_EvenClosest_Round_from_even_or_high`, but these require the scaled
  closestness or even/high competitor boundary premise. Upstream proves that
  scaled closestness theorem from `EvenClosest r x`, normality, and the
  exponent lower bound, so the public theorem is still absent.
- Remaining active Pff names either had no credible declaration-name
  counterpart in `FloatSpec/src/Pff/Pff.lean`, or only broad helper-family
  hits such as `Closest`, `EvenClosest`, `Underf_Err`, `LSB`, and
  `LeExpRound` that do not encode the upstream theorem statement. They remain
  active until each is either restored exactly or matched to a theorem with
  the same payload.

Updated status: the plausible Pff false-positive candidates checked so far
are confirmed as real semantic gaps, not renamed/split complete ports. The
Pff active count therefore remains 104.

Checked batch 11: active Core bucket revalidation after direct `rg` scan.

No entries were removed from the active semantic gap list in this batch.

The scan intentionally revisited names with nearby `_spec` or helper names:

- `Core/Raux.v`: the active names still have only weaker or tautological local
  carriers. In particular, `Rabs_lt_spec` is a boolean test for `|x| < y`,
  `Rabs_gt_inv_spec` proves the already-removed forward `Rabs_gt` direction
  after argument swap, and `Rcompare_middle_spec` returns `(c, c)` instead of
  comparing `Rcompare (x - d) (u - x)` with
  `Rcompare x ((d + u) / 2)`. The floor/ceil midpoint and conditional-negation
  entries likewise remain statement mismatches, not hidden ports.
- `Core/Round_pred.v`: the active `satisfies_any_*` `_spec` declarations are
  over the local existential-only `Generic_fmt.satisfies_any`, or assume the
  target rounding totality directly. They do not prove the upstream
  `Round_pred.satisfies_any` consequences, where `satisfies_any` packages
  `F 0`, symmetry, and DN totality.
- `Core/Generic_fmt.v`: `Zaway`, `Zaway_le`, `Zaway_IZR`, and the nearest
  choice helpers exist, but no `Valid_rnd Zaway`/AW instance or public
  `valid_rnd_NA`/`valid_rnd_N0` instance was found under a faithful renamed
  declaration. The active instance names remain real import debt.
- `Core/FIX.v`, `Core/FLT.v`, and `Core/FLX.v`: `FIX_exp_valid`,
  `FLT_exp_mono`, `FLX_exp_mono`, and private/specialized Pff bridges exist,
  but the active public `Monotone_exp`/`Exists_NE` instances listed above are
  still not present with the upstream payload.
- `Core/Digits.v` and `Core/Zaux.v`: the visible renamed helpers remain the
  already-recorded weaker forms (`Zdigit_*_nonneg`,
  `Zdigit_scale_point`, `Zslice_div_pow_scale_nonnegKp`, and direct `Int`
  division/modulo correctness specs), not exact statement counterparts.

Checked batch 12: IEEE active sibling-name revalidation after direct `rg`
scan.

No entries were removed from the active semantic gap list in this batch.

The scan revisited active IEEE names with nearby same-stem declarations:

- `IEEE754/Binary.v`: `FullFloat` and `Binary754` are real local type
  counterparts, but still do not encode upstream's positive payload and
  finite/NaN validity obligations. `Bcompare_check`, `binary_add`,
  `binary_mul`, `binary_sub`, `binary_fma`, `binary_div`, `binary_sqrt`,
  `binary_nearbyint`, and `binary_trunc` are nearby operation families, but
  they are not faithful definitions of the upstream `Bcompare`, `Bplus`,
  `Bmult`, `Bminus`, `Bfma`, `Bdiv`, `Bsqrt`, `Bnearbyint`, and `Btrunc`
  APIs. The local arithmetic operations drop upstream NaN payload handler
  parameters, some local `binary_*_correct` declarations are explicit `Unit`
  port-gap markers, and `Btrunc_correct` is still a tautological
  `result = Btrunc_correct_check ...` statement. `Bulp` remains explicitly
  reserved in the Lean source, so `Bulp_correct` cannot be considered hidden.
- `IEEE754/BinarySingleNaN.v`: `SF2B` and `SF2B_B2SF` exist, but they do not
  implement the upstream `SF2B'` validation behavior that maps invalid finite
  standard floats to NaN. The Binary-level `Bopp`/`Babs` classifier facts do
  not supply the active BSN-specific `is_nan_Bopp`,
  `is_finite_strict_Bopp`, `is_nan_Babs`, or
  `is_finite_strict_Babs` declarations. The local rounding/normalization
  helpers are documented as audit helpers rather than Flocq algorithm ports,
  and no faithful hidden counterparts were found for the active overflow,
  fit, shift/truncate, successor/predecessor, `Bulp'`, or
  `SFnearbyint_binary` families.
- `IEEE754/Bits.v`: generic `binary_to_bits`, `split_bits`,
  `bits_to_binary`, and `binary_float_of_bits_aux` exist, but the active
  upstream names are the specialized `bits_of_binary_float`,
  `split_bits_of_binary_float`, `binary_float_of_bits`, `binary32`,
  `binary64`, and `b32_*`/`b64_*` API layer. Local `Binary32` and `Binary64`
  use `Binary754 24 127` and `Binary754 53 1023`, while upstream uses
  `binary_float 24 128` and `binary_float 53 1024`; without an explicit
  equivalence proof this remains a gap, not a safe renaming.
- `IEEE754/PrimFloat.v`: the file is in
  `ExperimentalPrimFloatBridge` and explicitly uses an opaque real-wrapper
  model that must not be counted as a faithful primitive-float bridge.
  Existing `compare_equiv`, `opp_equiv`, `div_equiv`, and related local
  declarations do not cover the active upstream names
  `round_nearest_even_equiv`, `binary_round_aux_equiv`, `mul_equiv`,
  `binary_round_equiv`, `binary_normalize_equiv`, `add_equiv`, or
  `normfr_mantissa_equiv`. The local `prim_add_correct` and
  `prim_mul_correct` statements are reflexive identities over the local
  model, not the upstream equivalences to `Bplus` and `Bmult`.

Checked batch 13: `Pff/Pff.v` first active closestness/Veltkamp block.

No entries were removed from the active semantic gap list in this batch.

Statement-level checks performed for the first 35 active Pff entries:

- `errorBoundedMultClosest`, `plusExact2Aux`, `plusExact2`,
  `plusExactExp`, `UlpFlessuGe`, `UlpFlessuGe2`, and `Axpy_opt` were
  rechecked against the local helper families already noted in batch 10.
  The same conclusion holds: local declarations are prerequisite/reduction
  forms such as `*_from_*`, `*_aux`, or `*_check`; they do not prove the
  public upstream conclusions directly from the upstream hypotheses.
- `ClosestSuccPred`, `ImplyClosest`, `ImplyClosestStrict`,
  `ImplyClosestStrict2`, `ClosestImplyEven`, `ClosestImplyEven_int`,
  `hxExact`, `eqLeep`, `epLe`, `eqLe`, `eqGe`, and `eqEqual` have no exact
  Lean declaration under `FloatSpec/src/Pff`. Broad hits on the predicates
  `Closest` and `EvenClosest` are definitions, not theorem counterparts.
  These names are section-local proof lemmas in upstream Pff, but they remain
  active because they are parsed public Coq declarations and no faithful
  split payload has been identified.
- `Veltkamp_aux_aux`, `Veltkamp_aux`, `VeltkampEven1`,
  `VeltkampEven2`, `Veltkamp_pos`, `VeltkampN_aux`, `VeltkampN`,
  `VeltkampEven_pos`, `VeltkampEvenN_aux`, `VeltkampEvenN`, and
  `VeltkampS` are not covered by the public Lean `Veltkamp` wrapper in
  `FloatSpec/src/Pff/Pff2Flocq.lean`. The wrapper assumes a reduced
  nearest-even witness as input; the active upstream lemmas construct the
  Veltkamp error bound and reduced witness from rounded intermediate
  products/sums. They are therefore missing lower Pff payloads, not hidden
  under the public wrapper.
- `bimplybplusNorm`, `Closestbbplus`, `EvenClosestbplusb`,
  `ClosestClosest`, and `EvenClosestbbplus` have no faithful counterpart.
  Lean has `Closestbplusb`, but that is the reverse restriction direction
  from `plusExp b` closestness plus a bound proof back to `b` closestness.
  Upstream `Closestbbplus` proves the extension direction from `b` to
  `plusExp b`; upstream `EvenClosestbplusb` and `EvenClosestbbplus` add
  nearest-even side conditions in the two directions. The local theorem is
  not a replacement for either missing even-closest theorem or for
  `Closestbbplus`.

Updated status: active Pff entries 1-35 are confirmed real semantic gaps or
unported section lemmas, not renamed/split complete ports. The Pff active
count remains 104.

Checked batch 14: `Pff/Pff.v` Veltkamp-tail, underflow, and Dekker lead-in
block.

No entries were removed from the active semantic gap list in this batch.

Statement-level checks performed for active Pff entries 36-70:

- `VeltkampEvenS`, `VeltkampEven`, `Veltkamp_tail_aux`,
  `Veltkamp_tail2`, and `VeltkampU` are not covered by the public Lean
  `Veltkamp` or `Veltkamp_tail` wrappers in `Pff2Flocq.lean`. The wrappers
  expose high-level consequences from reduced witness or tail payload
  hypotheses; the upstream active lemmas construct those witnesses and tail
  decompositions from the rounded intermediate `p`, `q`, `hx`, and `tx`
  hypotheses. They remain lower Pff payload gaps.
- `BoundedL`, `Closestbbext`, `Underf_Err1`, `Underf_Err2_aux`,
  `Underf_Err2`, `Underf_Err3`, and `Underf_Err3_bis` have no exact Lean
  declaration under `FloatSpec/src/Pff`. Local hits on `Bound`, `Closest`,
  `Underf_Err`, and `underf_mult_aux*` are data definitions or separate
  public underflow-multiplication helpers, not the upstream bounded-lifting
  and underflow-error transfer theorems.
- `eLe`, `rExp`, `Boundedt1`, `Boundedt2`, `Boundedt3`,
  `Boundedt4`, `Boundedt4_aux`, `Boundedx1y1_aux`, `Boundedx1y1`,
  `Boundedx1y2_aux`, `Boundedx1y2`, `Boundedx2y1_aux`,
  `Boundedx2y1`, and `Boundedx2y2` are section-local product-splitting
  bounds in upstream Pff. Local broad hits on `Bound`, `ZleLe`,
  `ClosestRoundeLeNormal`, or rounded-error helpers do not encode these
  concrete existential boundedness statements for the Dekker construction.
- `Dekker_aux`, `DekkerN`, `DekkerS1`, `DekkerS2`, `Dekker1`,
  `Dekker2_aux`, and `Dekker2` are not supplied by the public Lean
  `Dekker` wrapper or the local `Dekker1_FTS`/`Dekker2_FTS` helper
  family. The wrapper assumes summarized payloads, while the upstream names
  prove the concrete product decomposition or error bound from the section's
  rounded split/multiply hypotheses. The `*_FTS` helpers are Fast2Sum-style
  support lemmas over abstract operations and do not match the Pff Dekker
  section statements.
- `Veltkampb'` and `NormalbPrim` have no faithful local counterpart found.
  The former is a bound-parameter side theorem inside the Veltkamp/Dekker
  development, and the latter constructs a normal representative in the
  enlarged bound. Neither is implied by the public Veltkamp/Dekker wrappers
  without the missing lower proof payloads.

Updated status: active Pff entries 36-70 are confirmed real semantic gaps or
unported section lemmas, not renamed/split complete ports. The Pff active
count remains 104.

Checked batch 15: `Pff/Pff.v` final active rounded-error/FMA approximation
block.

No entries were removed from the active semantic gap list in this batch.

Statement-level checks performed for active Pff entries 71-104:

- `Twice_EvenClosest_Round` was rechecked against
  `Twice_EvenClosest_Round_from_closest` and
  `Twice_EvenClosest_Round_from_even_or_high`. As in batch 10, the local
  theorems assume the scaled closestness or even/high boundary payload that
  upstream proves from normality, exponent lower bound, and
  `EvenClosest`; they are not the public theorem.
- `errorBoundedMultClosest_Can`, `AddExpGe1Underf`,
  `AddExpGe1Underf2`, and `cases` have no faithful local counterpart.
  Broad hits on `errorBoundedMult`, `Closest`, or
  `ExactMinusIntervalAux_pred_constructive_cases` do not encode these
  section-specific underflow/case-split conclusions.
- `xLe2y_aux1`, `xLe2y_aux2`, `yLe2x_aux`, `xLe2y`, `yLe2x`,
  `Subexact`, `LSB_Pred`, `Midpoint_aux_aux`, `Midpoint_aux`,
  `gatCorrect`, `Expr1`, `Expbe1`, `be2MuchSmaller`, and `gaCorrect`
  have no exact Lean declaration under `FloatSpec/src/Pff`. Local hits on
  `LSB` or FMA helper theorems are definitions or narrower branch helpers,
  not the upstream subtraction/midpoint/least-significant-bit payloads.
- `tBounded_aux`, `tBounded`, `ErrFmaApprox_1_aux`,
  `ErrFmaApprox_1`, `ErrFmaApprox_2_aux`, `ErrFmaApprox_2`, and
  `ErrFmaApprox` are not hidden under the current local FMA helper family.
  The visible local helpers such as
  `FmaErr_gaCorrect_of_be1_eq_r1`,
  `FmaErr_gaCorrect_of_al2_zero`, and several `Fma_FTS_*_leexp_witness`
  theorems cover isolated branches or prerequisite exponent witnesses, not
  the final upstream FMA approximation bounds.
- `LeExp1`, `LeExp2`, `LeExp3`, `LeExp`, `vLe_aux`, `vLe`, `tLe`,
  and `wLe` remain active. Local hits such as `LeExpRound`,
  `LeExpRound2`, `RoundedModeMultLess`, `FboundedShiftLess`,
  `maxDivLess`, and `digitLess` are generic or unrelated support lemmas;
  they do not prove the concrete exponent and absolute-value bounds in this
  FMA section.

Updated status: all 104 active Pff entries have now been counterpart-checked
at least once. The checked local hits are helper, prerequisite, reverse
direction, or wrapper declarations rather than faithful renamed/split ports,
so the Pff active count remains 104.

Checked batch 16: explicitly named IEEE entries that were previously covered
only by grouped wording.

No entries were removed from the active semantic gap list in this batch.

Coverage checks performed:

- `loc_of_shr_record_of_loc`, `inbetween_shr_1`, `shr_nat`,
  `le_shr1_le`, `inbetween_shr`, `le_shr_le`, and `shr_limit` were
  searched directly in `FloatSpec/src/IEEE754`. The only hits are in
  `IEEE754_Theorems_Comparison_Manual.md`; no Lean theorem counterpart was
  found. They remain missing BinarySingleNaN shift/truncation lemmas.
- `default_nan_pl32`, `unop_nan_pl32`, `binop_nan_pl32`,
  `ternop_nan_pl32`, `b32_erase`, `b32_opp`, `b32_abs`, `b32_pred`,
  `b32_succ`, `b32_sqrt`, `b32_plus`, `b32_minus`, `b32_mult`,
  `b32_div`, `b32_fma`, `b32_compare`, `b32_of_bits`, and
  `bits_of_b32` were searched directly in `FloatSpec/src/IEEE754`. No Lean
  declaration counterpart was found. The generic local helpers
  `erase`, `succ`, `pred`, `compare`, `binary_to_bits`, and
  `bits_to_binary` are not the upstream binary32 API layer because they do
  not instantiate the upstream `binary_float 24 128` type, NaN-payload
  handlers, operation aliases, or bit-conversion aliases.
- `default_nan_pl64`, `unop_nan_pl64`, `binop_nan_pl64`,
  `ternop_nan_pl64`, `b64_erase`, `b64_opp`, `b64_abs`, `b64_pred`,
  `b64_succ`, `b64_sqrt`, `b64_plus`, `b64_minus`, `b64_mult`,
  `b64_div`, `b64_fma`, `b64_compare`, `b64_of_bits`, and
  `bits_of_b64` were searched directly in `FloatSpec/src/IEEE754`. No Lean
  declaration counterpart was found. The same generic-helper caveat applies:
  the upstream binary64 layer is specialized to `binary_float 53 1024` with
  concrete NaN payload propagation and operation aliases, while the local
  file only exposes generic weakened-model helpers and `Binary64 :=
  Binary754 53 1023`.

Updated status: every active name is now explicitly mentioned in the
counterpart/renaming audit notes at least once. This does not mean all
entries are proved missing forever; it means the current workspace search did
not find a faithful exact, renamed, formatted, or split counterpart for any
remaining active entry.

## Branch Diff Audit

Audit basis:

- Current branch: `floatspec-pipeline-gpt55`
- Compared against current `origin/main` after the PR #3 rebase:
  `bb9d513511a5ae4e945eebe0b48ba58afbc831f5`
- Current checked head for this audit:
  `97adda589bdb829819b958dcbf68a0b0eb529ecf`
- Current `origin/floatspec-pipeline-gpt55`:
  `97adda589bdb829819b958dcbf68a0b0eb529ecf`
- Flocq source checked locally under `/mnt2/users/kaile/hantao/flocq-upstream`.

I rechecked the branch-diff list against current `origin/main`, the current
branch, and the local Flocq clone. This section now keeps only declarations
that are exact Flocq declaration names and that have not been replaced by a real
theorem or lemma in the current branch. They should be restored as theorem
declarations with real proofs, not as `Unit`, `True`, `by trivial`, or other
payload-free definitions.

Workspace progress snapshot from 2026-07-03:

- `lake build` succeeds for the default FloatSpec target: 3345 jobs completed.
- `scripts/status_report.sh --write` reports 58 Lean files, with
  `sorry = 0`, `axiom = 0`, and `admit = 0`.
- Placeholder/weakening audit findings are now at 56 total:
  40 `placeholder_text`, 13 `true_definition`, 2 `true_relation`, and
  1 `identity_hint`.
- By module, those findings are currently Core 30, IEEE754 11, Calc 5, Pff 5,
  Other 5, Prop 0, and ErrorBound 0.
- Operational interpretation of the current 56 findings:
  - 43 of the 56 are text/meta findings, not theorem payloads:
    40 `placeholder_text` hits, 2 `true_relation` hits in commented-out
    `Ulp.lean` examples, and 1 `identity_hint` comment in `Calc/Round.lean`.
    These are useful audit breadcrumbs, but they are not 43 broken Flocq
    declarations.
  - 13 of the 56 are code-level `True` branches. Of those, 2 are the
    Hoare-style linter intentionally matching `⇓ _ => True`, 2 are recursive
    `Pff.lean` base cases where the base case proposition is genuinely
    vacuous, and the remaining 9 are simplified IEEE754 validity/special-value
    branches in `Binary.lean` and `BinarySingleNaN.lean`.
  - Therefore the current 56 should be read as a broad risk/hygiene queue, not
    as 56 confirmed wrong ports and not as 56 exact upstream Flocq names.
- These 56 findings are not the same thing as 56 active exact Flocq declaration
  gaps. They are the output of a broad hygiene scanner:
  - Some are scanner/meta false positives or documentation markers, such as the
    Hoare-style linter source matching `⇓ _ => True`, commented-out helper
    text in `Ulp.lean`, and section labels in `Calc/Round.lean`.
  - Some are intentional local infrastructure stubs, such as the currently
    empty `VersoExt.lean` module kept only so imports compile.
  - Some are real semantic debt: local predicates or helper theorem families
    that still use weak `True` branches, local placeholder statements, or
    underpowered support lemmas. These are repair targets only when they are
    exact upstream declarations or direct prerequisites for exact upstream
    declarations.
  - The active exact public Flocq-name scaffold list is now empty: 0 same-name
    `Unit` scaffolds in `Pff2Flocq.lean` and 0 absent active public
    declarations. Remaining work is now in lower prerequisite payloads rather
    than active public branch-diff wrappers. The broad placeholder scanner is
    deliberately noisier than
    the exact-name scan, so previous exact-name scans did not "miss" these 56;
    they filtered them out unless they corresponded to an upstream declaration
    name or an immediate blocker for one.
- 2026-07-03 source-level parsed exact-name scan, using the local Flocq source
  under `repo-level-vcg-pipeline-pr/output/sources/flocq`, shows the following
  remaining same-name gaps in the currently audited files:
  - 0 in `Core/Generic_fmt.v`, `Core/Round_NE.v`, `Core/Ulp.v`,
    `Calc/Round.v`, `Prop/Round_odd.v`, `Prop/Relative.v`, and
    `Prop/Div_sqrt_error.v`.
  - 3 file-local parsed gaps remain for `Pff/Pff2FlocqAux.v`:
    `RND_Closest`, `RND_Closest_canonic`, and `RND_Closest_correct`. These
    already exist globally in `FloatSpec/src/Pff/Pff.lean`; they are not absent
    from FloatSpec, only from this auxiliary file's parsed-name comparison.
    The same pass restored `FtoR_F2R`, and the 2026-07-03 follow-up restored
    the actionable reverse nearest-rounding bridge `pff_round_is_round_N` in
    `FloatSpec/src/Pff/Pff2FlocqAux.lean`.
  - 0 in `Prop/Double_rounding.v`. The 2026-07-03 follow-up restored
    `mag_mult_disj`, `mag_minus_disj`, `mag_minus_separated`,
    `round_round_sqrt_aux`, `round_round_sqrt_radix_ge_4_aux`,
    `round_round_div_aux0`, `round_round_div_aux1`, `round_round_div_aux2`,
    `round_round_div_aux`, and `round_round_div` as exact public names in
    `FloatSpec/src/Prop/Double_rounding.lean`, reusing the existing proved
    suffixed payloads where the file had already factored the arithmetic.
  - The same pass restored the two previous `Prop/Round_odd.v` gaps,
    `Rnd_odd` and `Zrnd_odd`, as public definitions in
    `FloatSpec/src/Prop/Round_odd.lean`.
  - A broader direct scan of all parsed public names in `Pff/Pff.v` now shows
    112 direct-file missing names after stripping Coq comments and excluding
    local Coq `Let` aliases. Those are not the same queue as the branch-diff
    active scaffold list, but they are real source-level coverage gaps for a
    complete Flocq port. The 2026-07-03 follow-up restored
    `Even_Odd_double`, `Even_double`, `Odd_double`, `Rinv_mult_distr`,
    `Rabs_Rinv`, `Rinv_pow`, `Rinv_involutive`, `Rlt_Rminus`, `IZR_neq`,
    `Zmax`, `float`, `FtoR`, `Fle`, `Fminus`, `ZdividesP`, and
    `PosNormMin`, `FnormalPpred`, `FcanonicPpred`, `FnormalNnormMin`, and
    `FcanonicNnormMin`, then restored `FSuccDiff1`, `FSuccDiff2`, and
    `FSuccDiff3`, followed by `ZltNormMinVnum` and `FSuccNormPos`, in
    `FloatSpec/src/Pff/Pff.lean`. The latest follow-ups restored
    `FSuccSubnormNotNearNormMin`, `FSuccSubnormNearNormMin`,
    `FSuccSubnormal`, `FSuccPosNotMax`, `FSuccNormNegNormMin`,
    `nNormMimLtvNum`, `FPredDiff1`, `FPredDiff2`, `FPredDiff3`,
    `FNPredFopFNSucc`, `FNPredCanonic`, `FNPredLt`, `ProjectMin`,
    `MonotoneMin`, `ProjectMax`, `MonotoneMax`, `FmaxRep`, and `MaxMin` in
    the same file, then restored `maxDivSimplAux`, `maxDivSimpl`,
    `maxDivUnique`, `maxDivSimplInvAux`, `maxDivSimplInv`,
    `maxDivUniqueInverse`, `maxDivUniqueDigit`,
    `maxDivUniqueInverseDigit`, `Ulp_Le_LSigB`, `MSB_le_abs`,
    `abs_lt_MSB`, `LSB_le_abs`, `MSB_monotoneAux`, and
    `MSB_monotone`, `isMinComp`, `isMaxComp`, `FUlp_Le_LSigB`,
    `FSuccNegCanonic`, `FSuccNormNegNotNormMin`, and
    `RoundedModeErrorExpStrict`, `RoundAbsMonotoner`, `RoundAbsMonotonel`,
    `errorBoundedMultPos`, `errorBoundedMultNeg`, `pPredMoreThanOne`, and
    `pPredMoreThanRadix`, `MSBroundLSB`, `FboundedMbound2Pos`,
    `FboundedMbound2`, `ErrorBoundedIplus`, `MDekkerAux1`, and
    `pow_add`, then `Odd` and `Option`, followed by `Underf_Err`, `zPos`,
    `x2y2Le`, `powerRZSumRle`, `SLe`, `SGe`, `s2Ge`, `s2Le`,
    `p''GivesBound`, `x2y1Le`, `x1y2Le`, `dExpPrim`, `dExpPrimEq`,
    `UnMoinsPos`, `abeLeab`, and `uhPos`, then
    `ClosestErrorBoundNormal_aux`, `ClosestErrorBoundNormal`, `plusExpMin`,
    `plusExpUpperBound`, and `plusExpBound`, then `AddExpGeUnderf2`,
    `pGeUnderf`, `qGeUnderf`, `ClosestRoundeGeNormal`,
    `ClosestRoundeLeNormal`, `TwoSumProp`, `plusExact1`, `plusExactR0`,
    `multExpUpperBound`, `errorBoundedMultExp_aux`,
    `errorBoundedMultExpPos`, `errorBoundedMultExp`, and
    `errorBoundedMultClosest_aux`.
  - A project-level parsed-name scan across all `FloatSpec/**/*.lean` currently
    shows 104 missing `Pff/Pff.v` names after stripping Coq comments. This is
    lower than the direct-file count because some exact names are supplied by
    imported FloatSpec modules or Lean/Mathlib.
    The first entries are now local FloatSpec gaps beginning with
    `errorBoundedMultClosest`, followed by `plusExact2Aux` in the addition
    block.
  - The current direct-file parser still lists `Fplus`, `Fopp`, `Fabs`, and
    `Fmult`, but those exact names already exist in FloatSpec through
    `FloatSpec/src/Compat.lean`; they are not absent project-level names.
    It also lists `Fbound`; that exact name already exists in
    `FloatSpec/src/Pff/Pff2FlocqAux.lean`, so adding a same-name alias in
    `Pff.lean` would conflict during the aggregate build.
    The project-level scan's former imported-library counterparts `pow_add`,
    `Odd`, and `Option` now have explicit namespaced compatibility declarations
    in `Pff.lean`.
- The 56 findings should therefore not be treated as 56 known-wrong Flocq
  ports. Some are wrong or underpowered relative to Flocq, some are harmless
  marker text, and some are local scaffolding. The repair policy is to fix a
  finding when it is either an exact upstream declaration with a weak local
  payload or a direct prerequisite for one of the active exact upstream
  declarations. Same-name weak theorems can escape a pure missing-name scan
  because the name exists; they require statement-level or dependency-level
  inspection to detect.
- Clarification after the 2026-06-26 `round_NE_pt` investigation: the current
  proof work is not trying to burn down all 56 broad scanner findings. The
  active item was a real Flocq-alignment problem exposed by dependency repair:
  `FloatSpec/src/Core/Round_NE.lean` had a same-name `round_NE_pt`, but its
  public wrapper proved only totality
  `∀ x, ∃ f, Rnd_NE_pt beta fexp x f`, while upstream Flocq's theorem is the
    concrete point statement that `roundR ... ZnearestE x` itself satisfies
    `Rnd_NE_pt`. That was worth fixing even though it was not one of the exact
  absent/`Unit` public names. Previous branch-diff scans did not discover it
  because they were name/payload-scaffold scans; the name existed and was a
  theorem, so only statement-level inspection or a downstream attempt to prove
  `pff_round_NE_is_round` exposed the mismatch. A subscription attempt at
  `.change_log/codex_attempt_20260626_083824` tried to replace the wrapper with
  the exact point theorem but produced a non-typechecking patch; the malformed
  generated fragment was removed. The current branch now restores the concrete
  point wrapper, and `lake env lean FloatSpec/src/Core/Round_NE.lean` accepts it.
- Why some of these were not surfaced by earlier exact-name scans:
  - The branch-diff scan asks whether an upstream Flocq declaration name is
    absent or still represented by a payload-free same-name scaffold. It is
    intentionally narrow and currently leaves 0 active public scaffolds.
  - The placeholder scan asks whether any local source text or definition shape
    looks suspicious. It is intentionally broad and currently reports 56
    findings, including comments, linter implementation code, local helper
    names, and simplified validity branches.
  - Dependency-level repairs, such as `round_N_pt`, `round_DN_pt`,
    `round_UP_pt`, and the partial `round_NE_pt` support lemmas, do not reduce
    the exact public scaffold list unless they close one of the public missing
    wrappers.
    They are fixed anyway when a pipeline attempt shows that an exact missing
    declaration cannot be restored faithfully until that prerequisite has real
    Flocq-shaped payload.
- The live Calc findings are still concentrated in
  `FloatSpec/src/Calc/Round.lean`: placeholder-section markers at lines 115,
  120, and 2979, a nearest-rounding placeholder-family marker at line 1206,
  and one identity-hint comment at line 1084. These are audit markers for the
  remaining Round compatibility section, not evidence that the already-restored
  truncation payloads listed below regressed.
- During the same pass, `FloatSpec/src/Core/Generic_fmt.lean` restored
  `round_DN_pt` and `round_UP_pt` from existential placeholder-style statements
  to the concrete Flocq-style point theorems for `roundR ... rnd_floor` and
  `roundR ... rnd_ceil`; `lake build` accepted the strengthened declarations
  through downstream `Round_NE`, `Calc`, `IEEE754`, and `Pff` modules.
- `FloatSpec/src/Core/Generic_fmt.lean` also restored `round_DN_or_UP` from a
  DN-witness existence theorem to the upstream-style concrete disjunction
  `roundR ... rnd = roundR ... rnd_floor ∨ roundR ... rnd = roundR ... rnd_ceil`
  for any `[Valid_rnd rnd]`, using the already ported `Zrnd_DN_or_UP`.
- `FloatSpec/src/Core/Generic_fmt.lean` restored `round_DN_opp` from a
  relation-shaped `round_to_generic` placeholder to the concrete Flocq-style
  theorem `roundR ... rnd_floor (-x) = - roundR ... rnd_ceil x`, using the
  earlier `roundR_opp` negation lemma plus `Zrnd_opp rnd_floor = rnd_ceil`.
- `FloatSpec/src/Core/Generic_fmt.lean` restored `round_DN_small_pos` from a
  Hoare-triple wrapper around `round_to_generic` to the direct Flocq-style
  equality `roundR ... rnd_floor x = 0` under the small-positive interval and
  exponent assumptions, using `mantissa_DN_small_pos`.
- `FloatSpec/src/Core/Generic_fmt.lean` restored `round_DN_UP_lt` from a
  generic outside-interval helper to the upstream-style strict bracketing
  theorem: if `x` is not in the generic format, then
  `roundR ... rnd_floor x < x < roundR ... rnd_ceil x`.
- `FloatSpec/src/Core/Generic_fmt.lean` restored `round_N_pt` from an
  existential nearest-point placeholder to the concrete Flocq-style theorem:
  `roundR beta fexp (Znearest choice) x` itself satisfies
  `Rnd_N_pt (fun y => generic_format beta fexp y) x ...`. This does not reduce
  the 19 active exact-name list because `round_N_pt` was not one of those
  public missing Pff/double-rounding wrappers; it removes a nearest-rounding
  prerequisite needed before `Round_NE.round_NE_pt` and the Pff bridge can be
  made fully concrete.
- `FloatSpec/src/Core/Generic_fmt.lean` also corrected the same-name statement
  split between `round_generic` and `generic_format_round` after comparison with
  upstream Flocq: `round_generic` is now the identity theorem for already-generic
  inputs, while `generic_format_round` no longer assumes `generic_format x` and
  exposes the format-of-rounded-value theorem via `roundR`. This is statement
  alignment debt, not a reduction of the 19 active absent/scaffold wrappers.
- `FloatSpec/src/Core/Round_NE.lean` now factors the DN/UP parity theorem into
  `DN_UP_NE_prop`: for a non-representable value and concrete down/up
  neighbors, at least one endpoint satisfies `NE_prop`. This packages the
  parity-to-even-endpoint payload needed by nearest-even tie handling. It is
  still not the full Flocq `round_NE_pt`, because the remaining midpoint bridge
  must show that the concrete `Znearest (fun t => !(decide (2 ∣ t)))` choice
  selects that `NE_prop` endpoint in exact ties.
- `FloatSpec/src/Core/Round_NE.lean` now also has `round_NE_pt_of_ne_mid`:
  outside the exact midpoint case, the concrete `ZnearestE` result satisfies
  `Rnd_NE_pt` by combining the concrete `Generic_fmt.round_N_pt`,
  `round_DN_pt`, `round_UP_pt`, and `Round_pred.Rnd_N_pt_unique_spec`.
  A follow-up subscription harness attempt at
  `.change_log/codex_attempt_20260626_074353` made no source changes and
  reconfirmed that the remaining proof gap for the real Flocq `round_NE_pt` is
  the concrete midpoint parity-selection theorem.
- `FloatSpec/src/Core/Round_NE.lean` now has the integer-side midpoint lemma
  `ZnearestE_half_even`: at an exact half-integer, the concrete nearest-even
  choice `fun t => !(decide (2 ∣ t))` returns an integer with residue `0`
  modulo `2`. This proves the parity of the selected scaled mantissa; the
  remaining midpoint bridge must still connect that selected integer/endpoint
  back to the canonical DN/UP float used by `NE_prop`.
- `FloatSpec/src/Core/Round_NE.lean` now has
  `round_NE_pt_of_midpoint_choice`: once the exact-midpoint branch proves that
  the endpoint selected by `Znearest choice` satisfies `NE_prop`, the concrete
  rounded value immediately satisfies `Rnd_NE_pt` via `round_N_middle` and
  `Generic_fmt.round_N_pt`. This removes the rounding-rewrite part of the
  midpoint blocker; the unresolved payload is now specifically the selected
  endpoint's canonical even-mantissa witness.
- `FloatSpec/src/Core/Round_NE.lean` now has
  `NE_prop_of_generic_even_mantissa` and
  `round_NE_pt_of_canonical_even`. These mirror the witness construction in
  Flocq's positive midpoint proof: a generic rounded value yields the canonical
  float `(Ztrunc (scaled_mantissa r), cexp r)`, and an even canonical mantissa
  is enough to produce `NE_prop` and hence `Rnd_NE_pt` for the concrete
  `roundR ... (Znearest choice) x`. The remaining exact-midpoint task is now
  the parity fact
  `Ztrunc (scaled_mantissa (roundR ... ZnearestE x)) % 2 = 0`.
- `FloatSpec/src/Core/Round_NE.lean` now also has
  `round_DN_canonical_even_of_floor_even`, the floor-selected half of that
  parity bridge: if positive `x` rounds downward and the original scaled floor
  mantissa is even, then the canonical mantissa of the concrete down-rounded
  endpoint is even. This was infrastructure for the non-generic exact-midpoint
  branch of Flocq's `round_NE_pt`; it was not itself one of the 19 public
  exact-name gaps, so the public count did not decrease at this step.
- `FloatSpec/src/Core/Round_NE.lean` now has `round_NE_pt_of_generic`, the
  concrete generic-format branch of Flocq's `round_NE_pt`: when `x` is already
  in `generic_format`, `roundR ... ZnearestE x` is an `Rnd_NE_pt` by
  `roundR_generic` and `Rnd_NG_pt_refl_spec`.
- `FloatSpec/src/Core/Round_NE.lean` also has
  `round_NE_pt_of_generic_or_ne_mid`, which closes the concrete
  nearest-even point theorem whenever `x` is generic or the concrete DN/UP
  distances are unequal. After this helper, the only remaining case for the
  public `round_NE_pt` theorem was the non-generic exact-midpoint case.
- `FloatSpec/src/Core/Round_NE.lean` now has
  `round_DN_canonical_parity_of_floor`, `round_NE_pt_pos_exact`,
  `ZnearestE_opp`, and `roundR_ZnearestE_opp`, and the public
  `round_NE_pt` wrapper has been restored from totality to the concrete
  upstream-style point theorem:
  `Rnd_NE_pt beta fexp x (roundR beta fexp (Znearest (fun t => !(decide (2 ∣ t)))) x)`.
  `lake env lean FloatSpec/src/Core/Round_NE.lean` typechecks the result. This
  closes the same-name underpowered theorem that blocked the Pff nearest-even
	  bridge; it did not itself reduce the exact active list because
  `round_NE_pt` was a dependency-level theorem, not one of the currently listed
  absent/`Unit` public wrappers.
- `FloatSpec/src/Core/Generic_fmt.lean` restored `Znearest_DN_or_UP` from a
  Hoare-triple wrapper around `pure (Znearest choice x)` to the direct
  upstream-style disjunction
  `Znearest choice x = Zfloor x ∨ Znearest choice x = Zceil x`; downstream
  `Relative` and `Ulp` callers now consume the theorem directly.
- `FloatSpec/src/Core/Generic_fmt.lean` restored `Znearest_ge_floor` from a
  Hoare-triple wrapper over an auxiliary pair-checker to the direct upstream
  integer inequality `Zfloor x ≤ Znearest choice x`; the obsolete local checker
  was removed and `valid_rnd_N` now consumes the theorem directly.
- `FloatSpec/src/Core/Generic_fmt.lean` restored `Znearest_le_ceil` from the
  matching Hoare-triple pair-check wrapper to the direct upstream integer
  inequality `Znearest choice x ≤ Zceil x`; `valid_rnd_N` now uses it without
  reducing `Id`/Hoare syntax.
- `FloatSpec/src/Core/Generic_fmt.lean` restored `Znearest_N_strict`,
  `Znearest_half`, and `Znearest_imp` from Hoare-triple/check-carrier wrappers
  to direct upstream-style theorems over the integer chosen by `Znearest`.
  Downstream `Ulp`, `Relative`, `Div_sqrt_error`, `Double_rounding`, and
  `Round_odd` callers now consume the direct theorem payloads.
- A 2026-06-26 source recheck confirmed `Znearest_opp` is also already exposed
  as a direct Flocq-shaped theorem:
  `Znearest choice (-x) = - Znearest (fun t => ! choice (-(t + 1))) x`.
  It is no longer Generic nearest-rounding alignment debt.
- `FloatSpec/src/Core/Float_prop.lean` now includes the Coq-compatible
  `Raux.mag` bridges `Zdigits_Raux_mag` and `Raux_mag_F2R_Zdigits`, which align
  integer digit counts and scaled `F2R` magnitudes with the magnitude used by
  `Generic_fmt.cexp`.
- `FloatSpec/src/Core/Float_prop.lean` now also includes
  `Raux_mag_F2R_bounds_Zdigits`, the positive adjacent-float interval analogue
  needed by the Calc/Round exponent bridge.
- `FloatSpec/src/Calc/Round.lean` restored `cexp_inbetween_float` and
  `cexp_inbetween_float_loc_Exact` from conclusion-as-hypothesis wrappers to
  Flocq-style exponent alignment theorems. Lean keeps the Coq radix condition
  explicit as `1 < beta`.
- `FloatSpec/src/Calc/Round.lean` restored `Audit.generic_format_truncate` from
  a placeholder over `truncate_aux ... 0` to a proof over `truncate_triple`.
  The proof handles both the positive truncation case and the unchanged case,
  using `Zdigits_div_Zpower`, `Zpower_gt_Zdigits`, and the new `Raux.mag` bridge
  to discharge `generic_format_F2R`.
- `FloatSpec/src/Calc/Round.lean` restored `Audit.truncate_correct_partial'`
  and `Audit.truncate_correct_partial` from self-equality shells to Coq-style
  preservation theorems over `truncate_triple`: the truncated triple still
  brackets the original positive `x`, and its resulting exponent is
  `cexp beta fexp x`. Lean keeps the radix condition explicit as `1 < beta`.
- `FloatSpec/src/Calc/Round.lean` restored `Audit.truncate_correct'` and
  `Audit.truncate_correct` from self-equality shells to Coq-style truncation
  correctness theorems over `truncate_triple`: truncation preserves the
  `inbetween_float` bracket, and the resulting exponent is either the canonical
  exponent `cexp beta fexp x` or the result is exact and `x` is in the generic
  format. The unprimed theorem uses `cexp_inbetween_float_loc_Exact` to bridge
  the upstream `fexp (Zdigits beta m + e)` hypothesis.
- `FloatSpec/src/Calc/Round.lean` restored `round_sign_any_correct`,
  `round_trunc_sign_any_correct'`, and `round_trunc_sign_any_correct` from
  canonical-exponent-only/self-equality shells to sign-aware Flocq-style
  wrappers. They now round `x` from an `inbetween_float` bracket on `|x|`,
  use `cond_Zopp (Rlt_bool x 0)` in the returned mantissa, pass exact generic
  cases through `roundR_generic`, and reuse the restored truncation correctness
  payloads plus `cexp_abs`/`generic_format_abs_inv`.
- `FloatSpec/src/Calc/Round.lean` restored `Audit.truncate_correct_format` from
  a tautological `truncate_triple` self-equality to the upstream-shaped payload:
  truncating an exact generic-format `F2R (Float beta m e)` preserves its real
  value and returns exponent `cexp beta fexp x`. The positive truncation branch
  uses `scaled_mantissa_generic`, `Raux_mag_F2R_Zdigits`, and the integer
  `Zfloor_div` bridge.
- `FloatSpec/src/Calc/Round.lean` restored `truncate_FIX_correct` from a weak
  exponent-bound wrapper over `fun k => max emin k` to the upstream-shaped
  specialization for `FIX_exp emin`: `truncate_FIX` preserves the
  `inbetween_float` bracket, and either returns the FIX canonical exponent or
  returns an exact location with `x` in the FIX generic format. The no-shift
  exact branch uses `generic_format_F2R`; Lean keeps the radix condition
  explicit as `1 < beta`.
- `FloatSpec/src/Calc/Round.lean` restored `inbetween_float_round` from a
  scaled-mantissa helper theorem to the upstream-shaped theorem over
  `inbetween_float beta m (cexp beta fexp x) x l`. A new private
  `inbetween_scaled_mantissa` bridge factors the positive scaling argument
  through `inbetween_mult_compat`; downstream `inbetween_float_NA` and
  `round_any_correct` now call the direct theorem.
- `lake build FloatSpecTests` still fails because the declared
  `FloatSpecTests` library points at `FloatSpec/Test`, but that directory does
  not exist. The property-test/smoke-test layer is therefore still infrastructure
  debt even though the default library build succeeds.

Current live split after the latest re-audit: 0 exact active public scaffolds
remain. There are 0 same-name public `Unit` scaffolds and 0 absent active
public declarations in the current branch-diff wrapper list. This does not
mean the full Flocq port is complete: lower prerequisite theorem stacks such
as Pff `Dekker` product splitting and Pff `ErrFmaApprox` still remain.

- `FloatSpec/src/Pff/Pff2Flocq.lean`:
  - none

Current restore blockers found by pipeline attempts:

- No exact active names remain in `FloatSpec/src/IEEE754/Binary.lean`.
- No exact active names remain in `FloatSpec/src/Prop/Double_rounding.lean`.
- `Veltkamp_Even`, `Veltkamp`, and `Veltkamp_tail`: these public
  `Pff2Flocq` wrappers are now present as real Lean theorems. A checked
  2026-07-02 follow-up restored `Veltkamp_Even` at
  `FloatSpec/src/Pff/Pff2Flocq.lean:1525`, `Veltkamp` at
  `FloatSpec/src/Pff/Pff2Flocq.lean:1550`, and `Veltkamp_tail` at
  `FloatSpec/src/Pff/Pff2Flocq.lean:1573`; each consumes the explicit lower
  Pff payload that upstream obtains from `VeltkampEven`/`Veltkamp`/
  `Veltkamp_tail` and delegates to the checked final conversion bridge.
  The lower Pff algorithm payloads themselves remain prerequisite debt, but
  the public wrapper names are no longer active exact-name gaps. Upstream
  `Pff2Flocq.v` proves them by importing the Pff algorithm payloads through
  the generic nearest-rounding bridge and canonicity facts. The generic
  nearest-rounding equality bridge is now present in
  `Pff2FlocqAux.lean`, and `Fast2Sum_correct` now shows the wrapper pattern.
  A 2026-06-30 checked helper, `Veltkamp_round_N_witnesses`, now packages the
  wrapper-side conversion of formatted `x` and the three `round_N_is_pff_round`
  destructs for the Veltkamp intermediates `p`, `q`, and `hx`. A follow-up
  checked helper, `Veltkamp_tail_round_N_witnesses`, adds the fourth tail
  destruct for `tx := rnd (x - hx)`, matching the extra wrapper setup in
  upstream `Veltkamp_tail`. A subsequent checked bridge,
  `Veltkamp_Even_from_reduced_evenClosest`, performs the final
  reduced-bound `EvenClosest` to public Flocq nearest-even equality conversion
  needed by `Pff2Flocq.Veltkamp_Even`; it still assumes the lower Pff
  `VeltkampEven` payload supplies that reduced-bound witness. Two additional
  checked bridges, `Veltkamp_from_reduced_evenClosest` and
  `Veltkamp_tail_from_pff_tail_payload`, now package the corresponding final
  public conversions for `Pff2Flocq.Veltkamp` and `Pff2Flocq.Veltkamp_tail`;
  the former chooses nearest-even as the existential nearest choice, and the
  latter converts a bounded tail float into the public equality plus
  `generic_format` conclusion. The lower Pff `Veltkamp`/`Veltkamp_tail`
  payloads still remain missing algorithmic steps. As lower unblock steps,
  `IplusCorrectEq`, `IminusCorrectEq`, `IplusOl`, and `IminusOp` are now
  restored in `Pff.lean`; `MKnuth`, `MKnuth1`, `MKnuth2`, `MKnuth3`,
  `MKnuth4`, `MKnuth6`, and `MKnuthOpp` are now also restored as real theorems after
  `errorBoundedPlus`. The `s - c` exactness subgoal is now factored as
  `MKnuth5_s_minus_c_exact` through `minusRoundRep`, and the `q <= c`
  Sterbenz branch of upstream `MKnuth5` is now factored as `MKnuth5_q_le_c`.
  The easy branches of upstream `ExactMinusIntervalAux1` are also packaged as
  `ExactMinusIntervalAux1_from_hard_branch`, so the remaining exact-minus work
  is localized to the hard branch where both `2*p < q` and `2*p < r`.
  The sign split from upstream `MKnuth7` is now packaged as
  `MKnuth7_from_MKnuth5`, so once the positive `MKnuth5` payload is available
  the nonpositive cases no longer block the final theorem. The remaining Knuth
  payload also has the upstream `ExactMinusInterval` normalization wrapper
  factored as `ExactMinusInterval_from_Aux1`, so bounded inputs can be reduced
  to the canonical interval payload without repeating normalization
  bookkeeping. The hard-branch induction is now also factored as
  `ExactMinusIntervalAux_from_pred_step` using `FinductNeg`; the remaining
  work is the concrete predecessor-step arithmetic inside upstream
  `ExactMinusIntervalAux`. The normalization/radix-range setup for that step is
  now packaged as `ExactMinusIntervalAux_pred_setup`. The boundary subcase where
  `FPred r <= 2*p` is packaged as
  `ExactMinusIntervalAux_pred_sterbenz_case`, and `FPredBounded` packages the
  canonicity-to-boundedness fact needed by both predecessor branches, so the
  remaining predecessor step is the strictly-above-boundary arithmetic.

  A 2026-06-29 subscription harness attempt at
  `.change_log/codex_attempt_20260629_151203` targeted
  `Veltkamp_Even`. The underlying Codex run reached a blocked classification
  before the outer wrapper was interrupted: upstream `Pff2Flocq.v` proves this
  wrapper by calling the lower Pff `VeltkampEven` payload, while the local tree
  still has no `VeltkampEven`/`Veltkamp`/`Veltkamp_tail` Pff theorem. A manual
  follow-up added the checked bridge
  `evenClosest_value_eq_round_NE` in
  `FloatSpec/src/Pff/Pff2FlocqAux.lean`: from any Pff `EvenClosest` witness it
  derives equality with the concrete Lean nearest-even `roundR` value. This
  removes the wrapper conversion work needed after the lower Pff Veltkamp
  payload is restored. The public Veltkamp wrappers have since been exposed as
  exact Lean theorem names using that conversion boundary. A 2026-06-30
  follow-up restored the lower Pff
  Veltkamp subnormal-bound helper `plusExp` and the exact theorem
  `Closestbplusb` in `FloatSpec/src/Pff/Pff.lean`; this closes the
  enlarged-bound-to-original-bound closestness transfer used by upstream
  `VeltkampS`. A later 2026-06-30 checked follow-up added the explicit
  reduced Veltkamp bound `Veltkamp_reducedBound` and the exact Coq local
  theorem `p'GivesBound`, restoring the mantissa-bound equation for the
  smaller `t - s` precision bound. A subsequent checked pass restored the
  adjacent Coq local sign lemmas `pPos` and `qNeg`: the first rounded scaled
  value is nonnegative, and the rounded residual `x - p` is nonpositive.
  These package the rounded-mode monotonicity setup used repeatedly in the
  later Veltkamp section. Another checked helper,
  `RleRRounded_from_Fulp_rel`, now factors the final real-arithmetic step of
  upstream local `RleRRounded`: once `ClosestUlp` and the relative
  `FulpLe2`-style estimate are available, it derives the Veltkamp relative
  rounded-value bound. A subsequent checked pass restored the exact Coq name
  `FulpLe2`, proving that relative ulp estimate from normality of the
  normalized representative and `FnormalizeCorrect`. A later checked pass
	  restored the exact local theorem `RleRRounded` by combining `ClosestUlp`,
	  `FcanonicFnormalizeEq`, `FulpLe2`, and the factored arithmetic helper. A
	  2026-06-30 checked follow-up also added `Fnormalize_Fabs` and `FNevenFabs`,
	  the lower-Pff absolute-value normalization/parity bridges needed before
	  porting upstream `EvenClosestFabs`. A 2026-07-01 checked pass restored exact
	  Coq theorem `FulpFabs` at `FloatSpec/src/Pff/Pff.lean:3351`, proving
	  that the normalized ulp is invariant under float absolute value. The same
	  line of work restored exact Coq theorem `EvenClosestFabs` at
	  `FloatSpec/src/Pff/Pff.lean:9869`,
	  combining `ClosestFabs`, `FNevenFabs`, and symmetry/uniqueness of
	  `EvenClosest`. This removes the absolute-value even-closest prerequisite
	  from the Veltkamp path, but the lower Pff
	  `VeltkampEven`/`Veltkamp`/`Veltkamp_tail` algorithm payloads are still
	  absent.

  `ExactMinusIntervalAux_pred_same_exp_case` now packages the first constructive
  branch of that arithmetic: when the normalized representative of `r - p` has
  the same exponent as `r` and `FPred r` is one ulp below `r` in that exponent,
  decrementing the representative mantissa gives a bounded representative of
  `FPred r - p`. `ExactMinusIntervalAux_pred_one_ulp_case` factors that
  decrement step, and the adjacent-exponent normal-boundary branch using
  `FPredSimpl2` is now packaged as
  `ExactMinusIntervalAux_pred_adjacent_normmin_case`. The non-boundary
  adjacent branch using `FPredSimpl4` is now packaged through
  `ExactMinusIntervalAux_pred_beta_ulp_case` and
  `ExactMinusIntervalAux_pred_adjacent_non_normmin_case`, where decrementing
  the representative mantissa by `beta` gives the bounded representative. The
  same-exponent `FPredSimpl4` and `FPredSimpl3` branches are now packaged as
  `ExactMinusIntervalAux_pred_same_exp_non_normmin_case` and
  `ExactMinusIntervalAux_pred_same_exp_normmin_minexp_case`. The four
  branch helpers are now composed by
  `ExactMinusIntervalAux_pred_constructive_cases`, which dispatches over the
  same/adjacent exponent split and the normal-boundary cases without adding a
  public wrapper shell. The normalization/radix-range facts from
  `ExactMinusIntervalAux_pred_setup` are now plugged into that dispatcher by
  `ExactMinusIntervalAux_pred_constructive_from_setup`. The remaining
  same-exponent normal-boundary contradiction is now packaged as
  `ExactMinusIntervalAux_same_exp_normmin_non_minexp_contradiction`, using
  `FcanonicLtPos` and `pNormal_absolu_min`. The predecessor induction and
  interval stack are now closed: `ExactMinusIntervalAux_from_hard_pred_step`
  packages the Coq predicate `2*p < r -> exists r', r' = r - p`,
  `ExactMinusIntervalAux` closes the hard branch, `ExactMinusIntervalAux1`
  adds the easy Sterbenz branches, and `ExactMinusInterval` restores the
  bounded-input theorem through the normalization wrapper. With that payload
  available, the explicit interval premise has also been discharged from the
  Knuth chain: `MKnuth5`, `MKnuth7`, and `Knuth` now have direct theorem
  declarations and proofs, while the older `*_from_interval` helpers remain as
  internal factored wrappers. `TwoSum_correct` is now restored using that
  `Knuth` payload through the Pff-to-Flocq wrapper and nearest-rounding bridge.
  A 2026-06-22 XHub harness attempt on `ExactMinusIntervalAux_pred_setup`
  reached the local target gate but produced no patch because the supplied API
  token returned 401 quota exhausted. A later 2026-06-22 XHub API attempt on
  composing the restored predecessor branch helpers likewise produced no patch:
  `.change_log/codex_attempt_20260622_051815` records `provider_mode=api`,
  `api_wire_api=responses`, `local_target_gate=pass`, and the same
  quota-exhausted 401 from `/models`.
  Restoring the Pff2Flocq wrappers before that would either be circular or
  payload-free.
- `Axpy`: upstream Flocq proves this from Pff's `Axpy_opt` plus the min/max
  rounding infrastructure (`MinOrMax`, `MinUniqueP`, `MaxUniqueP`,
  `RND_Min_correct`, `RND_Max_correct`, and the Pff-to-Flocq DN/UP rounding
  bridges). The current Lean tree now has the min/max uniqueness and
  correctness infrastructure, including `MinUniqueP`, `MaxUniqueP`,
  `RND_Min_correct`, `RND_Max_correct`, and the closed DN/UP support, but it
  still has no local `Axpy_opt` theorem in `FloatSpec/src/Pff/Pff.lean`. A
  2026-06-29 checked bridge, `Axpy_from_min_or_max` in
  `FloatSpec/src/Pff/Pff2Flocq.lean`, now proves the final wrapper conversion:
  from an explicit bounded Pff witness for `tv` plus the
  `isMin' ... ftv ∨ isMax' ... ftv` result corresponding to upstream
  `Axpy_opt`, it derives that `tv` is either the concrete Flocq DN or UP
  rounding of `y + a*x`. A checked 2026-07-02 follow-up restored the public
  exact-name wrapper `Axpy` at `FloatSpec/src/Pff/Pff2Flocq.lean:4361`;
  it consumes the explicit final `MinOrMax` payload and calls
  `Axpy_from_min_or_max`. The remaining Axpy work is therefore the lower Pff
  computation theorem `Axpy_opt`, not the public Pff-to-Flocq wrapper name.
  A checked 2026-07-01 pass restored the exact
  upstream AxpyMisc prerequisite `FulpLeGeneral` at
  `FloatSpec/src/Pff/Pff.lean:19472`, proving the normal branch from
  `FulpLe2` and the subnormal branch from the boundary exponent of
  `Fnormalize`. A follow-up checked pass restored the radix-2 AxpyMisc theorem
  `RoundLeGeneral` at `FloatSpec/src/Pff/Pff.lean:27375`, deriving the rounded
  value bound from `ClosestUlp`, `FulpLeGeneral`, and the positive
  `1 - 2^-precision` denominator. A subsequent checked pass restored
  `ExactSum_Near` at `FloatSpec/src/Pff/Pff.lean:27502`, using
  `errorBoundedPlus` to construct the sum-error float and the strict
  minimum-exponent bound to prove that error has zero mantissa. The remaining
  Axpy prerequisite path now moves into the large `Axpy_aux*`/`Axpy_opt` stack.
  In that stack, a checked pass restored the Coq `MinOrMax` disjunction at
  `FloatSpec/src/Pff/Pff.lean:675` and `MinOrMax_Fopp` at
  `FloatSpec/src/Pff/Pff.lean:15868`, deriving sign symmetry from
  `MinOppMax`, `MaxOppMin`, and `Fopp_Fopp`. A checked 2026-07-01 pass restored
  the upstream predecessor/successor cancellation theorem `FSucPred` at
  `FloatSpec/src/Pff/Pff.lean:1900`, deriving it from `FPredSuc`,
  `FPredFopFSucc`, `FSuccFopFPred`, `FcanonicFopp`, and `Fopp_Fopp`. This is
  prerequisite progress, not a reduction of the then-active exact public
  Pff-to-Flocq wrapper names. A follow-up checked pass restored the upstream
  predecessor ordering theorem `FPredProp` at
  `FloatSpec/src/Pff/Pff.lean:13864`, proving it as the sign-dual of
  `FSuccProp` through `FcanonicFopp`, `FPredFopFSucc`, and `F2R_opp`. The same
  checked pass restored the upstream positive-predecessor theorem
  `R0RltRlePred` at `FloatSpec/src/Pff/Pff.lean:2410`, using the sign-dual
  `R0RltRleSucc` bridge and `FPredFopFSucc`. Another checked pass restored the
  upstream ulp monotonicity theorem `LeFulpPos` at
  `FloatSpec/src/Pff/Pff.lean:26912`, using canonical exponent comparison via
  `Fcanonic_Rle_Zle`; it then restored the two predecessor ulp corollaries
  `FulpFPredGePos` at `FloatSpec/src/Pff/Pff.lean:26984` and `FulpFPredLe` at
  `FloatSpec/src/Pff/Pff.lean:27036`. A follow-up checked pass restored the
  upstream successor/predecessor ulp bridge: `FSuccDiffPos` at
  `FloatSpec/src/Pff/Pff.lean:27110`, `FSuccUlpPos` at
  `FloatSpec/src/Pff/Pff.lean:27194`, and `FpredUlpPos` at
  `FloatSpec/src/Pff/Pff.lean:27234`. Another checked pass restored the first
  two upstream MinOrMax closeness lemmas: `MinOrMax2` at
  `FloatSpec/src/Pff/Pff.lean:27312`, using the restored predecessor ulp bridge
  and `FPredProp`, and `MinOrMax1` at `FloatSpec/src/Pff/Pff.lean:27425`,
  splitting around the sign of `z - p` and delegating the nonnegative branch to
  `MinOrMax2`. A follow-up checked pass restored the zero-valued MinOrMax case:
  local bridges `FcanonicZeroEq` at `FloatSpec/src/Pff/Pff.lean:27542` and
  `FpredUlpZero` at `FloatSpec/src/Pff/Pff.lean:27576`, the upstream
  nonpositive auxiliary theorem `MinOrMax3_aux` at
  `FloatSpec/src/Pff/Pff.lean:27640`, and the signed theorem `MinOrMax3` at
  `FloatSpec/src/Pff/Pff.lean:27724`. A checked follow-up restored the exact
  subnormal branch theorem `Axpy_aux2` at
	  `FloatSpec/src/Pff/Pff.lean:28517`, using `ClosestUlp`, the subnormal ulp
	  boundary, and `MinOrMax1` to derive the min/max conclusion. A subsequent
	  checked pass restored the exact upstream estimate `Axpy_aux1_aux3` at
	  `FloatSpec/src/Pff/Pff.lean:29194`, deriving the quarter-ulp bound from
	  `ClosestUlp`, the subnormal ulp identity, `FPredCanonic`, `CanonicFulp`, and
	  the predecessor exponent lower bound. A 2026-07-01 checked pass restored
	  `Axpy_aux1_aux1` at `FloatSpec/src/Pff/Pff.lean:29017`, using the normal
	  `t` branch, a two-exponent scaling comparison through `LeFulpPos`, and
	  `FulpFPredLe` to obtain the predecessor quarter-ulp bound. A checked
	  2026-07-01 follow-up restored exact upstream theorem `Axpy_aux1` at
	  `FloatSpec/src/Pff/Pff.lean:28780`, using the factored quarter-ulp error
	  estimate, `Closest` against the predecessor candidate in the left branch,
	  and `MinOrMax1`/`MinOrMax2` for the final min/max disjunction. Another
	  checked 2026-07-01 pass restored the upstream Axpy neighbor definition
	  `FLess` at `FloatSpec/src/Pff/Pff.lean:27932` and exact theorem
	  `UlpFlessuGe_aux` at `FloatSpec/src/Pff/Pff.lean:30030`, proving the
	  selected neighbor's absolute value is at least one ulp closer to zero via
	  the positive predecessor case and the `Fopp` successor/predecessor dual.
	  Another checked pass restored exact upstream theorem `Axpy_aux3` at
	  `FloatSpec/src/Pff/Pff.lean:29289`, combining the subnormal predecessor
	  boundary, the restored `ExactSum_Near` payload via `errorBoundedPlus`, and
	  the `MinOrMax1`/`MinOrMax2` branches. Another checked pass restored
	  `AxpyPos` at `FloatSpec/src/Pff/Pff.lean:29604`, dispatching the positive
	  `u` case across the normal `t` branch (`Axpy_aux1_aux1` then `Axpy_aux1`)
	  and the subnormal `t` branches (`Axpy_aux3` for the boundary predecessor,
	  or `Axpy_aux1_aux3` then `Axpy_aux1` for the larger predecessor exponent).
	  Another checked pass restored the nonzero signed dispatch helper
	  `Axpy_tFlessu_nonzero` at `FloatSpec/src/Pff/Pff.lean:29678`, using
	  `AxpyPos` directly for positive `u` and via `ClosestOpp`,
	  `FcanonicFopp`, `oppBounded`, the `FPredFopFSucc`
	  predecessor/successor dual, and `MinOrMax_Fopp` for negative `u`. A
	  checked follow-up packaged the zero-valued branch as
	  `Axpy_tFlessu_zero` at `FloatSpec/src/Pff/Pff.lean:29884`: the scale
	  hypothesis forces `t = 0`, closestness of `u` to `t + y` forces
	  `y = 0`, and `ClosestUlp` plus the predecessor ulp comparison provides
	  the small-distance hypothesis for `MinOrMax3`. A 2026-07-01 follow-up
	  restored upstream-shaped `Axpy_tFlessu` at
	  `FloatSpec/src/Pff/Pff.lean:30029` without the extra
	  `_root_.F2R u ≠ 0` precondition by dispatching to the nonzero helper or
	  the zero branch. A checked follow-up added the `Axpy_opt` scale-algebra
	  cut `Axpy_scale_from_round_and_lower` at
	  `FloatSpec/src/Pff/Pff.lean:30411`: once `RoundLeGeneral` supplies the
	  rounded-`t` bound and the closestness/ulp estimates supply the lower
	  bound on `u`, this real-arithmetic lemma derives the
	  `4 * |t| ≤ |u|` premise needed by `Axpy_tFlessu`. Another checked
	  follow-up added the rounded-sum lower-bound cut
	  `Axpy_u_lower_from_sum_error` at
	  `FloatSpec/src/Pff/Pff.lean:30446`, packaging the reverse-triangle and
	  closest-rounding-error part of the Coq derivation of
	  `(|y| - |t|)/(1 + eps) ≤ |u|`. A checked follow-up added
	  `Axpy_sum_error_from_closest_ulp` at
	  `FloatSpec/src/Pff/Pff.lean:30489`, deriving the needed
	  `|S-u| ≤ |u|*2^(-precision)` premise from `ClosestUlp` and `FulpLe2`
	  in the normal rounded-sum branch. Another checked follow-up added
	  `Axpy_u_lower_from_closest_sum` at
	  `FloatSpec/src/Pff/Pff.lean:30567`, composing that estimate with the
	  concrete sum `Y + T` to prove
	  `(|Y| - |T|)/(1 + 2^(-precision)) ≤ |u|`. A checked follow-up added
	  `Axpy_scale_from_rounding_inputs` at
	  `FloatSpec/src/Pff/Pff.lean:30610`, composing `RoundLeGeneral`,
	  `Axpy_u_lower_from_closest_sum`, and
	  `Axpy_scale_from_round_and_lower` to derive the full
	  `4 * |t| ≤ |u|` scale premise from the rounded-input hypotheses and the
	  large-`y` dominance hypothesis. Another checked follow-up added the
	  perturbation handoff
	  `Axpy_perturb_from_error_bound` at
	  `FloatSpec/src/Pff/Pff.lean:30686`, packaging the final Coq
	  `Rle_lt_trans` step from the user-facing error hypothesis and the
	  future `UlpFlessuGe2` estimate into the strict quarter-ulp perturbation
	  premise expected by `Axpy_tFlessu`. A checked follow-up added
	  `Axpy_min_or_max_from_rounding_inputs` at
	  `FloatSpec/src/Pff/Pff.lean:32017`, composing the scale premise, the
	  perturbation handoff, and `Axpy_tFlessu` into the final `MinOrMax`
		  conclusion under explicit rounded-input, predecessor-case, and
		  strict-error hypotheses. A 2026-07-02 checked follow-up added
		  `Axpy_opt_from_strict_bound` at `FloatSpec/src/Pff/Pff.lean:32109`,
		  converting the upstream large-`y` hypothesis shape into the rounded-input
		  bridge and leaving the genuine strict coefficient estimate plus predecessor
		  side conditions explicit. A checked follow-up added
		  `Axpy_opt_from_general_bound` at
		  `FloatSpec/src/Pff/Pff.lean:32178`, composing
		  `UlpFlessuGe2_from_general_bound` with the strict-bound bridge so the
		  remaining perturbation obligation has the general coefficient-estimate
		  shape used by upstream `UlpFlessuGe2`. The remaining `Axpy_opt` work is
		  now the numeric `UlpFlessuGe2` coefficient estimate plus
		  discharging/internalizing those explicit side hypotheses from the
		  upstream case split. A checked follow-up added
		  `FLessBounded` at `FloatSpec/src/Pff/Pff.lean:28058`, packaging the
	  upstream sign split that proves the `FLess u` neighbor remains bounded
	  from `FBoundedSuc` and `FBoundedPred`. Another checked follow-up added
	  upstream `FulpGe` at `FloatSpec/src/Pff/Pff.lean:27031`, proving the
	  bounded-float magnitude estimate
	  `|p| <= (radix^precision - 1) * Fulp p`, and
	  `FulpGe_FLess` at `FloatSpec/src/Pff/Pff.lean:28085`, composing
	  `FLessBounded` with `FulpGe` for the exact neighbor bound used at the end
	  of upstream `UlpFlessuGe`. A checked follow-up added
	  `UlpFlessuGe_final_scale` at `FloatSpec/src/Pff/Pff.lean:28123`,
	  packaging the final upstream scale step that turns a
	  `(4*(radix^precision-1))^-1 * |FLess u|` bound into
	  `(1/4) * Fulp (FLess u)` via `FulpGe_FLess`. A checked follow-up added
	  `UlpFlessuGe_from_abs_sub_fulp` at
	  `FloatSpec/src/Pff/Pff.lean:30500`, composing `UlpFlessuGe_aux` with
	  `UlpFlessuGe_final_scale`; it packages the upstream transition from a
	  bound by `|u| - Fulp u` to the quarter-ulp bound on `FLess u`. A checked
	  follow-up added `UlpFlessuGe_from_general_fulp_bound` at
	  `FloatSpec/src/Pff/Pff.lean:30569`, packaging the upstream
	  `FulpLeGeneral` reduction from
	  `|u| - (|u| * radix^(1-precision) + radix^(-dExp))` to the
	  `|u| - Fulp u` premise. A checked follow-up added
	  `UlpFlessuGe2_from_general_bound` at
	  `FloatSpec/src/Pff/Pff.lean:30648`, packaging the strict handoff from
	  the future `UlpFlessuGe2` coefficient estimate to the quarter-ulp
	  conclusion. These are final prerequisites used by the `UlpFlessuGe` path
	  toward `UlpFlessuGe2`.
	  This is still lower-prerequisite progress; the public `Pff2Flocq.Axpy`
	  wrapper is now restored, but the exact lower Pff computation theorem
	  `Axpy_opt` is still not closed. The next Axpy target is the arithmetic
	  estimate layer needed by `Axpy_opt`, plus discharging or internalizing the
	  explicit predecessor-exponent splits now exposed in
	  `AxpyPos`/`Axpy_tFlessu`.
- `Dekker`: a 2026-06-26 subscription harness attempt at
  `.change_log/codex_attempt_20260626_085649` targeted the same-name `Unit`
  scaffold in `FloatSpec/src/Pff/Pff2Flocq.lean` and made no source changes.
  The blocker is semantic, not a placeholder-count artifact: upstream
  `Pff2Flocq.v` proves a full real-valued product-splitting theorem, while the
  existing local `Dekker_FTS_closed` payload only covers the Fast2Sum-style
  closedness/equation used by `Fast2Sum_correct`. Restoring `Dekker` faithfully
  still requires the lower Pff product-splitting payload and the Pff-to-Flocq
  rounding bridge, not just replacing the scaffold with a theorem shell. A
  checked 2026-06-29 follow-up in `FloatSpec/src/Pff/Pff2Flocq.lean` now
  introduces the Coq-shaped wrapper definitions `Dekker_round`,
  `Dekker_t4`, and `Dekker_result`, then proves the two initial upstream zero
  branches `Dekker_result_of_x_eq_zero` and `Dekker_result_of_y_eq_zero`. A
  checked 2026-06-30 follow-up packages those branches as
  `Dekker_result_of_product_eq_zero`, matching the zero-product disjunct in
  `Dekker_result`. A 2026-07-01 follow-up added
  `Dekker_round_N_witnesses` at `FloatSpec/src/Pff/Pff2Flocq.lean:1700`,
  packaging the wrapper-side Pff witnesses for the two Veltkamp
  decompositions, four product rounds, and five final summation rounds by
  destructing `format_is_pff_format` and `round_N_is_pff_round`. A checked
  2026-07-02 follow-up replaced the public `Dekker` `Unit` scaffold at
  `FloatSpec/src/Pff/Pff2Flocq.lean:1853` with a theorem that proves the
  zero-product public postcondition and packages those bounded/canonical Pff
  witnesses. The remaining Dekker-family work is no longer an active public
  `Pff2Flocq` scaffold; it is the lower Pff product-splitting theorem stack
  that supplies the nonzero exactness and unconditional error bound consumed by
  the upstream wrapper.
- `ErrFMA_correct` and `ErrFMA_correct_simpl`: XHub pipeline attempts
  `.change_log/codex_attempt_20260620_013323` and
  `.change_log/codex_attempt_20260620_012353`, plus the subscription attempt
  `.change_log/codex_attempt_20260626_080358`, checked the upstream
  `Pff2Flocq.v` proofs and left these blocked.  Upstream `ErrFMA_correct`
  uses the Pff-level reconstruction theorem `FmaErr` after converting all
  rounded intermediates through the generic nearest-rounding bridge
  `round_N_is_pff_round`; `ErrFMA_correct_simpl` then depends on
  `ErrFMA_correct` after discharging the V2 non-underflow hypotheses.  The
  generic `round_N_is_pff_round` witness bridge is now present in
  `Pff2FlocqAux.lean`, and the current Lean tree has the V2 helpers.  As a
  direct `FmaErr` prerequisite, `FloatSpec/src/Pff/Pff.lean` now restores the
  exact upstream name `ClosestZero2` by reusing the already proved
  `ClosestZero` payload; `lake env lean FloatSpec/src/Pff/Pff.lean` accepts the
  wrapper.  A 2026-06-27 manual pass also restored upstream prerequisites
  `LeExpRound` and `LeExpRound2` in `FloatSpec/src/Pff/Pff.lean`, factoring the
  existing `FminRep`/`FmaxRep_from_FminRep`/`RoundedModeRep_float_from_minmax`
  chain into `ClosestRoundedModeRep` and then using `FboundedEqExp` to transfer
  boundedness to the same-real-value representative at the larger exponent.
  `lake env lean FloatSpec/src/Pff/Pff.lean` accepts these new declarations, and
  the placeholder audit remains at 56 findings.  The larger Pff reconstruction
  theorem `FmaErr` itself is still absent, and the next missing lower theorem in
  that chain is the multiplication-error stack headed by `errorBoundedMult`.
  The current tree now also exposes the exact upstream name `Fmult_correct` in
  `FloatSpec/src/Pff/Pff.lean`, reusing `FloatSpec.Calc.Operations.F2R_mult`
  under the required `1 < beta` section assumption; the Pff file check accepts
  it.  A subsequent manual pass added
  `errorBoundedMultClosest_from_nonneg`, a proved sign-reduction bridge for the
  closest-rounding multiplication error: once the nonnegative branch is proved
  from the min/max quotient arithmetic, this lemma extends it to all input signs
  using `ClosestOpp` and `oppBounded`.  The same pass also added
  `errorBoundedMultClosest_nonneg_from_minmax` and
  `errorBoundedMultClosest_from_minmax`, which dispatch a closest-rounded
  nonnegative product through `ClosestMinOrMax` once the min/max multiplication
  branches are available.  This still does not restore the public Flocq name
  `errorBoundedMult`; the missing arithmetic payload is now isolated to the
  positive min/max quotient branches corresponding to upstream
  `errorBoundedMultMin` and `errorBoundedMultMax`.  Restoring the ErrFMA
  wrappers first would still require a weakened theorem or a payload-free proof.
	  A 2026-06-29 manual helper
	  `errorBoundedMult_from_same_exp_mantissa_bound` at
	  `FloatSpec/src/Pff/Pff.lean:21252` now packages the common final min/max
	  arithmetic step: given a same-exponent representative and the strict mantissa
	  error bound, it constructs the bounded error float at exponent
	  `p.Fexp + q.Fexp`.  A 2026-06-30 checked follow-up added
	  `errorBoundedMultMin_from_quotient_bound` and
	  `errorBoundedMultMax_from_quotient_bound` in
	  `FloatSpec/src/Pff/Pff.lean`: the min/max branches now derive the required
	  same-exponent rounded-product representation through `FminRep` and
	  `FmaxRep_from_FminRep`, then call the shared construction helper.  The
	  next 2026-06-30 checked follow-up added
	  `errorBoundedMultMin_quotient_error_bound_from_decomp` and
	  `errorBoundedMultMax_quotient_error_bound_from_decomp` at
	  `FloatSpec/src/Pff/Pff.lean:21419` and
	  `FloatSpec/src/Pff/Pff.lean:21467`. These package the strict integer
	  mantissa-error estimates once the quotient decomposition and the min/max
	  bucket inequalities have been established.  The next checked pass connected
	  those estimates to `ZquotientProp` as
	  `errorBoundedMultMin_quotient_error_bound` and
	  `errorBoundedMultMax_quotient_error_bound` at
	  `FloatSpec/src/Pff/Pff.lean:21437` and
	  `FloatSpec/src/Pff/Pff.lean:21489`.  A subsequent checked pass added
	  `F2R_le_same_exp_mantissa_le` plus left/right representation wrappers at
	  `FloatSpec/src/Pff/Pff.lean:21291`, `FloatSpec/src/Pff/Pff.lean:21310`,
	  and `FloatSpec/src/Pff/Pff.lean:21329`; these cancel the common positive
	  radix power and turn same-exponent real comparisons into integer mantissa
	  inequalities.  The next checked layer added
	  `errorBoundedMultMin_bucket_le_from_isMin` and
	  `errorBoundedMultMax_bucket_le_from_isMax` at
	  `FloatSpec/src/Pff/Pff.lean:21352` and
	  `FloatSpec/src/Pff/Pff.lean:21385`; these feed bounded same-exponent
	  quotient-bucket candidates through the `isMin'`/`isMax'` extremum payloads
	  and recover the integer min/max bucket inequalities.  A follow-up added
	  `errorBoundedMultMin_bucket_le_from_isMin_candidate_repr` and
	  `errorBoundedMultMax_bucket_le_from_isMax_candidate_repr` at
	  `FloatSpec/src/Pff/Pff.lean:21419` and
	  `FloatSpec/src/Pff/Pff.lean:21454`, matching the actual upstream shape
	  where `FboundedMbound` supplies a bounded shifted-exponent candidate whose
	  real value is then identified with the same-exponent quotient bucket.  The
	  next checked helper, `FboundedMbound_zpower_bucket_candidate` at
	  `FloatSpec/src/Pff/Pff.lean:21491`, packages that construction directly:
	  from `FboundedMbound` at exponent `precision + e`, it produces a bounded
	  candidate represented as `bucket * Zpower_nat radix precision` at exponent
	  `e`.  The next checked integer layer added `abs_mul_le_square_of_abs_lt`,
	  `quotient_abs_le_of_mul_abs_le_square`, and
	  `Zquotient_abs_le_of_product_abs_le_square` at
	  `FloatSpec/src/Pff/Pff.lean:21553`,
	  `FloatSpec/src/Pff/Pff.lean:21566`, and
	  `FloatSpec/src/Pff/Pff.lean:21584`; these package the quotient-size side
	  condition needed to apply `FboundedMbound` to `Zquotient prod n`.  The
	  next checked layer added `F2R_le_of_same_exp_mantissa_le`,
	  `Zquotient_bucket_F2R_le_product`, and
	  `product_F2R_le_next_Zquotient_bucket` at
	  `FloatSpec/src/Pff/Pff.lean:21347`,
	  `FloatSpec/src/Pff/Pff.lean:21614`, and
	  `FloatSpec/src/Pff/Pff.lean:21643`; these package the real comparisons
	  between the quotient bucket candidates and the exact product for the min
	  and max branches.  The next checked helper,
	  `errorBoundedMultMin_mantissa_bound_from_quotient` at
	  `FloatSpec/src/Pff/Pff.lean:21665`, composes the min-side stack all the way
	  to the strict mantissa bound required by
	  `errorBoundedMultMin_from_quotient_bound`: quotient size, bounded bucket
	  candidate, `isMin'` extremum comparison, and final quotient-error
	  arithmetic.  A 2026-06-30 checked follow-up added the max-side successor
	  quotient size helper `Zquotient_succ_abs_le_of_product_abs_le_square` at
	  `FloatSpec/src/Pff/Pff.lean:21607` and the corresponding composed
	  mantissa-bound helper `errorBoundedMultMax_mantissa_bound_from_quotient`
	  at `FloatSpec/src/Pff/Pff.lean:21885`.  The next checked follow-up exposed
	  the exact lower Pff branch theorem `errorBoundedMultMin` at
	  `FloatSpec/src/Pff/Pff.lean:22059`, deriving the quotient-bound premise
	  from bounded nonnegative input mantissas and the product-square estimate.
	  A further checked follow-up added the max-side remainder sign helper
	  `Zquotient_remainder_nonneg_of_nonneg` at
	  `FloatSpec/src/Pff/Pff.lean:21633`, the exact-zero helper
	  `errorBoundedMultMax_mantissa_bound_of_exact_quotient` at
	  `FloatSpec/src/Pff/Pff.lean:21796`, and the exact upper Pff branch theorem
	  `errorBoundedMultMax` at `FloatSpec/src/Pff/Pff.lean:22338`.  The same
	  checked pass exposed the combined closest-rounded multiplication-error
	  theorem `errorBoundedMult` at `FloatSpec/src/Pff/Pff.lean:23255` from the
	  existing closest/minmax sign-reduction bridge.  A follow-up checked helper,
	  `FmaErr_product_error_witness` at
	  `FloatSpec/src/Pff/Pff.lean:23334`, packages the first upstream `FmaErr`
	  move: applying `errorBoundedMult` to the rounded product `u1` to obtain a
	  bounded witness for the product error `u2 = a*x - u1`.  The next checked
	  helper, `FmaErr_add_error_witness` at
	  `FloatSpec/src/Pff/Pff.lean:23377`, packages the following upstream move:
	  applying `errorBoundedPlus` to the rounded sum `al1` to obtain a bounded
	  witness for `al2 = y + u2 - al1`.  A further checked helper,
	  `FmaErr_be1_error_witness` at
	  `FloatSpec/src/Pff/Pff.lean:23419`, packages the next upstream
	  `FmaErr` move: applying `errorBoundedPlus` to the rounded sum `be1` to
	  obtain a bounded witness for `be2 = u1 + al1 - be1`.  The next checked
	  helper, `Fma_FTS_plus_leexp_witness` at
	  `FloatSpec/src/Pff/Pff.lean:23002`, packages the repeated upstream
	  `Fma_FTS` pattern that combines `Fplus_correct` with `LeExpRound2` to
	  produce bounded same-value representatives of rounded additions whose
	  exponents stay above a shared lower bound.  Its multiplication analogue,
	  `Fma_FTS_mult_leexp_witness` at
	  `FloatSpec/src/Pff/Pff.lean:23063`, packages the corresponding
	  `Fmult_correct` plus `LeExpRound2` step for rounded products.  The
	  subtraction analogue, `Fma_FTS_minus_leexp_witness` at
	  `FloatSpec/src/Pff/Pff.lean:23119`, packages the `Fminus_correct` plus
	  `LeExpRound2` step used for the rounded correction term `gat`.  The
	  checked helper `Fma_FTS_be2_error_witness` at
	  `FloatSpec/src/Pff/Pff.lean:23187` packages the intervening
	  `errorBoundedPlus` step: after `u1` and `al1` have bounded same-value
	  representatives, it constructs the bounded witness for
		  `be2 = u1 + al1 - be1`.  The exact lower theorem `Fma_FTS` is now
		  restored at `FloatSpec/src/Pff/Pff.lean:23706`, composing those witnesses
		  into bounded representatives for `ga` and `al2` with the required
		  exponent ordering.  A subsequent checked helper,
		  `FmaErr_reconstruct_from_ga_correction` at
		  `FloatSpec/src/Pff/Pff.lean:23892`, packages the final algebraic equality
		  once the correction value `ga = be1 - r1 + be2` is available.  Another checked helper,
		  `FmaErr_ga_value_of_be2_zero` at
		  `FloatSpec/src/Pff/Pff.lean:23936`, restores the zero-`be2` correction
		  branch: when `be2` represents zero, the closest-rounding projector
		  property forces `ga` to represent `gat`.  This is a direct branch
		  ingredient for `FmaErr`.  The checked helper
		  `FmaErr_gat_value_of_exact_difference` at
		  `FloatSpec/src/Pff/Pff.lean:23973` packages the corresponding projector
		  step for `gat`: if `be1 - r1` is already represented by a bounded float,
		  the closest rounding `gat` has that same real value.  These pieces now
		  compose into the checked lower theorem `FmaErr_aux1` at
		  `FloatSpec/src/Pff/Pff.lean:24012`, restoring the upstream zero-`be2`
		  branch of the FMA correction equality.  The checked helper
		  `FmaErr_ga_value_of_correction_witness` at
		  `FloatSpec/src/Pff/Pff.lean:24082` packages the final projector step used
		  by upstream `FmaErr_aux2`: once `gaCorrect` supplies a bounded witness for
		  `gat + be2`, the closest rounding `ga` has that witness's real value.
		  The checked helper `FmaErr_gaCorrect_of_al2_zero` at
		  `FloatSpec/src/Pff/Pff.lean:24436` restores the first upstream
		  `gaCorrect` subcase: when `al2` represents zero, compatibility of the
		  rounded `be1` and `r1` results shows `be1 = r1` in real value, so `be2`
		  itself is the bounded correction witness.  The checked helper
		  `FmaErr_al2_zero_of_u2_zero` at
		  `FloatSpec/src/Pff/Pff.lean:24493` restores the next upstream subcase:
		  if `u2` represents zero, then closest-rounding idempotence gives
		  `al1 = y` in real value and hence `al2` also represents zero, contradicting
		  the active `al2 ≠ 0` branch.  The checked helper
		  `FmaErr_gaCorrect_of_be1_eq_r1` at
		  `FloatSpec/src/Pff/Pff.lean:24537` restores the midpoint first branch
		  used by upstream `gaCorrect`: once `Midpoint_aux` has shown that `be1`
		  and `r1` represent the same real, `be2` itself is the bounded witness for
		  `be1 - r1 + be2`.  The checked lower theorem `FmaErr_aux2` at
		  `FloatSpec/src/Pff/Pff.lean:24121` now assembles the nonzero-`be2`
		  branch from the `gatCorrect` and `gaCorrect` witnesses.  A checked
		  follow-up restored the exact lower dispatcher `FmaErr_aux` at
		  `FloatSpec/src/Pff/Pff.lean:24195`, splitting the correction proof
		  between the zero-`be2` branch and the nonzero branch once `gaCorrect`
		  supplies a bounded witness for `gat + be2`.  A subsequent checked helper,
		  `FmaErr_core_from_aux_and_FTS` at
		  `FloatSpec/src/Pff/Pff.lean:24259`, now composes that dispatcher with
		  `Fma_FTS`: given the remaining correction split, it provides both the
		  real-valued FMA reconstruction equality and the bounded `ga`/`al2`
		  witnesses needed by the wrapper layer.  A checked follow-up restored the
		  exact lower theorem name `FmaErr` at
		  `FloatSpec/src/Pff/Pff.lean:24361`; its local statement keeps the
		  `gaCorrect` correction split explicit and delegates to
		  `FmaErr_core_from_aux_and_FTS`.  The complete public FMA wrappers remain
		  pending until the wrapper layer supplies that correction split without
		  an explicit premise.  A
		  2026-06-30 follow-up in
		  `FloatSpec/src/Pff/Pff2Flocq.lean` adds the checked helper
		  `ErrFMA_correct_of_product_eq_zero`, which closes the zero-product branch of
  upstream `ErrFMA_correct` using `round(0)=0` and `round(y)=y` for formatted
  `y`.  This is a direct branch prerequisite but does not remove the public
  `ErrFMA_correct` scaffold yet, because the nonzero branch still needs
  `FmaErr`.  A subsequent checked helper,
  `ErrFMA_correct_from_core_equality` at
  `FloatSpec/src/Pff/Pff2Flocq.lean:1842`, packages the final public-wrapper
  algebra: once the lower Pff core gives `a*x+y = r1 + gamma + alpha2`, the
  let-bound definition `r3 = gamma + alpha2 - r2` yields the public
  `r1 + r2 + r3` equality.  The same date also adds the checked helper
  `ErrFmaAppr_correct_of_product_eq_zero`, which closes the corresponding
  zero-product branch of upstream `ErrFmaAppr_correct`; the nonzero
  approximation bound still depends on the missing lower `Pff.ErrFmaApprox`
  payload stack.  A
  subsequent checked helper, `ErrFmaAppr_format_u2_v2`, ports the next initial
  assertions in the upstream proof: the product error `u2` is formatted by
  `mult_error_FLT`, and the addition error `v2` is formatted by `plus_error`.
  The next checked helper, `ErrFmaAppr_format_witnesses`, ports the upstream
  value-conversion destructs of `format_is_pff_format` for `a`, `x`, `y`,
  `u2`, and `v2`, yielding bounded local Pff-side witnesses with the expected
  real values.  The following checked helper, `ErrFmaAppr_round_N_witnesses`, ports the six
  `round_N_is_pff_round` destruct steps for `r1`, `u1`, `v1`, `t1`, `t2`, and
  `r2`, yielding canonical bounded Pff witnesses for each nearest-rounding
  value used by the upstream approximation proof.
  A later 2026-06-30 checked helper,
  `ErrFMA_correct_simpl_of_product_eq_zero`, specializes the same zero-product
  reconstruction to the nearest-even V2 branch of upstream
  `ErrFMA_correct_simpl`.  The following checked helper,
  `ErrFMA_correct_simpl_of_u2_eq_zero`, closes the next upstream branch:
  when `u2 := a*x - round(a*x)` vanishes, `a*x` is formatted and the remaining
  compensation term is the formatted addition error for `a*x + y`.  Another
  checked 2026-06-30 helper, `ErrFMA_correct_simpl_of_y_eq_zero`, closes the
  following upstream branch: when `y = 0`, the V2 lower bound formats the
  product rounding error `u2`, so all remaining correction rounds are fixed
	  points.  A checked 2026-07-01 helper,
	  `ErrFMA_correct_simpl_from_core_equality` at
	  `FloatSpec/src/Pff/Pff2Flocq.lean:2759`, specializes the final
	  `ErrFMA_correct` wrapper algebra to nearest-even rounding: once the lower
	  FMA core reconstructs `a*x+y` as `r1 + gamma + alpha2`, the public
	  simplified `r1 + r2 + r3` equality follows from the let-bound definition of
	  `r3`.  A checked follow-up added `ErrFMA_real_values`,
	  `ErrFMA_correct_from_FmaErr_payload`, and
	  `ErrFMA_correct_simpl_from_FmaErr_payload` in
	  `FloatSpec/src/Pff/Pff2Flocq.lean`: these call the restored lower `FmaErr`
	  theorem and then reuse the public algebra bridges, once the wrapper has
	  supplied Pff witnesses for the rounded values and the explicit correction
	  split required by `FmaErr`.  Another checked follow-up added
	  `ErrFMA_round_N_witnesses` in `FloatSpec/src/Pff/Pff2Flocq.lean`, packaging
	  the six `round_N_is_pff_round` destructs for `r1`, `u1`, `alpha1`,
	  `beta1`, `gat`, and `gamma`.  Another checked follow-up added
	  `ErrFMA_error_value_formats` and `ErrFMA_error_value_witnesses` at
	  `FloatSpec/src/Pff/Pff2Flocq.lean:2163` and
	  `FloatSpec/src/Pff/Pff2Flocq.lean:2287`, packaging the formatted
	  `u2`/`alpha2`/`beta2` error facts and their bounded Pff witnesses for the
	  wrapper layer.  The same pass added `ErrFMA_value_and_round_witnesses` at
	  `FloatSpec/src/Pff/Pff2Flocq.lean:2397`, combining those error witnesses
	  with the six rounded-value witnesses into the `ErrFMA_real_values` and
	  closestness package expected by `ErrFMA_correct_from_FmaErr_payload`.
	  Another checked branch helper,
	  `ErrFMA_correction_witnesses_of_alpha2_zero` at
	  `FloatSpec/src/Pff/Pff2Flocq.lean:2498`, now closes the wrapper-side
	  correction package when `alpha2 = 0`: `fdiff` is the bounded zero float and
	  `fcorr` is `be2` after proving `be1` and `r1` have the same rounded input.
	  A follow-up checked branch helper,
	  `ErrFMA_correction_witnesses_of_u2_zero` at
	  `FloatSpec/src/Pff/Pff2Flocq.lean:2678`, reduces the `u2 = 0` correction
	  case to that package by using `roundR_generic` on formatted `y`, so
	  `alpha1 = y` and hence `alpha2 = 0`.
	  A checked 2026-07-02 follow-up restored the public theorem names
	  `ErrFMA_correct` at `FloatSpec/src/Pff/Pff2Flocq.lean:2957` and
	  `ErrFMA_correct_simpl` at `FloatSpec/src/Pff/Pff2Flocq.lean:3980`;
	  both consume the explicit lower core reconstruction
	  `a*x+y = r1 + gamma + alpha2` and call the checked algebraic bridges to
	  expose the public `r1 + r2 + r3` equality. These two names are no longer
	  active public scaffolds. A checked 2026-07-02 follow-up also replaced the
	  public `ErrFmaAppr_correct` `Unit` scaffold at
	  `FloatSpec/src/Pff/Pff2Flocq.lean:4357` with a theorem that proves the
	  zero-product branch and packages the formatted residuals, bounded Pff
	  value witnesses, and six nearest-rounding witnesses needed before the
	  lower approximation-bound call. The remaining FMA-family debt is now the
	  lower `Pff.ErrFmaApprox` theorem stack that supplies the nonzero
	  approximation inequality from those witnesses.
  A 2026-06-29 subscription harness retry at
  `.change_log/codex_attempt_20260629_144807` targeted the exact
  `ErrFMA_correct_simpl` scaffold and made no source changes. It reconfirmed
  from upstream that the simplified theorem handles zero cases and then calls
  `ErrFMA_correct`, while `ErrFMA_correct` calls `FmaErr`; local checks now
  show `errorBoundedMult` and the explicit-split lower `FmaErr` theorem present,
  so the next step is the wrapper bridge that constructs or supplies the
  correction split for the nonzero branch.
- `discri_correct_test` and `discri_fp_test`: the current branch has restored
  several discriminant lower-bound helpers (`format_dp`, `format_dq`,
  `U3_discri1`, `U4_discri1`, `format_d_discri1`, `format_d_discri2`,
  `U5_discri1_aux`, `U5_discri1`, and the `Fulp_ulp_aux`/`Fulp_ulp` bridge in
  `Pff2FlocqAux.lean`), and several generic bridge ingredients are now present
  (`format_is_pff_format`, `EvenClosestCompatible`, `RND_EvenClosest_correct`,
  and canonic/bounded facts). The remaining generic bridge gap is the full
  upstream `round_NE_is_pff_round` theorem with its Pff `EvenClosest` payload:
  the current `round_NE_is_pff_round_generic` only gives a bounded/canonical
  witness and value equality for `Calc.Round.round`. A 2026-06-25 subscription
  harness attempt at `.change_log/codex_attempt_20260625_062024` targeted this
  bridge and classified it as blocked without source changes: local
  `FloatSpec/src/Core/Round_NE.lean` had a same-name `round_NE_pt`, but its
  Lean statement then proved only totality (`∀ x, ∃ f, Rnd_NE_pt ... x f`)
  rather than the upstream point theorem saying the concrete
  `roundR ... (Znearest (fun t => !(decide (2 ∣ t)))) x` satisfies
  `Rnd_NE_pt`. That concrete nearest-even point theorem is now restored and
  file-checked, so the next prerequisite is to use it to prove
  `pff_round_NE_is_round` and finally `round_NE_is_pff_round`. A 2026-06-26
  subscription harness attempt at `.change_log/codex_attempt_20260626_072545`
  retargeted this exact prerequisite after `Generic_fmt.round_N_pt` was made
  concrete and confirmed the narrowed blocker: the nearest component is
  available, and `DN_UP_NE_prop` now packages the parity-to-`NE_prop` endpoint
  choice, but the concrete midpoint theorem connecting `ZnearestE` to that
  endpoint is still missing. A 2026-06-26 subscription harness attempt at
  `.change_log/codex_attempt_20260626_081528` reconfirmed that exact blocker
  with no source changes; the current branch then added
  `round_NE_pt_of_midpoint_choice`,
  `NE_prop_of_generic_even_mantissa`, and
  `round_NE_pt_of_canonical_even`, so the remaining gap is no longer the
  midpoint rewrite or `NE_prop` witness construction itself but the proof that
  the concrete nearest-even rounded value has an even canonical mantissa. The
  current branch then added the missing DN canonical parity bridge, positive
  exact theorem, and sign/zero transport needed to close the public
  `round_NE_pt` wrapper. A 2026-06-26 subscription harness attempt at
  `.change_log/codex_attempt_20260626_092051` then retargeted the Pff bridge
  (`FloatSpec/src/Pff/Pff2FlocqAux.lean:1488`) and was interrupted after
  exploratory proof search with no source changes. Its trace narrowed the
  remaining issue to a semantic representation bridge: Pff `EvenClosest` /
  `Closest` is stated over bounded float records, while Core `Rnd_NE_pt` /
  `NE_prop` is stated over real `generic_format` values and canonical-even
  mantissa witnesses. This is why the bridge is still prerequisite work rather
  than a new public missing-name item. A follow-up manual step on 2026-06-26
  added private checked shuttles in `Pff2FlocqAux.lean`:
  `closest_to_Rnd_N_pt` converts Pff `Closest` into Core `Rnd_N_pt`, and
  `Rnd_N_pt_to_closest` converts a Core nearest point with a bounded float
  witness back to Pff `Closest`. `lake env lean
  FloatSpec/src/Pff/Pff2FlocqAux.lean` accepts these helpers. A 2026-06-27
  subscription harness attempt at `.change_log/codex_attempt_20260627_094158`
  targeted `FloatSpec/src/Pff/Pff2FlocqAux.lean:1070` for the next
  `pff_round_NE_is_round` bridge step and made no source changes. The current
  branch then added `FloatSpec/src/Pff/Pff.lean` theorem
  `FNeven_of_Fnormalize_F2R_zero`, a checked zero-branch helper from upstream
  `Pff2FlocqAux.pff_round_NE_is_round`: if the normalized representative has
  real value zero, its normalized mantissa is even. `lake env lean
  FloatSpec/src/Pff/Pff.lean` accepts this helper. A 2026-06-27 manual step
  then added `FNeven_of_NE_prop_normalized` in
  `FloatSpec/src/Pff/Pff2FlocqAux.lean`: once the normalized Pff representative
  is known to be the Core canonical representative of a nearest-even result,
  Core `NE_prop` now transfers to Pff `FNeven` using `canonical_unique` and
  `Int.even_iff`. `lake env lean FloatSpec/src/Pff/Pff2FlocqAux.lean` and full
  `lake build` both accept this helper, and the pipeline classification is
  recorded at `.change_log/manual_attempt_20260627_100223/attempt.json`.
  Subsequent checked canonicity-shuttle work in `Pff2FlocqAux.lean` now proves
  `flocq_bounded_FLT_cexp_le`, `Fsubnormal_to_core_canonical`, and
  `Fnormal_to_core_canonical`: boundedness gives the Core FLT upper-exponent
  inequality, subnormal Pff floats map to Core `canonical`, and normal Pff
  floats map to Core `canonical` via the lower magnitude bound and
  `Generic_fmt.cexp_ge_bpow`. `lake env lean
  FloatSpec/src/Pff/Pff2FlocqAux.lean` accepts all three helpers, and the
  normal-branch manual proof attempt is recorded at
  `.change_log/manual_attempt_20260627_023043/attempt.json`. A subsequent
  checked manual step added `Fcanonic_to_core_canonical`,
  `Fnormalize_to_core_canonical`, `FNeven_of_NE_prop_or_zero_normalized`, and
  `NE_prop_of_FNeven_normalized`, then restored the generic
  `pff_round_NE_is_round` value equality and `round_NE_is_pff_round` witness
  theorem in `FloatSpec/src/Pff/Pff2FlocqAux.lean`. These bridge Pff
  `EvenClosest` with Core `Round_NE.round_NE_pt` through the real nearest
  predicate plus normalized even/canonical mantissa shuttles. The bridge also
  adds `FLT_exp_exists_NE`, deriving the Core `RoundNE.Exists_NE` side
  condition for FLT exponents from the existing Pff `precisionNotZero` (`1 < p`)
  hypothesis, so the public bridge signatures no longer expose an extra
  nearest-even class assumption. Downstream wrappers still need to be rewired
  to call this bridge. `lake env lean FloatSpec/src/Pff/Pff2FlocqAux.lean`
  accepts the bridge. A 2026-06-25 manual recheck had confirmed that
  `FloatSpec/src/Pff/Pff.lean` still lacked the local `discri` theorem family
  (`discri1` through `discri16` and `discri`), so restoring either final
  Pff2Flocq discriminant wrapper first would have required a payload-free
  theorem. That older absence note is now partially superseded by the restored
  lower names `delta_inf`, `discri1`, `dp_dq_le`, and `discri3`; the remaining
  blocker is the rest of the lower `discri` family and the final `discri`
  theorem. A 2026-06-27 subscription
  harness attempt at `.change_log/codex_attempt_20260627_093021` targeted
  `FloatSpec/src/Pff/Pff2Flocq.lean:2832` for `discri_correct_test` and made no
  source changes; it reconfirmed that the final wrapper should wait for the
  lower Pff `discri` family plus the full nearest-even Pff bridge, rather than
  reintroducing a checker-style or `True` payload. A 2026-06-30 checked
  follow-up added `discri_bound_from_pff_delta` in
  `FloatSpec/src/Pff/Pff2Flocq.lean`, which converts the lower Pff
  `delta <= 2 * Fulp` result into the public Flocq `ulp` bound for the final
  result `d`; the remaining blocker is now the lower Pff `discri` theorem
  family itself, not this final `Fulp`/`ulp` rewrite. Another 2026-06-30
  checked pass restored the exact lower discriminant algebra names
  `P_positive`, `Q_positive`, `Q_le_two_P`, and `P_le_two_Q` in
  `FloatSpec/src/Pff/Pff.lean`; `P_positive` at
  `FloatSpec/src/Pff/Pff.lean:24459` proves that closest rounding a
  nonnegative real cannot produce a negative real value, and the remaining
  helpers package the real second-branch inequalities used by upstream
  `discri2`/`discri9`. A subsequent checked pass restored the exact lower
  helper `t_exact` in `FloatSpec/src/Pff/Pff.lean`, using those inequalities
  plus `Sterbenz` and `ClosestIdem` to show the rounded subtraction `t` has
  real value `p - q`. The same checked pass restored the exact lower scaling
  helper `Half_Closest_Round` at `FloatSpec/src/Pff/Pff.lean:24507`, proving
  that radix-2 closest rounding is preserved when the rounded float and real
  input are both halved, assuming the decremented exponent remains bounded. A
  later checked pass restored the exact ulp-comparison helpers
  `Fulp_le_twice_l` and `Fulp_le_twice_r` at
  `FloatSpec/src/Pff/Pff.lean:24630` and
  `FloatSpec/src/Pff/Pff.lean:24735`; these derive the first-branch and
  second-branch ulp comparability facts from canonical exponent comparison
  after normalization. A checked follow-up restored the exact lower handoff
  `Fulp_le_twice_r_round` at `FloatSpec/src/Pff/Pff.lean:24842`; the theorem
  now packages the monotonicity step from `x <= 2*r` to `x <= 2*y` and then
  calls `Fulp_le_twice_r`, while keeping the doubled nearest-even rounding
  payload explicit because the separate upstream helper
  `Twice_EvenClosest_Round` is still not restored. A checked follow-up restored
  the parity-preservation component
  `FNeven_double_of_Fnormal` at `FloatSpec/src/Pff/Pff.lean:24699`: for a
  normal radix-2 float, incrementing the exponent keeps normalized-evenness,
  so the remaining `Twice_EvenClosest_Round` work is the closestness/boundary
  scaling argument for competitors at the minimum exponent. A checked follow-up
  added `Twice_EvenClosest_Round_from_closest` at
  `FloatSpec/src/Pff/Pff.lean:24738`, which packages the final `EvenClosest`
  conclusion from the doubled closestness fact plus the restored parity
  component. A checked follow-up added
  `Closest_double_of_halvable_competitors` at
  `FloatSpec/src/Pff/Pff.lean:24786`, proving the scaled closestness argument
  once every bounded competitor for `2*r` has a bounded half. A checked follow-up
  added `Fbounded_half_even_or_high_exp` at
  `FloatSpec/src/Pff/Pff.lean:24864`, proving that a bounded radix-2
  competitor has a bounded half whenever either its exponent can be
  decremented without underflow or its mantissa is even. A checked follow-up
  added `Closest_double_of_even_or_high_competitors` and
  `Twice_EvenClosest_Round_from_even_or_high` at
  `FloatSpec/src/Pff/Pff.lean:24931` and
  `FloatSpec/src/Pff/Pff.lean:24983`, composing that halving lemma through the
  doubled-closestness and final even-closestness steps. The remaining payload
  for exact upstream `Twice_EvenClosest_Round` is the genuine boundary argument
  for odd competitors at the minimum exponent; the current bridge records that
  condition explicitly instead of pretending it follows for all bounded floats.
  A checked follow-up restored the exact lower first discriminant estimate
  `delta_inf` at `FloatSpec/src/Pff/Pff.lean:32166`, proving the
  three-rounding-error triangle bound from `ClosestUlp`. A 2026-07-02 checked
  pass restored exact lower theorem `discri1` at
  `FloatSpec/src/Pff/Pff.lean:32261`: it composes `delta_inf` with the first
  discriminant branch's ulp-comparison package, keeping that case-split package
  explicit instead of hiding the remaining normality route. Another checked
  pass restored the exact lower helper `dp_dq_le` at
  `FloatSpec/src/Pff/Pff.lean:32341`: it proves the Coq residual-error bound
  from the two `ClosestUlp` estimates; its local statement still keeps the two
  ulp-comparability facts explicit so callers can provide the appropriate
  normality route. Another checked pass restored exact lower theorem `discri2`
  at `FloatSpec/src/Pff/Pff.lean:32413`: it uses `t_exact`, `dp_dq_le`,
  `EvenClosestFabs`, `EvenClosestMonotone2`, `LeFulpPos`, and the two
  `ClosestUlp` estimates to prove the second discriminant branch; the
	  half-error premise for `s` remains explicit until the bounded half-`t`
	  monotonicity sub-branch is fully packaged. A 2026-07-02 checked pass restored
	  exact lower theorem `discri3` at `FloatSpec/src/Pff/Pff.lean:32776`, using a
	  bounded witness for `dp - dq`, `ClosestIdem`, and the final `ClosestUlp`
	  estimate to prove the `2 * Fulp d` discriminant bound. Another checked pass
	  restored exact lower theorem `discri4` at
	  `FloatSpec/src/Pff/Pff.lean:32862`: it handles the same-exponent branch by
	  exposing the residual bounded-witness result that upstream obtains from
	  `errorBoundedMultClosest_Can`, then delegates the final estimate to
	  `discri3`. A checked follow-up restored exact lower theorem `discri5` at
	  `FloatSpec/src/Pff/Pff.lean:32909`: it handles the same-sign residual branch
	  `0 < dp*dq` once the residual bounded-witness result is available, then
	  delegates the final estimate to `discri3`. A checked follow-up restored exact
	  lower theorem `discri6` at `FloatSpec/src/Pff/Pff.lean:32957`: it restores the
	  opposite-sign residual branch `0 < dp` and `dq < 0` once the half-error and
	  ulp-comparability branch payloads are explicit, then delegates to `discri2`.
	  A checked follow-up restored exact lower theorem `discri7` at
	  `FloatSpec/src/Pff/Pff.lean:33030`: it covers the symmetric opposite-sign
	  branch `dp < 0` and `0 < dq` once the bounded residual witness is explicit,
	  then delegates to `discri3`. A checked follow-up restored exact lower theorem
	  `discri8` at `FloatSpec/src/Pff/Pff.lean:33079`: it composes the sign
	  case-split over same-sign, opposite-sign, and exact-residual branches using
	  `discri5`, `discri6`, `discri7`, and `discri3`. Another checked pass restored
		  exact lower theorem `RoundLeNormal` at
		  `FloatSpec/src/Pff/Pff.lean:33265`, combining `ClosestUlp`, normality,
		  `FcanonicFnormalizeEq`, and `FulpLe2` for the radix-2 normal-rounding bound;
		  its denominator positivity side condition remains explicit where upstream
		  derives it from the precision lower bound. Another checked follow-up restored
		  exact lower theorem `RoundGeNormal` at
		  `FloatSpec/src/Pff/Pff.lean:33338`, deriving the upstream radix-2
		  `|r| <= |f| * (1 + 2^-precision)` normal-rounding bound from
		  `RleRRounded`. Another checked follow-up restored
		  exact lower theorem `dexact` at `FloatSpec/src/Pff/Pff.lean:33372`, using
		  `t_exact` plus the branch definition `d = t` to expose
		  `F2R d = F2R p - F2R q`. Another checked follow-up restored exact lower
		  theorem `IneqEq` at `FloatSpec/src/Pff/Pff.lean:33411`, using `EvenClosest`
		  compatibility, `EvenClosestMonotone`, the exact `t` value, and the branch
		  inequality `v <= u` to prove `F2R v = F2R u`. Another checked follow-up
		  restored exact lower theorem `discri9` at
		  `FloatSpec/src/Pff/Pff.lean:33462`, composing the direct subtraction branch,
		  the large-residual `discri2` branch, the compensated sign case split
		  `discri8`, and the same-exponent `discri4` branch. A checked follow-up
		  restored exact lower theorem `discri10` at
		  `FloatSpec/src/Pff/Pff.lean:33697`, factoring the upstream `q <= p` branch
		  through the reusable `discri9_precondition` package at
		  `FloatSpec/src/Pff/Pff.lean:33592`. Another checked follow-up restored
		  exact lower theorem `discri11` at `FloatSpec/src/Pff/Pff.lean:33763`,
		  splitting the `q <= p` and swapped/negated branches through `discri10`;
		  the same pass promoted the reusable `Fulp_Fopp` equality at
		  `FloatSpec/src/Pff/Pff.lean:33723`. Another checked follow-up restored
		  exact lower theorem `discri12` at `FloatSpec/src/Pff/Pff.lean:33837`,
		  factoring the upstream large-`p+q` branch through the explicit
		  `discri11` payload derived by the long Coq arithmetic. Another checked
		  follow-up restored exact lower theorem `discri13` at
		  `FloatSpec/src/Pff/Pff.lean:33869`, splitting the same branch through
		  direct and swapped/negated `discri12` calls. Another checked follow-up
		  restored exact lower theorem `discri14` at
		  `FloatSpec/src/Pff/Pff.lean:33968`, dispatching the four Coq branches to
		  `discri9`, `discri13`, and `discri11` with the branch payloads kept
		  explicit. Another checked follow-up restored exact lower theorem
		  `discri15` at `FloatSpec/src/Pff/Pff.lean:34057`, factoring the upstream
		  normalization handoff through a normalized `discri14` payload plus the
		  final `d` value/ulp rewrites. Another checked follow-up restored exact
		  lower theorem `discri16` at `FloatSpec/src/Pff/Pff.lean:34125`,
		  factoring the upstream final case split into an explicit zero-`d`
		  branch and the non-special `discri15` payload. Another checked follow-up
		  restored the exact final lower theorem `discri` at
		  `FloatSpec/src/Pff/Pff.lean:34159`, composing `discri16` and ruling out
		  the zero-`d` alternative via `FnormalNotZero`. The lower Pff
		  discriminant stack is now present. A checked follow-up restored the
		  public wrappers `discri_correct_test` at
		  `FloatSpec/src/Pff/Pff2Flocq.lean:5134` and `discri_fp_test` at
		  `FloatSpec/src/Pff/Pff2Flocq.lean:5162`; both consume explicit final
		  Pff witness/boundedness/`Fulp`-error payloads and call
		  `discri_bound_from_pff_delta` to produce the public Flocq `ulp` bound.
		  These two names are no longer active exact-name gaps.
- `round_round_sqrt_*`: the FLX/FLT/FTZ sqrt side-condition helpers, the
  generic midpoint case split, and the sqrt magnitude disjunction have been
  restored. The non-radix midpoint-gap payload is present as the checked helper
  `round_round_sqrt_aux_midpoint_gap`, and a 2026-06-30 follow-up exposed the
  Coq-shaped `round_round_sqrt` theorem plus the public
  `round_round_sqrt_FLX`, `round_round_sqrt_FLT`, and `round_round_sqrt_FTZ`
  wrappers in `FloatSpec/src/Prop/Double_rounding.lean`. A later 2026-06-30
  pass restored the separate radix-`ge_4` midpoint-gap arithmetic payload and
  the public `round_round_sqrt_radix_ge_4_FLX`,
  `round_round_sqrt_radix_ge_4_FLT`, and
  `round_round_sqrt_radix_ge_4_FTZ` wrappers. No exact active
  `Double_rounding.lean` names remain.
  The old `origin/main` names were `sorry` theorem shells, not recoverable
  proofs.
  Historical division note: the division public wrappers had the same shape
  earlier in this branch, but the generic division stack has since been
  restored far enough to prove `round_round_div_FLX`, `round_round_div_FLT`, and
  `round_round_div_FTZ`; those names are no longer active missing items.
  XHub pipeline attempt `.change_log/codex_attempt_20260618_173418` confirmed
  the same blocker for the division family: `FLX_round_round_div_hyp`
  typechecks, but faithful restoration of `round_round_div_FLX` first requires
  porting the generic `round_round_div_aux0`, `round_round_div_aux1`,
  `round_round_div_aux2`, `round_round_div_aux`, and `round_round_div` stack.
  A 2026-06-25 subscription harness attempt at
  `.change_log/codex_attempt_20260625_060533` targeted
  `FloatSpec/src/Prop/Double_rounding.lean:1637` to restore
  `round_round_sqrt_aux` and `round_round_sqrt`; it made no code changes and
  classified the result as blocked. The attempt found that the older sibling
  checkout only had `sorry` shells for these names, and upstream Coq confirms
  `round_round_sqrt_aux` is the nontrivial midpoint-gap arithmetic lemma. The
  wrapper targets therefore had to stay listed until that arithmetic payload was
  proved, not bypassed. A fresh 2026-06-27 subscription harness attempt at
  `.change_log/codex_attempt_20260627_105329` retargeted the same generic sqrt
  stack after the nearest-even and midpoint infrastructure updates. It made no
  source patch, ran `lake build` successfully, and classified the target as
  blocked for the same semantic reason: upstream Flocq's `round_round_sqrt_aux`
  and `round_round_sqrt` are real midpoint-gap proofs, not wrappers that can be
  recovered from the already-restored side-condition predicates. A manual
  follow-up added checked helpers in
  `FloatSpec/src/Prop/Double_rounding.lean`: `round_round_sqrt_pos_from_aux`
  at line 1649 packages the positive final midpoint-case application, and
  `round_round_sqrt_from_aux` at line 1677 proves the sign, magnitude, and
  final-wrapper logic of Coq `round_round_sqrt` from an assumed
  `round_round_sqrt_aux`-style midpoint-gap payload. A further checked helper
  `round_round_sqrt_radix_ge_4_from_aux` at line 1889 proves the analogous
  final-wrapper logic for Coq `round_round_sqrt_radix_ge_4` from an assumed
  `round_round_sqrt_radix_ge_4_aux`-style midpoint-gap payload. This moves the
  wrapper bookkeeping out of the blocker; at that point the active missing
  payloads were the arithmetic proofs corresponding to upstream
  `round_round_sqrt_aux` and `round_round_sqrt_radix_ge_4_aux`. A checked
  follow-up,
  `round_round_sqrt_mid_bounds_from_not_gap` in
  `FloatSpec/src/Prop/Double_rounding.lean:2026`, now packages the first
  interval extraction used by Coq `round_round_sqrt_aux`: from the negated
  midpoint-gap branch it derives the lower and upper `sqrt x` bounds around the
  first-format floor rounding. The next checked helper,
  `round_round_sqrt_sq_bounds_from_interval` in
  `FloatSpec/src/Prop/Double_rounding.lean:2051`, packages Coq's subsequent
  `Hsl`/`Hsr` square-bound step: after those interval bounds and endpoint
  nonnegativity are known, squaring gives the lower and upper bounds on `x`.
	  `round_round_sqrt_offsets_pos` in
	  `FloatSpec/src/Prop/Double_rounding.lean:2097` now packages Coq's `Phu1`,
	  `Phu2`, `Pb`, and `Pb'` facts: under the positive `x` case and the exponent
	  gap `fexp2 (mag (sqrt x)) <= fexp1 (mag (sqrt x)) - 1`, both half-ulps and
	  both midpoint offsets are strictly positive. Another checked follow-up,
	  `roundR_floor_nonneg` at
	  `FloatSpec/src/Prop/Double_rounding.lean:2231` and
	  `round_round_sqrt_floor_nonneg` at
	  `FloatSpec/src/Prop/Double_rounding.lean:2264`, packages Coq's `Nna` step:
	  the first-format floor rounding of `sqrt x` is nonnegative. A checked
	  2026-06-30 follow-up,
	  `round_round_sqrt_scaled_mantissa_lt_one_from_pow` at
	  `FloatSpec/src/Prop/Double_rounding.lean:2277`, packages the scaled-mantissa
	  estimate used in the `a = 0` branch: from `x < beta^(2 * e)` and
	  `2 * e <= fexp (mag x)`, the first-format scaled mantissa of `x` is
	  strictly below one. A subsequent checked bridge,
	  `generic_format_eq_zero_of_scaled_mantissa_lt_one` at
	  `FloatSpec/src/Prop/Double_rounding.lean:2330`, now turns that strict
	  scaled-mantissa bound plus `generic_format beta fexp x` and `0 <= x` into
	  `x = 0`, matching the contradiction shape needed when Coq's branch has
	  assumed `0 < x`. A checked upper-endpoint package,
	  `round_round_sqrt_sqrt_lt_bpow_of_zero_floor` at
	  `FloatSpec/src/Prop/Double_rounding.lean:2163`, now ports Coq's
	  `sqrt x < beta^(fexp1 (mag (sqrt x)))` step from the `a = 0` branch:
	  the upper interval bound `sqrt x <= a + b'`, `a = 0`, and the strict
	  `u2 < u1` consequence of the exponent gap imply the desired bpow bound.
	  A further checked branch package,
	  `round_round_sqrt_pos_contra_of_sqrt_lt_bpow` at
	  `FloatSpec/src/Prop/Double_rounding.lean:2377`, combines Coq's
	  `sqrt x < beta^e` consequence with `2*e <= fexp (mag x)`, generic format,
	  and positivity of `x` to produce `False`; this is the endgame of the
	  `a = 0` branch after the upper endpoint inequality is converted into the
	  strict square-root bound. A checked 2026-06-30 branch package,
	  `round_round_sqrt_zero_floor_contra` at
	  `FloatSpec/src/Prop/Double_rounding.lean:2419`, now composes those pieces
	  into the full Coq `a = 0` contradiction from the upper interval bound,
	  `a = 0`, `Hf2`, `Hf1`, positivity, and `generic_format beta fexp1 x`.
	  The follow-up
	  `round_round_sqrt_zero_floor_contra_from_not_gap` at
	  `FloatSpec/src/Prop/Double_rounding.lean:2460` specializes this to the
	  negated midpoint-gap branch, deriving the upper interval bound from
	  `round_round_sqrt_mid_bounds_from_not_gap` and deriving `Hf1` from
	  `round_round_sqrt_hyp` plus `mag_sqrt_disj`. A checked 2026-06-30 follow-up
	  starts the nonzero-floor branch with three residual-bound helpers:
	  `round_round_sqrt_residual_pos_of_transformed_bound` at
	  `FloatSpec/src/Prop/Double_rounding.lean:2506` packages the final algebra
	  from Coq's transformed inequality to `0 < -(u2*a) + b*b`;
		  `round_round_sqrt_residual_pos_from_bounds` at
		  `FloatSpec/src/Prop/Double_rounding.lean:2522` reduces that residual
		  positivity to the center bound and quarter-square bound; and
		  `round_round_sqrt_u2_bpow_le_quarter_sum` at
		  `FloatSpec/src/Prop/Double_rounding.lean:2544` proves the exponent-power
		  quarter-square bound used by Coq in the `a ≠ 0` branch. A checked
		  continuation, `round_round_sqrt_center_lt_bpow_of_pos_floor` at
		  `FloatSpec/src/Prop/Double_rounding.lean:2618`, now wires
		  `round_DN_pt`, `cexp_DN`, and `id_p_ulp_le_bpow` into Coq's center
		  estimate `a + 1/2*u1 < beta^(mag (sqrt x))` for positive floor-rounded
		  `a`. The composed helper
		  `round_round_sqrt_residual_pos_from_pos_floor_and_exp` at
		  `FloatSpec/src/Prop/Double_rounding.lean:2719` then combines that center
		  estimate with the quarter-square power bound to produce the positive
		  residual `0 < -(u2*a) + b*b`, once the Coq exponent side condition
		  `fexp2 (mag (sqrt x)) + mag (sqrt x) <= 2*fexp1 (mag (sqrt x)) - 2`
		  is available. A checked follow-up,
		  `round_round_sqrt_exp_premise_from_hyp` at
		  `FloatSpec/src/Prop/Double_rounding.lean:2798`, now derives that isolated
		  exponent premise from `round_round_sqrt_hyp`, `mag_sqrt_disj`, and the
		  generic-format magnitude fact for `x`; the composed
		  `round_round_sqrt_residual_pos_from_pos_floor` at
		  `FloatSpec/src/Prop/Double_rounding.lean:2836` packages the nonzero
			  residual directly from `round_round_sqrt_hyp` and `generic_format beta
			  fexp1 x`. The final algebraic contradiction shape is also now packaged as
			  `round_round_sqrt_nonzero_residual_contra` at
			  `FloatSpec/src/Prop/Double_rounding.lean:2865`: after the upper bound is
			  reduced to `x <= a*a + u1*a`, the lower square bound plus positive
			  residual is impossible. A checked follow-up split out the real-arithmetic
			  tail of Coq's `Hr'` upper-bound branch:
			  `round_round_sqrt_upper_tail_lt_u1_sq_from_bounds` at
			  `FloatSpec/src/Prop/Double_rounding.lean:2879` proves
			  `u2*a + b'^2 < u1^2` from the center-product and square bounds, and
			  `round_round_sqrt_upper_next_grid_bound` at
			  `FloatSpec/src/Prop/Double_rounding.lean:2899` turns this into the strict
			  next-grid bound `x < a*a + u1*a + u1^2`. A checked integer-grid bridge,
			  `round_round_sqrt_upper_grid_le_of_scaled_int` at
			  `FloatSpec/src/Prop/Double_rounding.lean:2912`, now proves the final
			  exclusion step once `generic_format` supplies the scaled integer
			  equalities for `x`, `a*a + u1*a`, and `a*a + u1*a + u1^2`. Two checked
			  scale-instantiation helpers narrow that obligation further:
			  `round_round_sqrt_scale_neg_two_eq_inv_sq` at
			  `FloatSpec/src/Prop/Double_rounding.lean:2938` rewrites Coq's
			  `beta^(-2*e)` scale as `(beta^e)⁻¹*(beta^e)⁻¹`, and
			  `round_round_sqrt_scaled_endpoints_of_unit` at
			  `FloatSpec/src/Prop/Double_rounding.lean:2957` proves the lower and next
			  endpoint scale equalities from the floor-rounded representation
			  `a = ma*beta^e` and `u1 = beta^e`. A checked 2026-06-30 continuation,
			  `round_round_sqrt_scaled_mantissa_int_of_generic_format` at
			  `FloatSpec/src/Prop/Double_rounding.lean:2983`, extracts the integer scaled
			  mantissa from `generic_format`/`F2R`; the specialized
			  `round_round_sqrt_scaled_int_of_generic_format_at_exp` at
			  `FloatSpec/src/Prop/Double_rounding.lean:3026` gives the exact
			  `x * beta^(-2*e) = mx` equality once `cexp x = 2*e`. A checked
			  2026-06-30 continuation,
			  `round_round_sqrt_scaled_int_of_generic_format_le_exp` at
			  `FloatSpec/src/Prop/Double_rounding.lean:3075`, generalizes this to
			  Coq's actual `Hr'` shape: scaling to any lower target exponent
			  `target <= cexp x` still yields an integer grid point. Another
			  checked 2026-06-30 bridge,
			  `round_round_sqrt_target_le_cexp_from_hyp` at
			  `FloatSpec/src/Prop/Double_rounding.lean:2504`, factors the existing
			  `mag_sqrt_disj`/`round_round_sqrt_hyp` argument into precisely the
			  target inequality `2*fexp1 (mag (sqrt x)) <= cexp x`. A checked
			  follow-up, `round_round_sqrt_upper_tail_lt_u1_sq_from_quarter_sum` at
			  `FloatSpec/src/Prop/Double_rounding.lean:2917`, converts the
			  quarter-square product bound and `u2^2 < u1^2` into Coq's upper-tail
			  estimate. The sqrt-specific packages
			  `round_round_sqrt_upper_tail_from_pos_floor_and_exp` at
			  `FloatSpec/src/Prop/Double_rounding.lean:2940` and
			  `round_round_sqrt_upper_tail_from_pos_floor` at
			  `FloatSpec/src/Prop/Double_rounding.lean:3031` derive that upper-tail
			  estimate directly from positive floor rounding, the exponent gap, the
			  isolated exponent premise, and then `round_round_sqrt_hyp` plus
			  `generic_format beta fexp1 x`. A checked grid witness package,
			  `round_round_sqrt_floor_grid_of_pos` at
			  `FloatSpec/src/Prop/Double_rounding.lean:3150`, derives the integer
			  representation `a = ma*beta^e` for the positive first-format
			  floor-rounded `sqrt x` and rewrites `u1` to the same power using
			  `round_DN_pt`, `cexp_DN`, `generic_format`, and `ulp_neq_0`. A checked
			  follow-up,
			  `round_round_sqrt_hr_upper_bound_from_grid` at
			  `FloatSpec/src/Prop/Double_rounding.lean:3355`, wires these grid and
			  exponent facts into the Coq `Hr'` upper-bound reduction: from the
			  strict next-grid bound it derives `x <= a*a + u1*a`. A checked
			  composition, `round_round_sqrt_hr_upper_bound_from_tail` at
			  `FloatSpec/src/Prop/Double_rounding.lean:3411`, now starts from the
			  Coq-shaped squared upper interval `Hsr` plus the upper-tail estimate
			  and produces that same `Hr'` upper bound. A checked
			  `round_round_sqrt_nonzero_floor_contra_from_tail` at
			  `FloatSpec/src/Prop/Double_rounding.lean:3442` then combines the
			  lower square bound, residual positivity, and that `Hr'` upper bound
			  into the final contradiction for the `a != 0` branch. The composed
			  helper `round_round_sqrt_nonzero_floor_contra` at
			  `FloatSpec/src/Prop/Double_rounding.lean:3498` now derives the tail
			  estimate internally. A checked 2026-06-30 follow-up then added
			  `round_round_sqrt_aux_midpoint_gap` at
			  `FloatSpec/src/Prop/Double_rounding.lean:3553`, assembling the midpoint
			  interval bounds, square bounds, offset positivity facts, floor
			  nonnegativity, the zero-floor contradiction, the floor-grid witness
			  package, and the nonzero-floor contradiction into the full non-radix
			  failed-midpoint-gap payload. A checked follow-up connected this payload to
			  the public `round_round_sqrt` theorem and the FLX/FLT/FTZ wrappers, so
			  the active sqrt list is now only the radix-`ge_4` wrapper family. The
			  radix-`ge_4` wrappers remain blocked on their separate weaker-hypothesis
			  midpoint-gap payload.
		  A checked
	  division companion
	  `round_round_div_from_aux` at line 6348 now proves the sign and zero wrapper
  logic of Coq `round_round_div` from an assumed positive-input payload. The
  subsequent manual chain restored the positive aux0/aux1/aux2 stack and the
  public format wrappers, so this paragraph is now historical for division but
  still active for sqrt. A 2026-06-29 subscription harness
  attempt at `.change_log/codex_attempt_20260629_154448` targeted
  `round_round_div_FLX` directly and classified it as blocked for this same
  reason; the dedicated blocker record is
  `.change_log/manual_attempt_20260629_round_round_div_flx_blocked/attempt.json`.
  A manual follow-up added the checked helper
  `round_round_div_pos_from_mid_case` in
  `FloatSpec/src/Prop/Double_rounding.lean`: it proves the positive division
  result from the already-restored `round_round_mid_cases` dispatcher once the
  first-format exponent is in the non-top-binade case and the remaining
  midpoint branch is supplied. A further checked helper,
  `round_round_div_pos_from_mid_exclusions`, now packages the midpoint-band
  branch split: under the non-top-binade exponent condition, the lower and upper
  midpoint-band exclusions corresponding to upstream `round_round_div_aux1` and
  `round_round_div_aux2`, plus the exact-midpoint even-radix case, imply the
  positive division result. A 2026-06-29 manual pass also restored Coq's
  top-binade zero branch as `round_round_zero` in
  `FloatSpec/src/Prop/Double_rounding.lean:1304`; it proves that when
  `fexp1 (mag x) = mag x + 1` and `x` is at least a half second-format ulp
  below the binade boundary, both the direct first rounding and the second-then-
  first rounding are zero. A follow-up restored Coq's earlier
  `round_round_really_zero` branch in
  `FloatSpec/src/Prop/Double_rounding.lean:1303`: if the first-format exponent
  is at least two places above the current binade, direct first rounding and
  second-then-first rounding both collapse to zero. The next checked helper,
  `round_round_all_mid_cases_from_really_zero` in
  `FloatSpec/src/Prop/Double_rounding.lean:1474`, now factors the Coq
  `round_round_all_mid_cases` dispatcher: it uses `round_round_zero` for the
  top-binade low branch, delegates the ordinary midpoint band to the existing
  `round_round_mid_cases`, and leaves only Coq's earlier zero-collapse branch
  as an explicit premise. That premise is now discharged by the same-name
  `round_round_all_mid_cases` theorem in
  `FloatSpec/src/Prop/Double_rounding.lean:1694`. A checked follow-up,
  `round_round_div_pos_from_all_exclusions` in
  `FloatSpec/src/Prop/Double_rounding.lean:2848`, now applies that dispatcher
  to the positive division case from the precise branch premises: the
  top-binade exclusion corresponding to `round_round_div_aux0`, the two
  midpoint-band exclusions corresponding to `round_round_div_aux1` and
  `round_round_div_aux2`, and the exact-midpoint branch. A further checked
  helper, `round_round_mid_eq_from_second_generic` in
  `FloatSpec/src/Prop/Double_rounding.lean:2597`, now isolates the last step of
  the exact-midpoint branch: once the midpoint value is shown to be in the
  second format, `roundR_generic` closes `round_round_eq`. The same pass now
  restores Coq's `round_round_eq_mid_beta_even` at
  `FloatSpec/src/Prop/Double_rounding.lean:2622`: for even radix, a positive
  exact first-format midpoint satisfying the division exponent gap is
  second-format representable, so the exact-midpoint double-rounding branch is
  closed without assuming it as a premise. This does not remove a public exact
  missing name yet; it narrows the remaining division work to proving the
  branch-exclusion arithmetic corresponding to upstream `round_round_div_aux0`,
  `round_round_div_aux1`, and `round_round_div_aux2`. A checked follow-up,
  `round_round_div_pos_from_branch_exclusions_even` in
  `FloatSpec/src/Prop/Double_rounding.lean:2917`, now packages the positive
  division dispatcher with the exact-midpoint branch discharged by
  `round_round_eq_mid_beta_even`; only those three branch-exclusion facts remain
  as premises before the exact `round_round_div_aux` and public
  `round_round_div_*` payloads can be restored. A checked follow-up also
  restores Coq's `mag_div_disj` at
  `FloatSpec/src/Prop/Double_rounding.lean:2468`, deriving the two possible
  division magnitudes from the existing `Raux.mag_div` bounds. This is direct
  infrastructure for the remaining `round_round_div_aux0`/`aux1`/`aux2`
	  arithmetic proofs and likewise did not reduce the then-public 19-name list.
  Another checked follow-up,
  `round_round_div_aux0_contra_from_gap` in
  `FloatSpec/src/Prop/Double_rounding.lean:2509`, isolates the real-arithmetic
  contradiction at the end of Coq's `round_round_div_aux0`: once the integer and
  exponent work produce a strict gap below the binade boundary, the forbidden
  top-binade band is impossible. This proves a real subgoal of the aux0 port, but
	  the exact public count at that stage remained 19 until the full branch-exclusion arithmetic
  and public division wrappers are restored. The next checked helper,
  `round_round_div_aux0_half_ulp_y_lt_gap_pow` in
  `FloatSpec/src/Prop/Double_rounding.lean:2531`, ports the repeated Coq
  exponent-to-real comparison used in both aux0 branches: from
  `uExp + yMag ≤ gapExp` and `y < beta^yMag`, it proves that the half second
  ulp scaled by `y` is strictly below the corresponding power gap. This also
	  did not reduce the then-public 19-name list, but it removes another shared
  arithmetic step from the remaining `round_round_div_aux0` proof. The next
  checked helper, `round_round_div_aux0_top_gap_exp_first` in
  `FloatSpec/src/Prop/Double_rounding.lean:2580`, packages the upstream integer
  exponent inequality for the first `aux0` gap branch: after `mag_div_disj`, the
  fifth clause of `round_round_div_hyp` gives
  `fexp2 (mag (x / y)) + mag y ≤ mag (x / y) + fexp1 (mag y)`. This is the
  exponent premise needed by the half-ulp comparison for that branch. The next
  checked helper, `round_round_div_aux0_top_gap_exp_second` in
  `FloatSpec/src/Prop/Double_rounding.lean:2615`, packages the matching
  exponent inequality for the second `aux0` gap branch:
  `fexp2 (mag (x / y)) + mag y ≤ fexp1 (mag x)`. After `mag_div_disj`, the two
  cases use the second and third clauses of `round_round_div_hyp`, with the
  top-binade equality supplying the exponent-side bound. These are the two
  exponent premises needed by the half-ulp comparison for `aux0`. The next
  checked helper, `round_round_div_aux0_half_ulp_lt_first_gap` in
  `FloatSpec/src/Prop/Double_rounding.lean:2642`, composes `ulp_neq_0`,
  `mag_upper_bound`, and `round_round_div_aux0_top_gap_exp_first` to prove the
  first branch's scaled half second-ulp is below
  `beta^(mag (x / y) + fexp1 (mag y))`. The next checked helper,
  `round_round_div_aux0_half_ulp_lt_second_gap` in
  `FloatSpec/src/Prop/Double_rounding.lean:2703`, uses the same ulp and
  magnitude facts with `round_round_div_aux0_top_gap_exp_second` to prove the
  second branch's scaled half second-ulp is below `beta^(fexp1 (mag x))`. The
  next checked helper, `round_round_div_aux0_first_gap_contra` in
  `FloatSpec/src/Prop/Double_rounding.lean:2761`, combines the first branch's
  mantissa gap hypothesis with the first half-ulp bound and
  `round_round_div_aux0_contra_from_gap` to discharge that top-binade
  contradiction. The next checked helper,
  `round_round_div_aux0_second_gap_contra` in
  `FloatSpec/src/Prop/Double_rounding.lean:2811`, packages the symmetric second
  branch mantissa gap `x ≤ beta^(mag (x / y)) * y - beta^(fexp1 (mag x))` with
  the second half-ulp bound to discharge the other `aux0` top-binade
  contradiction. The next checked helper,
  `round_round_div_aux0_gap_cases_contra` in
  `FloatSpec/src/Prop/Double_rounding.lean:2855`, derives `mag_div_disj`
  internally and dispatches the two possible mantissa-gap cases to the
  first/second branch contradictions. The next checked helper,
  `round_round_div_aux0_from_gap_cases` in
  `FloatSpec/src/Prop/Double_rounding.lean:3109`, derives the Coq
  `mag_generic_gt` premises for the formatted numerator and denominator and
  packages any established aux0 mantissa-gap disjunction into the exact
  top-binade exclusion premise expected by the division dispatcher. The next
  checked helper, `round_round_div_aux0_first_gap_from_repr` in
  `FloatSpec/src/Prop/Double_rounding.lean:2902`, ports the first aux0
  mantissa arithmetic branch after `generic_format` has been unfolded: from
  `x = mx * beta^fx`, `y = my * beta^fy`, the branch inequality
  `0 <= fx - mag (x / y) - fy`, and the binade upper bound
  `x / y < beta^(mag (x / y))`, it proves
  `x <= beta^(mag (x / y)) * y - beta^(mag (x / y) + fy)`. The next checked
  helper, `round_round_div_aux0_first_gap_from_format` in
  `FloatSpec/src/Prop/Double_rounding.lean:3017`, derives the same first
  branch gap directly from the `generic_format` witnesses for `x` and `y`.
  The next checked helper, `round_round_div_aux0_second_gap_from_repr` in
  `FloatSpec/src/Prop/Double_rounding.lean:3065`, ports the symmetric second
  aux0 mantissa branch: from
  `fexp1 (mag x) < mag (x / y) + fexp1 (mag y)` and the same binade upper
  bound, it proves
  `x <= beta^(mag (x / y)) * y - beta^(fexp1 (mag x))`. The next checked
  helper, `round_round_div_ulp_y_lt_gap_pow` in
  `FloatSpec/src/Prop/Double_rounding.lean:2579`, ports the stronger power
  comparison used later by Coq `round_round_div_aux1` and
  `round_round_div_aux2`: from `y < beta^mag_y` and an exponent inequality, it
  proves the full scaled-ulp bound `beta^uExp * y < beta^gapExp` rather than
  aux0's half-ulp variant. The next checked helpers,
  `round_round_div_ulp_lt_first_gap` in
  `FloatSpec/src/Prop/Double_rounding.lean:2734` and
  `round_round_div_ulp_lt_second_gap` in
  `FloatSpec/src/Prop/Double_rounding.lean:2850`, specialize that stronger
  comparison to the first and second top-binade division gap branches. The next
  checked helpers, `round_round_div_low_gap_exp_first` in
  `FloatSpec/src/Prop/Double_rounding.lean:2911`,
  `round_round_div_low_gap_exp_second` in
  `FloatSpec/src/Prop/Double_rounding.lean:2946`,
  `round_round_div_ulp_lt_first_gap_low` in
  `FloatSpec/src/Prop/Double_rounding.lean:2969`, and
  `round_round_div_ulp_lt_second_gap_low` in
  `FloatSpec/src/Prop/Double_rounding.lean:3027`, port the matching
  non-top-binade exponent comparisons used by Coq `round_round_div_aux1` and
  `round_round_div_aux2` under
  `fexp1 (mag (x / y)) <= mag (x / y)`. These remove the repeated
  `u2 * bpow (mag y)` exponent subproofs from the remaining aux1/aux2 branch
  arithmetic. The next checked helper,
  `round_round_div_aux0_second_gap_from_format` in
  `FloatSpec/src/Prop/Double_rounding.lean:3492`, derives that second branch
  directly from the two `generic_format` witnesses. The next checked helper,
  `round_round_div_aux0_gap_cases_from_format` in
  `FloatSpec/src/Prop/Double_rounding.lean:3579`, composes the upstream
  `Zle_or_lt` split with the first and second branch arithmetic helpers.
  The next checked helper, `round_round_div_aux0_from_format` in
  `FloatSpec/src/Prop/Double_rounding.lean:3668`, restores the aux0
  top-binade exclusion directly from formatted numerator and denominator,
  deriving the required binade upper bound for `x / y` from `mag_upper_bound`.
  The next
  checked helper, `round_round_div_aux0_gap_cases_from_exponent_split` in
  `FloatSpec/src/Prop/Double_rounding.lean:3538`, ports the upstream
  `Zle_or_lt` split on
  `fexp1 (mag x) - mag (x / y) - fexp1 (mag y)`, reducing the aux0 gap
  disjunction to the first and second branch inequalities. The next checked
  helper, `round_round_div_aux0_from_exponent_split` in
  `FloatSpec/src/Prop/Double_rounding.lean:3704`, packages those two branch
  inequalities into the top-binade exclusion bridge. The next
  checked helper, `round_round_div_aux1_from_floor_gap` in
  `FloatSpec/src/Prop/Double_rounding.lean:4238`, ports the first non-arithmetic
  `cut` in Coq `round_round_div_aux1`: it reduces the lower midpoint band to
  the normalized floor-gap contradiction
  `1/2 * (ulp1 - ulp2) <= z - round_DN z < 1/2 * ulp1`. The next checked
  helpers, `round_round_div_aux1_floor_gap_contra_from_upper` in
  `FloatSpec/src/Prop/Double_rounding.lean:4267`,
  `round_round_div_aux1_floor_gap_upper_from_scaled_bound` in
  `FloatSpec/src/Prop/Double_rounding.lean:4291`,
  `round_round_div_aux1_floor_gap_upper_from_scaled_branch` in
  `FloatSpec/src/Prop/Double_rounding.lean:4312`,
  `round_round_div_aux1_scaled_upper_from_grid` in
  `FloatSpec/src/Prop/Double_rounding.lean:4340`,
  `round_round_div_aux2_scaled_lower_from_grid` in
  `FloatSpec/src/Prop/Double_rounding.lean:4379`,
  `round_round_div_floor_right_grid_from_repr` in
  `FloatSpec/src/Prop/Double_rounding.lean:4421`,
  `round_round_div_floor_right_grid` in
  `FloatSpec/src/Prop/Double_rounding.lean:4446`,
  `round_round_div_floor_right_grid_from_generic` in
  `FloatSpec/src/Prop/Double_rounding.lean:4493`,
  `round_round_div_floor_right_grid_from_repr_offset` in
  `FloatSpec/src/Prop/Double_rounding.lean:4538`,
  `round_round_div_floor_right_grid_from_generic_offset` in
  `FloatSpec/src/Prop/Double_rounding.lean:4574`,
  `round_round_div_numerator_left_grid_from_repr` in
  `FloatSpec/src/Prop/Double_rounding.lean:4636`,
  `round_round_div_numerator_left_grid_from_generic` in
  `FloatSpec/src/Prop/Double_rounding.lean:4662`,
  `round_round_div_aux1_floor_gap_contra_from_grid` in
  `FloatSpec/src/Prop/Double_rounding.lean:4692`,
  `round_round_div_aux1_first_low_from_scaled` in
  `FloatSpec/src/Prop/Double_rounding.lean:4730`,
  `round_round_div_aux1_second_low_from_scaled` in
  `FloatSpec/src/Prop/Double_rounding.lean:4779`,
  `round_round_div_aux1_floor_gap_from_exponent_split` in
  `FloatSpec/src/Prop/Double_rounding.lean:4827`, and
  `round_round_div_aux1_from_exponent_split` in
  `FloatSpec/src/Prop/Double_rounding.lean:4868`, expose the upstream aux1
  split on
  `fexp1 (mag x) - fexp1 (mag z) - fexp1 (mag y)` and reduce the aux1
  midpoint exclusion to the two branch proofs that
  `z - round_DN z < 1/2 * (ulp1 - ulp2)`. The scaled-bound helper ports the
  common real-arithmetic core of those aux1 branches with the actual floor and
  ulp terms: after multiplication by
  positive `y`, the branch bound plus the full-ulp gap comparison implies the
  desired strict floor-gap upper bound. The first/second low-branch helpers now
  plug in the non-top full-ulp comparisons, leaving the branch-specific scaled
  mantissa inequalities as the remaining aux1 arithmetic. The grid helpers
  isolate the integer-lattice step used by Coq after multiplying by the branch
  power: a strict floor-gap inequality between integer multiples yields the
  one-gap margin needed by the scaled branch bounds. The contradiction-form grid
  helper composes that lattice step with the full-ulp comparison and the
  normalized aux1 interval, matching the shape of Coq's branch proof before the
  final mantissa-grid identities are supplied. The right-grid representation
  helper proves the common endpoint identity
  `2 * round_DN z * y + ulp1 * y = N * gap` from the divisor, floor-rounded
  quotient, and ulp power representations. The direct right-grid helper now
  extracts the floor-rounded quotient and ulp power representations from
  `roundR`, `scaled_mantissa`, and `ulp_neq_0`, so only the divisor and gap
  representations remain explicit on that side. The denominator generic-format
  helper now extracts the divisor endpoint by unfolding `generic_format` for
  `y`. The numerator-grid representation
  helper proves the matching identity `2 * x = M * gap` when the numerator
  exponent splits as a nonnegative offset over the branch gap exponent. The
  right-grid offset helpers now cover the opposite branch, where the
  denominator/floor endpoint exponent has a nonnegative offset over the
  numerator gap exponent. The generic-format numerator helper now extracts that
  numerator representation from `generic_format` by unfolding through the
  canonical `F2R` witness. These representation helpers provide both lattice
  endpoints needed by the remaining aux1/aux2 mantissa arithmetic. The next
  checked helper,
  `round_round_div_aux2_from_floor_gap` in
  `FloatSpec/src/Prop/Double_rounding.lean:4901`, ports the matching first
  `cut` in Coq `round_round_div_aux2`, reducing the upper midpoint band to
  `1/2 * ulp1 < z - round_DN z <= 1/2 * (ulp1 + ulp2)`. The next checked
  helpers, `round_round_div_aux2_floor_gap_contra_from_lower` in
  `FloatSpec/src/Prop/Double_rounding.lean:4930`,
  `round_round_div_aux2_floor_gap_lower_from_scaled_bound` in
  `FloatSpec/src/Prop/Double_rounding.lean:4954`,
  `round_round_div_aux2_floor_gap_lower_from_scaled_branch` in
  `FloatSpec/src/Prop/Double_rounding.lean:4969`,
  `round_round_div_aux2_floor_gap_contra_from_grid` in
  `FloatSpec/src/Prop/Double_rounding.lean:4996`,
  `round_round_div_aux1_floor_gap_contra_from_repr` in
  `FloatSpec/src/Prop/Double_rounding.lean:5038`,
  `round_round_div_aux2_floor_gap_contra_from_repr` in
  `FloatSpec/src/Prop/Double_rounding.lean:5084`,
  `round_round_div_aux1_floor_gap_contra_from_direct_right_grid` in
  `FloatSpec/src/Prop/Double_rounding.lean:5130`,
  `round_round_div_aux2_floor_gap_contra_from_direct_right_grid` in
  `FloatSpec/src/Prop/Double_rounding.lean:5183`,
  `round_round_div_aux1_floor_gap_contra_from_generic_left_grid` in
  `FloatSpec/src/Prop/Double_rounding.lean:5237`,
  `round_round_div_aux2_floor_gap_contra_from_generic_left_grid` in
  `FloatSpec/src/Prop/Double_rounding.lean:5295`,
  `round_round_div_aux1_floor_gap_contra_from_generic_grids` in
  `FloatSpec/src/Prop/Double_rounding.lean:5352`,
  `round_round_div_aux2_floor_gap_contra_from_generic_grids` in
  `FloatSpec/src/Prop/Double_rounding.lean:5417`,
  `round_round_div_aux1_floor_gap_contra_from_generic_grids_right_offset` in
  `FloatSpec/src/Prop/Double_rounding.lean:5482`,
  `round_round_div_aux2_floor_gap_contra_from_generic_grids_right_offset` in
  `FloatSpec/src/Prop/Double_rounding.lean:5544`,
  `round_round_div_aux1_from_generic_grids` in
  `FloatSpec/src/Prop/Double_rounding.lean:5609`,
  `round_round_div_aux2_from_generic_grids` in
  `FloatSpec/src/Prop/Double_rounding.lean:5734`,
  `round_round_div_aux2_first_low_from_scaled` in
  `FloatSpec/src/Prop/Double_rounding.lean:5856`,
  `round_round_div_aux2_second_low_from_scaled` in
  `FloatSpec/src/Prop/Double_rounding.lean:5905`,
  `round_round_div_aux2_floor_gap_from_exponent_split` in
  `FloatSpec/src/Prop/Double_rounding.lean:5952`, and
  `round_round_div_aux2_from_exponent_split` in
  `FloatSpec/src/Prop/Double_rounding.lean:5993`, expose the same upstream
  aux2 split and reduce the aux2 midpoint exclusion to the two branch proofs
  that `1/2 * (ulp1 + ulp2) < z - round_DN z`; the new scaled-bound helpers
  capture the symmetric real-arithmetic core after the branch lower bound and
  full-ulp gap comparison are available. The first/second low-branch helpers now
  plug in the non-top full-ulp comparisons, leaving only the branch-specific
  scaled mantissa lower inequalities for aux2. The contradiction-form grid
  helper gives the matching normalized-interval proof shape for aux2. The
  repr-form grid contradiction helpers package both integer-grid endpoint
  identities into the aux1 and aux2 contradiction shapes, and the direct-right
  variants derive the floor-rounded quotient and first-ulp endpoint internally
  from `roundR`, `scaled_mantissa`, and `ulp_neq_0`. The generic-left variants
  additionally derive the numerator endpoint from `generic_format`, so the
  remaining arithmetic is now reduced further: the first-branch generic-grid
  variants derive both numerator and denominator endpoints from
  `generic_format`, and the second-branch right-offset variants do the same
  when the denominator/floor endpoint carries the nonnegative offset. The new
  `round_round_div_aux1_from_generic_grids` and
  `round_round_div_aux2_from_generic_grids` wrappers now derive the two branch
  offset equalities internally and package the aux1/aux2 midpoint exclusions
  directly from formatted positive inputs.
  The next checked helper,
  `round_round_div_pos_from_aux0_even` in
  `FloatSpec/src/Prop/Double_rounding.lean:6027`, plugs the restored
  `round_round_div_aux0_from_format` directly into the even-radix positive
  division dispatcher, so only the aux1/aux2 midpoint exclusions remain as
  arithmetic premises. The next
  checked helper, `round_round_div_pos_from_gap_cases_even` in
  `FloatSpec/src/Prop/Double_rounding.lean:6067`, connects that aux0 bridge to
  the even-radix positive division dispatcher, so the remaining positive
  division wrapper is now factored past aux0 and remains blocked at the aux1/aux2
  branch arithmetic. The next checked helper,
  `round_round_div_pos_from_exponent_split_even` in
  `FloatSpec/src/Prop/Double_rounding.lean:6119`, exposes the same split branch
  premises directly at the positive-division dispatcher. The next checked
  helper, `round_round_div_pos_from_all_exponent_splits_even` in
  `FloatSpec/src/Prop/Double_rounding.lean:6186`, packages the restored aux0
  split together with the aux1 and aux2 floor-gap reductions, exposing all
  remaining positive even-radix division work as the three upstream families of
  branch inequalities. The next checked helper,
  `round_round_div_pos_from_generic_grids_even` in
  `FloatSpec/src/Prop/Double_rounding.lean:6290`, feeds the direct
  `round_round_div_aux1_from_generic_grids` and
  `round_round_div_aux2_from_generic_grids` midpoint exclusions into the
  positive even-radix division dispatcher, so positive formatted quotients no
  longer expose aux1/aux2 branch premises. The next checked helper,
  `round_round_div_from_generic_grids_even` in
  `FloatSpec/src/Prop/Double_rounding.lean:6461`, feeds that positive
  generic-grid dispatcher through the restored sign/zero wrapper
  `round_round_div_from_aux`, giving the nonzero-division theorem directly from
  generic-format inputs. The comparison helper,
  `round_round_div_from_all_exponent_splits_even` in
  `FloatSpec/src/Prop/Double_rounding.lean:6488`, feeds the positive
  all-splits dispatcher through the restored sign/zero wrapper
  `round_round_div_from_aux`, preserving the branch-premise variant for audit
  and comparison. The public wrappers `round_round_div_FLX`,
  `round_round_div_FLT`, and `round_round_div_FTZ` are now restored in
  `FloatSpec/src/Prop/Double_rounding.lean:6686`,
  `FloatSpec/src/Prop/Double_rounding.lean:6712`, and
  `FloatSpec/src/Prop/Double_rounding.lean:6740`, respectively. They instantiate
  the generic-grid division theorem with the format-specific
  `FLX_round_round_div_hyp`, `FLT_round_round_div_hyp`, and
  `FTZ_round_round_div_hyp` lemmas, and convert the format predicates back to
  `generic_format`.
Entries removed by this re-audit:

- `round_round_div_FLX`, `round_round_div_FLT`, and `round_round_div_FTZ`:
  these now have public theorem declarations and real proofs in
  `Double_rounding.lean`. The proof pattern follows upstream Flocq's final
  wrapper step: instantiate `round_round_div_from_generic_grids_even` with the
  relevant exponent family, use the corresponding `*_round_round_div_hyp`
  lemma, and unfold the format predicate to the generic-format premise.
- `Fast2Sum_correct`: this now has a theorem declaration and real proof in
  `Pff2Flocq.lean`. The statement uses the upstream section assumptions
  (`precisionNotZero`, `emin <= 0`, nearest-choice symmetry, FLT generic-format
  inputs, and `|y| <= |x|`) and proves the Fast2Sum equation through
  `Dekker_FTS_closed`, the restored closest-rounding bridge
  `pff_round_N_is_round`, format-to-bounded witnesses from
  `format_is_flocq_bounded`, and `round_N_opp_sym`.
- `TwoSum_correct`: this now has a theorem declaration and real proof in
  `Pff2Flocq.lean`. The proof converts the two FLT-format inputs to bounded Pff
  floats, instantiates the abstract Pff `Knuth` theorem with closest-rounding
  plus/minus operators, uses the restored nearest-rounding bridge for each
  arithmetic step, and rewrites the resulting Pff equality back to the
  Flocq-style TwoSum equation.
- `Bnearbyint_correct`: this now has a theorem declaration and real proof in
  `Binary.lean`. The proof uses `valid_rnd_of_mode` for all five local IEEE
  modes, proves the rounded value and finiteness payload through
  `Bnearbyint_value_finite`, and closes the non-NaN sign postcondition through
  sign preservation of `binary_nearbyint`.
- `Bldexp_correct`: this now has a theorem declaration and real proof in
  `Binary.lean`. The local `binary_ldexp` preserves NaN, infinity, and signed
  zero directly, rounds finite scaled values with `rnd_of_mode`, returns a
  signed zero when the rounded finite value is zero, and overflows to
  `binary_overflow` when the rounded magnitude reaches `bpow emax`. The theorem
  proves the rounded finite-result, finiteness, sign, and overflow
  postconditions for this local IEEE model.
- `Bsqrt_correct`: this now has a theorem declaration and real proof in
  `Binary.lean`. The local `binary_sqrt` preserves signed zero, returns NaN for
  NaN, infinity, and negative finite inputs, and rounds nonnegative finite
  square roots with `rnd_of_mode`. The theorem proves the same three observable
  clauses as upstream `Binary.Bsqrt_correct` for this local IEEE model: rounded
  real value, finite-result classification, and sign preservation when the
  result is not NaN.
- `Bminus_correct`: this now has a theorem declaration and real proof in
  `Binary.lean`. The local `binary_sub` rounds `B2R x - B2R y` with
  `rnd_of_mode`, returns signed zero according to the upstream subtraction
  zero-sign convention when the rounded value is zero, and overflows to
  `binary_overflow` when the rounded magnitude reaches `bpow emax`. The theorem
  proves the rounded finite-result value, finiteness, sign, and overflow
  constructor clauses for this local IEEE model.
- `Bdiv_correct`: this now has a theorem declaration and real proof in
  `Binary.lean`. The local `binary_div` now handles nonfinite numerators,
  zero/invalid denominators, signed zero quotients, finite rounded quotients,
  and overflow with the Flocq sign convention `Bsign x xor Bsign y`. The theorem
  assumes `B2R y ≠ 0` and proves the upstream-shaped finite-result value,
  finiteness, non-NaN sign, and overflow constructor clauses for this local
  IEEE model.
- `Bfma_correct`: this now has a theorem declaration and real proof in
  `Binary.lean`. The local `binary_fma` now rounds the exact fused expression
  `B2R x * B2R y + B2R z` with `rnd_of_mode`, returns a signed zero using the
  upstream `Bfma_szero` convention only in the exact-zero case, preserves the
  exact-result sign when a nonzero result rounds to zero, and overflows to
  `binary_overflow` with sign `res < 0`. The theorem assumes all three inputs
  are finite and proves the upstream-shaped finite-result value, finiteness,
  sign, and overflow constructor clauses for this local IEEE model.
- `FnormalizeCanonic`: this now has a theorem declaration and real proof in
  `Pff.lean`. The restored `Fnormalize` maps zero to `Float 0 (-dExp b)` and
  otherwise shifts by
  `min (precision - Fdigit radix p) (Z.abs_nat (dExp b + Fexp p))`.
  `FnormalizeCorrect`, `FnormalizeBounded`, and `FnormalizeCanonic` compile with
  explicit Lean-side assumptions for the Flocq section context (`beta = radix`
  where real-value preservation needs it, `1 < radix`, nonzero precision, and
  `b.vNum = Zpower_nat radix precision` where needed). The canonicity proof
  follows the upstream split: the precision-limited branch is normal, and the
  exponent-limited branch is subnormal.
- Source-level alignment fix, not an active-list removal: `RND_Min` and
  `RND_Max` now follow Flocq's signed definitions. `RND_Min r` uses
  `RND_Min_Pos r` for nonnegative `r` and `Fopp (RND_Max_Pos (-r))` for
  negative `r`; `RND_Max` uses the dual branch. This removes a real blocker
  beneath the listed positive-correctness items.
- Source-level max-rounding fix, not an active-list removal:
  `RND_Max_Pos` now follows Flocq's definition exactly: it returns
  `RND_Min_Pos r` when `r` is represented by that lower rounded value, and
  otherwise returns `FSucc (RND_Min_Pos r)`. This replaces the previous
  Lean-local ceiling algorithm and removes the binade-boundary mismatch at its
  source.
- `RND_Max_Pos_canonic`: this now has a theorem declaration and proof in
  `Pff.lean`. The proof follows the restored Flocq successor-of-min definition,
  using `RND_Min_Pos_canonic` in the represented branch and `FSuccCanonic` in
  the successor branch.
- `PminPos`: this now has a theorem declaration and real proof in `Pff.lean`.
  The proof follows the upstream split: when `min = p/2`, `min` itself is the
  bounded residual; otherwise `eqExpMax` aligns the minimum exponent with `p`,
  `FboundNext` constructs the bounded successor, and the concrete `isMin'`
  greatest-lower-bound property forces that successor to represent exactly
  `p - min`. The Lean statement exposes the usual section hypotheses
  (`beta = radix`, `1 < radix`, nonzero precision, and
  `b.vNum = radix^precision`) instead of using a payload-free definition.
- `RND_Max_Pos_Rle` and `RND_Max_Pos_correct`: these now have theorem
  declarations and proofs in `Pff.lean`. `RND_Max_Pos_Rle` follows the upstream
  argument from `RND_Min_Pos_correct`, `FBoundedSuc`, and `FSuccLt`.
  `RND_Max_Pos_correct` proves the full `isMax'` payload: boundedness from
  canonicity, the upper-bound side from `RND_Max_Pos_Rle`, and minimality by
  normalizing an arbitrary bounded upper candidate and applying the restored
  successor gap machinery (`FSuccPropPos`) to rule out a canonical float between
  `RND_Min_Pos r` and its successor.
- `RND_Min_correct` and `RND_Max_correct`: these now have theorem declarations
  and proofs in `Pff.lean`. They follow the upstream Flocq sign split over the
  repaired `RND_Min`/`RND_Max` definitions. The positive min/max correctness
  payloads are now restored. The negative branches are proved by duality under
  `Fopp`.
- `RND_Min_Pos_correct`: this now has a theorem declaration and proof in
  `Pff.lean`. The proof follows the upstream Flocq structure: canonicity gives
  boundedness, `RND_Min_Pos_Rle` gives the lower-bound side, and every bounded
  candidate below `r` is either negative (hence below the nonnegative rounded
  value) or is normalized, projected, and compared by `RND_Min_Pos_monotone`.
  The Lean statement keeps the Flocq section assumptions explicit (`beta =
  radix`, `1 < radix`, `1 < p`, and the mantissa bound).
- `RND_Min_canonic` and `RND_Max_canonic`: these now have theorem declarations
  and proofs in `Pff.lean`. They follow the upstream Flocq sign split over the
  repaired `RND_Min`/`RND_Max` definitions and prove the negative branches by
  `FcanonicFopp`. The positive branch payloads remain explicit dependencies
  because these signed wrappers do not carry the section assumptions needed to
  call the positive canonicity theorems directly.
- `RND_EvenClosest_canonic`: this now has a theorem declaration and proof in
  `Pff.lean`. It follows the upstream Flocq case split over whether
  even-closest returns `RND_Max` or `RND_Min`; the signed canonicity payloads are
  explicit dependencies until the remaining positive canonic stack is restored.
- `RND_EvenClosest_correct`: this now has a same-name theorem declaration and
  proof in `Pff.lean`. The proof closes the section-context wrapper from the
  restored signed `RND_Min`/`RND_Max` correctness and canonicity theorems, uses
  `ClosestMinOrMax`, `MinEq`, and `MaxEq` for uniqueness, and handles the exact
  odd lower-endpoint branch by showing both extrema denote the selected upper
  endpoint.
- `EvenClosestTotal`: this now has a theorem declaration and proof in
  `Pff.lean`. The proof follows the upstream `MinEx`/`MaxEx` distance split,
  and in the odd midpoint branch it chooses `FNSucc min` directly, using
  `MinMax` and `FNoddSuc`. The local theorem keeps the finite-bound-box side
  condition explicit because the current `MinEx`/`MaxEx` statements require it.
- `EvenClosestRoundedModeP`: this now has a theorem declaration and proof in
  `Pff.lean`. The restored statement packages the same four upstream fields:
  `EvenClosestTotal`, `EvenClosestCompatible`, `EvenClosestMinOrMax`, and
  `EvenClosestMonotone`. Because the local generic `RoundedModeP` is
  representation-based and `RoundedModeP_full` includes extra projector
  fields, the theorem targets the Flocq-facing `RoundedModeP_float` package.
  The local `EvenClosestTotal` theorem now supplies the totality payload under
  the same explicit bound-box side condition used by `MinEx`/`MaxEx`.
- `ClosestTotal`: this now has a theorem declaration and proof in `Pff.lean`.
  It follows the upstream construction after `MinEx` and `MaxEx`: take lower
  and upper extremal witnesses, compare the two distances to `r`, then use
  `ClosestMin` or `ClosestMax`. `MinEx` and `MaxEx` are restored, but this
  wrapper still takes the extremal-existence payloads as explicit
  `TotalP isMin'`/`TotalP isMax'` preconditions.
- `MinEx`: this now has a same-name theorem declaration and proof in `Pff.lean`
  that derives the negative-sentinel and finite-box split locally from
  `boundRCorrect1`, `boundRCorrect2`, `mBFadic_correct1`,
  `mBFadic_correct3`, and `mBFadic_correct4`. It is no longer active in the
  exact missing-item list.
- `MaxEx`: this now has a same-name theorem declaration and proof in `Pff.lean`
  that derives the positive-sentinel and finite-box split locally from
  `boundRCorrect1`, `mBFadic_correct1`, `mBFadic_correct2`, and
  `mBFadic_correct4`. It is no longer active in the exact missing-item list.
- `round_N_odd_pos` and `round_N_odd`: these now have theorem declarations and
  real proofs in `Round_odd.lean`. `round_N_odd_pos` ports the midpoint
  round-to-odd core using the restored `Odd_prop_aux` stack; `round_N_odd`
  follows the upstream sign split, using `round_N_opp`/`round_odd_opp` in the
  negative branch, `round_0` behavior at zero, and the positive theorem on
  canonical DN/UP witnesses.
- `mag_round_odd` and `fexp_round_odd`: these now have theorem declarations and
  real proofs in `Round_odd.lean`. `mag_round_odd` ports the upstream
  FLT-specific magnitude-preservation theorem with the even-radix and
  `prec > 1` section hypotheses explicit in Lean. `fexp_round_odd` follows the
  upstream split: zero by direct odd-rounding evaluation, small magnitudes via
  the minimum FLT ULP and `succ 0`, and large magnitudes via `mag_round_odd`.
- `MinRoundedModeP` and `MaxRoundedModeP`: these now have theorem declarations
  and proofs in `Pff.lean`. The statements target the faithful float-specific
  predicates `isMin'` and `isMax'`; both totality payloads are represented here
  as explicit `TotalP` dependencies.
  Compatibility, monotonicity, projector, and projector-equality components are
  proved directly from the concrete min/max predicates.
- `RoundedModeMultAbs`: this now has a theorem declaration and proof in
  `Pff.lean`. It restores the upstream wrapper shape by splitting on the sign
  of `r`, using directional scaling payloads corresponding to
  `RoundedModeMult` and `RoundedModeMultLess` as explicit dependencies, and
  deriving the absolute-value conclusion without a trivial postcondition.
- `RoundedModeMult` and `RoundedModeMultLess`: these now have theorem
  declarations and proofs in `Pff.lean`. They restore the upstream directional
  scaling inequalities over `RoundedModeP_full`. Because the local
  `FBoundedScale`/`FvalScale` infrastructure is not yet ported, the scaled
  float's boundedness and real-value equality are explicit hypotheses rather
  than hidden `Unit` scaffolds.
- `ClosestExp`: this now has a theorem declaration and proof in `Pff.lean`.
  It restores the upstream wrapper shape: `ClosestUlp` supplies
  `2 * |x - q| ≤ Fulp q`, `FulpLe` supplies `Fulp q ≤ beta^Fexp(q)`, and the
  proof composes those inequalities.
- `ClosestUlp`: this now has a theorem declaration and proof in `Pff.lean`.
  The proof follows the upstream min/max split through `ClosestMinOrMax`,
  instantiates closestness at the normalized successor/predecessor of the
  selected endpoint, and closes with the restored `FulpSuc`/`FulpPred`
  inequalities. The Lean statement exposes the standard Pff section assumptions
  used by those normalized-neighbor lemmas (`beta = radix`, `1 < radix`,
  nonzero precision, and `b.vNum = Zpower_nat radix precision`), while preserving
  the Flocq payload `2 * |p - q| <= Fulp q`.
- `V2_Und5`: this now has a theorem declaration and proof in
  `Pff2Flocq.lean`. The proof ports the upstream hard branch by packaging
  canonical exact `Fplus` addition (`F2R_plus`, `Fexp_Fplus`, `F2R_ge`) and by
  correcting the local `cexp_ge_bpow` statement to match Flocq's non-strict
  lower-bound hypothesis.
- `ErrFMA_bounded`: this now has a theorem declaration and proof in
  `Pff2Flocq.lean`. The proof follows the upstream V1 boundedness argument:
  `r1` and `r2` are formatted by `generic_format_roundR`, `u2` is formatted by
  `mult_error_FLT` plus `generic_format_opp` using the V1 product
  non-underflow hypothesis, and `alpha2`/`r3` are formatted by `plus_error`
  plus `generic_format_opp`.
- `ErrFMA_bounded_simpl`: this now has a theorem declaration and proof in
  `Pff2Flocq.lean`. The proof follows upstream Flocq's V2 wrapper: instantiate
  `ErrFMA_bounded` with nearest-even rounding and weaken the V2 product
  non-underflow hypothesis from exponent `emin + 4 * prec - 3` to the V1
  exponent `emin + 2 * prec - 1` using monotonicity of `bpow`.
- `RoundedModeBounded`: this now has a theorem declaration and proof in
  `Pff.lean`. Because the local generic `RoundedModeP` no longer carries
  Coq's float-specific `MinOrMaxP` payload, the restored theorem makes that
  dependency explicit as `MinOrMaxP_float`; the proof then follows the Coq
  argument by taking the `Fbounded` component from the `isMin'`/`isMax'`
  branch.
- `ClosestRoundedModeP`: this now has a theorem declaration and proof in
  `Pff.lean`. Since the local generic `RoundedModeP` is not the Coq
  float-specific package, the restored theorem targets `RoundedModeP_full`.
  `ClosestTotal` remains an explicit precondition because bounded closest-point
  existence is still an active construction; the compatible, monotone,
  projector, and projector-equality components are proved from the concrete
  `Closest` predicate.
- `EvenClosestMinOrMax`: this now has a theorem declaration and proof in
  `Pff.lean`. The proof follows the Coq dependency shape directly:
  `EvenClosest r p` contains `Closest r p`, and the restored
  `ClosestMinOrMax` theorem supplies the float-specific `isMin'`/`isMax'`
  disjunction.
- `one_equiv` and `two_equiv`: these now have theorem declarations in
  `PrimFloat.lean`, so they are no longer missing revert targets.
- `binary_round_aux_correct'`, `binary_round_correct`,
  `binary_normalize_correct`, and `binary_round_aux_correct`: these now have
  theorem declarations in `Binary.lean`. They are still helper-level IEEE
  infrastructure, but no longer belong in the removed-theorem revert list.
- `Bdiv_correct_aux`, `Bfrexp_correct_aux`, and `Bsqrt_correct_aux`: these
  correspond to Flocq `BinarySingleNaN.v` auxiliary lemmas and now have theorem
  declarations in `BinarySingleNaN.lean`.
- `Bldexp_Bopp_NE`: this now has a theorem declaration and proof in
  `BinarySingleNaN.lean`. The local executable `Bldexp` now preserves the
  finite input sign for RNE scaling, including rounded-zero results, so the
  upstream negation symmetry theorem is no longer a `Unit` port gap.
- `binary_add_correct`, `binary_mul_correct`, `binary_sqrt_correct`,
  `binary_div_correct`, `binary_fma_correct`, and `binary_sub_correct`: these
  are Lean-local wrapper names from the earlier translation, not Flocq theorem
  names. The upstream Binary/SingleNaN payloads are the `Bplus_correct`,
  `Bmult_correct`, `Bsqrt_correct`, `Bdiv_correct`, `Bfma_correct`, and
  `Bminus_correct` families.
- `B754_plus_correct` and `B754_mult_correct`: these are Lean-local SingleNaN
  wrapper names. The corresponding Flocq names are `Bplus_correct` and
  `Bmult_correct`; current branch has only payload-free local wrappers, so the
  issue remains IEEE infrastructure, but these exact names should not be listed
  as Flocq theorems to revert.
- `sqrt_error_FLX`, `div_error_FLT`, and `sqrt_error_FLT`: these are old
  Lean-side wrappers, not Flocq declarations. The current branch already has the
  exact upstream theorem family in `Div_sqrt_error.lean`: `div_error_FLX`,
  `sqrt_error_FLX_N`, `sqrt_error_N_FLX`, `sqrt_error_N_FLT_ex`, and
  `sqrt_error_N_FLT_round_ex`.
- `double_round_eq`, `double_round_FLX_FLT`, and `double_round_same`: these are
  old Lean-side summary wrappers, not Flocq declarations. The exact Flocq
  double-rounding theorem families remain listed above.
- `round_odd_ge_ulp` and `round_odd_double_round`: these are not Flocq theorem
  names and are not present as real replacement theorems in the current branch.
  The exact Flocq Round_odd names remain listed above.
- `round_odd_pt`: this now has a theorem declaration in `Round_odd.lean`, with
  the Coq `Exists_NE` section hypothesis made explicit.
- `Rnd_odd_pt_monotone`: this now has a theorem declaration in
  `Round_odd.lean`, with the same explicit `Exists_NE` and `1 < beta`
  hypotheses needed by the Lean statement.
- `digitAuxLess` and `digitAuxMore`: these now have theorem declarations in
  `Pff.lean`. The local `digitAux` model was strengthened from a constant
  placeholder to a fuel recursion over the unary `Positive` compatibility
  wrapper before proving them, so these are no longer payload-free gaps.
- `RoundedProjector`: this now has a theorem declaration in `Pff.lean`. Under
  the current generic Lean fallback, `ProjectorP` is the same same-input
  uniqueness property carried by `MinOrMaxP`, the third component of
  `RoundedModeP`.
- `round_round_lt_mid_same_place`: this now has a theorem declaration and proof
  in `Double_rounding.lean`. The proof follows the upstream Flocq shape: the
  midpoint hypothesis gives a strict half-ulp floor-mantissa bound, both
  nearest rounds reduce via `Znearest_imp`, and the outer round fixes the
  generic floor result.
- `round_round_lt_mid_further_place'`: this now has a theorem declaration and
  proof in `Double_rounding.lean`. The proof follows the upstream split on the
  inner nearest round being zero/nonzero, using the concrete `roundR`
  half-ulp error bound and `mag_roundR_ge` to recover the original binade in
  the nonzero case.
- `round_round_lt_mid_further_place`: this now has a theorem declaration and
  proof in `Double_rounding.lean`. It derives the primed theorem's upper-binade
  premise from the upstream `fexp1 (mag x) <= mag x` condition; the nonzero
  floor-round branch uses `id_p_ulp_le_bpow` plus the concrete `mag_roundR_ge`
  bridge instead of the older `ulp_DN` hypothesis.
- `RND_Min_Pos_bounded_aux`: this now has a theorem declaration and proof in
  `Pff.lean`. The Lean statement keeps the Coq section hypotheses explicit:
  nonnegative input, radix greater than one, precision greater than one,
  `b.vNum = Zpower_nat radix p.toNat`, the lower exponent bound, and the
  upper binade bound `r < radix^(e + p)`.
- `RND_Min_Pos_canonic`: this now has a theorem declaration and proof in
  `Pff.lean`. The Lean statement keeps the Coq section hypotheses explicit:
  nonnegative input, `beta = radix`, radix greater than one, precision greater
  than one, and `b.vNum = Zpower_nat radix p.toNat`. The proof splits exactly
  on the upstream normal/subnormal branch for `RND_Min_Pos`; the normal branch
  derives the selected exponent from the logarithmic floor and applies
  `RND_Min_Pos_bounded_aux`, while the subnormal branch reuses the boundedness
  lemma at exponent `-b.dExp` and proves the strict mantissa bound below the
  first normal value.
- `round_round_lt_mid`: this now has a theorem declaration and proof in
  `Double_rounding.lean`. It matches the upstream case split between equal
  exponent places, handled by `round_round_lt_mid_same_place`, and strictly
  further places, handled by `round_round_lt_mid_further_place`.
- `round_round_gt_mid_same_place`: this now has a theorem declaration and
  proof in `Double_rounding.lean`. It is the upstream symmetric same-place
  midpoint lemma, using `midp'`/ceil, `Znearest_imp`, and `roundR_generic` for
  the outer fixed generic result.
- `round_round_gt_mid_further_place'`: this now has a theorem declaration and
  proof in `Double_rounding.lean`. It preserves the upstream hypotheses,
  including the premise that the inner nearest round is below the current
  binade bound, and mirrors the ceil-side proof using the concrete `roundR`
  half-ulp error bound and `mag_roundR_ge`.
- `round_round_gt_mid_further_place`: this now has a theorem declaration and
  proof in `Double_rounding.lean`. It matches the upstream Flocq split on
  whether the inner nearest round is below the current binade bound. The
  boundary branch proves the inner result is exactly `beta^(mag x)` by
  converting the scaled mantissa into an integer interval, then proves the
  outer nearest round chooses the same binade-boundary mantissa using the
  concrete half-ulp error bound.
- `round_round_gt_mid`: this now has a theorem declaration and proof in
  `Double_rounding.lean`. It matches the upstream case split between equal
  exponent places, handled by `round_round_gt_mid_same_place`, and strictly
  further places, handled by `round_round_gt_mid_further_place`.
- `ClosestSymmetric`: this now has a theorem declaration in `Pff.lean`. The
  proof follows the Flocq argument: boundedness is preserved by `Fopp`, and the
  closest-distance inequality is transported through `F2R (Fopp x) = -F2R x`
  plus `abs_neg`.
- `ClosestOpp`: this now has a theorem declaration in `Pff.lean`. It is the
  pointwise negation theorem from Flocq and uses the same boundedness and
  absolute-value symmetry argument as `ClosestSymmetric`.
- `EvenClosestSymmetric`: this now has a theorem declaration in `Pff.lean`.
  The proof mirrors Flocq: apply `ClosestSymmetric` to the closest component,
  use `FNevenFop` for the even branch, and use closest symmetry plus `Fopp`
  involution for the uniqueness branch.
- `firstNormalPosNormal`: this now has a theorem declaration in `Pff.lean`,
  with the Flocq section assumptions made explicit: `1 < radix`,
  `1 < precision`, and `b.vNum = Zpower_nat radix precision`.
- `FboundedMboundPos`: this now has a theorem declaration in `Pff.lean`,
  with the Flocq section assumptions made explicit: `beta = radix`,
  `1 < radix`, positive `precision`, and
  `b.vNum = Zpower_nat radix precision`. The proof constructs the direct
  bounded float for strict mantissas and the normalized boundary float
  `radix^(precision - 1) * radix^(z + 1)` when
  `m = Zpower_nat radix precision`.
- `FboundedMbound`: this now has a theorem declaration in `Pff.lean`, with the
  same explicit Flocq section assumptions as `FboundedMboundPos`. The proof
  follows Flocq: use `FboundedMboundPos` directly for nonnegative mantissas and
  use `Fopp` for negative mantissas.
- `ClosestMonotone`: this now has a theorem declaration in `Pff.lean`. The
  Lean statement targets `MonotoneP_float (Closest ...)`, the float-specific
  real-value monotonicity corresponding to Flocq's `MonotoneP radix Closest`;
  the proof uses the two closest-distance inequalities and a real-line
  projection argument.
- `ClosestFabs`: this now has a theorem declaration in `Pff.lean`, with the
  Flocq section radix assumption `1 < beta` made explicit. The proof uses
  boundedness preservation under `Fabs`, `F2R (Fabs p) = |F2R p|`, the reverse
  triangle inequality for absolute values, and the original closestness
  instantiated at either `g` or `Fopp g` depending on the sign of `r`.
- `SterbenzAux`: this now has a theorem declaration in `Pff.lean`, with the
  Flocq radix assumption `1 < beta` made explicit. The proof follows the local
  aligned-subtraction model: it uses `Fminus_correct` for the real value,
  derives `0 ≤ x - y`, `x - y ≤ x`, and `x - y ≤ y` from the Sterbenz range,
  then splits on the selected alignment exponent and applies
  `Rle_Fexp_eq_Zle` to bound the result mantissa by the corresponding input
  mantissa.
- `Sterbenz`: this now has a theorem declaration in `Pff.lean`, with the Flocq
  radix assumption `1 < beta` made explicit. The proof follows Flocq: apply
  `SterbenzAux` directly when `F2R y ≤ F2R x`; otherwise apply `SterbenzAux` to
  `y, x`, transfer through `Fopp_Fminus`, and use `oppBoundedInv`.
- `EvenClosestMonotone`: this now has a theorem declaration in `Pff.lean`. The
  Lean statement targets `MonotoneP_float (EvenClosest ...)`, matching the
  float-specific order payload of Flocq's `MonotoneP radix EvenClosest`; the
  proof follows Flocq by unpacking both `EvenClosest` hypotheses and applying
  the restored `ClosestMonotone` to their `Closest` components.
- `ClosestMin`: this now has a theorem declaration in `Pff.lean`. The Lean
  statement uses the concrete float-specific `isMin'` and `isMax'` predicates,
  plus the upstream midpoint condition `2 * r <= min + max`, and proves the
  existing concrete `Closest` predicate by splitting whether each bounded
  candidate lies below or above `r`.
- `ClosestMax`: this now has a theorem declaration in `Pff.lean`. It is the
  symmetric companion of `ClosestMin`: the statement uses `isMin'`, `isMax'`,
  and the upstream midpoint condition `min + max <= 2 * r`, then proves
  `Closest ... max` by splitting whether each bounded candidate lies above or
  below `r`.
- `ClosestMinOrMax`: this now has a theorem declaration in `Pff.lean`. I added
  `MinOrMaxP_float`, a float-specific predicate matching Flocq's
  `MinOrMaxP P := forall r p, P r p -> isMin r p \/ isMax r p`, because the
  existing generic `MinOrMaxP` fallback is a uniqueness property and is not the
  Flocq payload. The theorem proves the concrete `Closest` result by rewriting
  the closest-distance inequality on each side of `r`.
- `round_round_mult`: this now has a theorem declaration in
  `Double_rounding.lean`, with the Flocq radix invariant `1 < beta` and the
  local `Calc.Round.Mode` wrapper made explicit. I also restored the upstream
  helper `round_round_mult_aux`. The proof follows Flocq: use
  `round_round_mult_hyp` plus `mag_mult` to show the product of two `fexp1`
  generic values is `fexp2` generic, then apply `roundR_generic` to collapse the
  inner rounding.
- `round_round_mult_FLX`: this now has a theorem declaration in
  `Double_rounding.lean`. It specializes the restored `round_round_mult` theorem
  to `FLX_exp`, makes Lean's positive-precision and `1 < beta` assumptions
  explicit, and proves the upstream `2 * prec <= prec'` exponent side-condition
  by arithmetic on `FLX_exp`.
- `round_round_mult_FLT`: this now has a theorem declaration in
  `Double_rounding.lean`. It specializes the restored `round_round_mult` theorem
  to `FLT_exp`, makes Lean's positive-precision and `1 < beta` assumptions
  explicit, and proves the upstream `emin' <= 2 * emin` and
  `2 * prec <= prec'` exponent side-conditions by arithmetic over the `max`
  definition of `FLT_exp`.
- `round_round_mult_FTZ`: this now has a theorem declaration in
  `Double_rounding.lean`. It specializes the restored `round_round_mult` theorem
  to `FTZ_exp`, makes Lean's positive-precision and `1 < beta` assumptions
  explicit, and proves the upstream `emin' + prec' <= 2 * emin + prec` and
  `2 * prec <= prec'` exponent side-conditions by splitting the `FTZ_exp`
  cutoff branches and discharging the integer arithmetic.
- `FTZ_exp`, `round_FTZ_small`, and `ulp_FTZ_0`: the core FTZ exponent function
  is now aligned with Flocq's branch `if e - prec < emin then emin + prec - 1
  else e - prec`. The local `round_FTZ_small` and `ulp_FTZ_0` specs were updated
  to the Flocq threshold `emin + prec - 1`; the previous `emin` threshold was a
  Lean-side translation bug and made the FTZ sqrt side-condition lemmas false.
- `FLX_round_round_sqrt_hyp` and
  `FLX_round_round_sqrt_radix_ge_4_hyp`: these now have theorem declarations
  and proofs in `Double_rounding.lean`. They restore the upstream FLX
  arithmetic side conditions for the blocked sqrt double-rounding family, with
  the Coq `Prec_gt_0 prec` section assumption explicit. The non-radix public
  wrappers are now restored through `round_round_sqrt`; the active
  `round_round_sqrt_*` targets that remain listed are only the radix-`ge_4`
  wrappers, because their midpoint-gap payload is separate missing
  infrastructure.
- `round_round_mid_cases`: this upstream helper now has a theorem declaration
  and proof in `Double_rounding.lean`. The Lean proof avoids adding the
  `Exp_not_FTZ` assumption required by the public `Ulp.round_UP_DN_ulp` wrapper
  by proving the needed positive floor/ceil spacing directly from the concrete
  `roundR` formula and non-integrality of the scaled mantissa. The active
  sqrt/div public wrappers remained listed at this point because the generic
  sqrt and division stacks were still absent; the current sqrt state is now
  narrower, with the non-radix public wrappers restored and only the
  radix-`ge_4` sqrt wrapper family still listed.
- `mag_sqrt_disj`: this upstream helper now has a theorem declaration and proof
  in `Double_rounding.lean`. The proof uses the local `Raux.mag_sqrt` theorem
  and integer parity decomposition of `floor(log x / log beta)`; the branch
  order follows this Lean port's `mag = floor(log) + 1` convention.
- `FLT_round_round_sqrt_hyp`, `FTZ_round_round_sqrt_hyp`,
  `FLT_round_round_sqrt_radix_ge_4_hyp`,
  `FTZ_round_round_sqrt_radix_ge_4_hyp`, `FLX_round_round_div_hyp`,
  `FLT_round_round_div_hyp`, and `FTZ_round_round_div_hyp`: these upstream
  exponent side-condition lemmas are restored with proofs in
  `Double_rounding.lean`. They remove the exponent-side-condition blocker for
  the sqrt/div wrapper families. The non-radix sqrt wrappers are now restored;
  the radix-`ge_4` sqrt family still needs its separate midpoint-gap payload,
  and any remaining division wrappers still depend on their generic division
  stack.
- Current-tree harness check on 2026-06-26 (`.change_log/codex_attempt_20260626_070400`)
  reconfirmed `round_round_sqrt_FLX` is blocked specifically because the
  generic `round_round_sqrt_aux` / `round_round_sqrt` stack was absent at that
  time. The non-radix midpoint-gap payload has since been restored as
  `round_round_sqrt_aux_midpoint_gap`, and the public non-radix wrappers are now
  restored. The local `mag_generic_gt` theorem now has the strict Flocq-style
  conclusion `cexp beta fexp x < mag beta x`, so the older strict-magnitude note
  is no longer the active blocker for this wrapper family.

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

Current validation, 2026-07-02:

- The active public `Branch Diff Audit` scaffold list contains 0 exact Flocq
  declaration names; the live list is recorded near the top of this file.
- No active public name remains as a same-name `def`/`Unit` port gap.
- No active public names are absent in the current branch.

The older bullets below record how this list shrank over prior re-audits; their
older active-count numbers are historical, not the current count.

- Re-audit on 2026-06-12 removed `FboundedMboundPos`, `FboundedMbound`, and
  `ClosestMonotone` after restoring them as proved theorems. I also
  checked the plausible different-name IEEE replacements (`binary_*_correct`
  and `B754_*_correct`); they are local `Unit` port-gap wrappers, not faithful
  replacements for the exact Flocq theorem payloads.
- Follow-up re-audit on 2026-06-12 restored `ClosestFabs`, `SterbenzAux`, and
  `Sterbenz`. Every remaining active name still has an upstream Flocq
  declaration, none has a same-name Lean theorem/lemma on this branch, and the
  similar-name Lean declarations found near the active names are helper facts
  or payload-free wrappers rather than replacements for the listed Flocq
  statements.
- Follow-up branch-base validation on 2026-06-12 checked the active list
  mechanically against `origin/main`, the current branch, and the local Flocq
  clone. All 98 active names were theorem/lemma declarations in `origin/main`;
  all 98 are exact upstream Flocq declaration names; none is already restored
  as a theorem/lemma in the current branch. The 41 same-name current Lean
  declarations are still `def`/`Unit` port gaps, and the other 57 names are
  absent rather than replaced.
- Additional current-branch validation on 2026-06-12 found no further names to
  delete from the active list. The close-looking IEEE wrappers
  (`binary_*_correct`, `B754_plus_correct`, and `B754_mult_correct`) are still
  local payload-free `def` wrappers, not replacements for the listed Flocq
  theorem payloads. The Pff2Flocq, Double_rounding, and Round_odd active names
  are either absent or same-name `def` scaffolds rather than restored theorems.
- User-requested revert-list re-audit on 2026-06-12 rechecked the active list
  mechanically: all 98 names are theorem/lemma declarations in `origin/main`,
  all 98 are exact upstream Flocq declarations in the local
  `/mnt2/users/kaile/hantao/flocq-upstream` checkout, none is restored as a
  same-name Lean theorem/lemma on this branch, and the only close-looking
  different-name current declarations are still `Unit`/port-gap wrappers. No
  active entry should be deleted from the revert list on this basis.
- After restoring `round_round_mult`, `round_round_mult_FLX`,
  `round_round_mult_FLT`, and `round_round_mult_FTZ`, the same mechanical check
  gives 94 active names: all 94 are upstream Flocq declarations and none is
  restored as a same-name Lean theorem/lemma on this branch. The remaining split
  is 41 same-name `def`/`Unit` port gaps and 53 absent declarations.
- After restoring `RND_Min_Pos_bounded_aux`, `RND_Min_Pos_canonic`, and the two
  FLX sqrt hypothesis helpers, the active `Branch Diff Audit` list contains 84
  exact revert targets. The FLX sqrt helpers are supporting infrastructure and
  do not remove the active sqrt wrapper targets until the generic sqrt
  double-rounding stack is restored.
- After restoring `underf_mult_aux` and `underf_mult_aux'` in
  `Pff2Flocq.lean`, the active list contains 82 exact revert targets. Both
  theorems follow the upstream Flocq `Underf_mult_aux` section: bounded inputs
  plus the product lower bound imply the exponent lower bound, with the primed
  lemma specialized at `e = -dExp b`.
- After restoring `V1_Und3'` and `V1_Und3` in `Pff2Flocq.lean`, the active
  list contains 80 exact revert targets. These correspond to the upstream
  ErrFMA V1 non-underflow consequences for `u1 := round_flt (a*x)`.
- After restoring `mult_error_FLT_ge_bpow'` in `Pff2Flocq.lean`, the active
  list contains 79 exact revert targets. The theorem specializes the existing
  multiplication-error lower-bound infrastructure to the nearest-even rounding
  setup used by upstream Flocq's ErrFMA V2 section.
- After restoring `V2_Und4` in `Pff2Flocq.lean`, the active list contains 78
  exact revert targets. The theorem proves the upstream ErrFMA V2 lower bound
  for `beta1 := round_flt (u1 + alpha1)` from the `U1` non-underflow
  hypothesis.
- After restoring `V2_Und2` in `Pff2Flocq.lean`, the active list contains 77
  exact revert targets. The theorem proves the upstream ErrFMA V2 lower bound
  for `alpha1 := round_flt (y + u2)` from the `U2` non-underflow hypothesis,
  with `u2` formatted through the existing `mult_error_FLT` theorem.
- After restoring `U3_discri1` in `Pff2Flocq.lean`, the active list contains
  76 exact revert targets. The theorem proves the upstream Discri1 lower bound
  for `round_flt (p - q)` from the `U1` non-underflow hypothesis.
- After restoring `U4_discri1` in `Pff2Flocq.lean`, the active list contains
  75 exact revert targets. The theorem proves the upstream Discri1 lower bound
  for the final branch value `d`, using `U3_discri1` and
  `round_FLT_plus_ge`.
- After restoring `U5_discri1_aux` and `U5_discri1` in `Pff2Flocq.lean`, the
  active list contains 73 exact revert targets. The auxiliary theorem follows
  the upstream proof split: if `|x + y|` is already large, monotonicity of
  rounding gives the rounded lower bound; otherwise the small-sum case would
  make `x + y` formatted by the restored `generic_format_plus_weak`, contrary
  to the non-exact-rounding hypothesis. The specialized theorem applies this
  auxiliary result to `dp` and `-dq`, using the restored multiplication-error
  lower-bound theorem for each product residual.

The earlier explanatory sections also mentioned Lean-local wrappers and support
facts. Those are not Flocq revert targets and are kept only when they identify a
supporting proof obligation. In particular, these names were removed from the
theorem lists below rather than treated as upstream Flocq items to revert:

- local IEEE wrappers: `binary_add_correct`, `binary_mul_correct`,
  `binary_sqrt_correct`, `binary_div_correct`, `binary_fma_correct`,
  `binary_sub_correct`, `B754_plus_correct`, and `B754_mult_correct`
- local Generic/Ulp support names: `Znearest_eq_choice_of_eq_half`,
  `Znearest_eq_if`, `round_DN_exists`, `round_DN_exists_global`,
  `round_UP_exists`, `round_to_generic_monotone`,
  `succ_le_plus_ulp_theorem`, `ulp_round_pos_theorem`,
  `ulp_round_theorem`, `error_le_half_ulp_theorem`,
  `generic_format_pred_aux1_theorem_early`, `succ_le_lt_aux_pos_core`,
  `succ_le_lt_theorem`, `round_DN_eq_theorem`,
  `pred_succ_pos_theorem`, `pred_succ_theorem`,
  `generic_format_pred_aux1_theorem`, and
  `round_DN_plus_eps_pos_strict`

The prose mention of `Znearest_half` refers to the upstream Flocq theorem in
`src/Core/Generic_fmt.v`; the Lean payload is now exposed under that direct
name rather than through the earlier local wrapper.

## Calc/Round Placeholder Section

`FloatSpec/src/Calc/Round.lean` still contains a Coq theorem compatibility
section:

- Section: `CoqTheoremsPlaceholders`
- Audit namespace: `Audit`

`truncate_aux_comp` is no longer a tautological placeholder. It now proves the
real Coq-style composition theorem for two positive truncation shifts, with the
Coq radix assumption made explicit as `1 < beta`, by reusing
`inbetween_float_ex`, `inbetween_float_new_location`, and
`inbetween_float_unique`.

`truncate_0` is no longer the old auxiliary zero-shift check. It now matches the
upstream `truncate` theorem shape through the local `truncate_triple` wrapper:
truncating any `(0, e, l)` triple has zero mantissa in the result.

`generic_format_truncate` is no longer the placeholder over a zero-shift
`truncate_aux` call. It now proves the upstream-shaped format result for
`truncate_triple`; the positive truncation branch uses digit division
infrastructure and the new `FloatSpec.Core.Float_prop.Raux_mag_F2R_Zdigits`
bridge to show that the output exponent is exactly the generic-format exponent.
The related `Zdigits_Raux_mag` theorem proves that nonzero integer digit counts
agree with the Coq-compatible `FloatSpec.Core.Raux.mag`; the older same-file
`Zdigits_mag` remains a legacy compatibility theorem for the local ceiling-based
`Float_prop.mag`.

`cexp_inbetween_float` and `cexp_inbetween_float_loc_Exact` are no longer
conclusion-as-hypothesis wrappers. They now prove the Flocq-style exponent
alignment from an `inbetween_float` interval and the relevant exponent-side
bound, with Lean's radix condition passed explicitly as `1 < beta`.

`truncate_correct_partial'` and `truncate_correct_partial` are no longer
self-equality shells. They now match the positive-input Coq payload over the
local `truncate_triple` wrapper: truncation preserves the `inbetween_float`
bracket and returns exponent `cexp beta fexp x`; the non-primed variant uses
`cexp_inbetween_float` to bridge the `fexp (Zdigits beta m + e)` hypothesis.

`truncate_correct'` and `truncate_correct` are no longer self-equality shells.
They now match the Coq payload over `truncate_triple`: the truncated triple
preserves the `inbetween_float` bracket, and either returns exponent
`cexp beta fexp x` or returns an exact location with `x` in
`generic_format beta fexp`. The zero branch proves that a zero bracket forces
mantissa zero and exact location; the exact positive branch uses
`generic_format_F2R` with the `Raux.mag` bridge.

`truncate_correct_format` is no longer a tautological compatibility shell. It
now proves the upstream-shaped exact-generic truncation payload over
`truncate_triple`: for nonzero mantissa `m`, truncating
`(m, e, loc_Exact)` preserves the represented real value and returns exponent
`cexp beta fexp x`. Lean keeps `[Valid_exp beta fexp]` and the radix condition
`1 < beta` explicit. The positive truncation branch identifies the scaled
mantissa with `m / beta^k` using `scaled_mantissa_generic` and `Zfloor_div`; the
zero-shift branch collapses from the side condition `e ≤ fexp (Zdigits beta m +
e)`.

`round_any_correct`, `round_trunc_any_correct`, and
`round_trunc_any_correct'` are no longer self-equality or canonical-exponent-only
wrappers. `round_any_correct` now matches the upstream disjunction shape: either
the input exponent is already `cexp beta fexp x`, or the location is exact and
`x` is in `generic_format beta fexp`; the exact branch uses `roundR_generic`
and the `Valid_rnd` integer-fixing law. The two truncating-round wrappers now
call `Audit.truncate_correct`/`Audit.truncate_correct'` and then
`round_any_correct` on the resulting triple.

`round_sign_any_correct`, `round_trunc_sign_any_correct`, and
`round_trunc_sign_any_correct'` are also restored. The sign-aware theorem now
uses an `inbetween_float` bracket on `|x|` and returns the Coq-style
`cond_Zopp (Rlt_bool x 0)` mantissa. The truncating sign wrappers now route
through `Audit.truncate_correct`/`Audit.truncate_correct'`, transport canonical
exponents across `abs` with `cexp_abs`, and turn exact generic-format evidence
for `|x|` back into evidence for `x` with `generic_format_abs_inv`.

`inbetween_float_round` is no longer a scaled-mantissa-only helper. It now
matches the upstream theorem shape: from
`inbetween_float beta m (cexp beta fexp x) x l`, it proves that
`roundR beta fexp rnd x` is the `F2R` value with mantissa `choice m l` and
canonical exponent `cexp beta fexp x`. The local private
`inbetween_scaled_mantissa` lemma carries the scale-down step needed to apply
the integer-level choice hypothesis.

`round_DN_correct` is now present as the Coq-compatible downward-rounding
specialization of `round_any_correct`. It uses the existing `inbetween_int_DN`
integer payload with choice function `fun m _ => m`, so this restores a missing
public Flocq name without adding a new placeholder or weakening the theorem.
`round_trunc_DN_correct`, `round_trunc_DN_correct'`,
`round_sign_DN_correct`, `round_trunc_sign_DN_correct`, and
`round_trunc_sign_DN_correct'` are now present as the remaining Coq-compatible
downward-rounding alias wrappers. The truncation variants specialize
`round_trunc_any_correct`/`round_trunc_any_correct'` with `inbetween_int_DN`;
the sign variants specialize the sign-aware generic wrappers with
`inbetween_int_DN_sign` and the Coq choice
`fun s m l => cond_incr (round_sign_DN s l) m`.
`round_UP_correct`, `round_trunc_UP_correct`, and
`round_trunc_UP_correct'` are also present as Coq-compatible upward-rounding
alias wrappers over `round_any_correct`/`round_trunc_any_correct`/
`round_trunc_any_correct'`, using `inbetween_int_UP` and the Coq choice
`fun m l => cond_incr (round_UP l) m`. The sign-UP upward-rounding payload is
also restored: `round_sign_UP`, `inbetween_int_UP_sign`,
`inbetween_float_UP_sign`, `round_sign_UP_correct`,
`round_trunc_sign_UP_correct`, and `round_trunc_sign_UP_correct'` are present.
`inbetween_int_UP_sign` proves the `Zceil`/`cond_Zopp` sign bridge, and the
public aliases specialize the sign-aware generic wrappers with the Coq choice
`fun s m l => cond_incr (round_sign_UP s l) m`.
`inbetween_int_ZR_sign` and `inbetween_float_ZR_sign` are also restored as
the Coq-compatible zero-rounding sign variants. The integer theorem proves
`Ztrunc x = cond_Zopp (Rlt_bool x 0) m` from an `inbetween_int` bracket on
`|x|`, and the float theorem specializes `inbetween_float_round_sign` with the
constant choice `fun _ m _ => m`.
The ZR correctness aliases are restored too: `round_ZR_correct`,
`round_trunc_ZR_correct`, `round_trunc_ZR_correct'`,
`round_sign_ZR_correct`, `round_trunc_sign_ZR_correct`, and
`round_trunc_sign_ZR_correct'` specialize the generic round/truncate wrappers
with the Coq ZR choices.
The remaining nearest-even and nearest-away alias wrappers from upstream
`Round.v` are restored as well: `round_NE_correct`,
`round_trunc_NE_correct`, `round_trunc_NE_correct'`,
`round_sign_NE_correct`, `round_trunc_sign_NE_correct`,
`round_trunc_sign_NE_correct'`, `round_NA_correct`,
`round_trunc_NA_correct`, `round_trunc_NA_correct'`,
`round_sign_NA_correct`, `round_trunc_sign_NA_correct`, and
`round_trunc_sign_NA_correct'`. The direct declaration-name comparison between
upstream `Calc/Round.v` and `FloatSpec/src/Calc/Round.lean` is now empty for
the parsed `Theorem`/`Definition` names in `Round.v`.
These name restores do not reduce the placeholder scanner count, because they
were absent exact aliases rather than current scanner hits.

Other names in this section that should be audited against Coq `Round.v`:

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

Why this matters: Core and IEEE rounding correctness eventually need the
integer/real inbetween lemmas to justify that a chosen integer mantissa and
exponent really correspond to the requested rounding mode. Without these, proofs
can only show that local helper functions execute, not that they implement the
Flocq rounding theorem.

## Core Generic Format Infrastructure

The following exact Flocq `Generic_fmt.v` items are central to spacing,
monotonicity, and DN/UP neighbor correctness:

`Znearest_DN_or_UP`, `Znearest_ge_floor`, `Znearest_le_ceil`,
`Znearest_N_strict`, `Znearest_half`, `Znearest_imp`, and `Znearest_opp` are
now aligned as direct theorems rather than Hoare wrappers.

As of the 2026-07-03 parsed exact-name comparison against upstream
`Generic_fmt.v`, allowing Lean theorem names with apostrophes, no parsed absent
public `Generic_fmt.v` declaration names remain. This pass restored the public
`round` definition as the Flocq-name wrapper around `roundR`, and restored
`cexp_round_ge` as the concrete integer-rounding theorem proved from
`mag_roundR_ge` and `Monotone_exp.mono`. Earlier parser hits for
`valid_exp_large'`, `generic_format_F2R'`, `generic_format_bpow'`, and
`generic_format_bpow_inv'` were false positives from apostrophe handling; those
names are already present in Lean.

Items still needing Flocq-level alignment or stronger supporting lemmas:

- local Lean support for UP existence, monotonicity, round-to-format helper
  lemmas, and small/boundary rounding facts may still be needed, but those
  helper names are not direct Flocq branch-diff declarations to revert.
- the placeholder audit still flags several Generic helper comments and local
  helper statements, especially around round-to-format and away/UP/DN support;
  these are support debt below ULP, Pff, and IEEE correctness, not evidence that
  the direct `Znearest` theorem family is still missing.

Why this matters: these are the format-level facts that make nearest, down, and
up rounding behave like adjacent representable points. ULP proofs, error bounds,
and IEEE operation correctness all depend on the same adjacency and monotonicity
properties.

## Core ULP Infrastructure

As of the 2026-07-03 parsed exact-name comparison against upstream
`flocq-upstream/src/Core/Ulp.v`, `FloatSpec/src/Core/Ulp.lean` has no remaining
parsed absent public Flocq declaration names.

This pass restored `succ_DN_eq_UP`, `pred_UP_le_DN`, `UP_le_succ_DN`, and
`pred_UP_eq_DN` as public theorems over the concrete
`roundR ... rnd_floor`/`roundR ... rnd_ceil` operations, using the existing
DN/UP witness bridge, `succ_DN_eq_UP_theorem`, and predecessor/successor
inverse lemmas. It also restored `generic_format_succ_aux1` as the positive
`x + ulp x` closure lemma by reducing to `generic_format_succ`.
`lake env lean FloatSpec/src/Core/Ulp.lean` accepts the result.

Earlier ULP entries such as `succ_le`, `succ_le_inv`, `succ_le_plus_ulp`,
`round_DN_ge_UP_gt`, `ulp_round_pos`, `ulp_round`,
`error_lt_ulp_round`, `error_le_ulp_round`, `generic_format_pred_aux2`,
`generic_format_pred_pos`, `succ_le_lt_aux`, `succ_le_lt`, `round_DN_eq`,
`generic_format_pred`, `pred_succ_pos`, `pred_succ`,
`generic_format_pred_aux1`, `round_DN_plus_eps_pos`,
`round_DN_minus_eps_pos`, `round_DN_minus_eps`, `round_DN_plus_eps`,
`error_le_half_ulp`, and `error_le_half_ulp_round` now have parsed Lean
counterpart names. They may still deserve statement-level review, but they are
not in the current absent-name delta for `Ulp.v`.

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

- `Fulp`: now has the Flocq-shaped bound/radix/precision-indexed normalized
  exponent definition in `Pff.lean`, and `CanonicFulp`, `Fulp_zero`,
  `FulpComp`, `FulpLe`, `FulpSucCan`, `FulpPredCan`, `FulpSuc`, and
  `FulpPred` have been restored. `FulpSuc`/`FulpPred` are stated over the
  expanded normalized-neighbor expressions `FSucc (Fnormalize p)` and
  `FPred (Fnormalize p)`. The `FSucc` parity facts have also been restored
  over the boundary-aware successor. `FNSuccCanonic`, `FNSuccLt`, and
  `FNSuccProp` are now restored as public normalized-neighbor wrappers over
  `FnormalizeCanonic`, `FnormalizeCorrect`, `FSuccCanonic`, `FSuccLt`, and
  the all-sign `FSuccProp`. `MinMax` is also restored as the strict-minimum to
  normalized-successor maximum step.
- `Fnormalize`: real Coq-shaped construction is present, including
  `FnormalizeCorrect`, `FnormalizeBounded`, and `FnormalizeCanonic`; remaining
  work is downstream endpoint parity/totality use rather than the
  normalized-neighbor order stack itself.
- `Fshift`: Coq-shaped mantissa/exponent shift is present and connected to the
  restored normalizer for `FnormalizeCorrect`/`FnormalizeBounded`.
- `RND_Closest`, `RND_Closest_canonic`, and `RND_Closest_correct`: the generic
  arbitrary-tie closest-rounding layer from `Pff2FlocqAux.v` is now present and
  compiles in `Pff.lean`; the DN/UP/N equality bridge to Flocq `roundR`
  (`pff_round_DN_is_round`, `pff_round_UP_is_round`,
  `pff_round_N_is_round`, and `round_N_is_pff_round`) is now present and
  compiles in `Pff2FlocqAux.lean`.
- `Fulp_ulp_aux` and `Fulp_ulp`: now use a real auxiliary `PFulp` quantity and
  prove `PFulp = ulp beta (FLT_exp ...) ...` under the same explicit radix and
  positive-precision side conditions that are section assumptions upstream.
- `round_NE_is_pff_round_generic`: a generic PffFloat witness/equality bridge
  is now present in `Pff2FlocqAux.lean`, extending the earlier binary32/64-only
  bridges to arbitrary bounds and precision under an explicit `Valid_exp`
  side condition. The arbitrary-choice `round_N_is_pff_round` bridge is also
  restored. The upstream nearest-even value and witness bridges
  (`pff_round_NE_is_round` and `round_NE_is_pff_round`) are now restored; the
  required `RoundNE.Exists_NE` condition for FLT exponents is derived locally
  from `precisionNotZero`. Remaining nearest-even work is to feed that bridge
  into the public Pff2Flocq wrappers.
- `digitAux`: now a fuel recursion over the unary `Positive` compatibility
  wrapper, but still not a literal port of Coq's binary-`positive` recursion.
- public generic skeletons around `isMin`, `isMax`, `MonotoneP`, and
  `MinOrMaxP` that require float-specific hypotheses in downstream proofs.

Why this matters: Pff depends on canonical float normalization, boundedness, and
digit/shift reasoning. These are needed before Pff2Flocq and high-level error
theorems can be trusted as translations rather than executable sketches.

## IEEE Infrastructure

The exact active branch-diff names in the IEEE layer have been restored.
The IEEE layer still has local non-Flocq port-gap definitions for broader
correctness payloads.

`Binary.lean`:

- No exact active branch-diff names remain.

The old local wrappers `binary_*_correct`, `B754_plus_correct`, and
`B754_mult_correct` are not exact Flocq names, so they are not revert targets.
They still point at real IEEE port gaps: the corresponding upstream payloads are
the `Bplus_correct`, `Bmult_correct`, `Bdiv_correct`, and `Bfma_correct`
families. `Bplus_correct` and
`Bmult_correct` are not in the branch-diff revert list because the branch base
exposed them through local wrapper names rather than exact Flocq theorem names.

`PrimFloat.lean`:

- primitive classifiers `prim_is_finite`, `prim_is_nan`,
  `prim_is_infinite` remain constant in the current bridge model.

Why this matters: the IEEE layer can build and run local models, but the
correctness theorems that connect those models to Flocq/IEEE semantics are not
ported. A product API should not expose these as trusted correctness results
until the Binary and SingleNaN rounding/normalization cores are ported.

## Suggested Repair Order

1. Continue `Calc/Round.lean` inbetween/truncate theorem payloads, starting with
   the remaining inbetween rounding-mode theorem families.
2. Feed the restored `pff_round_NE_is_round` / `round_NE_is_pff_round` bridge
   into the active Pff2Flocq wrappers.
3. Finish `Ulp.lean` predecessor/successor and ULP-stability stack:
   `generic_format_pred*`, `pred_succ*`, `succ_le_lt*`, `ulp_round*`,
   `error_*_ulp*`, and `round_DN_*_eps*`.
4. Continue Generic helper-level monotonicity and UP/DN support as needed by
   the ULP stack, including local `round_UP_exists`,
   `round_to_generic_monotone`, and round-to-format helper gaps.
5. Finish the remaining Pff/Pff2Flocq payloads:
   active-name wrappers still need `FmaErr`, `ErrFmaAppr`, and the
   `Veltkamp`/`Dekker` payloads; lower exact-name debt still includes
   `Axpy_opt`.
6. Port IEEE Binary/SingleNaN rounding and normalization cores, then restore
   exact Flocq correctness theorem statements in place of `Unit` port gaps;
   replace old local wrapper names only after the upstream payload is present.
