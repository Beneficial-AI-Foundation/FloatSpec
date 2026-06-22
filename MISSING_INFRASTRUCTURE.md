# Missing Flocq Infrastructure

This document names the remaining infrastructure that blocks a product-grade
FloatSpec/Flocq translation. It focuses on concrete theorem and definition
names rather than broad labels.

The `Branch Diff Audit` section is the revert list. Later sections describe
supporting infrastructure; they should not be read as additional exact
branch-diff revert targets unless explicitly stated.

## Branch Diff Audit

Audit basis:

- Current branch: `floatspec-pipeline-gpt55`
- Compared against current `origin/main` after the PR #3 rebase:
  `bb9d513511a5ae4e945eebe0b48ba58afbc831f5`
- Current checked head for this audit:
  `8e667d622c3c24640e6427d48435495bd8b129a6`
- Flocq source checked locally under `/mnt2/users/kaile/hantao/flocq-upstream`.

I rechecked the branch-diff list against current `origin/main`, the current
branch, and the local Flocq clone. This section now keeps only declarations
that are exact Flocq declaration names and that have not been replaced by a real
theorem or lemma in the current branch. They should be restored as theorem
declarations with real proofs, not as `Unit`, `True`, `by trivial`, or other
payload-free definitions.

Current live split after the latest re-audit: 19 exact active names remain.
Of those 19, 4 are still same-name scaffold definitions and 15 are absent
declarations.

- `FloatSpec/src/Pff/Pff2Flocq.lean`:
  - `Veltkamp_Even`, `Veltkamp`, `Veltkamp_tail`
  - `Dekker`, `ErrFMA_correct`
  - `ErrFMA_correct_simpl`, `ErrFmaAppr_correct`, `discri_correct_test`
  - `discri_fp_test`, `Axpy`
- `FloatSpec/src/Prop/Double_rounding.lean`:
  - `round_round_sqrt_FLX`, `round_round_sqrt_FLT`,
    `round_round_sqrt_radix_ge_4_FLX`,
    `round_round_sqrt_radix_ge_4_FLT`, `round_round_sqrt_FTZ`,
    `round_round_sqrt_radix_ge_4_FTZ`
  - `round_round_div_FLX`, `round_round_div_FLT`,
    `round_round_div_FTZ`

Current restore blockers found by pipeline attempts:

- No exact active names remain in `FloatSpec/src/IEEE754/Binary.lean`.
- `Veltkamp_Even`, `Veltkamp`, and `Veltkamp_tail`: these
  are absent as real Lean theorems, and the same-name declarations in
  `origin/main` were only `sorry` shells. Upstream `Pff2Flocq.v` proves them by
  importing the Pff algorithm payloads (`VeltkampEven`, `Veltkamp`,
  `Veltkamp_tail`) through the generic nearest-rounding bridge and canonicity
  facts. The generic nearest-rounding equality bridge is now present in
  `Pff2FlocqAux.lean`, and `Fast2Sum_correct` now shows the wrapper pattern.
  As lower unblock steps,
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
  bridges). The current Lean file does not yet have that generic Pff min/max
  payload; local `roundR` floor/ceil facts alone only say how a rounded real
  behaves, not that the Pff-computed `tv` is the DN/UP rounded value of
  `y + a*x`.
- `ErrFMA_correct` and `ErrFMA_correct_simpl`: XHub pipeline attempts
  `.change_log/codex_attempt_20260620_013323` and
  `.change_log/codex_attempt_20260620_012353` checked the upstream
  `Pff2Flocq.v` proofs and left these blocked.  Upstream `ErrFMA_correct`
  uses the Pff-level reconstruction theorem `FmaErr` after converting all
  rounded intermediates through the generic nearest-rounding bridge
  `round_N_is_pff_round`; `ErrFMA_correct_simpl` then depends on
  `ErrFMA_correct` after discharging the V2 non-underflow hypotheses.  The
  generic `round_N_is_pff_round` witness bridge is now present in
  `Pff2FlocqAux.lean`, and the current Lean tree has the V2 helpers, but it
  still lacks the Pff reconstruction theorem `FmaErr`. Restoring these wrappers
  first would require a weakened theorem or a payload-free proof. The correct
  order is to port `FmaErr`, then restore the ErrFMA wrappers.
- `discri_correct_test` and `discri_fp_test`: the current branch has restored
  several discriminant lower-bound helpers (`format_dp`, `format_dq`,
  `U3_discri1`, `U4_discri1`, `format_d_discri1`, `format_d_discri2`,
  `U5_discri1_aux`, `U5_discri1`, and the `Fulp_ulp_aux`/`Fulp_ulp` bridge in
  `Pff2FlocqAux.lean`), but the final upstream theorems also depend on Pff's
  `discri` theorem and the remaining generic Pff-to-Flocq bridges
  (`format_is_pff_format`, `round_NE_is_pff_round`, `EvenClosestCompatible`,
  `RND_EvenClosest_correct`, and canonic/bounded facts). Those dependencies are
  still scaffolded or absent locally, so the final wrappers remain listed.
- `round_round_sqrt_*` and `round_round_div_*`: the FLX sqrt side-condition
  helpers, the generic midpoint case split, and the sqrt magnitude disjunction
  have been restored, but the public wrapper family still depends on
  the generic Flocq double-rounding stacks for square root and division
  (`round_round_sqrt_aux`, `round_round_sqrt`, and the `round_round_div_aux*`
  lemmas). The old
  `origin/main` names were `sorry` theorem shells, not recoverable proofs.
  XHub pipeline attempt `.change_log/codex_attempt_20260618_173418` confirmed
  the same blocker for the division family: `FLX_round_round_div_hyp`
  typechecks, but faithful restoration of `round_round_div_FLX` first requires
  porting the generic `round_round_div_aux0`, `round_round_div_aux1`,
  `round_round_div_aux2`, `round_round_div_aux`, and `round_round_div` stack.
Entries removed by this re-audit:

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
  the Coq `Prec_gt_0 prec` section assumption explicit. The active
  `round_round_sqrt_*` targets remain listed because the generic
  `round_round_sqrt_aux` and `round_round_sqrt` stack is still absent as proved
  Lean infrastructure.
- `round_round_mid_cases`: this upstream helper now has a theorem declaration
  and proof in `Double_rounding.lean`. The Lean proof avoids adding the
  `Exp_not_FTZ` assumption required by the public `Ulp.round_UP_DN_ulp` wrapper
  by proving the needed positive floor/ceil spacing directly from the concrete
  `roundR` formula and non-integrality of the scaled mantissa. The active
  sqrt/div public wrappers remain listed because `round_round_sqrt_aux`,
  `round_round_sqrt`, and the `round_round_div_aux*` stack are still absent.
- `mag_sqrt_disj`: this upstream helper now has a theorem declaration and proof
  in `Double_rounding.lean`. The proof uses the local `Raux.mag_sqrt` theorem
  and integer parity decomposition of `floor(log x / log beta)`; the branch
  order follows this Lean port's `mag = floor(log) + 1` convention.
- `FLT_round_round_sqrt_hyp`, `FTZ_round_round_sqrt_hyp`,
  `FLT_round_round_sqrt_radix_ge_4_hyp`,
  `FTZ_round_round_sqrt_radix_ge_4_hyp`, `FLX_round_round_div_hyp`,
  `FLT_round_round_div_hyp`, and `FTZ_round_round_div_hyp`: these upstream
  exponent side-condition lemmas are restored with proofs in
  `Double_rounding.lean`. They remove the arithmetic blocker for the sqrt/div
  wrapper families; the public wrappers remain listed until the generic
  midpoint/sqrt/div proof stacks are restored.

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

I rechecked the `Branch Diff Audit` block against the branch-base Lean
declarations, the current branch, and the local Flocq clone.

- The active revert list contains 94 names.
- All 94 are exact Flocq declarations.
- None of the 94 is already present in the current branch as a same-name Lean
  `theorem` or `lemma`.
- 41 of the 94 still have same-name Lean declarations, but those declarations
  are scaffold `def`/`Unit` port gaps, not proof replacements. They therefore
  remain valid revert targets.
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
  `Znearest_eq_if`, `Znearest_half_theorem`, `round_DN_exists`,
  `round_DN_exists_global`, `round_UP_exists`, `round_to_generic_monotone`,
  `succ_le_plus_ulp_theorem`, `ulp_round_pos_theorem`,
  `ulp_round_theorem`, `error_le_half_ulp_theorem`,
  `generic_format_pred_aux1_theorem_early`, `succ_le_lt_aux_pos_core`,
  `succ_le_lt_theorem`, `round_DN_eq_theorem`,
  `pred_succ_pos_theorem`, `pred_succ_theorem`,
  `generic_format_pred_aux1_theorem`, and
  `round_DN_plus_eps_pos_strict`

The prose mention of `Znearest_half` refers to the upstream Flocq theorem in
`src/Core/Generic_fmt.v`; the branch-base Lean name for that payload was the
local wrapper `Znearest_half_theorem`.

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

The following exact Flocq `Generic_fmt.v` items are central to spacing,
monotonicity, and DN/UP neighbor correctness:

- `Znearest_DN_or_UP`
- `Znearest_ge_floor`
- `Znearest_le_ceil`
- `Znearest_N_strict`
- `Znearest_half`
- `Znearest_imp`
- `Znearest_opp`
- `round_DN_pt`
- `round_DN_or_UP`
- `round_DN_opp`
- `round_DN_small_pos`
- `round_DN_UP_lt`

Items still needing Flocq-level alignment or stronger supporting lemmas:

- DN/UP adjacency used by `round_DN_or_UP`
- sign/duality bridge behind `round_DN_opp`
- small-value and boundary lemmas behind `round_DN_small_pos`
- strict DN/UP separation behind `round_DN_UP_lt`
- the remaining Znearest theorem family referenced near `Znearest`:
  `Znearest_N_strict`, `Znearest_half`, `Znearest_imp`, `Znearest_opp`
- local Lean support for UP existence and monotonicity may still be needed, but
  those helper names are not direct Flocq declarations to revert.

Why this matters: these are the format-level facts that make nearest, down, and
up rounding behave like adjacent representable points. ULP proofs, error bounds,
and IEEE operation correctness all depend on the same adjacency and monotonicity
properties.

## Core ULP Infrastructure

The following exact Flocq `Ulp.v` items form the predecessor/successor, ULP
stability, and rounding-error stack:

- `succ_le`
- `succ_le_inv`
- `succ_le_plus_ulp`
- `round_DN_ge_UP_gt`
- `ulp_round_pos`
- `ulp_round`
- `error_lt_ulp_round`
- `error_le_ulp_round`
- `generic_format_pred_aux2`
- `generic_format_pred_pos`
- `succ_le_lt_aux`
- `succ_le_lt`
- `round_DN_eq`
- `generic_format_pred`
- `pred_succ_pos`
- `pred_succ`
- `generic_format_pred_aux1`
- `round_DN_plus_eps_pos`
- `round_DN_minus_eps_pos`
- `round_DN_minus_eps`
- `round_DN_plus_eps`
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
  restored. Remaining nearest-even work is specific to the upstream
  `round_NE_is_pff_round` payload and its Pff `EvenClosest` compatibility
  component.
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
   exact Flocq correctness theorem statements in place of `Unit` port gaps;
   replace old local wrapper names only after the upstream payload is present.
