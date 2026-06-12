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
  `aae0e712807b0088cf52335046ac868cec388748`
- Flocq source checked locally under `/mnt2/users/kaile/hantao/flocq-upstream`.

I rechecked the branch-diff list against current `origin/main`, the current
branch, and the local Flocq clone. This section now keeps only declarations
that are exact Flocq declaration names and that have not been replaced by a real
theorem or lemma in the current branch. They should be restored as theorem
declarations with real proofs, not as `Unit`, `True`, `by trivial`, or other
payload-free definitions.

- `FloatSpec/src/IEEE754/Binary.lean`:
  - `Bfma_correct`
  - `Bminus_correct`, `Bdiv_correct`, `Bsqrt_correct`, `Bnearbyint_correct`,
    `Bldexp_correct`
- `FloatSpec/src/IEEE754/BinarySingleNaN.lean`:
  - `Bldexp_Bopp_NE`
- `FloatSpec/src/Pff/Pff.lean`:
  - `FnormalizeCanonic`, `RND_Min_canonic`, `RND_Max_Pos_canonic`,
    `RND_Min_Pos_correct`
  - `RND_Max_Pos_correct`, `RND_Max_canonic`, `RND_Min_correct`,
    `RND_Max_correct`, `RND_EvenClosest_canonic`,
    `RND_EvenClosest_correct`
  - `EvenClosestTotal`, `ClosestTotal`
  - `MinEx`, `MaxEx`, `ClosestRoundedModeP`
  - `ClosestUlp`, `ClosestExp`, `EvenClosestMinOrMax`
  - `EvenClosestRoundedModeP`, `RoundedModeBounded`, `PminPos`,
    `RoundedModeMult`
  - `RoundedModeMultLess`, `RoundedModeMultAbs`, `MinRoundedModeP`,
    `MaxRoundedModeP`
- `FloatSpec/src/Pff/Pff2Flocq.lean`:
  - `Fast2Sum_correct`, `TwoSum_correct`, `Veltkamp_Even`, `Veltkamp`,
    `Veltkamp_tail`
  - `Dekker`, `ErrFMA_bounded`, `ErrFMA_correct`
  - `ErrFMA_bounded_simpl`, `V2_Und5`
  - `ErrFMA_correct_simpl`, `ErrFmaAppr_correct`, `U5_discri1_aux`,
    `U5_discri1`, `discri_correct_test`
  - `discri_fp_test`, `Axpy`
- `FloatSpec/src/Prop/Double_rounding.lean`:
  - `round_round_sqrt_FLX`, `round_round_sqrt_FLT`,
    `round_round_sqrt_radix_ge_4_FLX`,
    `round_round_sqrt_radix_ge_4_FLT`, `round_round_sqrt_FTZ`,
    `round_round_sqrt_radix_ge_4_FTZ`
  - `round_round_div_FLX`, `round_round_div_FLT`,
    `round_round_div_FTZ`
  - `round_round_plus_radix_ge_3_FLX`,
    `round_round_minus_radix_ge_3_FLX`,
    `round_round_plus_radix_ge_3_FLT`,
    `round_round_minus_radix_ge_3_FLT`,
    `round_round_plus_radix_ge_3_FTZ`,
    `round_round_minus_radix_ge_3_FTZ`
  - `round_round_plus_FLX`, `round_round_minus_FLX`,
    `round_round_plus_FLT`, `round_round_minus_FLT`,
    `round_round_plus_FTZ`, `round_round_minus_FTZ`
- `FloatSpec/src/Prop/Round_odd.lean`:
  - `mag_round_odd`, `fexp_round_odd`
  - `round_N_odd_pos`, `round_N_odd`

Current restore blockers found by pipeline attempts:

- `round_N_odd_pos`: the upstream proof depends on the `Odd_prop_aux`
  midpoint stack (`mag_m`, `mag_m_0`, `m_eq`, `m_eq_0`, `fexp_m_eq_0`,
  `Fm`, and `Zm`). These were present only as `sorry`-based spec variants in
  `origin/main`, and are absent as proved Lean declarations on this branch. The
  theorem should stay listed until that stack is ported with real proofs.
- `Bldexp_Bopp_NE`: the Flocq theorem is over finite constructors whose
  mantissa is positive. The current Lean `B754` type admits
  `B754_finite _ 0 _`; with that widened model, `Bldexp RNE (Bopp x) e =
  Bopp (Bldexp RNE x e)` is not valid for all local `B754` values because
  zero-sign behavior can diverge after `real_to_FullFloat`. The proper fix is
  to restore the positive-mantissa invariant in the `B754` model or add an
  equivalent validity precondition before proving the Flocq payload.
- `FnormalizeCanonic`: upstream Flocq's `Fnormalize` maps zero to
  `Float 0 (-dExp b)` and otherwise shifts by
  `min (precision - Fdigit radix p) (Z.abs_nat (dExp b + Fexp p))`. The
  current Lean `Fnormalize` is still identity, so `Fbounded b p ->
  Fcanonic (Fnormalize p)` is false; for example `b = { dExp := 0,
  vNum := 10 }`, `radix = 2`, and `p = ⟨1, 1⟩` is bounded but not canonical.
  The correct fix is to port the real `Fnormalize`/`Fshift` boundedness stack
  (`FnormalizeBounded`, `pGivesDigit`, `digitGivesBoundedNum`,
  `FshiftFdigit`, `FshiftCorrect`, and `FboundedShiftLess`) before proving this
  theorem.
- `ClosestUlp`: upstream Flocq proves this from `ClosestMinOrMax`,
  canonical successor/predecessor facts (`FNSuccCanonic`, `FNPredCanonic`) and
  the real `FulpSuc`/`FulpPred` stack. The current Lean file has
  `FNSucc`/`FNPred` as mantissa `+/- 1` sketches and `Fulp` as the constant
  `1`, so the faithful theorem should remain listed until the normalized
  neighbor and ulp infrastructure is ported.
- `Fast2Sum_correct`: upstream Flocq's theorem is stated in the `FTS` section
  with local algorithm bindings `a := round_flt (x + y)` and
  `b := round_flt (y + round_flt (x - a))`, then proves
  `Rabs y <= Rabs x -> a + b = x + y`. The current Lean file has no local
  `Fast2Sum`/`Fast2Sum_correct` binding, and the upstream proof depends on the
  generic Pff nearest-rounding bridge `pff_round_N_is_round`, `RND_Closest`,
  `RND_Closest_correct`, `RND_Closest_canonic`, and `Pff.Dekker_FTS`. The
  specialized b32/b64 bridges in `Pff2FlocqAux.lean` are not enough to recover
  the generic `emin`/`prec`/`choice` theorem.
- `V2_Und5`: the pipeline attempt restored the surrounding V2 lemmas
  (`mult_error_FLT_ge_bpow'`, `V2_Und2`, and `V2_Und4`) but this final V2
  lower-bound lemma remains blocked on the hard branch where `y ≠ 0`, `u2 ≠ 0`,
  and `u1 + y ≠ 0`. Upstream Flocq uses `F2R_plus`, `Fexp_Fplus`, `F2R_ge`,
  and `cexp_ge_bpow` to propagate a lower bound through nested exact float
  additions before the final round. The local Lean port has low-level pieces,
  but no roundR-facing theorem packaging that nested `Fplus` exponent/lower
  bound propagation. Do not replace this by a weaker theorem; restore the
  float-addition propagation stack first.

Entries removed by this re-audit:

- `one_equiv` and `two_equiv`: these now have theorem declarations in
  `PrimFloat.lean`, so they are no longer missing revert targets.
- `binary_round_aux_correct'`, `binary_round_correct`,
  `binary_normalize_correct`, and `binary_round_aux_correct`: these now have
  theorem declarations in `Binary.lean`. They are still helper-level IEEE
  infrastructure, but no longer belong in the removed-theorem revert list.
- `Bdiv_correct_aux`, `Bfrexp_correct_aux`, and `Bsqrt_correct_aux`: these
  correspond to Flocq `BinarySingleNaN.v` auxiliary lemmas and now have theorem
  declarations in `BinarySingleNaN.lean`. `Bldexp_Bopp_NE` remains listed
  because it is still a `Unit` port gap.
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
- `FLX_round_round_sqrt_hyp` and
  `FLX_round_round_sqrt_radix_ge_4_hyp`: these now have theorem declarations
  and proofs in `Double_rounding.lean`. They restore the upstream FLX
  arithmetic side conditions for the blocked sqrt double-rounding family, with
  the Coq `Prec_gt_0 prec` section assumption explicit. The active
  `round_round_sqrt_*` targets remain listed because the generic
  `round_round_mid_cases`, `mag_sqrt_disj`, `round_round_sqrt_aux`, and
  `round_round_sqrt` stack is still absent as proved Lean infrastructure.

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

- `Fulp`: currently a lightweight ulp model for floats.
- `Fnormalize`: identity-style normalization skeleton.
- `Fshift`: no-op local model over the stored representation.
- `digitAux`: now a fuel recursion over the unary `Positive` compatibility
  wrapper, but still not a literal port of Coq's binary-`positive` recursion.
- public generic skeletons around `isMin`, `isMax`, `MonotoneP`, and
  `MinOrMaxP` that require float-specific hypotheses in downstream proofs.

Why this matters: Pff depends on canonical float normalization, boundedness, and
digit/shift reasoning. These are needed before Pff2Flocq and high-level error
theorems can be trusted as translations rather than executable sketches.

## IEEE Infrastructure

The IEEE layer still has explicit port-gap definitions for correctness payloads.

`Binary.lean`:

- `Bfma_correct`
- `Bminus_correct`
- `Bdiv_correct`
- `Bsqrt_correct`
- `Bnearbyint_correct`
- `Bldexp_correct`

`BinarySingleNaN.lean`:

- `Bldexp_Bopp_NE`

The old local wrappers `binary_*_correct`, `B754_plus_correct`, and
`B754_mult_correct` are not exact Flocq names, so they are not revert targets.
They still point at real IEEE port gaps: the corresponding upstream payloads are
the `Bplus_correct`, `Bmult_correct`, `Bsqrt_correct`, `Bdiv_correct`,
`Bfma_correct`, and `Bminus_correct` families. `Bplus_correct` and
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
