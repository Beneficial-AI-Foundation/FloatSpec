# FLoCq to FloatSpec semantic-alignment repair checklist

Audit date: 2026-09-06

## Pinned audit scope

- FLoCq source: `../sources/flocq`, commit
  `7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`.
- FloatSpec target: this repository, branch `integration`, source-bearing
  repair commit `f8c007d10f3814c3b64048efec08cb26e42a1af7` (based on
  `43065f115fdf4826a3c1408d7b89499d2ba412c7`). The repair was committed
  locally and the worktree was clean at the G1 check; no remote push is part
  of this audit.
- Latest repository-wide judge evidence inspected:
  `../pipeline/runs/flocq-integration-20260827/artifacts/judge-report.md`.
  It compiled, but only 7/5145 judge jobs were valid and its decision was
  `INCOMPLETE`. Its 2459/2548 name-match count is not a semantic-alignment
  score.

## Repair execution status (2026-09-06)

- The implementation work listed in D1-D11, T1-T44, and M1-M5 is complete.
  Public source names expose source-shaped contracts, while compatibility and
  derived-payload endpoints use distinct names.  On the final named-repair
  snapshot, `lake build` passed 3351/3351 jobs and `lake build FloatSpec.Test`
  passed 3359/3359 jobs.
- A structural check found all 60 named sections (D1-D11, T1-T44, M1-M5), with
  zero sections missing an explicit FLoCq/source contract, pre-repair Lean
  mismatch, or required repair.
- After T38 and its caller migration, `lake build floatspec` passed
  6686/6686 jobs and `lake build FloatSpec.Test` passed 3359/3359 jobs on code
  commit `38610f96f72bdb2931eea6f91b9f0e74fe85c576`. The pipeline regression suite
  also passed 158/158 tests after the T38 target-only repair.
- The source and elaborated-environment trust scan found no `sorry`, `admit`,
  `sorryAx`, unauthorized `axiom`/`opaque`/`extern`, unsafe declaration, or
  `implemented_by` escape. Nine generated `native_decide` axioms found by the
  environment scan were replaced with kernel-checked `decide` proofs; the
  rebuilt environment now contains zero axiom declarations. Evidence is in
  `../pipeline/runs/flocq-integration-repair-r2-20260905/artifacts/promotion-report.json`.
  `git diff --check` passed.
- The current post-T38 deterministic pairing plan is
  `../pipeline/runs/flocq-integration-repair-r2-20260905/artifacts/judge-plan.json`.
  Its typed target environment and compile preflight passed; it indexes 5745
  target declarations, creates 5791 jobs, and pairs 2472/2548 source
  declarations. The 76 unmatched records have an exact reviewed ledger at
  `../pipeline/runs/flocq-integration-repair-r2-20260905/manual-audit/source-unmatched-ledger.json`:
  69 non-exported local `FtoRradix` coercions, one exported Pff2 `FtoRradix`
  alias mapped to `FloatSpec.F2R`, two exported `fexp_correct` instances
  mapped to the shared `FLT_exp_valid` result, three Coq numeric-coercion
  registrations mapped to native Lean casts, and the generated `eq_dep_elim`
  scheme mapped to Lean's native dependent equality eliminator. This is
  reviewed pairing/classification coverage, not semantic accuracy for the
  remaining matched declarations.
- The G7 scan found all 17 generic `Prop.Relative` declarations applying their
  bound `rnd` through `Mode.ofRnd`, no `Unit`-to-mode coercion or `round ... ()`
  call in the source tree, and the five concrete floor/ceil/toward-zero/two-tie
  executions in `FloatSpec/Test/RoundingModeSource.lean` compile successfully.
- The matcher now limits module/namespace preference to equal normalized
  basenames, binds a `Source ID` annotation only to the immediately following
  compiler-confirmed declaration, and resolves an exact root environment name
  before namespace-suffix fallbacks. These changes prevent both the prior
  `fexp_correct`/`Bfrexp_correct` false match and the Binary/SingleNaN
  same-basename collision. The audit also rejects generated environment axioms,
  not only lexical `axiom` commands. The pipeline regression suite passes
  158/158 tests.
- The post-T38 plan hashes are source index
  `b63167bfb633c45bebee9b0effb7282974ece811d3eafa84e14e16c4bb872b6b`,
  target index
  `cf4d412ca46e82e47e338ab0fd52ad17c7390887307ce296d0ee21d56923cd98`
  and plan
  `74471270cf767c884006a8d5da85695ea09e26c3d64abc6ba30edb9a8139235d`.
- The post-D10 targeted v24 judge marks `new_location_odd` aligned at 0.99
  confidence; all three examples and all six native Coq/Lean execution chains
  verified. The subsequent full 5741-job subscription run was stopped after
  its `Zsame_sign_imp` result exposed the T37 target gap and a judge false
  positive. A fresh plan and run are required; the stopped run is not a
  repository-wide alignment score.
- The post-T42 stable plan is
  `../pipeline/runs/flocq-alignment-r3-20260906/artifacts/judge-plan.json`.
  It indexes 5907 target declarations, creates 5953 jobs, and pairs 2472/2548
  source declarations.  Its source-index hash is
  `b63167bfb633c45bebee9b0effb7282974ece811d3eafa84e14e16c4bb872b6b`,
  target-index hash is
  `7acb5c7d65bac84f8556cad04967da5aaa6544b9a0ccf769ef7f4ff83b6f37d4`,
  and plan-file hash is
  `8e574e828afd3847f17662ff4602fcea5a500c8b7c1f83c78a13df68c0f16c8e`.
  The v24 subscription smoke rerun marks `Fsqrt_core`, source-facing `boundR`,
  and `Binary.Bfrexp` aligned (0.99, 0.99, and 0.98 confidence), with every
  generated Coq/Lean execution chain compiler-verified.  Manual audit added
  the omitted root-boundary observations: `Fsqrt_core 2 1 0 1` returns exact
  zero on both sides, `boundR 1 0` returns mantissa/exponent `(1,1)` on both
  sides, and finite `Bfrexp` maps the value 1 to significand value 1/2 and
  exponent 1 on the Lean side, matching the evaluated Coq result.  The model's
  original `Bfrexp` examples covered only zero/infinity/NaN, so those examples
  alone would have been insufficient evidence for its finite branch.  The
  complete root-smoke review is
  `../pipeline/runs/flocq-alignment-r3-20260906/manual-audit/post-t42-root-smoke.md`.
- A subsequent 25-job subscription batch produced 28 valid verdicts: 27
  `aligned` and one `not_aligned`, with every generated Coq/Lean execution
  chain verified. Manual review confirmed the `Zdigits_aux` counterexample as
  a true positive and found one false-positive `aligned` verdict for
  `powerRZ_inv`: the judge treated a related total integer-power identity as
  the exact source theorem despite the missing nonzero premise and different
  exported conclusion. Both target declarations are repaired in T43. This
  batch remains incomplete repository evidence, not an alignment score.
- The post-T43 fresh v24 plan is
  `../pipeline/runs/flocq-alignment-r4-20260906/artifacts/judge-plan.json`.
  It indexes 5905 target declarations, creates 5951 jobs, and retains the
  reviewed 2472/2548 source pairing plus the 76-item unmatched ledger. Its
  source-index hash is
  `b63167bfb633c45bebee9b0effb7282974ece811d3eafa84e14e16c4bb872b6b`,
  target-index hash is
  `ffc5592ca517e9e9aaa533bbf78bc3701617c41622fb0c3050809bfb3015de46`,
  and plan-file hash is
  `33093cb11c68fdaf8285ad8e13c11486bb4f07776b17c31180030a974159b65a`.
  Focused subscription reruns mark both repaired items aligned at 0.99
  confidence with three independently verified Coq/Lean observations each.
  Manual review confirms the signed stop/recursive branches for `Zdigits_aux`
  and the exact nonzero interface and conclusion for `powerRZ_inv`; see
  `../pipeline/runs/flocq-alignment-r4-20260906/manual-audit/post-t43-focused.md`.
  The next 25 dependency-ordered jobs also complete successfully: the fresh
  workspace now has 27/27 `aligned` verdicts, 82 accepted examples, and all 82
  source plus 82 target execution chains verified. Manual review finds no
  false positive in this dependency-first batch; the item-by-item record is
  `../pipeline/runs/flocq-alignment-r4-20260906/manual-audit/dependency-batch-001-review.md`.
  This is still only 27/5951 jobs (0.45%), so the judge report remains
  `INCOMPLETE` and cannot close a whole-repository gate.
- The final elaborated-environment trust scan indexes 13100 declarations and
  reports zero explicit axioms, environment axioms, sorries, unsafe
  declarations, and `implemented_by` declarations.  The source tree contains
  no `native_decide`, and `git diff --check` passes. The post-T43 full build
  passes 3351/3351 jobs and `lake build FloatSpec.Test` passes 3359/3359 jobs.
- The repository is **not yet audit-aligned** under the close-out rule below:
  the 2548-item ledger has not received complete human review (G4-G6/G9),
  exhaustive cross-language executions and
  adversarial reproduction are absent (G10-G11), and independent whole-scope
  sign-off is absent (G12). Pff/Pff2 received a separate proof review, but that
  is not whole-repository sign-off.

## What this checklist does and does not certify

Every named declaration in the repair list below was checked against its
FLoCq declaration. Each entry states the concrete contract mismatch and the
required repair. The list contains confirmed necessary repairs; it is not, by
itself, evidence that all 2548 source declarations have already been audited.

The named-entry review was repeated after implementation. Every T-entry below
identifies the original FLoCq contract, the pre-repair Lean difference (either
inline or in its comparison table), and the required semantic repair. D-items
cover shared definition/carrier causes, while M-items cover absent declarations.
The later-discovered canonical-instance leakage is covered by T26/T31 rather
than hidden as an unlisted exception.

Target line numbers in the mismatch descriptions refer to the audited
pre-repair layout and may have shifted after the repairs. Current declarations
should be located by their qualified names and the pinned pairing plan.

“All items in this document are fixed” therefore means both:

1. every named repair is complete; and
2. every completion gate in the final section passes, including a reviewed
   2548/2548 source-declaration alignment ledger with no unresolved item.

Only after both parts pass may this pinned version be called **audit-aligned**
with FLoCq. Even that is an engineering audit claim, not a machine-checked
meta-theorem relating Coq's and Lean's logics. A literal formal guarantee of
whole-repository equivalence would additionally require a verified
cross-language semantics or translation proof.

## Root definition repairs

These are root causes. Fix them before repairing their dependent theorems.

### D1. Preserve the supplied rounding function

- **Source semantics:** `round beta fexp rnd x` applies the caller's `rnd` to
  the scaled mantissa. See `src/Core/Generic_fmt.v` and its use in
  `src/Prop/Relative.v:41-715`.
- **Current Lean:** `FloatSpec/src/Calc/Round.lean` permits `()` as a rounding
  mode; its `Unit` coercion selects nearest-even. The 17 generic declarations
  in `FloatSpec/src/Prop/Relative.lean` bind `rnd` but call `round ... ()`, so
  `rnd` is erased.
- **Observable mismatch:** for radix 2, `FIX_exp 0`, `rnd_floor`, and
  `x = 3/4`, FLoCq rounds to `0`, while the Lean `()` route rounds
  nearest-even to `1`.
- **Repair:** add a mode constructor/bridge whose `rnd` field is the supplied
  function and whose zero law comes from `Valid_rnd`; replace every generic
  `()` call with that bridge. Use an explicit nearest-even mode only for source
  declarations that actually use `ZnearestE`. Remove the public `Unit -> Mode`
  coercion after migration so mode erasure cannot recur silently.

### D2. Make `isMin` and `isMax` source-faithful

- **Source:** `src/Pff/Pff.v:4534-4570` defines `isMin`/`isMax` as bounded
  greatest-lower/least-upper representable floats.
- **Current Lean:** `FloatSpec/src/Pff/Pff.lean:805-809` defines polymorphic
  `isMin`/`isMax` as `fun _ x => forall y, y = x`, which is unrelated and
  usually uninhabited. Correct float-specific definitions exist separately as
  `isMin'`/`isMax'` at lines 813-827.
- **Repair:** rename or remove the polymorphic fallbacks, expose the current
  `isMin'`/`isMax'` semantics under the source names, and migrate all public
  Pff contracts to the source-faithful predicates. Do not compensate by
  copying the predicates' fields into every theorem precondition.

### D3. Use the proof-carrying IEEE `binary_float` at the source boundary

- **Source:** `src/IEEE754/Binary.v:185-230` makes finite mantissas positive
  and carries `bounded m e = true` in the `B754_finite` constructor.
- **Current Lean:** an exact proof-carrying `binary_float` exists at
  `FloatSpec/src/IEEE754/Binary.lean:412-420`, but many source-facing theorems
  instead use permissive `Binary754` at lines 423-429, whose `valid` field
  proves only `True`.
- **Repair:** state FLoCq-facing definitions and theorems on `binary_float`.
  Keep `Binary754` only as a clearly named compatibility carrier and provide a
  checked conversion requiring the missing validity proof.

### D4. Preserve the full IEEE value in `Binary.B2FF`

- **FLoCq:** `src/IEEE754/Binary.v:208` maps every constructor of the
  proof-carrying `binary_float` to the corresponding `full_float` constructor,
  including a NaN's sign and payload.
- **Lean before repair:** `FloatSpec/src/IEEE754/BinarySingleNaN.lean:5160`
  defined `Binary.B2FF x := SF2FF (B2SF x)`.  `single_nan` intentionally has
  only one NaN, so this route erased the source NaN sign and payload.
- **Counterexample:** `B754_nan true p hp` maps in FLoCq to
  `F754_nan true p`; the former Lean definition mapped every such input to
  `F754_nan false 1`.
- **Repair:** erase through the checked `binary_float.toBinary754` bridge,
  whose value is the corresponding `FullFloat`, and retain an `rfl` regression
  on a negative NaN with arbitrary valid payload.

### D5. Complete the proof-carrying `Binary` source surface

- **FLoCq:** `src/IEEE754/Binary.v:192-1428` exposes all ordinary IEEE
  operations on its proof-carrying `binary_float`: the `B2BSN`/`FF2B`/`B2FF`
  representation bridges, `erase`, `Bopp`, `Babs`, `Bcompare`, arithmetic and
  rounding helpers, `Bnearbyint`, `Btrunc`, `Bone`, `Bmax_float`,
  `Bnormfr_mantissa`, `lift`, `Bldexp`, `Bfrexp`, `Bulp`, `Bsucc`, and `Bpred`.
- **Independent `Bfrexp` root mismatch:** the old Lean
  `Bfrexp_correct_aux` returns its input unchanged and assumes the `[1/2,1)`
  bound that FLoCq proves.  Replace it with `Ffrexp_core_binary` over the
  finite constructor's `specFloat_bounded` evidence, deriving output validity,
  normalization (when `2 < emax`), and exact value decomposition.  The public
  Binary `Bfrexp_correct` must derive all three source conclusions without an
  added normalization or validity premise.
- **Lean before repair:** the proof-carrying `namespace Binary` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean:5127-6280` contains `B2R`,
  observers, `B2FF`, arithmetic, `Bopp`, and `Bulp`, but omits the remaining
  public definitions.  Same-named implementations elsewhere in
  `Binary.lean`/`BinarySingleNaN.lean` primarily consume permissive
  `Binary754`, raw `B754`, or the single-NaN carrier; those are not substitutes
  for the source API because they admit values excluded by the source type or
  erase a NaN's sign/payload.
- **Repair:** expose every listed source definition on `binary_float`; reuse
  the existing proof-carrying-to-single-NaN bridges for operations whose
  numeric algorithm is already implemented there, and lift the result back
  while preserving the caller-supplied NaN when the source does.  Keep legacy
  implementations only under compatibility names.  Use the exact lowercase
  `full_float` bridge for `FF2B`/`B2FF`, or prove the embedding into the legacy
  uppercase `FullFloat` observer preserves all source-observable fields.

### D6. Restore the integer-width `IEEE754.Bits` source boundary

- **FLoCq:** `src/IEEE754/Bits.v:33-446` exposes `join_bits`, `split_bits`,
  `bits_of_binary_float`, `split_bits_of_binary_float`, and
  `binary_float_of_bits_aux` over integer widths `mw ew : Z`.
  `binary_float_of_bits_aux` returns `full_float`; the later checked decoder
  converts that value to the proof-carrying `binary_float (mw+1) 2^(ew-1)`.
- **Lean before repair:** `FloatSpec/src/IEEE754/Bits.lean:18-106` changes the
  widths of `join_bits`/`split_bits` to `Nat`; lines 835-879 change the public
  encoder's parameters to `(prec, emax)` and add two typeclass premises; and
  line 563 publishes `binary_float_of_bits_aux` on permissive `Binary754`
  rather than source `full_float`.
- **Observable mismatch:** FLoCq evaluates `join_bits (-1) 1 false 0 3` by
  arithmetic right shift to `1`; the same source input cannot be expressed by
  the Nat-width Lean declaration.  More importantly, the legacy decoder's
  `Binary754.valid` proves only `True`, so it is not the source validity
  certificate.
- **Repair:** keep Nat-width routines as internal/compatibility helpers, but
  expose integer-width source definitions (including negative-width behavior)
  and the exact `full_float` auxiliary decoder.  Prove bridges to the Nat core
  for positive widths and use the proof-carrying decoder at the public source
  boundary.

### D7. Finish the exact `BinarySingleNaN` representation facade

- **FLoCq:** `Bcompare` returns `option comparison`, and the arithmetic
  operations consume the five-constructor source `mode`.  Source conversion
  lemmas are stated on the proof-carrying SingleNaN carrier.
- **Lean before repair:** `BinarySingleNaN.Bcompare` returns `Option Int`; the
  exact operations consume the isomorphic but differently named
  `RoundingMode`; and several source basenames still resolve first to legacy
  raw-`B754`/Hoare declarations.  The facade defines a proved bijection for
  `mode`, but does not expose source-mode operation wrappers or an explicit
  comparison-result bridge.
- **Repair:** expose annotated source-facing wrappers using `mode`, map the
  comparison result to `Ordering` (Coq `comparison`) with a proved inverse on
  `-1/0/1`, and ensure matching resolves source names to the proof-carrying
  declarations.  Reuse the already checked arithmetic; do not duplicate its
  implementation.

### D8. Preserve Coq's positive offset in `plusExp`

- **FLoCq:** `src/Pff/Pff.v:15037` adds
  `Npos (P_of_succ_nat (pred (pred t)))` to `dExp`.  Its integer value is
  `max 1 (t - 1)`, including at the small public inputs `t = 0` and `t = 1`.
- **Lean before repair:** `FloatSpec/src/Pff/Pff.lean:725` added the truncated
  natural subtraction `t - 1`; at `t = 1` and `dExp = 0` it therefore returned
  exponent `0`, while FLoCq returns exponent `1`.
- **Repair:** define the offset as `max 1 (t - 1)`.  Keep the later
  `2 <= t` simplification in theorem proofs, but do not silently strengthen
  the domain of the exported definition.  Retain a concrete `t = 1`
  regression.

### D9. Implement the strict `up` used by `boundR`

- **FLoCq:** `src/Pff/Pff.v:4336` defines
  `boundR r := boundNat (Z.abs_nat (up (Rabs r)))`, where `up x` is the least
  integer *strictly greater* than `x`.
- **Lean before repair:** `FloatSpec/src/Pff/Pff.lean:16950` used
  `Int.ceil |r|`, which agrees away from integers but is not strict at an
  integral input.  At radix 2 and `r = 1`, FLoCq selects `boundNat 2`; the old
  Lean definition selected `boundNat 1`.
- **Repair:** use the strict ceiling `floor |r| + 1`, transported through
  `Int.natAbs`, and prove `boundRCorrect1` from `Int.lt_floor_add_one`.
  Retain the integral-input regression because nonintegral examples do not
  distinguish the two definitions.

### D10. Preserve `new_location_odd` at the public `nb_steps = 1` input

- **FLoCq:** `src/Calc/Bracket.v:463-472` exports `new_location_odd` without
  the later Section hypothesis `1 < nb_steps`.  At `k = 0`, every inexact
  location is mapped to `loc_Inexact Lt`, including when `nb_steps = 1`.
- **Lean before repair:** `FloatSpec/src/Calc/Bracket.lean:1216` special-cased
  `nb_steps = 1` and preserved the input ordering.  Thus input
  `(1, 0, loc_Inexact Gt)` returned `loc_Inexact Lt` in Coq but
  `loc_Inexact Ordering.gt` in Lean.
- **Repair:** remove the target-only `nb_steps = 1` branch from the definition.
  Restore the actual exported `1 < nb_steps` dependency on
  `new_location_even_correct`, `new_location_odd_correct`, and
  `new_location_correct`, migrate their callers, and retain the concrete
  definition-level regression in `FloatSpec/Test/BracketSource.lean`.

### D11. Preserve `make_bound` at negative precision

- **FLoCq:** `src/Pff/Pff2FlocqAux.v:222-228` defines the mantissa bound as
  `Z.to_pos (Zpower beta p)`. The surrounding `1 < p` hypothesis is not used
  by the definition and is absent from `Check @make_bound`; for `beta = 2`,
  `p = -1`, and `E = 0`, the bound therefore has `vNum = 1`.
- **Lean before repair:** `FloatSpec/src/Pff/Pff2FlocqAux.lean:109` used
  `Zpower_nat beta p.natAbs`, so the same negative input returned `vNum = 2`.
- **Repair:** use `1` when `p < 0`, retaining the natural-power path when
  `0 ≤ p`. Keep the source `make_bound_p` theorem under its exported
  `1 < p` context and retain a concrete negative-precision regression in
  `FloatSpec/Test/PffSourceContracts.lean`.

## Confirmed theorem-contract repairs

### T1. `F2R_lt_bpow`

- **FLoCq:** `src/Core/Float_prop.v:369` quantifies `f` and `e'`; from
  `abs(Fnum f) < beta^(e' - Fexp f)` it proves `abs(F2R f) < beta^e'`.
- **Lean:** `FloatSpec/src/Core/Float_prop.lean:844` instead assumes
  `f.Fnum < 0` and proves only `F2R f < beta^f.Fexp`. It has no `e'`, no
  magnitude premise, and no absolute-value conclusion.
- **Why misaligned:** this is an unrelated negative-value bound under the
  source theorem's public name. For example, `(Fnum,Fexp,e') = (1,0,1)` at
  radix 2 satisfies the FLoCq premise and conclusion, but cannot enter the
  Lean theorem because `1 < 0` is false.
- **Repair:** restore the FLoCq statement and proof. Rename the current helper
  to something such as `F2R_lt_bpow_of_neg_mantissa` if it is still useful.

### T2. Six `Core.Ulp` order theorems

FLoCq statements are at `src/Core/Ulp.v:1977-2038`; the Lean declarations are
at `FloatSpec/src/Core/Ulp.lean:405-566`.

| Declaration | FLoCq conclusion | Current Lean conclusion | Required repair |
|---|---|---|---|
| `pred_le` | `pred x <= pred y` | `pred x <= y` | Restore monotonicity of `pred`. |
| `succ_le` | `succ x <= succ y` | `x <= succ y` | Restore monotonicity of `succ`. |
| `pred_le_inv` | `x <= y` | `pred x <= y` | Restore inverse monotonicity. |
| `succ_le_inv` | `x <= y` | `x <= succ y` | Restore inverse monotonicity. |
| `pred_lt` | `pred x < pred y` | `pred x < y` | Restore strict monotonicity. |
| `succ_lt` | `succ x < succ y` | `x < succ y` | Restore strict monotonicity. |

The Lean conclusions are explicitly documented as adaptations and are
strictly weaker than the source contracts. Port the source dependency order
(`generic_format_pred/succ`, `succ_pred`, and `pred_succ`) and keep any weak
inequality only under a different internal name.

### T3. `Fdiv_core_correct`

- **FLoCq:** `src/Calc/Div.v:70` assumes only `0 < m1` and `0 < m2`, then
  proves correctness for both branches of `Fdiv_core`.
- **Lean:** `FloatSpec/src/Calc/Div.lean:114` adds `e <= e1 - e2` and proves
  only that branch. Its direct arguments `Hm1`/`Hm2` are also duplicated in
  the Hoare precondition.
- **Observable mismatch:** `beta=2`, `m1=m2=1`, `e1=e2=0`, `e=1` is admitted
  by FLoCq but rejected by the extra Lean inequality.
- **Repair:** remove the extra exponent precondition and prove both branches
  by splitting on `e <= e1 - e2`. State each source assumption once.

### T4. The 17 generic `Prop.Relative` declarations

**FLoCq:** The following declarations at `src/Prop/Relative.v:41-715` all use
the quantified `rnd`:

- `relative_error_lt_conversion`
- `relative_error_le_conversion`
- `relative_error_le_conversion_inv`
- `relative_error_le_conversion_round_inv`
- `relative_error`
- `relative_error_ex`
- `relative_error_F2R_emin`
- `relative_error_F2R_emin_ex`
- `relative_error_round`
- `relative_error_round_F2R_emin`
- `relative_error_FLX`
- `relative_error_FLX_ex`
- `relative_error_FLX_round`
- `relative_error_FLT`
- `relative_error_FLT_F2R_emin`
- `relative_error_FLT_F2R_emin_ex`
- `relative_error_FLT_ex`

**Lean before repair:** Their counterparts at
`FloatSpec/src/Prop/Relative.lean:19-1540` evaluated `round ... ()`. Each
therefore proved a nearest-even fact while advertising an arbitrary valid
`rnd`.

**Repair:** Route all 17 through D1, and add executed floor, ceil,
toward-zero, and two distinct nearest tie-breaker cases. A source declaration
using a fixed nearest mode must not be mechanically changed to arbitrary
rounding.

### T5. `RleBoundRoundl` and `RleBoundRoundr`

- **FLoCq:** `src/Pff/Pff.v:7008` and `:7026` require `RoundedModeP b radix P`.
- **Lean:** `FloatSpec/src/Pff/Pff.lean:925` and `:963` require the different
  `RoundedModeP_full`, including projector fields supplied by the caller.
- **Why misaligned:** the source derives projector and compatibility facts
  from `RoundedModeP`; Lean exposes proof payload as a stronger public
  precondition.
- **Repair:** use D2's source `RoundedModeP` and derive the needed projector
  lemmas internally.

### T6. `FNoddEq` and `FNevenEq`

- **FLoCq:** `src/Pff/Pff.v:5133` and `:5149` require boundedness of `f1` and
  `f2`, real-value equality, and the parity premise.
- **Lean:** `FloatSpec/src/Pff/Pff.lean:9145` and `:9177` replace boundedness
  with `Fcanonic'` for both inputs. The comments still claim
  `Fnormalize = id`, although the current file has a real `Fnormalize` and
  its correctness, boundedness, and canonicity theorems.
- **Repair:** restore the two boundedness premises and reproduce the source
  proof through `FnormalizeCorrect`, `FnormalizeCanonic`, and
  `FcanonicUnique`.

### T7. `ClosestMinEq` and `ClosestMaxEq`

- **FLoCq:** `src/Pff/Pff.v:8171` and `:8206` take `isMin`, `isMax`, midpoint
  strictness, and `Closest`.
- **Lean:** `FloatSpec/src/Pff/Pff.lean:10103` and `:10141` discard those
  predicates and instead ask the caller for selected inequalities, the
  `min-or-max` disjunction, and one distance comparison.
- **Why misaligned:** the public theorem assumes consequences that the source
  theorem derives; it no longer accepts source-shaped hypotheses.
- **Repair:** state the exact four source predicates/conditions using D2 and
  derive the current arithmetic core internally.

### T8. `RleMinR0`, `RleMaxR0`, `RleRoundedR0`, and `RleRoundedLessR0`

- **FLoCq:** `src/Pff/Pff.v:6672-6730` uses only source `isMin`, `isMax`, or
  `RoundedModeP` plus the sign premise and rounding witness.
- **Lean:** `FloatSpec/src/Pff/Pff.lean:12934-13108` uses the invalid generic
  `isMin`/`isMax` and asks separately for their GLB/LUB fields, boundedness,
  `vNum` positivity, monotonicity, or a sign-preservation theorem.
- **Repair:** migrate to D2's concrete predicates and remove every duplicated
  or derived premise. Rebuild the zero-witness argument and rounded-mode case
  split inside the proofs.

### T9. `div2IsBetweenPos` and `div2IsBetween`

- **FLoCq:** `src/Pff/Pff.v:6852` and `:6915` require bounded `p` and the
  `isMin`/`isMax` witnesses around `p/2` (plus nonnegativity for the positive
  variant).
- **Lean:** `FloatSpec/src/Pff/Pff.lean:10976` and `:11033` additionally demand
  expanded GLB/LUB fields and two bounded residual witnesses.
- **Repair:** expose only the source premises. Derive the residual witnesses
  with the translated `PminPos`, `PmaxPos`, and Sterbenz chain; keep
  `div2IsBetween_from_extrema` internal if useful.

### T10. Signed `RND_Min`/`RND_Max` wrapper theorems

Affected declarations:

- `RND_Min_canonic`: FLoCq `src/Pff/Pff.v:27594`, Lean
  `FloatSpec/src/Pff/Pff.lean:8614`
- `RND_Max_canonic`: FLoCq `:27617`, Lean `:8647`
- `RND_Min_correct`: FLoCq `:27602`, Lean `:8682`
- `RND_Max_correct`: FLoCq `:27625`, Lean `:8753`

The FLoCq theorems derive signed canonicity/correctness from section
assumptions and the positive-rounding theorems. Lean instead asks callers for
two universal positive-branch canonicity or correctness functions. Those are
the proof being translated, not source inputs. The current file now contains
the needed `RND_Min_Pos_*` and `RND_Max_Pos_*` results later in declaration
order.

Source-shaped closed versions now exist at lines 53153-53249.

**Repair:** rename the four early payload-bearing declarations to
`_from_positive_payload` helpers and publish the corresponding `_closed`
statements under the FLoCq names. Preserve only actual FLoCq section
assumptions in the public contracts.

### T11. `FmaErr_aux` and `FmaErr`

- **FLoCq:** `src/Pff/Pff.v:24770` and `:24902` derive
  `a*x+y = r1+ga+al2` from the section's rounded-operation, normal/canonical,
  exponent, boundedness, and `P1`/`P2` assumptions.
- **Lean:** `FloatSpec/src/Pff/Pff.lean:27816` and `:27982` replace that route
  with numerous already-expanded value equalities/`Closest` witnesses and,
  critically, an explicit `be2 = 0` or bounded correction-witness split. The
  latter is the missing `gaCorrect` construction in the source proof.
- **Why misaligned:** the caller must supply the hard intermediate result that
  FLoCq proves. The extra existential packaging in the Lean conclusion does
  not repair the weakened input contract.
- **Repair:** restore the source section assumptions, complete `gaCorrect` and
  its midpoint/boundedness chain, and make the correction split internal.

### T12. `Veltkamp_Even`, `Veltkamp`, and `Veltkamp_tail`

- **FLoCq:** `src/Pff/Pff2Flocq.v:382`, `:473`, and `:545` define their
  algorithmic intermediates with local `Let`s, build Pff witnesses, and derive
  the reduced rounding/tail results.
- **Lean:** `FloatSpec/src/Pff/Pff2Flocq.lean:1466-1533` accepts `hx`/`tx` as
  free inputs and requires `hReduced` or `hTail`, which are the substantive
  lower-Pff conclusions.
- **Repair:** restore the source-shaped local definitions and hypotheses; use
  the now-available lower Pff Veltkamp theorem chain internally. Do not expose
  `hReduced` or `hTail` in the public contract.

### T13. `Dekker`

- **FLoCq:** `src/Pff/Pff2Flocq.v:729` proves the general product correction
  and error bound (under the source radix/parity condition).
- **Lean:** `FloatSpec/src/Pff/Pff2Flocq.lean:1794` proves only the zero-product
  implication and returns a package of bounded/canonical rounding witnesses;
  its own comment says the lower Pff error-bound payload is missing.
- **Repair:** port/call the lower Pff `Dekker` payload and restore the source
  conclusion for arbitrary valid `x` and `y`. Keep witness packaging private.

### T14. `ErrFmaAppr_correct`

- **FLoCq:** `src/Pff/Pff2Flocq.v:1584` uses the complete `Und1` through
  `Und5` hypotheses and proves the unconditional FMA approximation bound.
- **Lean:** `FloatSpec/src/Pff/Pff2Flocq.lean:4362` takes only `Und1`, proves
  the error bound only under `a*x = 0`, and exports intermediate witnesses.
- **Repair:** restore all five source underflow hypotheses, finish the lower
  Pff `ErrFmaApprox` chain, and prove the unconditional source bound. Keep the
  zero-product result as a private branch lemma.

### T15. `Axpy`

- **FLoCq:** `src/Pff/Pff2Flocq.v:1767` assumes formatted `ta`, `tx`, `ty` and
  numerical conditions `H1`/`H2`, defines `tv`, constructs witnesses, and
  proves that `tv` is the down- or up-rounding of `y+a*x`.
- **Lean:** `FloatSpec/src/Pff/Pff2Flocq.lean:4620` accepts free `tv`/`ftv`,
  their value equality, and the final `MinOrMax` payload. It omits the source
  `Fta`/`Ftx`/`Fty`, `H1`, and `H2` route that derives that payload.
- **Repair:** restore the source inputs and local `tv`; complete/call Pff
  `Axpy_opt` internally. Retain `Axpy_from_min_or_max` only as an internal
  bridge.

### T16. `ErrFMA_correct` and `ErrFMA_correct_simpl`

- **FLoCq:** `src/Pff/Pff2Flocq.v:1054` and `:1472` derive the exact
  reconstruction equality from formatted `a`/`x`/`y`, the locally defined
  rounding algorithm, and the corresponding non-underflow hypotheses.
- **Lean:** `FloatSpec/src/Pff/Pff2Flocq.lean:2957` and `:3980` take
  `hcore : a*x+y = r1+gamma+alpha2`, the substantive result supplied by the
  lower `FmaErr` proof, and perform only the final algebraic split.
- **Why misaligned:** the hard conclusion is an input; the source formatting
  and non-underflow route is absent from the public contract.
- **Repair:** after T11, state both declarations with their exact FLoCq
  section assumptions and construct `hcore` internally. Rename the current
  algebraic wrappers to `_from_core_equality` helpers.

### T17. `discri_correct_test` and `discri_fp_test`

- **FLoCq:** `src/Pff/Pff2Flocq.v:2018` and `:2361` take formatted `a`, `b`,
  `c`, define the complete discriminant algorithm locally, and use `U1`,
  `U2`, and `Zd` to prove the final two-ULP error bound.
- **Lean:** `FloatSpec/src/Pff/Pff2Flocq.lean:5428` and `:5457` instead ask
  callers for a final Pff result `fd`, its value/boundedness proofs, and the
  already-established Pff error bound `hdelta`.
- **Why misaligned:** the entire algorithm-to-error-bound proof has become an
  input to a conversion lemma under the source theorem names.
- **Repair:** restore both source-shaped algorithms and hypotheses, construct
  the Pff witnesses and `hdelta` internally, and retain
  `discri_bound_from_pff_delta` only as the final private bridge.

### T18. IEEE theorems weakened by `Binary754`

Affected declarations:

- `B2R_inj`: FLoCq `src/IEEE754/Binary.v:392`, Lean
  `FloatSpec/src/IEEE754/Binary.lean:656`
- `abs_B2R_le_emax_minus_prec`: FLoCq `:822`, Lean `:4039`
- `abs_B2R_lt_emax`: FLoCq `:831`, Lean `:4154`

FLoCq's proof-carrying `binary_float` makes representation validity part of
the value. Lean states these theorems on permissive `Binary754`: `B2R_inj`
therefore asks for mantissa positivity and equal exponents, while both bound
theorems ask for a new `Binary754_bounded` hypothesis. These are not source
premises.

**Repair:** apply D3 and state the public results on proof-carrying
`binary_float`. Rename any compatibility lemmas on `Binary754` to names that
advertise their added assumptions.

### T19. `ClosestErrorBound` and `FmultRadixInv`

- **`ClosestErrorBound`:** FLoCq `src/Pff/Pff.v:8804` assumes bounded `p`,
  `Closest ... x p`, and `q = x - p`. Lean
  `FloatSpec/src/Pff/Pff.lean:10659` additionally requires
  `2 * |x - F2R p| <= beta ^ p.Fexp`, which is the result of the source
  proof's `ClosestUlp`/`FulpLe` chain. Remove that derived bound from the
  precondition and establish it inside the theorem.
- **`FmultRadixInv`:** FLoCq `src/Pff/Pff.v:8761` assumes bounded `x`,
  `Closest ... y z`, and `F2R x / 2 < y`. Lean
  `FloatSpec/src/Pff/Pff.lean:10690` additionally requires a bounded float
  `w` between `F2R x / 2` and `y`; FLoCq constructs that witness using
  `MinEx`, `MaxEx`, and `div2IsBetween`. Remove the existential input and
  construct it internally. The separately expanded fields of `Closest` are
  redundant and should also be removed from the public contract.

Both Lean declarations currently accept a proof result as an input, so they
do not cover every source-valid invocation. Their current arithmetic bodies
may remain as private `_from_bound`/`_from_witness` helpers.

**Repair:** Remove the derived bound/witness inputs from both public source
names, construct them internally through the cited FLoCq dependency chains,
and retain only descriptively named payload helpers.

### T20. Pff uniqueness, monotonicity, underflow, and scaling payloads

- **`EvenClosestUniqueP`:** FLoCq `src/Pff/Pff.v:8484` proves
  `UniqueP radix EvenClosest` from the section assumptions. Lean
  `FloatSpec/src/Pff/Pff.lean:11417` additionally asks for two universal
  uniqueness functions (`hEvenUnique` and `hRealUnique`) that contain the
  difficult cases of the source proof. Derive them from `MinOrMax`, canonical
  uniqueness, and odd/even exclusion inside the theorem.
- **`EvenClosestMonotone2`:** FLoCq `src/Pff/Pff.v:19309` assumes `p <= q`
  and the two `EvenClosest` judgments. Lean
  `FloatSpec/src/Pff/Pff.lean:11208` additionally requires
  `MonotoneP_float EvenClosest` and `UniqueP EvenClosest`, precisely the two
  results used internally by the source proof. Call the translated
  `EvenClosestMonotone` and repaired `EvenClosestUniqueP` instead of accepting
  them from the caller.
- **`AddExpGeUnderf` and `AddExpGeUnderf2`:** FLoCq
  `src/Pff/Pff.v:22311` and `:22341` derive the nonzero rounded-sum witness by
  invoking `plusExactExp`. Lean `FloatSpec/src/Pff/Pff.lean:11547` and
  `:11648` require that witness through `hPlusExact`. Remove `hPlusExact` from
  both public contracts and complete/call `plusExactExp` internally; retain
  the actual FLoCq section assumptions.
- **`RoundedModeMultAbs`:** FLoCq `src/Pff/Pff.v:6940` assumes
  `RoundedModeP`, `P r q`, bounded `q'`, and the absolute input bound. Lean
  `FloatSpec/src/Pff/Pff.lean:12537` additionally asks for both directional
  scaling theorems and both sign-preservation theorems as higher-order
  premises. Derive those four results from the repaired source
  `RoundedModeP` chain inside the theorem.

These are contract mismatches, not merely proof-style differences: each Lean
statement has additional hypotheses that a caller of the corresponding FLoCq
theorem never supplies.

### T21. Nearest-rounding wrappers published under source names

Affected source names and payload-bearing Lean declarations:

- `RND_Closest_canonic`: FLoCq `src/Pff/Pff2FlocqAux.v:57`, Lean
  `FloatSpec/src/Pff/Pff.lean:8849`
- `RND_Closest_correct`: FLoCq `src/Pff/Pff2FlocqAux.v:70`, Lean
  `FloatSpec/src/Pff/Pff.lean:9404`
- `RND_EvenClosest_canonic`: FLoCq `src/Pff/Pff.v:27658`, Lean
  `FloatSpec/src/Pff/Pff.lean:8918`

FLoCq derives lower/upper canonicity or correctness from its section
assumptions. The three early Lean theorems instead require those derived
lower/upper results in their preconditions. Source-shaped closed versions now
exist as `RND_Closest_canonic_closed` (line 53282),
`RND_Closest_correct_closed` (line 53310), and
`RND_EvenClosest_canonic_closed` (line 58121).

**Repair:** rename the early payload lemmas to `_from_min_max` helpers and put
the corresponding source theorem names on the closed statements. The later
`RND_EvenClosest_correct` at line 58152 is already the closed, source-shaped
contract and is not a repair item.

### T22. Lower-Pff discriminant theorem chain

- **FLoCq:** `src/Pff/Pff.v` proves `discri1` through `discri16` and the final
  `discri` from their section hypotheses.  In particular, Discriminant7
  `discri16` (line 22619) derives all special-case and normalization branches,
  and Discriminant5B `discri` (line 22936) accepts bounded intermediates,
  no-underflow/normality facts, and the actual branch rounding equations.
- **Lean before repair:** the public declarations `discri1`--`discri16` and
  `discri` around `FloatSpec/src/Pff/Pff.lean:41797-53560` expose one or more
  internal proof products as caller inputs: ulp-comparison disjunctions,
  residual witnesses, branch-dispatch payloads, normalized
  `discri14_precondition`, or `discri15_precondition`.  The final Lean
  `discri` also has the wrong Discriminant7 `u`/`v` parameterization rather
  than the source Discriminant5B contract.
- **Why misaligned:** a source-valid call has no term of these internal
  payload types; accepting one assumes the proof step the theorem is meant to
  establish.  This blocks the source-shaped Pff2 `discri_correct_test` and
  `discri_fp_test` proofs.
- **Repair:** suffix payload consumers with `_from_*_payload`; restore every
  source name with its exact section contract; derive branch, residual,
  normalization, zero-case, and ulp-comparison facts internally.  The public
  Discriminant5B `discri` and Discriminant7 `discri16` must remain distinct and
  must be sufficient for the two Pff2 source proofs without added premises.

### T23. `EvenClosestTotal`

- **FLoCq:** `src/Pff/Pff.v:8371` derives totality from the section assumptions
  `1 < radix`, `1 < precision`, and `vNum = radix^precision`.
- **Lean before repair:** `FloatSpec/src/Pff/Pff.lean:31810` additionally asks
  callers for `1 < b.vNum` and a universal `boundR` exponent inequality.
- **Repair:** derive `1 < b.vNum` from the power equation, and derive the
  exponent inequality from `b.dExp_nonneg` and the nonnegative exponent of
  `boundNat`; expose only the source section assumptions.

### T24. `EvenClosestRoundedModeP`

- **FLoCq:** `src/Pff/Pff.v:8474` closes the exact source `RoundedModeP` by
  composing `EvenClosestTotal`, `EvenClosestCompatible`,
  `EvenClosestMinOrMax`, and `EvenClosestMonotone`.
- **Lean before repair:** `FloatSpec/src/Pff/Pff.lean:11459` asks for
  `TotalP EvenClosest` and concludes the legacy `RoundedModeP_float`, whose
  compatibility component is structural equality rather than equality of
  represented values.
- **Repair:** retain that composition helper only as
  `EvenClosestRoundedModeP_from_total`; publish a source-shaped theorem that
  derives totality and the value-compatible parity transport internally and
  concludes the exact `RoundedModeP`.

### T25. Pff2 helper contracts used by the discriminant proofs

- **`C_format`:** FLoCq `src/Pff/Pff2Flocq.v:354` is radix-polymorphic and
  proves formatting of `bpow beta s + 1`; Lean had fixed beta to two and used
  a Nat-power surrogate.  Generalize it to `[ValidRadix beta]` and the exact
  `bpow` conclusion.
- **`format_d_discri2`:** FLoCq `src/Pff/Pff2Flocq.v:2352` branches on the
  comparison of the *rounded* `p+q` and `3*abs(round(p-q))`; Lean copied the
  Discri1 comparison of the unrounded expressions.  Restore the actual
  algorithm condition.

**Repair:** Generalize `C_format` and restore `format_d_discri2`'s rounded
branch condition exactly as specified above; neither public theorem may retain
the pre-repair surrogate.

### T26. Theorems over the complete proof-carrying IEEE surface

- **FLoCq:** `src/IEEE754/Binary.v:230-1428` proves representation,
  finiteness, sign, NaN, comparison, rounding, nearby-integer, scaling,
  decomposition, ulp, successor, and predecessor contracts directly for
  `binary_float`.  Examples include `B2SF_B2BSN`, `B2R_B2BSN`,
  `B2FF_FF2B`, `FF2B_B2FF`, `Bcompare_correct`, `Bnearbyint_correct`,
  `Bldexp_correct`, `Bfrexp_correct`, `Bsucc_correct`, and `Bpred_correct`.
- **Lean before repair:** many same-named declarations are proved only for
  permissive `Binary754`/raw `B754`; the proof-carrying namespace has only a
  subset of the source contracts.  A theorem on the wider carrier with an
  added boundedness/positivity premise is not the source theorem, and a
  single-NaN result cannot establish sign/payload behavior for arbitrary
  source NaNs. A post-repair signature audit also found canonical FLT
  `Valid_exp`/`Monotone_exp` instances exposed by `Bmult_correct`,
  `Bplus_correct`, `Bone_correct`, `Bldexp_correct`, `Bulp_correct`,
  `Bsucc_correct`, `Bpred_correct`, and the rounding/normalization contracts;
  FLoCq derives these instances from `Prec_gt_0` instead of asking callers for
  them.
- **Repair:** publish every exported theorem at the proof-carrying boundary
  established by D5, with exactly the FLoCq premises and conclusion.  Derive
  boundedness and payload validity from constructors, and use explicit proved
  bridges to reuse the existing single-NaN numeric results.  Suffix legacy
  wider-carrier statements with `_compat`; do not leave a compatibility
  contract under a source theorem name. Synthesize canonical FLT instances
  internally in every source-facing definition and theorem.

### T27. Exact `BinarySingleNaN` operation and observer contracts

- **FLoCq:** `src/IEEE754/BinarySingleNaN.v` exports `Bopp` and its observer
  laws (`Bopp_involutive`, `B2R_Bopp`, `is_nan_Bopp`, `is_finite_Bopp`,
  `is_finite_strict_Bopp`, and `Bsign_Bopp`) and the SingleNaN arithmetic
  operations/contracts `Bmult_correct`, `Bplus_correct`, `Bminus_correct`,
  `Bfma_correct`, `Bdiv_correct`, `Bsqrt_correct_aux`, and `Bsqrt_correct` on
  the proof-carrying SingleNaN carrier.
- **Lean before repair:** numeric helpers existed on raw `B754`, while
  same-named arithmetic theorems were primarily the `Binary.v` surface with
  caller-supplied NaN handlers.  The qualified `BinarySingleNaN` namespace
  did not expose the six source arithmetic contracts; using the Binary
  theorems also adds a handler that cannot be constructed at every
  source-valid precision. The old `ExperimentalSingleNaNArithmetic`
  `Bsqrt_correct_aux` additionally assumed the desired rounded square-root
  equality and returned its input instead of executing `SFsqrt_core_binary`
  followed by `binary_round_aux`.
- **Boundary counterexample:** the source permits `prec = 1`.  Requiring a
  Binary NaN handler is not a harmless bridge there: the payload validity
  predicate need not admit a Binary NaN, while SingleNaN has its intrinsic
  unique NaN constructor.
- **Repair:** implement the exact SingleNaN operations without an added NaN
  policy argument, prove their source contracts for every source-valid
  precision, and expose the missing observer laws in the qualified namespace.
  Reuse the checked normalization/division/square-root cores internally; do
  not strengthen the public contracts with finiteness assumptions absent from
  `Bmult_correct`, `Bdiv_correct`, or `Bsqrt_correct`. Reconstruct
  `Bsqrt_correct_aux` from the source algorithm and bounded input alone; the
  rounded result must be a conclusion, never a premise.

### T28. Complete the `BinarySingleNaN` source surface, not only arithmetic

- **FLoCq:** `src/IEEE754/BinarySingleNaN.v:424-3671` continues beyond the
  arithmetic operations covered by T27. Its public API also contains the
  proof-carrying SingleNaN versions of `erase`, `Babs`, `Bcompare`, the
  bounded-value lemmas, `binary_round_aux`, `binary_round`,
  `binary_normalize`, `Bnearbyint`, `Btrunc`, `Bone`, `Bmax_float`,
  `Bnormfr_mantissa`, `Bldexp`, `Bfrexp`, `Bulp`, `Bsucc`, and `Bpred`, with
  their observer and correctness theorems.
- **Lean before repair:** the qualified `BinarySingleNaN` namespace exposes
  observers and the T27 arithmetic subset, but the remaining source names are
  resolved by the judge to either `Binary.*` declarations on the distinct
  arbitrary-payload carrier or root/`ExperimentalSingleNaNArithmetic`
  declarations on the proof-erased raw `B754`. In particular,
  `Binary.Babs` and `Binary.Bnearbyint` add NaN-handler inputs absent from
  `BinarySingleNaN.v`; `Binary.Bfrexp` returns the full Binary carrier; and
  the experimental `Bsucc_correct`/`Bpred_correct` conclusions observe raw
  `B754` results rather than return the source proof-carrying result.
- **Why misaligned:** unique-NaN and arbitrary-payload IEEE carriers are not
  interchangeable public domains. A proof about the full Binary operation
  can depend on a caller-selected NaN result, while the source operation has
  one intrinsic NaN and no policy argument. Conversely, erasing an output's
  boundedness proof does not implement the source result type.
- **Repair:** publish every remaining source definition and theorem on
  `BinarySingleNaN.binary_float`; reuse the already proved SingleNaN rounding,
  normalization, decomposition, successor, and predecessor cores through
  transparent bridges. Define the simple constructor operations directly.
  No public source name may add a NaN handler, return raw `B754`, or consume a
  boundedness/correctness payload that the source constructor already carries.

### T29. Integer comparison graph specifications in `Core/Zaux`

- **FLoCq:** `src/Core/Zaux.v` defines `Zeq_bool_prop`, `Zle_bool_prop`,
  `Zlt_bool_prop`, and `Zcompare_prop` as inductive graphs, and its four
  corresponding `*_spec` theorems relate the actual integer comparison result
  to those graphs.
- **Lean before repair:** `Zeq_bool_spec`, `Zle_bool_spec`, and
  `Zlt_bool_spec` were Hoare wrappers around unrelated checker values, while
  `Zcompare_spec` was a behavioral wrapper; the four graph types were absent.
  A fuzzy match even paired the missing integer graphs with similarly named
  real-comparison graphs from `Core/Raux`.
- **Why misaligned:** proving that a locally defined checker returns its own
  value does not connect `Zeq_bool`, `Zle_bool`, `Zlt_bool`, or `Int.compare`
  to the source graph. The real graph types quantify over a different domain
  and cannot witness the integer specification.
- **Repair:** restore all four inductive graph definitions and constructors,
  and state each `*_spec` theorem over the actual integer comparison. Keep any
  behavioral Hoare wrapper only under a distinct compatibility name.

### T30. `IEEE754.Bits` source theorem contracts

- **FLoCq:** `join_bits_range`, `split_join_bits`, `join_split_bits`, and
  `split_bits_inj` quantify integer widths.  The encoder/decoder theorems
  `split_bits_of_binary_float_correct`, `bits_of_binary_float_range`,
  `binary_float_of_bits_aux_correct`,
  `binary_float_of_bits_of_binary_float`, and
  `bits_of_binary_float_of_bits` use the proof-carrying carrier and the exact
  derived precision/exponent parameters.
- **Lean before repair:** the first four contracts use Nat widths; the public
  encoder theorems at lines 1640-1849 use permissive `Binary754` and the
  `(prec, emax)` compatibility encoder; and the old auxiliary-correctness
  theorem is a self-returning Hoare wrapper rather than `valid_binary = true`.
- **Repair:** publish the exact integer-width theorem statements and close
  them through D6's bridges.  Rename the wider-carrier results as compatibility
  theorems.  Add binary32/binary64, NaN-payload, subnormal, normal, infinity,
  signed-zero, and round-trip executions.

### T31. Remaining `BinarySingleNaN` source-interface contracts

- **`Bsign_SF2B`:** FLoCq `src/IEEE754/BinarySingleNaN.v:343` proves the sign
  equality for every valid `StandardFloat`, including its unique NaN.  Lean
  adds `is_nan_SF z = false`; remove that unnecessary premise and close the
  NaN case directly.
- **`Bcompare` and arithmetic modes:** publish source-shaped results through
  D7's `comparison` and `mode` bridges.  The public wrappers must require only
  FLoCq's `Prec_gt_0`/`Prec_lt_emax`; `Valid_exp` and `Monotone_exp` are
  canonical derived instances and must not become caller-supplied payloads.
- **Legacy collisions:** add checked source-target annotations or exact
  namespace wrappers for the conversion/observer names that otherwise match
  permissive raw-carrier declarations.  A same-name Hoare theorem over raw
  `B754` is not the source theorem.

**Repair:** Apply all three interface corrections above: remove the extra
`Bsign_SF2B` premise, expose source-mode/comparison bridges without canonical
instance payloads, and make every source basename resolve to the exact
proof-carrying declaration.

### T32. `Pff2FlocqAux` source-facing bridge contracts

- **FLoCq:** `pff_format_is_format` takes the section equalities
  `pGivesBound` and `precisionNotZero`, then only a Pff float and its
  `Fbounded` proof. `round_NE_is_pff_round_b32` and
  `round_NE_is_pff_round_b64` each quantify only the real input and return a
  canonical `EvenClosest` Pff witness.
- **Lean before repair:** `pff_format_is_format` additionally exposed a
  derivable `Prec_gt_0` instance and repeated all section inputs inside a
  Hoare precondition. The b32/b64 declarations added an unused arbitrary
  `rnd : ℝ → Int` and a concrete precision class, and returned a weaker
  compatibility witness without the source `EvenClosest` field.
- **Repair:** preserve those Hoare endpoints under descriptive compatibility
  names. Publish direct source-shaped theorems, derive precision and radix
  facts internally, and obtain the exact `Fcanonic`/`EvenClosest`/value triple
  from the already proved generic bridge.

### T33. `Round_odd` FLT section contracts

- **FLoCq:** `mag_round_odd` and `fexp_round_odd` are exported from
  `Odd_propbis` with only an even-radix hypothesis and `1 < prec`; radix
  validity belongs to `beta : radix`, while `Prec_gt_0`, `Valid_exp`, and
  `Exists_NE` are derived inside the proofs.
- **Lean before repair:** both source names additionally required
  `Prec_gt_0`, `1 < beta`, an existential evenness witness, and an explicit
  `Exists_NE` proof. These are proof payloads derived by the Coq theorem, not
  caller inputs.
- **Repair:** retain the existing proof bodies as explicit-payload helpers and
  expose source-shaped wrappers that accept `beta % 2 = 0` and `1 < prec`,
  synthesize the FLT facts locally, and conclude over the source `roundR`
  operator.

### T34. Remaining early-Pff source contracts

The exhaustive `Pff.v`/`Pff.lean` declaration sweep found the following
source names still attached to strengthened or representation-leaking Lean
contracts.  Every row names the exact mismatch; none may be dismissed merely
because its extra premise is derivable.

| Public source name(s) | Lean-before-repair mismatch | Required repair |
|---|---|---|
| `ClosestMinOrMax`, `ClosestMonotone`, `EvenClosestMinOrMax`, `EvenClosestMonotone` | Returned Lean-only `*_float` predicate aliases and split the single source radix into an operational and an inert radix argument. | Keep the split-radix form as a payload helper; publish the source predicate and one radix, with `beta = radix` at the representation bridge. |
| `ClosestZero` | Repeated boundedness and the universal distance-minimality fields already contained in `Closest`, while omitting the exported `precision`, `1 < precision`, and `vNum = radix^precision` context used by `ClosestRoundedModeP`. | Destructure `Closest`, derive its fields internally, and restore the actual exported precision section. |
| `ClosestIdem`, `ClosestZero1` | Repeated boundedness and the universal distance-minimality fields already contained in `Closest`; `ClosestZero1` also replaced source section facts by derived numeric premises. | Destructure `Closest` and derive the numeric facts internally. |
| `ClosestExp`, `ClosestErrorExpStrict` | Accepted respectively the output of source `ClosestUlp` and the output of source `ClosestExp` as hypotheses. | Invoke those translated lemmas inside source-shaped wrappers. |
| `mBFadic_correct1` | Replaced the source pair of strict sentinel bounds with the exponent upper bound that the Coq proof derives from them. | Derive the exponent bound from the two source inequalities before calling the payload proof. |
| `mBFadic_correct3`, `mBFadic_correct4` | Exposed derived `1 < vNum` and `boundR` exponent facts absent from the FMinMax section contract. | Derive them from the power equation and `Fbound` invariants. |
| `FboundedFzero` | Added positivity already stored by `Fbound`. | Read the record invariant internally. |
| `FcanonicLeastExp` | Added bound positivity while omitting the actual exported precision, nonzero-precision, and power-equation section used by `FnormalizeCanonic`. | Restore the source section and read bound positivity internally. |
| `FnormalNotZero` | Added an integer radix, `0 < vNum`, and a mantissa-product bound already supplied by `Fnormal`. | Use the radix indexed by the float and destruct `Fnormal`. |
| `FsubnormalFexp`, `FsubnormalUnique`, `FsubnormalLt` | Repeated exponent equalities supplied by `Fsubnormal`; `FsubnormalFexp` literally assumed its own conclusion. | Project the equalities from the source predicates. |
| `MaxFloat`, `maxMax`, `maxMax1` | `MaxFloat` added an unused exponent, an exponent bound, and repeated boundedness; `maxMax`/`maxMax1` repeated `Fbounded'`. | Publish only the quantified values and hypotheses in the corresponding Coq declarations. |
| `FexpGeUnderf` | Changed source Nat precision to Int, omitted part of the source precision section, repeated boundedness, and exposed a casted power surrogate. | Restore the source Nat precision and section assumptions, deriving the generalized payload internally. |
| `pGeUnderf`, `qGeUnderf` | Added `TotalP EvenClosest`, which FLoCq obtains from `EvenClosestTotal`, and left the binary radix implicit in a wider interface. | Fix the source radix 2 contract and construct totality internally. |

**Repair:** every strengthened body above must have a descriptive
`_from_*_payload` name, while the exact source name denotes the repaired
wrapper.  Add a compile-time `#check` for every public name.

### T35. Pff proof-stage payloads in Dekker, FMA, and ulp lemmas

These declarations had correct-looking conclusions but asked the caller for
facts constructed by the corresponding FLoCq proof:

| Public source name(s) | Lean-before-repair mismatch |
|---|---|
| `dExpPrim` | Added `0 <= dExp`, already a bound-record invariant, while omitting the `4 <= t` premise present in the actual exported Coq constant. |
| `NormalbPrim` | Added `0 <= dExp`, already a bound-record invariant. |
| `Dekker2_aux`, `Dekker2` | Added `0 <= dExp` and also leaked the ambient `Expoxy` inequality even though `Check @Dekker2_aux` and `Check @Dekker2` show that it is not part of either exported Coq constant. |
| `RoundLeNormal` | Added positivity of `1 - 2^(-precision)`, which Coq derives internally, while weakening the actual exported `3 <= precision` premise to `1 < precision`. |
| `dp_dq_le` | Accepted both ulp-comparison conclusions used inside the Coq proof, represented the residuals as reals instead of the source floats, and omitted the two explicit (though redundant) source `Fbounded p/q` premises. |
| `abeLeab` | Replaced the two source magnitude premises with the intermediate `|e| <= |a+b|/4` cut derived by Coq, and widened the source `e : float` binder to an arbitrary `e : Real`. |
| `ErrorBoundedIplus`, `MDekkerAux1` | Accepted the entire `errorBoundedPlus` theorem as a higher-order premise. |
| `Dekker1_FTS`, `Dekker3`, `MDekker`, `Dekker_FTS` | Exposed combinations of `TotalP Closest`, universal exponent bounds, midpoint/subtraction witness constructors, derived `1 < vNum`, and (for `Dekker_FTS`) the entire `errorBoundedPlus` theorem. |
| `Fulp_le_twice_r_round` | Accepted the doubled rounding judgment plus `MonotoneP` and `UniqueP`; FLoCq derives them through `Twice_EvenClosest_Round`, `EvenClosestMonotone`, and `EvenClosestUniqueP`. |
| `zPos` | Added `TotalP Closest`; FLoCq derives totality from the precision section. |
| `uhPos` | Added both `TotalP Closest` and the already-derived nonnegativity of `ph+b`; FLoCq derives the latter from product rounding, bounded `b`, and its original positivity premise. |
| `FmaErr_aux1` | Added a bounded exact-difference float and `TotalP Closest`; FLoCq constructs the difference through `gatCorrect`. |
| `FmaErr_aux2` | Added bounded difference and correction floats plus `TotalP Closest`; FLoCq obtains them through `gatCorrect` and `gaCorrect`. |

**Repair:** restore the exact source carrier, section assumptions, algorithm
equations, and conclusion for every listed name.  Rename the old bodies and
derive all proof-stage values internally by calling the same dependency chain
as FLoCq.  An existential witness produced by the theorem may not be changed
into a universally supplied caller function.

### T36. Universal `boundR` payload leaked through the Pff error chain

FLoCq derives `forall r, -dExp <= Fexp (boundR r)` from the nonnegative
`Fbound.dExp` invariant and the construction of `boundNat`.  The pre-repair
Lean contracts below all exposed that derived universal theorem as an
additional public premise:

- `errorBoundedPlusLe`, `LeExpRound`, `LeExpRound2`,
  `errorBoundedPlusAbs`, `errorBoundedPlus`;
- `Fma_FTS`, `MKnuth`, `MKnuth1`, `MKnuth3`, `MKnuth4`, `MKnuth5`,
  `MKnuth6`, `MKnuth7`, `Knuth`;
- `errorBoundedMultClosest_aux`, `errorBoundedMultClosest`, `plusExact1`,
  `plusExact2Aux`, `plusExact2`, `LeExp1`, `plusExactExp`,
  `AddExpGe1Underf`, `AddExpGe1Underf2`, `plusExactR0`, `ExactSum_Near`;
- `xLe2y_aux1`, `xLe2y_aux2`, `xLe2y`, `Subexact`, `gatCorrect`, `Expbe1`,
  `be2MuchSmaller`, `gaCorrect`;
- `tBounded_aux`, `tBounded`, `ErrFmaApprox_1_aux`, `ErrFmaApprox_1`,
  `LeExp2`, `LeExp3`, `LeExp`, `vLe_aux`, `vLe`, `tLe`, `wLe`,
  `ErrFmaApprox_2_aux`, `ErrFmaApprox_2`, and `ErrFmaApprox`.

For **each** name in this list, the semantic mismatch is the same concrete
loss of domain: a valid FLoCq caller supplies the bound record and section
assumptions but does not supply this universal proof.  Some declarations also
exposed the derived `1 < vNum`; that must likewise be synthesized from the
source power equation.

An independent `Check @name` review of the actual compiled Coq constants
found further exact-export mismatches in this same set:

- `errorBoundedPlusLe`, `errorBoundedPlusAbs`, `errorBoundedPlus`,
  `errorBoundedMultClosest_aux`, `errorBoundedMultClosest`, `plusExact1`,
  `plusExact2Aux`, `plusExact2`, `plusExactExp`, and `plusExactR0` replaced
  source `1 < precision` by `precision != 0` and leaked `1 < vNum`;
- `LeExpRound` and `LeExpRound2` similarly replaced source
  `3 <= precision`, while `LeExp1` replaced source `4 <= precision`;
- `Fma_FTS` erased the source abstract relation `P`, its refinement into
  `Closest`, and the two `P` judgments, replacing them by concrete `Closest`
  premises; it also replaced `3 <= precision` by the weaker derived inputs;
- `MKnuth`, `MKnuth1`, `MKnuth3`, `MKnuth4`, `MKnuth5`, `MKnuth6`,
  `MKnuth7`, and `Knuth` omitted source `IplusCompatible`; the affected
  wrappers also generalized a fixed radix-2 theorem and/or exposed
  `vNum_gt`, `TotalP`, or `precision != 0` in place of the exact source
  precision section;
- `AddExpGe1Underf` and `AddExpGe1Underf2` generalized the source radix 2,
  omitted both `1 < precision` and `4 <= precision`, and exposed the derived
  nonzero-precision/value-bound inputs;
- `ExactSum_Near` replaced source `1 < precision` by
  `precision != 0` plus `1 < vNum`, thereby incorrectly admitting
  `precision = 1`;
- `xLe2y_aux1`, `xLe2y_aux2`, `xLe2y`, and `Subexact` widened the exported
  source binder `e : float` to an arbitrary `e : Real`.  This is observable:
  the Lean-only caller can choose a nondyadic value such as
  `sqrt 2 / 2^20`, for which no radix-2 source float exists, while satisfying
  the small-error rounding premises;
- `ErrFmaApprox_1_aux` omitted the exported (logically redundant)
  `Fnormal z \/ F2R z = 0` premise, while `LeExp3` added an unexported
  `Fnormal uh` premise;
- `xLe2y_aux1`, `Subexact`, `Expbe1`, `be2MuchSmaller`, `gaCorrect`,
  `tBounded`, `ErrFmaApprox_1`, `LeExp2`, `LeExp3`, `vLe`, `tLe`, `wLe`,
  `ErrFmaApprox_2`, and `ErrFmaApprox` exposed `[ValidRadix radix]` as an
  additional implicit public binder even though the Coq contract has only
  explicit `1 < radix`; construct that instance locally.
- The same redundant implicit binder remained after the first repair pass on
  `errorBoundedPlusLe`, `LeExpRound`, `LeExpRound2`,
  `errorBoundedPlusAbs`, `errorBoundedPlus`, `Fma_FTS`,
  `errorBoundedMultClosest_aux`, `errorBoundedMultClosest`, `plusExact1`,
  `plusExact2Aux`, `plusExact2`, `LeExp1`, `plusExactExp`, and
  `plusExactR0`; remove it from the public type as well.

**Repair:** remove both derived premises from every public source contract.
Also repair every exact-export mismatch in the list above. Where the existing
proof body still needs derived facts, preserve it under a descriptive payload
name or bind them locally using the source precision inequalities,
`Fbound.dExp_nonneg`, `Fbound.vNum_pos`, and the power equation. Mechanically
scan every caller so the source-shaped public name is never invoked with an
old payload-shaped argument list.

### T37. `Core.Zaux` same-sign theorems were replaced by reflexive Boolean checks

- **FLoCq:** `src/Core/Zaux.v:450-490` exports four propositions:
  `Zsame_sign_trans`, `Zsame_sign_trans_weak`, `Zsame_sign_imp`, and
  `Zsame_sign_odiv`. Their conclusions are the required product
  nonnegativity facts; `Zsame_sign_odiv` uses truncating `Z.quot`.
- **Lean before repair:** the first two source names were Hoare specifications
  of Boolean checks, while `Zsame_sign_imp` and `Zsame_sign_odiv` had only
  computational definitions plus `_spec` theorems. Every `_spec` merely
  proved that a pure result equals the same `decide` expression used to define
  it, so it did not establish the source proposition. The old division check
  also used Lean integer `/`, not Coq's toward-zero quotient.
- **Judge failure:** v24 job `00c7d9ad513bf9b3291c` called the Coq theorem on
  one side and `Zsame_sign_imp_spec` on the other, then marked them aligned at
  0.98 confidence. All six compiler chains were genuine, but they proved
  different claims: direct product nonnegativity versus a reflexive Hoare
  equality. Executing two unrelated true claims cannot supply the missing
  theorem-contract bridge.
- **Observable division mismatch:** at `u = -3`, `v = 2`, Coq
  `Z.quot (-3) 2 = -1`, while Lean Euclidean `(-3) / 2 = -2`; hence the
  products in the old computational check were `3` and `6` respectively,
  even though both happen to be nonnegative.
- **Repair:** retain computation under explicit `_check` names; restore all
  four source names as direct propositions with the exact hypotheses and
  conclusions; use `Int.tdiv` for `Z.quot`; and compile source-contract checks
  plus the negative-quotient regression in `FloatSpec/Test/ZauxSource.lean`.

### T38. Remaining `Core.Zaux` source names exposed checks, wrong carriers, or Euclidean division

- **FLoCq:** outside the four T37 declarations, `src/Core/Zaux.v` exports
  direct propositions for integer powers, radix facts, division/remainder,
  Boolean comparisons, three-way comparison, conditional negation, fast
  power/division correctness, and iteration. `Zfast_pow_pos` and
  `iter_pos_nat` quantify over Coq `positive`; the `ZO*` family uses
  truncating `Z.quot`/`Z.rem`; `Zfast_div_eucl_correct` also covers a zero
  divisor.
- **Lean before repair:** many exact source names denoted constants or Boolean
  computations whose `_spec` theorem only restated the defining result. In
  particular, `Zeq_bool_true`, `Zle_bool_opp`, `Zcompare_Lt`, and the
  `cond_Zopp` lemmas did not mention the source operation in their conclusion.
  `Zmod_mod_mult`, `ZOmod_eq`, `Zdiv_mod_mult`, `ZOmod_mod_mult`,
  `ZOdiv_mod_mult`, and `ZOdiv_plus` similarly exposed result-producing checks
  instead of source equations. The `ZO*` checks used Lean Euclidean `/` and
  `%`; `Zpower_pos_gt_0` and `Zfast_pow_pos_correct` used `Nat`, admitting the
  source-impossible exponent zero; `Zfast_div_eucl_correct` added `b ≠ 0`;
  and the three iteration source names were check functions/spec variants.
- **Observable arithmetic mismatch:** Coq truncation gives
  `Z.quot (-7) 3 = -2` and `Z.rem (-7) 3 = -1`, whereas Lean Euclidean
  `(-7) / 3 = -3` and `(-7) % 3 = 2`. Thus the old `ZOmod_eq`/nested
  quotient checks could execute different values while their reflexive specs
  still passed. A later executed judge exposed the distinct floor-division
  mismatch in `Z_div_eucl`/`Zfast_div_eucl`: for `(7,-3)`, FLoCq
  `Z.div_eucl` returns `(-3,-2)`, while Lean's `/,%` pair returned `(-2,1)`.
  Both observations were then reproduced directly with Coq and Lean.
- **Dependent caller mismatch:** `Core.Raux.mag_le_Zpower` and
  `mag_gt_Zpower` used the theorem name `Zpower_Zpower_nat` as if it were the
  integer-power function. Their public premises therefore did not state the
  FLoCq `Zpower` bound.
- **Repair:** keep executable checks under `_check` names and restore every
  source theorem name as its direct equation/proposition. Represent Coq
  `positive` by `Positive`, use `Int.tdiv`/`Int.tmod` for all `ZO*` statements,
  use `Int.fdiv` plus the defining remainder equation for `Z.div_eucl`, cover
  negative and zero divisors, and expose direct fast-power, fast-division, and
  iteration equalities. Preserve the existing `iter_nat` implementation shape
  required by IEEE definitional reductions, but prove the source recursion and
  composition equations extensionally. Route both Raux magnitude theorems
  through the actual `Zpower` definition. Compile the full repository and the
  `ZauxSource` contract/negative-arithmetic regressions.

### T39. `Rnd_NG_pt_unique_prop` must retain its Type-valued tie payload

- **FLoCq:** `src/Core/Round_pred.v:701` exports
  `Rnd_NG_pt_unique_prop` with `P : R -> R -> Type`; it is not restricted to
  proof-irrelevant propositions.
- **Lean before repair:** `FloatSpec/src/Core/Round_pred.lean` restricted `P`
  to `Real -> Real -> Prop`.
- **Observable domain mismatch:** Coq accepts
  `Rnd_NG_pt_unique_prop (fun _ => True) (fun _ _ => nat)`, while the old Lean
  binder rejected `fun _ _ => Nat` before any rounding hypotheses were
  considered.
- **Repair:** universe-generalize only this definition's `P` binder and retain
  the Prop-specialized public theorems whose FLoCq contracts are themselves
  Prop-valued. Add a compilation regression instantiating the definition with
  `Nat`.

### T40. `Core.Raux` checks and magnitude lemmas must observe the source operations

- **FLoCq:** the 25 affected public items expose direct real/integer
  propositions over `Rabs`, comparison, floor/truncating division, integer
  powers, conditional negation, and the dependent `mag_prop` magnitude:
  `Rabs_gt`; `Rcompare_sym`, `Rcompare_opp`, `Rcompare_plus_r`,
  `Rcompare_plus_l`, `Rcompare_mult_r`, `Rcompare_mult_l`;
  `negb_Rlt_bool`, `negb_Rle_bool`; `Zfloor_div`, `Ztrunc_div`;
  `IZR_Zpower_pos`, `IZR_Zpower_nat`, `IZR_Zpower`;
  `bpow`, `mag`, `bpow_unique`, `mag_unique_pos`, `mag_le_abs`, `mag_le`,
  `lt_mag`, `bpow_mag_gt`, `bpow_mag_le`, `mag_sqrt`; and `IZR_cond_Zopp`.
- **Lean before repair:** `Rabs_gt` was paired with an unrelated spec; the six
  `Rcompare_*` checks returned the expected right-hand side and their specs
  proved only that result's self-equality; the two `negb_*` formulas were
  interchanged. `Zfloor_div` strengthened `y != 0` to `0 < y`, and
  `Ztrunc_div` added both `0 <= x` and `0 < y`. The three `IZR_Zpower*`
  bridges and `IZR_cond_Zopp` observed duplicate real expressions rather than
  the translated integer operation. The magnitude block changed the source
  carrier, moved or weakened hypotheses between neighboring names, added
  derived positivity/absolute-value/logarithm payloads, or returned a
  generalized intermediate theorem instead of the direct source result.
- **Observable mismatches:** at `x = y = 0`, FLoCq's
  `negb_Rlt_bool` and `negb_Rle_bool` produce different Booleans, exposing the
  swap. Negative divisors satisfy both source division theorems but were
  rejected by Lean; the correct observers are `Int.fdiv` for floor division
  and `Int.tdiv` for truncation. A vacuous power bridge continued to pass even
  if the integer-power implementation was changed because it never mentioned
  that implementation.
- **Repair:** restore direct source propositions under all 25 public names;
  retain generalized or proof-stage forms only under descriptive
  `_from_*_payload` names. Put the source-dependent `bpow`/`mag` carriers in
  the existing `RauxSourceFacade`, use `Int.fdiv`/`Int.tdiv`, and migrate every
  old payload-shaped caller explicitly. Compile negative division, Boolean
  equality-boundary, and source-signature regressions.

### T41. `Prop` theorems must derive format and rounding witnesses internally

An exhaustive check of all 241 exports in `Prop/{Relative,
Double_rounding,Round_odd,Div_sqrt_error,Plus_error,Mult_error,Sterbenz}.v`
found 57 additional contract mismatches. The required repairs are:

- **Relative (3):** `relative_error_le_conversion_inv` and
  `relative_error_le_conversion_round_inv` are source theorems for an arbitrary
  `rnd`; Lean added `[Valid_rnd rnd]`. `error_N_FLT` duplicated source
  `0 < prec` with an exposed `[Prec_gt_0 prec]`. Remove those public proof
  payloads and derive only what the bodies actually need.
- **Mult_error (3):** `mult_bpow_exact_FLX`, `mult_bpow_exact_FLT`, and
  `mult_bpow_pos_exact_FLT` exported `[Prec_gt_0 prec]`, absent from FLoCq.
  Preserve the source domains, including `prec = 0`, using a direct proof or a
  lower helper that does not demand the stronger instance.
- **Plus_error (1):** `round_repr_same_exp` added `[Valid_exp fexp]` although
  FLoCq requires only `Valid_rnd rnd`; remove the exponent instance from the
  public contract.
- **Div_sqrt_error (9):** `generic_format_plus_prec` added
  `[Valid_exp fexp]`, and `sqrt_error_N_FLX_aux1` added `[Prec_gt_0 prec]`.
  Conversely, `sqrt_error_N_FLX_aux2`, `sqrt_error_N_FLX_aux3`,
  `sqrt_error_N_FLX`, `sqrt_error_N_FLX_ex`,
  `sqrt_error_N_FLX_round_ex`, `sqrt_error_N_FLT_ex`, and
  `sqrt_error_N_FLT_round_ex` dropped the exported source premise
  `1 < prec`. Restore that premise even where the Lean theorem happens to prove
  a stronger statement.
- **Round_odd (18):** `generic_format_fexpe_fexp` added two `Valid_exp`
  instances. The source names `d_eq`, `u_eq`, `d_ge_0`, `mag_d`, `Fexp_d`,
  `format_bpow_x`, `format_bpow_d`, `d_le_m`, `m_le_u`, `mag_m`, `u'_eq`,
  `m_eq`, `m_eq_0`, `fexp_m_eq_0`, `mag_m_0`, `DN_odd_d_aux`, and
  `UP_odd_d_aux` exposed some combination of the internally derived opposite
  endpoint, canonicality, positivity, `Exists_NE`, or even-radix witnesses.
  Restore each exact FLoCq input list and construct those intermediates in the
  body; do not duplicate the already repaired `mag_round_odd` and
  `fexp_round_odd` work.
- **Double_rounding (23):** `round_round_mult_aux`, `round_round_mult`,
  `round_round_mult_FLX`, `round_round_mult_FLT`, and
  `round_round_mult_FTZ` added `Valid_exp`/`Prec_gt_0` payloads; the four public
  operation theorems also replaced FLoCq's supplied `rnd` function by the
  finite `Mode` carrier. `mag_plus_separated`,
  `round_round_plus_aux0_aux_aux`, `round_round_plus_aux0_aux`,
  `round_round_plus_aux0`, `round_round_minus_aux0_aux`,
  `round_round_minus_aux0`, `round_round_plus_radix_ge_3_aux0`, and
  `round_round_minus_radix_ge_3_aux0` added `Valid_exp` instances absent from
  their exported FLoCq types. Finally,
  `FLX_round_round_plus_hyp`, `FLT_round_round_plus_hyp`,
  `FLX_round_round_plus_radix_ge_3_hyp`,
  `FLT_round_round_plus_radix_ge_3_hyp`, `FLT_round_round_sqrt_hyp`,
  `FTZ_round_round_sqrt_hyp`, `FLT_round_round_sqrt_radix_ge_4_hyp`,
  `FTZ_round_round_sqrt_radix_ge_4_hyp`, `FLT_round_round_div_hyp`, and
  `FTZ_round_round_div_hyp` exposed `Prec_gt_0 prec'`, which FLoCq derives
  from the arithmetic precision relation. Restore raw `rnd` through the
  existing D1 bridge and derive every secondary instance internally.

Concrete rejected-source witnesses include `prec = 0` for the multiplication
and square-root auxiliary contracts, invalid but source-permitted exponent
functions for the helper contracts, and `x = d = u = 0` for the Round_odd
lemmas whose old Lean contracts incorrectly required `0 < x`. These are
source-pass/old-Lean-uninvokable counterexamples even when the theorem
conclusion itself was unchanged.

### T42. Remaining `Calc`/`Core` definitions and contracts must preserve total and boundary semantics

An exhaustive `Check @` audit matched all 603 exports in the 16 audited
`Calc`/`Core` modules and found 77 affected public items. Fix every name below;
keeping only a nearby generalized theorem is not sufficient.

- **Calc.Div (3):** `Fdiv_core` and `Fdiv` used Lean Euclidean `/` and `%`
  instead of Coq `Z.div_eucl` total semantics. For `(m1,m2,e) = (5,-3,0)`,
  FLoCq returns quotient/remainder `(-2,-1)` while the old Lean code returned
  `(-1,2)`. `Fdiv_correct` also omitted the source conclusion
  `e <= cexp (...)`. Implement the signed Euclidean branch and restore the
  full conjunction.
- **Calc.Sqrt (2):** `Fsqrt_core` and `Fsqrt` computed a negative-input
  remainder after `Int.sqrt`, while Coq `Z.sqrtrem` totalizes negative inputs
  as `(0,0)`. Thus mantissa `-1` was exact in FLoCq but inexact in Lean.
  Preserve that total branch without changing the positive-domain correctness
  theorem.
- **Core.Digits (23):** repair `digits2_Pnat`, `digits2_Pnat_correct`,
  `Z_of_nat_S_digits2_Pnat`, `Zpos_digits2_pos`, `Zdigits2_Zdigits`,
  `Zsum_digit_digit`, `Zdigit_ge_Zpower_pos`, `Zdigit_ge_Zpower`,
  `Zdigit_not_0_pos`, `Zdigit_not_0`, `ZOmod_plus_pow_digit`,
  `ZOdiv_plus_pow_digit`, `Zdigit_slice`, `Zpower_le_Zdigits`,
  `Zdigits_gt_Zpower`, `Zdigits_correct`, `Zdigits_unique`, `Zdigits_le`,
  `Zdigits_slice`, `Zslice_scale`, `Zsame_sign_slice`, `Zslice_slice`, and
  `lt_Zdigits`. The old translation used Nat bit-length
  (`digits2_Pnat 1 = 1` rather than source `0`), replaced indexed/all-position
  digit theorems by single-point or existential claims, reversed
  `Zpower_le_Zdigits`, changed truncating remainder to `%`, converted negative
  exponents with `.natAbs`, and added positivity, nonzero, nonnegative-index,
  positive-length, or divisibility assumptions absent from FLoCq. Restore
  Coq-positive recursion, signed powers, truncating division/remainder, and
  each exact quantified contract. Required boundary regressions include zero,
  negative integers, negative exponents, and negative slice indices.
- **Core.FLT (5):** `FLT_format` incorrectly collapsed invalid precision to a
  permissive generic format; `cexp_FLT_FLX` and `generic_format_FLT_FLX` used
  threshold `beta^(emin+prec)` instead of `beta^(emin+prec-1)`;
  `ulp_FLT_gt` weakened strict `<` to `<=`; and
  `succ_FLT_exact_shift_pos` added one to both source bounds. Preserve the
  source predicate even when precision is invalid and restore all boundaries.
- **Core.FLX (3):** `FLX_format` had the same invalid-precision collapse, and
  `FIX_format_FLX` changed the lower endpoint from `<=` to `<`. In addition,
  Lean defined `FLXN_format` as an alias of `FLX_format`, while FLoCq defines
  a distinct existential representation whose nonzero mantissa lies in
  `[beta^(prec-1), beta^prec)`. Restore both source predicates and the closed
  `FIX_format_FLX` endpoint; prove their generic-format bridges only under the
  source precision context rather than identifying the definitions.
- **Core.Float_prop (7):** restore the exact implication direction and
  assumptions of `F2R_lt`, `F2R_eq`, `F2R_le`, `eq_F2R`, `lt_F2R`, and
  `le_F2R`; generalized iff endpoints may remain only under descriptive names.
  `bpow_le_F2R_m1` was translated as an unrelated negative-mantissa bound;
  replace it with the source power/value inequality. A simple positive
  mantissa witness already distinguishes that wrong contract.
- **Core.Generic_fmt (16):** repair `canonical_generic_format`,
  `abs_lt_bpow_prec`, `subnormal_exponent`, `generic_format_bpow_inv'`,
  `generic_format_bpow`, `generic_inclusion_mag`,
  `generic_inclusion_lt_ge`, `generic_inclusion_ge`, `generic_inclusion`,
  `generic_inclusion_le_ge`, `scaled_mantissa_lt_bpow`,
  `generic_format_round_pos`, `generic_N_pt_DN_or_UP`, `round_ZR_pt`,
  `round_N0_pt`, and `round_NA_pt`. The old declarations variously added
  `Valid_exp`, changed `<`/`<=` boundary conditions, tested `fexp e` instead of
  source `fexp (e+1)`, replaced a conjunction/existential by a one-way program
  postcondition, or replaced equality to the concrete rounded result by
  existence/satisfaction of some endpoint. Keep generalized payload forms
  separately and restore the concrete source result under the source name.
- **Core.Round_NE (8):** `DN_UP_parity_pos_prop`, `DN_UP_parity_prop`,
  `DN_UP_parity_aux`, `DN_UP_parity_generic_pos`,
  `DN_UP_parity_generic`, `round_NE_opp`, `round_NE_abs`, and
  `round_NE_pt_pos` must use the source float/canonical premises and the
  concrete `round ... ZnearestE` result. The old facade substituted real
  endpoint predicates or existentially selected an arbitrary nearest result;
  some checks did not observe their bound `x` at all.
- **Core.Ulp (10):** remove the source-absent `[Exp_not_FTZ]` payload from
  `round_UP_DN_ulp`, `error_le_half_ulp`, `ulp_DN`, and
  `pred_UP_eq_DN`, and from `error_le_half_ulp_round` where FLoCq assumes only
  `Monotone_exp`. Remove the extra `Monotone_exp` from
  `round_neq_0_negligible_exp` and `eq_0_round_0_negligible_exp`, the added
  difference-nonzero premise from `generic_format_pred_aux2`, and the added
  `u != 0` premise from `round_N_ge_ge_midp` and `round_N_le_le_midp`.
  Derive any needed facts internally. Source-valid witnesses include an FTZ
  exponent that is monotone but not `Exp_not_FTZ`, a valid nonmonotone
  exponent with `negligible_exp = None`, and `u = v = 0` for both midpoint
  theorems.

For T42, repair root definitions first, preserve old generalized endpoints
only under descriptive names, migrate all callers, and add focused edge-case
regressions. A full build is required because these declarations sit below
most of FloatSpec.

### T43. Post-T42 judge findings must preserve signed helper semantics and exact compatibility contracts

- **`Core.Digits.Zdigits_aux`:** FLoCq compares its signed section parameter
  `p : Z` directly with the current power. The old Lean helper converted `p`
  with `Int.natAbs`, so `(beta,p,d,pow,fuel) = (2,-1,5,0,1)` returned `6`
  instead of the source result `5`. Keep the helper signed and make only the
  public `Zdigits` caller supply the positive magnitude of its integer input.
- **`Pff.powerRZ_inv`:** the exported source contract requires `x <> 0` and
  proves `powerRZ (/x) z = / powerRZ x z`. The old Lean source name instead
  exposed a total Hoare theorem for `(r^z)⁻¹ = r^(-z)`. The latter identity is
  related but admits the target-only input `r = 0` and is not the same public
  contract. Expose the nonzero premise and the direct inversion-of-base
  equality under `powerRZ_inv`; retain any normalized identity only under a
  descriptive compatibility name.

Both repairs require focused regressions for the signed helper boundary and
the nonzero theorem interface, followed by a fresh judge plan because the
target declarations and hashes changed.

## Confirmed missing source-facing declarations

These are absent source contracts, not proof holes in an existing theorem.

### M1. `generic_round_generic`

- **FLoCq:** `src/Core/Generic_fmt.v:2326` says that an `fexp1`-formatted value
  remains `fexp1`-formatted after rounding it in `fexp2`, under the section's
  exponent-inclusion assumptions.
- **Lean gap:** only `generic_format_roundR` at
  `FloatSpec/src/Core/Generic_fmt.lean:4154` is present; it proves formatting in
  the same format used for rounding and is not the two-format theorem.
- **Repair:** port the full `fexp1`/`fexp2` declaration and its inclusion proof.

### M2. `monotone_exp_not_FTZ`

- **FLoCq:** public global instance at `src/Core/Generic_fmt.v:1551`.
- **Lean gap:** the result exists only as a private helper at
  `FloatSpec/src/Core/Ulp.lean:8901`, so other translated modules cannot obtain
  the source instance.
- **Repair:** move the proof to `Core/Generic_fmt.lean` as the public instance
  and reuse it from `Core/Ulp.lean`.

### M3. Generic IEEE equality API

- **FLoCq:** `Beqb`, `Beqb_correct`, and `Beqb_refl` at
  `src/IEEE754/BinarySingleNaN.v:628-648` operate on the generic binary-float
  carrier.
- **Lean gap:** no corresponding generic declarations are present; a
  specialized primitive-float equality elsewhere is not this API.
- **Repair:** add all three on the D3 source-faithful carrier and preserve NaN
  behavior in `Beqb_refl`.

### M4. `Flocq_version`

- **FLoCq:** `src/Version.v:24` exposes parsed version metadata.
- **Lean gap:** no target declaration exists.
- **Repair:** add the pinned source-version constant or document an explicit,
  reviewed repository-metadata mapping if version constants are intentionally
  outside the translated library surface.

### M5. Public `Calc.Round` truncation theorem names

- **FLoCq:** `src/Calc/Round.v` publicly exports `truncate_aux_comp`,
  `truncate_0`, `generic_format_truncate`, `truncate_correct_format`,
  `truncate_correct_partial'`, `truncate_correct_partial`,
  `truncate_correct'`, and `truncate_correct`.
- **Lean before repair:** complete proofs existed only under
  `FloatSpec.Calc.Round.Audit`, while comments said their Coq proofs were not
  ported.  Consequently importers and name matching could not use the source
  declarations even though the proof terms already existed.
- **Repair:** publish exact aliases in `FloatSpec.Calc.Round` and keep the
  `Audit` namespace only as an implementation detail; compile all eight aliases
  against the existing proof terms.

### T44. r4 raw `not_aligned` boundary findings

- **FLoCq:** `relative_error_FLX_aux` and `relative_error_FLT_aux` export no
  positive-precision premise; `Zpower_nat_less` assumes `1 < n` and includes
  `q = 0`; Pff `pos_length` is the zero-based depth of Coq `positive`;
  `FtoR`, `UniqueP`, `MonotoneP`, and `MinExList` are total over integer radix.
- **Lean before repair:** the two relative lemmas exposed `Prec_gt_0`;
  `Zpower_nat_less` required `q > 0`; `pos_length` returned the positive value,
  changing `digitAux`; and only the indexed implementation exposed the last
  three predicates/theorem. `Source.FtoR` was already exact but was paired to
  the wrong target by the judge.
- **Repair:** remove the proof-only precision binders, restore the exact power
  premise, use binary depth for `pos_length`, and add unrestricted
  `Source.UniqueP`, `Source.MonotoneP`, and `Source.MinExList`. Preserve the
  indexed implementation as the internal library API. Native Coq/Lean edge
  observations and `FloatSpec.Test.PffSourceContracts` must pass.

## Known match gaps that are not independent semantic repair items

The last full inventory also reported `FLT_exp_monotone`, `FLX_exp_monotone`,
`valid_rnd_UP`, `valid_rnd_ZR`, `valid_rnd_odd`, `valid_rnd_round_mode`, two
section-local `fexp_correct`/`is_finite_strict` declarations, many repeated
local `FtoRradix`/cast aliases, and `eq_dep_elim` as unmatched.

These must be entered in the final ledger as one of:

- a checked equivalence to an existing renamed Lean declaration;
- a source-facing compatibility alias/instance that should be added; or
- a reviewed non-exported local/extractor artifact with no target obligation.

They must not be counted as aligned merely because a fuzzy name matcher found
something nearby. Conversely, a harmless rename is not a theorem-semantic
bug and is therefore not presented as one in the repair list above.

## Whole-repository completion gates

All boxes below are part of this checklist. The named repairs alone are not a
whole-repository certificate.

- [x] **G1 — Freeze revisions.** Record the exact FLoCq and FloatSpec commits;
  the FloatSpec worktree used for certification must be clean.
- [x] **G2 — Build everything.** `lake build floatspec` and
  `lake build FloatSpecTests` pass from a clean checkout.
- [x] **G3 — No trust holes.** The full source tree contains no `sorry`,
  `admit`, `sorryAx`, unauthorized `axiom`/`opaque`/`extern`, unsafe escape,
  or generated placeholder theorem. Standard Lean axioms such as
  `Classical.choice`, `propext`, and quotient soundness must be reported rather
  than mislabeled as custom holes.
- [ ] **G4 — Complete source ledger.** All 2548 extracted FLoCq declarations
  have a reviewed record containing source item, target item or justified
  non-exported-local classification, dependency mapping, and reviewer. There
  are zero unclassified source items.
- [ ] **G5 — Definition alignment.** Every exported source definition has
  either the same observable semantics in Lean or a proved bridge to the
  chosen idiomatic Lean representation. Test-only observers and same-name
  shadow declarations do not count.
- [ ] **G6 — Contract alignment.** For every exported theorem, the ledger
  checks quantifier order, domains, section/typeclass assumptions, hypotheses,
  conclusion, and representation bridge. There are zero `uncertain`,
  `not_judged`, unreviewed added-precondition, weakened-conclusion, or
  proof-payload-as-input cases.
- [x] **G7 — Rounding audit.** A mechanical scan finds no generic declaration
  that binds `rnd`/`choice` while evaluating a fixed mode or `()`. Every fixed
  mode is traced to the same fixed source mode.
- [x] **G8 — Carrier audit.** Pff extrema and IEEE source-facing APIs use their
  source-faithful carriers/predicates. Compatibility wrappers cannot inherit a
  source theorem name while adding validity assumptions.
- [ ] **G9 — Dependency-complete proofs.** Every source theorem in the ledger
  is closed without asking callers for a lemma, witness, disjunction, or
  invariant that the FLoCq proof derives from the source assumptions.
- [ ] **G10 — Executed semantic observations.** For every executable
  definition, and for theorem contracts where concrete instantiation is
  meaningful, accepted examples run independently in Coq and Lean and compare
  a shared observer. Harnesses must import the real declaration and must not
  shadow it. Examples supplement, but do not replace, G5/G6.
- [ ] **G11 — Adversarial review.** Counterexample search covers branch
  boundaries, zero/sign cases, min/max extrema, all rounding modes and ties,
  subnormal/normal/overflow boundaries, NaN/infinity/signed zero, and alternate
  representations of equal real values. Every claimed counterexample is
  manually reproduced on both sides.
- [ ] **G12 — Independent sign-off.** A second reviewer checks every repaired
  entry in D1-D11, T1-T44, and M1-M5 plus all nontrivial ledger
  classifications. The final report links the clean build, trust scan, ledger,
  executed harnesses, and counterexample audit.

## Close-out rule

Do not mark this document complete while any checkbox above is open. In
particular, a successful Lean build proves internal consistency of the target,
not faithfulness to FLoCq, and a high name-match percentage proves coverage of
the matcher, not semantic equivalence.
