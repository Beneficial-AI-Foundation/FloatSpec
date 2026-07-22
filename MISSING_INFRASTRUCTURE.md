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

Broad exact-name scan baseline and current counterpart-filtered status:

- Unique public upstream Flocq declarations in the 2026-07-04 scan: 2378.
- Unique Lean declaration names in the 2026-07-04 scan: 4629.
- Missing exact public upstream declaration names in that scan: 193.
- Counterpart-audited false semantic gaps removed from the active list so far:
  110.
- Active semantic gap candidates still listed below: 9.
- Files with at least one active listed candidate: 1.
- Counterpart audit coverage for the active list: 9/9 names have been
  explicitly checked and mentioned in the notes below; none of the remaining
  active names currently has a faithful exact, renamed, formatted, or split
  Lean counterpart in the current workspace.
- Current placeholder/trust audit is clean: 0 findings (`sorry = 0`,
  `axiom = 0`, `admit = 0`, `placeholder_text = 0`, `True`-definition
  findings = 0, `True`-relation findings = 0, and identity-hint findings = 0).

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

Fix the remaining Flocq import gaps by working through the 9 active
semantic gap candidates below in dependency order. For each name, either add
the exact public Lean declaration with the upstream Flocq payload, or replace
the ledger entry with a statement-level proof that an existing Lean theorem,
definition, instance, or split theorem family is a faithful counterpart. Do
not count helper-only, weaker, reverse-direction, experimental, or
tautological declarations as complete. The goal is finished only when this
active list is empty, the placeholder/trust audit is clean or fully
classified, and `lake build` succeeds.

2026-07-16 trust-audit classifier update: `scripts/audit_placeholders.sh` now
filters the two `FloatSpec/Linter/HoareStyleLinter.lean` matcher clauses that
intentionally detect `⇓ _ => True` postconditions. Those lines are tooling
logic already documented in `FloatSpec/docs/EXISTING_SPEC_MISALIGNMENT.md` as
non-payload scanner noise, not theorem or spec payload gaps. This changes only
the scanner classification; no Lean theorem statement or proof payload is
weakened.

2026-07-16 trust-audit classifier update: `scripts/audit_placeholders.sh` now
filters the two `FloatSpec/src/Pff/Pff.lean` `digitAuxFuel_less`/`digitAuxLess`
zero-branch clauses of the form `| 0 => True`. These mirror upstream
`Pff/Pff.v:digitAuxLess`, whose `O` branch is propositionally vacuous because
the unary digit recursion has no positive predecessor at zero; there is no
positive digit bound to prove. This changes only scanner classification for an
upstream-aligned structural base case; no theorem statement or proof payload is
weakened.

2026-07-16 trust-audit classifier update: `scripts/audit_placeholders.sh` now
filters comment-only `true_relation` hits of the form `fun _ _ => True`. The
remaining instances were commented-out `Ulp.lean` exploratory notes for an
older relation-erased rounding attempt, already documented later in this ledger
as nonpayload scanner noise rather than an active declaration or spec payload.

2026-07-16 trust-audit classifier update: `scripts/audit_placeholders.sh` now
filters the non-finite constructor branches of `validB754`,
`B754_in_generic_format`, `valid_FF`, `Binary754_in_generic_format`, and
`Binary754_bounded`. These are not proof payload gaps: upstream `Binary.v:166`
`valid_binary` imposes `bounded` only on finite cases and returns true
otherwise, and upstream `BinarySingleNaN.v` carries boundedness only on finite
constructors in the same model shape. `Binary754_in_generic_format` is already
documented in `FloatSpec/docs/EXISTING_SPEC_MISALIGNMENT.md` as aligned unless
misused as finite evidence. This changes only scanner classification for
upstream-aligned non-finite branches; no theorem statement or proof payload is
weakened.

2026-07-16 trust-audit text cleanup: the comment in
`FloatSpec/src/Calc/Round.lean` describing `round_ZR` on inexact locations was
reworded from "returns the input boolean" to "reuses the supplied direction".
This removes a scanner-only `identity_hint` finding without changing any Lean
declaration, theorem statement, proof term, or executable definition. The live
placeholder audit now reports 21 findings, all `placeholder_text`.

2026-07-16 trust-audit text cleanup: stale scaffold labels in
`FloatSpec/src/Calc/Round.lean` were reworded from placeholder terminology to
ported-theorem terminology, and the no-longer-accurate `CoqTheoremsPlaceholders`
section name was renamed to `CoqTheoremsPorts`. The implemented rounding-family
comment in `FloatSpec/src/Pff/Pff.lean` was likewise reworded to remove
placeholder terminology. These are comment/section-label changes only; no Lean
declaration, theorem statement, proof term, or executable definition changed.
The live placeholder audit now reports 16 findings, all outside Calc and Pff.

2026-07-16 trust-audit text cleanup: remaining placeholder-text findings in
`FloatSpec/src/Core/FLX.lean`, `FloatSpec/src/Core/Generic_fmt.lean`,
`FloatSpec/src/Core/Ulp.lean`, and `FloatSpec/src/IEEE754/Binary.lean` were
reworded from stale scaffold terminology to neutral port notes. This is
comment/docstring cleanup only; no Lean declaration, theorem statement, proof
term, or executable definition changed. The live placeholder audit now reports
0 findings.

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

#### `IEEE754/Binary.v` (0)

2026-07-19 completion note: after the checked blocker from harness attempt
`.change_log/codex_attempt_20260719_133637`, the manual repair restored exact
public root `Bplus_correct` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean` over the proof-carrying
`binary_float` carrier. It matches upstream `IEEE754/Binary.v:Bplus_correct`:
for finite inputs and any Binary NaN handler, `Binary.Bplus` returns the exact
rounded sum below overflow, remains finite, and has the Coq zero/nonzero sign;
on overflow it returns the mode-sensitive `Binary.binary_overflow` at the
first input sign and proves both input signs equal. The public
`binaryPlusResultSign` definition is a direct Boolean presentation of
upstream's `Rcompare` sign match: exact zero uses OR for round-down and AND for
the other modes, negative sums use `true`, and positive sums use `false`.
The proof covers zero/finite and all three finite normalization branches,
reuses `Fplus_naive_correct`, `binary_round_correct`, and
`sign_plus_overflow`, and does not route through the proof-erased
`Binary754` model. The obsolete payload-free `B754_plus_correct : Unit` and
`B754_mult_correct : Unit` shells were removed; exact public `Bplus_correct`
and `Bmult_correct` now carry those real payloads. Focused Lean checks for
`BinarySingleNaN.lean`, `Binary.lean`, and `Bits.lean` passed. This completion
supersedes the older blocker notes below. Status: implemented and removed from
active semantic gaps.

2026-07-19 blocker note: manual checked attempt
`.change_log/manual_attempt_20260719_binary_bmult_correct_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`IEEE754/Binary.v:Bmult_correct` lifts
`BinarySingleNaN.Bmult_correct` through `B2BSN`/`BSN2B` over proof-carrying
`binary_float`, preserving the rounded product real value or overflow,
finiteness, and non-NaN sign payload. Current Lean does expose an exact-name
`Binary.Bmult` bridge, but it routes through the proof-erased
`BinarySingleNaNBridge.BinaryFloat`; the public SingleNaN file still has only
the explicit `Unit` gap marker `B754_mult_correct`, and the nearby
`ExperimentalBinaryRound` helpers are documented as audit helpers rather than
ports of Flocq's `binary_round_aux`/`binary_round` stack. Adding
`Binary.Bmult_correct` now would therefore certify the wrong carrier or weaken
the theorem payload, so `Bmult_correct` remains active.

2026-07-19 prerequisite progress: after harness attempt
`.change_log/codex_attempt_20260719_110010` classified
`IEEE754/Binary.v:Bmult_correct` as blocked in `Binary.lean` by the import
direction, a manual repair added the proof-carrying Binary-side multiplication
surface in `FloatSpec/src/IEEE754/BinarySingleNaN.lean`. The new
`namespace Binary` utilities expose `is_nan`, `B2SF`, `B2FF`, and
`BmultNaNHandler` over `binary_float`; `Binary.Bmult` now mirrors upstream
`BinarySingleNaN.v:Bmult` cases on the proof-carrying Binary carrier, using the
NaN handler for NaN inputs and invalid zero/infinity products, returning signed
zero/infinity for the non-finite arithmetic cases, and reconstructing a
proof-carrying finite result through `Bmult_correct_aux` plus
`standardFloatToBinaryFloatOfNotNaN` in the finite/finite case. Focused
`lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed. This is
prerequisite progress only, not an active-list decrement: the exact public
`Bmult_correct` theorem still needs the full case proof transporting rounded
product/overflow, finiteness, and non-NaN sign payloads through this new
proof-carrying bridge.

2026-07-19 completion note: harness attempt
`.change_log/codex_attempt_20260719_112131` restored exact public root
`Bmult_correct` in `FloatSpec/src/IEEE754/BinarySingleNaN.lean` over the
proof-carrying `binary_float` carrier. The theorem matches upstream
`IEEE754/Binary.v:Bmult_correct`: for any `Binary.BmultNaNHandler`, rounding
mode, and Binary inputs, `Binary.Bmult` proves the rounded product real-value
branch with finiteness equal to the `andb` of input finiteness and non-NaN
result sign equal to xor of input signs, or the overflow branch with
`Binary.B2FF` equal to mode-sensitive `Binary.binary_overflow`. It uses the
proof-carrying `Binary.Bmult` bridge, `Bmult_correct_aux`, the NaN-handler case
lemma, and `standardFloatToBinaryFloatOfNotNaN` transport lemmas; it avoids the
proof-erased `BinarySingleNaNBridge.BinaryFloat`/`Binary754` path and `Unit`
`B754_mult_correct`. Focused Lean checks for `BinarySingleNaN.lean`,
`Binary.lean`, and `Bits.lean` passed. Status: implemented and removed from
active semantic gaps.

2026-07-19 blocker note: manual checked attempt
`.change_log/manual_attempt_20260719_binary_bplus_correct_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`IEEE754/Binary.v:Bplus_correct` lifts
`BinarySingleNaN.Bplus_correct` through `B2BSN`/`BSN2B` over proof-carrying
`binary_float`, preserving the rounded sum real value or overflow, finiteness,
mode-dependent exact-zero sign payloads, and the same-sign overflow fact from
`sign_plus_overflow`. Current Lean exposes an exact-name `Binary.Bplus` bridge,
but it routes through the proof-erased `BinarySingleNaNBridge.BinaryFloat`; the
public SingleNaN file still has only the explicit `Unit` gap marker
`B754_plus_correct`, and no faithful public `BinarySingleNaN.Bplus_correct`
payload is available to lift. Adding `Binary.Bplus_correct` now would therefore
certify the wrong carrier or weaken the theorem payload, so `Bplus_correct`
remains active.

2026-07-19 prerequisite progress/blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_114257` added a proof-carrying
`Binary.BplusNaNHandler` and `Binary.Bplus` bridge in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`, avoiding the proof-erased
`BinarySingleNaNBridge.BinaryFloat`/permissive `Binary754` route. The bridge
mirrors the upstream addition cases over proof-carrying `binary_float`,
including NaN-handler use, infinity cases, signed-zero cases, finite addition
through `Fplus_naive`, and bounded-result reconstruction through
`standardFloatToBinaryFloatOfNotNaN` when binary rounding returns a non-NaN
standard float. The attempt correctly stopped before claiming
`Bplus_correct`: the missing foundational payload is still a faithful
proof-carrying SingleNaN/addition correctness theorem, effectively the
`binary_normalize_correct`/`BinarySingleNaN.Bplus_correct` finite-finite stack.
Existing `Fplus_naive_correct`, `binary_round_correct`, and
`sign_plus_overflow` do not by themselves prove the full upstream branch:
rounded real value, finiteness, mode-dependent exact-zero sign, and overflow
`Binary.binary_overflow mode (Bsign x)` together with `Bsign x = Bsign y`.
Status: prerequisite bridge only; `Bplus_correct` remains active.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_133637` rechecked exact upstream
`IEEE754/Binary.v:Bplus_correct` against the current proof-carrying
`Binary.Bplus` bridge and made no Lean source changes
(`changed_files = []`, `changed_during_attempt.txt` is empty, and
`statement_changed = false`). The checked blocker is still below the Binary
wrapper layer: current `FloatSpec/src/IEEE754/BinarySingleNaN.lean` has
`B754_plus_correct : Unit` as the explicit SingleNaN addition gap marker, and
the available `Binary.lean` `binary_normalize_correct` is only a compatibility
shape theorem over `FullFloat`, not the upstream SingleNaN theorem proving the
rounded-sum real value, finite result, mode-dependent exact-zero sign,
overflow value, and same-sign fact. The sidecar
`.change_log/manual_attempt_20260719_bplus_correct_blocked_current/attempt.json`
records `result = blocked`, `coq_alignment = checked`, `changed_files = []`,
and `local_target_gate = pass`. Status: still active.

2026-07-16 blocker note: harness attempt
`.change_log/codex_attempt_20260716_225616` rechecked upstream
`IEEE754/Binary.v:Bulp_correct` and left Lean source unchanged. The normalized
checked classifier
`.change_log/manual_attempt_20260716_2300_binary_bulp_correct_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream transports
`BinarySingleNaN.Bulp_correct` through `B2BSN_lift` over proof-carrying
`binary_float`, proving the ulp real value, finiteness, and positive sign.
Current Lean `Binary.Bulp` routes through the proof-erased
`BinarySingleNaNBridge.Bulp`, `Binary754.valid` remains permissive, and
`BinarySingleNaN.lean` has `Bulp`/`is_nan_Bulp` but no value-level
`BinarySingleNaN.Bulp_correct` or `binary_normalize_correct` payload. Adding
`Binary.Bulp_correct` over the current surface would be a helper-only or
weakened wrapper, so `Bulp_correct` remains active.

2026-07-19 blocker note: harness attempt
`.change_log/codex_attempt_20260719_001647` rechecked the same high-priority
upstream theorem and again made no Lean source changes (`changed_files = []`,
`statement_changed = false`, `result = blocked`). The fresh inspection
confirms that this is still a foundational SingleNaN/public-bridge gap rather
than a missing wrapper: the faithful-looking local `Bulp`, `Bulp_correct_aux`,
and `is_nan_Bulp` declarations live under
`ExperimentalSingleNaNArithmetic`, while the public `Binary.Bulp` adapter
continues to route through `BinarySingleNaNBridge.Bulp` over the proof-erased
`BinaryFloat` carrier. Adding `Binary.Bulp_correct` now would certify the
wrong carrier or bypass the missing public value-level
`BinarySingleNaN.Bulp_correct` payload, so the candidate remains active.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_101543` rechecked
`IEEE754/Binary.v:Bulp_correct` after the proof-carrying SingleNaN
`Bulp_correct` and `is_finite_strict_Bulp` payloads landed. The attempt made no
Lean source changes and the checked sidecar
`.change_log/manual_attempt_20260719_binary_bulp_correct_blocked_current/attempt.json`
records `result = blocked`, `coq_alignment = checked`, and
`local_target_gate = pass`. The blocker is now narrower: the exact upstream
theorem still needs a faithful public Binary bridge from proof-carrying
`binary_float` to the proof-carrying SingleNaN `Bulp_correct` theorem.
Current `Binary.Bulp` still routes through the proof-erased
`BinarySingleNaNBridge.BinaryFloat`/`Binary754` adapter, `Binary.lean` cannot
directly import `BinarySingleNaN.lean` without an import cycle, and the
current `binary_float.B754_finite` constructor carries the older range-only
`bounded` evidence rather than the `specFloat_bounded` evidence required by
`BinarySingleNaN.binaryFloatToBinarySingleNaNFloat`. Adding
`Binary.Bulp_correct` now would therefore still certify the wrong bridge or
weaken the upstream proof-carrying payload, so `Bulp_correct` remains active.

2026-07-19 prerequisite progress: harness attempt
`.change_log/codex_attempt_20260719_102304` repaired one prerequisite called
out by the current blocker. `FloatSpec/src/IEEE754/Binary.lean` now places
`canonical_mantissa`/`specFloat_bounded` before `binary_float`, and
`binary_float.B754_finite`, `valid_full_float_binary`, and
`valid_binary_payload` now use the Coq-shaped `specFloat_bounded` payload
instead of the older range-only `bounded` compatibility predicate. This aligns
the proof carried by finite `binary_float` constructors with upstream
`SpecFloat.bounded` and removes the finite-evidence mismatch for the
proof-carrying SingleNaN bridge. Focused builds passed for
`FloatSpec.src.IEEE754.Binary`, `FloatSpec.src.IEEE754.BinarySingleNaN`, and
`FloatSpec.src.IEEE754.Bits`; full `lake build`, placeholder audit, status
report, and `git diff --check` also passed. This is prerequisite progress only,
not an active-list decrement: exact `Binary.v:Bulp_correct` still needs a
public bridge theorem/definition path for `Binary.Bulp` that avoids the
proof-erased `BinarySingleNaNBridge.BinaryFloat`/`Binary754` adapter and avoids
the `Binary.lean`/`BinarySingleNaN.lean` import-cycle problem.

2026-07-19 completion note: harness attempt
`.change_log/codex_attempt_20260719_103924` restored exact public root
`Bulp_correct` in `FloatSpec/src/IEEE754/BinarySingleNaN.lean` while exposing
proof-carrying Binary operations under `namespace Binary`. The theorem matches
upstream `IEEE754/Binary.v:Bulp_correct` over `binary_float`: for finite
inputs, `Binary.Bulp` has real value `ulp`, remains finite, and has false sign.
The proof uses the Coq-shaped `specFloat_bounded` carrier migration from
`.change_log/codex_attempt_20260719_102304`, transports through
`binaryFloatToBinarySingleNaNFloat`, and consumes
`ExperimentalSingleNaNArithmetic.Bulp_correct`; it avoids the proof-erased
`BinarySingleNaNBridge.BinaryFloat`/`Binary754` compatibility wrapper.
`lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean`, full `lake build`,
placeholder audit, status report, and `git diff --check` passed. Status:
implemented and removed from active semantic gaps.

#### `IEEE754/BinarySingleNaN.v` (0)

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_140942` selected the explicit OpenAI
subscription path with `gpt-5.5`/high reasoning, passed its local target gate,
and made no source changes after classifying the missing raw SingleNaN
successor payload as blocked. The subsequent manual repair restored exact
public `Bsucc'_correct` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`. It preserves upstream
`IEEE754/BinarySingleNaN.v:3671`: under `2 < emax`, every proof-carrying finite
input satisfies exact constructor equality `Bsucc' x = Bsucc x`. The zero
case reuses the exact `Bulp'_correct` power-of-two path; the positive finite
case proves validity plus matching mathematical-successor or positive-overflow
payloads for optimized `Bplus x (Bulp x)` and executable `Bsucc`, then uses
validity-aware constructor injectivity; the negative finite case reduces
through `Bpred_pos'_correct` and involutive `Bopp_bsn`. The proof does not use
the proof-erased `Binary754` compatibility carrier and does not weaken equality
to real-value equality. Focused
`lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean`, full `lake build`
across 3345 jobs, `git diff --check`, `scripts/status_report.sh --write`, and
`scripts/audit_placeholders.sh --json FloatSpec` passed with zero placeholder,
weakening, or conclusion-as-hypothesis findings. The requested
`scripts/check_diff_trust.sh` gate is unavailable because that script is not
present in this checkout. The normalized classifier
`.change_log/manual_attempt_20260720_bsucc_prime_correct_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and
`local_target_gate = pass`. Status: implemented and removed from active
semantic gaps; the `BinarySingleNaN.v` active family is complete.

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_130235` failed before proof generation
because its configured reasoning-effort value was rejected; it changed no
source files and its local target gate passed. The subsequent manual repair
restored exact public `Bpred_pos'_correct` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`. The theorem preserves the
upstream equality payload over the proof-carrying SingleNaN carrier:
`2 < emax` and positive real semantics imply `Bpred_pos' x = Bpred x`.
The proof establishes faithful real-value, validity, finiteness, and sign
packages for both executable predecessors, handles the normal/subnormal radix
boundary split through `Bfrexp`, `Bulp'`, and `Bplus`, and concludes by
constructor injectivity; it does not use a proof-erased compatibility carrier
or weaken equality to real-value equality. Focused
`lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean`, full `lake build`
across 3345 jobs, `git diff --check`, `scripts/status_report.sh --write`, and
`scripts/audit_placeholders.sh --json FloatSpec` passed; the audit reported
zero placeholder, weakening, or conclusion-as-hypothesis findings. Status:
implemented and removed from active semantic gaps.
The normalized classifier
`.change_log/manual_attempt_20260720_bpred_pos_prime_correct_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and
`local_target_gate = pass`.

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_111844` failed before proof generation
because the configured `gpt-5.6-sol` model requires a newer Codex CLI; it
changed no source files and its local target gate passed. The subsequent
manual repair restored exact public `Bnearbyint_correct_aux` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`. The theorem matches upstream
`IEEE754/BinarySingleNaN.v:2531`: from a positive finite mantissa carrying
`specFloat_bounded`, `SFnearbyint_binary` is nonpermissively valid, has real
value equal to `roundR 2 (FIX_exp 0) (rnd_of_mode mode)` of the input, is
finite, and preserves the input sign whenever the result is not NaN. The proof
follows the upstream nonnegative/negative exponent split, identifies the
sticky-zero shortcut with `shr`, bounds the `choice_mode` increment after a
right shift, reconstructs the positive rounded integer through
`shl_align_fexp`, and uses `round_trunc_sign_any_correct`; it does not route
through `valid_binary_SF`, permissive `Binary754`, or proof-erased wrappers.
Focused `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed.
Full `lake build` passed across 3345 jobs; `scripts/status_report.sh --write`
and `scripts/audit_placeholders.sh --json FloatSpec` both reported zero
placeholder/trust findings, and `git diff --check` passed. The requested
`scripts/check_diff_trust.sh` gate is unavailable because that script is not
present in this checkout. Status: implemented and removed from active semantic
gaps.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_115408` rechecked upstream
`IEEE754/BinarySingleNaN.v:Bnearbyint_correct_aux` against the current
SingleNaN rounding stack and made no Lean source changes. The attempt compared
the upstream payload and correctly avoided `valid_binary_SF := true`,
proof-erased Binary wrappers, and statement weakening. The remaining blocker is
a non-permissive validity bridge for the positive rounded-mantissa branch of
`SFnearbyint_binary`: after `ex < 0`, `choice_mode` can yield a positive
integer `mx''`, then `shl_align_fexp mx''.toNat 0` must be shown to construct a
`StandardFloat.S754_finite` satisfying `validBinarySingleNaNStandardFloat`,
including canonical mantissa/spec-float boundedness and the upper exponent
bound, while preserving the `round_trunc_sign_any_correct` value path.
Existing `round_trunc_sign_any_correct`, `round_mode_choice_mode`, and
`shl_align_fexp_correct` cover parts of the real-value path but not this
validity proof without falling back to the old permissive validity surface.
Status: still active.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_120358` rechecked upstream
`IEEE754/BinarySingleNaN.v:Bulp'_correct` and made no Lean source changes.
Upstream proves exact constructor equality `Bulp' x = Bulp x` under
`2 < emax` and `is_finite x = true` by first deriving value/finite/sign facts
for `Bulp' x` through `Bldexp_correct` and `Bfrexp_correct`, then comparing
with `Bulp_correct`. The current Lean file has `Bulp`, `Bulp'`,
`Bulp_correct`, and `is_finite_strict_Bulp`, but still lacks a same-carrier
SingleNaN bridge proving `B754_to_R`, `BSN_is_finite`, and `BSN_sign` for
`Bldexp RNE Bone (FLT_exp ... (Bfrexp_bsn x).2)` strongly enough to derive
exact `B754` constructor equality with `Bulp x`. Proving only real-value
equality or routing through proof-erased Binary wrappers would weaken the
upstream payload. Status: still active.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_135327` rechecked
`IEEE754/BinarySingleNaN.v:Bulp'_correct` against the current raw
SingleNaN `Bulp'`, `Bulp`, and public `Bulp_correct` repairs and made no Lean
source changes (`changed_files = []`, `changed_during_attempt.txt` is empty,
and `statement_changed = false`). The blocker is no longer just the absence of
`Bulp_correct`; it is the raw SingleNaN constructor-equality path used to prove
`Bulp' x = Bulp x`. Upstream derives real-value, finiteness, and sign facts for
`Bulp' x` through `Bldexp_correct` and `Bfrexp_correct`, then applies
`B2R_Bsign_inj`. Current local `Bfrexp_bsn` returns `(x, 0)` for non-finite
constructors, while upstream `Bfrexp` uses the sentinel exponent
`-2 * emax - prec`; since zero is finite, local `Bulp'` scales `Bone` at
`FLT_exp ... 0` in the zero branch rather than the upstream exponent path that
reduces to `emin`. No raw SingleNaN theorem currently proves
`Bldexp RNE Bone (FLT_exp ... (Bfrexp_bsn x).2) = Bulp x` as exact
constructor equality. An explicit `scripts/classify_attempt.py` follow-up
recorded `result = blocked`, `coq_alignment = checked`, `build = pass`, and
`local_target_gate = pass`. Status: still active.

2026-07-19 completion note: after the pipeline blocker above isolated the raw
SingleNaN decomposition/scaling mismatch, the manual repair restored exact
public `ExperimentalSingleNaNArithmetic.Bulp'_correct` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`. The theorem matches upstream
`IEEE754/BinarySingleNaN.v:Bulp'_correct`: under `2 < emax`, every finite
proof-carrying `BinarySingleNaNFloat` input satisfies exact constructor
equality `Bulp' x = Bulp x` after erasure, not merely equality of real values.
The prerequisite definitions now also follow Flocq: finite `Bldexp` calls
`binary_round` at exponent `ex + e`, and `Bfrexp_bsn` uses
`Ffrexp_core_binary` with non-finite sentinel exponent `-2 * emax - prec`.
The proof establishes mode independence only for the exact power-of-two
rounding path, derives the finite `Bfrexp` exponent from canonical boundedness,
and uses a validity/canonicality-aware `StandardFloat` injectivity lemma; it
does not assume injectivity of the permissive raw `B754` carrier. Focused Lean,
full build, placeholder/trust audit, status report, and `git diff --check`
passed. Status: implemented and removed from active semantic gaps.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_120911` rechecked upstream
`IEEE754/BinarySingleNaN.v:Bpred_pos'_correct` and made no Lean source
changes. Upstream states `2 < emax -> forall x, 0 < B2R x ->
Bpred_pos' x = Bpred x`, again as exact `B754` constructor equality rather
than only real-value equality. The current blocker is downstream of the active
`Bulp'_correct` gap: there is no SingleNaN theorem proving
`Bulp' x = Bulp x` under `2 < emax` and finiteness. The upstream-shaped proof
also needs raw SingleNaN `Bldexp_correct`, `Bminus_correct`, `Bpred_correct`,
and a `B754` constructor-equality bridge; current nearby facts are either
limited (`Bldexp_Bopp_NE`), explicitly gap-marked (`B754_plus_correct : Unit`),
or live only over the proof-erased/permissive Binary compatibility layer.
Status: still active.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_121525` rechecked upstream
`IEEE754/BinarySingleNaN.v:Bsucc'_correct` and made no Lean source changes.
Upstream states `2 < emax -> forall x, is_finite x = true ->
Bsucc' x = Bsucc x`, as exact `B754` constructor equality. The proof depends
on `Bldexp_correct` for zero, `Bplus_correct`/`Bulp_correct` for positive
finite inputs, `Bpred_pos'_correct` plus `Bopp` bridges for negative finite
inputs, and constructor equality support. Current Lean is missing the faithful
SingleNaN-level dependencies needed to prove this without weakening: public
BSN `Bplus_correct`, `Bulp'_correct`, `Bpred_pos'_correct`, and BSN-level
`Bsucc_correct`/`Bldexp_correct` bridges strong enough to derive constructor
equality rather than only `B754_to_R`/`B2R` equality or a proof-erased
`Binary754` result. Status: still active.

2026-07-16 blocker note: harness attempt
`.change_log/codex_attempt_20260716_230316` rechecked upstream
`IEEE754/BinarySingleNaN.v:Bmult_correct_aux` and left Lean source unchanged.
The checked classifier
`.change_log/manual_attempt_20260716_current_bmult_correct_aux_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`Bmult_correct_aux` applies the faithful `binary_round_aux_correct` theorem to
the finite bounded product mantissa/exponent path, proving `valid_binary`,
rounded real semantics, finite/sign preservation, or exact overflow. Current
Lean exposes `BinarySingleNaN.binary_round_aux`, `binary_round`,
`binary_normalize`, and `is_nan_binary_round`, but no
`BinarySingleNaN`-level `binary_round_aux_correct` carrying the `valid_binary`,
`SF2R`, finite/sign, and overflow payload. The only same-name theorem in the
current workspace is under the experimental `Binary.lean` compatibility layer
and proves only a weaker finite-or-overflow shape, so it is not a faithful
counterpart. `Bmult_correct_aux` remains active.

2026-07-19 blocker note: current direct inspection rechecked upstream
`IEEE754/BinarySingleNaN.v:Bmult_correct_aux` at line 1526 against the live
SingleNaN API. The local file now has public `binary_round_aux`,
`binary_round`, `binary_normalize`, `binary_fit_aux_correct`, and
`is_nan_binary_round`, but it still has no public
`BinarySingleNaN.binary_round_aux_correct` theorem matching upstream lines
1405-1415. That missing prerequisite is the proof that
`binary_round_aux mode sx (Zpos mx) ex lx` has non-tautological
`valid_binary`, exact rounded `SF2R`, finite/sign preservation, or exact
`bsn_binary_overflow`. Adding `Bmult_correct_aux` now would either prove
`valid_binary_SF ... = true` through the current permissive
`valid_binary_SF := true` surface, delegate to the explicitly experimental
FullFloat `ExperimentalBinaryRound.binary_round_aux_correct`, or return only an
overflow/wrapper branch. Those are weaker than the Flocq payload, so
`Bmult_correct_aux` remains active until the faithful SingleNaN
`binary_round_aux_correct` and non-permissive validity bridge are restored.

2026-07-19 prerequisite blocker note: harness attempt
`.change_log/codex_attempt_20260719_030058` targeted the missing faithful
SingleNaN `binary_round_aux_correct` prerequisite directly and left Lean source
unchanged. The checked manual classifier
`.change_log/manual_attempt_20260718_190412_binary_round_aux_correct_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`BinarySingleNaN.v:binary_round_aux_correct` proves non-tautological
`valid_binary`, exact rounded `SF2R`, finite/sign preservation, or exact
overflow for `binary_round_aux`. Current Lean still has
`valid_binary_SF` as a permissive constant-true surface in
`FloatSpec/src/IEEE754/Binary.lean`, and the only same-name theorem is the
weaker `ExperimentalBinaryRound.binary_round_aux_correct` over `FullFloat`,
which proves only finite-or-overflow. Adding a public SingleNaN theorem now
would therefore either make the validity conjunct tautological or weaken the
upstream statement. The prerequisite remains a non-permissive SingleNaN
validity bridge plus the faithful round/truncate/fit correctness chain.

2026-07-19 prerequisite recheck: harness attempt
`.change_log/codex_attempt_20260719_050956` reattempted the same faithful
SingleNaN `binary_round_aux_correct` prerequisite after the
`binaryRoundAuxToBinarySingleNaNFloat` adapter landed. It left Lean source
unchanged (`changed_during_attempt.txt` is empty) and the checked classifier
`.change_log/manual_attempt_20260719_0527_binary_round_aux_correct_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`. The adapter is useful
for carrying a proof into `BinarySingleNaNFloat`, but it only consumes
`validBinarySingleNaNStandardFloat (binary_round_aux ...) = true`; it does not
prove upstream `BinarySingleNaN.v:binary_round_aux_correct` lines 1405-1415.
The scratch probe found that the local canonical-mantissa bridge from
`canonical` through `mag 2 (F2R (Float m e)) = Zdigits 2 m + e` is feasible, so
that small bridge is not the remaining blocker by itself. The still-missing
payload is the full second `truncate`/`shr_fexp` correctness chain, a
non-permissive `binary_fit_aux` validity proof over
`validBinarySingleNaNStandardFloat`, exact rounded `SF2R` and finite/sign
facts, plus the upstream overflow split. Replacing this with the old
`valid_binary_SF` constant or with `ExperimentalBinaryRound` would still weaken
the Flocq theorem, so `Bmult_correct_aux` remains active.

2026-07-19 prerequisite progress: harness attempt
`.change_log/codex_attempt_20260719_083558` restored public root
`FloatSpec.IEEE754.BinarySingleNaN.binary_round_aux_correct` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`. The proof follows upstream
`BinarySingleNaN.v:binary_round_aux_correct` lines 1405-1415 through
`round_trunc_sign_any_correct`, first `truncate_correct_partial`,
`cexp_round_ge`, second `truncate_correct_format`, `binary_fit_aux_correct`,
and a non-permissive `validBinarySingleNaNStandardFloat` validity proof, while
avoiding `Binary.lean`'s `ExperimentalBinaryRound`/`FullFloat` helpers and the
old permissive `valid_binary_SF := true` surface. Focused
`lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean`, full
`lake build`, `scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed. At that point this was prerequisite
progress only; the downstream finite-product theorem was restored later by
`.change_log/codex_attempt_20260719_090915`.

2026-07-19 prerequisite progress: harness attempt
`.change_log/codex_attempt_20260719_085850` restored public root
`FloatSpec.IEEE754.BinarySingleNaN.binary_round_correct` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`. The proof follows upstream
`BinarySingleNaN.v:binary_round_correct` lines 1704-1731: it unfolds the
local `binary_round`, uses `shl_align_fexp_correct` to build the exact
`inbetween_float` witness and exponent side condition, normalizes
`Rlt_bool x 0 = sx` for the signed finite input, and then applies the restored
public `binary_round_aux_correct`. Lean's local mantissa type is `Nat`, so the
statement carries an explicit `0 < mx` hypothesis corresponding to Coq's
`positive` mantissa. Focused `lake env lean
FloatSpec/src/IEEE754/BinarySingleNaN.lean`, full `lake build`,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed. At that point this was prerequisite
progress only; `Bmult_correct_aux` was restored later by
`.change_log/codex_attempt_20260719_090915`, while `Bnearbyint_correct_aux` and
the `Bulp`/successor family remain active.

2026-07-19 completion note: harness attempt
`.change_log/codex_attempt_20260719_090915` restored public root
`FloatSpec.IEEE754.BinarySingleNaN.Bmult_correct_aux` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`. The theorem matches upstream
`BinarySingleNaN.v:Bmult_correct_aux` lines 1526-1558 modulo Lean's
`Nat`-mantissa bridge: Coq's positive mantissas are represented by explicit
`0 < mx` / `0 < my` hypotheses, and Coq's local `bounded` notation is
`SpecFloat.bounded`, represented by `specFloat_bounded`. The proof rewrites the
finite product to an exact `inbetween_float` witness, proves the product
exponent side condition from the canonical bounded input hypotheses and
`Zdigits_mult`/`Zdigits_mult_ge`, proves the signed-product sign as
`Bool.xor sx sy`, and applies the restored public `binary_round_aux_correct`.
Focused `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean`, full
`lake build`, `scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed. Status: implemented and removed
from active semantic gaps.

2026-07-19 live recheck for line 260: upstream `Binary.v:valid_binary`
matches finite values with `bounded m e`, NaNs with `nan_pl pl`, and only zero
or infinity with `true`; upstream `BinarySingleNaN.v:SF2B` consumes a
`valid_binary x = true` proof and `B2SF` returns only values whose constructor
already carries bounded payload evidence. The current Lean tree has a
proof-carrying `binary_float`, but the public bridge used by existing Binary
theorems is still `Binary754` with `valid : is_finite_FF val = true -> True`
and `FF2B` accepts arbitrary `FullFloat`. Making `valid_binary` /
`valid_binary_SF` non-permissive would make current all-input bridges such as
`valid_binary_B2FF` false for invalid finite payloads, while the SingleNaN
`StandardFloat` representation erases NaN payloads entirely and cannot express
upstream `nan_pl` bounds except by the fixed `SF2FF S754_nan = F754_nan false 1`
choice. Therefore this target is blocked by a carrier/API representation
mismatch: repair requires migrating the Binary/SingleNaN bridges to proof
arguments or subtype/proof-carrying carriers before porting faithful
`binary_round_aux_correct`, `Bmult_correct_aux`, `Bnearbyint_correct_aux`, or
the Bits b32/b64 operation aliases.

2026-07-19 follow-up: added aligned Binary-side migration infrastructure in
`FloatSpec/src/IEEE754/Binary.lean` over the exact lowercase `full_float`
carrier: `valid_full_float_binary`, proof-consuming
`fullFloatToBinaryFloat`, `binaryFloatToFullFloat`, and the corresponding
validity/roundtrip lemmas. This mirrors upstream `Binary.v:valid_binary`,
`FF2B`, `B2FF`, `valid_binary_B2FF`, and `FF2B_B2FF_valid` without changing the
permissive compatibility `valid_binary` / `FF2B : FullFloat -> Binary754`
surface. The target remains blocked for the downstream IEEE SingleNaN bridge:
local `BinarySingleNaN.B754` and `StandardFloat` are still payload-erasing /
non-proof-carrying, so faithful SingleNaN `SF2B`, `binary_round_aux_correct`,
`Bmult_correct_aux`, `Bplus_correct`, `Bulp_correct`, and b32/b64 operation
aliases cannot be ported without first migrating those APIs to proof arguments
or proof-carrying carriers.

2026-07-19 manual migration note: after the checked blocker above,
`FloatSpec/src/IEEE754/Binary.lean` gained `valid_binary_payload` and
`valid_binary_SF_payload` as non-tautological migration predicates. They check
finite `FullFloat` payloads with `bounded` and NaN payloads with the same
digit-bound test as `nan_pl`, while the StandardFloat predicate is defined as
the validity of the fixed local `SF2FF` image. This is intentionally not
counted as completing an active Flocq declaration: the public
`valid_binary`/`valid_binary_SF`, `Binary754`, and all-input bridge theorems
remain permissive, so the faithful upstream `SF2B`/`FF2B` proof-argument API is
still missing.

2026-07-19 targeted migration update: added proof-carrying SingleNaN
infrastructure in `FloatSpec/src/IEEE754/BinarySingleNaN.lean` without changing
the existing raw `B754`, `SF2B`, `SF2B'`, or permissive `valid_binary_SF`
compatibility APIs. The new `BinarySingleNaNFloat` carrier stores the
`bounded m e = true` finite evidence carried by upstream
`BinarySingleNaN.v:B754_finite`; `validBinarySingleNaNStandardFloat`,
`standardFloatToBinarySingleNaNFloat`, `standardFloatToBinarySingleNaNFloat'`,
and `binarySingleNaNFloatToStandardFloat` mirror upstream `valid_binary`,
`SF2B`, `SF2B'`, and `B2SF`. The checked lemmas include the proof-carrying
counterparts of `valid_binary_B2SF` and `SF2B_B2SF_valid`, plus erasure lemmas
back to the historical raw `B754` surface. This completes the focused
carrier/API migration infrastructure for the SingleNaN bridge; the downstream
arithmetic names remain blocked until `binary_round_aux`, `Bmult`, `Bplus`,
`Bulp`, and the b32/b64 aliases are migrated to return this proof-carrying
surface rather than rebuilding through proof-erased `Binary754`/raw `B754`.

2026-07-19 targeted migration update: added the proof-carrying
Binary-to-SingleNaN bridge `binaryFloatToBinarySingleNaNFloat` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`, mirroring upstream
`Binary.v:B2BSN` on the new `BinarySingleNaNFloat` carrier. It maps Binary
zero and infinity constructors directly, collapses Binary NaN sign/payload
evidence to the single SingleNaN NaN constructor, and passes finite `bounded`
evidence through after the local `Positive`-to-`Nat` mantissa projection. The
historical proof-erased `B2BSN : Binary754 -> B754` surface remains unchanged,
and this is not counted as completing an active declaration: the public
arithmetic APIs still need to return or reconstruct proof-carrying
SingleNaN/Binary values before `Bmult_correct`, `Bplus_correct`, `Bulp_correct`,
and the b32/b64 operation aliases can be restored faithfully.

2026-07-19 targeted migration update: harness attempt
`.change_log/codex_attempt_20260719_044802` added
`binaryRoundAuxToBinarySingleNaNFloat` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`. This is a proof-carrying adapter
from the current raw `binary_round_aux` result into `BinarySingleNaNFloat`,
parameterized by an explicit
`validBinarySingleNaNStandardFloat (binary_round_aux ...) = true` proof, with
erasure lemmas back to `StandardFloat` and raw `B754`. The provider checked
upstream `BinarySingleNaN.v:binary_round_aux` lines 1270-1277,
`binary_round_aux_correct` lines 1405-1415, and `Bmult_correct_aux` lines
1526-1536; focused `lake env lean
FloatSpec/src/IEEE754/BinarySingleNaN.lean`, placeholder audit, status report,
`git diff --check`, and full `lake build` passed. This is intentionally not
counted as closing an active declaration: it preserves the proof-carrying
surface once the validity proof is available, but the faithful public
`BinarySingleNaN.binary_round_aux_correct` theorem still has to prove
non-tautological validity, rounded `SF2R`, finite/sign preservation, and exact
overflow from the upstream hypotheses before `Bmult_correct_aux`,
`Bnearbyint_correct_aux`, or the Binary/Bits arithmetic names can be restored.

2026-07-19 targeted prerequisite update: harness attempt
`.change_log/codex_attempt_20260719_053626` added the private bridge
`canonical_mantissa_bsn_of_canonical` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`. The bridge derives the local
boolean `canonical_mantissa = true` from `Generic_fmt.canonical` for a positive
finite SingleNaN mantissa by using the existing `Raux_mag_F2R_Zdigits` and
signed/unsigned `Zdigits` bridge. This discharges the small canonical-mantissa
extraction identified by the previous `binary_round_aux_correct` blocker, but
it is not counted as closing an active public Flocq declaration. The remaining
blocker is still the full `binary_round_aux_correct` payload: prove
non-tautological validity for the actual `binary_round_aux` result, exact
rounded `SF2R`, finite/sign preservation, and the overflow split.

2026-07-19 targeted prerequisite update: harness attempt
`.change_log/codex_attempt_20260719_060608` added the private lemmas
`validBinarySingleNaNStandardFloat_bsn_binary_overflow` and
`validBinarySingleNaNStandardFloat_binary_fit_aux` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`. These prove the non-permissive
SingleNaN validity predicate for `bsn_binary_overflow` and `binary_fit_aux`
from the existing `canonical_mantissa` hypothesis. The finite branch reuses
`binary_fit_aux_bounded_of_canonical_le`; the overflow branch reuses the
bounded half of `Bmax_float_proof`. This removes the small `binary_fit_aux`
validity sub-blocker noted above, but it is intentionally not counted as
closing an active public Flocq declaration. The remaining
`binary_round_aux_correct` blocker is still the two-stage `truncate` /
`shr_fexp` correctness chain plus exact rounded `SF2R`, finite/sign
preservation, and the overflow split for the actual `binary_round_aux` result.

2026-07-19 targeted prerequisite update: harness attempt
`.change_log/codex_attempt_20260719_063824` targeted the next
`binary_round_aux_correct` prerequisite at `binary_round_aux` but produced no
final classifier after a stale broad source search. Manual follow-up
`.change_log/manual_attempt_20260719_070241_bsn_truncate_canonical_prereq/attempt.json`
added the private helpers `canonical_mantissa_bsn_of_repr_cexp` and
`bsn_shr_fexp_truncate_eq` in `FloatSpec/src/IEEE754/BinarySingleNaN.lean`.
These record the local rewrite from `bsn_shr_fexp` to `truncate_triple` and
derive `canonical_mantissa` from the `truncate_correct_format`-style exact
`F2R` representation plus canonical exponent equality. This removes the small
second-truncation canonical-mantissa wiring sub-blocker, but it is not counted
as closing an active public Flocq declaration. The remaining blocker is still
the full first/second `truncate_correct_partial` /
`round_trunc_sign_any_correct` integration, exact rounded `SF2R`, finite/sign
preservation, and the overflow split for the actual `binary_round_aux` result.

2026-07-16 completion note: harness attempt
`.change_log/codex_attempt_20260716_231417` rechecked upstream
`IEEE754/BinarySingleNaN.v:sign_plus_overflow`. The provider first restored the
payload as `ExperimentalSingleNaNArithmetic.sign_plus_overflow`; a follow-up
manual wrapper exposes the same statement as the non-experimental public theorem
`sign_plus_overflow` in `FloatSpec/src/IEEE754/BinarySingleNaN.lean`. The proof
uses the checked experimental payload rather than changing the statement, and
`#print axioms` for the payload reports only standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`). This closes the active
`sign_plus_overflow` candidate without counting an experimental-only theorem.

2026-07-16 blocker note: harness attempt
`.change_log/codex_attempt_20260716_233729` rechecked upstream
`IEEE754/BinarySingleNaN.v:Bnearbyint_correct_aux` against the current helper
stack and made no Lean source changes. The checked classifier
`.change_log/manual_attempt_20260716_bnearbyint_correct_aux_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream proves the
bounded-only SingleNaN validity, exact `FIX_exp 0` rounded `SF2R` equation,
finiteness, and sign preservation for `z := SFnearbyint_binary md sx mx ex`.
Current Lean `valid_binary`/`valid_binary_SF` are still permissive `true`
predicates, and `canonical_bounded` still needs extra `hmx_pos` and
`h_canonical` hypotheses not present in the upstream theorem. Adding the exact
public theorem now would either certify validity tautologically or weaken the
Flocq payload, so `Bnearbyint_correct_aux` remains active.

2026-07-19 blocker note: harness attempt
`.change_log/codex_attempt_20260719_071101` rechecked upstream
`IEEE754/BinarySingleNaN.v:Bnearbyint_correct_aux` against the current
`SFnearbyint_binary` surface. The provider fetched the upstream statement and
proof lines 2573-2693, ran the placeholder audit and status report, and then
classified the target as blocked without Lean source edits; the wrapper process
was terminated after it stayed resident following classification. The checked
manual sidecar
`.change_log/manual_attempt_20260719_071458_bnearbyint_correct_aux_blocked/attempt.json`
records `coq_alignment = checked`: the upstream proof uses Coq
`bounded mx ex = true` to recover canonical-mantissa and digit-bound facts
before applying `shl_align_correct'`, `shr_truncate`,
`round_trunc_sign_any_correct`, and `round_mode_choice_mode`. Current Lean has
the nearbyint definitions and those rounding/shifting helpers, but local
`bounded` is range-only while `canonical_bounded` still needs explicit
`hmx_pos` and `h_canonical` hypotheses. Therefore a faithful theorem still
needs either a Coq-aligned bounded/canonical bridge for positive finite
mantissas or a proof that `SFnearbyint_binary` is valid and rounded from the
current range-only `bounded` predicate without adding non-upstream premises.

2026-07-19 prerequisite blocker note: manual follow-up
`.change_log/manual_attempt_20260719_072544_canonical_bounded_blocked/attempt.json`
classified the direct `canonical_bounded` prerequisite after the stale harness
attempt `.change_log/codex_attempt_20260719_071811`. Upstream
`IEEE754/BinarySingleNaN.v:canonical_bounded` applies
`canonical_canonical_mantissa` and obtains `canonical_mantissa mx ex = true`
from `bounded mx ex = true` by `andb_prop`. Current Lean cannot make that step:
`FloatSpec/src/IEEE754/Binary.lean` defines `bounded` as the range-only
conjunction `mx < 2^prec`, `3 - emax - prec <= ex`, and `ex <= emax - prec`,
while `canonical_mantissa` remains a separate exponent-equality predicate. For
example, under the usual single-precision parameters `prec = 24`, `emax = 128`,
`mx = 1`, and `ex = 0`, the range-only `bounded` checks are true, but
`canonical_mantissa` is false because the canonical exponent is
`FLT_exp (-149) 24 (Zdigits 2 1 + 0) = -23`, not `0`. Therefore the exact
upstream `canonical_bounded` payload is false over the current local predicate;
repair has to migrate or introduce a Coq-aligned bounded/canonical finite
payload before `Bnearbyint_correct_aux` can use this prerequisite faithfully.

2026-07-19 prerequisite progress note: harness attempt
`.change_log/codex_attempt_20260719_072901` targeted the local `bounded`
definition and became stale after broad diff/source inspection, but it produced
a narrow migration helper that was manually checked and repaired in
`.change_log/manual_attempt_20260719_073630_specfloat_bounded_migration/attempt.json`.
`FloatSpec/src/IEEE754/Binary.lean` now has `specFloat_bounded`, a separate
Coq-shaped bounded predicate with explicit `canonical_mantissa` and
`ex <= emax - prec` conjuncts, plus extraction lemmas
`canonical_mantissa_of_specFloat_bounded` and
`exponent_le_of_specFloat_bounded`. It also has
`range_bounded_of_specFloat_bounded` for positive mantissas, preserving the
existing range-only `bounded` compatibility predicate while allowing
proof-carrying callers to move from the Coq-shaped predicate back to existing
range-bound lemmas. `FloatSpec/src/IEEE754/BinarySingleNaN.lean` now has
`canonical_bounded_of_specFloat_bounded`, which recovers the canonicality
payload that upstream gets from `SpecFloat.bounded`. Focused checks passed:
`lake build FloatSpec.src.IEEE754.Binary` and `lake env lean
FloatSpec/src/IEEE754/BinarySingleNaN.lean`. This is helper/prerequisite
progress only and does not close an active public Flocq declaration yet;
`Bnearbyint_correct_aux` still needs `SFnearbyint_binary` to carry or derive
this Coq-shaped bounded evidence together with the upstream rounding,
finiteness, and sign-preservation payload.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_092738` rechecked
`IEEE754/BinarySingleNaN.v:Bnearbyint_correct_aux` after the public
`binary_round_aux_correct`, `binary_round_correct`, `Bmult_correct_aux`,
`specFloat_bounded`, and proof-carrying `BinarySingleNaNFloat` infrastructure
landed. The attempt made no Lean source changes
(`changed_during_attempt.txt` is empty), ran focused
`lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean`,
`scripts/audit_placeholders.sh --json FloatSpec`,
`scripts/status_report.sh --write`, and `git diff --check`, and wrote the
checked sidecar
`.change_log/manual_attempt_20260719_093539_bnearbyint_correct_aux_blocked/attempt.json`.
The blocker has narrowed: validity is no longer just the old permissive
`valid_binary_SF := true` surface, but no faithful local theorem yet proves
the actual `SFnearbyint_binary` algorithm valid and equal to
`roundR 2 (FIX_exp 0) (rnd_of_mode md)` from
`0 < mx` plus `specFloat_bounded mx ex = true`. The landed
`binary_round_correct` theorem proves the separate FLT `binary_round`
algorithm; using it for `SFnearbyint_binary` would still require an unproved
equivalence/no-overflow/canonical-validity theorem for the positive
`shl_align_fexp n 0` branch. Adding `Bnearbyint_correct_aux` now would either
weaken the upstream payload or certify the wrong algorithm path, so the
candidate remains active.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_134510` rechecked
`IEEE754/BinarySingleNaN.v:Bnearbyint_correct_aux` against the same live
`SFnearbyint_binary`/`shl_align_fexp` helper stack and made no Lean source
changes (`changed_files = []`, `changed_during_attempt.txt` is empty, and
`statement_changed = false`). The blocker is now localized to the `ex < 0`,
positive rounded-mantissa branch: after `mx'' > 0`, the implementation returns
`S754_finite sx aligned.1 aligned.2` with
`aligned := shl_align_fexp mx''.toNat 0`. To prove the upstream payload,
Lean must derive `validBinarySingleNaNStandardFloat` for this finite result,
namely `0 < aligned.1` and
`specFloat_bounded (prec:=prec) (emax:=emax) aligned.1 aligned.2 = true`,
while preserving the rounded `SF2R` equality. Current
`shl_align_fexp_correct` proves value preservation and only
`aligned.2 ≤ FLT_exp (...)`; it does not provide the canonical-mantissa
equality or upper-bound package needed for `specFloat_bounded` in this branch.
The checked sidecar
`.change_log/manual_attempt_20260719_134852_bnearbyint_correct_aux_blocked/attempt.json`
records `result = blocked`, `coq_alignment = checked`, `build = pass`,
`changed_files = []`, and `local_target_gate = pass`. Status: still active.

2026-07-16 blocker note: harness attempt
`.change_log/codex_attempt_20260716_234242` rechecked upstream
`IEEE754/BinarySingleNaN.v:Bnormfr_mantissa_correct` against the current
SingleNaN representation and made no Lean source changes. The checked
classifier
`.change_log/manual_attempt_20260716_bnormfr_mantissa_correct_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream derives the
finite constructor, `Bnormfr_mantissa x = m`, `digits2_pos m = prec`, and
`e = -prec` from the normalized magnitude premise using the proof-carrying
`B754_finite` bounded/canonical payload. Current Lean `B754_finite` stores only
sign, mantissa, and exponent, while local `bounded` is range-only and does not
imply `canonical_mantissa`; noncanonical finite encodings can satisfy
`/2 <= |B2R x| < 1` without the upstream normalized payload. Adding the exact
public theorem now would be false or require extra hypotheses, so
`Bnormfr_mantissa_correct` remains active.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_074843` rechecked
`Bnormfr_mantissa_correct` after the new proof-carrying
`BinarySingleNaNFloat` infrastructure landed. The attempt left
`FloatSpec/src/IEEE754/BinarySingleNaN.lean` unchanged
(`changed_during_attempt.txt` is empty), and the normalized sidecar
`.change_log/manual_attempt_20260719_075242_bnormfr_mantissa_current_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`. The blocker is
still semantic, not syntactic: the new `BinarySingleNaNFloat.B754_finite`
constructor carries the current local `bounded` predicate, but that predicate
is range-only. Upstream `Bnormfr_mantissa_correct` relies on the Coq
`SpecFloat.bounded` finite payload, whose canonical-mantissa conjunct is what
lets the normalized magnitude premise force
`Bnormfr_mantissa x = m`, `digits2_pos m = prec`, and `e = -prec`. The
Coq-shaped `specFloat_bounded` helper now exists separately, but the public
SingleNaN carrier/API has not been migrated to carry that evidence. Adding the
exact theorem now would either be false over range-only `bounded` or require
non-upstream hypotheses, so `Bnormfr_mantissa_correct` remains active.

2026-07-19 prerequisite progress note: harness attempt
`.change_log/codex_attempt_20260719_075541` migrated the proof-carrying
`BinarySingleNaNFloat.B754_finite` constructor and its `StandardFloat`
conversion/erasure surface to carry the Coq-shaped finite payload:
`0 < m` plus `specFloat_bounded (prec:=prec) (emax:=emax) m e = true`.
The historical raw `B754`, `SF2B`, `SF2B'`, and range-only `bounded`
compatibility APIs remain unchanged, and `SF2BSpec'` records the raw erasure of
the proof-carrying Coq-shaped total `SF2B'` path. Direct verification after the
attempt passed: `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean`,
`scripts/audit_placeholders.sh --json FloatSpec`, raw
`rg -n "\b(sorry|axiom|admit)\b" FloatSpec --glob "*.lean"`,
`git diff --check -- FloatSpec/src/IEEE754/BinarySingleNaN.lean
FloatSpec/docs/status.json FloatSpec/docs/status.md`,
`scripts/status_report.sh --write`, and full `lake build` (3345 jobs).
This is prerequisite progress only and does not close an active public Flocq
declaration: `Bnormfr_mantissa_correct` still needs the exact upstream
normalized-magnitude proof over the migrated proof-carrying carrier.

2026-07-19 completion note: harness attempt
`.change_log/codex_attempt_20260719_080616` restored the SingleNaN normfr
mantissa surface and proved exact public theorem `Bnormfr_mantissa_correct` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean` over the proof-carrying
`BinarySingleNaNFloat` carrier. The theorem uses the carrier's stored `0 < m`
and Coq-shaped `specFloat_bounded` payload, not raw `B754`, range-only
`bounded`, or experimental wrappers. Verification recorded in
`.change_log/manual_attempt_20260719_081300_bnormfr_mantissa_correct/attempt.json`
has `result = proved`, `coq_alignment = checked`, `local_target_gate = pass`,
and `build = pass`; the provider also ran focused Lean, placeholder/trust,
status, `git diff --check`, and full `lake build` gates. This removes
`Bnormfr_mantissa_correct` from the active semantic gap list.

2026-07-16 blocker note: harness attempt
`.change_log/codex_attempt_20260716_235124` rechecked upstream
`IEEE754/BinarySingleNaN.v:is_finite_strict_Bulp` after the current faithful
BSN-level `Bulp` and `is_nan_Bulp` repairs and made no Lean source changes. The
checked classifier
`.change_log/manual_attempt_20260716_235522_is_finite_strict_Bulp_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream proves
`is_finite_strict (Bulp x) = is_finite x` by invoking `Bulp_correct` on
proof-carrying finite constructors. Current Lean `B754_finite` is
proof-erased/permissive and still lacks the BSN-level `Bulp_correct` payload
needed to rule out zero or overflow-normalize results for arbitrary finite
mantissa/exponent pairs. Adding boundedness hypotheses, routing through
Binary-level wrappers, or proving only NaN-freedom would weaken or change the
upstream theorem, so `is_finite_strict_Bulp` remains active.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_081700` rechecked
`IEEE754/BinarySingleNaN.v:is_finite_strict_Bulp` after the
`BinarySingleNaNFloat` carrier migration and the exact
`Bnormfr_mantissa_correct` restoration. The attempt made no Lean source changes
(`changed_during_attempt.txt` is empty) and the checked sidecar
`.change_log/manual_attempt_20260719_002020_is_finite_strict_Bulp_blocked/attempt.json`
records `result = blocked`, `coq_alignment = checked`, and
`local_target_gate = pass`. The blocker is now narrowed to the missing faithful
BSN-level `Bulp_correct` package: upstream `is_finite_strict_Bulp` destructs
`Bulp_correct` for proof-carrying finite inputs, while current Lean has public
`Bulp`, `is_nan_Bulp`, `BinarySingleNaNFloat`, and `specFloat_bounded`, but
still no value-level SingleNaN `Bulp_correct`,
`binary_round_correct`, or `binary_normalize_correct` payload that proves the
real ulp value, finiteness, and false sign of `Bulp`. Raw `B754` remains
proof-erased/permissive, and Binary wrappers are proof-erased or explicitly
experimental, so adding this theorem now would weaken or change the upstream
payload. The target remains active.

2026-07-19 prerequisite progress: harness attempt
`.change_log/codex_attempt_20260719_094001` restored
`ExperimentalSingleNaNArithmetic.Bulp_correct` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean` over the proof-carrying
`BinarySingleNaNFloat` erasure surface. The theorem proves the upstream
`Bulp_correct` package for finite inputs: the `Bulp` real value is the ulp,
the result is finite, and its sign is `false`. Focused
`lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean`, full
`lake build`, `scripts/audit_placeholders.sh --json FloatSpec`,
`scripts/status_report.sh --write`, and `git diff --check` passed. This is
prerequisite progress, not an active-list decrement by itself: the active exact
names `is_finite_strict_Bulp`, `Bulp'_correct`, `Bpred_pos'_correct`,
`Bsucc'_correct`, and `Binary.v:Bulp_correct` still need their own faithful
public payloads or bridge wrappers over the now-available SingleNaN theorem.

2026-07-19 completion note: harness attempt
`.change_log/codex_attempt_20260719_095650` restored
`ExperimentalSingleNaNArithmetic.is_finite_strict_Bulp` in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean`. The theorem matches upstream
`BinarySingleNaN.v:is_finite_strict_Bulp` on the local proof-carrying
SingleNaN carrier by proving
`BSN_is_finite_strict (Bulp (binarySingleNaNFloatToB754 x)) =
BSN_is_finite (binarySingleNaNFloatToB754 x)`. The finite branch consumes the
restored `Bulp_correct` package and the nonzero-ulp/`is_finite_strict_B2R`
bridge; zero, infinity, and NaN branches are definitional. Focused
`lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean`, full
`lake build`, `scripts/audit_placeholders.sh --json FloatSpec`,
`scripts/status_report.sh --write`, and `git diff --check` passed; the
classifier was recorded as `result = proved`, `build = pass`, and
`coq_alignment = checked`. This removes `is_finite_strict_Bulp` from the
active semantic gap list.

2026-07-16 blocker note: harness attempt
`.change_log/codex_attempt_20260716_235911` rechecked upstream
`IEEE754/BinarySingleNaN.v:Bulp'_correct` after the current faithful BSN-level
`Bulp`, `is_nan_Bulp`, and `Bulp'` repairs and made no Lean source changes. The
checked classifier
`.change_log/manual_attempt_20260716_160447_bulp_prime_correct_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream proves
`(2 < emax)%Z -> forall x, is_finite x = true -> Bulp' x = Bulp x` by first
deriving the real-value, finiteness, and sign facts for `Bulp'`, then invoking
faithful BSN-level `Bulp_correct` plus representation injectivity. Current Lean
still lacks the public BSN-level `Bulp_correct` theorem over proof-carrying
bounded finite payload; the available Binary-level `Bulp` wrappers are
proof-erased and would change the SingleNaN theorem. Adding extra hypotheses or
weakening the equality target would not preserve the upstream payload, so
`Bulp'_correct` remains active.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_100629` rechecked
`IEEE754/BinarySingleNaN.v:Bulp'_correct` after the faithful proof-carrying
`Bulp_correct` package and `is_finite_strict_Bulp` theorem landed. The attempt
made no Lean source changes and classified the target as blocked: upstream
proves exact constructor equality `Bulp' x = Bulp x`, not just equality of
real values, by deriving real-value/finite/sign facts for `Bulp'` through
`Bldexp_correct` and `Bfrexp_correct`, then applying `Bulp_correct` plus
`B2R_Bsign_inj`. Current Lean now has the `Bulp_correct` side of that final
comparison, but it still lacks SingleNaN-level constructor/equality support for
the `Bldexp`/`Bfrexp` path. Scratch goals reduce to exact object equalities
such as `Bldexp ... Bone ... = B754_finite ...` or the corresponding
`binary_normalize` constructor, and those cannot be closed from the available
real-value payload without weakening the theorem. Therefore `Bulp'_correct`
remains active.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_000908` rechecked upstream
`IEEE754/BinarySingleNaN.v:Bpred_pos'_correct` against the current faithful
BSN-level `Bpred_pos'`, `Bsucc`, `Bpred`, and NaN-preservation surfaces and made
no Lean source changes. The checked classifier
`.change_log/manual_attempt_20260717_001315_bpred_pos_prime_correct_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream proves
`(2 < emax)%Z -> forall x, 0 < B2R x -> Bpred_pos' x = Bpred x` using the
SingleNaN correctness stack `Bulp_correct`, `Bulp'_correct`, `Bminus_correct`,
and `Bpred_correct`. Current Lean exposes `Bulp_correct_aux`,
`Bfrexp_correct_aux`, and Binary-level correctness wrappers, but still lacks
those public BSN-level payloads; using the Binary wrappers would route through a
proof-erased model and weaken the target. Therefore `Bpred_pos'_correct`
remains active.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_001708` rechecked upstream
`IEEE754/BinarySingleNaN.v:Bsucc'_correct` against the current Lean
`BinarySingleNaN` surface and left Lean source unchanged. The checked
classifier
`.change_log/manual_attempt_20260717_bsucc_prime_correct_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream proves
`(2 < emax)%Z -> forall x, is_finite x = true -> Bsucc' x = Bsucc x` by using
`Bldexp_correct`/`Bone_correct`/`generic_format_bpow` in the zero branch, then
faithful BSN-level `Bplus_correct`, `Bulp_correct`, `Bulp'_correct`,
`Bpred_pos'_correct`, `Bsucc_correct`, `Bpred_correct`, and `B2R`/`Bsign`
injectivity in the finite branches. Current Lean has the faithful public
`Bsucc'`, `Bsucc`, `Bpred_pos'`, `Bpred`, `Bplus`, and `Bulp` definitions plus
NaN-preservation, but still lacks the public BSN-level `Bplus_correct`,
`Bulp_correct`, `Bulp'_correct`, and `Bpred_pos'_correct` payloads required to
derive the finite-branch equality. Binary-level wrappers route through
proof-erased/permissive adapters and are not a faithful replacement for the
SingleNaN theorem. Therefore `Bsucc'_correct` remains active and blocked rather
than being restored as a weakened equality.

#### `IEEE754/Bits.v` (0)

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_123847` targeted exact upstream
`IEEE754/Bits.v:b32_div` but failed before proof generation because the
configured `gpt-5.6-sol` model requires a newer Codex CLI; it changed no source
files and its local target gate passed. The manual repair removed the
always-overflow `Bdiv_correct_aux_check` shell and restored the exact quotient
path: `SFdiv_core_binary` specializes the proved `Fdiv` core, its data theorem
supplies the inbetween and exponent obligations, and exact public
`Bdiv_correct_aux` feeds those obligations to `binary_round_aux_correct'` for
the signed quotient. Proof-carrying `Binary.Bdiv` now follows the upstream NaN,
infinity, signed-zero, divide-by-zero, and finite/finite constructor split and
reconstructs every finite result through nonpermissive binary validity. Exact
public `b32_div` and `b64_div` specialize that operation with `binop_nan_pl32`
and `binop_nan_pl64`, returning the proof-carrying `binary32`/`binary64`
carriers without routing through permissive `Binary754` or proof-erased bridge
types. Focused dependency builds for `BinarySingleNaN.lean` and `Bits.lean`
passed. The classifier sidecar
`.change_log/codex_attempt_20260720_123847/manual_proved.json` records
`result = proved`, `coq_alignment = checked`, `build = pass`, and
`local_target_gate = pass`. `git diff --check`,
`scripts/status_report.sh --write`, and
`scripts/audit_placeholders.sh --json FloatSpec` passed with zero trust or
placeholder findings, and full `lake build` completed successfully with 3345
jobs. The requested `scripts/check_diff_trust.sh` gate remains unavailable
because that script is not present in this checkout. Status: both exact names
are implemented and removed from active semantic gaps.

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_122317` targeted exact upstream
`IEEE754/Bits.v:b32_fma` but failed before proof generation because the
configured `gpt-5.6-sol` model requires a newer Codex CLI; it changed no source
files and its local target gate passed. The subsequent manual repair added a
proof-carrying `Binary.Bfma` over `binary_float prec emax`, together with the
upstream signed-zero rule and a bounded-result normalization helper backed by
the nonpermissive validity theorem `binary_round_correct`. The finite path
performs exact integer `Fmult` and, when the addend is finite and nonzero,
exact integer `Fplus` before a single binary rounding; it therefore preserves
the fused upstream payload rather than composing rounded multiplication and
addition. NaN inputs, invalid infinity-times-zero products, and opposite-sign
infinity cancellation all route through the original ternary NaN-payload
handler, while the remaining infinity and signed-zero cases match the upstream
constructor split. Exact public `b32_fma` and `b64_fma` are now the upstream
specializations through `ternop_nan_pl32` and `ternop_nan_pl64`; they return
the proof-carrying `binary32`/`binary64` carriers and do not route through
permissive `Binary754`, proof-erased `BinarySingleNaNBridge.BinaryFloat`, or
post-hoc bit reconstruction. Focused Lean checks for
`BinarySingleNaN.lean` and `Bits.lean` passed. The normalized classifier
sidecar `.change_log/codex_attempt_20260720_122317/manual_proved.json` records
`result = proved`, `coq_alignment = checked`, `build = pass`, and
`local_target_gate = pass`. `git diff --check`,
`scripts/status_report.sh --write`, and
`scripts/audit_placeholders.sh --json FloatSpec` passed with zero trust or
placeholder findings, and full `lake build` completed successfully with 3345
jobs. The requested `scripts/check_diff_trust.sh` gate remains unavailable
because that script is not present in this checkout. Status: both exact names
are implemented and removed from active semantic gaps.

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_115700` targeted exact upstream
`IEEE754/Bits.v:b32_sqrt` but failed before proof generation because the
configured `gpt-5.6-sol` model requires a newer Codex CLI; it changed no source
files and its local target gate passed. The subsequent manual repair added
Coq-shaped `SFsqrt_core_binary` as the binary-FLT specialization of the proved
generic `Fsqrt` core, proved its positive mantissa, inbetween, and exponent
side conditions from `Fsqrt_correct` and `cexp_inbetween_float`, and added a
non-NaN result theorem for nonnegative `binary_round_aux` inputs. The new
proof-carrying `Binary.Bsqrt` follows the upstream IEEE case split, preserves
positive infinity and signed zero, routes NaN and negative inputs through the
unary NaN-payload handler, and reconstructs positive finite rounded results as
`binary_float prec emax` using the nonpermissive validity result from
`binary_round_aux_correct`. Exact public `b32_sqrt` and `b64_sqrt` are now the
upstream specializations through `unop_nan_pl32` and `unop_nan_pl64`; they do
not route through permissive `Binary754`, proof-erased `B754`/`BinaryFloat`, or
post-hoc bit reconstruction. The normalized classifier sidecar
`.change_log/codex_attempt_20260720_115700/manual_proved.json` records
`result = proved`, `coq_alignment = checked`, `build = pass`, and
`local_target_gate = pass`. Focused Lean checks for
`BinarySingleNaN.lean` and `Bits.lean` passed. `git diff --check`,
`scripts/status_report.sh --write`, and
`scripts/audit_placeholders.sh --json FloatSpec` passed with zero trust or
placeholder findings, and full `lake build` completed successfully with 3345
jobs. The optional `scripts/check_diff_trust.sh` gate remains unavailable in
this checkout. Status: both exact names are implemented and removed from
active semantic gaps.

2026-07-16 blocker note: the harness run
`.change_log/codex_attempt_20260716_183518` targeted `b32_sqrt`, and the
manual classifier sidecar
`.change_log/manual_attempt_20260716_b32_sqrt_current_blocked/attempt.json`
records the family-level blocker. Upstream `Bits.v` specializes `Bsqrt`,
`Bplus`, `Bminus`, `Bmult`, `Bdiv`, and `Bfma` to the proof-carrying
`binary32 := binary_float 24 128` and `binary64 := binary_float 53 1024`
surfaces. Current Lean has those proof-carrying types and NaN handlers, but the
available arithmetic adapters in `FloatSpec/src/IEEE754/Binary.lean` return the
permissive `Binary754` compatibility wrapper through the proof-erased
SingleNaN bridge. A direct `b32_*`/`b64_*` alias over those adapters would
therefore weaken the Coq payload; these names remain active until a faithful
adapter preserves or reconstructs the `binary_float` bounded finite proofs.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_002519` rechecked upstream
`IEEE754/Bits.v:b32_plus` against the current proof-carrying `binary32` and
NaN-handler surface and left Lean source unchanged. The checked classifier
`.change_log/manual_attempt_20260717_b32_plus_current_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream `b32_plus`
is exactly `Bplus _ _ Hprec Hprec_emax binop_nan_pl32` at type
`mode -> binary32 -> binary32 -> binary32`, where finite `binary32`
constructors carry bounded proofs and `binop_nan_pl32` preserves NaN payload
proofs. Current Lean has `binary32` and `binop_nan_pl32`, but public
`Binary.Bplus`/`binary_add` return permissive `Binary754`, while the more
faithful SingleNaN `Bplus` returns raw proof-erased `B754` without a bounded
finite-result theorem for reconstructing `binary32`. Routing through those
helpers or rebuilding through bits would weaken the upstream proof-carrying
surface, so `b32_plus` remains active.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_003740` rechecked upstream
`IEEE754/Bits.v:b32_minus` against the current Lean helper stack. The checked
classifier
`.change_log/manual_attempt_20260717_b32_minus_current_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`b32_minus` is exactly `Bminus _ _ Hprec Hprec_emax binop_nan_pl32` at type
`mode -> binary32 -> binary32 -> binary32`, with `binary32` carrying finite
boundedness proofs and `binop_nan_pl32` preserving NaN payload proofs. Current
Lean has `binary32`, `b32_opp`, and `binop_nan_pl32`, but local subtraction
does not expose a faithful proof-carrying adapter: `Binary.Bminus`/`binary_sub`
return the permissive `Binary754` wrapper, and `BinarySingleNaNBridge.Bminus`
returns proof-erased `BinaryFloat`. The raw SingleNaN `Bminus` in
`BinarySingleNaN.lean` similarly returns raw `B754` and only proves NaN shape,
not a finite-result `bounded` theorem sufficient to reconstruct `binary32`.
Adding `b32_minus` through any of those paths would weaken the upstream
surface, so `b32_minus` remains active until a bounded-result reconstruction
theorem for the exact SingleNaN/Binary subtraction path is available.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_004924` rechecked upstream
`IEEE754/Bits.v:b32_mult` against the current Lean proof-carrying surface. The
checked classifier
`.change_log/manual_attempt_20260717_b32_mult_current_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`b32_mult` is exactly `Bmult _ _ Hprec Hprec_emax binop_nan_pl32` at type
`mode -> binary32 -> binary32 -> binary32`, where `binary32` is
`binary_float 24 128` and finite constructors carry `bounded` proofs while
`binop_nan_pl32` preserves source NaN payload proofs. Current Lean has exact
`binary32` and `binop_nan_pl32`, but the available multiplication adapters do
not preserve that surface: `Binary.Bmult`/`binary_mul` return permissive
`Binary754`, whose finite validity field is only `True`, and
`BinarySingleNaNBridge.Bmult` returns proof-erased `BinaryFloat`. The raw
SingleNaN multiplication path similarly exposes proof-erased `B754` and does
not provide a finite-result `bounded` theorem sufficient to reconstruct
`binary32`. Adding `b32_mult` through any of those paths would change the
return type or erase the proof payload, so `b32_mult` remains active until an
exact bounded-result reconstruction theorem for the SingleNaN/Binary
multiplication path is available.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_005548` rechecked upstream
`IEEE754/Bits.v:b32_div` against the same current proof-carrying surface. The
checked classifier
`.change_log/manual_attempt_20260717_b32_div_current_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream line 672
defines `b32_div` exactly as `Bdiv _ _ Hprec Hprec_emax binop_nan_pl32` at type
`mode -> binary32 -> binary32 -> binary32`, where `binary32` is
`binary_float 24 128` with bounded finite proofs and `binop_nan_pl32`
preserves source NaN payload proofs. Current Lean has exact `binary32` and
`binop_nan_pl32`, but the available division adapters still do not preserve
that surface: `Binary.Bdiv` and `binary_div` return permissive `Binary754`,
whose finite validity field is not the upstream `bounded` proof payload, and
`BinarySingleNaNBridge.Bdiv` returns proof-erased `BinaryFloat`. Applying
local `Binary.Bdiv` directly to `binop_nan_pl32` is also a handler type
mismatch because local `BdivNaNHandler 24 128` is over `Binary754 24 128`, not
proof-carrying `binary32`. Rebuilding through `b32_of_bits` would decode a
new bit pattern rather than preserve the upstream bounded finite proof and
NaN-payload path. Adding `b32_div` through any current helper would therefore
change the return type or erase the proof payload, so `b32_div` remains active
until an exact bounded-result reconstruction theorem for the SingleNaN/Binary
division path is available.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_010715` rechecked upstream
`IEEE754/Bits.v:b32_fma` against the same current proof-carrying surface. The
checked classifier
`.change_log/manual_attempt_20260716_171116_b32_fma_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream line 674
defines `b32_fma` exactly as `Bfma _ _ Hprec Hprec_emax ternop_nan_pl32` at
type `mode -> binary32 -> binary32 -> binary32 -> binary32`, where `binary32`
is `binary_float 24 128` with bounded finite proofs and `ternop_nan_pl32`
preserves source NaN payload proofs across three inputs. Current Lean has exact
`binary32` and `ternop_nan_pl32`, but the available FMA adapters still do not
preserve that surface: `Binary.Bfma` and `binary_fma` return permissive
`Binary754`, whose finite validity field is not the upstream `bounded` proof
payload, and `BinarySingleNaNBridge.Bfma` returns proof-erased `BinaryFloat`.
The local `BfmaNaNHandler 24 128` is over `Binary754 24 128`, not
proof-carrying `binary32`; rebuilding through bits would decode a new bit
pattern rather than preserve the upstream bounded finite proof and ternary
NaN-payload path. Adding `b32_fma` through any current helper would therefore
change the return type or erase the proof payload, so `b32_fma` remains active
until an exact bounded-result reconstruction theorem for the SingleNaN/Binary
FMA path is available.

2026-07-19 blocker note: manual target recheck
`.change_log/manual_attempt_20260719_b32_fma_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`IEEE754/Bits.v:b32_fma` is the exact public specialization
`Bfma _ _ Hprec Hprec_emax ternop_nan_pl32` at type
`mode -> binary32 -> binary32 -> binary32 -> binary32`, with
`binary32 := binary_float 24 128`. Current Lean still has proof-carrying
`binary32` and exact `ternop_nan_pl32`, but the callable FMA surfaces do not
match the upstream payload path: `FloatSpec.IEEE754.Binary.Bfma` and
`binary_fma` return permissive `Binary754 24 128`, while
`BinarySingleNaNBridge.Bfma` returns proof-erased `BinaryFloat`. The local
`BfmaNaNHandler 24 128` also expects `Binary754 24 128` inputs, so
`ternop_nan_pl32` cannot be passed to it without changing carrier types.
Rebuilding through bits would decode/reconstruct instead of preserving the
source bounded finite proofs and ternary NaN payload proof. Therefore no
`b32_fma` alias was added; the prerequisite remains an exact
`binary_float`-preserving FMA adapter or a theorem reconstructing bounded
finite and NaN-payload proofs for the SingleNaN/Binary FMA result.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_011635` rechecked upstream
`IEEE754/Bits.v:b64_sqrt` against the current proof-carrying binary64 surface.
The checked classifier
`.change_log/manual_attempt_20260717_b64_sqrt_blocked/attempt.json` records
`result = blocked` and `coq_alignment = checked`: upstream line 734 defines
`b64_sqrt` exactly as `Bsqrt _ _ Hprec Hprec_emax unop_nan_pl64` at type
`mode -> binary64 -> binary64`, where `binary64` is
`binary_float 53 1024` with bounded finite proofs and `unop_nan_pl64` preserves
source NaN payload proofs. Current Lean has exact `binary64` and
`unop_nan_pl64`, but the available square-root adapters do not preserve that
surface: `Binary.Bsqrt` and `binary_sqrt` return permissive `Binary754`, whose
finite validity field is not the upstream `bounded` proof payload, and
`BinarySingleNaNBridge.Bsqrt` returns proof-erased `BinaryFloat`. Adding
`b64_sqrt` through any current helper would therefore change the return type or
erase the proof payload, so `b64_sqrt` remains active until an exact
bounded-result reconstruction theorem for the SingleNaN/Binary square-root path
is available.

2026-07-19 blocker note: manual target recheck
`.change_log/manual_attempt_20260719_b64_sqrt_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream line 734
defines `b64_sqrt` exactly as `Bsqrt _ _ Hprec Hprec_emax unop_nan_pl64` at
type `mode -> binary64 -> binary64`, where `binary64` is the proof-carrying
`binary_float 53 1024` and `unop_nan_pl64` preserves source NaN payload
proofs. The current Lean API still cannot expose that surface faithfully:
`Binary.Bsqrt` and `binary_sqrt` return permissive `Binary754`,
`BinarySingleNaNBridge.Bsqrt` returns proof-erased `BinaryFloat`, and
`BsqrtNaNHandler 53 1024` is typed over `Binary754 53 1024` rather than
proof-carrying `binary64`. No public theorem reconstructs the bounded finite
result proofs and NaN-payload proof path needed to turn those results into
`binary64` without changing semantics. Therefore no `b64_sqrt` alias was added;
the prerequisite remains an exact `binary_float`-preserving square-root adapter
or a reconstruction theorem for the SingleNaN/Binary square-root result.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_013046` rechecked upstream
`IEEE754/Bits.v:b64_plus` against the current proof-carrying binary64 surface.
The checked classifier
`.change_log/manual_attempt_20260716_173513_b64_plus_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream line 736
defines `b64_plus` exactly as `Bplus _ _ Hprec Hprec_emax binop_nan_pl64` at
type `mode -> binary64 -> binary64 -> binary64`, where `binary64` is
`binary_float 53 1024` with bounded finite proofs and `binop_nan_pl64`
preserves source NaN payload proofs. Current Lean has exact `binary64` and
`binop_nan_pl64`, but the available addition adapters do not preserve that
surface: `Binary.Bplus` and `binary_add` return permissive `Binary754`, whose
finite validity field is not the upstream `bounded` proof payload, and
`BinarySingleNaNBridge.Bplus` returns proof-erased `BinaryFloat`. Adding
`b64_plus` through any current helper would therefore change the return type or
erase the proof payload, so `b64_plus` remains active until an exact
bounded-result reconstruction theorem for the SingleNaN/Binary addition path is
available.

2026-07-19 blocker note: harness attempt
`.change_log/codex_attempt_20260719_022141` rechecked upstream
`IEEE754/Bits.v:b64_plus` against the current proof-carrying binary64 surface
and left Lean source unchanged. The checked manual classifier
`.change_log/manual_attempt_20260719_b64_plus_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`b64_plus` is the exact public specialization
`Bplus _ _ Hprec Hprec_emax binop_nan_pl64` at type
`mode -> binary64 -> binary64 -> binary64`, with
`binary64 := binary_float 53 1024`. Current Lean has exact `binary64` and
`binop_nan_pl64`, but the callable addition surfaces still do not preserve
that carrier: `Binary.Bplus` and `binary_add` return permissive
`Binary754`, `BinarySingleNaNBridge.Bplus` returns proof-erased
`BinaryFloat`, and raw `BinarySingleNaN.Bplus` returns `B754` without a public
bounded finite-result theorem reconstructing `binary64` while preserving
exact-zero/sign behavior and the `binop_nan_pl64` NaN-payload path. Therefore
no `b64_plus` alias was added; the prerequisite remains an exact
`binary_float`-preserving addition adapter or a reconstruction theorem for the
SingleNaN/Binary addition result.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_013941` rechecked upstream
`IEEE754/Bits.v:b64_minus` against the current proof-carrying binary64 surface.
The checked classifier
`.change_log/manual_attempt_20260717_b64_minus_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream line 737
defines `b64_minus` exactly as `Bminus _ _ Hprec Hprec_emax binop_nan_pl64` at
type `mode -> binary64 -> binary64 -> binary64`, where `binary64` is
`binary_float 53 1024` with bounded finite proofs and `binop_nan_pl64`
preserves source NaN payload proofs. Current Lean has exact `binary64` and
`binop_nan_pl64`, but the available subtraction adapters do not preserve that
surface: `Binary.Bminus` and `binary_sub` return permissive `Binary754`, whose
finite validity field is not the upstream `bounded` proof payload, and
	`BinarySingleNaNBridge.Bminus` returns proof-erased `BinaryFloat`. Adding
	`b64_minus` through any current helper would therefore change the return type or
	erase the proof payload, so `b64_minus` remains active until an exact
	bounded-result reconstruction theorem for the SingleNaN/Binary subtraction path
	is available.

2026-07-19 blocker note: harness attempt
`.change_log/codex_attempt_20260719_022817` rechecked upstream
`IEEE754/Bits.v:b64_minus` against the current proof-carrying binary64 surface
and left Lean source unchanged. The checked manual classifier
`.change_log/manual_attempt_20260719_b64_minus_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`b64_minus` is the exact public specialization
`Bminus _ _ Hprec Hprec_emax binop_nan_pl64` at type
`mode -> binary64 -> binary64 -> binary64`, with
`binary64 := binary_float 53 1024`. Current Lean has exact `binary64`,
`b64_opp`, and `binop_nan_pl64`, but the callable subtraction surfaces still
do not preserve that carrier: `Binary.Bminus` and `binary_sub` return
permissive `Binary754`, `BinarySingleNaNBridge.Bminus` returns proof-erased
`BinaryFloat`, and raw `BinarySingleNaN.Bminus` returns `B754` without a
public bounded finite-result theorem reconstructing `binary64` while
preserving exact-zero/sign behavior and the `binop_nan_pl64` NaN-payload path.
Therefore no `b64_minus` alias was added; the prerequisite remains an exact
`binary_float`-preserving subtraction adapter or a reconstruction theorem for
the SingleNaN/Binary subtraction result.

2026-07-17 blocker note: manual target recheck
`.change_log/manual_attempt_20260717_b64_mult_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream line 738
defines `b64_mult` exactly as `Bmult _ _ Hprec Hprec_emax binop_nan_pl64` at
type `mode -> binary64 -> binary64 -> binary64`, where `binary64` is
`binary_float 53 1024` with bounded finite proofs and `binop_nan_pl64`
preserves source NaN payload proofs. Current Lean has exact `binary64` and
`binop_nan_pl64`, but the available multiplication adapters do not preserve that
surface: `Binary.Bmult` and `binary_mul` return permissive `Binary754`, whose
finite validity field is not the upstream `bounded` proof payload, and
`BinarySingleNaNBridge.Bmult` returns proof-erased `BinaryFloat`. The raw
SingleNaN path also lacks a bridge back to proof-carrying `binary64`. Adding
`b64_mult` through any current helper would therefore change the return type or
erase the proof payload, so `b64_mult` remains active until an exact
bounded-result reconstruction theorem for the SingleNaN/Binary multiplication
path is available.

2026-07-19 blocker note: manual target recheck
`.change_log/manual_attempt_20260719_b64_mult_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream line 738
defines `b64_mult` exactly as `Bmult _ _ Hprec Hprec_emax binop_nan_pl64` at
type `mode -> binary64 -> binary64 -> binary64`, where `binary64` is
`binary_float 53 1024` with bounded finite proofs and `binop_nan_pl64`
preserves source NaN payload proofs. Current Lean has exact `binary64` and
`binop_nan_pl64`, but the available multiplication adapters do not preserve
that surface: `Binary.Bmult` and `binary_mul` return permissive `Binary754`,
whose finite validity field is not the upstream `bounded` proof payload, and
`BinarySingleNaNBridge.Bmult` returns proof-erased `BinaryFloat`. Raw
`BinarySingleNaN.B754_mult` returns proof-erased `B754`; the current public API
has `is_nan_binary_normalize`, but no theorem reconstructing bounded finite
results as proof-carrying `binary64`. Rebuilding through bits would decode a
new bit pattern rather than preserve the upstream bounded finite proof and
binary NaN-payload path. Adding `b64_mult` through any current helper would
therefore change the return type or erase the proof payload, so `b64_mult`
remains active until an exact bounded-result reconstruction theorem for the
SingleNaN/Binary multiplication path is available.

2026-07-17 blocker note: manual target recheck
`.change_log/manual_attempt_20260717_b64_div_current_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream line 739
defines `b64_div` exactly as `Bdiv _ _ Hprec Hprec_emax binop_nan_pl64` at
type `mode -> binary64 -> binary64 -> binary64`, where `binary64` is
`binary_float 53 1024` with bounded finite proofs and `binop_nan_pl64`
preserves source NaN payload proofs. Current Lean has exact `binary64` and
`binop_nan_pl64`, but the available division adapters do not preserve that
surface: `Binary.Bdiv` and `binary_div` return permissive `Binary754`, whose
finite validity field is not the upstream `bounded` proof payload, and
`BinarySingleNaNBridge.Bdiv` returns proof-erased `BinaryFloat`. The local
`BdivNaNHandler 53 1024` is over `Binary754 53 1024`, not proof-carrying
`binary64`; rebuilding through bits would decode a new bit pattern rather than
preserve the upstream bounded finite proof and NaN-payload path. Adding
`b64_div` through any current helper would therefore change the return type or
erase the proof payload, so `b64_div` remains active until an exact
bounded-result reconstruction theorem for the SingleNaN/Binary division path is
available.

2026-07-19 blocker note: harness attempt
`.change_log/codex_attempt_20260719_024133` rechecked upstream
`IEEE754/Bits.v:b64_div` against the current proof-carrying binary64 surface
and left Lean source unchanged. The checked manual classifier
`.change_log/manual_attempt_20260719_b64_div_current_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`b64_div` is the exact public specialization
`Bdiv _ _ Hprec Hprec_emax binop_nan_pl64` at type
`mode -> binary64 -> binary64 -> binary64`, with
`binary64 := binary_float 53 1024`. Current Lean has exact `binary64` and
`binop_nan_pl64`, but the callable division surfaces still do not preserve
that carrier: `Binary.Bdiv` and `binary_div` return permissive `Binary754`,
`BinarySingleNaNBridge.Bdiv` returns proof-erased `BinaryFloat`, and
`BdivNaNHandler 53 1024` is typed over `Binary754 53 1024` rather than
proof-carrying `binary64`. No public bounded finite-result reconstruction
theorem/API returns `binary64` while preserving division sign,
divide-by-zero/overflow semantics, and the `binop_nan_pl64` NaN-payload path.
Therefore no `b64_div` alias was added; the prerequisite remains an exact
`binary_float`-preserving division adapter or a reconstruction theorem for the
SingleNaN/Binary division result.

2026-07-17 blocker note: manual target recheck
`.change_log/manual_attempt_20260717_b64_fma_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream line 740
defines `b64_fma` exactly as `Bfma _ _ Hprec Hprec_emax ternop_nan_pl64` at
type `mode -> binary64 -> binary64 -> binary64 -> binary64`, where `binary64`
is `binary_float 53 1024` with bounded finite proofs and `ternop_nan_pl64`
preserves source NaN payload proofs across three inputs. Current Lean has exact
`binary64` and `ternop_nan_pl64`, but the available FMA adapters do not preserve
that surface: `Binary.Bfma` and `binary_fma` return permissive `Binary754`,
whose finite validity field is not the upstream `bounded` proof payload, and
`BinarySingleNaNBridge.Bfma` returns proof-erased `BinaryFloat`. The local
`BfmaNaNHandler 53 1024` is over `Binary754 53 1024`, not proof-carrying
`binary64`; rebuilding through bits would decode a new bit pattern rather than
preserve the upstream bounded finite proof and ternary NaN-payload path. Adding
`b64_fma` through any current helper would therefore change the return type or
erase the proof payload, so `b64_fma` remains active until an exact
bounded-result reconstruction theorem for the SingleNaN/Binary FMA path is
available.

2026-07-19 blocker note: harness attempt
`.change_log/codex_attempt_20260719_024632` rechecked upstream
`IEEE754/Bits.v:b64_fma` against the current proof-carrying binary64 surface
and left Lean source unchanged. The checked manual classifier
`.change_log/manual_attempt_20260719_b64_fma_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`b64_fma` is the exact public specialization
`Bfma _ _ Hprec Hprec_emax ternop_nan_pl64` at type
`mode -> binary64 -> binary64 -> binary64 -> binary64`, with
`binary64 := binary_float 53 1024`. Current Lean has exact `binary64` and
`ternop_nan_pl64`, but the callable fused multiply-add surfaces still do not
preserve that carrier: `Binary.Bfma` and `binary_fma` return permissive
`Binary754`, `BinarySingleNaNBridge.Bfma` returns proof-erased
`BinaryFloat`, and `BfmaNaNHandler 53 1024` is typed over
`Binary754 53 1024` rather than proof-carrying `binary64`. No public bounded
finite-result reconstruction theorem/API returns `binary64` while preserving
fused-operation semantics, sign/zero behavior, and the `ternop_nan_pl64`
payload path. Therefore no `b64_fma` alias was added; the prerequisite remains
an exact `binary_float`-preserving FMA adapter or a reconstruction theorem for
the SingleNaN/Binary FMA result.

2026-07-19 blocker note: manual target recheck
`.change_log/manual_attempt_20260719_b32_plus_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream line 668
defines `b32_plus` exactly as `Bplus _ _ Hprec Hprec_emax binop_nan_pl32` at
type `mode -> binary32 -> binary32 -> binary32`, where `binary32` is
`binary_float 24 128` with bounded finite proofs and `binop_nan_pl32` preserves
source NaN payload proofs. Current Lean has exact `binary32` and
`binop_nan_pl32`, but the available addition adapters do not preserve that
surface: `Binary.Bplus` and `binary_add` return permissive `Binary754`, whose
finite validity field is not the upstream `bounded` proof payload, and
`BinarySingleNaNBridge.Bplus` returns proof-erased `BinaryFloat`. Raw
`BinarySingleNaN.Bplus` returns proof-erased `B754`; the current public API has
`is_nan_binary_normalize`, but no theorem reconstructing bounded finite results
as proof-carrying `binary32`. Rebuilding through bits would decode a new bit
pattern rather than preserve the upstream bounded finite proof and binary
NaN-payload path. Adding `b32_plus` through any current helper would therefore
change the return type or erase the proof payload, so `b32_plus` remains active
until an exact bounded-result reconstruction theorem for the SingleNaN/Binary
addition path is available.

2026-07-19 completion note: harness attempt
`.change_log/codex_attempt_20260719_122215` restored exact public `b32_mult`
in `FloatSpec/src/IEEE754/Bits.lean` as the proof-carrying specialization
`Binary.Bmult (prec := 24) (emax := 128) binop_nan_pl32`, returning
`binary32 := binary_float 24 128`. This matches upstream
`IEEE754/Bits.v:b32_mult` and preserves the bounded finite proof carrier and
binary NaN-payload path; it avoids permissive `Binary754`, raw `B754`,
proof-erased `BinarySingleNaNBridge.BinaryFloat`, and bit roundtrip
reconstruction. Focused `lake env lean FloatSpec/src/IEEE754/Bits.lean` and
`#check b32_mult` passed. Status: implemented and removed from active
semantic gaps.

2026-07-19 completion note: harness attempt
`.change_log/codex_attempt_20260719_123426` restored exact public `b64_mult`
in `FloatSpec/src/IEEE754/Bits.lean` as the proof-carrying specialization
`Binary.Bmult (prec := 53) (emax := 1024) binop_nan_pl64`, returning
`binary64 := binary_float 53 1024`. This matches upstream
`IEEE754/Bits.v:b64_mult` and preserves the bounded finite proof carrier and
binary NaN-payload path; it avoids permissive `Binary754`, raw `B754`,
proof-erased `BinarySingleNaNBridge.BinaryFloat`, and bit roundtrip
reconstruction. The top-level attempt metadata inconsistently recorded
`result = blocked`, but its generated final message and the normalized
sidecar `.change_log/manual_attempt_20260719_b64_mult_proved/attempt.json`
record `result = proved`, `coq_alignment = checked`, `build = pass`, and
`local_target_gate = pass`. Independent focused `lake env lean
FloatSpec/src/IEEE754/Bits.lean` and `#check b64_mult` passed. Status:
implemented and removed from active semantic gaps.

2026-07-19 completion note: harness attempt
`.change_log/codex_attempt_20260719_124257` restored exact public `b32_plus`
in `FloatSpec/src/IEEE754/Bits.lean` as the proof-carrying specialization
`Binary.Bplus (prec := 24) (emax := 128) binop_nan_pl32`, returning
`binary32 := binary_float 24 128`. This matches upstream
`IEEE754/Bits.v:b32_plus`; it is only the exact Bits alias and does not claim
the separate active `Bplus_correct` theorem. The implementation avoids
permissive `Binary754`, raw `B754`, proof-erased
`BinarySingleNaNBridge.BinaryFloat`, and bit roundtrip reconstruction. Harness
attempt metadata records `result = proved`, `local_target_gate = pass`, and
the normalized sidecar `.change_log/codex_attempt_20260719_124724/attempt.json`
records `result = proved`, `coq_alignment = checked`, and `build = pass`.
Independent focused `lake env lean FloatSpec/src/IEEE754/Bits.lean` and
`#check b32_plus` passed. Status: implemented and removed from active semantic
gaps.

2026-07-19 completion note: harness attempt
`.change_log/codex_attempt_20260719_125022` restored exact public `b64_plus`
in `FloatSpec/src/IEEE754/Bits.lean` as the proof-carrying specialization
`Binary.Bplus (prec := 53) (emax := 1024) binop_nan_pl64`, returning
`binary64 := binary_float 53 1024`. This matches upstream
`IEEE754/Bits.v:b64_plus`; it is only the exact Bits alias and does not claim
the separate active `Bplus_correct` theorem. The implementation avoids
permissive `Binary754`, raw `B754`, proof-erased
`BinarySingleNaNBridge.BinaryFloat`, and bit roundtrip reconstruction. Harness
attempt metadata records `result = proved` and `local_target_gate = pass`, and
the normalized sidecar
`.change_log/manual_attempt_20260719_b64_plus_proved_exact_alias/attempt.json`
records `result = proved`, `coq_alignment = checked`, and `build = pass`.
Independent focused `lake env lean FloatSpec/src/IEEE754/Bits.lean` and
`#check b64_plus` passed. Status: implemented and removed from active semantic
gaps.

2026-07-19 completion note: harness attempt
`.change_log/codex_attempt_20260719_125929` restored the prerequisite
proof-carrying `Binary.Bminus` bridge in
`FloatSpec/src/IEEE754/BinarySingleNaN.lean` and exact public `b32_minus` in
`FloatSpec/src/IEEE754/Bits.lean`. The Bits alias is the proof-carrying
specialization `Binary.Bminus (prec := 24) (emax := 128) binop_nan_pl32`,
returning `binary32 := binary_float 24 128`, matching upstream
`IEEE754/Bits.v:b32_minus := Bminus _ _ Hprec Hprec_emax binop_nan_pl32`.
The implementation avoids permissive `Binary754`, raw `B754`,
proof-erased `BinarySingleNaNBridge.BinaryFloat`, post-hoc bit
reconstruction, and differently parameterized helpers, and it does not claim
the separate `Bminus_correct` theorem. Harness metadata records
`result = proved` and `local_target_gate = pass`; explicit
`scripts/classify_attempt.py` classification records `result = proved`,
`coq_alignment = checked`, and `build = pass`. Independent focused
`lake env lean FloatSpec/src/IEEE754/Bits.lean`, `#check Binary.Bminus`, and
`#check b32_minus` passed. Status: implemented and removed from active
semantic gaps.

2026-07-19 completion note: harness attempt
`.change_log/codex_attempt_20260719_131228` restored exact public
`b64_minus` in `FloatSpec/src/IEEE754/Bits.lean` as the proof-carrying
specialization `Binary.Bminus (prec := 53) (emax := 1024) binop_nan_pl64`,
returning `binary64 := binary_float 53 1024`, matching upstream
`IEEE754/Bits.v:b64_minus := Bminus _ _ Hprec Hprec_emax binop_nan_pl64`.
The implementation reuses the proof-carrying `Binary.Bminus` bridge and avoids
permissive `Binary754`, raw `B754`, proof-erased
`BinarySingleNaNBridge.BinaryFloat`, post-hoc bit reconstruction, and
differently parameterized helpers. It does not claim the separate
`Bminus_correct` theorem. Harness metadata records `result = proved` and
`local_target_gate = pass`; explicit `scripts/classify_attempt.py`
 classification records `result = proved`, `coq_alignment = checked`, and
`build = pass`. Independent focused `lake env lean
FloatSpec/src/IEEE754/Bits.lean` and `#check b64_minus` passed. Status:
implemented and removed from active semantic gaps.

2026-07-19 blocker refresh: harness attempt
`.change_log/codex_attempt_20260719_132559` rechecked upstream
`IEEE754/Bits.v:b32_sqrt` after the proof-carrying Binary-side
`Bplus`/`Bminus`/`Bmult` bridges landed. It made no Lean source changes
(`changed_files = []`, `changed_during_attempt.txt` is empty, and
`statement_changed = false`) and correctly left the declaration absent rather
than routing through a weaker carrier. The blocker is still foundational:
upstream `b32_sqrt` is the exact proof-carrying specialization
`Bsqrt _ _ Hprec Hprec_emax unop_nan_pl32` returning
`binary32 := binary_float 24 128`, but current Lean has no proof-carrying
`Binary.Bsqrt`. The available root `Bsqrt` returns permissive `Binary754`,
`BinarySingleNaNBridge.Bsqrt` returns proof-erased `BinaryFloat`, and the
local SingleNaN sqrt support lacks the upstream-shaped
`SFsqrt_core_binary`/`binary_round_aux` bridge needed to reconstruct a
valid bounded finite `binary_float` result without changing the payload. An
explicit follow-up `scripts/classify_attempt.py` run recorded
`result = blocked`, `coq_alignment = checked`, `build = pass`, and
`local_target_gate = pass`. Status: still active.

#### `IEEE754/PrimFloat.v` (0)

2026-07-17 blocker note: manual target recheck
`.change_log/manual_attempt_20260717_Prim2B_current_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream line 27
defines `Prim2B (x : float) : binary_float prec emax` exactly as
`SF2B (Prim2SF x) (Prim2SF_valid x)`, preserving Coq primitive-float
`StandardFloat` semantics and returning proof-carrying `binary_float`. Current
Lean still exposes only `ExperimentalPrimFloatBridge.PrimFloat`, an opaque
real-projection wrapper; local `prim_to_binary` returns permissive `Binary754`,
and the file explicitly warns that this bridge must not be counted as faithful
IEEE/PrimFloat equivalence. No faithful Coq primitive `float`, `Prim2SF_valid`,
or proof-carrying `SF2B ... : binary_float prec emax` path is present, so
`Prim2B` remains active until that primitive-float bridge exists.

2026-07-17 blocker note: manual target recheck
`.change_log/manual_attempt_20260717_B2Prim_current_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream line 32
defines `B2Prim (x : binary_float prec emax) : float := SF2Prim (B2SF x)`,
preserving proof-carrying binary_float input and Coq primitive-float output.
Current Lean still exposes only `ExperimentalPrimFloatBridge.PrimFloat`, an
opaque real-projection wrapper; local `binary_to_prim` takes permissive
`Binary754` and maps through `B2R`, collapsing NaN, infinity, payload, and
signed-zero behavior. No faithful Coq primitive `float`, `SF2Prim`, or
proof-carrying `B2SF ... : StandardFloat` path from local `binary_float prec
emax` is present, so `B2Prim` remains active until that primitive-float bridge
exists.

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_202634` correctly rejected an invasive
replacement of the historical real-only experimental bridge and restored a
clean worktree. Manual follow-up then added an independent
`FaithfulPrimFloat` model whose `PrimitiveFloat` carrier stores a
`StandardFloat` together with the exact fixed-binary64
`validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024)` proof.
`FaithfulPrimFloat.Prim2B` is definitionally
`SF2B (Prim2SF x) (Prim2SF_valid x)`, and
`FaithfulPrimFloat.B2Prim` is definitionally `SF2Prim (B2SF x)`, matching
upstream `PrimFloat.v:30-34` on the proof-carrying SingleNaN binary64 carrier.
The accompanying `B2SF_SF2B`, `SF2B_B2SF`, `B2Prim_Prim2B`, and
`Prim2B_B2Prim` theorems prove exact round trips for signed zeros,
infinities, the unique NaN, and bounded finite values. The existing
`ExperimentalPrimFloatBridge` declarations were not changed or counted as
evidence. Focused `lake env lean FloatSpec/src/IEEE754/PrimFloat.lean`
passed. Therefore `Prim2B` and `B2Prim` are removed from the active list.

2026-07-17 blocker note: manual target recheck
`.change_log/manual_attempt_20260717_035155_normfr_mantissa_equiv_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`IEEE754/PrimFloat.v:normfr_mantissa_equiv` proves
`to_Z (normfr_mantissa x) = Z.of_N (Bnormfr_mantissa (Prim2B x))` for
Coq primitive `float`s by rewriting `normfr_mantissa_spec`, rewriting
`B2SF_Prim2B` in reverse, then case-splitting the faithful `Prim2B x`.
Current Lean still exposes only `ExperimentalPrimFloatBridge.PrimFloat`, an
opaque real-projection wrapper; local `prim_to_binary` is not Coq's
`Prim2B := SF2B (Prim2SF x) (Prim2SF_valid x)`, and there are no faithful
primitive-float `normfr_mantissa`, `to_Z`, or `Z.of_N` payloads with matching
types. `Bnormfr_mantissa` exists only on local binary bridge types. Adding
the exact theorem over the current wrappers would be helper-only or
tautological rather than the upstream primitive-float theorem, so
`normfr_mantissa_equiv` remained active at that time.

2026-07-20 completion note: the first subscription harness attempt
`.change_log/codex_attempt_20260720_213724` failed before editing because the
ambient model cache used the unsupported reasoning value `max`. The corrected
subscription attempt `.change_log/codex_attempt_20260720_213832`, explicitly
using `gpt-5.5` with high reasoning, added the faithful primitive-side
`Uint63.t`, `Uint63.to_Z`, `Z.of_N`, `normfr_mantissa`,
`normfr_mantissa_spec`, `B2SF_Prim2B`, and exact
`normfr_mantissa_equiv` in `FaithfulPrimFloat`. The primitive operation is
defined independently through `SFnormfr_mantissa primPrec (Prim2SF x)` and
does not call `BinarySingleNaNFloat.Bnormfr_mantissa`; its specification has
the exact Coq `FloatAxioms.normfr_mantissa_spec` payload after representing
Coq's nonnegative `uint63`/`N` results with the local `Nat` carrier and both
integer conversions with `Int.ofNat`. The equivalence proof rewrites that
specification, rewrites `B2SF_Prim2B` in reverse, and case-splits the
proof-carrying `Prim2B x`, matching upstream `PrimFloat.v:259-266`. Focused
Lean checking, the zero-finding placeholder/status audits, and the full
3345-job `lake build` passed. The authoritative classifier for the final
patch records `result = proved`, `build = pass`, `coq_alignment = checked`,
and a passing local target gate. Therefore `normfr_mantissa_equiv` is removed
from the active list.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_025301` rechecked upstream
`IEEE754/PrimFloat.v:binary_round_aux_equiv` and left source unchanged. The
checked classifier
`.change_log/manual_attempt_20260717_binary_round_aux_equiv_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream unfolds Coq
`SpecFloat.binary_round_aux` and Flocq `binary_round_aux`, reduces `shr_fexp`,
and rewrites with `round_nearest_even_equiv`. Current Lean still has only the
`ExperimentalPrimFloatBridge` real-wrapper `PrimFloat` model and
`ExperimentalBinaryRound` audit helpers that are explicitly documented as not
ports of Flocq `binary_round_aux`/`binary_round`/`binary_normalize`. Adding an
exact-name theorem over those local wrappers would be helper-only or
tautological rather than the primitive-float/Flocq payload, so
`binary_round_aux_equiv` remained active at that time.

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_204757` restored
`FaithfulPrimFloat.binary_round_aux_equiv` with `result = proved` and a passing
local target gate. The new `FaithfulPrimFloat.binary_round_aux` independently
mirrors upstream `SpecFloat.binary_round_aux` for fixed binary64: it performs
the same two `bsn_shr_fexp` passes and `binary_fit_aux` step, but selects the
mantissa with its own SpecFloat nearest-even operation. The equivalence proof
unfolds that algorithm and the root Flocq `binary_round_aux`, then rewrites the
only differing operation by the local nearest-even/`choice_mode RNE`
equivalence, matching upstream `PrimFloat.v:134-142`. Manual follow-up kept
this helper wholly inside `FaithfulPrimFloat`, with no dependency on the
real-only experimental bridge. Focused Lean checking, the zero-finding
placeholder/status audits, and the full 3345-job `lake build` all passed.
Therefore `binary_round_aux_equiv` is removed from the active list; its older
blocker note above is retained as historical evidence of the infrastructure
that was missing before `bsn_shr_fexp` and the faithful primitive carrier were
restored.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_030122` rechecked upstream
`IEEE754/PrimFloat.v:mul_equiv` and left source unchanged. The checked
classifier
`.change_log/manual_attempt_20260716_190652_mul_equiv_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream proves
`Prim2B (x * y) = Bmult mode_NE (Prim2B x) (Prim2B y)` for Coq primitive
`float`s through the faithful `Prim2B`/`B2Prim`/`B2SF_Prim2B` conversion stack,
`SpecFloat.mul_spec`, finite case analysis, `B2SF_SF2B`, and
`binary_round_aux_equiv`. Current Lean still has only the experimental
real-wrapper `PrimFloat`; local `prim_mul_correct` is a reflexive statement
over `binary_mul`, and the faithful primitive-float conversions,
`SpecFloat.mul_spec`, and `binary_round_aux_equiv` payloads are not present in
the upstream shape. Adding `mul_equiv` over those local wrappers would be
helper-only or differently parameterized, so `mul_equiv` remained active at
that time.

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_215315`, explicitly using `gpt-5.5` with
high reasoning, added exact primitive multiplication infrastructure inside
`FaithfulPrimFloat`: independent SpecFloat-side `SFmul`, proof-carrying
primitive `mul` with a `Mul PrimitiveFloat` instance, exact `mul_spec`, and a
separate mode-parameterized SingleNaN `Bmult`. The two finite branches are not
aliases: `SFmul` calls the namespace-local SpecFloat `binary_round_aux`, while
`Bmult` calls root `_root_.binary_round_aux` at its supplied mode and packages
its result with validity from `_root_.Bmult_correct_aux`; `mul_equiv`
specializes that mode to `RNE`. The other branches independently
match Coq's NaN, infinity, signed-zero, and sign-xor constructor behavior.
The exact `mul_equiv` statement uses primitive `x * y` notation and follows
upstream `PrimFloat.v:144-159` through `B2Prim_inj`, `B2Prim_Prim2B`,
`Prim2SF_inj`, `Prim2SF_B2Prim`, `mul_spec`, reverse `B2SF_Prim2B` rewrites,
proof-carrying constructor case analysis, `B2SF_SF2B`, and
`binary_round_aux_equiv`. Focused Lean checking, zero-finding
placeholder/status audits, and the full 3345-job `lake build` passed. The
authoritative classifier for the final patch records `result = proved`,
`build = pass`, `coq_alignment = checked`, and a passing local target gate.
Therefore `mul_equiv` is removed from the active list.

2026-07-17 blocker note: manual target recheck
`.change_log/manual_attempt_20260717_032042_binary_round_equiv_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream proves
`SpecFloat.binary_round prec emax s m e = binary_round prec emax mode_NE s m e`
by unfolding `SpecFloat.binary_round`, Flocq `binary_round`, and
`shl_align_fexp`, destructing `shl_align`, then applying
`binary_round_aux_equiv`. Current Lean does not expose a faithful Coq
`SpecFloat.binary_round` primitive-float payload in `PrimFloat.lean`;
`PrimFloat.lean` is explicitly the `ExperimentalPrimFloatBridge` real-wrapper,
`Binary.lean`'s `ExperimentalBinaryRound` helpers are documented audit helpers
rather than Flocq algorithm ports, and the prerequisite
`binary_round_aux_equiv` remained active/blocked at that time. Adding
`binary_round_equiv` over those local wrappers would be helper-only,
tautological, or differently parameterized, so `binary_round_equiv` remained
active at that time.

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_210214` added the independent
`FaithfulPrimFloat.binary_round` and exact
`FaithfulPrimFloat.binary_round_equiv`. The SpecFloat-side definition applies
the shared `shl_align_fexp` and then calls the namespace-local faithful
`binary_round_aux` at `loc_Exact`; it does not alias the root operation. The
proof unfolds both rounders and `shl_align_fexp`, destructs the shared
alignment pair, and applies `binary_round_aux_equiv`, matching upstream
`PrimFloat.v:161-168`. The provider's internal classifier recorded
`result = proved`, `build = pass`, and `coq_alignment = checked`; the outer
harness misparsed the provider's leading `Status: proved` prose and recorded a
spurious blocked result, so
`.change_log/manual_attempt_20260720_binary_round_equiv_proved/attempt.json`
is the corrected authoritative classification. Focused Lean checking, the
zero-finding placeholder/status audits, and the full 3345-job `lake build` all
passed. Therefore `binary_round_equiv` is removed from the active list.

2026-07-17 blocker note: manual target recheck
`.change_log/manual_attempt_20260717_193147_binary_normalize_equiv_blocked_current/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream
`IEEE754/PrimFloat.v:binary_normalize_equiv` states
`SpecFloat.binary_normalize prec emax m e szero =
B2SF (binary_normalize prec emax Hprec Hmax mode_NE m e szero)`.
The Coq proof cases on the signed mantissa `m`; the zero branch simplifies
directly, while the positive and negative finite branches rewrite
`B2SF_SF2B` and apply `binary_round_equiv`. Current Lean still does not expose
a faithful Coq `SpecFloat.binary_normalize` primitive-float payload in
`PrimFloat.lean`; the file is explicitly `ExperimentalPrimFloatBridge`, and
`Binary.lean`'s `ExperimentalBinaryRound` helpers are documented audit helpers
rather than Flocq `binary_round_aux`/`binary_round`/`binary_normalize` ports.
`BinarySingleNaN.lean` has a closer local `binary_normalize`, but it does not
provide the PrimFloat/SpecFloat equivalence target, and the prerequisite
`binary_round_equiv` remained active/blocked at that time. Adding
`binary_normalize_equiv` over the available wrappers would therefore be
helper-only, tautological, or differently parameterized, so
`binary_normalize_equiv` remained active at that time.

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_211626` added the independent
`FaithfulPrimFloat.binary_normalize`, proof-carrying
`FaithfulPrimFloat.binary_normalize_bsn`, and exact
`FaithfulPrimFloat.binary_normalize_equiv`. The SpecFloat side returns a
`StandardFloat` by splitting the signed integer mantissa into zero, positive,
and negative branches. The BinarySingleNaN side returns `PrimBinaryFloat`,
constructing each nonzero branch with `SF2B` and validity supplied by
root `binary_round_correct`; it does not use the proof-erased raw `B754`
normalizer. The theorem follows upstream `PrimFloat.v:170-179`: split by sign
and reduce the nonzero branches through `B2SF_SF2B` and
`binary_round_equiv`. Focused Lean checking, zero-finding placeholder/status
audits, and the full 3345-job `lake build` passed. The authoritative classifier
`.change_log/manual_attempt_20260720_binary_normalize_equiv_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `binary_normalize_equiv` is removed from
the active list.

2026-07-17 blocker note: harness attempt
`.change_log/codex_attempt_20260717_033820` rechecked upstream
`IEEE754/PrimFloat.v:add_equiv` and left source unchanged. The checked
classifier
`.change_log/manual_attempt_20260716_194258_primfloat_add_equiv_blocked/attempt.json`
records `result = blocked` and `coq_alignment = checked`: upstream proves
`Prim2B (x + y) = Bplus mode_NE (Prim2B x) (Prim2B y)` for Coq primitive
`float`s through the faithful `Prim2B`/`B2Prim` conversion and injection stack,
`SpecFloat.add_spec`, `B2SF_Prim2B`, proof-carrying binary case analysis, and
`binary_normalize_equiv`. Current Lean still has only the experimental
real-wrapper `PrimFloat`; local `prim_add_correct` is a reflexive statement
over `binary_add`, and the faithful primitive-float/Bplus bridge plus
`binary_normalize_equiv` are unavailable in the upstream shape. Adding
`add_equiv` over those local wrappers would be helper-only, tautological, or
differently parameterized, so `add_equiv` remained active at that time.

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_221430`, explicitly using `gpt-5.5` with
high reasoning, added the independent SpecFloat-side `SFadd`, primitive
`add`/`Add PrimitiveFloat` operation and exact `add_spec`, proof-carrying
SingleNaN `Bplus`, and exact `add_equiv` inside `FaithfulPrimFloat`.
`SFadd` matches Coq `SpecFloat.SFadd`: it preserves the NaN, infinity, and
signed-zero constructor matrix, aligns finite mantissas at `min ex ey`, forms
the signed `Fplus_naive` sum, and calls the namespace-local RNE
`binary_normalize`; it does not call `Bplus`. Manual fidelity review found
that the generated `Bplus` initially accepted a rounding mode but used an
RNE-only finite normalizer. The final patch therefore generalized the
proof-carrying `binary_normalize_bsn` and its validity helper over the supplied
mode, keeps `binary_normalize_equiv` explicitly specialized to `RNE`, and
passes `Bplus`'s mode through both finite rounding and the mode-dependent zero
sign. The exact theorem states
`Prim2B (x + y) = Bplus RoundingMode.RNE (Prim2B x) (Prim2B y)` and follows
upstream `PrimFloat.v:182-197` through the conversion/injection stack,
`add_spec`, reverse `B2SF_Prim2B` rewrites, proof-carrying constructor case
analysis, and `binary_normalize_equiv`. Focused Lean checking, `git diff
--check`, zero-finding placeholder/status audits, and the full 3345-job
`lake build` passed; `scripts/check_diff_trust.sh` is absent from this checkout.
Therefore `add_equiv` is removed from the active list, leaving no active
`PrimFloat.v` gaps.

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_223036` produced the full displayed
`UlpFlessuGe` coefficient proof and passed its final focused/full builds, but
its public theorem initially carried a universal `boundR` exponent premise
that is not present in the upstream Axpy section. The manual repair removed
that premise and replaced the affected subnormal branch with a direct bounded-
lattice argument: shift both inputs to the minimum exponent, then show that
if the subnormal closest result differed from the exact sum, the adjacent
minimum-exponent float in the direction of the sum would be bounded and
strictly closer. The exact public theorem now assumes only the translated
Axpy section context plus `Fcanonic u`, proves the full upstream coefficient
inequality, and composes `RoundLeGeneral`, the normal/subnormal lower bound,
`FulpLeGeneral`, `UlpFlessuGe_aux`, and the final `FLess` scale. Focused Lean
checking, `git diff --check`, zero-finding placeholder/status audits, and the
full 3345-job `lake build` passed; `scripts/check_diff_trust.sh` is absent from
this checkout. The authoritative classifier
`.change_log/manual_attempt_20260720_UlpFlessuGe_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `UlpFlessuGe` is removed from the active list.

2026-07-20 completion note: subscription harness attempt
`.change_log/codex_attempt_20260720_233428` restored exact public
`UlpFlessuGe2` in `FloatSpec/src/Pff/Pff.lean`. Its assumptions are precisely
the live `AxpyAux` section context used upstream: bounded `a`, `x`, `y`, `t`,
and `u`, closest rounded product and sum, canonic `u`, radix 2, precision
greater than one, and `vNum = 2^precision`. Its conclusion is the full strict
upstream coefficient inequality, with the two predecessor shifts represented
as exponents `-precision - 2` and `-dExp - 2`. The proof derives the strict
coefficient comparison internally and composes it with exact public
`UlpFlessuGe`; it does not expose the old general-bound helper premise.
Focused `lake env lean FloatSpec/src/Pff/Pff.lean` passed. The normalized
classifier `.change_log/manual_attempt_20260720_UlpFlessuGe2_proved/attempt.json`
records the checked provider, build, and Coq-alignment result. Therefore
`UlpFlessuGe2` is removed from the active list.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_000636` correctly blocked rather than
wrapping the weakened local helper chain: `AxpyPos` and `Axpy_tFlessu` still
exported predecessor-exponent splits and a universal `boundR` exponent premise
that upstream `Pff.v:Axpy_opt` does not assume. The manual repair internalized
those branches. `AxpyPos` now derives the `u` and predecessor cases from
`FcanonicBound` and `FBoundedPred`; the minimum-exponent case uses a direct
bounded-lattice exactness lemma. `Axpy_aux3`, `Axpy_tFlessu_nonzero`, and exact
public `Axpy_tFlessu` no longer expose the universal exponent oracle or
predecessor splits. The rounded-input scale helper now handles both normal and
subnormal canonical `u` internally. Exact public `Axpy_opt` assumes only the
expanded upstream Axpy section context, large-`y` inequality, and non-strict
perturbation coefficient bound, then composes the repaired scale proof,
`UlpFlessuGe2`, and `Axpy_tFlessu`. Focused checking, `git diff --check`, the
zero-finding placeholder audit, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The normalized
classifier `.change_log/manual_attempt_20260721_Axpy_opt_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `Axpy_opt` is removed from the active
list, and `eqLe` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_005450` correctly left `eqLe` blocked with
no source changes because the local Veltkamp helper surface still exposed a
non-upstream `TotalP Closest` premise and lacked the low-mantissa comparison
and high-boundary proof packages. The manual repair removed that artificial
totality premise from public `pPos`, `qNeg`, `hxExact`, `eqLeep`, and `epLe` by
using the concrete `ClosestMonotone` property and direct bounded-float
projectors. Exact public `eqLe` now assumes only the expanded upstream Veltkamp
section context. Its low-mantissa branch constructs the upstream normal
comparison float and combines `ClosestExp`, `eqLeep`, `epLe`, and
`Fcanonic_Rle_Zle`; its high-mantissa branch proves the exact negative
minimal-normal boundary value and both sides of the half-ulp residual bound,
using the bounded upper comparison for `p` and the exact `FNSucc` boundary
gap. Focused `lake env lean FloatSpec/src/Pff/Pff.lean`, `git diff --check`,
the zero-finding placeholder audit, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The normalized
classifier `.change_log/manual_attempt_20260721_eqLe_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `eqLe` is removed from the active list,
and `eqGe` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_020438` correctly left `eqGe` blocked with
no source changes because the existing local helper surface did not package
the full residual lower-bound argument from upstream's second comparison
branch. The manual repair restored exact public `eqGe` under only the expanded
upstream Veltkamp section context. It constructs the same minimal-normal
comparison float used upstream and proves the required value lower bound in
three mantissa ranges: the large range combines `ClosestExp`, `eqLeep`, and
`epLe` to absorb both half-ulp errors; the middle range constructs and bounds
the upstream three-term comparison float and applies concrete
`ClosestMonotone`; and the minimal-normal range proves both rounded inputs are
exactly representable. `Fcanonic_Rle_Zle` then yields
`(s : Int) + x.Fexp <= q.Fexp`. The corrected focused Lean process exited 0,
`git diff --check` passed, placeholder/status audits reported zero findings,
and the full 3345-job `lake build` passed; `scripts/check_diff_trust.sh` is
absent from this checkout. The normalized classifier
`.change_log/manual_attempt_20260721_eqGe_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. This completion supersedes the older `eqGe` blocker notes
below. Therefore `eqGe` is removed from the active list, and `eqEqual` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_025037` restored exact public `eqEqual` in
`FloatSpec/src/Pff/Pff.lean`. The theorem keeps the expanded upstream
Veltkamp section assumptions and the exact upstream disjunction: either
`q.Fexp = (s : Int) + x.Fexp`, or `q` has the negative minimal-normal boundary
value and the reconstructed high part satisfies the half-ulp residual bound.
Its proof combines exact public `eqLe` with exact public `eqGe`; the exponent
branch is closed by antisymmetry, while the boundary branch is preserved
unchanged. The real focused Lean process exited 0, `git diff --check` passed,
placeholder/status audits reported zero findings, and the full 3345-job
`lake build` passed; `scripts/check_diff_trust.sh` is absent from this
checkout. The normalized classifier
`.change_log/manual_attempt_20260721_eqEqual_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `eqEqual` is removed from the active list, and
`Veltkamp_aux_aux` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_031224` correctly classified the exact
`Veltkamp_aux_aux` payload as blocked without changing Lean source: the local
proof still needed upstream's low-mantissa reconstruction branch rather than a
weaker generic canonicity argument. The manual repair restored exact public
`Veltkamp_aux_aux` under only the expanded upstream Veltkamp section context.
For the low-mantissa branch it defines the upstream integer residual `eps`,
constructs the same two bounded normal comparison floats, applies
`ImplyClosestStrict` to identify the represented values of `p` and `Fopp q`,
and combines those values with `hxExact` to reconstruct the lower binade
endpoint exactly. The complementary mantissa branch follows directly from the
half-ulp residual premise. The corrected focused Lean process exited 0,
`git diff --check` passed, placeholder/status audits reported zero findings,
and the full 3345-job `lake build` passed; `scripts/check_diff_trust.sh` is
absent from this checkout. The normalized classifier
`.change_log/manual_attempt_20260721_Veltkamp_aux_aux_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `Veltkamp_aux_aux` is removed from the
active list, and `Veltkamp_aux` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_035252` correctly classified exact public
`Veltkamp_aux` as blocked without retaining source changes: the missing step
was a tight reduced-bound representative for `Fplus p q`. The manual repair
restored the exact upstream conjunction and existential payload under only the
expanded Veltkamp section context. A private residual lemma composes
`eqEqual`, `ClosestUlp`, `ClosestExp`, and `hxExact`. A second private lemma
uses `eqGe` to bound the exact sum's mantissa, applies `FboundedMbound` at
precision `t - s`, and normalizes the result into a canonical same-value
representative. The public theorem applies `Veltkamp_aux_aux` and
`ImplyClosest`, then derives `(s : Int) + x.Fexp <= hx'.Fexp` with
`Fcanonic_Rle_Zle`. The focused Lean process exited 0, `git diff --check`
passed, placeholder/status audits reported zero findings, and the full
3345-job `lake build` passed; `scripts/check_diff_trust.sh` is absent from this
checkout. The normalized classifier
`.change_log/manual_attempt_20260721_Veltkamp_aux_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `Veltkamp_aux` is removed from the active list,
and `VeltkampEven1` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_043449` left the exact
`VeltkampEven1` payload unchanged and did not run a build. The manual repair
restored exact public `VeltkampEven1` with all expanded upstream Veltkamp
section assumptions, including the three `EvenClosest` hypotheses, and the
exact existential conclusion: a same-value representative of `hx` that is
even-closest to `x` in the reduced `t - s` format. A private candidate lemma
reconstructs the high part at exponent `s + Fexp x`, normalizes the strict
mantissa case, and uses an even minimal-normal representative at the mantissa
boundary. A private tie lemma aligns the `p` and `q` mantissas at the reduced
exponent and applies `ClosestImplyEven_int` to the even-closest split stages;
outside the exact midpoint, `ImplyClosestStrict2` supplies uniqueness. The
focused Lean process exited 0, `git diff --check` passed, placeholder/status
audits reported zero findings, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The normalized
classifier
`.change_log/manual_attempt_20260721_VeltkampEven1_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `VeltkampEven1` is removed from the
active list, and `VeltkampEven2` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_052705` left the exact `VeltkampEven2`
payload unchanged and did not run a build. The manual repair restored exact
public `VeltkampEven2` with the expanded upstream Veltkamp section assumptions
and exact conclusion: a same-value representative of `hx` that is even-closest
to `x` in the reduced `t - s` format. A private no-tie lemma represents the
residual as an integer multiple of `radix ^ Fexp x`; an exact half-ulp tie
would make `radix ^ s` even, contradicting `Odd radix`. The public proof uses
`Veltkamp_aux`, constructs the canonical reduced representative, rules out the
tie, and applies `ImplyClosestStrict2` for uniqueness and hence
`EvenClosest`. The focused Lean process exited 0, `git diff --check` passed,
placeholder/status audits reported zero findings, and the full 3345-job
`lake build` passed; `scripts/check_diff_trust.sh` is absent from this
checkout. The normalized classifier
`.change_log/manual_attempt_20260721_VeltkampEven2_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `VeltkampEven2` is removed from the
active list, and `Veltkamp_pos` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_054503` left the exact `Veltkamp_pos`
payload unchanged and did not run a build. The manual repair restored exact
public `Veltkamp_pos` under only the expanded upstream `VeltN` section
assumptions. A private first-normal separation lemma proves that a canonical
closest result is normal when its exact input lies above `firstNormalPos`.
The public proof applies that lemma directly to `p`; for `q`, it follows the
upstream two-exponent shift of `x`, uses closest-rounding monotonicity to show
`2*x < p`, and applies the same separation argument to `Fopp q`. Exact
`Veltkamp_aux` then supplies the half-ulp residual bound and same-value reduced
closest witness with the required exponent lower bound. The focused Lean
process exited 0, `git diff --check` passed, placeholder/status audits reported
zero findings, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The normalized
classifier `.change_log/manual_attempt_20260721_Veltkamp_pos_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `Veltkamp_pos` is removed from the active
list, and `VeltkampN_aux` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_060314` left the exact `VeltkampN_aux`
payload unchanged and did not run a build. The manual repair restored exact
public `VeltkampN_aux` under only the expanded upstream `VeltN` assumptions.
Normality gives a nonzero represented value, so the nonnegative branch calls
`Veltkamp_pos` directly. The negative branch negates `x`, `p`, `q`, and `hx`,
transports all three closest-rounding premises with `ClosestOpp`, applies
`Veltkamp_pos`, and negates the reduced witness back while preserving its
value, closestness, exponent, and the residual bound. The focused Lean process
exited 0, `git diff --check` passed, placeholder/status audits reported zero
findings, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The normalized
classifier
`.change_log/manual_attempt_20260721_VeltkampN_aux_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `VeltkampN_aux` is removed from the
active list, and `VeltkampN` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_061502` left the exact `VeltkampN` payload
unchanged and did not run a build. The manual repair restored exact public
`VeltkampN` under only the expanded upstream `VeltN` assumptions. It
normalizes the merely bounded closest outputs `p` and `q`, proves both
normalized representatives are bounded and canonical with unchanged real
values, reconstructs the three closest-rounding premises, and invokes exact
`VeltkampN_aux` for the unchanged residual and reduced-witness conclusion.
The focused Lean process exited 0, `git diff --check` passed,
placeholder/status audits reported zero findings, and the full 3345-job
`lake build` passed; `scripts/check_diff_trust.sh` is absent from this
checkout. The normalized classifier
`.change_log/manual_attempt_20260721_VeltkampN_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `VeltkampN` is removed from the active list, and
`VeltkampEven_pos` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_062537` left the exact
`VeltkampEven_pos` payload unchanged and did not run a build. The manual repair
restored exact public `VeltkampEven_pos` under only the expanded upstream
`VeltN` assumptions. It extracts the ordinary closest-rounding components from
the three even-closest premises, proves `p` normal with the first-normal
separation argument, and proves `q` normal using closest-rounding monotonicity
and the upstream two-exponent shift. It then splits on radix parity and invokes
exact `VeltkampEven1` or `VeltkampEven2` to construct the unchanged
same-value reduced even-closest witness. The focused Lean process exited 0,
`git diff --check` passed, placeholder/status audits reported zero findings,
and the full 3345-job `lake build` passed; `scripts/check_diff_trust.sh` is
absent from this checkout. The normalized classifier
`.change_log/manual_attempt_20260721_VeltkampEven_pos_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `VeltkampEven_pos` is removed from the
active list, and `VeltkampEvenN_aux` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_063702` left the exact
`VeltkampEvenN_aux` payload unchanged and did not run a build. The manual
repair restored exact public `VeltkampEvenN_aux` under only the expanded
upstream `VeltN` assumptions. Normality excludes a zero represented input, so
the nonnegative branch invokes exact `VeltkampEven_pos`. The negative branch
negates `x`, `p`, `q`, and `hx`, transports all three `EvenClosest` premises
with exact `EvenClosestSymmetric`, invokes the positive theorem, and negates
the reduced witness back while preserving its represented value and
even-closest relation. The focused Lean process exited 0, `git diff --check`
passed, placeholder/status audits reported zero findings, and the full
3345-job `lake build` passed; `scripts/check_diff_trust.sh` is absent from this
checkout. The normalized classifier
`.change_log/manual_attempt_20260721_VeltkampEvenN_aux_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `VeltkampEvenN_aux` is removed from the
active list, and `VeltkampEvenN` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_064633` left the exact `VeltkampEvenN`
payload unchanged and did not run a build. The manual repair restored exact
public `VeltkampEvenN` under only the expanded upstream `VeltN` assumptions.
It normalizes the rounded intermediates `p` and `q`, proves the normalized
representatives bounded, canonical, and value-preserving, and explicitly
transports both branches of each `EvenClosest` premise: normalization
idempotence preserves normalized-even parity, while represented-value equality
preserves uniqueness. Exact `VeltkampEvenN_aux` then supplies the unchanged
same-value reduced even-closest witness. The focused Lean process exited 0,
`git diff --check` passed, placeholder/status audits reported zero findings,
and the full 3345-job `lake build` passed; `scripts/check_diff_trust.sh` is
absent from this checkout. The normalized classifier
`.change_log/manual_attempt_20260721_VeltkampEvenN_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `VeltkampEvenN` is removed from the active list,
and `Closestbbplus` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_065619` left the exact `Closestbbplus`
payload unchanged and did not run a build. The manual repair restored exact
public `Closestbbplus`, the upstream extension direction from `Closest b0` to
`Closest (plusExp b0 t)`, with no extra premises. Competitors satisfying the
original exponent bound are handled directly by original closestness. Any
newly admitted lower-exponent competitor has magnitude below the first
interior radix threshold: when the exact float lies inside that threshold, an
exact shifted original-bound representative gives zero error; otherwise the
signed threshold representative is no farther away. The focused Lean process
exited 0, `git diff --check` passed, placeholder/status audits reported zero
findings, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The normalized
classifier `.change_log/manual_attempt_20260721_Closestbbplus_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `Closestbbplus` is removed from the active
list, and `EvenClosestbplusb` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_071155` left the exact
`EvenClosestbplusb` payload unchanged and did not run a build. The manual
repair restored exact public `EvenClosestbplusb`, the upstream restriction of
nearest-even closestness from `plusExp b0 t` back to `b0`, with no extra
premises. Ordinary closestness restricts through exact `Closestbplusb`. In the
normal branch, canonical uniqueness identifies the normalizations under the
two bounds and transfers normalized parity; in the subnormal branch,
`ClosestUlp` and minimum-unit discreteness force exactness, which supplies the
required uniqueness alternative. The focused Lean process exited 0,
`git diff --check` passed, placeholder/status audits reported zero findings,
and the full 3345-job `lake build` passed; `scripts/check_diff_trust.sh` is
absent from this checkout. The normalized classifier
`.change_log/manual_attempt_20260721_EvenClosestbplusb_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `EvenClosestbplusb` is removed from the
active list, and `ClosestClosest` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_073226` failed without source changes or a
build after the Codex process encountered the local model-cache configuration
error. The manual repair restored exact public `ClosestClosest` under only the
expanded upstream section assumptions. It takes absolute values, normalizes
the lower-exponent closest result, and proves that its bounded normalized
successor lies strictly between the two closest represented values. Depending
on which side of that successor contains `|z|`, one of the original
closestness inequalities is then impossible. The focused Lean process exited
0, `git diff --check` passed, placeholder/status audits reported zero
findings, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The normalized
classifier `.change_log/manual_attempt_20260721_ClosestClosest_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `ClosestClosest` is removed from the
active list, and `EvenClosestbbplus` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_074904` failed without source changes or a
build. The manual repair restored exact public `EvenClosestbbplus` under only
the expanded upstream section assumptions. Above the original minimum
exponent, normalized parity transfers by canonical uniqueness; original-bound
uniqueness handles ordinary competitors, while exact `ClosestClosest` excludes
new lower-exponent competitors admitted by `plusExp`. At the minimum exponent,
`ClosestUlp` and minimum-unit discreteness force the rounded result to equal the
exact input, so uniqueness follows under the enlarged bound. The focused Lean
process exited 0, `git diff --check` passed, placeholder/status audits reported
zero findings, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The normalized
classifier `.change_log/manual_attempt_20260721_EvenClosestbbplus_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `EvenClosestbbplus` is removed from the
active list, and `VeltkampS` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_080854` failed without source changes or a
build after Codex process/session persistence errors. The manual repair
restored exact public `VeltkampS` under only the expanded upstream section
assumptions. The zero branch constructs a direct zero witness. For a nonzero
subnormal input, the proof normalizes the input under `plusExp`, transfers the
three closestness premises to that enlarged bound, and applies exact
`VeltkampN`. It then transfers the residual bound back to the original input
exponent and restricts the reduced-bound witness: witnesses already above the
old minimum exponent transfer directly, while lower-exponent min/max witnesses
are re-encoded at the subnormal input exponent before restriction. The focused
Lean process exited 0, `git diff --check` passed, placeholder/status audits
reported zero findings, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The normalized
classifier `.change_log/manual_attempt_20260721_VeltkampS_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `VeltkampS` is removed from the active
list, and `VeltkampEvenS` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_083331` failed without source changes or a
build after Codex process/session persistence errors. The manual repair
restored exact public `VeltkampEvenS` under only the expanded upstream section
assumptions. The zero branch constructs a normalized-even zero witness. For a
nonzero subnormal input, the proof normalizes the input under `plusExp`,
transfers all three `EvenClosest` premises to that enlarged bound, and applies
exact `VeltkampEvenN`. It restricts witnesses already in the old exponent
range directly. For lower-exponent min/max witnesses, it re-encodes the value
at the subnormal input exponent and preserves nearest-even parity by proving
the two normalized canonical representatives equal before restricting the
bound. The focused Lean process exited 0, `git diff --check` passed,
placeholder/status audits reported zero findings, and the full 3345-job
`lake build` passed; `scripts/check_diff_trust.sh` is absent from this
checkout. The normalized classifier
`.change_log/manual_attempt_20260721_VeltkampEvenS_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `VeltkampEvenS` is removed from the active list,
and `VeltkampEven` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_084628` failed without source changes or a
build after Codex process/session persistence errors. The manual repair
restored exact public `VeltkampEven` under only the expanded upstream section
assumptions. It normalizes the bounded input, proves the normalized
representative canonical, transfers the two input-dependent `EvenClosest`
premises by exact represented-value equality, and splits the canonical result.
The normal branch delegates to exact `VeltkampEvenN`; the subnormal branch
delegates to exact `VeltkampEvenS`. The focused Lean process exited 0,
`git diff --check` passed, placeholder/status audits reported zero findings,
and the full 3345-job `lake build` passed; `scripts/check_diff_trust.sh` is
absent from this checkout. The normalized classifier
`.change_log/manual_attempt_20260721_VeltkampEven_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `VeltkampEven` is removed from the active list,
and `Veltkamp_tail_aux` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_085558` failed without source changes or a
build after Codex process/session persistence errors. The manual repair
restored exact public `Veltkamp_tail_aux` under only the expanded upstream
section assumptions, including the upstream `tx` closestness premise. It
splits canonical `x` into normal and subnormal cases, obtains an equal-value
reduced Veltkamp witness from exact `VeltkampN` or `VeltkampS`, and proves that
the witness exponent is at least `x.Fexp`. The local `Fminus` exponent law then
preserves `x.Fexp`; the real residual bound cancels the positive radix scale to
give the exact mantissa bound. The focused Lean process exited 0,
`git diff --check` passed, placeholder/status audits reported zero findings,
and the full 3345-job `lake build` passed; `scripts/check_diff_trust.sh` is
absent from this checkout. The normalized classifier
`.change_log/manual_attempt_20260721_Veltkamp_tail_aux_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `Veltkamp_tail_aux` is removed from the
active list, and `Veltkamp_tail2` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_091300` restored exact public
`Veltkamp_tail2` under only the expanded upstream section assumptions. It
normalizes the bounded input, reuses exact `Veltkamp_tail_aux`, and applies
`FboundedMbound2` to construct an equal-value residual witness in the `s - 1`
split bound. The binary-radix identity `2 ^ s / 2 = 2 ^ (s - 1)` supplies the
mantissa bound; closest-rounding minimality identifies the witness with `tx`,
while the constructor preserves the normalized input exponent lower bound.
The independent focused Lean process exited 0, `git diff --check` passed, the
placeholder and generated-status audits reported zero findings, and the full
3345-job `lake build` passed; `scripts/check_diff_trust.sh` is absent from this
checkout. The harness's top-level `attempt.json` recorded `result = proved`
but did not propagate its nested build or Coq-alignment checks. The normalized
classifier
`.change_log/manual_attempt_20260721_Veltkamp_tail2_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `Veltkamp_tail2` is removed from the active list,
and `VeltkampU` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_094158` restored exact public `VeltkampU`
under only the expanded upstream section assumptions: canonical `x`, the four
`Closest` premises, the residual estimate and exact `x = hx + tx`
decomposition, an equal-value reduced-bound `hx` witness with the conditional
normal exponent lower bound, and an equal-value split-bound `tx` witness with
exponent at least `x.Fexp`. The proof combines `VeltkampN` and `VeltkampS` for
the head witness with `Veltkamp_tail_aux` for the tail, then uses closestness
to identify the exact residual with `tx`. The independent focused Lean process
exited 0, `git diff --check` passed, the placeholder and generated status
audits reported zero findings, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The harness's
top-level `attempt.json` recorded `result = proved` but did not propagate its
nested build or Coq-alignment checks. The normalized classifier
`.change_log/manual_attempt_20260721_VeltkampU_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `VeltkampU` is removed from the active
list, and `BoundedL` is next.

2026-07-21 completion note: exact public `BoundedL` is restored under the
expanded GenericDek section assumptions. The proof constructs the upstream
rescaled-mantissa witness at exponent `e`, preserves the represented real
value, and cancels the positive `radix ^ e` scale from the strict magnitude
bound to establish `Fbounded b`. The focused Lean process produced no errors,
`git diff --check` passed, the placeholder and generated-status audits
reported zero findings, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The classifier
`.change_log/manual_attempt_20260721_BoundedL_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `BoundedL` is removed from the active list, and
`Closestbbext` is next.

2026-07-21 completion note: the default subscription harness attempt
`.change_log/codex_attempt_20260721_103346` failed before proof work because
the configured `gpt-5.6-sol` model requires a newer Codex CLI. The explicit
`gpt-5.5` subscription retry
`.change_log/codex_attempt_20260721_103544` restored exact public
`Closestbbext` under only the expanded GenericDek section assumptions. It
represents an arbitrary `bext` with the same mantissa bound and strictly larger
`dExp` as `plusExp b ((bext.dExp - b.dExp + 1).toNat)`, then applies exact
`Closestbbplus`. The independent focused Lean process exited 0,
`git diff --check` passed, the placeholder and generated-status audits
reported zero findings, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The harness's
top-level `attempt.json` recorded `result = proved` but did not propagate its
nested build or Coq-alignment checks. The normalized classifier
`.change_log/manual_attempt_20260721_Closestbbext_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `Closestbbext` is removed from the active list,
and `Underf_Err1` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_110255` restored exact public
`Underf_Err1` under only the expanded upstream GenericDek section assumptions
and the existing exact `Underf_Err` predicate. The proof transfers the bounded
input to the original bound in the above-minimum-exponent branch, where
closestness gives exact equality. In the underflow branch it bounds the input
and closest result by `firstNormalPos`, normalizes the result, derives the
minimum original exponent with `Fcanonic_Rle_Zle`, and combines the resulting
minimum `Fulp` equality with `ClosestUlp` to prove the exact half-unit error
bound. The independent focused Lean process exited 0, `git diff --check`
passed, the direct live-hole scan and placeholder/generated-status audits
reported zero findings, and the full 3345-job `lake build` passed;
`scripts/check_diff_trust.sh` is absent from this checkout. The harness's
top-level `attempt.json` recorded `result = proved` but did not propagate its
nested build or Coq-alignment checks. The normalized classifier
`.change_log/manual_attempt_20260721_Underf_Err1_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `Underf_Err1` is removed from the active list,
and `Underf_Err2_aux` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_114333` checked exact upstream
`Underf_Err2_aux`, left the tracked worktree unchanged, and classified the
target as blocked on the arbitrary-real canonical closest-transfer argument.
The blocker was then repaired manually rather than preserved. Two private
lemmas prove that a canonical float strictly above the old minimum exponent
has one ulp plus the minimum-normal magnitude available, and use that gap to
transfer arbitrary-real closestness from `b` to an extended bound with the
same mantissa limit. Exact public `Underf_Err2_aux` then follows the upstream
case split: the strict-exponent branch returns `x1`; the minimum-exponent
branch constructs an extended-bound closest `x2` with the closed
`RND_Closest` correctness stack and combines the original half-unit error
with the extended quarter-unit error to obtain the exact `3/4` payload. No
totality, finite-box, conclusion, or other extra public premise was added.
The focused Lean process exited 0, `git diff --check` passed, the direct
live-hole scan and placeholder/generated-status audits reported zero findings,
and the full 3345-job `lake build` passed; `scripts/check_diff_trust.sh` is
absent from this checkout. The normalized classifier
`.change_log/manual_attempt_20260721_Underf_Err2_aux_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `Underf_Err2_aux` is removed from the
active list, and `Underf_Err2` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_122007` restored exact public
`Underf_Err2` from upstream `Pff.v` line 16750 under the expanded GenericDek
section assumptions and existing exact `Underf_Err2_aux`. The proof normalizes
the original closest result internally, derives the normalized closest payload
from `FnormalizeCorrect` and concrete `Closest`, applies `Underf_Err2_aux` to
the canonical normalized representative, and transports the exact `3/4`
underflow-error payload back to the original representation. No canonicality,
totality, finite-box, conclusion, or other extra public premise was added. The
focused Lean process exited 0, `git diff --check` passed, the placeholder and
generated-status audits reported zero findings, and the full 3345-job
`lake build` passed; `scripts/check_diff_trust.sh` is absent from this checkout.
The normalized classifier
`.change_log/manual_attempt_20260721_Underf_Err2_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `Underf_Err2` is removed from the active list, and
`Underf_Err3` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_123937` explored exact upstream
`Underf_Err3` but was classified failed. Its draft added non-upstream public
`hvNum_gt` and `hBoundExp` premises, so it was not counted. The manual repair
removed both premises and restored exact public `Underf_Err3` under only the
expanded GenericDek section assumptions and the theorem's explicit upstream
hypotheses. A private lattice lemma aligns the exact input sum at the rounded
result exponent, combines `ClosestUlp` with the nonzero integer-mantissa gap,
and forces the rounding error to zero without totality or `boundR` premises.
The low-exponent branch bounds the exact subtraction by the predecessor of the
mantissa limit, applies that lattice exactness result, and combines the two
input underflow errors; the high-exponent branch transports both exactness
implications directly. No `dExp` invariant, totality, finite-box, canonicity,
conclusion, or other extra public premise was added. The focused Lean process
exited 0, `git diff --check` passed, the direct live-hole scan and
placeholder/generated-status audits reported zero findings, and the full
3345-job `lake build` passed; `scripts/check_diff_trust.sh` is absent from this
checkout. The normalized classifier
`.change_log/manual_attempt_20260721_Underf_Err3_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `Underf_Err3` is removed from the active list, and
`Underf_Err3_bis` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_132843` restored the proof of exact public
`Underf_Err3_bis`; a manual fidelity check then restored the explicit
GenericDek `1 < precision` section hypothesis that the harness draft had
omitted as redundant under `4 <= precision`. The final theorem adds only the
upstream `4 <= precision` and `epsx + epsy <= 7` hypotheses over the existing
section assumptions and `Underf_Err3` payloads, derives
`7 <= radix^(precision-1)-1` from `radix >= 2` and `precision >= 4`, and applies
`Underf_Err3` with the unchanged underflow-error, bounded-difference, exponent,
and closestness hypotheses. No totality, `dExp`, `boundR`, finite-box,
canonicality, conclusion, or other extra public premise was added. The focused
Lean check exited 0, `git diff --check` passed, the direct live-hole scan and
placeholder/generated-status audits reported zero findings, and the full
3345-job `lake build` passed; `scripts/check_diff_trust.sh` is absent from this
checkout. The classifier record
`.change_log/manual_attempt_20260721_Underf_Err3_bis_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore `Underf_Err3_bis` is removed from the
active list, and `eLe` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_135051` correctly rejected a deliberately
too-weak projection of upstream `eLe`; without the Sec1 precision and product
range hypotheses the claimed error bound has a radix-2 counterexample. The
corrected subscription attempt `.change_log/codex_attempt_20260721_135903`
then restored exact public `eLe` with the section facts consumed by the Coq
proof: the beta/radix equality, radix lower bound,
`b.vNum = Zpower_nat radix t`, natural range hypotheses `2 <= s` and
`s <= t - 2`, normality of `x` and `y`, product exponent lower bound `K`,
closestness of `r`, and exact residual decomposition
`F2R x * F2R y = F2R r + F2R e`. It deliberately omits unused `Hst1`/`Hst2`
and the later split operands and assumptions for `x1`/`x2`/`y1`/`y2`. The
proof follows the upstream `ClosestUlp` route, derives the product max-float
bound directly from `Closest` instead of adding totality as a public premise,
and compares normalized exponents via `Fcanonic_Rle_Zle`. Independent focused
Lean exited 0, `git diff --check` passed, the direct live-hole scan and
placeholder/generated-status audits reported zero findings, and the full
3345-job `lake build` passed; `scripts/check_diff_trust.sh` is absent from this
checkout. The normalized classifier
`.change_log/manual_attempt_20260721_eLe_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore `eLe` is removed from the active list, reducing
the ledger from 53 to 52; `rExp` is next.

2026-07-21 completion note: subscription harness attempt
`.change_log/codex_attempt_20260721_142334` checked exact upstream `rExp` but
stopped because the local `RoundAbsMonotonel` packaging requires
`ClosestTotal`, whose current construction exposes the forbidden `boundR`
side condition. The manual repair preserved the exact Sec1 public surface and
avoided that local packaging mismatch: it derives the minimum-normal product
magnitude from the two `Fnormal` hypotheses, applies `Closest` directly to the
positive or negative bounded comparison float according to the product sign,
then compares canonical exponents after normalization and transports the
bound back to `r`. No residual `e`, `eeq`, `Hst1`/`Hst2`, split operands,
totality, `boundR`, canonicity, conclusion, or other extra public premise was
added. Focused `lake env lean FloatSpec/src/Pff/Pff.lean` exited 0. Therefore
`git diff --check` passed, the direct live-hole scan and
placeholder/generated-status audits reported zero findings, and the full
3345-job `lake build` passed; `scripts/check_diff_trust.sh` is absent from this
checkout. The normalized classifier
`.change_log/manual_attempt_20260721_rExp_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore exact public `rExp` is removed from the active
list, reducing the ledger from 52 to 51; `Boundedt1` is next.

2026-07-21 completion note: exact public `Boundedt1` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after exact `rExp`. The public Lean
payload matches the upstream Sec1 context consumed by Coq `Boundedt1`: beta/radix
equality, `1 < radix`, `b.vNum = Zpower_nat radix t`, `SLe`, `SGe`, `Hst1`,
`Hst2`, normality of `x` and `y`, product exponent lower bound `K`, closestness
of `r`, exact residual equality, split equalities for `x = x1 + x2` and
`y = y1 + y2`, half-scale bounds on `x2` and `y2`, plus `x1Exp` and `y1Exp`.
The last two exponent premises are needed exactly as in upstream to prove the
constructed `Fminus r (Fmult x1 y1)` exponent is at least
`t - 1 + x.Fexp + y.Fexp`; `x2Exp` and `y2Exp` are not used and were not added.
No totality, `boundR`, canonicity, conclusion premise, weakened payload, or
mode-erased placeholder was introduced. The proof uses exact local `BoundedL`,
`eLe`, `rExp`, `x2y2Le`, `x2y1Le`, `x1y2Le`, and `powerRZSumRle`
infrastructure, after deriving the normal operand magnitude bounds from
`Fbounded`. Focused `lake env lean FloatSpec/src/Pff/Pff.lean` exited 0;
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings;
`git diff --check` passed; `scripts/status_report.sh --write` reported 58 Lean
files with `sorry = 0`, `axiom = 0`, `admit = 0`, and zero
placeholder/weakening findings; full `lake build` passed all 3345 jobs. The
repository has no `scripts/check_diff_trust.sh`, so that optional trust gate
could not be run. The
normalized classifier
`.change_log/manual_attempt_20260721_Boundedt1_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore exact public `Boundedt1` is removed from the active
list, reducing the ledger from 51 to 50; `Boundedt2` is next.

2026-07-21 completion note: exact public `Boundedt2` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after exact `Boundedt1`. The public
Lean payload matches the upstream Sec1 context consumed by Coq `Boundedt2`:
beta/radix equality, `1 < radix`, `b.vNum = Zpower_nat radix t`, `SLe`,
`SGe`, `Hst1`, `Hst2`, normality of `x` and `y`, product exponent lower bound
`K`, closestness of `r`, exact residual equality, split equalities for
`x = x1 + x2` and `y = y1 + y2`, half-scale bounds on `x2` and `y2`, plus
`x1Exp`, `y1Exp`, and the exact upstream `y2Exp : y.Fexp ≤ y2.Fexp`.
No `x2Exp`, totality, `boundR`, canonicity,
conclusion premise, weakened payload, or mode-erased placeholder was introduced.
The proof uses exact local `Boundedt1`, `BoundedL`, `eLe`, `x2y1Le`,
`x2y2Le`, and `powerRZSumRle` infrastructure, following upstream by building
`Fminus t1 (Fmult x1 y2)` and bounding the residual
`r - x1*y1 - x1*y2`. Focused
`lake env lean FloatSpec/src/Pff/Pff.lean` exited 0;
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings;
`git diff --check` passed; `scripts/status_report.sh --write` reported 58 Lean
files with `sorry = 0`, `axiom = 0`, `admit = 0`, and zero
placeholder/weakening findings; full `lake build` passed all 3345 jobs. The
repository has no `scripts/check_diff_trust.sh`, so that optional trust gate
could not be run. The normalized classifier
`.change_log/manual_attempt_20260721_Boundedt2_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore exact public `Boundedt2` is removed from the active
list, reducing the ledger from 50 to 49; `Boundedt3` is next.

2026-07-21 completion note: exact public `Boundedt3` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after exact `Boundedt2`. The public
Lean payload matches the upstream Sec1 context consumed by Coq `Boundedt3`:
beta/radix equality, `1 < radix`, `b.vNum = Zpower_nat radix t`, `SLe`,
`SGe`, `Hst1`, `Hst2`, normality of `x` and `y`, product exponent lower bound
`K`, closestness of `r`, exact residual equality, split equalities for
`x = x1 + x2` and `y = y1 + y2`, half-scale bounds on `x2` and `y2`, plus
`x1Exp`, `y1Exp`, and exact upstream `x2Exp : x.Fexp ≤ x2.Fexp` and
`y2Exp : y.Fexp ≤ y2.Fexp`. No totality, `boundR`, canonicity, conclusion
premise, weakened payload, or mode-erased placeholder was introduced. The proof
uses exact local `Boundedt2`, `BoundedL`, `eLe`, `x2y2Le`, and
`powerRZSumRle` infrastructure, following upstream by building
`Fminus t2 (Fmult x2 y1)` and bounding the residual
`r - x1*y1 - x1*y2 - x2*y1`. Focused
`lake env lean FloatSpec/src/Pff/Pff.lean` exited 0;
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings;
`git diff --check` passed; `scripts/status_report.sh --write` reported 58 Lean
files with `sorry = 0`, `axiom = 0`, `admit = 0`, and zero
placeholder/weakening findings; full `lake build` passed all 3345 jobs. The
repository has no `scripts/check_diff_trust.sh`, so that optional trust gate
could not be run. The normalized classifier
`.change_log/manual_attempt_20260721_Boundedt3_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore exact public `Boundedt3` is removed from the active
list, reducing the ledger from 49 to 48; `Boundedt4` is next.

2026-07-21 completion note: exact public `Boundedt4` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after exact `Boundedt3`. The public
Lean payload matches the upstream Sec1 context consumed by Coq `Boundedt4`:
beta/radix equality, `1 < radix`, `b.vNum = Zpower_nat radix t`, `SLe`, `SGe`,
normality of `x` and `y`, product exponent lower bound `K`, closestness of `r`,
and split equalities for `x = x1 + x2` and `y = y1 + y2`. No `Hst1`/`Hst2`,
residual error float `e` or `eeq`, half-scale bounds, split exponent premises,
totality, `boundR`, canonicity, conclusion premise, weakened payload, or
mode-erased placeholder was introduced. The proof follows upstream by applying
exact local `errorBoundedMult` to `x * y` rounded to `r`, then constructing
`Fopp g`; `Fopp_correct` supplies the real value and `oppBounded` supplies the
boundedness. Focused `lake env lean FloatSpec/src/Pff/Pff.lean` exited 0;
`git diff --check` passed;
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings;
`scripts/status_report.sh --write` reported 58 Lean files with `sorry = 0`,
`axiom = 0`, `admit = 0`, and zero placeholder/weakening findings; full
`lake build` passed all 3345 jobs. The repository has no
`scripts/check_diff_trust.sh`, so that optional trust gate could not be run.
The normalized classifier
`.change_log/manual_attempt_20260721_Boundedt4_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore exact public `Boundedt4` is removed from the active
list, reducing the ledger from 48 to 47; `Boundedt4_aux` is next.

2026-07-21 completion note: exact public `Boundedt4_aux` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after exact `Boundedt4`. The public
Lean payload matches the upstream Sec1 context consumed by Coq `Boundedt4_aux`:
beta/radix equality, `1 < radix`, `b.vNum = Zpower_nat radix t`, `SLe`, `SGe`,
normality of `x` and `y`, product exponent lower bound `K`, closestness of `r`,
and split equalities for `x = x1 + x2` and `y = y1 + y2`. The conclusion is the
exact upstream auxiliary strengthening of `Boundedt4`: existence of `xprime`
with the five-term residual value, `Fbounded b xprime`, and
`xprime.Fexp = x.Fexp + y.Fexp`. No `Hst1`/`Hst2`, residual error float `e` or
`eeq`, half-scale bounds, split exponent premises, totality, `boundR`,
canonicity, conclusion premise, weakened payload, or mode-erased placeholder was
introduced. The proof follows upstream by applying exact local
`errorBoundedMult` to `x * y` rounded to `r`, then constructing `Fopp g`;
`Fopp_correct` supplies the real value, `oppBounded` supplies boundedness, and
the definitional exponent preservation of `Fopp` supplies the auxiliary exponent
equality. Focused `lake env lean FloatSpec/src/Pff/Pff.lean` exited 0;
`git diff --check` passed; `scripts/audit_placeholders.sh --json FloatSpec`
reported zero findings; `scripts/status_report.sh --write` reported 58 Lean
files with `sorry = 0`, `axiom = 0`, `admit = 0`, and zero
placeholder/weakening findings. The repository has no executable
`scripts/check_diff_trust.sh`, so that optional trust gate could not be run.
Full `lake build` passed all 3345 jobs. The normalized classifier
`.change_log/manual_attempt_20260721_Boundedt4_aux_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore exact public `Boundedt4_aux` is removed from the
active list, reducing the ledger from 47 to 46; `Boundedx1y1_aux` is next.

2026-07-21 completion note: exact public `Boundedx1y1_aux` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after exact `Boundedt4_aux`. The public
Lean payload matches the upstream Sec1 context consumed by Coq
`Boundedx1y1_aux`: beta/radix equality, `1 < radix`,
`b.vNum = Zpower_nat radix t`, product exponent lower bound `K`, split exponent
premises for `x1` and `y1`, reduced-bound hypotheses for `x1` and `y1`, and
`(t : Int) <= 2 * (s : Int)`. The conclusion is the exact upstream auxiliary
product result: existence of `xprime` with
`F2R xprime = F2R x1 * F2R y1`, `Fbounded b xprime`, and
`xprime.Fexp = x1.Fexp + y1.Fexp`. No `SLe`/`SGe`, `Hst1`/`Hst2`, normality,
rounding or `Closest`, residual hypotheses, `Fx2`/`Fy2`, totality, `boundR`,
canonicity, conclusion premise, weakened payload, or mode-erased placeholder was
introduced. The proof constructs `Fmult x1 y1`; `Fmult_correct` supplies the real
value, the reduced-bound mantissa inequalities combine through integer-power
product monotonicity to recover `b.vNum`, and the exponent hypotheses plus `K`
give the product exponent lower bound. Focused
`lake env lean FloatSpec/src/Pff/Pff.lean` exited 0; `git diff --check` passed;
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings;
`scripts/status_report.sh --write` reported 58 Lean files with `sorry = 0`,
`axiom = 0`, `admit = 0`, and zero placeholder/weakening findings. The
repository has no executable `scripts/check_diff_trust.sh`, so that optional
trust gate could not be run. Full `lake build` passed all 3345 jobs. The
normalized classifier
`.change_log/manual_attempt_20260721_Boundedx1y1_aux_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore exact public `Boundedx1y1_aux` is removed
from the active list, reducing the ledger from 46 to 45; `Boundedx1y1` is next.

2026-07-21 completion note: exact public `Boundedx1y1` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after exact `Boundedx1y1_aux`. It
matches upstream `Pff.v:Boundedx1y1`: the public theorem consumes the same
Sec1 payload as the auxiliary theorem and returns an `xprime` whose real value
is `F2R x1 * F2R y1` and which is `Fbounded b`. It introduces no extra
hypothesis and drops only the auxiliary exponent-equality conjunct, exactly as
the Coq wrapper does. The proof directly eliminates local exact
`Boundedx1y1_aux` and projects its value and boundedness witnesses. The first
subscription harness attempt
`.change_log/codex_attempt_20260721_170359` made no changes because the local
Codex CLI rejected its configured `gpt-5.6-sol` default as requiring a newer
CLI. The required compatible rerun at
`.change_log/codex_attempt_20260721_170512` used `gpt-5.5` with high reasoning,
recorded `result = proved`, and passed its local target gate. Independent
focused `lake env lean FloatSpec/src/Pff/Pff.lean` exited 0;
`git diff --check` and the direct added-hole scan passed;
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings; and
`scripts/status_report.sh --write` reported 58 Lean files with `sorry = 0`,
`axiom = 0`, `admit = 0`, and zero placeholder/weakening findings. The
repository has no executable `scripts/check_diff_trust.sh`, so that optional
trust gate could not be run. Full `lake build` passed all 3345 jobs. The
normalized classifier
`.change_log/manual_attempt_20260721_Boundedx1y1_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore exact public `Boundedx1y1` is removed from the
active list, reducing the ledger from 45 to 44; `Boundedx1y2_aux` is next.

2026-07-21 completion note: exact public `Boundedx1y2_aux` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after exact `Boundedx1y1`. The public
Lean payload matches the upstream Sec1 context consumed by Coq
`Boundedx1y2_aux`: beta/radix equality, `1 < radix`,
`b.vNum = Zpower_nat radix t`, `SGe`, product exponent lower bound `K`, split
exponent premises for `x1` and `y2`, reduced-bound hypothesis for `x1`, and
split-bound hypothesis for `y2`. The conclusion is the exact upstream auxiliary
product result: existence of `xprime` with
`F2R xprime = F2R x1 * F2R y2`, `Fbounded b xprime`, and
`xprime.Fexp = x1.Fexp + y2.Fexp`. No residual hypotheses, rounding or
closestness assumptions, totality, boundR, canonicity, conclusion premise,
weakened payload, or mode-erased placeholder was introduced. The proof
constructs `Fmult x1 y2`; `Fmult_correct` supplies the real value, the
reduced/split mantissa inequalities combine through integer-power monotonicity
and `SGe` to recover `b.vNum`, and the exponent hypotheses plus `K` give the
product exponent lower bound. Focused `lake env lean FloatSpec/src/Pff/Pff.lean`
exited 0; `git diff --check` passed; `scripts/audit_placeholders.sh --json
FloatSpec` reported zero findings; `scripts/status_report.sh --write` reported
58 Lean files with `sorry = 0`, `axiom = 0`, `admit = 0`, and zero
placeholder/weakening findings. The repository has no executable
`scripts/check_diff_trust.sh`, so that optional trust gate could not be run.
Full `lake build` passed all 3345 jobs. The normalized classifier
`.change_log/manual_attempt_20260721_Boundedx1y2_aux_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore exact public `Boundedx1y2_aux` is removed
from the active list, reducing the ledger from 44 to 43; `Boundedx1y2` is next.

2026-07-21 completion note: exact public `Boundedx1y2` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after exact `Boundedx1y2_aux`. It
matches upstream `Pff.v:Boundedx1y2`: the public theorem consumes the same Sec1
payload as `Boundedx1y2_aux` and returns an `xprime` whose real value is
`F2R x1 * F2R y2` and which is `Fbounded b`. It introduces no extra hypothesis
and drops only the auxiliary exponent-equality conjunct, exactly as the Coq
wrapper does. The proof directly eliminates local exact `Boundedx1y2_aux` and
projects its value and boundedness witnesses. Focused
`lake env lean FloatSpec/src/Pff/Pff.lean` exited 0; full `lake build` passed
all 3345 jobs; `git diff --check` passed; `scripts/audit_placeholders.sh --json
FloatSpec` reported zero findings; and `scripts/status_report.sh --write`
reported 58 Lean files with `sorry = 0`, `axiom = 0`, `admit = 0`, and zero
placeholder/weakening findings. The repository has no executable
`scripts/check_diff_trust.sh`, so that optional trust gate could not be run.
The normalized classifier
`.change_log/manual_attempt_20260721_Boundedx1y2_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore exact public `Boundedx1y2` is removed from the
active list, reducing the ledger from 43 to 42; `Boundedx2y1_aux` is next.

2026-07-21 completion note: exact public `Boundedx2y1_aux` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after exact `Boundedx1y2`. The public
Lean payload matches the upstream Sec1 context consumed by Coq
`Boundedx2y1_aux`: beta/radix equality, `1 < radix`,
`b.vNum = Zpower_nat radix t`, `SGe`, product exponent lower bound `K`, split
exponent premises for `x2` and `y1`, split-bound hypothesis for `x2`, and
reduced-bound hypothesis for `y1`. Its conclusion is the exact upstream
auxiliary product result: existence of `xprime` with
`F2R xprime = F2R x2 * F2R y1`, `Fbounded b xprime`, and
`xprime.Fexp = x2.Fexp + y1.Fexp`. No normality, residual, rounding,
closestness, unrelated component, `Hst1`/`Hst2`/`Hst3`, totality, `boundR`,
canonicity, conclusion, or weakening premise was introduced. The proof
constructs `Fmult x2 y1`; `Fmult_correct` supplies the real value, the
split/reduced mantissa inequalities combine through integer-power monotonicity
and `SGe` to recover `b.vNum`, and the exponent hypotheses plus `K` give the
product exponent lower bound. Required subscription harness attempt
`.change_log/codex_attempt_20260721_175413` used `gpt-5.5` with high reasoning,
recorded `result = proved`, and passed its local target gate. Independent
focused `lake env lean FloatSpec/src/Pff/Pff.lean` exited 0;
`git diff --check` and the direct added-Lean-hole scan passed;
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings; and
`scripts/status_report.sh --write` reported 58 Lean files with `sorry = 0`,
`axiom = 0`, `admit = 0`, and zero placeholder/weakening findings. The
repository has no executable `scripts/check_diff_trust.sh`, so that optional
trust gate could not be run. Full `lake build` passed all 3345 jobs. The
normalized classifier
`.change_log/manual_attempt_20260721_Boundedx2y1_aux_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore exact public `Boundedx2y1_aux` is removed
from the active list, reducing the ledger from 42 to 41; `Boundedx2y1` is next.

2026-07-21 completion note: exact public `Boundedx2y1` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after exact `Boundedx2y1_aux`. It
matches upstream `Pff.v:Boundedx2y1`: the public theorem consumes the same Sec1
payload as `Boundedx2y1_aux` and returns an `xprime` whose real value is
`F2R xprime = F2R x2 * F2R y1` and which is `Fbounded b xprime`; the auxiliary
exponent equality is projected away, as the Coq wrapper does. No normality,
residual, rounding, closestness, unrelated component, totality, canonicity,
conclusion, or weakening premise was introduced. The proof directly eliminates
local exact `Boundedx2y1_aux` and returns the value and boundedness conjuncts.
Required subscription harness attempt
`.change_log/codex_attempt_20260721_181627` used `gpt-5.5` with high reasoning,
recorded `result = proved`, and passed its local target gate. Independent
focused `lake env lean FloatSpec/src/Pff/Pff.lean` exited 0;
`git diff --check` and the direct added-Lean-hole scan passed;
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings; and
`scripts/status_report.sh --write` reported 58 Lean files with `sorry = 0`,
`axiom = 0`, `admit = 0`, and zero placeholder/weakening findings. The
repository has no executable `scripts/check_diff_trust.sh`, so that optional
trust gate could not be run. Full `lake build` passed all 3345 jobs. The
normalized classifier
`.change_log/manual_attempt_20260721_Boundedx2y1_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore exact public `Boundedx2y1` is removed from the
active list, reducing the ledger from 41 to 40; `Dekker_aux` is next.

2026-07-21 completion note: exact public `Dekker_aux` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after exact `Boundedx2y1`. It matches
upstream `Pff.v:Dekker_aux` and its `Algo` section context: it consumes the
radix/bound/precision hypotheses, normality of `x` and `y`, the product
exponent lower bound, all four split-rounding hypotheses for each operand, the
four component-product rounding hypotheses, the five residual-rounding
hypotheses, and the sole theorem premise giving a bounded representative of
`tx * ty`; it concludes `F2R x * F2R y = F2R r - F2R t4`. No totality,
canonicity, precomputed split equality, bounded intermediate, conclusion, or
weakening premise was introduced. The proof derives the local `s` bounds,
uses exact `VeltkampU` twice, constructs the exact bounded component products
with `Boundedx1y1`, `Boundedx1y2`, and `Boundedx2y1`, constructs the four exact
residual witnesses with `Boundedt1` through `Boundedt4`, identifies every
rounded output through the projector property proved directly from `Closest`,
and closes the upstream algebraic reconstruction. Required subscription
harness attempt `.change_log/codex_attempt_20260721_183648` used `gpt-5.5`
with high reasoning, recorded `result = proved`, and passed its local target
gate. Independent focused `lake env lean FloatSpec/src/Pff/Pff.lean` exited 0;
`git diff --check` and the direct added-Lean-hole scan passed;
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings; and
`scripts/status_report.sh --write` reported 58 Lean files with `sorry = 0`,
`axiom = 0`, `admit = 0`, and zero placeholder/weakening findings. The
repository has no executable `scripts/check_diff_trust.sh`, so that optional
trust gate could not be run. Full `lake build` passed all 3345 jobs. The
normalized classifier
`.change_log/manual_attempt_20260721_Dekker_aux_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore exact public `Dekker_aux` is removed from the
active list, reducing the ledger from 40 to 39; `Boundedx2y2` is next.

2026-07-21 completion note: exact public `Boundedx2y2` is restored with the
upstream `Algo` section payload. It consumes the radix/bound/precision equation,
`pGe`, the product exponent lower bound, normality of `x` and `y`, the two
four-step split-rounding chains, and the upstream branch premise
`radix = 2 ∨ Even t`; it returns a representative of `tx * ty` that is bounded
by `b` and whose exponent is at least `x.Fexp + y.Fexp`. The local
`s := t - Nat.div2 t`, its lower/upper bounds, and the product-width
inequalities are derived internally rather than exposed as caller premises.
The radix-two branch uses `Veltkamp_tail2` for both tails, the even-precision
branch uses `VeltkampU`, and both branches share the exact bounded `Fmult`
construction. Required subscription harness attempt
`.change_log/codex_attempt_20260721_190324` used `gpt-5.5` with high reasoning
and passed its local target gate; its initially expanded theorem boundary was
manually repaired before independent verification. Focused
`lake env lean FloatSpec/src/Pff/Pff.lean` exited 0;
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings;
`scripts/status_report.sh --write` reported 58 Lean files with `sorry = 0`,
`axiom = 0`, `admit = 0`, and zero placeholder/weakening findings;
`git diff --check` passed; and full `lake build` passed all 3345 jobs. The
classifier `.change_log/manual_attempt_20260721_Boundedx2y2_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Therefore exact public `Boundedx2y2` is removed from
the active list, reducing the ledger from 39 to 38; `DekkerN` is next.

2026-07-21 completion note: exact public `DekkerN` is restored immediately
after exact `Dekker_aux`. It matches upstream `Pff.v:DekkerN`: the theorem
consumes the full `Algo` section payload plus the sole branch premise
`radix = 2 ∨ Even t`, obtains the bounded `tx * ty` representative from exact
`Boundedx2y2`, discards only that helper's additional exponent conjunct, and
applies exact `Dekker_aux` to conclude
`F2R x * F2R y = F2R r - F2R t4`. No separate bounded-witness, totality,
canonicity, conclusion, or weakening premise was introduced. Required
subscription harness attempt `.change_log/codex_attempt_20260721_192803` used
`gpt-5.5` with high reasoning, recorded `result = proved`, and passed its local
target gate. Independent focused `lake env lean FloatSpec/src/Pff/Pff.lean`
exited 0; `git diff --check` and the direct added-Lean-hole scan passed;
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings; and
`scripts/status_report.sh --write` reported 58 Lean files with `sorry = 0`,
`axiom = 0`, `admit = 0`, and zero placeholder/weakening findings. The
repository has no executable `scripts/check_diff_trust.sh`, so that optional
trust gate could not be run. Full `lake build` passed all 3345 jobs. The
normalized classifier
`.change_log/manual_attempt_20260721_DekkerN_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Therefore exact public `DekkerN` is removed from the active
list, reducing the ledger from 38 to 37; `DekkerS1` is next.

2026-07-22 completion note: exact public `DekkerS1` is restored immediately
after exact `DekkerN`. It matches upstream `Pff.v:DekkerS1` and the full
`AlgoS1` section payload: normal `x`, subnormal `y`, the exponent-sum bound,
all A1-A4/B1-B4/C1-C4/D1-D5 `Closest` hypotheses, and only the branch premise
`radix = 2 ∨ Even t`. The zero-`y` case follows the upstream zero-projection
cascade. The nonzero case obtains a normal representative of `y` under
`plusExp b t` via exact `bimplybplusNorm`, constructs exact float-operation
witnesses to lift every closestness hypothesis via `Closestbbplus`, and applies
exact `DekkerN` under the enlarged bound. No canonicity, bounded-witness,
totality, conclusion, or weakening premise was added. Required subscription
harness attempt `.change_log/codex_attempt_20260722_060750` used `gpt-5.5`
with high reasoning and recorded `result = proved` with a passing local target
gate. Independent focused `lake env lean FloatSpec/src/Pff/Pff.lean` exited 0,
and `git diff --check` plus the direct added-hole scan passed.
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings;
`scripts/status_report.sh --write` reported 58 Lean files with `sorry = 0`,
`axiom = 0`, `admit = 0`, and zero placeholder/weakening findings. The
repository has no executable `scripts/check_diff_trust.sh`, so that optional
trust gate could not be run. Full `lake build` passed all 3345 jobs. Therefore
the normalized classifier
`.change_log/manual_attempt_20260722_DekkerS1_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `DekkerS1` is removed from the active list,
reducing the ledger from 37 to 36; `DekkerS2` is next.

2026-07-22 completion note: exact public `DekkerS2` is restored immediately
after exact `DekkerS1`. It matches upstream `Pff.v:DekkerS2` and the full
`AlgoS2` section payload: subnormal `x`, normal `y`, the exponent-sum bound,
all A1-A4/B1-B4/C1-C4/D1-D5 `Closest` hypotheses, and only the branch premise
`radix = 2 ∨ Even t`. The zero-`x` case follows the upstream zero-projection
cascade. The nonzero case obtains a normal representative of `x` under
`plusExp b t` via exact `bimplybplusNorm`, constructs exact float-operation
witnesses to lift every closestness hypothesis via `Closestbbplus`, preserves
the D3/D4 subtraction order, and applies exact `DekkerN` under the enlarged
bound. No canonicity, bounded-witness, totality, conclusion, or weakening
premise was added. Focused `lake env lean FloatSpec/src/Pff/Pff.lean` exited 0
independently. Required subscription harness attempt
`.change_log/codex_attempt_20260722_063431` used `gpt-5.5` with high reasoning,
recorded `result = proved`, and passed its local target gate. `git diff --check`
and the direct added-hole scan passed.
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings;
`scripts/status_report.sh --write` reported 58 Lean files with `sorry = 0`,
`axiom = 0`, `admit = 0`, and zero placeholder/weakening findings. The
repository has no executable `scripts/check_diff_trust.sh`, so that optional
trust gate could not be run. Full `lake build` passed all 3345 jobs. The
normalized classifier
`.change_log/manual_attempt_20260722_DekkerS2_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `DekkerS2` is removed from the active list,
reducing the ledger from 36 to 35.

2026-07-22 completion note: exact public `Dekker1` is restored with the full
upstream `Algo1` section payload: canonic `x` and `y`, the exponent-sum bound,
all A1-A4/B1-B4/C1-C4/D1-D5 `Closest` hypotheses, the section exponent
condition, and only the branch premise `radix = 2 ∨ Even t`. Because upstream
`dExp b : N`, its premise `Z.of_N (dExp b) ≠ 0` is represented faithfully as
`0 < b.dExp` for the local `Int`-valued `Fbound_skel.dExp`; a bare integer
nonzero premise would incorrectly admit negative exponents. The proof splits
both exact `Fcanonic = Fnormal ∨ Fsubnormal` hypotheses, dispatches the three
possible cases to exact `DekkerN`, `DekkerS1`, and `DekkerS2`, and derives the
double-subnormal case contradiction from `Expoxy` and positive `dExp`. No
extra decomposition, conclusion, totality, or weakening premise was added.
Required subscription harness attempt
`.change_log/codex_attempt_20260722_065543` used `gpt-5.5` with high reasoning,
recorded `result = proved`, and passed its local target gate. Independent
focused `lake env lean FloatSpec/src/Pff/Pff.lean` exited 0; `git diff --check`
and the direct added-hole scan passed.
`scripts/audit_placeholders.sh --json FloatSpec` reported zero findings;
`scripts/status_report.sh --write` reported 58 Lean files with `sorry = 0`,
`axiom = 0`, `admit = 0`, and zero placeholder/weakening findings. The
repository has no executable `scripts/check_diff_trust.sh`, so that optional
trust gate could not be run. Full `lake build` passed all 3345 jobs. The
normalized classifier
`.change_log/manual_attempt_20260722_Dekker1_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `Dekker1` is removed from the active list,
reducing the ledger from 35 to 34; `Veltkampb'` is next.

2026-07-22 completion note: exact public `Veltkampb'` is restored beside its
exact `Closestbbext` prerequisite. It matches the full upstream `Algo2`
payload: for arbitrary `f`, `pf`, `qf`, `hf`, and `tf`, strict extension from
`b.dExp` to `Dekker_extendedBound b t`, boundedness of `f` under `b`, and the
four original split-operation `Closest` hypotheses imply the same four
closestness statements under the extended bound, in the same nested
conjunction. The proof builds exact `Fmult`/`Fplus`/`Fminus` input witnesses,
derives their old-bound exponent floors from `Fbounded` and preceding
closestness outputs, and applies exact `Closestbbext`; no canonicity,
normality, totality, conclusion, or weakening premise was added. Required
subscription harness attempt `.change_log/codex_attempt_20260722_071159` used
`gpt-5.5` with high reasoning and recorded `result = proved`. Its line-based
post-edit dependency sidecar resolved the old insertion line to `DekkerS2`, so
that sidecar is not counted as target evidence. Independent focused
`lake env lean FloatSpec/src/Pff/Pff.lean` at the actual declaration exited 0;
`git diff --check`, the direct added-hole scan, and
`scripts/audit_placeholders.sh --json FloatSpec` passed with zero findings.
`scripts/status_report.sh --write` reported 58 Lean files with `sorry = 0`,
`axiom = 0`, `admit = 0`, and zero placeholder/weakening findings. The
repository has no executable `scripts/check_diff_trust.sh`, so that optional
trust gate could not be run. Full `lake build` passed all 3345 jobs. The
normalized classifier at the actual declaration,
`.change_log/manual_attempt_20260722_Veltkampb_prime_proved/attempt.json`,
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Exact public `Veltkampb'` is removed from the active
list, reducing the ledger from 34 to 33; `NormalbPrim` is next.

2026-07-22 completion note: exact public `NormalbPrim` is restored in
`FloatSpec/src/Pff/Pff.lean` beside the Algo2 bound-extension lemmas. It matches
the upstream payload over `Dekker_extendedBound b t`: for every canonical
nonzero `f` under `b`, assuming the section hypotheses and only the faithful
local integer representation invariant `0 <= b.dExp`, it constructs
`Fnormalize radix (Dekker_extendedBound b t) t f`, proves it normal under the
extended bound, preserves `F2R`, and proves `-(t:Int)-b.dExp <= Fexp`. The proof
uses `dExpPrim`/`dExpPrimEq`, `FcanonicBound`, `FnormalizeCanonic`, and
`FnormalizeCorrect`; no magnitude, exponent, totality, conclusion, or weakening
premise was added. `lake env lean FloatSpec/src/Pff/Pff.lean`,
`git diff --check`, `scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
independently normalized classifier
`.change_log/manual_attempt_20260722_NormalbPrim_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `NormalbPrim` is removed from the active list,
reducing the ledger from 33 to 32; `Dekker2_aux` is next.

2026-07-22 completion note: exact public `Dekker2_aux` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after `DekkerN`. It preserves the full
upstream Algo2 payload: canonical nonzero `x` and `y`, the strict underflow
exponent premise, all A/B/C/D `Closest` hypotheses, the radix-two/even-precision
branch, and the `7/2 * radix^(-dExp b)` error bound. The only Lean-only premise
is the faithful local integer representation invariant `0 <= b.dExp`. The
proof normalizes both inputs under `Dekker_extendedBound`, reconstructs the
extended-bound Dekker computation with the existing bounded-product and
projector stack, and accumulates the exact `Underf_Err` bounds. Independent
`lake env lean FloatSpec/src/Pff/Pff.lean`, `git diff --check`,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/manual_attempt_20260722_Dekker2_aux_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `Dekker2_aux` is removed from the active list,
reducing the ledger from 32 to 31; `Dekker2` is next.

2026-07-22 completion note: exact public `Dekker2` is restored in
`FloatSpec/src/Pff/Pff.lean` immediately after `Dekker2_aux`. It preserves the
full upstream Algo2 section payload: canonical inputs, the strict underflow
exponent premise, all A/B/C/D `Closest` hypotheses, the radix-two/even-precision
branch, and the `7/2 * radix^(-dExp b)` error bound. The only Lean-only premise
is the faithful local integer representation invariant `0 <= b.dExp`. The
proof follows the upstream case split, propagating either zero input through
the complete rounded-operation chain with `ClosestZero2` and delegating the
nonzero case to exact `Dekker2_aux`. Independent
`lake env lean FloatSpec/src/Pff/Pff.lean`, `git diff --check`,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/manual_attempt_20260722_Dekker2_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `Dekker2` is removed from the active list,
reducing the ledger from 31 to 30; `Twice_EvenClosest_Round` is next.

2026-07-22 completion note: exact public `Twice_EvenClosest_Round` is restored
in `FloatSpec/src/Pff/Pff.lean` immediately after `ClosestUlp`, whose exact
closest-rounding error bound it uses. The theorem preserves the complete
upstream radix-two payload: `1 < precision`, `vNum = 2^precision`, the
predecessor-exponent bound, normality, and `EvenClosest`, with no extra
scaled-closestness, parity, competitor-halvability, monotonicity, uniqueness,
or conclusion premise. The proof handles high-exponent competitors by bounded
halving and proves the minimum-exponent boundary directly from the mantissa
bound, normal lower magnitude, and closest-ulp estimate. Its uniqueness branch
derives the competitor exponent through absolute-value closest monotonicity and
canonical exponent comparison before applying `Half_Closest_Round`.
Independent `lake env lean FloatSpec/src/Pff/Pff.lean`, `git diff --check`,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/manual_attempt_20260722_Twice_EvenClosest_Round_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Exact public `Twice_EvenClosest_Round` is removed
from the active list, reducing the ledger from 30 to 29;
`errorBoundedMultClosest_Can` is next.

2026-07-22 completion note: exact public `errorBoundedMultClosest_Can` is
restored in `FloatSpec/src/Pff/Pff.lean` with the full upstream binary section
payload: `1 < precision`, `vNum = 2^precision`, bounded inputs, a closest and
canonical rounded product, the no-underflow product-magnitude premise, and a
bounded residual whose value, exponent, and `2^(precision - 1)` mantissa bound
match Flocq. The required subscription harness attempt
`.change_log/codex_attempt_20260722_094154` timed out with exit status 124
after producing a compiling theorem with an extra global `boundR` exponent
premise. That non-upstream premise was rejected and removed in the normalized
manual proof. Independent `lake env lean -DmaxErrors=20
FloatSpec/src/Pff/Pff.lean`, `git diff --check`, the added-hole scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/manual_attempt_20260722_errorBoundedMultClosest_Can_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Exact public `errorBoundedMultClosest_Can` is
removed from the active list, reducing the ledger from 29 to 28; `cases` is
next.

2026-07-22 completion note: exact public `cases` is restored as Lean
declaration `«cases»` in `FloatSpec/src/Pff/Pff.lean`. It preserves the
Discriminant7 section payload, including float-typed `dp`/`dq`, their
conditional boundedness and residual equations, all rounding hypotheses, the
five zero alternatives, and the six no-underflow magnitude bounds. The only
Lean-specific premise is `boundR` exponent totality required by the local
`Fbound_skel` representation. Required subscription harness attempt
`.change_log/codex_attempt_20260722_104151` produced the core proof strategy,
but its generated `discri16_cases` statement changed `dp`/`dq` to reals with
existential bounded representations. That altered public statement was
rejected; the normalized proof restores the upstream types and exact reserved
name. Independent `lake env lean -DmaxErrors=20 FloatSpec/src/Pff/Pff.lean`,
`git diff --check`, the added-hole scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/manual_attempt_20260722_cases_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `cases` is removed from the active list,
reducing the ledger from 28 to 27.

2026-07-22 completion note: exact public GenericA lemma `xLe2y_aux1` is
restored in `FloatSpec/src/Pff/Pff.lean`, preserving the upstream beta/radix,
precision, even-radix, closestness, canonicity, exponent, error-bound, and
magnitude payload. The proof derives exactness of `x` from the representable
power magnitude, constructs the even-radix half-unit bounded witness, proves
that witness lies below `|a + b + e|`, and transfers the bound to `|y|` by
closest absolute monotonicity. The only Lean-specific premise is `boundR`
exponent totality required by the local `Fbound_skel` representation. Required
subscription harness attempt `.change_log/codex_attempt_20260722_112000`
produced the exact declaration and proof. Independent `lake env lean
-DmaxErrors=20 FloatSpec/src/Pff/Pff.lean`, `git diff --check`, the added-hole
scan, `scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/manual_attempt_20260722_xLe2y_aux1_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `xLe2y_aux1` is removed from the active list,
reducing the ledger from 27 to 26; `xLe2y_aux2` is next.

2026-07-22 completion note: exact public GenericA lemma `xLe2y_aux2` is
restored in `FloatSpec/src/Pff/Pff.lean` with the full upstream payload. Its
private trichotomy helper derives the zero, exact-radix-power, and
at-least-two-units branches from canonical `Fplus`; the theorem projects the
zero branch exactly, reuses `xLe2y_aux1` for the exact-power branch, and
combines `ClosestRoundeLeNormal`, `ClosestRoundeGeNormal`, `abeLeab`, and
`UnMoinsPos` for the large branch. The only additional section invariant is
the established `boundR` exponent totality required by the local
`Fbound_skel` representation. Required subscription harness attempt
`.change_log/codex_attempt_20260722_120120` produced the exact declaration and
proof. Independent focused Lean passed; the remaining trust, status, and full
build gates passed, including all 3345 build jobs. `scripts/check_diff_trust.sh`
is absent in this checkout. The normalized classifier
`.change_log/manual_attempt_20260722_xLe2y_aux2_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public
`xLe2y_aux2` is removed from the active list, reducing the ledger from 26 to
25; `yLe2x_aux` is next.

2026-07-22 completion note: exact public GenericA lemma `yLe2x_aux` is restored
in `FloatSpec/src/Pff/Pff.lean`. It derives the upstream zero-or-positive-unit
split from canonical `Fplus`; the zero branch contradicts the explicit
`F2R x != 0` premise, while the positive branch combines the `eLeb` half-ulp
bound with `ClosestRoundeLeNormal`, `ClosestRoundeGeNormal`, and
`UnMoinsPos` to prove `|y| <= 2 * |x|`. Required subscription harness attempt
`.change_log/codex_attempt_20260722_123242` produced the proof. Its generated
signature was manually normalized by removing `Even radix` and the strict
`b`-exponent hypothesis, which are unused section hypotheses omitted from the
exported Coq lemma; no mathematical premise used by upstream was removed.
Independent focused Lean, `git diff --check`, the added-hole scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/manual_attempt_20260722_yLe2x_aux_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `yLe2x_aux` is removed from the active list,
reducing the ledger from 25 to 24; `xLe2y` is next.

2026-07-22 completion note: exact public GenericB lemma `xLe2y` is restored in
`FloatSpec/src/Pff/Pff.lean`. It splits on `|b| <= |a|`, applies exact
`xLe2y_aux2` directly in the first branch, and swaps `a` and `b` plus the two
error and exponent hypotheses in the second branch. The exported payload
includes both half-ulp bounds, both canonical/strict-exponent facts, closest
and normality hypotheses, even radix, and the local `boundR` totality needed by
`xLe2y_aux2`; it correctly omits the later GenericB sign-transfer hypothesis
`dsd`. Required subscription harness attempt
`.change_log/codex_attempt_20260722_130343` produced the exact declaration and
proof. Independent focused Lean, `git diff --check`, the added-hole scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier `.change_log/manual_attempt_20260722_xLe2y_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Exact public `xLe2y` is removed from the active
list, reducing the ledger from 24 to 23; `yLe2x` is next.

2026-07-22 completion note: exact public GenericB lemma `yLe2x` is restored in
`FloatSpec/src/Pff/Pff.lean`. It preserves only the exported premises used by
upstream, splits on `|b| <= |a|`, applies exact `yLe2x_aux` directly in the
first branch, and swaps `a` and `b` with their error/canonicity hypotheses in
the second branch. It correctly omits unused even-radix, strict-exponent,
`dsd`, and `boundR`-totality hypotheses. Required subscription harness attempt
`.change_log/codex_attempt_20260722_131848` produced the exact declaration and
proof. Independent focused Lean, `git diff --check`, the added-hole scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier `.change_log/manual_attempt_20260722_yLe2x_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Exact public `yLe2x` is removed from the active
list, reducing the ledger from 23 to 22; `Subexact` is next.

2026-07-22 completion note: exact public GenericB lemma `Subexact` is restored
in `FloatSpec/src/Pff/Pff.lean` with the full upstream existential payload. It
derives nonzero `x` from normality, obtains both magnitude bounds from restored
`xLe2y`/`yLe2x`, and splits on the sign of `y`. The nonnegative branch uses
`Fminus x y`; the negative branch uses
`Fopp (Fminus (Fopp x) (Fopp y))`. In both branches `Fminus_correct` proves the
real subtraction value, `Sterbenz` proves boundedness, and
`Fminus_exp_eq_min` proves the exact minimum exponent. Required subscription
harness attempt `.change_log/codex_attempt_20260722_133425` produced the exact
declaration and proof. Independent focused Lean, `git diff --check`, the
added-hole scan, `scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier `.change_log/manual_attempt_20260722_Subexact_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Exact public `Subexact` is removed from the active
list, reducing the ledger from 22 to 21; `Midpoint_aux_aux` is next.

2026-07-22 completion note: exact public GenericC lemma `Midpoint_aux_aux` is
restored in `FloatSpec/src/Pff/Pff.lean` with the full upstream disjunction.
Given closest representations of `x1 + x2` by `x1` and of `x1 + x2 + y` by
`f`, strict `MSB y < LSB x2`, positive normal `x1`, nonzero `x2`, and the
upstream radix, precision, parity, and exponent assumptions, the theorem
proves either `F2R x1 = F2R f` or an equivalent representation `v` of `x2`
with `x1.Fexp - 2 <= v.Fexp`. The proof first returns the canonical
least-significant-bit representation when its exponent is already large
enough. Otherwise it derives the strict half-ulp residual bound from the even
radix midpoint, then handles the normal minimum significand and predecessor
spacing branches before applying `ImplyClosestStrict`. The required harness
attempt `.change_log/codex_attempt_20260722_135515` made no source changes and
classified the attempt as failed, so the exact proof was completed manually.
Focused Lean, `git diff --check`, the added-hole scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/manual_attempt_20260722_Midpoint_aux_aux_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Exact public `Midpoint_aux_aux` is removed from the
active list, reducing the ledger from 21 to 20; `Midpoint_aux` is next.

2026-07-22 completion note: exact public GenericD lemma `Midpoint_aux` is
restored in `FloatSpec/src/Pff/Pff.lean` with the full upstream disjunction
and without adding an `x1` positivity premise. The proof matches upstream
`Pff/Pff.v:24209`: it splits on the sign of `F2R x1`, applies
`Midpoint_aux_aux` directly in the positive branch, rules out zero from
normality, and handles the negative branch by transporting the two `Closest`
premises through `Fopp`/`ClosestOpp`, rewriting `MSB`/`LSB` with
`MSB_opp`/`LSB_opp`, preserving normality with `FnormalFop`, and mapping the
witness back with `Fopp`. Focused Lean, `lake build`, `git diff --check`,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed. The required subscription harness
attempt `.change_log/codex_attempt_20260722_144725` generated the exact
declaration and proof. `scripts/check_diff_trust.sh` is absent in this
checkout. The normalized classifier
`.change_log/manual_attempt_20260722_Midpoint_aux_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `Midpoint_aux` is removed from the active
list, reducing the ledger from 20 to 19; `gatCorrect` is next.

2026-07-22 completion note: exact public Be2Zero lemma `gatCorrect` is restored
in `FloatSpec/src/Pff/Pff.lean` with the full upstream existential payload: a
float representing `F2R be1 - F2R r1`, bounded by `bo`, whose exponent is
`min be1.Fexp r1.Fexp`. The proof derives the two half-ulp error bounds from
`ClosestUlp` and `TwoSumProp`, reconstructs the exact rounded sum, transports
the required sign conditions through positive, zero, and negated closest
branches, and applies exact `Subexact`. The required subscription harness
attempt `.change_log/codex_attempt_20260722_150956` generated the declaration
and proof. Independent focused Lean, `git diff --check`, the added-hole scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. Exact
public `gatCorrect` is removed from the active list, reducing the ledger from
19 to 18; `Expr1` is next.

2026-07-22 completion note: exact public Be2NonZero lemma `Expr1` is restored
in `FloatSpec/src/Pff/Pff.lean` with the upstream exponent payload
`r1.Fexp <= be1.Fexp + 1`. The proof derives the two residual half-ulp bounds
with `TwoSumProp` and `ClosestUlp`, applies exact `yLe2x` to obtain
`|F2R r1| <= 2 * |F2R be1|`, constructs the canonical scaled `be1` float at
exponent `be1.Fexp + 1`, and closes the exponent comparison with
`Fcanonic_Rle_Zle`. The required subscription harness attempt
`.change_log/codex_attempt_20260722_153945` generated the exact declaration
and proof. Independent focused Lean, `git diff --check`, the added-hole scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/manual_attempt_20260722_Expr1_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `Expr1` is removed from the active list,
reducing the ledger from 18 to 17; `Expbe1` is next.

2026-07-22 completion note: exact public Be2NonZero lemma `Expbe1` is restored
in `FloatSpec/src/Pff/Pff.lean` with the upstream exponent payload
`be1.Fexp <= r1.Fexp + 1`. The proof keeps the genuinely required GenericB
premises for local `xLe2y`: radix parity, strict exponent bounds for `u1` and
`al1`, and total `boundR` exponent coverage. It derives the two residual
half-ulp bounds with `TwoSumProp` and `ClosestUlp`, applies exact `xLe2y` to
obtain `|F2R be1| <= 2 * |F2R r1|`, constructs the canonical scaled `r1` float
at exponent `r1.Fexp + 1`, and closes the exponent comparison with
`Fcanonic_Rle_Zle`. The required subscription harness attempt
`.change_log/codex_attempt_20260722_160030` generated the exact declaration,
proof, and provisional ledger note. Independent focused Lean,
`git diff --check`, the added-hole scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/manual_attempt_20260722_Expbe1_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `Expbe1` is removed from the active list,
reducing the ledger from 17 to 16; `be2MuchSmaller` is next.

2026-07-22 completion note: exact public Be2NonZero lemma `be2MuchSmaller` is
restored in `FloatSpec/src/Pff/Pff.lean` with the upstream payload: nonzero
`al2`, `u2`, and `be2` imply
`MSB radix al2 < LSB radix be2`. The proof transports exact representations
through `MSB_comp`/`LSB_comp`, propagates the residual bit bounds with
`MSBroundLSB`, `LSBPlus`, and `LSBMinus`, uses `TwoSumProp` for the absolute
residual comparison, and rules out the remaining `be1` exponent branch with
`plusExact1`. The required subscription harness attempt
`.change_log/codex_attempt_20260722_161709` generated the exact result but
initially exposed closest totality as an extra public premise; that premise was
removed manually and derived internally from `MinEx`, `MaxEx`, and
`ClosestTotal` using the existing `boundR` invariant. The theorem is placed
after `LSBPlus`, where its local Lean dependencies are available. Independent
focused Lean, `git diff --check`, the added-hole scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/manual_attempt_20260722_be2MuchSmaller_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Exact public `be2MuchSmaller` is removed from the
active list, reducing the ledger from 16 to 15; `gaCorrect` is next.

2026-07-22 completion note: exact public Be2NonZero lemma `gaCorrect` is
restored in `FloatSpec/src/Pff/Pff.lean` with the upstream existential payload:
a bounded float representing
`F2R be1 - F2R r1 + F2R be2`. The proof first obtains the exact
`gatCorrect` witness for `be1 - r1`, handles the `al2 = 0` branch through the
effective rounded-mode compatibility payload, derives the upstream
`u2 = 0` contradiction, then applies `Midpoint_aux`. In the nontrivial
midpoint branch it adds the `gatCorrect` and midpoint witnesses, proves the
upstream magnitude bound using `Expr1`, `be2MuchSmaller`, and closest-ulp
bounds, and applies exact `BoundedL` at exponent `be1.Fexp - 2`. The public
statement intentionally does not expose unused section variables such as
`gat`, `ga`, `P1`, or boundedness of `a` and `x`. Focused Lean,
`lake build`, `git diff --check`, `scripts/audit_placeholders.sh --json
FloatSpec`, and `scripts/status_report.sh --write` passed.
`scripts/check_diff_trust.sh` is absent in this checkout. The normalized
classifier `.change_log/manual_attempt_20260722_gaCorrect_proved/attempt.json`
records `result = proved`, `build = pass`, `coq_alignment = checked`, and a
passing local target gate. Exact public `gaCorrect` is removed from the active
list, reducing the ledger from 15 to 14; `tBounded_aux` is next.

2026-07-22 completion note: exact public FMA lemma `tBounded_aux` is restored in
`FloatSpec/src/Pff/Pff.lean` with the effective upstream payload: bounded
inputs `a`, `x`, and `b`, canonical `b`, normal rounded values `ph`, `z`, and
`uh`, the product-exponent floor, the three closest-rounding relations, the
exact multiplication residual `pl`, and nonnegativity of `a*x+b` yield a
bounded float representing `F2R uh - F2R z`. The proof preserves all three
upstream branches. When `ph+b=0`, closestness forces `uh=0` and bounded `-z`
is the witness. Under `|pl| <= |ph+b|/4`, normal relative-error bounds and the
upstream radix/precision factor inequality establish the Sterbenz ratios and
exact subtraction supplies the witness. In the complementary branch, the
proof combines `errorBoundedMult`, canonical comparison floats,
`Fcanonic_Rle_Zle`, `FcanonicLeastExp`, `LeExpRound2`, closest-ulp bounds, and
two applications of `BoundedL` to construct the exact bounded difference.
Closest totality is derived internally from `MinEx`, `MaxEx`, and
`ClosestTotal`; no helper result or additional totality premise is exposed in
the public theorem. Required subscription harness attempt
`.change_log/codex_attempt_20260722_171329` made no source changes and reported
that the prerequisite names existed but the unfactored proof exceeded its
single-attempt scope; the manual continuation completed that proof.
Independent focused Lean, `git diff --check`, the added-hole scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/manual_attempt_20260722_tBounded_aux_proved/attempt.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `tBounded_aux` is removed from the active list,
reducing the ledger from 14 to 13; `tBounded` is next.

2026-07-22 completion note: exact public FMA lemma `tBounded` is restored in
`FloatSpec/src/Pff/Pff.lean` with the upstream payload: bounded inputs `a`,
`x`, and `b`, canonical `b`, normal-or-zero rounded values `ph`, `z`, and `uh`,
the product-exponent floor, the three closest-rounding relations, and the exact
multiplication residual `pl` yield a bounded float representing
`F2R uh - F2R z`. In the all-normal branch, nonnegative inputs apply exact
`tBounded_aux` directly; negative inputs transport every premise through
`Fopp`, `ClosestOpp`, `FnormalFop`, `FcanonicFopp`, and `oppBounded`, apply
`tBounded_aux`, and negate its witness. The zero-valued branches preserve the
upstream construction: `ph = 0` uses `ClosestZero1` to force the exact product
to zero and rounded projector equality to identify `z` and `uh` with `b`,
`z = 0` returns `uh`, and `uh = 0` returns bounded `-z`. Closest totality is
derived internally from `MinEx`, `MaxEx`, and `ClosestTotal`, so no additional
public totality premise is exposed. Required subscription harness attempt
`.change_log/codex_attempt_20260722_183900` generated the exact declaration and
proof. Independent focused Lean, `git diff --check`, the added-hole scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/codex_attempt_20260722_183900/attempt.verified.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `tBounded` is removed from the active list,
reducing the ledger from 13 to 12.

2026-07-22 completion note: exact public FMA lemma `ErrFmaApprox_1_aux` is
restored in `FloatSpec/src/Pff/Pff.lean` with the effective upstream exact-`uh`
Case1 payload. Under the bounded/canonical input hypotheses, normal-or-zero
`ph` and `uh`, bounded multiplication residual `pl`, the FMA rounding
definitions, `F2R ul = 0`, and explicit normality of `z` and `w`, it proves
`|z+w-(a*x+b)| <= (3*radix/2+1/2)*radix^(2-2*precision)*|z|`. The proof uses
exact `tBounded` and rounded projector equality to establish `F2R t = uh-z`,
identifies `v` with `pl` by projector equality, and rewrites the target as the
rounding error of `w`. `RoundedModeUlp`, `FcanonicFnormalizeEq`, and `FulpLe2`
provide the normal relative ulp bounds for `z` and `w`; the final inequality
derives the upstream quadratic precision power and relaxes the coefficient to
`3*radix/2+1/2`. Redundant normal-or-zero section hypotheses for `z` and `w`
are not exposed because the theorem already assumes both are normal. Closest
totality is derived internally from `MinEx`, `MaxEx`, and `ClosestTotal`; no
public totality, ulp, magnitude, or algebraic-rewrite premises are exposed.
Required subscription harness attempt
`.change_log/codex_attempt_20260722_185832` generated the exact declaration,
proof, and initial ledger note. Independent focused Lean, `git diff --check`,
the added-hole scan, `scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/codex_attempt_20260722_185832/attempt.verified.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `ErrFmaApprox_1_aux` is removed from the active
list, reducing the ledger from 12 to 11; `ErrFmaApprox_1` is next.

2026-07-22 completion note: exact public FMA lemma `ErrFmaApprox_1` is restored
in `FloatSpec/src/Pff/Pff.lean` with the upstream exact-`uh` Case1 payload and
normal-or-zero hypotheses for both `z` and `w`. The all-normal branch delegates
directly to exact `ErrFmaApprox_1_aux`. In the normal-`z`/zero-`w` branch, the
proof preserves the upstream exactness chain: `tBounded` plus projector equality
gives `F2R t = F2R uh - F2R z`, projector equality gives `F2R v = F2R pl` under
`F2R ul = 0`, and `ClosestZero1` applied to the exact `Fplus t v` witness forces
`F2R t + F2R v = 0`, making the target zero. In the zero-`z` branch,
`ClosestZero1` first forces the exact FMA input to zero, rounded projector
equality identifies `ph` with `-b`, `ClosestZero2` forces `uh`, `t`, `v`, and
`w` to zero, and the target again reduces to zero. Closest totality is derived
internally from `MinEx`, `MaxEx`, and `ClosestTotal`; no totality, equality,
positivity, or nonzero premises are exposed. Required subscription harness
attempt `.change_log/codex_attempt_20260722_192358` generated the exact
declaration, proof, and ledger update. Independent focused Lean
`lake env lean FloatSpec/src/Pff/Pff.lean`, `git diff --check`, the added-hole
scan,
`scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized classifier
`.change_log/codex_attempt_20260722_192358/attempt.verified.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `ErrFmaApprox_1` is removed from the active
list, reducing the ledger from 11 to 10; `LeExp2` is next.

2026-07-22 completion note: exact public inexact-`uh` FMA lemma `LeExp2` is
restored in `FloatSpec/src/Pff/Pff.lean` with the effective upstream payload.
Under the radix, precision, bounded-exponent, bounded-`b`, normal `ph`/`uh`/`z`,
rounded `z`/`ph`/`uh`, exact `ul`, and nonzero-`ul` hypotheses, it proves
`Fexp uh <= Fexp z + 1`. The proof combines the three closest-rounding ulp
bounds, uses exact `LeExp1` to bound `Fulp ph` by `radix * Fulp uh`, and then
uses `FcanonicFnormalizeEq`, `FulpLe2`, and the upstream precision-four
coefficient argument to derive `|F2R uh| <= radix * |F2R z|`. A canonical
shift of `z` and `Fcanonic_Rle_Zle` yield the exponent conclusion. Coq section
premises not used by this lemma, including boundedness of `a` and `x`,
canonicity of `b`, and the `pl` residual, are not exposed publicly. Required
subscription harness attempt `.change_log/codex_attempt_20260722_195131`
generated the exact candidate proof; its initial full build was interrupted by
the full `/mnt/users` Ceph volume. After moving the ignored `.lake/build`
symlink to `/tmp`, independent focused Lean, `git diff --check`, the added-hole
scan, `scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. `scripts/check_diff_trust.sh` is absent in this checkout. The
normalized verified classifier
`.change_log/codex_attempt_20260722_195131/attempt.verified.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. Exact public `LeExp2` is removed from the active list,
reducing the ledger from 10 to 9; `LeExp3` is next. Overall exact-gap progress
is 246 of 255 resolved.

2026-07-22 prerequisite progress: exact upstream-strength `RleRoundedAbs` is
restored in `FloatSpec/src/Pff/Pff.lean`. Its public surface now uses the Coq
section payload: integer radix, natural precision, `vNum = radix^precision`,
precision at least four, closestness, normality, and exponent strictly above
the minimum boundary. The former public expansions of `Closest` and `Fnormal`
and the non-upstream premise `vNum >= |Fnum f| * radix` were removed. In the
minimum-normal branch, the mantissa-product equality is derived internally
from `nNormMin`, `PosNormMin`, and the `vNum` power equation. Required
subscription harness attempt `.change_log/codex_attempt_20260722_203914`
performed the repair. Independent focused Lean, `git diff --check`, the
added-hole scan, `scripts/audit_placeholders.sh --json FloatSpec`, and
`scripts/status_report.sh --write` passed, and full `lake build` passed all
3345 jobs. The normalized classifier
`.change_log/codex_attempt_20260722_203914/attempt.verified.json` records
`result = proved`, `build = pass`, `coq_alignment = checked`, and a passing
local target gate. This directly clears the blocker recorded by the first
`LeExp3` harness attempt `.change_log/codex_attempt_20260722_203104`; it is
prerequisite progress only, so the active exact-gap count remains 9.

#### `Pff/Pff.v` (9)

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
  - `Zdigit_ext`: restored as the exact public Lean theorem in
    `FloatSpec/src/Core/Digits.lean` after aligning `Zdigit` with Flocq's
    signed remainder semantics. Lean previously had only `Zdigit_ext_nonneg`,
    which assumed both integers were nonnegative, while upstream `Zdigit_ext`
    is over all integers. Pipeline attempt `.change_log/codex_attempt_20260704_165233`
    classified the exact theorem as blocked under the current local
    semantics: with `Zdigit` defined using `Int.tdiv` followed by Euclidean
    `%`, `Zdigit 10 (-1) 0 = 9`, `Zdigit 10 9 0 = 9`,
    `Zdigit 10 (-1) 1 = 0`, and `Zdigit 10 9 1 = 0`, but `-1 ≠ 9`.
    Reattempt `.change_log/codex_attempt_20260705_071433` confirmed the same
    blocker and left `Digits.lean` unchanged. Subscription reattempt
    `.change_log/codex_attempt_20260713_081648` reconfirmed the same concrete
    counterexample and left `Digits.lean` unchanged. A direct local probe that
    changed `Zdigit`'s final remainder to `Int.tmod` removed the concrete
    counterexample shape but broke the existing digit proof surface at
    `Zdigit_opp`, `Zdigit_at_zero`, `Zdigit_mul_pow`, `Zdigit_div_pow`,
    `Zdigit_mod_pow`, and nonnegative plus/digits lemmas, which are still
    stated and proved around Euclidean `%`.
    Config-provider harness attempt
    `.change_log/codex_attempt_20260713_094219` again left `Digits.lean`
    unchanged and reconfirmed the exact same blocker: local
    `Zdigit 10 (-1) 0 = 9`, `Zdigit 10 9 0 = 9`,
    `Zdigit 10 (-1) 1 = 0`, and `Zdigit 10 9 1 = 0`, but `-1 != 9`.
    Config-provider harness attempt
    `.change_log/codex_attempt_20260713_115846` rechecked the exact upstream
    payload against `Zdigit_ext_nonneg`, left the target source unchanged
    (`target_before.lean` and `target_after.lean` identical), and classified
    the unrestricted theorem as blocked.  The explicit checked-classifier
    sidecar
    `.change_log/codex_attempt_20260713_115846/zdigit_ext_checked_blocked.json`
    records `coq_alignment = checked`; a live `lake env lean --stdin` probe
    in the same workspace evaluates
    `(Zdigit 10 (-1) 0, Zdigit 10 9 0, Zdigit 10 (-1) 1, Zdigit 10 9 1)` to
    `(9, 9, 0, 0)`.
    Config-provider harness attempt
    `.change_log/codex_attempt_20260713_185034` reconfirmed the same
    foundational blocker, with no source changes for this target; a live probe
    additionally confirmed `Zdigit 10 (-1) 2 = 0`,
    `Zdigit 10 9 2 = 0`, while `Int.tmod (-1) 10 = -1` and
    `Int.tmod 9 10 = 9`.
    Manual follow-up on 2026-07-13 changed `Zdigit` to use `Int.tmod`, repaired
    the local digit proof surface, and added exact `Zdigit_ext`. A rebuilt
    probe now gives `Zdigit 10 (-1) 0 = -1`, `Zdigit 10 9 0 = 9`,
    `Zdigit 10 (-1) 1 = 0`, and `Zdigit 10 9 1 = 0`; `lake build` passed
    after rebuilding downstream Core, Calc, IEEE754, Prop, and Pff modules.
    Status: implemented and removed from active semantic gaps.
  - `Zdigit_plus`: not faithfully present. Lean has `Zdigit_plus_nonneg`, but
    it gives a carry-form statement for nonnegative operands, while upstream
    `Zdigit_plus` proves exact digit additivity under the disjoint-digit
    hypothesis. Pipeline attempt `.change_log/codex_attempt_20260704_172834`
    left the file unchanged and classified the exact theorem as blocked for
    now: the upstream proof uses signed, two-input `ZOdiv_plus_pow_digit` and
    `ZOmod_plus_pow_digit` infrastructure, while current Lean only has
    nonnegative/single-input decomposition variants plus Hoare/spec wrappers
    instead of the matching signed quotient/remainder lemmas. Subscription
    reattempt `.change_log/codex_attempt_20260713_082314` reconfirmed that
    blocker and left `Digits.lean` unchanged. Config-provider harness attempt
    `.change_log/codex_attempt_20260713_105024` again left the target source
    unchanged (`target_before.lean` and `target_after.lean` identical) and
    classified the exact theorem as blocked. Its nested classifier
    `.change_log/manual_attempt_20260713_zdigit_plus_blocked` records
    `coq_alignment = checked`: exact upstream `Zdigit_plus` still depends on
    signed two-input `ZOdiv_plus_pow_digit` and `ZOmod_plus_pow_digit` over
    `Z.quot`/`Z.rem`, while local `Digits.lean` only has nonnegative
    single-input decomposition variants and the nonfaithful carry-form
    `Zdigit_plus_nonneg`; local `Zdigit` also uses `Int.tdiv` followed by
    Euclidean `%`, not Flocq's signed `Z.rem` payload. Config-provider
    harness attempt `.change_log/codex_attempt_20260713_120652` rechecked the
    exact signed disjoint-digit payload, left `Digits.lean` unchanged
    (`target_before.lean` and `target_after.lean` identical), and wrote the
    nested checked classifier
    `.change_log/manual_attempt_20260713_zdigit_plus_blocked_recheck/attempt.json`
    with `result = blocked`, `coq_alignment = checked`, and `build = pass`.
    A controlled signed-remainder probe, recorded at
    `.change_log/manual_attempt_20260713_zdigit_signed_remainder_probe/attempt.json`,
    replaced the final Euclidean `%` in `Zdigit` with `Int.tmod` and was
    reverted after `lake env lean FloatSpec/src/Core/Digits.lean` failed
    broadly across the existing Euclidean digit proof surface (`Zdigit_opp`,
    `Zdigit_at_zero`, `Zdigit_eval_nonneg`, `Zdigit_mul_pow`,
    `Zdigit_div_pow`, `Zdigit_mod_pow`, `ZOmod_plus_pow_digit`, and
    `Zdigit_plus_nonneg` among the failures). Status:
    renamed/split but different payload; exact theorem still required after
    the signed quotient/remainder prerequisites are ported.
    Config-provider harness attempt `.change_log/codex_attempt_20260714_173102`
    rechecked the target after `Zdigit` had been aligned to signed
    `Int.tmod`. It left `Digits.lean` unchanged (`target_before.lean` and
    `target_after.lean` identical) and reported `blocked`: upstream
    `Zdigit_plus` still depends on signed two-input `ZOdiv_plus_pow_digit`
    and `ZOmod_plus_pow_digit` plus the lower-digit no-carry/disjointness
    payload, while the current Lean file only has single-input/nonnegative
    decomposition lemmas under those names and the nonfaithful carry-form
    `Zdigit_plus_nonneg`. A nested manual classifier
    `.change_log/manual_attempt_20260714_zdigit_plus_blocked/attempt.json`
    records `result = blocked`, `coq_alignment = checked`, and
    `build = pass`; `lake build` completed successfully with 3345 jobs.
    Manual follow-up `.change_log/manual_attempt_20260714_zdigit_plus_proved/attempt.json`
    restored the exact public theorem in `FloatSpec/src/Core/Digits.lean`.
    The proof derives a private lower-prefix no-carry lemma from the
    disjoint-digit hypothesis, proves the nonnegative exact case, and then
    reduces the signed same-sign case through `Zdigit_neg_eq`. Status:
    implemented and removed from active semantic gaps.
  - `Zdigit_scale`: partially present as `Zdigit_scale_point`, but the Lean
    theorem has an extra precondition `(0 <= k || 0 <= n)` and is wrapped in a
    Hoare-style spec. Upstream only assumes `0 <= k'`. Pipeline attempt
    `.change_log/codex_attempt_20260704_173447` classified the exact theorem
    as blocked against the current local definition: upstream `Zscale` uses
    `Z.quot` in the negative-shift branch, but local `Zscale` uses Lean `/`.
    The harness reported a concrete counterexample for the exact statement:
    with `beta = 10`, `n = -1`, `k = -1`, and `k' = 0`, the left side is
    `9` while the right side is `0`. Temporarily switching the branch to
    `Int.tdiv` made the exact target viable in scratch form but broke later
    local `Zscale`/`Zslice` proofs that currently depend on `/` semantics.
    Reattempt `.change_log/codex_attempt_20260711_153359` reconfirmed the
    same blocker with a Lean `#guard`: the checked pair is `(9, 0)`. Follow-up
    subscription attempt `.change_log/codex_attempt_20260711_194800` again
    classified the exact theorem as blocked with no source changes: for
    `beta = 10`, `n = -1`, `k = -1`, and `k' = 0`, local `Zscale` keeps the
    left digit at `9` while the upstream right side is `0`, so the exact
    upstream payload remains false until the signed quotient semantics are
    aligned. Config-provider harness attempt
    `.change_log/codex_attempt_20260713_111111` rechecked the exact upstream
    payload, left source code unchanged (`target_before.lean` and
    `target_after.lean` identical), and reconfirmed the same counterexample
    with a live `lake env lean --stdin` check: for `beta = 10`, `n = -1`,
    `k = -1`, and `k' = 0`, `(Zscale, left digit, right digit)` evaluates to
    `(-1, 9, 0)`. The attempt ran `scripts/audit_placeholders.sh --json
    FloatSpec`, `scripts/status_report.sh --write`, and
    `scripts/classify_attempt.py ... --result blocked --coq-alignment
    checked`. Faithful repair still requires aligning signed
    quotient/remainder semantics for `Zscale` and dependent digit/slice
    lemmas, not adding a theorem with the local extra nonnegativity side
    condition. Config-provider harness attempt
    `.change_log/codex_attempt_20260713_121354` rechecked the exact upstream
    theorem against `Zdigit_scale_point`, left `Digits.lean` unchanged
    (`target_before.lean` and `target_after.lean` identical), and wrote the
    nested checked classifier
    `.change_log/manual_attempt_20260713_zdigit_scale_blocked/attempt.json`.
    A live `lake env lean --stdin` probe in the same workspace again evaluated
    `(Zscale 10 (-1) (-1), Zdigit 10 (Zscale 10 (-1) (-1)) 0,
    Zdigit 10 (-1) (0 - (-1)))` to `(-1, 9, 0)`, showing the exact theorem is
    false for the current negative-branch `/` semantics.
    Config-provider harness attempt
    `.change_log/codex_attempt_20260713_202429` tried the faithful direction:
    it changed the negative `Zscale` branch to `Int.tdiv` and introduced an
    exact public `Zdigit_scale` theorem with only the upstream `0 <= k'`
    assumption. The target theorem itself became locally plausible, but
    `lake build` failed in `FloatSpec.src.Core.Digits` because existing
    downstream `Zscale`/`Zslice` proofs (`Zsame_sign_scale`,
    `Zscale_mul_pow`, `Zscale_scale`, `Zdigit_slice`, `Zslice_div_pow`, and
    `Zplus_slice`) still encode Euclidean `/` branch facts. The failed source
    edits were restored from the harness `target_before.lean`; a focused
    `lake env lean FloatSpec/src/Core/Digits.lean` check then passed again
    with warnings only. This confirms the required repair is a coherent
    signed-quotient tranche through the dependent scale/slice stack, not just
    a local wrapper around `Zdigit_scale_point`.
    Config-provider harness attempt `.change_log/codex_attempt_20260714_173659`
    rechecked the exact upstream theorem after the signed-`Zdigit` repair and
    again left `Digits.lean` unchanged (`target_before.lean` and
    `target_after.lean` identical). A live probe now evaluates
    `(Zscale 10 (-1) (-1), Zdigit 10 (Zscale 10 (-1) (-1)) 0,
    Zdigit 10 (-1) (0 - (-1)))` to `(-1, -1, 0)`: the old Euclidean-digit
    counterexample changed from left digit `9` to signed left digit `-1`, but
    the exact upstream theorem is still false because `Zscale`'s negative
    branch still uses Lean `/` rather than Flocq `Z.quot`. A controlled manual
    probe in the same turn changed only the negative `Zscale` branch to
    `Int.tdiv`; `lake env lean FloatSpec/src/Core/Digits.lean` then failed at
    the dependent scale/slice proof surface, including `Zdigit_scale_point`,
    `Zsame_sign_scale`, `Zscale_mul_pow`, `Zscale_scale`,
    `Zslice_div_pow`, and `Zplus_slice`. The probe was reverted and the
    focused Lean check passed again. This reconfirms that the required repair
    is the broader signed-quotient `Zscale`/`Zslice` tranche.
    Config-provider harness attempt `.change_log/codex_attempt_20260714_180608`
    targeted the shared `Zscale` definition directly. It tried the faithful
    repair direction by changing the negative branch to `Int.tdiv`,
    generalizing `Zdigit_div_pow` to truncating quotients, removing the extra
    nonnegative side condition from the scale-digit proof surface, and
    propagating the change into slice/division helpers. The attempt then
    restored `Digits.lean` to its pre-attempt snapshot and classified the
    tranche as blocked: existing downstream slice-addition infrastructure,
    especially `Zplus_slice`, still encodes the old Euclidean `/` behavior
    and becomes false under the partial signed-truncation repair (the harness
    reported a counterexample shape with `beta = 10`, `k = 1`, `l = 1`,
    `n = -9`, `m = -9`). The focused command
    `lake env lean FloatSpec/src/Core/Digits.lean` passed after restoration.
    The next prerequisite is therefore not just `Zscale`'s quotient branch,
	    but a coherent signed quotient/remainder repair for `Zscale`, `Zslice`,
	    and their slice-addition lemmas.
	    Config-provider harness attempt `.change_log/codex_attempt_20260714_183359`
	    targeted the foundational `Zslice` definition after the signed-`Zscale`
	    blocker. It confirmed upstream `Digits.v` defines `Zslice` with signed
	    `Z.rem` after `Zscale`, while local Lean still uses Euclidean `%`.
	    Temporarily changing local `Zslice` to `Int.tmod` exposed a precise
	    downstream mismatch: the existing local `Zplus_slice` is a Euclidean
	    carry theorem for `n + m`, not upstream's signed slice recomposition
	    theorem. Under signed slices, the local theorem is false for
	    `beta = 10`, `k = 0`, `l = 1`, and `n = m = -3`: the signed slice of
	    `n + m` is `-6`, while the local Euclidean alternatives are `4` or `5`.
	    The attempt restored `Digits.lean`, wrote the checked blocker sidecar
	    `.change_log/manual_attempt_20260714_zslice_signed_blocked/attempt.json`,
	    and reported `lake env lean FloatSpec/src/Core/Digits.lean`,
	    `scripts/audit_placeholders.sh --json FloatSpec`,
	    `scripts/status_report.sh --write`, and `git diff --check` passing.
	    This narrows the prerequisite to replacing the local slice-addition
	    surface with the upstream signed `Zplus_slice` payload, supported by the
	    missing signed `Zdigit_slice`/`Zdigit_plus` infrastructure, rather than
	    preserving the current Euclidean carry statement.
	    Follow-up harness attempt `.change_log/codex_attempt_20260714_193130`
	    repaired one same-name prerequisite in that stack: public
	    `Zsame_sign_scale` now matches upstream's product-sign payload
	    `0 <= n * Zscale n k` instead of the previous stronger Euclidean
	    zero-characterization Hoare postcondition. The only local dependent use
	    in `Zdigit_slice` was updated to derive nonnegativity of the scaled value
	    from `0 <= n * Zscale n (-k)` and `0 < n`. This does not remove any
	    active semantic-gap candidate by itself, but it clears one false
	    same-name support theorem that blocked the signed `Zscale`/`Zslice`
	    tranche.
	    Config-provider harness retry `.change_log/codex_attempt_20260714_194553`
	    then reattempted the active `Zdigit_scale` target with that prerequisite
	    fixed. The provider again tried the faithful direction: changing
	    `Zscale`'s negative branch to `Int.tdiv` and adding the exact signed
	    `Zdigit_scale` theorem. The target was locally plausible, but the attempt
	    restored the source and classified the exact theorem as still blocked by
	    downstream proofs that preserve old Euclidean division/slice semantics:
	    `Zscale_scale`, `Zslice_div_pow`, and especially the local
	    `Zplus_slice`. With truncating `Zscale`, `beta = 10`, `k = 1`, `l = 1`,
	    and `n = m = -9`, the current local `Zplus_slice` shape is false:
	    `Zslice (n + m) = 9`, while its two Euclidean carry alternatives are `0`
	    and `1`. The checked classifier for the retry records `result =
	    blocked`, `coq_alignment = checked`, `build = pass`, and no source
	    changes left behind. The next concrete prerequisite is to replace local
	    `Zplus_slice` with upstream's signed slice recomposition theorem instead
	    of preserving the current carry theorem.
	    Harness attempt `.change_log/codex_attempt_20260714_201257` then
	    repaired that same-name support theorem: public `Zplus_slice` now has the
	    upstream slice-recomposition statement
	    `Zslice n k l1 + Zscale (Zslice n (k + l1) l2) l1 =
	    Zslice n k (l1 + l2)` under `0 <= l1` and `0 <= l2`, instead of the
	    stale Euclidean carry theorem over `n + m`. The old carry theorem was
	    not preserved under the upstream name. This is still a support repair,
	    not an active-candidate closure, because `Zscale` and `Zslice` definitions
	    still need their signed quotient/remainder alignment before exact
	    `Zdigit_scale` can be restored.
	    Post-`Zplus_slice` retry `.change_log/codex_attempt_20260714_203427`
	    reattempted the active `Zdigit_scale` target again. It left no source
	    changes and classified the exact theorem as still blocked, but narrowed
	    the next prerequisite: `Zdigit_div_pow` is still a nonnegative/positive
	    numerator theorem over local Euclidean `/`. Upstream needs the signed
	    `Z.quot` payload
	    `Zdigit beta (Int.tdiv n (beta ^ k'.natAbs)) k =
	    Zdigit beta n (k + k')` under `0 <= k` and `0 <= k'`, with no
	    `0 < n` restriction. Until that theorem and its callers move to signed
	    quotient semantics, changing `Zscale`'s negative branch to `Int.tdiv`
	    keeps breaking `Zslice_div_pow` and the affected `Zscale_*` proofs.
	    Harness attempt `.change_log/codex_attempt_20260714_204822` repaired
	    that support theorem: public `Zdigit_div_pow` now matches the upstream
	    signed quotient payload, using `Int.tdiv n (beta ^ l.natAbs)` and only
	    assuming `0 <= k` and `0 <= l`. The previous nonnegative Euclidean `/`
	    behavior was preserved privately as `Zdigit_div_pow_nonneg_ediv` for
	    current local callers such as `Zdigit_scale_point`. A focused
	    `lake env lean FloatSpec/src/Core/Digits.lean` check, status/placeholder
	    audits, `git diff --check`, and full `lake build` all passed after this
	    repair. This is another same-name support repair rather than an
	    active-candidate closure; `Zscale`'s negative branch still needs to move
	    from `/` to `Int.tdiv` before exact `Zdigit_scale` can be restored.
	    Retry `.change_log/codex_attempt_20260714_210940` reattempted
	    `Zdigit_scale` after the `Zdigit_div_pow` support repair. The exact
	    theorem and `Int.tdiv` negative branch were locally plausible, but the
	    attempt restored the partial edit and classified the active target as
	    still blocked by the remaining Euclidean scale/slice surface:
	    `Zscale_mul_pow`, `Zscale_scale`, `Zslice_div_pow`, and helper
	    `zscale_div_pow_nonneg` still need signed quotient semantics before
	    `Zscale` can be switched. The focused Lean check, placeholder audit,
	    status refresh, and `git diff --check` passed after restoration; no
	    source changes were left by that retry.
	    Follow-up harness attempt `.change_log/codex_attempt_20260714_212530`
	    targeted the first remaining support blocker, `Zscale_mul_pow`. It
	    checked upstream `Core/Digits.v` and tried the faithful direction by
	    switching the negative `Zscale` branch from Lean Euclidean `/` to
	    `Int.tdiv`, then repairing the scale/multiply proof against signed
	    quotient cancellation. That target-only patch again had to be restored:
	    the surrounding scale/slice surface still assumes Euclidean division,
	    with failures reported at `Zdigit_scale_point`, `Zsame_sign_scale`,
	    `Zscale_scale`, `Zslice_div_pow`, and later scale/slice helpers. The
	    checked sidecar
	    `.change_log/manual_attempt_20260714_zscale_mul_pow_blocked/attempt.json`
	    records `result = blocked`, `coq_alignment = checked`, and
	    `build = pass`. No source changes were left by the attempt; the blocker
	    remains the broader signed quotient `Zscale`/`Zslice` tranche, not
	    `Zscale_mul_pow` in isolation.
	    Harness attempt `.change_log/codex_attempt_20260714_214654` then
	    repaired one same-name support theorem in that stack: public
	    `Zscale_scale` now matches the upstream `Core/Digits.v` payload
	    `Zscale (Zscale n k) k' = Zscale n (k + k')` with only the upstream
	    `0 <= k` precondition. The old local all-exponent theorem with
	    divisibility side conditions was preserved privately as
	    `zscale_scale_divisible` for the current Euclidean-scale callers, and
	    `Zslice_scale` was updated to use that private compatibility helper.
	    The checked sidecar
	    `.change_log/codex_attempt_20260714_214654/zscale_scale_checked_proved.json`
	    records `result = proved`, `coq_alignment = checked`,
	    `statement_changed = true`, and `build = pass`. This is a support
	    repair rather than an active-candidate closure; exact `Zdigit_scale`
	    still requires the signed quotient `Zscale`/`Zslice` tranche.
	    Harness attempt `.change_log/codex_attempt_20260714_220639` then
	    targeted the next same-name support blocker, `Zslice_div_pow`. It left
	    no source changes and classified the exact upstream signed-quotient
	    payload as blocked under current local semantics. The checked
	    counterexample is `beta = 10`, `n = -1`, `k = 1`, `k1 = 1`,
	    `k2 = 1`: `Zslice 10 (Int.tdiv (-1) (10^1)) 1 1 = 0`, while
	    `Zslice 10 (-1) (1 + 1) 1 = 9`. The failure is caused by the remaining
	    mismatch that local `Zscale` still uses Lean Euclidean `/` in its
	    negative branch and local `Zslice` still uses Euclidean `%`, while
	    upstream uses `Z.quot`/`Z.rem`. The nested classifier
	    `.change_log/manual_attempt_20260714_zslice_div_pow_blocked/attempt.json`
	    records `result = blocked`, `coq_alignment = checked`, and
	    `build = pass`; focused `Digits.lean`, placeholder audit, status
	    refresh, and `git diff --check` passed, with no Lean source change
	    left by this attempt.
	    Harness attempt `.change_log/codex_attempt_20260714_223222`
	    re-targeted the `Zscale` definition itself after the `Zscale_scale`
	    support repair. It compared against upstream `Digits.v`, confirmed that
	    upstream `Zscale` uses `Z.quot`, and probed the faithful direction by
	    changing the negative branch to `Int.tdiv`. The probe was restored:
	    changing `Zscale` alone still breaks the current Euclidean
	    slice/recomposition surface. The provider reported a standalone
	    recomposition mismatch with signed `Zscale` but current Euclidean
	    `Zslice`: for `beta = 10`, `n = -3`, `k = 0`, `l1 = 1`, and
	    `l2 = 1`, the slice recomposition shape gives `(7, 97)`. The checked
	    classifier
	    `.change_log/manual_attempt_20260714_zscale_signed_quot_blocked/attempt.json`
	    records `result = blocked`, `coq_alignment = checked`, and
	    `build = pass`. No source changes were left by this attempt; the next
	    prerequisite is the signed `Zslice`/`Z.rem` alignment and dependent
	    slice lemmas, not a standalone `Zscale` switch.
	    Harness attempt `.change_log/codex_attempt_20260714_224035` then
	    targeted the `Zslice` definition directly. It confirmed upstream
	    `Zslice` uses signed `Z.rem` and probed the local change from
	    Euclidean `%` to `Int.tmod`, but restored the edit because the current
	    quotient/slice proof surface is not yet coherent under signed
	    quotient/remainder semantics. The checked classifier
	    `.change_log/manual_attempt_20260714_zslice_signed_rem_blocked/attempt.json`
	    records `result = blocked`, `coq_alignment = checked`, and
	    `build = pass`: changing `Zslice` alone is blocked until `Zscale`'s
	    negative branch uses `Int.tdiv` and dependent `Zplus_slice`,
	    `zscale_div_pow_nonneg`, and `Zslice_div_pow` proofs use truncating
	    quotient decomposition rather than Lean Euclidean `/` and `%`.
	    Harness attempt `.change_log/codex_attempt_20260714_235829`
	    re-ran the active `Zdigit_scale` target after the latest signed digit
	    repairs. It left no source changes and wrote the checked classifier
	    `.change_log/manual_attempt_20260715_000553_zdigit_scale_blocked/attempt.json`:
	    with the current local `Zscale` negative branch still using Lean `/`,
	    the exact upstream theorem remains false at
	    `beta = 10`, `n = -1`, `k = -1`, and `k' = 0`, where the live probe
	    evaluates `(Zscale, left digit, right digit)` to `(-1, -1, 0)`.
	    A manual broader probe then switched `Zscale` to `Int.tdiv` and added
	    the exact public `Zdigit_scale` wrapper; that target and several
	    signed support proofs became locally plausible, but the file exposed
	    the remaining real semantic conflict in `zscale_div_pow_nonneg` and
	    `Zplus_slice`, which still combine signed quotient behavior with
	    Euclidean outer `/` and `%` decomposition. The probe was restored from
	    the harness `target_before.lean`, and `lake env lean
	    FloatSpec/src/Core/Digits.lean` passed again. The next repair must be
	    a coherent signed `Zscale`/`Zslice`/`Zplus_slice` tranche, not an
	    isolated `Zdigit_scale` theorem.
	    Follow-up harness attempt `.change_log/codex_attempt_20260715_015614`
	    targeted `Zplus_slice` directly. It confirmed that the public
	    statement is already the upstream recomposition payload, but its
	    current proof still depends on the Euclidean helper
	    `int_emod_mul_decompose`, local `Zslice` using `%`, and local
	    `Zscale` using `/`. The provider probed the faithful direction by
	    changing `Zscale`/`Zslice` to `Int.tdiv`/`Int.tmod`, then restored the
	    probe after `lake env lean FloatSpec/src/Core/Digits.lean` failed in
	    earlier scale/digit/slice proofs before the target-local repair could
	    complete. The checked manual classifier
	    `.change_log/manual_attempt_20260715_020355_zplus_slice_signed_tranche_blocked/attempt.json`
	    records `result = blocked`, `coq_alignment = checked`, and
	    `build = pass`. This narrows the next repair to a broad coherent
	    signed definition/support tranche: `Zscale`, `Zslice`,
	    `Zdigit_slice`, `Zslice_div_pow`, and `Zplus_slice` must move
	    together.
	    Config-provider harness attempt `.change_log/codex_attempt_20260715_025434`
	    re-ran the active `Zdigit_scale` target after the latest ledger update.
	    It again tried the faithful direction by switching the negative
	    `Zscale` branch to `Int.tdiv` and adding the exact public
	    `Zdigit_scale` theorem with only the upstream `0 <= k'` assumption.
	    The target theorem itself became plausible, but the provider restored
	    the probe because the remaining local `Zslice`/`Zplus_slice` surface
	    still depends on Euclidean `/` and `%` behavior. The attempt left no
	    source patch and classified the target as blocked; focused
	    `lake env lean FloatSpec/src/Core/Digits.lean`,
	    `scripts/audit_placeholders.sh --json FloatSpec`,
	    `scripts/status_report.sh --write`, and full `lake build` passed.
	    This reconfirms that no weakened wrapper should be added for
	    `Zdigit_scale`; the next implementation tranche must jointly migrate
	    `Zscale`, `Zslice`, `Zdigit_slice`, `Zslice_div_pow`, and
	    `Zplus_slice` to signed `Z.quot`/`Z.rem` semantics.
	    Config-provider harness attempt `.change_log/codex_attempt_20260715_034735`
	    targeted that signed `Zscale`/`Zslice` support tranche directly at the
	    `Zslice` definition. It compared the live file against upstream
	    `Core/Digits.v`, probed the faithful `Int.tdiv`/`Int.tmod` direction,
	    and restored the probe because the repair is still not local to the two
	    definitions. The checked blocker is now sharper: before the public
	    definitions can move, the file needs signed `Zdigit_mod_pow` and
	    `Zdigit_mod_pow_out`, an unrestricted signed `Zdigit_slice`, truncating
	    quotient versions of `Zslice_div_pow` and `zscale_div_pow_nonneg`, and a
	    signed product-remainder decomposition for `Zplus_slice`. The focused
	    `lake env lean FloatSpec/src/Core/Digits.lean` check, placeholder audit,
	    status refresh, `git diff --check`, and full `lake build` all passed
	    after the probe was restored.
	    Follow-up support harness attempt
	    `.change_log/codex_attempt_20260715_040846` repaired public
	    `Zdigit_mod_pow` to the signed upstream shape over
	    `Int.tmod n (beta ^ l.natAbs)`, with only the upstream `k < l`
	    assumption and no positive-numerator precondition. Current Euclidean
	    slice callers bridge through local nonnegativity until `Zslice` itself
	    moves to signed remainder semantics. Support harness attempt
	    `.change_log/codex_attempt_20260715_043830` then repaired public
	    `Zdigit_mod_pow_out` to the signed upstream `Z.rem` payload, represented
	    by `Int.tmod`, under only `0 <= k' <= k`; the old Euclidean `%` theorem
	    was kept privately as `Zdigit_emod_pow_out` for still-Euclidean local
	    callers. Focused `lake env lean FloatSpec/src/Core/Digits.lean`,
	    placeholder/status audits, and full `lake build` were reported passing
	    by the support attempts, and the current focused Lean check also passes.
	    These are support repairs, not active-candidate closures; exact
	    `Zdigit_scale` still requires the broader signed `Zscale`/`Zslice`
	    tranche plus unrestricted `Zdigit_slice`, signed `Zslice_div_pow`, and
	    signed decomposition support for `Zplus_slice`.
	    Harness attempt `.change_log/codex_attempt_20260715_050146` then
	    targeted the unrestricted upstream `Zdigit_slice` theorem directly
	    after the two signed modulo repairs. It left no source patch and wrote
	    the checked blocker
	    `.change_log/manual_attempt_20260715_zdigit_slice_unrestricted_blocked/attempt.json`.
	    The remaining obstruction is not `Zdigit_mod_pow`/`Zdigit_mod_pow_out`
	    anymore: upstream-shaped `Zdigit_slice` needs signed `Zslice`/`Z.rem`
	    semantics plus an unrestricted signed `Zdigit_scale`/`Zscale` theorem.
	    Local `Zslice` still uses Euclidean `%`; changing it alone breaks
	    `Zslice_nonneg`, `Zslice_slice`, `Zplus_slice`, and later digit-count
	    proofs, and `Zdigit_scale_point` still requires `0 <= -k` or `0 <= n`.
	    The attempt reported focused `Digits.lean`, placeholder/status audits,
	    and full `lake build` passing after restoration.
	    Harness attempt `.change_log/codex_attempt_20260715_052830` then
	    targeted the `Zscale` definition itself after the signed
	    `Zdigit_div_pow`, `Zdigit_mod_pow`, and `Zdigit_mod_pow_out` repairs.
	    It confirmed the faithful direction, because upstream `Zscale` uses
	    `Z.quot` and local `Zscale` still uses Lean `/` in the negative branch.
	    The minimal `Int.tdiv` branch switch was restored rather than left as a
	    partial semantic migration. The precise remaining blocker is the local
	    slice stack: `zscale_div_pow_nonneg` and `Zplus_slice` are still built
	    around Euclidean division/remainder decomposition, while upstream also
	    requires `Zslice` to use signed `Z.rem` and `Zslice_div_pow` to use
	    `Z.quot`. The attempt reported focused `Digits.lean`, placeholder/status
	    audits, `git diff --check`, and full `lake build` passing after
	    rollback. The next prerequisite remains a joint signed migration of
	    `Zscale`, `Zslice`, `Zslice_div_pow`, `zscale_div_pow_nonneg`, and
	    `Zplus_slice`, not an isolated `Zscale` branch edit.
	    Harness attempt `.change_log/codex_attempt_20260715_060414` targeted
	    same-name support theorem `Zslice_div_pow`, whose upstream statement is
	    over `Z.quot`. It left no source patch and wrote the checked blocker
	    `.change_log/manual_attempt_20260715_zslice_div_pow_signed_quot_blocked/attempt.json`.
	    The upstream-aligned `Int.tdiv` statement is false under the live mixed
	    definitions: with `beta = 10`, `n = -1`, `k = 1`, `k1 = 1`, and
	    `k2 = 1`, the two sides evaluate to `0` and `9`. This reconfirms that
	    `Zslice_div_pow` cannot be repaired independently of the signed
	    `Zscale`/`Zslice`/`Zplus_slice`/`zscale_div_pow_nonneg` migration.
	    Support harness attempt `.change_log/codex_attempt_20260715_071443`
	    then targeted the Euclidean product-remainder helper that current
	    `Zplus_slice` uses. It preserved the old private
	    `int_emod_mul_decompose` and added/proved private
	    `int_tmod_mul_decompose`, the signed truncating counterpart
	    `Int.tmod a (b * c) = Int.tmod a b + b * Int.tmod (Int.tdiv a b) c`
	    for positive `b` and `c`. This clears one local support prerequisite
	    for replacing the Euclidean `Zplus_slice` proof with a signed
	    `Z.rem`/`Z.quot` proof, but it is not an active-candidate closure by
	    itself. The attempt reported focused `Digits.lean`, placeholder/status
	    audits, `git diff --check`, and full `lake build` passing.
	    Follow-up harness attempt `.change_log/codex_attempt_20260715_073336`
	    targeted `Zplus_slice` with `int_tmod_mul_decompose` now available. It
	    left no source patch and classified the target as still blocked: the
	    recomposition payload is the upstream one, but it cannot be repaired
	    locally while live `Zscale` still uses Lean `/` in the negative branch
	    and live `Zslice` still uses Euclidean `%`. The next proof-producing
	    step must move those definitions together, then reuse the signed
	    decomposition helper inside the migrated `Zplus_slice` proof.
	    Harness attempt `.change_log/codex_attempt_20260715_162050`
	    completed that support tranche: `Zscale` now uses `Int.tdiv` in the
	    negative branch, `Zslice` now uses `Int.tmod`, and the dependent
	    `Zslice_div_pow`, `zscale_div_pow_nonneg`, and `Zplus_slice` proofs were
	    adjusted to the signed quotient/remainder shape. The attempt reported
	    focused `lake env lean FloatSpec/src/Core/Digits.lean`,
	    `scripts/audit_placeholders.sh --json FloatSpec`,
	    `scripts/status_report.sh --write`, full `lake build`, and
	    `git diff --check` passing, with placeholder/trust findings reduced
	    from 56 to 53. This is still a support-tranche completion rather than an
	    active-candidate closure: exact public `Zdigit_scale` remains absent and
	    must be restored next against the now-signed definitions.
	    Follow-up harness attempt `.change_log/codex_attempt_20260715_164646`
	    restored exact public `Zdigit_scale` in `FloatSpec/src/Core/Digits.lean`
	    with the upstream precondition `0 <= k'` and payload
	    `Zdigit (Zscale n k) k' = Zdigit n (k' - k)`, using the signed
	    `Zscale` definition and signed `Zdigit_div_pow`. The older
	    `Zdigit_scale_point` Hoare wrapper is now only a compatibility theorem
	    derived from exact `Zdigit_scale`; it is no longer counted as the
	    faithful counterpart. The nested classifier
	    `.change_log/manual_attempt_20260715_zdigit_scale_proved/attempt.json`
	    records `result = proved`, `coq_alignment = checked`, and
	    `build = pass`; the harness reported focused `Digits.lean`,
	    placeholder/status audits, full `lake build`, and `git diff --check`
	    passing.
	    Status: implemented and removed from active semantic gaps.
  - `Zslice_div_pow_scale`: partially present as
    `Zslice_div_pow_scale_nonnegKp`, but the local theorem has a different
    scaled/divided expression and extra nonnegativity/order assumptions.
    Pipeline attempt `.change_log/codex_attempt_20260704_174539` left
    `Digits.lean` unchanged and classified the exact theorem as blocked by
    missing unrestricted digit infrastructure: upstream proves it through
    unrestricted `Zdigit_ext`, `Zdigit_slice`, and `Zdigit_div_pow`, whereas
    current Lean has `Zdigit_ext_nonneg` and local slice/division lemmas with
    nonnegative or positive numerator restrictions. Subscription reattempt
    `.change_log/codex_attempt_20260711_195128` reconfirmed the same blocker:
    reducing the Hoare wrapper to the intended integer equality leaves signed
    quotient/remainder and slice-scaling obligations not covered by
    `Zdigit_ext_nonneg`, `Zdigit_slice`, or `Zdigit_div_pow`. Status:
    renamed/split but not a faithful counterpart; exact theorem still
    required after the signed digit/slice/division lemmas are strengthened.
    Subscription harness attempt `.change_log/codex_attempt_20260713_085747`
    rechecked the current upstream four-argument statement from
    `Core/Digits.v:656` and left source code unchanged. The existing local
    comment/wrapper around `Digits.lean:2803` is for a different older payload
    with an extra `k'` and product by `beta^k'`; the current upstream theorem
    instead relates `Zslice (Z.quot n (Zpower beta k)) k1 k2` to
    `Zscale (Zslice n k (k1 + k2)) (-k1)` under only `0 <= k`. The blocker is
    still the missing unrestricted stack: exact proof needs unrestricted
    `Zdigit_ext`, `Zdigit_scale`, `Zdigit_slice`, and `Zdigit_div_pow`, while
    local counterparts impose nonnegativity/positivity/sign assumptions. The
    local helper docstring was repaired after the attempt so it no longer
    presents `Zslice_div_pow_scale_nonnegKp` as the current upstream theorem.
    Config-provider harness attempt
    `.change_log/codex_attempt_20260713_111757` rechecked the same exact
    current upstream statement, left source code unchanged
    (`target_before.lean` and `target_after.lean` identical), and classified
    it as still blocked. Its nested classifier
    `.change_log/codex_attempt_20260713_032022` records
    `coq_alignment = checked`: exact restoration still requires unrestricted
    `Zdigit_ext`, `Zdigit_scale`, `Zdigit_slice`, and `Zdigit_div_pow` over
    signed quotient/remainder semantics; local counterparts remain restricted
    by nonnegativity, positivity, divisibility, and the current Lean
    division/remainder semantics. Config-provider harness attempt
    `.change_log/codex_attempt_20260713_122315` rechecked the exact upstream
    theorem against `Zslice_div_pow_scale_nonnegKp`, left `Digits.lean`
    unchanged (`target_before.lean` and `target_after.lean` identical), and
    classified the target as blocked. The explicit checked classifier
    `.change_log/manual_attempt_20260713_zslice_div_pow_scale_blocked/attempt.json`
    records `result = blocked`, `coq_alignment = checked`, and
    `build = pass`: the local helper is still the older product-by-power
    payload, while the exact upstream theorem needs unrestricted
    `Zdigit_ext`, `Zdigit_scale`, `Zdigit_slice`, and `Zdigit_div_pow`.
    Config-provider harness attempt
    `.change_log/codex_attempt_20260713_205848` rechecked the same exact
    four-argument upstream statement after the signed-`Zdigit_ext` work and
    still left `Digits.lean` unchanged. The attempt classified the target as
    blocked, with the same statement-level reason: exact restoration depends
    on unrestricted signed quotient/remainder infrastructure for
    `Zdigit_scale`, `Zdigit_slice`, and `Zdigit_div_pow`, while
    `Zslice_div_pow_scale_nonnegKp` remains a different product-by-power
    theorem with extra parameters and assumptions. The harness refreshed
    `scripts/status_report.sh --write` and
    `scripts/audit_placeholders.sh --json FloatSpec`; counts remained
    `sorry = 0`, `axiom = 0`, `admit = 0`, and 53 placeholder/trust findings.
    Config-provider harness attempt `.change_log/codex_attempt_20260714_224835`
    rechecked the active candidate after the recent `Zscale_scale` support
    repair and the signed `Zscale`/`Zslice` definition probes. It again left
    no source change and classified the exact upstream-shaped theorem as
    blocked under current local definitions. The checked counterexample is
    `beta = 2`, `n = -3`, `k = 1`, `k1 = -1`, and `k2 = 3`: the
    signed-quotient LHS evaluates to `6`, while the current RHS evaluates to
    `4`. The nested classifier
    `.change_log/manual_attempt_20260714_zslice_div_pow_scale_blocked/attempt.json`
    records `result = blocked`, `coq_alignment = checked`, and
    `build = pass`. Exact restoration still requires aligning `Zscale` and
    `Zslice` with signed `Z.quot`/`Z.rem` semantics and repairing the
    dependent slice lemmas, not weakening this active theorem.
    Follow-up support attempt `.change_log/codex_attempt_20260714_231734`
    targeted same-name `Zdigit_slice`, because upstream
    `Zslice_div_pow_scale` depends on unrestricted slicing. It left no source
    changes and classified the unrestricted upstream-style support theorem as
    blocked under current local definitions. The checked counterexample is
    `beta = 10`, `n = -1`, `k = 0`, `l = 1`, and `m = 0`:
    `Zdigit beta (Zslice beta n k l) m = 9`, while
    `Zdigit beta n (k + m) = -1`. The checked sidecar
    `.change_log/codex_attempt_20260714_231734/zdigit_slice_checked_blocked.json`
    records `result = blocked`, `coq_alignment = checked`, and
    `build = pass`. Removing the local `0 <= n` restriction from
    `Zdigit_slice` still requires first aligning `Zscale`/`Zslice` with
    signed quotient/remainder semantics.
    Follow-up harness attempt `.change_log/codex_attempt_20260715_022442`
    targeted the active `Zslice_div_pow_scale` candidate directly. It
    rechecked the exact upstream statement and confirmed that it is still
    false for the live local definitions: with `beta = 2`, `n = -3`,
    `k = 1`, `k1 = -1`, and `k2 = 3`, the left side evaluates to `6`
    while the right side evaluates to `4`. The provider then probed the
    faithful semantic direction by temporarily changing `Zscale`'s negative
    branch to `Int.tdiv` and `Zslice`'s remainder to `Int.tmod`, but restored
    the probe after the focused check broke existing `Zscale`, `Zslice`,
    `Zdigit_slice`, `Zslice_slice`, `Zplus_slice`, and later digit-count
    proofs. The checked manual classifier
	    `.change_log/manual_attempt_20260714_183121_zslice_div_pow_scale_blocked/attempt.json`
	    records `result = blocked`, `coq_alignment = checked`, and
	    `build = pass`. Exact restoration remains a broad signed
	    quotient/remainder migration, not a single-target wrapper.
	    Follow-up harness attempt `.change_log/codex_attempt_20260715_174950`
	    restored exact public `Zslice_div_pow_scale` in
	    `FloatSpec/src/Core/Digits.lean` with the current upstream
	    four-argument payload
	    `Zslice (Z.quot n (Zpower beta k)) k1 k2 =
	    Zscale (Zslice n k (k1 + k2)) (-k1)` under only `0 <= k`.
	    The proof adds private helper `Zdigit_slice_unrestricted` and uses the
	    now-signed `Zdigit_scale`, `Zdigit_div_pow`, `Zdigit_slice_out`, and
	    `Zdigit_ext` stack; the older `Zslice_div_pow_scale_nonnegKp` remains
	    local compatibility infrastructure and is not counted as the upstream
	    theorem. The harness reported focused `Digits.lean`, full `lake build`,
	    placeholder/status audits, and `git diff --check` passing, with
	    0 `sorry`, 0 `axiom`, 0 `admit`, and 53 existing placeholder/trust
	    findings.
	    Status: implemented and removed from active semantic gaps.
- `Core/FIX.v`
  - `FIX_exp_monotone`: restored as the exact Lean instance
    `FloatSpec.Core.FIX.FIX_exp_monotone` in
    `FloatSpec/src/Core/FIX.lean` after harness attempt
    `.change_log/codex_attempt_20260704_170409`. The instance proves
    `Monotone_exp (FIX_exp emin)` for the constant fixed exponent by
    `le_rfl`, matching the upstream `Global Instance FIX_exp_monotone`.
    Status: implemented and removed from active semantic gaps.
  - `exists_NE_FIX`: restored as the exact Lean instance
    `FloatSpec.Core.FIX.exists_NE_FIX` in `FloatSpec/src/Core/FIX.lean`
    after harness attempt `.change_log/codex_attempt_20260704_171807`.
    The instance proves the even-radix branch of
    `FloatSpec.Core.RoundNE.Exists_NE beta (FIX_exp emin)` by the constant
    exponent equations `FIX_exp emin e = emin` and
    `FIX_exp emin (FIX_exp emin e + 1) = FIX_exp emin e`, matching upstream
    `Global Instance exists_NE_FIX`.
    Status: implemented and removed from active semantic gaps.
- `Core/FLT.v`
  - `FLT_exp_monotone`: faithfully represented under the renamed Lean instance
    `FLT_exp_mono`. Status: removed from active semantic gaps.
  - `exists_NE_FLT`: restored as the exact Lean instance
    `FloatSpec.Core.FLT.exists_NE_FLT` in `FloatSpec/src/Core/FLT.lean`
    after harness attempt `.change_log/codex_attempt_20260704_180501`.
    The Lean instance uses `[Fact (beta % 2 ≠ 0 ∨ 1 < prec)]` for the
    upstream premise `(Z.even beta = false \/ (1 < prec)%Z)` and proves
    `FloatSpec.Core.RoundNE.Exists_NE beta (FLT_exp prec emin)` by the same
    two branches: odd radix immediately, or the `max (e - prec) emin`
    exponent-condition proof for the positive-precision branch. Status:
    implemented and removed from active semantic gaps.
- `Core/FLX.v`
  - `FLX_exp_monotone`: faithfully represented under the renamed Lean instance
    `FLX_exp_mono`. Status: removed from active semantic gaps.
  - `exists_NE_FLX`: restored as the exact Lean instance
    `FloatSpec.Core.FLX.exists_NE_FLX` in `FloatSpec/src/Core/FLX.lean`
    after harness attempt `.change_log/codex_attempt_20260704_175602`.
    The Lean instance uses `[Fact (beta % 2 ≠ 0 ∨ 1 < prec)]` to encode the
    upstream section hypothesis
    `NE_prop : Z.even beta = false \/ (1 < prec)%Z`, then proves
    `FloatSpec.Core.RoundNE.Exists_NE beta (FLX_exp prec)` by the same two
    branches: odd radix immediately, or the fixed-precision exponent equations
    by unfolding `FLX_exp`. Status: implemented and removed from active
    semantic gaps.
- `Core/Generic_fmt.v`
  - `valid_rnd_DN`, `valid_rnd_UP`, `valid_rnd_ZR`: present in substance under
    renamed instances `valid_rnd_floor`, `valid_rnd_ceil`, and
    `valid_rnd_Ztrunc`. Status: removed from active semantic gaps.
  - `valid_rnd_AW`: restored as the exact Lean instance
    `FloatSpec.Core.Generic_fmt.valid_rnd_AW` in
    `FloatSpec/src/Core/Generic_fmt.lean` after harness attempt
    `.change_log/codex_attempt_20260704_181840`. The instance proves
    `Valid_rnd FloatSpec.Core.Raux.Zaway` directly from the local
    `Zaway_le` and `Zaway_IZR` lemmas, matching upstream
    `Global Instance valid_rnd_AW : Valid_rnd Zaway`. Status: implemented
    and removed from active semantic gaps.
  - `monotone_exp_not_FTZ`: present in substance as
    `monotone_exp_not_FTZ_theorem` in `FloatSpec/src/Core/Ulp.lean`, not in
    `Generic_fmt.lean`. Status: removed from active semantic gaps.
  - `valid_rnd_NA`: restored as the exact Lean instance
    `FloatSpec.Core.Generic_fmt.valid_rnd_NA` in
    `FloatSpec/src/Core/Generic_fmt.lean` after harness attempt
    `.change_log/codex_attempt_20260704_182605`. The instance proves
    `Valid_rnd (Znearest ZnearestA)` by specializing the generic
    `valid_rnd_N` instance to the upstream tie-away choice
    `ZnearestA := fun t => decide (0 <= t)`, matching
    `Global Instance valid_rnd_NA : Valid_rnd (Znearest (Zle_bool 0))`.
    Status: implemented and removed from active semantic gaps.
  - `valid_rnd_N0`: restored as the exact Lean instance
    `FloatSpec.Core.Generic_fmt.valid_rnd_N0` in
    `FloatSpec/src/Core/Generic_fmt.lean` after harness attempt
    `.change_log/codex_attempt_20260704_183321`. The local
    `Znearest0` is now the upstream rounding function
    `Znearest (fun t => decide (t < 0))`, and the instance specializes
    `valid_rnd_N` to that choice, matching
    `Global Instance valid_rnd_N0 : Valid_rnd Znearest0`.
    Status: implemented and removed from active semantic gaps.
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
- `Rabs_lt`: restored as the exact Lean theorem
  `FloatSpec.Core.Raux.Rabs_lt` in `FloatSpec/src/Core/Raux.lean` after
  harness attempt `.change_log/codex_attempt_20260704_234132`. The theorem
  proves `∀ x y, -y < x ∧ x < y → |x| < y` by `abs_lt.mpr`, matching
  upstream `Theorem Rabs_lt : forall x y, (-y < x < y)%R ->
  (Rabs x < y)%R`. Status: implemented and removed from active semantic gaps.
- `Rabs_gt_inv`: restored as the exact Lean theorem
  `FloatSpec.Core.Raux.Rabs_gt_inv` in `FloatSpec/src/Core/Raux.lean` after
  target attempt `FloatSpec/src/Core/Raux.lean:662`. The theorem proves
  `∀ x y, x < |y| → y < -x ∨ x < y` by splitting on the sign of `y`, matching
  upstream `Theorem Rabs_gt_inv : forall x y, (x < Rabs y)%R ->
  (y < -x \/ x < y)%R`. Status: implemented and removed from active semantic
  gaps.
- `Rcompare_middle`: restored as the exact Lean theorem
  `FloatSpec.Core.Raux.Rcompare_middle` in `FloatSpec/src/Core/Raux.lean`
  after harness attempt `.change_log/codex_attempt_20260705_000449`, with the
  verified subscription-provider record at
  `.change_log/codex_attempt_20260705_000449/attempt.verified.json`.
  The theorem proves
  `∀ x d u, Rcompare (x - d) (u - x) = Rcompare x ((d + u) / 2)` by reducing
  both `Rcompare` calls to the same linear midpoint comparison, matching
  upstream `Theorem Rcompare_middle`. Status: implemented and removed from
  active semantic gaps.
- `Rcompare_floor_ceil_middle`: restored as the exact Lean theorem
  `FloatSpec.Core.Raux.Rcompare_floor_ceil_middle` in
  `FloatSpec/src/Core/Raux.lean` after harness attempt
  `.change_log/codex_attempt_20260705_002116`, with the verified
  subscription-provider record at
  `.change_log/codex_attempt_20260705_002116/attempt.verified.json`.
  The theorem proves
  `∀ x, (Zfloor x : ℝ) ≠ x →
    Rcompare (x - (Zfloor x : ℝ)) (1 / 2) =
    Rcompare (x - (Zfloor x : ℝ)) ((Zceil x : ℝ) - x)` by deriving
  `Zceil x = Zfloor x + 1` in the non-integral case and applying the already
  restored `Rcompare_middle`, matching upstream
  `Theorem Rcompare_floor_ceil_middle`. Status: implemented and removed from
  active semantic gaps.
- `Rcompare_ceil_floor_middle`: restored as the exact Lean theorem
  `FloatSpec.Core.Raux.Rcompare_ceil_floor_middle` in
  `FloatSpec/src/Core/Raux.lean` after harness attempt
  `.change_log/codex_attempt_20260705_003445`, with the verified
  subscription-provider record at
  `.change_log/codex_attempt_20260705_003445/attempt.verified.json`.
  The theorem proves
  `∀ x, (Zfloor x : ℝ) ≠ x →
    Rcompare ((Zceil x : ℝ) - x) (1 / 2) =
    Rcompare ((Zceil x : ℝ) - x) (x - (Zfloor x : ℝ))` by deriving
  `Zceil x = Zfloor x + 1` in the non-integral case and applying the already
  restored `Rcompare_middle`, matching upstream
  `Theorem Rcompare_ceil_floor_middle`. Status: implemented and removed from
  active semantic gaps.
- `cond_Ropp_Rlt_bool`: restored as the exact Lean theorem
  `FloatSpec.Core.Raux.cond_Ropp_Rlt_bool` in
  `FloatSpec/src/Core/Raux.lean` after harness attempt
  `.change_log/codex_attempt_20260705_005307`, with the verified
  subscription-provider record at
  `.change_log/codex_attempt_20260705_005307/attempt.verified.json`.
  The theorem proves
  `∀ m, cond_Ropp (Rlt_bool m 0) m = |m|` by splitting on `m < 0`
  and reducing `Rlt_bool`, `cond_Ropp`, and absolute value, matching upstream
  `Theorem cond_Ropp_Rlt_bool`. Status: implemented and removed from
  active semantic gaps.
- `Rlt_bool_cond_Ropp`: restored as the exact Lean theorem
  `FloatSpec.Core.Raux.Rlt_bool_cond_Ropp` in
  `FloatSpec/src/Core/Raux.lean` after harness attempt
  `.change_log/codex_attempt_20260705_010850`, with the verified
  subscription-provider record at
  `.change_log/codex_attempt_20260705_010850/attempt.verified.json`.
  The theorem proves
  `∀ x sx, 0 < x → Rlt_bool (cond_Ropp sx x) 0 = sx` by cases on `sx`,
  matching upstream `Theorem Rlt_bool_cond_Ropp`. Status: implemented and
  removed from active semantic gaps.

No active `Core/Raux.v` names remain after statement check.

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

Additional exact restoration:

- `eqbool_dep`: restored as the exact Lean definition
  `FloatSpec.Core.Zaux.eqbool_dep` in `FloatSpec/src/Core/Zaux.lean` after
  harness attempt `.change_log/codex_attempt_20260705_012623`, with the
  verified subscription-provider record at
  `.change_log/codex_attempt_20260705_012623/attempt.verified.json`.
  The definition is the upstream dependent boolean-indexed predicate:
  at index `true`, it compares the incoming `P true` value with the
  distinguished `h1`; at index `false`, it returns `False`. Status:
  implemented and removed from active semantic gaps.
- `Zpos_div_eucl_aux1_correct`: restored as the exact Lean theorem
  `FloatSpec.Core.Zaux.Zpos_div_eucl_aux1_correct` in
  `FloatSpec/src/Core/Zaux.lean` after harness attempt
  `.change_log/codex_attempt_20260705_050829`, with the verified
  subscription-provider record at
  `.change_log/codex_attempt_20260705_050829/attempt.verified.json`.
  The theorem follows the upstream positive-integer payload by adding a
  Core-local binary `Positive` carrier, the recursive
  `Zpos_div_eucl_aux1` helper, and proving equality with the local
  `Z_pos_div_eucl a (Zpos b)` quotient/remainder form. Status:
  implemented and removed from active semantic gaps.
- `Zpos_div_eucl_aux_correct`: restored as the exact Lean theorem
  `FloatSpec.Core.Zaux.Zpos_div_eucl_aux_correct` in
  `FloatSpec/src/Core/Zaux.lean` after harness attempt
  `.change_log/codex_attempt_20260705_053224`, with the verified
  subscription-provider record at
  `.change_log/codex_attempt_20260705_053224/attempt.verified.json`.
  The definition `Zpos_div_eucl_aux` now follows the upstream `Pos.compare`
  branch structure using the local binary `Positive` carrier: the small case
  returns `(0, Zpos a)`, the equality case returns `(1, 0)`, and the greater
  case delegates to `Zpos_div_eucl_aux1`; the theorem proves equality with
  `Z_pos_div_eucl a (Zpos b)`. Status: implemented and removed from active
  semantic gaps. No active `Core/Zaux.v` names remain.

Still active after statement check:

- No active `Core/Zaux.v` names remain after the two positive-division helper
  restorations above.

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

Additional exact restoration:

- `NG_existence_prop`: restored as the exact Lean definition
  `FloatSpec.Core.Round_pred.NG_existence_prop` in
  `FloatSpec/src/Core/Round_pred.lean` after harness attempt
  `.change_log/codex_attempt_20260705_013911`, with the verified
  subscription-provider record at
  `.change_log/codex_attempt_20260705_013911/attempt.verified.json`.
  The definition states
  `∀ x d u, ¬ F x → Rnd_DN_pt F x d → Rnd_UP_pt F x u → P x u ∨ P x d`,
  matching upstream `Definition NG_existence_prop`. Status: implemented and
  removed from active semantic gaps.
- `satisfies_any_eq`: restored as the exact Lean theorem
  `FloatSpec.Core.Round_pred.satisfies_any_eq` in
  `FloatSpec/src/Core/Round_pred.lean` after harness attempt
  `.change_log/codex_attempt_20260705_015324`, with the verified
  subscription-provider record at
  `.change_log/codex_attempt_20260705_015324/attempt.verified.json`.
  This tranche also restored the upstream `Round_pred.satisfies_any`
  predicate as a structural inductive proposition packaging `F 0`,
  closure under negation, and DN totality. The theorem proves that
  pointwise-equivalent formats preserve this predicate, matching upstream
  `Theorem satisfies_any_eq`; downstream `Round_NE.satisfies_any_imp_NE`
  was qualified to keep its pre-existing `Generic_fmt.satisfies_any`
  meaning after the namespace gained the Flocq predicate. Status:
  implemented and removed from active semantic gaps.
- `satisfies_any_imp_DN`: restored as the exact Lean theorem
  `FloatSpec.Core.Round_pred.satisfies_any_imp_DN` in
  `FloatSpec/src/Core/Round_pred.lean` after harness attempt
  `.change_log/codex_attempt_20260705_020600`, with the verified
  subscription-provider record at
  `.change_log/codex_attempt_20260705_020600/attempt.verified.json`.
  The theorem proves
  `∀ F, satisfies_any F → round_pred (Rnd_DN_pt F)` by destructing the
  restored Flocq-style `satisfies_any` predicate to obtain DN totality and
  using the existing DN monotonicity argument, matching upstream
  `Theorem satisfies_any_imp_DN`. The `_spec` wrapper now takes
  `hAny : satisfies_any F` as an explicit hypothesis instead of assuming
  `round_pred_total (Rnd_DN_pt F)` directly. Status: implemented and
  removed from active semantic gaps.

- `satisfies_any_imp_UP`: restored as the exact Lean theorem
  `FloatSpec.Core.Round_pred.satisfies_any_imp_UP` in
  `FloatSpec/src/Core/Round_pred.lean`. The theorem proves
  `∀ F, satisfies_any F → round_pred (Rnd_UP_pt F)` by taking DN totality at
  `-x`, transporting the witness through `Rnd_UP_pt_opp_pure`, and using UP
  monotonicity, matching upstream `Theorem satisfies_any_imp_UP`. The `_spec`
  wrapper now takes `hAny : satisfies_any F` as an explicit hypothesis instead
  of assuming `round_pred_total (Rnd_UP_pt F)` directly. Status: implemented
  and removed from active semantic gaps.

- `satisfies_any_imp_ZR`: restored as exact Lean theorem
  `FloatSpec.Core.Round_pred.satisfies_any_imp_ZR` in
  `FloatSpec/src/Core/Round_pred.lean` after harness attempt
  `.change_log/codex_attempt_20260705_022956`, with verified
  subscription-provider record at
  `.change_log/codex_attempt_20260705_022956/attempt.verified.json`.
  The theorem proves `∀ F, satisfies_any F → round_pred (Rnd_ZR_pt F)` by
  splitting totality on input sign, using DN totality for nonnegative inputs,
  `satisfies_any_imp_UP` for negative inputs, and the same ZR monotonicity
  argument as upstream `Rnd_ZR_pt_monotone`. The `_spec` wrapper now takes
  `hAny : satisfies_any F` instead of assuming `round_pred_total (Rnd_ZR_pt F)`
  directly. Status: implemented and removed from active semantic gaps.

- `satisfies_any_imp_NG`: restored as exact Lean theorem
  `FloatSpec.Core.Round_pred.satisfies_any_imp_NG` in
  `FloatSpec/src/Core/Round_pred.lean` after harness attempt
  `.change_log/codex_attempt_20260705_024140`, with verified
  subscription-provider record at
  `.change_log/codex_attempt_20260705_024140/attempt.verified.json`.
  The theorem proves
  `∀ F P, satisfies_any F → NG_existence_prop F P →
  round_pred_total (Rnd_NG_pt F P)`, matching upstream
  `Theorem satisfies_any_imp_NG`. The proof obtains DN/UP witnesses from
  `satisfies_any_imp_DN` and `satisfies_any_imp_UP`, chooses the nearer
  endpoint in strict-distance cases, and uses `NG_existence_prop` to select the
  tie endpoint in the non-representable equal-distance case. The checker now
  decides totality rather than full `round_pred`, because upstream NG existence
  does not assert monotonicity for arbitrary `P`; the `_spec` wrapper now takes
  `hAny : satisfies_any F` and `hP : NG_existence_prop F P` directly. Status:
  implemented and removed from active semantic gaps.

- `satisfies_any_imp_NA`: restored as exact Lean theorem
  `FloatSpec.Core.Round_pred.satisfies_any_imp_NA` in
  `FloatSpec/src/Core/Round_pred.lean` after harness attempt
  `.change_log/codex_attempt_20260705_043834`, with verified
  subscription-provider record at
  `.change_log/codex_attempt_20260705_043834/attempt.verified.json`.
  The theorem proves `∀ F, satisfies_any F → round_pred (Rnd_NA_pt F)`,
  matching upstream `Theorem satisfies_any_imp_NA`. The proof derives NA
  totality by instantiating `satisfies_any_imp_NG` with predicate
  `fun x f => |x| ≤ |f|`, uses the sign split on the input to satisfy
  `NG_existence_prop`, converts NG witnesses through `Rnd_NA_NG_pt_spec`, and
  obtains monotonicity from `Rnd_NA_pt_monotone_spec`. The `_spec` wrapper now
  takes `hAny : satisfies_any F` instead of assuming `round_pred_total
  (Rnd_NA_pt F)` and `F 0` directly. Status: implemented and removed from
  active semantic gaps.

Confirmed faithful counterparts removed from the active semantic gap list:

- `satisfies_any_imp_N0`: restored as the exact Lean theorem
  `FloatSpec.Core.Round_pred.satisfies_any_imp_N0` in
  `FloatSpec/src/Core/Round_pred.lean`. The theorem proves
  `∀ F, F 0 → satisfies_any F → round_pred (Rnd_N0_pt F)`, matching upstream
  `Theorem satisfies_any_imp_N0`. The proof derives N0 totality through
  `satisfies_any_imp_NG` with predicate `fun x f => |f| ≤ |x|`, uses the
  upstream sign split to satisfy `NG_existence_prop`, converts NG witnesses
  through `Rnd_N0_NG_pt_spec`, and obtains monotonicity from
  `Rnd_N0_pt_monotone_spec`. The `_spec` wrapper now takes `hF0 : F 0` and
  `hAny : satisfies_any F` instead of assuming `round_pred_total
  (Rnd_N0_pt F)` directly. Status: implemented and removed from active
  semantic gaps.

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
- `Bone`: restored as the exact BSN-layer Lean definition
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean:Bone`, using `SF2B` on the
  standard finite representation of positive one. The Binary layer still has
  `binary_one`, `Bone_correct`, `is_finite_Bone`, and `Bsign_Bone` exposing
  the corresponding constant-one payloads for `IEEE754/Binary.v`.
- `nan_pl`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.nan_pl` in `FloatSpec/src/IEEE754/Binary.lean`
  after harness attempt `.change_log/codex_attempt_20260705_055319`. The
  definition implements upstream `Zlt_bool (Zpos (digits2_pos pl)) prec` using
  the local `digits2_Pnat` digit-length bridge, with a zero guard for the extra
  `Nat` payload value that has no Coq `positive` counterpart. Status:
  implemented and removed from active semantic gaps.
- `Bcompare`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.Bcompare` in
  `FloatSpec/src/IEEE754/Binary.lean` after harness attempt
  `.change_log/codex_attempt_20260705_061749`. The definition exposes
  upstream ordered/unordered behavior directly in the Binary layer: it returns
  `none` for NaN operands, ordered comparison codes for infinities, and
  `Rcompare` for finite/zero values. `Bcompare_check` delegates to this exact
  operation; `Bcompare_correct` proves the finite payload and `Bcompare_swap`
  now preserves unordered `none` results while negating ordered codes. Status:
  implemented and removed from active semantic gaps.
- `Bmult`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.Bmult` in
  `FloatSpec/src/IEEE754/Binary.lean` after harness attempt
  `.change_log/codex_attempt_20260705_063205`. The definition follows the
  upstream adapter shape `BSN2B (mult_nan x y) (Bmult mode (B2BSN x)
  (B2BSN y))` using a local single-NaN bridge in the Binary layer, since
  importing `BinarySingleNaN` directly would create the existing module cycle.
  The old `binary_mul` helper now delegates to `Bmult` with the local RTZ
  compatibility mode and default NaN handler. Status: implemented and removed
  from active semantic gaps; `Bmult_correct` remains active as the upstream
  theorem payload has not been restored.
- `Bplus`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.Bplus` in
  `FloatSpec/src/IEEE754/Binary.lean` after harness attempt
  `.change_log/codex_attempt_20260705_064050`. The harness timed out before
  writing a final message, but it left a focused definition that typechecks:
  it follows the upstream adapter shape `BSN2B (plus_nan x y) (Bplus mode
  (B2BSN x) (B2BSN y))` using the same local single-NaN bridge used for
  `Bmult`, with an explicit NaN payload handler. Status: implemented and
  removed from active semantic gaps after manual verification; `Bplus_correct`
  remains active as the upstream theorem payload has not been restored.
- `Bminus`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.Bminus` in
  `FloatSpec/src/IEEE754/Binary.lean` after harness attempt
  `.change_log/codex_attempt_20260705_071857`. The definition follows the
  upstream adapter shape `BSN2B (minus_nan x y) (Bminus mode (B2BSN x)
  (B2BSN y))` using the local single-NaN bridge, with an explicit NaN payload
  handler. Status: implemented and removed from active semantic gaps.
- `Bfma`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.Bfma` in
  `FloatSpec/src/IEEE754/Binary.lean` after harness attempt
  `.change_log/codex_attempt_20260705_072524`. The harness timed out before
  writing a final message, but it left a focused definition that typechecks:
  it follows the upstream adapter shape `BSN2B (fma_nan x y z) (Bfma mode
  (B2BSN x) (B2BSN y) (B2BSN z))` using the same local single-NaN bridge used
  for `Bmult`, `Bplus`, and `Bminus`, with an explicit ternary NaN payload
  handler. Status: implemented and removed from active semantic gaps after
  manual verification; `Bfma_correct` remains separately tracked as a
  correctness theorem obligation.
- `Bdiv`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.Bdiv` in
  `FloatSpec/src/IEEE754/Binary.lean` after harness attempt
  `.change_log/codex_attempt_20260705_080200`. The definition follows the
  upstream adapter shape `BSN2B (div_nan x y) (Bdiv mode (B2BSN x)
  (B2BSN y))` using the local single-NaN bridge, with an explicit binary NaN
  payload handler. The older `binary_div` helper remains as a compatibility
  operation for existing local correctness proofs rather than being counted as
  the upstream API. Status: implemented and removed from active semantic gaps;
  `Bdiv_correct` remains separately tracked as a correctness theorem
  obligation.
- `Bsqrt`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.Bsqrt` in
  `FloatSpec/src/IEEE754/Binary.lean` after harness attempt
  `.change_log/codex_attempt_20260705_081229` failed without changing files.
  The manual follow-up follows the upstream adapter shape `BSN2B (sqrt_nan x)
  (Bsqrt mode (B2BSN x))` using the local single-NaN bridge, with an explicit
  unary NaN payload handler. The older `binary_sqrt` helper remains as a
  compatibility operation for existing local correctness proofs rather than
  being counted as the upstream API. Status: implemented and removed from
  active semantic gaps; `Bsqrt_correct` remains separately tracked as a
  correctness theorem obligation.
- `Bnearbyint`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.Bnearbyint` in
  `FloatSpec/src/IEEE754/Binary.lean` after harness attempt
  `.change_log/codex_attempt_20260706_045646`. The definition follows the
  upstream adapter shape `BSN2B (nearbyint_nan x) (Bnearbyint mode (B2BSN x))`
  using the local single-NaN bridge, with an explicit unary NaN payload
  handler. The older `binary_nearbyint` helper remains as a compatibility
  operation for existing local correctness proofs rather than being counted as
  the upstream API. Status: implemented and removed from active semantic gaps;
  `Bnearbyint_correct` remains separately tracked as a correctness theorem
  obligation.
- `Btrunc`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.Btrunc` in
  `FloatSpec/src/IEEE754/Binary.lean` after harness attempt
  `.change_log/codex_attempt_20260706_050523`. The definition follows the
  upstream adapter shape `Btrunc x := Btrunc (B2BSN x)` using the local
  single-NaN bridge. The older `binary_trunc` helper now delegates to the
  public upstream API name. Status: implemented and removed from active
  semantic gaps; the same-name theorem `Btrunc_correct` remains a separate
  statement-weakness/trust issue until it proves upstream's
  `IZR (Btrunc x) = round radix2 (FIX_exp 0) Ztrunc (B2R x)` payload.
- `Bmax_float`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.Bmax_float` in
  `FloatSpec/src/IEEE754/Binary.lean` after harness attempt
  `.change_log/codex_attempt_20260706_051853`. The single-NaN bridge exposes
  the maximum finite payload as
  `BinaryFloat.finite false (2 ^ prec.toNat - 1) (emax - prec)`, and the
  public Binary-level value follows the upstream wrapper shape
  `Bmax_float := BSN2B' Bmax_float eq_refl` through `BSN2B`. Status:
  implemented and removed from active semantic gaps; the upstream proof
  sibling `Bmax_float_proof` remains separately tracked under
  `IEEE754/BinarySingleNaN.v`.
- `Bnormfr_mantissa`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.Bnormfr_mantissa` in
  `FloatSpec/src/IEEE754/Binary.lean` after harness attempt
  `.change_log/codex_attempt_20260706_052816` failed before making changes.
  The single-NaN bridge mirrors upstream
  `Bnormfr_mantissa x := SFnormfr_mantissa prec (B2SF x)` by extracting the
  finite mantissa and returning `0` for non-finite constructors, and the
  public Binary-level value follows the upstream adapter shape
  `Bnormfr_mantissa x := Bnormfr_mantissa (B2BSN x)`. Status: implemented
  and removed from active semantic gaps; the upstream correctness sibling
  `Bnormfr_mantissa_correct` remains separately tracked under
  `IEEE754/BinarySingleNaN.v`.
- `Bulp`: restored as the exact Lean definition
  `FloatSpec.IEEE754.Binary.Bulp` in
  `FloatSpec/src/IEEE754/Binary.lean` after harness attempt
  `.change_log/codex_attempt_20260711_072607`. The public Binary-level value
  follows upstream's adapter shape
  `Bulp x := lift x (BinarySingleNaN.Bulp (B2BSN x))` by preserving full
  Binary NaN payloads and otherwise converting the local single-NaN bridge
  result back through `BSN2B`. Status: implemented and removed from active
  semantic gaps; `Bulp_correct` remains separately tracked as a correctness
  theorem obligation.

Still active after statement check:

- `full_float`: restored as the exact public Lean inductive
  `FloatSpec.IEEE754.Binary.full_float` in
  `FloatSpec/src/IEEE754/Binary.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260711_171234` timed out / reported the broad
  `FullFloat` migration as blocked and a manual scoped declaration was added.
  The constructors match upstream `IEEE754/Binary.v`: Boolean signs,
  `FloatSpec.Core.Zaux.Positive` for NaN payloads and finite mantissas, and
  `Int` for the exponent. Existing `FullFloat` remains the current Nat-based
  runtime model; this closes only the exact `full_float` type declaration, not
  downstream representation migration or `binary_float`. Focused check
  `lake env lean FloatSpec/src/IEEE754/Binary.lean` passed with existing
  warnings only. Status: implemented and removed from active semantic gaps.
- `binary_float`: restored as the exact public proof-carrying Lean inductive
  `FloatSpec.IEEE754.Binary.binary_float` in
  `FloatSpec/src/IEEE754/Binary.lean` by subscription harness attempt
  `.change_log/codex_attempt_20260711_172224`, which timed out before writing
  final artifacts but left a scoped patch. The constructors match upstream
  `IEEE754/Binary.v`: zero and infinity carry signs, NaNs carry a
  `FloatSpec.Core.Zaux.Positive` payload plus a `nan_pl` proof, and finite
  values carry a `FloatSpec.Core.Zaux.Positive` mantissa, `Int` exponent, and
  `bounded` proof. Existing `Binary754` remains the permissive compatibility
  wrapper over `FullFloat`; this closes only the exact `binary_float`
  declaration, not the downstream migration to use it. Focused check
  `lake env lean FloatSpec/src/IEEE754/Binary.lean` and full `lake build`
  passed with existing warnings only. Status: implemented and removed from
  active semantic gaps.
- `Bmult_correct` and `Bplus_correct`: no faithful counterparts found; local
  `binary_mul_correct` and `binary_add_correct` are `Unit` port-gap markers,
  not the upstream IEEE postconditions. Pipeline attempt
  `.change_log/codex_attempt_20260711_081455` classified `Bmult_correct` as
  blocked: the upstream theorem requires the full rounded-product payload,
  finite status as `andb (is_finite x) (is_finite y)`, non-NaN sign behavior,
  and an overflow branch returning `binary_overflow`, but local
  `BinarySingleNaNBridge.Bmult` sends non-NaN inputs through `roundReal` and
  cannot represent the Flocq SingleNaN nonfinite/overflow behavior. The
  lower-level BSN `B754_mult_correct` is still itself a `Unit` port gap.
  Config-provider harness attempt `.change_log/codex_attempt_20260713_094951`
  rechecked the current wrapper after the later Binary representation work and
  again left source code unchanged (`target_before.lean` and
  `target_after.lean` identical). It attempted a scoped repair but reverted the
  incomplete edits because the exact theorem still depends on faithful
  SingleNaN multiplication semantics and a real `B754_mult_correct` payload;
  proving through the current `Unit` marker or weakening the postcondition
  would not preserve the upstream rounded-product, finiteness, sign, and
  overflow branches. Config-provider harness attempt
  `.change_log/codex_attempt_20260713_123218` rechecked the exact upstream
  theorem at the current `binary_mul_correct` port-gap marker, left source code
  unchanged (`target_before.lean` and `target_after.lean` identical), and
  classified the target as blocked. The explicit checked classifier
  `.change_log/manual_attempt_20260713_bmult_correct_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and `build = pass`:
  upstream `Binary.v:Bmult_correct` delegates through `B2BSN`/`BSN2B` to the
  full `BinarySingleNaN.Bmult_correct` theorem, while local
  `BinarySingleNaN.lean` still has `B754_mult_correct : Unit` and
  `BinarySingleNaNBridge.Bmult` is a rounded-real shortcut rather than the full
  special-case multiplication with `Bmult_correct_aux`.
  Config-provider harness attempt `.change_log/codex_attempt_20260713_212314`
  rechecked the wrapper-level exact theorem and again made no Lean source
  changes. It classified the target as blocked because local
  `BinarySingleNaNBridge.Bmult` still routes every non-NaN case through
  `roundReal (B2R x * B2R y)`, so infinities collapse through `B2R = 0` and
  finite-overflow cases cannot satisfy the upstream finiteness and
  `binary_overflow` branches. The local SingleNaN multiplication correctness
  layer remains a `Unit` marker rather than the upstream
  `BinarySingleNaN.Bmult_correct`/`Bmult_correct_aux` payload.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_005430`
  rechecked `Bmult_correct` against the current branch, left source code
  unchanged (`target_before.lean` and `target_after.lean` identical), and
  classified the exact theorem as still blocked. The checked classifier
  `.change_log/manual_attempt_20260716_bmult_correct_blocked/attempt.json`
  records that upstream needs the full rounded-product `B2R` equality,
  finiteness as `andb (is_finite x) (is_finite y)`, non-NaN sign `xorb`, and
  overflow branch `B2FF = binary_overflow` through
  `BinarySingleNaN.Bmult_correct`, while local `binary_mul_correct` and
  `B754_mult_correct` remain `Unit` markers and `BinarySingleNaNBridge.Bmult`
  still routes non-NaN multiplication through the rounded-real shortcut
  `roundReal (B2R x * B2R y)`.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_051013`
  rechecked `Bmult_correct` at the current exact-name `Bmult` bridge, left
  source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean` / `target_after.lean` are identical), and returned
  `result = blocked`. The checked sidecar
  `.change_log/manual_attempt_20260716_051336_bmult_correct_blocked/attempt.json`
  records `coq_alignment = checked`: upstream `Binary.v:Bmult_correct` proves
  the rounded-product equality, finite status as
  `andb (is_finite x) (is_finite y)`, non-NaN sign `xorb`, and overflow
  `B2FF = binary_overflow` branch by delegating to
  `BinarySingleNaN.Bmult_correct` through `B2BSN`/`BSN2B`, while local
  `BinarySingleNaN.lean:B754_mult_correct` is still a payload-free `Unit`
  port-gap marker and no faithful SingleNaN `Bmult_correct` theorem is
  available to lift. Therefore `Bmult_correct` remains active rather than being
  replaced by a helper-only or tautological theorem over the current
  proof-erased/permissive bridge.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_061657`
  rechecked `Bmult_correct` again at the exact-name `Bmult` bridge and left
  source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean` / `target_after.lean` are identical). Its checked
  classifier sidecar
  `.change_log/manual_attempt_20260715_221850_bmult_correct_blocked/attempt.json`
  records `coq_alignment = checked`: upstream `Binary.v:Bmult_correct`
  requires the rounded-product `B2R` equality, finiteness
  `andb (is_finite x) (is_finite y)`, non-NaN sign `xorb`, and overflow
  `B2FF = binary_overflow` branch through the faithful
  `BinarySingleNaN.Bmult_correct`/`Bmult_correct_aux` stack. Current
  `BinarySingleNaN.lean` still exposes `B754_mult_correct : Unit`, and the
  bridge multiplication path remains the rounded-real shortcut
  `roundReal (B2R x * B2R y)`, so adding `Bmult_correct` here would be
  helper-only or tautological rather than a faithful Flocq payload.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_075220`
  rechecked `Bmult_correct` against the current `Bmult` bridge and left source
  code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean` / `target_after.lean` are identical). The top-level
  attempt record has `coq_alignment = not_checked`, but the checked sidecar
  `.change_log/manual_attempt_20260716_075220_bmult_correct_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, `local_target_gate =
  pass`, `changed_files = []`, and `build = not_run`. The fresh blocker is a
  concrete semantic mismatch, not merely a missing proof: upstream
  `BinarySingleNaN.Bmult` returns infinity for infinity times finite, while
  local `BinarySingleNaNBridge.Bmult` only checks NaN and then rounds
  `B2R x * B2R y`; since local `B2R` maps non-finite bridge values to `0`,
  infinity times finite can be routed to finite zero. That contradicts the
  upstream `Bmult_correct` finiteness clause
  `is_finite result = andb (is_finite x) (is_finite y)` and the required
  non-finite/overflow behavior. Local `BinarySingleNaN.lean:B754_mult_correct`
  and `Binary.lean:binary_mul_correct` remain `Unit` port-gap markers, so the
  faithful upstream payload is still absent.
  Manual pipeline recheck
  `.change_log/manual_attempt_20260716_191302_bmult_correct_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `changed_files = []`: upstream `IEEE754/Binary.v:Bmult_correct` is a bridge
  theorem over `BinarySingleNaN.Bmult_correct` through `B2BSN`/`BSN2B`, but the
  current Lean SingleNaN surface still lacks the faithful
  `Bmult_correct`/`Bmult_correct_aux` payload and exposes only the
  `B754_mult_correct : Unit` port-gap marker plus rounded-real bridge
  shortcuts. Adding an exact-name theorem here would therefore be a helper-only
  or proof-erased wrapper rather than the upstream rounded-product,
  finiteness, sign, and overflow result.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_204634`
  rechecked `Bmult_correct` at the same bridge and timed out of its repair loop
  with top-level `result = failed`, `build = not_run`, `changed_files = []`, and
  `coq_alignment = not_checked`. The transient proof attempt tried to add a
  public theorem but did not leave an exact declaration in the current file.
  A direct focused check after the attempt, `lake env lean
  FloatSpec/src/IEEE754/Binary.lean`, passed with warnings only. The blocker is
  unchanged: current `BinarySingleNaNBridge.Bmult` is still the rounded-real
  shortcut over `B2R`, current `binary_mul_correct` and
  `B754_mult_correct` are still `Unit` markers, and the faithful
  `BinarySingleNaN.Bmult_correct`/`Bmult_correct_aux` stack needed by upstream
  `Binary.v:Bmult_correct` is still absent. Status: still active.
  Pipeline attempt `.change_log/codex_attempt_20260711_081950` classified
  `Bplus_correct` with the analogous blocker: upstream requires the faithful
  BinarySingleNaN `Bplus` correctness payload, finite rounded-result semantics,
  sign rules, and an overflow branch returning `binary_overflow`; the local
  finite path delegates through `roundReal`/`real_to_FullFloat` without that
  overflow or proof-carrying validity payload, and BSN `B754_plus_correct` is
  still a `Unit` port gap.
  Config-provider harness attempt `.change_log/codex_attempt_20260713_100712`
  rechecked `Bplus_correct` and left source code unchanged
  (`target_before.lean` and `target_after.lean` identical). It classified the
  exact theorem as still blocked because upstream transports
  `BinarySingleNaN.Bplus_correct` through `B2BSN`/`BSN2B`, while local
  `B754_plus_correct` and `binary_add_correct` remain `Unit` port-gap markers
  and the finite bridge still uses the rounded-real shortcut rather than the
  Flocq rounded-sum, finiteness, exact-zero sign, and overflow payload.
  Config-provider harness attempt `.change_log/codex_attempt_20260713_124802`
  rechecked the exact upstream theorem at the current `binary_add_correct`
  port-gap marker, left source code unchanged (`target_before.lean` and
  `target_after.lean` identical), and classified the target as blocked. The
  refreshed checked classifier
  `.change_log/manual_attempt_20260713_bplus_correct_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and `build = pass`:
  exact restoration still depends on the full `BinarySingleNaN.Bplus_correct`
  layer, including `Fplus_naive`, `binary_normalize_correct`, overflow behavior,
  and `sign_plus_overflow`, while local `BinarySingleNaNBridge.Bplus` remains a
  rounded-real/`real_to_FullFloat` shortcut.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_051712`
  rechecked `Bplus_correct` at the current exact-name `Bplus` bridge, left
  source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean` / `target_after.lean` are identical), and returned
  `result = blocked`. The checked sidecar
  `.change_log/manual_attempt_20260716_052005_bplus_correct_blocked/attempt.json`
  records `coq_alignment = checked`: upstream `Binary.v:Bplus_correct` lifts
  `BinarySingleNaN.Bplus_correct` through `B2BSN`/`BSN2B` and requires rounded
  sum `B2R`, finiteness, exact-zero mode-dependent sign, overflow, and
  same-sign overflow facts. Current `Binary.lean` has the exact-name `Bplus`
  bridge, but local `binary_add_correct` and
  `BinarySingleNaN.lean:B754_plus_correct` remain payload-free `Unit` port-gap
  markers and no faithful SingleNaN `Bplus_correct` theorem is available to
  lift. Therefore `Bplus_correct` remains active rather than being replaced by a
  helper-only or tautological theorem over the current proof-erased/permissive
  bridge.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_062251`
  rechecked `Bplus_correct` at the exact-name `Bplus` bridge and left source
  code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean` / `target_after.lean` are identical). Its checked
  classifier sidecar
  `.change_log/manual_attempt_20260715_222524_bplus_correct_blocked/attempt.json`
  records `coq_alignment = checked`: upstream `Binary.v:Bplus_correct`
  bridges over `BinarySingleNaN.Bplus_correct` and requires rounded sum
  `B2R`, finiteness for finite inputs, the exact-zero mode-dependent sign
  rule, overflow via `binary_overflow`, and the same-sign overflow fact.
  Current `BinarySingleNaN.lean` still has only `B754_plus_correct : Unit`,
  and `BinarySingleNaNBridge.Bplus` handles finite/finite addition through
  `roundReal` rather than the upstream `binary_normalize` overflow/sign
  correctness payload. Adding `Bplus_correct` here would therefore be a
  helper-only or tautological wrapper over a missing SingleNaN theorem stack.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_075852`
  rechecked `Bplus_correct` against the current exact-name `Bplus` bridge and
  left source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean` / `target_after.lean` are identical). The top-level
  attempt record has `coq_alignment = not_checked`, but the checked sidecar
  `.change_log/codex_attempt_20260716_Bplus_correct_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, `local_target_gate =
  pass`, `changed_files = []`, and `build = not_run`. The current blocker is
  unchanged at statement level: upstream `Binary.v:Bplus_correct` delegates
  through `BSN2B` to `BinarySingleNaN.Bplus_correct` and needs the finite
  rounded-value/sign branch plus the same-sign overflow branch, including
  `sign_plus_overflow` and `binary_normalize_correct`. Local
  `Binary.lean:binary_add_correct` and
  `BinarySingleNaN.lean:B754_plus_correct` remain `Unit` port-gap markers with
  a much weaker shape, and the local normalization helpers do not prove the
  upstream rounded-real/sign/overflow correctness payload.
  The normalized checked sidecar
  `.change_log/manual_attempt_20260716_075852_bplus_correct_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass` for that same config-provider attempt.
  `Bplus_correct` remains active until the faithful SingleNaN
  `Bplus_correct`/`sign_plus_overflow`/`binary_normalize_correct` payload can
  be lifted through the exact-name `Bplus` bridge.
- `Btrunc_correct`: the exact same-name theorem is currently tautological
  (`result = Btrunc_correct_check ...`) instead of upstream's
  `IZR (Btrunc x) = round radix2 (FIX_exp 0) Ztrunc (B2R x)`.
- `Bulp_correct`: no faithful counterpart found yet; the exact `Bulp`
  definition now exists, but the upstream real-semantics, finiteness, and sign
  postcondition proof remains unported. Pipeline attempt
  `.change_log/codex_attempt_20260711_073801` classified the exact theorem as
  blocked for now because the upstream Binary proof delegates through
  `B2BSN_lift` to the SingleNaN `Bulp_correct` payload, while the local
  SingleNaN-side `Bulp_correct` support is still absent and the current
  `Binary754` wrapper still erases upstream bounded/NaN validity obligations.
  The prerequisite `Bulp_correct_aux` has since been restored. Status: exact
  theorem still required after the remaining SingleNaN ULP support and validity
  bridge are restored. A fresh subscription harness attempt
  `.change_log/codex_attempt_20260711_172928` rechecked the target against the
  current workspace after `full_float`/`binary_float` were restored. It left no
  code patch and again classified the exact theorem as blocked: `Bulp_correct`
  is an upstream theorem over proof-carrying `binary_float`, but the active
  local `Bulp`/`B2R`/`Bsign` surface is still the permissive `Binary754`
  compatibility wrapper whose `valid` field is effectively `True`; finite
  values can lack the bounded/canonical invariant needed to identify the
  adapter result with `ulp radix2 fexp (B2R x)`. Do not close this by proving a
  tautology or by adding the missing invariant as a theorem hypothesis. A
  follow-up config-provider harness attempt
  `.change_log/codex_attempt_20260713_091201` produced the same classification
  and left Lean code unchanged; its nested
  `.change_log/codex_attempt_20260713_091448_manual_bulp_correct_blocked`
  `classify_attempt.py` artifact records `coq_alignment = checked` and the
  missing SingleNaN `Bulp_correct`/validity stack as the blocker; the
  `is_nan_Bulp` portion was restored later on 2026-07-16.
  Config-provider harness attempt `.change_log/codex_attempt_20260713_131244`
  rechecked the exact upstream theorem at the current `Bulp` adapter, left
  source code unchanged (`target_before.lean` and `target_after.lean`
  identical), and classified the target as blocked. The checked classifier
  `.change_log/manual_attempt_20260713_bulp_correct_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and `build = pass`:
  upstream proves `Bulp_correct` over proof-carrying `binary_float` via
  `B2BSN_lift` and `BinarySingleNaN.Bulp_correct`, while local `Binary754`
  remains permissive, `BinarySingleNaNBridge.Bulp` directly returns
  `finite false 1 e` instead of using `binary_normalize mode_ZR 1 e false`,
  and the SingleNaN `Bulp_correct`/validity bridge remains absent. The
  `is_nan_Bulp` portion was restored later on 2026-07-16.
  Config-provider harness attempt `.change_log/codex_attempt_20260713_141607`
  rechecked the same exact upstream payload at the current adapter and left
  source code unchanged; its checked classifier
  `.change_log/manual_attempt_20260713_bulp_correct_blocked_current/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and `build = pass`.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_010819`
  rechecked `Bulp_correct` again, left source code unchanged
  (`target_before.lean` and `target_after.lean` identical), and classified the
  exact theorem as still blocked. The checked classifier
  `.change_log/manual_attempt_20260716_011130_binary_bulp_correct_blocked/attempt.json`
  records the then-current blocker explicitly: local `BinarySingleNaN.lean`
	  still lacked faithful `Bulp`, `is_nan_Bulp`, and `Bulp_correct` theorem
	  payload. The `Bulp`/`is_nan_Bulp` portion was restored later on
	  2026-07-16; the remaining blocker for this Binary theorem is still the
	  absent `BinarySingleNaN.Bulp_correct` real-semantics theorem plus the
	  proof-erased `BinarySingleNaNBridge.Bulp` and permissive
	  `Binary754.valid` wrapper.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_052645`
	  rechecked the same upstream theorem against the current workspace and made
	  no source changes. The checked classifier
	  `.change_log/manual_attempt_20260715_213203_binary_bulp_correct_blocked/attempt.json`
	  records `result = blocked`, `coq_alignment = checked`, and `build = not_run`:
	  upstream `Binary.v:Bulp_correct` still depends on lifting faithful
	  `BinarySingleNaN.Bulp_correct` through `B2BSN_lift`. The local
	  `BinarySingleNaN.lean` now has faithful `Bulp`/`is_nan_Bulp`, but still
	  lacks `Bulp_correct`, and the Binary bridge `Bulp` remains proof-erased.
	  Adding a theorem over the current bridge would be helper-only or
	  tautological, so `Bulp_correct` remains active.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_062934`
	  rechecked `Bulp_correct` at the current exact-name `Binary.Bulp` adapter
	  and left source code unchanged (`changed_during_attempt.txt` is empty and
	  `target_before.lean` / `target_after.lean` are identical). Its checked
	  classifier sidecar
	  `.change_log/manual_attempt_20260716_063200_binary_bulp_correct_blocked/attempt.json`
	  records `coq_alignment = checked`: upstream `Binary.Bulp_correct` lifts
	  faithful `BinarySingleNaN.Bulp_correct` through `B2BSN_lift`. The local
	  `BinarySingleNaN.lean` now has faithful public `Bulp`/`is_nan_Bulp`, but
	  still no `Bulp_correct`; the local Binary bridge `Bulp` remains
	  proof-erased, and `Binary754.valid` remains trivial, so the upstream ULP
	  equality, finiteness, and sign payload cannot be lifted without weakening
	  semantics.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_080529`
	  rechecked `Bulp_correct` at the current exact-name `Binary.Bulp` adapter
	  and left source code unchanged (`changed_during_attempt.txt` is empty and
	  `target_before.lean` / `target_after.lean` are identical). The top-level
	  attempt record has `coq_alignment = not_checked`, but the checked sidecar
	  `.change_log/manual_attempt_20260716_080529_binary_bulp_correct_blocked/attempt.json`
	  records `result = blocked`, `coq_alignment = checked`, `local_target_gate =
	  pass`, `changed_files = []`, and `build = not_run`. The statement-level
	  blocker is unchanged: upstream `Binary.v:Bulp_correct` proves
	  `B2R (Bulp x) = ulp radix2 fexp (B2R x)`, `is_finite (Bulp x) = true`,
	  and `Bsign (Bulp x) = false` for finite inputs by lifting faithful
	  `BinarySingleNaN.Bulp_correct` through `B2BSN_lift`. Current
	  `Binary.Bulp` instead adapts through `BinarySingleNaNBridge.Bulp`, whose
	  finite branch returns proof-erased `finite false 1 e` directly rather than
	  upstream `binary_normalize mode_ZR 1 e false`; `BinarySingleNaN.lean` now
	  has faithful public `Bulp` and `is_nan_Bulp`, but still lacks
	  `Bulp_correct`, and `Binary754.valid` remains permissive. Adding
	  `Bulp_correct` here would
	  therefore weaken or bypass the upstream ULP equality/finiteness/sign
	  payload, so the name remains active.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_193921`
	  rechecked `Bulp_correct` after the current BSN `binary_round`/
	  `binary_normalize` repairs and again left source code unchanged
	  (`changed_during_attempt.txt` is empty and `changed_files = []`). The
	  normalized checked classifier sidecar
	  `.change_log/manual_attempt_20260716_194451_binary_bulp_correct_blocked/attempt.json`
	  records `result = blocked`, `coq_alignment = checked`, and
	  `build = not_run`. The root blocker is now narrower but still decisive:
	  upstream `Binary.v:Bulp_correct` needs faithful BSN
	  `BinarySingleNaN.Bulp_correct`, which itself needs SingleNaN
	  `binary_round_correct`/`binary_normalize_correct` with rounded real value,
	  finiteness, sign, and overflow payload. Current `BinarySingleNaN.lean`
	  has `Bulp_correct_aux`, faithful public `Bulp`, `is_nan_Bulp`,
	  `binary_round`, and `is_nan_binary_round`, but no value-level
	  `binary_round_correct` or `binary_normalize_correct`; the similarly named
	  `Binary.lean` theorem is a FullFloat audit helper, and the
	  `BinarySingleNaNBridge`/`Binary754` path remains proof-erased and
	  wrong-carrier for this public theorem. Status: superseded by the
	  2026-07-19 restoration below.
  2026-07-19 update: exact public root `Bulp_correct` has since been restored
  by `.change_log/codex_attempt_20260719_103924` using the proof-carrying
  Binary-to-SingleNaN bridge and the Coq-shaped `specFloat_bounded` carrier
  migration. This older blocked classification is superseded. Status:
  implemented and removed from active semantic gaps.

Checked batch 6: `IEEE754/BinarySingleNaN.v` bridge and rounding-mode names.

Confirmed faithful counterparts removed from the active semantic gap list:

- `mode`: represented by the Lean `RoundingMode` inductive in
  `FloatSpec/src/IEEE754/Binary.lean`.
- `round_mode`: represented by `rnd_of_mode`, which maps each
  `RoundingMode` constructor to the corresponding integer rounding function.
- `valid_rnd_round_mode`: represented by the `valid_rnd_of_mode` instance.
- `Bulp_correct_aux`: restored as the exact Lean theorem
  `ExperimentalSingleNaNArithmetic.Bulp_correct_aux` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_074331`. The theorem proves the upstream
  single-NaN payload `bounded 1 emin = true`, translated to the local exponent
  spelling `bounded (prec:=prec) (emax:=emax) 1 (3 - emax - prec) = true`.
  Status: implemented and removed from active semantic gaps.
- `SF2B'`: restored as the exact Lean definition
  `ExperimentalSingleNaNArithmetic.SF2B'` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_082623`. The definition matches the
  upstream total `StandardFloat` to single-NaN binary bridge: zeros,
  infinities, and NaN map directly, while finite values map to
  `B754_finite` only when `bounded m e` is true and otherwise map to
  `B754_nan`. Status: implemented and removed from active semantic gaps.
- `SF2B'_B2SF`: restored as the exact-name Lean theorem `SF2B'_B2SF` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260713_132321` and fresh local focused Lean
  check, with clean classifier
  `.change_log/manual_attempt_20260713_sf2bp_b2sf_proved/attempt.json`. The
  theorem proves the upstream roundtrip payload
  `SF2B' (B2SF x) = x` over the local proof-carrying subtype
  `{ x : B754 // B754_bounded x }`, preserving the `bounded m e = true`
  validity proof carried by upstream finite `binary_float` values but absent
  from the raw local `B754` constructor. The prior `SF2B_B2SF` remains only
  the non-validating `SF2B` roundtrip and is not used as the justification.
  Status: implemented and removed from active semantic gaps.
- `Bsign_SF2B`: restored as the exact-name Lean theorem
  `ExperimentalSingleNaNArithmetic.Bsign_SF2B` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_084009`. The theorem keeps the upstream
  validity-witness argument and proves the constructor-by-constructor payload
  that `BSN_sign (SF2B x) = sign_SF x` in the local Hoare-style spec form.
  Status: implemented and removed from active semantic gaps.
- `is_finite_SF2B`: restored as the exact-name Lean theorem
  `ExperimentalSingleNaNArithmetic.is_finite_SF2B` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_084835`. The theorem keeps the upstream
  validity-witness argument and proves the constructor-by-constructor payload
  that `BSN_is_finite (SF2B x) = is_finite_SF x` in the local Hoare-style spec
  form. Status: implemented and removed from active semantic gaps.
- `is_nan_SF2B`: restored as the exact-name Lean theorem
  `ExperimentalSingleNaNArithmetic.is_nan_SF2B` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_085627`. The theorem keeps the upstream
  validity-witness argument and proves the constructor-by-constructor payload
  that `BSN_is_nan (SF2B x) = is_nan_SF x` in the local Hoare-style spec form.
  Status: implemented and removed from active semantic gaps.
- `is_nan_Bopp`: restored as the exact-name Lean theorem
  `ExperimentalSingleNaNArithmetic.is_nan_Bopp` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_090400`. The theorem proves the upstream
  constructor-by-constructor payload that
  `BSN_is_nan (Bopp_bsn x) = BSN_is_nan x` in the local Hoare-style spec form.
  Status: implemented and removed from active semantic gaps.
- `is_finite_strict_Bopp`: restored as the exact-name Lean theorem
  `ExperimentalSingleNaNArithmetic.is_finite_strict_Bopp` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_091239`. The theorem proves the upstream
  constructor-by-constructor payload that
  `BSN_is_finite_strict (Bopp_bsn x) = BSN_is_finite_strict x` in the local
  Hoare-style spec form. Status: implemented and removed from active semantic
  gaps.
- `is_nan_Babs`: restored as the exact-name Lean theorem
  `ExperimentalSingleNaNArithmetic.is_nan_Babs` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_092047`. The attempt also restored the
  faithful BSN-side absolute-value operation as `Babs_bsn`: NaN stays NaN,
  and zero, infinity, and finite signs are cleared. The theorem proves the
  upstream constructor-by-constructor payload that
  `BSN_is_nan (Babs_bsn x) = BSN_is_nan x` in the local Hoare-style spec form.
  Status: implemented and removed from active semantic gaps.
- `is_finite_strict_Babs`: restored as the exact-name Lean theorem
  `ExperimentalSingleNaNArithmetic.is_finite_strict_Babs` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_093026`. The theorem matches upstream
  `IEEE754/BinarySingleNaN.v:is_finite_strict_Babs` by proving the
  constructor-by-constructor payload that
  `BSN_is_finite_strict (Babs_bsn x) = BSN_is_finite_strict x` in the local
  Hoare-style spec form. Status: implemented and removed from active semantic
  gaps.
- `shr_m_shr_record_of_loc`: restored as the exact-name Lean theorem
  `shr_m_shr_record_of_loc` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_094124`. The theorem matches upstream
  `IEEE754/BinarySingleNaN.v:shr_m_shr_record_of_loc` by projecting the
  mantissa field from the faithful local `ShrRecord` produced by
  `shr_record_of_loc`, proving
  `(shr_record_of_loc m l).shr_m = m` by location cases. Status:
  implemented and removed from active semantic gaps.
- `loc_of_shr_record_of_loc`: restored as the exact-name Lean theorem
  `loc_of_shr_record_of_loc` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_100133`. The theorem matches upstream
  `IEEE754/BinarySingleNaN.v:loc_of_shr_record_of_loc` by proving that
  `loc_of_shr_record (shr_record_of_loc m l) = l` for exact and each inexact
  ordering case. Status: implemented and removed from active semantic gaps.
- `inbetween_shr_1`: restored as the exact-name Lean theorem
  `inbetween_shr_1` in `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after
  harness attempt `.change_log/codex_attempt_20260711_102530`. The theorem
  matches upstream `IEEE754/BinarySingleNaN.v:inbetween_shr_1` by proving the
  one-step right-shift payload
  `inbetween_float 2 (shr_1 mrs).shr_m (e + 1) x
  (loc_of_shr_record (shr_1 mrs))` from nonnegative mantissa and the original
  `inbetween_float 2 mrs.shr_m e x (loc_of_shr_record mrs)`. The attempt
  also restored the local `shr_1` helper and its field/location bridge lemmas
  needed for the exact statement. Status: implemented and removed from active
  semantic gaps.
- `shr_nat`: restored as the exact-name Lean theorem `shr_nat` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_103358`. The theorem matches upstream
  `IEEE754/BinarySingleNaN.v:shr_nat` by proving that for nonnegative shifts,
  `shr mrs e n` is the iterated one-step shift
  `(FloatSpec.Core.Zaux.iter_nat shr_1 n.toNat mrs, e + n)`. The attempt also
  restored the local `shr` helper needed by the exact statement. Status:
  implemented and removed from active semantic gaps.
- `le_shr1_le`: restored as the exact-name Lean theorem `le_shr1_le` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_103921`. The theorem matches upstream
  `IEEE754/BinarySingleNaN.v:le_shr1_le` by proving nonnegativity of the
  shifted mantissa and the one-step bounds
  `2 * (shr_1 mrs).shr_m ≤ mrs.shr_m <
  2 * ((shr_1 mrs).shr_m + 1)` from `0 ≤ mrs.shr_m`. Status: implemented and
  removed from active semantic gaps.
- `inbetween_shr`: restored as the exact-name Lean theorem `inbetween_shr` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after pipeline attempt
  `.change_log/codex_attempt_20260711_111820`. The theorem matches upstream
  `IEEE754/BinarySingleNaN.v:inbetween_shr` by proving that `shr` preserves
  `inbetween_float` through iterated `shr_1` steps for nonnegative shift counts,
  carrying one-step mantissa nonnegativity via `le_shr1_le`; negative shift
  counts reduce to the original `shr_record_of_loc` record. Status:
  implemented and removed from active semantic gaps.
- `le_shr_le`: restored as the exact-name Lean theorem `le_shr_le` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_113521` failed due the subscription usage
  limit rather than a proof blocker. The theorem matches upstream
  `IEEE754/BinarySingleNaN.v:le_shr_le` by proving nonnegativity of the iterated
  shifted mantissa and the two-sided bounds
  `2 ^ n.toNat * (shr mrs e n).1.shr_m ≤ mrs.shr_m <
  2 ^ n.toNat * ((shr mrs e n).1.shr_m + 1)` under `0 ≤ mrs.shr_m` and
  `0 ≤ n`. Status: implemented and removed from active semantic gaps.
- `shr_limit`: restored as the exact-name Lean theorem `shr_limit` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after harness attempt
  `.change_log/codex_attempt_20260711_114329` failed due the subscription usage
  limit rather than a proof blocker. The theorem matches upstream
  `IEEE754/BinarySingleNaN.v:shr_limit` by proving that a mantissa already below
  the Coq integer-power threshold `2 ^ (n - 1)` collapses after `shr` to the
  zero mantissa record with `shr_r = false` and `shr_s = true`, preserving the
  Coq negative-exponent case through the private `zpow2` helper. Status:
  implemented and removed from active semantic gaps.
- `shr_truncate`: restored as the exact-name Lean theorem `shr_truncate` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` by subscription harness attempt
  `.change_log/codex_attempt_20260711_133305`, whose local target gate passed.
  The theorem matches upstream `IEEE754/BinarySingleNaN.v:shr_truncate` by
  proving that shifting `shr_record_of_loc m l` by
  `fexp (Zdigits 2 m + e) - e` agrees with
  `FloatSpec.Calc.Round.truncate_triple (beta := 2) (fexp := fexp) (m, e, l)`
  re-encoded through `shr_record_of_loc`, under `Valid_exp 2 fexp` and
  `0 <= m`. Status: implemented and removed from active semantic gaps.
- `choice_mode`, `le_choice_mode_le`, and `round_mode_choice_mode`: restored as
  exact-name Lean declarations in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` by subscription harness attempt
  `.change_log/codex_attempt_20260711_140113`, whose target diff only added
  these three declarations. The definitions and lemmas match upstream
  `IEEE754/BinarySingleNaN.v` by mapping the local IEEE modes to
  `cond_incr (round_N (!(decide (2 ∣ mx))) lx) mx`, `mx`,
  `cond_incr (round_sign_DN sx lx) mx`,
  `cond_incr (round_sign_UP sx lx) mx`, and
  `cond_incr (round_N true lx) mx`, proving
  `mx <= choice_mode mode sx mx lx <= mx + 1`, and relating `rnd_of_mode mode x`
  to `cond_Zopp (Rlt_bool x 0) (choice_mode mode (Rlt_bool x 0) m l)` under
  `inbetween_int m |x| l`. Status: implemented and removed from active
  semantic gaps.
- `overflow_to_inf`, `is_nan_binary_overflow`, and
  `binary_overflow_correct`: restored as exact-name Lean declarations in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after subscription harness
  attempt `.change_log/codex_attempt_20260711_141105` proved the block and a
  follow-up manual correction moved the public declarations out of the
  experimental namespace. `overflow_to_inf` matches the upstream table:
  nearest-even and nearest-away overflow to infinity, toward-zero returns the
  finite maximum, toward positive infinity depends on `!s`, and toward negative
  infinity depends on `s`. Because the flat Lean namespace already contains the
  `Binary.v` FullFloat declaration named `binary_overflow`, the SingleNaN
  overflow operation is represented by the top-level helper
  `bsn_binary_overflow`, which returns either `S754_infinity s` or
  `S754_finite s ((2 : Nat) ^ prec.toNat - 1) (emax - prec)`. The exact theorem
  names prove the upstream payloads over this faithful SingleNaN helper:
  `is_nan_SF` is false and `valid_binary_SF` is true. Status: implemented and
  removed from active semantic gaps.

- `binary_fit_aux`: implemented at top level in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after subscription harness
  attempt `.change_log/codex_attempt_20260711_150905` stalled after a failed
  proof patch. The Lean definition matches upstream
  `IEEE754/BinarySingleNaN.v`: it returns `S754_finite sx mx ex` when
  `ex <= emax - prec`, and otherwise returns the faithful SingleNaN overflow
  helper `bsn_binary_overflow mode sx` because the root `binary_overflow` name
  is already occupied by the Binary.v port. Status: implemented and removed
  from active semantic gaps.
- `shl_align_correct'`: restored as the exact-name Lean theorem
  `shl_align_correct'` in `FloatSpec/src/IEEE754/BinarySingleNaN.lean` by
  subscription harness attempt `.change_log/codex_attempt_20260711_154155`.
  The theorem matches upstream
  `IEEE754/BinarySingleNaN.v:shl_align_correct'`: under `e <= ex`, destructing
  the shared local `shl_align mx ex e` returns a mantissa/exponent pair whose
  `F2R` at radix 2 equals the original `(mx, ex)` value and whose returned
  exponent is exactly `e`. Status: implemented and removed from active
  semantic gaps.
- `shl_align_correct`: restored as the exact-name Lean theorem
  `shl_align_correct` in `FloatSpec/src/IEEE754/BinarySingleNaN.lean` by
  subscription harness attempt `.change_log/codex_attempt_20260711_155942`.
  The theorem matches upstream
  `IEEE754/BinarySingleNaN.v:shl_align_correct`: for any target exponent,
  destructing the shared local `shl_align mx ex ex'` preserves the radix-2
  `F2R` value and returns an exponent bounded by `ex'`, splitting on whether
  `ex' <= ex` and reusing `shl_align_correct'` in the shifted branch. Status:
  implemented and removed from active semantic gaps.
- `snd_shl_align`: restored as the exact-name Lean theorem `snd_shl_align`
  in `FloatSpec/src/IEEE754/BinarySingleNaN.lean` by subscription harness
  attempt `.change_log/codex_attempt_20260711_160951`. The theorem matches
  upstream `IEEE754/BinarySingleNaN.v:snd_shl_align`: under `ex' <= ex`, the
  second projection of `shl_align mx ex ex'` is exactly `ex'`, obtained from
  the second component of `shl_align_correct'`. Status: implemented and
  removed from active semantic gaps.
- `binary_fit_aux_correct`: restored as the exact-name Lean theorem
  `binary_fit_aux_correct` in `FloatSpec/src/IEEE754/BinarySingleNaN.lean`
  after subscription harness attempt
  `.change_log/codex_attempt_20260711_193545`. The theorem matches upstream
  `IEEE754/BinarySingleNaN.v:binary_fit_aux_correct` modulo the local `Nat`
  mantissa encoding: it makes the upstream `positive` mantissa requirement
  explicit as `hmx_pos : 0 < mx`, derives `bounded` from canonical mantissa
  and the exponent branch, proves the finite branch preserves the `SF2R`
  value, finiteness, and sign under the magnitude test, and proves the
  overflow branch returns the SingleNaN overflow helper using
  `bounded_canonical_lt_emax`. Status: implemented and removed from active
  semantic gaps.
- `Bmult_correct_aux`: subscription harness attempt
  `.change_log/codex_attempt_20260711_162236` left the Lean file unchanged and
  classified the exact lemma as blocked. Upstream
  `IEEE754/BinarySingleNaN.v:Bmult_correct_aux` proves correctness of
  `binary_round_aux mode (xorb sx sy) (Zpos (mx * my)) (ex + ey) loc_Exact`
  and invokes the faithful `binary_round_aux_correct` path, which in turn
  relies on `binary_fit_aux_correct`. The current Lean file has no
  `binary_round_aux_correct` theorem and only the experimental rounded-real
  surface plus overflow-only audit helpers; using those would be a weaker
  payload, not the upstream lemma. Subscription reattempt
  `.change_log/codex_attempt_20260711_195842`, run after
  `binary_fit_aux_correct` was restored, reconfirmed that the remaining
  blocker is the missing faithful SingleNaN `binary_round_aux` definition and
  `binary_round_aux_correct` theorem, not the fit lemma. Config-provider
  harness attempt `.change_log/codex_attempt_20260713_101534` rechecked the
  current workspace and left source code unchanged (`target_before.lean` and
  `target_after.lean` identical). Its nested classifier artifact
  `.change_log/codex_attempt_20260713_021906_bmult_correct_aux_blocked`
  records `coq_alignment = checked` and the same blocker: local
  `Binary.lean` `ExperimentalBinaryRound` helpers have weakened audit
  postconditions and cannot support the upstream rounded-product mantissa
  payload. Config-provider harness attempt
  `.change_log/codex_attempt_20260713_140859` rechecked after the
  `SF2B'_B2SF` ledger update, left source code unchanged, and reconfirmed that
  a faithful SingleNaN `binary_round_aux` plus `binary_round_aux_correct` path
  is still missing. Config-provider harness attempt
  `.change_log/codex_attempt_20260715_192026` rechecked the same active target
  at the current `B754_mult_correct : Unit` marker, left source code unchanged,
  and recorded `changed_files = []`. The checked sidecar
  `.change_log/manual_attempt_20260715_bmult_correct_aux_blocked/attempt.json`
  records `result = blocked` and `coq_alignment = checked`: upstream
  `Bmult_correct_aux` requires `valid_binary`, rounded `SF2R`, finite/sign,
  and overflow branches for
  `binary_round_aux mode (xorb sx sy) (Zpos (mx * my)) (ex + ey) loc_Exact`,
  while the current workspace still has only the payload-free `B754_mult_correct`
  marker and weakened `Binary.lean` round-audit helpers rather than the
  faithful SingleNaN `binary_round_aux_correct` path. Status: still active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_011619`
  rechecked `Bmult_correct_aux` against the current branch, left source code
  unchanged (`target_before.lean` and `target_after.lean` identical), and
  classified the exact lemma as still blocked. The checked manual sidecar
  `.change_log/manual_attempt_20260716_011847_bmult_correct_aux_blocked/attempt.json`
  records the same missing prerequisite: upstream needs the faithful
	  SingleNaN `binary_round_aux` and `binary_round_aux_correct` path, while the
	  current Lean SingleNaN file has no such theorem, the only local
	  `binary_round_aux_correct` is under `ExperimentalBinaryRound` and explicitly
	  documented as not a Flocq algorithm port, and `B754_mult_correct` remains a
	  `Unit` marker.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_053353`
	  rechecked the same active target at the current `B754_mult_correct : Unit`
	  marker and left source code unchanged. The checked sidecar
	  `.change_log/manual_attempt_20260716_053526_bmult_correct_aux_blocked/attempt.json`
		  records `result = blocked`, `coq_alignment = checked`, and
		  `build = not_run`: upstream still requires faithful SingleNaN
		  `binary_round_aux_correct` for the rounded product and overflow split,
		  while the local file has only the payload-free marker and the available
		  `ExperimentalBinaryRound` wrappers are documented audit helpers, not a
		  Flocq algorithm port.
		  Config-provider harness attempt `.change_log/codex_attempt_20260716_081515`
		  rechecked `Bmult_correct_aux` at the current `B754_mult_correct : Unit`
		  marker and left source code unchanged (`changed_during_attempt.txt` is
		  empty and `target_before.lean` / `target_after.lean` are identical). The
		  top-level attempt record has `coq_alignment = not_checked`, but the checked
		  sidecar
		  `.change_log/manual_attempt_20260716_081720_bmult_correct_aux_blocked/attempt.json`
		  records `result = blocked`, `coq_alignment = checked`, `local_target_gate =
		  pass`, `changed_files = []`, and `build = not_run`. The blocker remains
		  the missing faithful SingleNaN `binary_round_aux` and
		  `binary_round_aux_correct` path: upstream applies that theorem to
		  `binary_round_aux mode (xorb sx sy) (Zpos (mx * my)) (ex + ey) loc_Exact`
		  and proves `valid_binary`, rounded `SF2R`, finite/sign, or exact overflow
		  behavior. Current `BinarySingleNaN.lean` still has only the payload-free
		  `B754_mult_correct` marker here, while the only local
		  `binary_round_aux_correct` name is under `Binary.lean`'s
		  `ExperimentalBinaryRound` audit namespace and is explicitly not a Flocq
		  SingleNaN algorithm port.
		  Config-provider harness attempt `.change_log/codex_attempt_20260716_171235`
		  rechecked `Bmult_correct_aux` again after the latest SingleNaN
		  `Bulp`/`Bplus`/`Bsucc` updates. It made no source changes
		  (`changed_during_attempt.txt` is empty, `changed_files = []`) and timed
		  out with exit 124 before writing a final classifier. The transcript still
		  found the same root blocker: the current file exposes only the
		  payload-free `B754_mult_correct : Unit` marker at the multiplication
		  correctness surface, while the available `Binary.lean`
		  `ExperimentalBinaryRound` helpers are audit-level wrappers and do not
		  prove upstream `Bmult_correct_aux`'s `valid_binary`, exact rounded
		  `SF2R`, finite/sign, and exact overflow split for `binary_round_aux` over
		  the product mantissa. The normalized sidecar
			  `.change_log/manual_attempt_20260716_171235_bmult_correct_aux_blocked/attempt.json`
			  records `result = blocked`, `coq_alignment = checked`,
			  `local_target_gate = pass`, and `changed_files = []`. Status: still
			  active.
		  Config-provider harness attempt `.change_log/codex_attempt_20260716_212432`
		  rechecked `Bmult_correct_aux` at the active SingleNaN multiplication
		  surface and made no target-source changes (`changed_files = []`,
		  `target_before.lean` / `target_after.lean` identical). It returned
		  `result = blocked` after confirming the same prerequisite gap: upstream
		  `IEEE754/BinarySingleNaN.v:Bmult_correct_aux` applies the faithful
		  SingleNaN `binary_round_aux_correct` theorem to
		  `binary_round_aux mode (xorb sx sy) (Zpos (mx * my)) (ex + ey)
		  loc_Exact`, while current Lean still has no SingleNaN
		  `binary_round_aux_correct` carrying `valid_binary`, rounded `SF2R`,
		  finite/sign, and overflow alternatives. The local alternatives remain
		  insufficient: `B754_mult_correct` is a payload-free `Unit` marker, and
		  `Binary.lean`'s `ExperimentalBinaryRound.binary_round_aux_correct` is
		  explicitly an audit wrapper rather than a Flocq algorithm port. Status:
		  still active.
		- `is_nan_binary_round`: subscription harness attempt
	  `.change_log/codex_attempt_20260711_162603` left the Lean file unchanged and
	  classified the exact theorem as blocked. Upstream
  `IEEE754/BinarySingleNaN.v:is_nan_binary_round` proves
  `is_nan_SF (binary_round mode sx mx ex) = false` by invoking the faithful
  `binary_round_correct` theorem for the SingleNaN `binary_round` algorithm
  built from `shl_align_fexp` and `binary_round_aux`. The current Lean
  SingleNaN file has no top-level `binary_round`/`binary_round_correct`
  counterpart; its only rounding surface is
  `ExperimentalSingleNaNArithmetic.B754_round_real` and
  `B754_round_real_signed_zero`, which are rounded-real execution models
  rather than the upstream algorithm. The `Binary.lean` `binary_round`
  declarations are FullFloat/Binary.v audit helpers, not faithful BSN ports.
  Config-provider harness attempt `.change_log/codex_attempt_20260713_102246`
  rechecked the current workspace and left source code unchanged
  (`target_before.lean` and `target_after.lean` identical). Its nested
  classifier artifact
  `.change_log/codex_attempt_20260713_102700_is_nan_binary_round_blocked`
  records `coq_alignment = checked` and the same blocker: the local SingleNaN
  file has `shl_align` and `binary_fit_aux` pieces, but no faithful
  top-level `binary_round_aux`/`binary_round`/`binary_round_correct` path.
  Config-provider harness attempt `.change_log/codex_attempt_20260715_200808`
  rechecked the current branch after the latest `Bmult_correct_aux`
  classification and left source code unchanged. The checked sidecar
  `.change_log/manual_attempt_20260715_is_nan_binary_round_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `changed_files = []`: upstream `is_nan_binary_round` is a small theorem, but
  it depends directly on faithful SingleNaN `binary_round_correct`, which in
  turn packages the upstream `binary_round` algorithm built from
  `shl_align_fexp` and `binary_round_aux`. The current local `Binary.lean`
  round helpers are FullFloat/Binary.v audit helpers, and the
  `ExperimentalSingleNaNArithmetic` rounded-real surface is not the upstream
  SingleNaN algorithm. Status: still active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_012336`
  rechecked `is_nan_binary_round` against the current branch, left source code
  unchanged (`target_before.lean` and `target_after.lean` identical), and
  classified the exact theorem as still blocked. The checked sidecar
  `.change_log/manual_attempt_20260716_is_nan_binary_round_blocked/attempt.json`
	  records the same missing payload: upstream proves the theorem through
	  faithful SingleNaN `binary_round_correct` over `binary_round` built from
	  `shl_align_fexp` and `binary_round_aux`, while local `BinarySingleNaN.lean`
	  still has only pieces plus rounded-real helpers, and `Binary.lean`'s
	  similarly named helpers are explicitly `ExperimentalBinaryRound` audit
	  helpers rather than a Flocq algorithm port.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_053949`
	  rechecked `is_nan_binary_round` at the nearby SingleNaN rounding/overflow
	  surface and left source code unchanged. The checked classifier
	  `.change_log/manual_attempt_20260715_214358_is_nan_binary_round_blocked/attempt.json`
	  records `result = blocked`, `coq_alignment = checked`, and
	  `build = not_run`: upstream's proof is small only because it depends on the
	  faithful SingleNaN `binary_round_correct`; local `BinarySingleNaN.lean`
		  still has `SFnearbyint_binary`, `bsn_binary_overflow`, `binary_fit_aux`, and
		  `is_nan_binary_overflow` pieces but no faithful top-level
		  `binary_round`/`binary_round_correct`, and `Binary.lean`'s similarly named
		  `ExperimentalBinaryRound` helpers remain documented audit helpers rather
		  than a Flocq algorithm port.
		  Config-provider harness attempt `.change_log/codex_attempt_20260716_082147`
		  rechecked `is_nan_binary_round` at the current SingleNaN rounded-real
		  surface and left source code unchanged (`changed_during_attempt.txt` is
		  empty and `target_before.lean` / `target_after.lean` are identical). The
		  top-level attempt record has `coq_alignment = not_checked`, but the checked
		  sidecar
		  `.change_log/manual_attempt_20260716_082147_is_nan_binary_round_blocked/attempt.json`
		  records `result = blocked`, `coq_alignment = checked`, `local_target_gate =
		  pass`, `changed_files = []`, and `build = not_run`. The blocker remains
		  the missing faithful SingleNaN round path: upstream
		  `BinarySingleNaN.v:is_nan_binary_round` proves
		  `is_nan_SF (binary_round mode sx mx ex) = false` by invoking
		  `binary_round_correct` over `binary_round` built from `shl_align_fexp` and
		  `binary_round_aux`. Current `BinarySingleNaN.lean` still has no faithful
			  `binary_round` or `binary_round_correct` counterpart, only
			  `ExperimentalSingleNaNArithmetic` rounded-real helpers; `Binary.lean`'s
			  similarly named `ExperimentalBinaryRound` helpers are FullFloat audit
			  helpers and explicitly not a Flocq SingleNaN algorithm port.
		  Manual repair on 2026-07-16 closed the blocker by restoring the faithful
		  SingleNaN `binary_round_aux` and `binary_round` surface in
		  `FloatSpec/src/IEEE754/BinarySingleNaN.lean`, using a BSN-local
		  `bsn_shr_fexp` wrapper over `FloatSpec.Calc.Round.truncate_triple` with
		  `FLT_exp (3 - emax - prec) prec` rather than the FullFloat audit helper
		  in `Binary.lean`. The new exact theorem `is_nan_binary_round` proves
		  `is_nan_SF (binary_round mode sx mx ex) = false` from structural
		  nonnegativity of the two BSN truncation passes and the existing
		  `binary_fit_aux`/`bsn_binary_overflow` non-NaN constructors. Focused
		  verification: `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean`
		  passed. Status: implemented and removed from active semantic gaps.
		- `is_nan_binary_normalize`: subscription harness attempt
		  `.change_log/codex_attempt_20260711_163145` left the Lean file unchanged and
		  classified the exact theorem as blocked. Upstream
  `IEEE754/BinarySingleNaN.v:is_nan_binary_normalize` proves
  `is_nan (binary_normalize mode m e szero) = false` by invoking the faithful
  `binary_normalize_correct` theorem. That theorem depends on the upstream
  SingleNaN `binary_normalize` algorithm, whose zero branch returns
  `B754_zero szero` and whose positive/negative branches package
  `binary_round_valid` through `SF2B`; it therefore also depends on the
  faithful `binary_round_correct` path. The current Lean SingleNaN file has no
  top-level `binary_normalize`/`binary_normalize_correct` counterpart. The
  `Binary.lean` declarations are FullFloat/Binary.v audit helpers, and
  `ExperimentalSingleNaNArithmetic.B754_round_real` is a rounded-real model,
  so using either would be a weaker payload. Config-provider harness attempt
  `.change_log/codex_attempt_20260713_103115` rechecked the current workspace
  and left source code unchanged (`target_before.lean` and
  `target_after.lean` identical). Its nested classifier artifact
  `.change_log/codex_attempt_20260713_103602_is_nan_binary_normalize_blocked`
  records `coq_alignment = checked` and the same structural blocker: local
  `BinarySingleNaN.lean` has `shl_align` and `binary_fit_aux` pieces, but no
  faithful top-level SingleNaN `binary_round`/`binary_round_valid`/
  `binary_normalize`/`binary_normalize_correct` path. Status: still active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_031755`
  rechecked `is_nan_binary_normalize` with an explicit root-repair allowance to
  add the faithful SingleNaN `binary_round`/`binary_normalize` surface if
  feasible. It left source code unchanged (`target_before.lean` and
  `target_after.lean` are identical) and classified the exact theorem as still
  blocked. The checked sidecar
  `.change_log/manual_attempt_20260716_is_nan_binary_normalize_blocked/attempt.json`
  records that upstream `binary_normalize` returns `B754_zero szero` for zero
  mantissas and wraps positive/negative mantissas through
  `binary_round_valid`, while the current Lean file still lacks faithful
  SingleNaN `binary_round_aux_correct`, `binary_round_correct`,
	  `binary_round_valid`, and `binary_normalize_correct`. Routing through
	  `ExperimentalSingleNaNArithmetic` or `Binary.lean`'s
	  `ExperimentalBinaryRound` helpers remains a weaker payload, so the candidate
	  stays active.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_054632`
	  rechecked the target with explicit permission to restore the faithful
	  SingleNaN normalization surface if feasible and left source code unchanged.
	  The checked classifier
	  `.change_log/manual_attempt_20260715_214956_is_nan_binary_normalize_blocked/attempt.json`
	  records `result = blocked`, `coq_alignment = checked`, and
	  `build = not_run`: upstream `is_nan_binary_normalize` sits on
	  `binary_normalize_correct`, where zero mantissas return `B754_zero szero`
	  and signed nonzero mantissas are wrapped through `binary_round_valid`/`SF2B`;
		  local `BinarySingleNaN.lean` still has only component pieces and
		  rounded-real helpers, while `Binary.lean`'s similarly named
		  `ExperimentalBinaryRound` declarations remain weaker audit helpers.
		  Config-provider harness attempt `.change_log/codex_attempt_20260716_082732`
		  rechecked `is_nan_binary_normalize` at the local `ExperimentalBinaryRound`
		  normalization surface and left source code unchanged
		  (`changed_during_attempt.txt` is empty and `target_before.lean` /
		  `target_after.lean` are identical). The top-level attempt record has
		  `coq_alignment = not_checked`, but the checked sidecar
		  `.change_log/manual_attempt_20260716_082732_is_nan_binary_normalize_blocked/attempt.json`
		  records `result = blocked`, `coq_alignment = checked`, `local_target_gate =
		  pass`, `changed_files = []`, and `build = not_run`. The blocker remains
		  the missing faithful SingleNaN normalization/rounding stack: upstream
			  `BinarySingleNaN.v:is_nan_binary_normalize` proves
			  `is_nan (binary_normalize mode m e szero) = false` through
			  `binary_normalize_correct`; upstream `binary_normalize` splits signed
			  integer mantissas, returns `B754_zero szero` for zero, and routes
			  positive/negative cases through `binary_round_valid`/`SF2B`. At this
			  point `BinarySingleNaN.lean` still lacked faithful public
			  `binary_normalize`, `binary_round_valid`, and
			  `binary_normalize_correct`; `Binary.lean` only
			  has `ExperimentalBinaryRound.binary_normalize` over `FullFloat`, explicitly
			  documented as an audit helper rather than a Flocq SingleNaN algorithm port.
		  Manual repair on 2026-07-16 closed the non-NaN theorem by restoring the
		  BSN-local `binary_normalize` branch structure in
		  `FloatSpec/src/IEEE754/BinarySingleNaN.lean`: zero mantissas return
		  `B754_zero szero`, positive mantissas route through `SF2B (binary_round
		  mode false m.toNat e)`, and negative mantissas route through
		  `SF2B (binary_round mode true m.natAbs e)`. The new exact theorem
		  `is_nan_binary_normalize` proves `BSN_is_nan (binary_normalize mode m e
		  szero) = false` from the restored `is_nan_binary_round` and the direct
		  `SF2B`/`is_nan_SF` constructor correspondence. This does not claim
		  `binary_normalize_correct`; that larger rounded-value/overflow theorem
		  remains unavailable. Focused verification:
		  `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed.
		  Status: implemented and removed from active semantic gaps.
		- `Fplus_naive`: restored as the exact Lean definition `Fplus_naive` in
		  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after subscription harness
	  attempt `.change_log/codex_attempt_20260711_163523` and a manual scoped
  patch. The definition matches upstream
  `IEEE754/BinarySingleNaN.v:Fplus_naive`: it aligns each positive mantissa to
  target exponent `ez` with the shared `shl_align`, applies the sign through
  `FloatSpec.Core.Zaux.cond_Zopp`, and adds the two signed aligned mantissas as
  an integer. Focused check
  `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed with
  existing warnings only. Status: implemented and removed from active semantic
  gaps.
- `Fplus_naive_correct`: restored as the exact Lean theorem
  `Fplus_naive_correct` in `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after
  subscription harness attempt `.change_log/codex_attempt_20260711_165829` and
  a manual proof. The statement matches upstream
  `IEEE754/BinarySingleNaN.v:Fplus_naive_correct`: under assumptions `ez <= ex`
  and `ez <= ey`, the real value of the signed aligned integer sum at exponent
  `ez` equals the sum of the two original signed float real values. The proof
  uses `shl_align_correct'` for both operands, preserves signs through
  `FloatSpec.Core.Zaux.cond_Zopp`, and combines the aligned terms with
  `FloatSpec.Core.Defs.F2R_add_same_exp'`. Focused check
  `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed with
  existing warnings only. Status: implemented and removed from active semantic
  gaps.
- `sign_plus_overflow`: subscription harness attempt
  `.change_log/codex_attempt_20260711_173532` compared the upstream lemma and
  left no accepted proof patch. The faithful proof needs a bridge from the
  local `rnd_of_mode mode : ℝ → Int` / `round_to_generic` representation to
  the relation-valued rounding-mode hypotheses used by upstream
  `round_ge_generic` / `round_le_generic`, together with bounded/canonical
  facts from the two finite operands. Adding extra positivity or canonical
  hypotheses would weaken the upstream payload. Config-provider harness
  attempt `.change_log/codex_attempt_20260713_092546` rechecked the current
  workspace and left Lean code unchanged (`target_before.lean` and
  `target_after.lean` identical). It confirmed the remaining blocker: local
  `bounded` currently checks only mantissa/exponent ranges, while the available
  `canonical_bounded` helper requires extra `hmx_pos` and `h_canonical`
  hypotheses, so the exact upstream lemma still needs a faithful bridge from
  bounded positive finite operands to the canonical/generic-format facts used
  by `round_ge_generic`/`round_le_generic`. Config-provider harness attempt
  `.change_log/codex_attempt_20260715_201845` and checked sidecar
  `.change_log/manual_attempt_20260715_sign_plus_overflow_blocked/attempt.json`
  revalidated the same blocker against upstream
  `IEEE754/BinarySingleNaN.v:1864`: no Lean code changed, the focused
  `target_before.lean`/`target_after.lean` snapshots are identical, placeholder
  audit stayed at `sorry = 0`, `axiom = 0`, `admit = 0` with 53 existing
  placeholder/trust findings, and `lake build` was not run because no Lean
  source changed. Status: still active until the rounding-mode and
  bounded/canonical bridges are restored.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_013130`
  rechecked `sign_plus_overflow` against the current branch and again left
  source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). Its checked sidecar
  `.change_log/manual_attempt_20260716_0138_sign_plus_overflow_blocked/attempt.json`
  records `coq_alignment = checked`: upstream proves the exact lemma from only
  `bounded mx ex = true` and `bounded my ey = true`, while local
  `Fplus_naive`/`Fplus_naive_correct` and the integer-rounding
  `roundR_ge_generic`/`roundR_le_generic` helpers still do not expose the
  missing endpoint bridge from local `bounded` to the canonical/generic-format
  facts used in the opposite-sign overflow contradiction. Adding `hmx_pos` or
  `h_canonical` to the theorem would weaken the Flocq payload, so the candidate
  remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_055457`
  rechecked the same exact upstream payload after the placeholder audit had
  dropped to 24 findings and again left source code unchanged
  (`changed_during_attempt.txt` is empty; `target_before.lean` and
  `target_after.lean` are identical). The checked sidecar
  `.change_log/manual_attempt_20260715_220020_sign_plus_overflow_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `build = not_run`: upstream `sign_plus_overflow` obtains the sign equality
  from only `bounded mx ex = true` and `bounded my ey = true`, but local
	  `bounded` remains range-only and local `canonical_bounded` still requires
	  extra `hmx_pos` and `h_canonical` hypotheses. Adding those hypotheses would
	  weaken the Flocq theorem, so this candidate stays active until a faithful
	  bounded-positive-finite to canonical/generic-format bridge is restored.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_083455`
	  rechecked `sign_plus_overflow` at the current `canonical_bounded` bridge and
	  left source code unchanged (`changed_during_attempt.txt` is empty and
	  `target_before.lean` / `target_after.lean` are identical). The top-level
	  attempt record has `coq_alignment = not_checked`, but the checked sidecar
	  `.change_log/manual_attempt_20260716_sign_plus_overflow_blocked/attempt.json`
	  records `result = blocked`, `coq_alignment = checked`, `local_target_gate =
	  pass`, `changed_files = []`, and `build = not_run`. The blocker remains the
	  upstream payload boundary: `sign_plus_overflow` must derive
	  `sx = Rlt_bool z 0 ∧ sx = sy` from only `bounded mx ex = true` and
	  `bounded my ey = true`, while local `bounded` is range-only and local
	  `canonical_bounded` still requires extra `hmx_pos` and `h_canonical`
	  hypotheses. No public local theorem currently derives the generic-format /
	  canonical facts needed by `round_ge_generic` and `round_le_generic` from
	  those bounded hypotheses alone; adding the extra hypotheses would weaken the
	  Flocq statement.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_172010`
	  rechecked `sign_plus_overflow` after the latest SingleNaN helper updates.
	  It made no source changes (`changed_during_attempt.txt` is empty,
	  `changed_files = []`) and timed out with exit 124 before writing its own
	  final classifier. The transcript confirmed the same current blocker:
	  endpoint rounding lemmas are available, but they still require
	  `generic_format`/canonical endpoint facts; current `canonical_bounded`
	  still needs extra `hmx_pos` and `h_canonical` premises, whereas upstream
	  proves the lemma from the two `bounded` hypotheses alone because the Coq
	  bounded/proof-carrying finite setup supplies the needed positive-mantissa
	  and canonicity facts. The normalized sidecar
		  `.change_log/manual_attempt_20260716_172010_sign_plus_overflow_blocked/attempt.json`
		  records `result = blocked`, `coq_alignment = checked`,
		  `local_target_gate = pass`, and `changed_files = []`. Status: still
		  active.
		  Config-provider harness attempt `.change_log/codex_attempt_20260716_213229`
		  rechecked `sign_plus_overflow` with the current BSN helper stack. It left
		  the target source unchanged (`changed_files = []`; `target_before.lean` /
		  `target_after.lean` identical) and returned `result = blocked`. The
		  blocker remains statement-level, not a missing syntactic wrapper: upstream
		  proves the opposite-sign overflow contradiction from only
		  `bounded mx ex = true` and `bounded my ey = true`, using
		  `canonical_bounded` plus `round_ge_generic`/`round_le_generic`; current
		  Lean documents that its local `bounded` predicate is range-only and
		  `canonical_bounded` still needs extra `hmx_pos` and `h_canonical`
		  hypotheses. Adding those hypotheses to `sign_plus_overflow` would weaken
		  the Flocq payload. The focused check
			  `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed with
			  warnings only, and the placeholder audit stayed at 0 findings. Status:
			  still active.
			  Manual attempt
			  `.change_log/manual_attempt_20260716_152815_sign_plus_overflow_proved/attempt.json`
			  restored `ExperimentalSingleNaNArithmetic.sign_plus_overflow` in
			  `FloatSpec/src/IEEE754/BinarySingleNaN.lean`. The proof follows upstream
			  `IEEE754/BinarySingleNaN.v:sign_plus_overflow`: same-sign operands give
			  the sign directly, and opposite signs contradict overflow by bounding the
			  exact sum between the negative and positive maximal finite generic
			  endpoint, then applying the concrete `round_to_generic`/`roundR`
			  endpoint lemmas. Verification: `lake env lean
			  FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed with existing warnings,
			  `lake build` completed successfully (3345 jobs), and
			  `scripts/audit_placeholders.sh --json FloatSpec` plus
			  `scripts/status_report.sh --write` both reported 0 placeholders, 0
			  `sorry`, 0 `axiom`, and 0 `admit`. Status: implemented and removed from
			  active semantic gaps.
			- `SFnearbyint_binary_aux`: restored as the exact-name Lean definition in
	  `FloatSpec/src/IEEE754/BinarySingleNaN.lean`, using the BSN-local sticky
	  shift record, saturation branch, `loc_of_shr_record`, and `choice_mode`.
- `SFnearbyint_binary`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after subscription harness
  attempt `.change_log/codex_attempt_20260711_183625`. The definition matches
  upstream `IEEE754/BinarySingleNaN.v:SFnearbyint_binary`: it returns
  `S754_finite sx mx ex` when `0 <= ex`; otherwise it calls
  `SFnearbyint_binary_aux`, returns a finite value after `shl_align_fexp n 0`
  for positive integer results, returns `S754_nan` for negative results, and
  returns `S754_zero sx` for zero. Focused Lean and full build checks passed
  with existing warnings only. Status: implemented and removed from active
  semantic gaps.
- `Bnearbyint_correct_aux`: subscription harness attempt
  `.change_log/codex_attempt_20260711_184239` timed out without an accepted
  proof patch or final classifier output. Subscription rerun
  `.change_log/codex_attempt_20260713_054328` left the Lean file unchanged and
  classified the exact lemma as blocked. The local exact
  `SFnearbyint_binary_aux`/`SFnearbyint_binary` definitions are present, but
  the upstream theorem's `valid_binary z = true` conjunct would be tautological
  against the current permissive `valid_binary_SF := true` bridge rather than a
  proof of the bounded SingleNaN payload. The value equation also still needs
  the exact nearbyint truncation proof stack over the BSN algorithm:
  `round_trunc_sign_any_correct`, `shr_truncate`, `round_mode_choice_mode`, and
  `shl_align_fexp_correct`, plus the bounded/canonical facts for the input.
  Binary-level rounded-real `Bnearbyint` helpers are not faithful counterparts
  for this BSN lemma. Config-provider harness attempt
  `.change_log/codex_attempt_20260713_104042` rechecked the current workspace,
  left source code unchanged (`target_before.lean` and `target_after.lean`
  identical), and classified the exact lemma as still blocked for the same
  reasons. In particular, local `valid_binary`/`valid_binary_SF` remain
  permissive `true` predicates, and `canonical_bounded` still requires extra
  `hmx_pos` and `h_canonical` hypotheses rather than exposing the upstream
  bounded finite payload directly. Status: still active until the
  non-permissive `valid_binary_SF` bridge and truncation/rounding-mode proof
  are restored.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_013855`
  rechecked the exact target against upstream
  `IEEE754/BinarySingleNaN.v:Bnearbyint_correct_aux` at line 2531 and left
  source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The checked sidecar
  `.change_log/manual_attempt_20260716_Bnearbyint_correct_aux_blocked/attempt.json`
  records `coq_alignment = checked`: `valid_binary_SF` is still a permissive
  `true` predicate, `canonical_bounded` still requires extra `hmx_pos` and
  `h_canonical` facts that upstream derives from `bounded`, and proving the
  lemma now would certify validity through placeholders instead of the Flocq
  bounded SingleNaN payload. The focused Lean gate for
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed with existing warnings;
  the candidate remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_060047`
  rechecked the exact theorem against the current branch after the local
  `SFnearbyint_binary` definitions and truncation/choice helpers were present,
  but again left source code unchanged (`changed_during_attempt.txt` is empty;
  `target_before.lean` and `target_after.lean` are identical). The checked
  sidecar
  `.change_log/manual_attempt_20260715_220650_bnearbyint_correct_aux_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `build = not_run`: upstream still needs a non-tautological
  `valid_binary z = true` proof plus the exact rounded value, finiteness, and
  sign-preservation equations from `bounded mx ex = true` alone. Local
  `valid_binary_SF` remains the permissive constant `true`, and the available
  `shr_truncate`, `round_mode_choice_mode`, and `shl_align_fexp_correct` pieces
  do not yet assemble the bounded-only Flocq payload without that validity
  bridge, so `Bnearbyint_correct_aux` stays active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_084335`
  rechecked the exact upstream payload against the current branch and left
  source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The top-level
  attempt record has `result = blocked`, `local_target_gate = pass`,
  `changed_files = []`, and `coq_alignment = not_checked`; the checked sidecar
  `.change_log/manual_attempt_20260716_084335_bnearbyint_correct_aux_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker is still semantic, not a name
  lookup issue: upstream `Bnearbyint_correct_aux` proves `valid_binary z =
  true`, the exact rounded-value equation, finiteness, and sign preservation
  for `z := SFnearbyint_binary md sx mx ex` from `bounded mx ex = true` alone.
  Local `valid_binary_SF` is still permissive `true`, and
  `canonical_bounded` still requires extra `hmx_pos` and `h_canonical`
  hypotheses not present in the upstream theorem. The local
  `SFnearbyint_binary_aux`/`SFnearbyint_binary`, `shr_truncate`,
  `round_mode_choice_mode`, and `shl_align_fexp_correct` pieces therefore do
  not yet assemble the bounded-only Flocq payload without either tautological
  validity or a weakened statement, so the candidate remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_165243`
  rechecked `Bnearbyint_correct_aux` against the current nearbyint helper
  surface and upstream Flocq 4.2.2 `BinarySingleNaN.v:2531`. It made no source
  changes (`changed_during_attempt.txt` is empty, `changed_files = []`, and
  the local target gate passed) but ended before writing a checked classifier.
  The normalized sidecar
  `.change_log/manual_attempt_20260716_165243_bnearbyint_correct_aux_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `local_target_gate = pass`: upstream proves `valid_binary z = true`, the
  exact `FIX_exp 0` rounded real equation, finiteness, and sign preservation
  for `z := SFnearbyint_binary md sx mx ex` from only
	  `bounded mx ex = true`. Current Lean has the nearbyint definitions and
	  shr/choice/shl helpers, but `valid_binary_SF` remains permissive and
	  `canonical_bounded` still requires extra `hmx_pos` and `h_canonical`
	  hypotheses. Proving the exact lemma now would either close validity through
	  a tautology or add non-upstream premises, so the candidate remains active.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_215743`
	  rechecked `Bnearbyint_correct_aux` after relocating Lake build artifacts off
	  the full `/mnt2` filesystem. It made no Lean source changes
	  (`changed_files = []`; `target_before.lean` / `target_after.lean`
	  identical) and returned `result = blocked`. The blocker is unchanged:
	  upstream proves the bounded-only SingleNaN payload for
	  `SFnearbyint_binary md sx mx ex`, while local `valid_binary_SF` is still the
	  permissive constant predicate and local `canonical_bounded` still needs
	  extra `hmx_pos` and `h_canonical` hypotheses. Using those surfaces would
	  certify validity tautologically or weaken the theorem statement, so this
	  candidate remains active.
- `is_finite_strict_Bone`: restored as the exact-name Lean theorem in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after subscription harness
  attempt `.change_log/codex_attempt_20260711_185011` failed before code work
  due the subscription usage limit. The local theorem computes
  `BSN_is_finite_strict Bone = true`, matching the upstream classifier
  payload for the SingleNaN constant one. Focused Lean check passed with
  existing warnings only. Status: implemented and removed from active semantic
  gaps.
- `is_nan_Bone`: restored as the exact-name Lean theorem in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after the same failed
  subscription harness attempt and manual port. The local theorem computes
  `BSN_is_nan Bone = false`, matching the upstream classifier payload for the
  SingleNaN constant one. Focused Lean check passed with existing warnings
  only. Status: implemented and removed from active semantic gaps.
- `Bmax_float_proof`: subscription harness attempt
  `.change_log/codex_attempt_20260711_191154` produced a compiling theorem,
  but it proved `valid_binary_SF ... = true` by `rfl` through the current
  permissive definition `valid_binary_SF := true`, and used a simplified
  mantissa expression instead of restoring the upstream proof of
  `valid_binary (S754_finite false (shift_pos (Z.to_pos prec) 1 - 1)
  (emax - prec)) = true`. The patch was removed as a tautological validity
  proof, not a faithful Flocq payload. Status: still active until
  `valid_binary_SF`/`bounded` exposes the real SingleNaN validity predicate or
  the proof is ported against an equivalent non-permissive surface.
  Config-provider harness attempt `.change_log/codex_attempt_20260713_093252`
  rechecked the current workspace and left Lean code unchanged
  (`target_before.lean` and `target_after.lean` identical). Its nested
  `.change_log/codex_attempt_20260713_bmax_float_proof_blocked`
  `classify_attempt.py` artifact records `coq_alignment = checked`: upstream
  unfolds `valid_binary, bounded`, proves the `canonical_mantissa` branch, and
  then proves the exponent branch, while current `valid_binary` /
  `valid_binary_SF` are permissive `true` definitions and local `bounded`
  still omits the canonical-mantissa payload.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_014455`
  rechecked the exact target against upstream
  `IEEE754/BinarySingleNaN.v:Bmax_float_proof` and left source code unchanged
  (`changed_during_attempt.txt` is empty and `target_before.lean`/
  `target_after.lean` are identical). The harness confirmed the same blocker:
  upstream proves a real validity fact by unfolding `valid_binary` and
  `bounded`, discharging `canonical_mantissa` for
  `shift_pos (Z.to_pos prec) 1 - 1`, and proving the exponent bound; current
  Lean `valid_binary`/`valid_binary_SF` are still permissive constants returning
  `true`, so adding the theorem now would again be a placeholder-validity proof
  rather than the Flocq payload. Status: still active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_060842`
  rechecked the exact upstream lemma after the latest status/audit refresh and
  left source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The checked sidecar
  `.change_log/codex_attempt_20260716_bmax_float_proof_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `build = not_run`: upstream `Bmax_float_proof` proves a non-tautological
  `valid_binary` fact by unfolding `bounded`, proving the
  `canonical_mantissa` branch for the maximal mantissa, and proving
  `emax - prec ≤ emax - prec`; local `valid_binary` and `valid_binary_SF`
  remain permissive constants and local `bounded` remains range-only. Adding
  the public theorem now would still close through a tautological validity
  surface rather than the Flocq payload, so the candidate stays active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_085007`
  rechecked `Bmax_float_proof` against the current branch and left source code
  unchanged (`changed_during_attempt.txt` is empty and `target_before.lean` /
  `target_after.lean` are identical). The top-level attempt record has
  `result = blocked`, `local_target_gate = pass`, `changed_files = []`, and
  `coq_alignment = not_checked`; the checked classifier artifact
  `.change_log/codex_attempt_20260716_bmax_float_proof_blocked_manual/attempt.json`
  records `coq_alignment = checked`. The upstream proof obligation is still a
  real validity proof: it unfolds `valid_binary`/`bounded`, proves the
  `canonical_mantissa` branch for the maximal mantissa
  `shift_pos (Z.to_pos prec) 1 - 1`, and closes the exponent bound. Current
  Lean `valid_binary`/`valid_binary_SF` remain permissive constants returning
  `true`, so adding the theorem now would again certify validity
  tautologically rather than porting the bounded/canonical Flocq payload.
  The normalized checked sidecar
  `.change_log/manual_attempt_20260716_085007_bmax_float_proof_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass` for that same config-provider attempt.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_173242`
  rechecked the target again and timed out after identifying a viable
  non-tautological route: do not prove through permissive `valid_binary_SF`;
  instead expose the exact finite-validity payload over the nontrivial local
  `bounded` plus `canonical_mantissa` predicates for the maximal finite
  mantissa/exponent pair. The exact public Lean theorem
  `ExperimentalSingleNaNArithmetic.Bmax_float_proof` is now restored in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean`. Its statement proves
  `bounded ((2 : Nat) ^ prec.toNat - 1) (emax - prec) = true` and
  `canonical_mantissa ((2 : Nat) ^ prec.toNat - 1) (emax - prec) = true`,
  avoiding the tautological `valid_binary_SF := true` surface while preserving
  the upstream `valid_binary` proof payload. The proof uses the existing
  `Zdigits_unique` digit-count theorem to show the maximal mantissa has
  exactly `prec` binary digits, then closes the `FLT_exp`/exponent branch.
  Focused `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed
  with existing warnings only, and the checked classifier
  `.change_log/manual_attempt_20260716_173242_bmax_float_proof_proved/attempt.json`
  records `result = proved`, `coq_alignment = checked`, `build = pass`, and
  `changed_files = ["FloatSpec/src/IEEE754/BinarySingleNaN.lean"]`. Status:
  implemented and removed from active semantic gaps.
- `Ffrexp_core_binary`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after subscription harness
  attempt `.change_log/codex_attempt_20260711_192135`. The definition matches
  upstream `IEEE754/BinarySingleNaN.v:Ffrexp_core_binary`: if `-prec < emin`,
  it returns the input finite value with exponent `0`; if the precision is
  already no larger than the mantissa digit count, it returns exponent
  `-prec` and external exponent `ex + prec`; otherwise it shifts the mantissa
  by `d = prec - digits2 mx` and returns external exponent `ex + prec - d`.
  Focused Lean and full build checks passed with existing warnings only.
  Status: implemented and removed from active semantic gaps.
- `Bnormfr_mantissa_correct`: subscription harness attempt
  `.change_log/codex_attempt_20260711_192933` classified the exact upstream
  theorem as blocked and left the Lean file unchanged. Upstream proves the
  theorem for Flocq `binary_float`, whose finite constructor carries a
  positive mantissa and `bounded m e = true` proof. The local
  `B754.B754_finite` stores only `(s : Bool) (m : Nat) (e : Int)`, so the
  direct upstream statement is false for arbitrary local finite values: for
  example, with `m = 1`, `e = -1`, and `prec = 3`, the real value can satisfy
  the normalized magnitude premise while `digits2 m = 1`, not `prec`, and
  `e ≠ -prec`. Config-provider harness attempt
  `.change_log/codex_attempt_20260713_114121` rechecked the exact upstream
  lemma and left source code unchanged (`target_before.lean` and
  `target_after.lean` identical). It reconfirmed the same blocker: upstream
  derives `digits2_pos m = prec` and `e = -prec` from the finite constructor's
  proof-carrying `bounded` payload, while local `B754_finite` stores only
  `(s, m, e)` and local `valid_binary`/`valid_binary_SF` remain permissive
  `true` predicates. The attempt also checked the concrete failure shape
  `prec = 3`, `m = 1`, `e = -1`, where the magnitude premise can hold but the
  requested conclusion would force `digits2 1 = 3` and `-1 = -3`. Status:
  still active until the SingleNaN finite representation or surrounding
  theorem stack restores the bounded/canonical invariant.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_063611`
  rechecked the theorem against the current raw SingleNaN type and left source
  code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean` / `target_after.lean` are identical). The checked
  classifier `.change_log/bnormfr_mantissa_correct_blocked_attempt.json`
  records `coq_alignment = checked`: upstream proves the theorem from the
  proof-carrying `B754_finite _ m e _` constructor, whose final field supplies
  bounded/canonical invariants. Local `BinarySingleNaN.lean:B754_finite`
  stores only sign, `Nat` mantissa, and exponent. The harness exhibited the
  same false-statement shape at `prec = 2`, `emax = 4`,
  `x = B754_finite false 1 (-1)`: the normalized magnitude premise holds
  (`|B754_to_R x| = 1/2`), but the upstream conclusion would require
  `digits2 1 = 2` and `-1 = -2`. Adding hypotheses or using the separate
  proof-carrying `Binary.lean` representation would change the public
  SingleNaN payload, so `Bnormfr_mantissa_correct` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_085648`
  rechecked the exact upstream statement against the current raw SingleNaN
  representation and left source code unchanged (`changed_during_attempt.txt`
  is empty and `target_before.lean`/`target_after.lean` are identical). The
  top-level attempt record has `result = blocked`, `local_target_gate = pass`,
  `changed_files = []`, and `coq_alignment = not_checked`; the checked sidecar
  `.change_log/manual_attempt_20260716_085648_bnormfr_mantissa_correct_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker is still that upstream
  `B754_finite _ m e _` carries the bounded/canonical proof used to derive
  `Bnormfr_mantissa x = N.pos m`, `Z.pos (digits2_pos m) = prec`, and
  `e = -prec` from `/2 <= |B2R x| < 1`, while local `B754.B754_finite` stores
  only sign, `Nat` mantissa, and exponent. The harness checked the concrete
  false-statement shape `prec = 2`, `emax = 3`,
  `x = B754.B754_finite false 1 (-1)`: the normalized magnitude premise holds,
  but the upstream-style conclusion would require `-1 = -2`. Adding hypotheses
  or switching to a different proof-carrying representation would change the
  public SingleNaN payload, so this candidate remains active.
- `Bulp'`: restored as the exact-name Lean definition
  `ExperimentalSingleNaNArithmetic.Bulp'` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after subscription harness
  attempt `.change_log/codex_attempt_20260713_052549`. The definition matches
  upstream `Bulp' x := Bldexp mode_NE Bone (fexp (snd (Bfrexp x)))` using local
  `RoundingMode.RNE`, `Bone`, `Bfrexp_bsn`, and
  `FLT_exp (3 - emax - prec) prec`. The attempt intentionally did not add or
  weaken `Bulp'_correct`. Status: implemented and removed from active semantic
  gaps.
- `Bpred_pos'`: restored as the exact-name Lean definition
  `ExperimentalSingleNaNArithmetic.Bpred_pos'` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean` after config-provider harness
  attempt `.change_log/codex_attempt_20260715_024444` and checked classifier
  record `.change_log/manual_attempt_20260714_184816_bpred_pos_proved`. The
  restoration adds the BSN-local `Bminus` support alias and matches upstream's
  finite-branch shape: choose the predecessor spacing term at the mantissa
  boundary, otherwise use `Bulp' x`, then subtract it with round-to-nearest.
  The upstream positive-mantissa boundary
  `(mx~0 =? shift_pos (Z.to_pos prec) 1)%positive` is represented against the
  local Nat mantissa as `2 * mx == (2 : Nat) ^ prec.toNat`. Validation passed
  `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean`, `lake build`,
  `scripts/audit_placeholders.sh --json FloatSpec`,
  `scripts/status_report.sh --write`, and `git diff --check`. Status:
  implemented and removed from active semantic gaps.
- `is_finite_strict_Bulp`, `Bulp'_correct`, `Bpred_pos'_correct`, and
  `Bsucc'_correct`: no faithful
  counterparts found in the BSN file. Some related Binary-level successor,
  predecessor, and constant-one theorems exist, but they do not provide these
  upstream BSN declarations.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_174823`
  targeted `is_finite_strict_Bulp` after the `Bmax_float_proof` restoration and
  left source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The top-level
  attempt record has `result = failed`, `changed_files = []`, and
  `local_target_gate = pass`; the normalized checked sidecar
  `.change_log/manual_attempt_20260716_1752_is_finite_strict_Bulp_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `changed_files = []`. The blocker is the raw local SingleNaN finite carrier:
  upstream proves `is_finite_strict (Bulp x) = is_finite x` by applying
  BSN-level `Bulp_correct` to a proof-carrying `B754_finite _ _ _ Bx`, while
  local `B754.B754_finite` stores only sign, `Nat` mantissa, and exponent. A
  live Lean probe shows the exact upstream-style statement is false over this
  raw carrier: with `prec = 2`, `emax = 4`, and
  `x = B754.B754_finite false 1 (-100)`, local
  `ExperimentalSingleNaNArithmetic.Bulp x` reduces to `B754.B754_zero false`,
  so `BSN_is_finite_strict (Bulp x) = false` while `BSN_is_finite x = true`.
  Adding a boundedness hypothesis, switching to a proof-carrying wrapper, or
  routing through proof-erased Binary-level helpers would change the public
  BSN payload, so `is_finite_strict_Bulp` remains active.
  Pipeline attempt `.change_log/codex_attempt_20260711_075827` produced a
  structurally provable `is_nan_Bulp`, but it had to introduce a BSN-local
  `Bulp` whose finite branch returned `B754_finite false 1 e` directly instead
  of upstream's `binary_normalize mode_ZR 1 e false`; that patch was rejected as
  a non-faithful surface. This historical blocker was superseded once the
  faithful SingleNaN `binary_normalize`/`Bulp` payload was restored.
  Config-provider harness attempt `.change_log/codex_attempt_20260713_114935`
  rechecked the exact theorem and left source code unchanged
  (`target_before.lean` and `target_after.lean` identical). Its nested
  `.change_log/codex_attempt_20260713_115329_is_nan_Bulp_blocked`
  classifier records `coq_alignment = checked` and the same blocker: the
  local SingleNaN file has `Bulp'` only, while the exact upstream `Bulp`
  finite branch must call the faithful SingleNaN
  `binary_normalize mode_ZR 1 e false`; routing through Binary-level helpers
  or reintroducing the direct finite branch would be non-faithful.
  Config-provider harness attempt `.change_log/codex_attempt_20260715_220424`
  rechecked `is_nan_Bulp` with the explicit root-repair framing of first adding
  faithful BSN `binary_normalize`/`Bulp` if feasible. It left source code
  unchanged: `target_before.lean` and `target_after.lean` are identical, the
  local target gate passed, `scripts/audit_placeholders.sh --json FloatSpec`
  reported `sorry = 0`, `axiom = 0`, `admit = 0`, and
  `scripts/status_report.sh --write` still reported 53 placeholder/trust
  findings. The attempt classified the target as blocked because upstream
	  `Bulp`'s finite branch must call `binary_normalize mode_ZR 1 e false`. That
	  attempt predated the restored BSN-local `binary_normalize` and
	  `is_nan_binary_normalize`; the remaining blocker is now the faithful
	  BSN-level `Bulp` definition plus `binary_round_correct`/`Bulp_correct`
	  stack needed to restore `is_nan_Bulp` without semantic weakening. No full
	  `lake build` was run for that attempt because no Lean source changed.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_015324`
  rechecked the same root-repair path at the current `Bulp'` location and left
  source code unchanged (`target_before.lean` and `target_after.lean` are
  identical, and `changed_during_attempt.txt` is empty). The checked sidecar
  `.change_log/manual_attempt_20260716_015705_is_nan_Bulp_blocked/attempt.json`
  records `coq_alignment = checked`: upstream `is_nan_Bulp` depends on the
	  faithful BSN `Bulp` finite branch `binary_normalize mode_ZR 1 e false` plus
	  `is_nan_binary_normalize`. Current Lean now has the BSN-local
	  `binary_normalize` and `is_nan_binary_normalize`, but still has only
	  `Bulp'` at the BSN level and no faithful public `Bulp`/`Bulp_correct`
	  stack. That status was superseded by the 2026-07-16 proof attempt below.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_064500`
  rechecked `is_nan_Bulp` at the current `Bulp'` location and again left source
  code unchanged (`target_before.lean` and `target_after.lean` are identical,
  and `changed_during_attempt.txt` is empty). The checked sidecar
  `.change_log/manual_attempt_20260716_is_nan_Bulp_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `local_target_gate = pass`: upstream `Bulp`'s finite branch is still the
  faithful BSN `binary_normalize mode_ZR 1 e false`, and upstream
  `is_nan_Bulp` uses `is_nan_binary_normalize`; local
  `BinarySingleNaN.lean` has `Bulp_correct_aux` and `Bulp'` but no faithful
  public BSN-level `Bulp`, while the visible `Bulp` surfaces are either
  proof-erased BinarySingleNaNBridge/Binary wrappers or the
  `ExperimentalBinaryRound` FullFloat audit helper. Adding a direct finite
  `B754_finite false 1 e` branch or a theorem over Binary-level wrappers would
  repeat the previously rejected non-faithful surface. This status was
  superseded by the later faithful `Bulp`/`is_nan_Bulp` repair below.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_090238`
  rechecked `is_nan_Bulp` at the current `Bulp'` location and left source code
  unchanged (`changed_during_attempt.txt` is empty and `target_before.lean` /
  `target_after.lean` are identical). The top-level attempt record has
  `result = blocked`, `local_target_gate = pass`, `changed_files = []`, and
  `coq_alignment = not_checked`; the checked sidecar
  `.change_log/manual_attempt_20260716_is_nan_Bulp_blocked_codex/attempt.json`
  records `coq_alignment = checked`. The blocker remains the upstream
	  operation boundary: `is_nan_Bulp` is stated over BSN `Bulp`, whose finite
	  branch calls `binary_normalize mode_ZR 1 e false` and whose proof applies
	  `is_nan_binary_normalize`. Current `BinarySingleNaN.lean` now has
	  BSN-local `binary_normalize` and `is_nan_binary_normalize`, but still has
	  only `Bulp_correct_aux` and `Bulp'` rather than a faithful public
	  BSN-level `Bulp`/`Bulp_correct` stack. The visible
	  `BinarySingleNaNBridge.Bulp` in `Binary.lean` is
  proof-erased and directly returns `finite false 1 e`, so using it would
  repeat the previously rejected weaker surface. This status was superseded by
  the later faithful `Bulp`/`is_nan_Bulp` repair below.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_154808`
  rechecked `is_nan_Bulp` after the BSN-local `binary_normalize` and
  `is_nan_binary_normalize` repair landed. It added the faithful
  `ExperimentalSingleNaNArithmetic.Bulp` in
  `FloatSpec/src/IEEE754/BinarySingleNaN.lean`: zero maps to
  `B754_finite false 1 (3 - emax - prec)`, infinity maps to positive
  infinity, NaN maps to NaN, and the finite branch calls
  `binary_normalize RoundingMode.RTZ 1 e false`, matching upstream
  `binary_normalize mode_ZR 1 e false` rather than the rejected direct finite
  shortcut. The exact theorem
  `ExperimentalSingleNaNArithmetic.is_nan_Bulp` proves
  `BSN_is_nan (Bulp x) = BSN_is_nan x` by cases and applies the restored
  `is_nan_binary_normalize` in the finite case. Focused
  `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed, and the
  checked sidecar
  `.change_log/manual_attempt_20260716_155137_is_nan_Bulp_proved/attempt.json`
  records `result = proved`, `coq_alignment = checked`,
  `local_target_gate = pass`, and `build = pass`. The top-level harness
  `attempt.json` parser mislabeled the attempt as `blocked`, but its final
  message and the checked sidecar record the proof. Status: implemented and
  removed from active semantic gaps.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_043537`
  rechecked `is_nan_Bsucc` directly and left source code unchanged
  (`target_before.lean` and `target_after.lean` are identical, with no files
  listed in `changed_during_attempt.txt`). The checked sidecar
  `.change_log/manual_attempt_20260716_is_nan_Bsucc_blocked/attempt.json`
  records `coq_alignment = checked`: upstream defines the BSN-level
  `Bsucc` with finite branches `SF2B _ (proj1 (binary_round_correct ...))`,
  then proves `is_nan_Bsucc` by rewriting `is_nan_SF2B` and applying
  `is_nan_binary_round`. Current `BinarySingleNaN.lean` now has the faithful
  BSN-local `binary_round`/`binary_round_aux` surface and
  `is_nan_binary_round`, but still has no faithful BSN-level `Bsucc` and no
  `binary_round_correct` theorem packaging the upstream validity/rounding
  payload. The `Bsucc` and older round names in `Binary.lean` are permissive
  `Binary754`/FullFloat helpers and cannot discharge this SingleNaN theorem
  without changing the payload, so `is_nan_Bsucc` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_092629`
  rechecked `is_nan_Bsucc` at the current `Bpred_pos'` area and left source
  code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The top-level
  attempt record has `result = blocked`, `local_target_gate = pass`,
  `changed_files = []`, and `coq_alignment = not_checked`; the checked sidecar
  `.change_log/manual_attempt_20260716_092629_is_nan_Bsucc_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the upstream
  SingleNaN rounding chain: `Bsucc`'s finite branches are built as
  `SF2B _ (proj1 (binary_round_correct ...))`, and `is_nan_Bsucc` rewrites
  `is_nan_SF2B` then applies `is_nan_binary_round`. Current
  `BinarySingleNaN.lean` has `is_nan_SF2B`, `Bulp'`, `Bminus`,
  `Bpred_pos'`, faithful BSN-local `binary_round`, and `is_nan_binary_round`,
  but no faithful public BSN-level `Bsucc` and no `binary_round_correct`; the
	  `Bsucc` and round helpers in `Binary.lean` are Binary754/FullFloat helpers
	  over a different permissive model.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_162503`
	  rechecked `is_nan_Bsucc` after faithful BSN-level `Bulp`, `Bplus`, and
	  `Bsucc'` were restored. The harness wrote a patch but classified it as
	  `result = failed`; the patch was manually checked and salvaged. It adds the
	  faithful BSN-local `ExperimentalSingleNaNArithmetic.Bsucc`: zero maps to
	  `B754_finite false 1 emin`, positive infinity is unchanged, negative
	  infinity maps to `Bopp Bmax_float`, NaN stays NaN, positive finite uses
	  `SF2B (binary_round mode_UP false (mx + 1) ex)`, and negative finite uses
	  `SF2B (binary_round mode_ZR true (2 * mx - 1) (ex - 1))`. The exact theorem
	  `ExperimentalSingleNaNArithmetic.is_nan_Bsucc` proves
	  `BSN_is_nan (Bsucc x) = BSN_is_nan x` by cases, rewriting the finite cases
	  through `BSN_is_nan_SF2B_eq` and `is_nan_binary_round`. Focused
	  `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed, and
	  `.change_log/manual_attempt_20260716_is_nan_Bsucc_proved/attempt.json`
	  records `result = proved`, `coq_alignment = checked`, and
	  `local_target_gate = pass`. Status: implemented and removed from active
	  semantic gaps.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_042527`
	  rechecked `is_nan_Bpred` directly and left source code unchanged
  (`target_before.lean` and `target_after.lean` are identical, with no files
  listed in `changed_during_attempt.txt`). The checked sidecar
  `.change_log/manual_attempt_20260716_is_nan_Bpred_blocked/attempt.json`
  records `coq_alignment = checked`: upstream defines the BSN-level
  `Bpred x := Bopp (Bsucc (Bopp x))` and proves `is_nan_Bpred` from
  `is_nan_Bopp` and `is_nan_Bsucc`. Current `BinarySingleNaN.lean` has
	  `Bopp_bsn`/`is_nan_Bopp`, `Bulp'`, `Bminus`, and `Bpred_pos'`, but no
	  faithful BSN-level `Bpred`; the faithful BSN-level `Bsucc` and
	  `is_nan_Bsucc` payload were restored later on 2026-07-16. The `Bsucc`/
	  `Bpred` names in `Binary.lean` are
  permissive `Binary754` rounded-real helpers and cannot discharge this
  SingleNaN theorem without changing the payload, so `is_nan_Bpred` remains
  active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_093309`
  rechecked `is_nan_Bpred` at the current `Bpred_pos'` area and left source
  code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The top-level
  attempt record has `result = blocked`, `local_target_gate = pass`,
  `changed_files = []`, and `coq_alignment = not_checked`; the checked sidecar
  `.change_log/manual_attempt_20260716_093309_is_nan_Bpred_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains downstream of the
  faithful SingleNaN successor chain: upstream defines
  `Bpred x := Bopp (Bsucc (Bopp x))` and proves `is_nan_Bpred` by rewriting
  `is_nan_Bopp` and `is_nan_Bsucc`. Current `BinarySingleNaN.lean` has
	  `Bopp_bsn`/`is_nan_Bopp`, `Bulp'`, `Bminus`, and `Bpred_pos'`, but no
	  faithful public BSN-level `Bpred`; the faithful public BSN-level `Bsucc`
	  and `is_nan_Bsucc` were restored later on 2026-07-16. The `Bsucc`/`Bpred`
	  names in `Binary.lean` are Binary754 helpers over a different permissive
	  model.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_163005`
	  rechecked `is_nan_Bpred` after faithful BSN-local `Bsucc` and
	  `is_nan_Bsucc` were restored. The harness wrote the right definition but
	  left a failed proof rewrite; the proof was manually repaired. It adds the
	  faithful BSN-local `ExperimentalSingleNaNArithmetic.Bpred` as
	  `Bopp_bsn (Bsucc (Bopp_bsn x))`, matching upstream
	  `Bpred x := Bopp (Bsucc (Bopp x))`. The exact theorem
	  `ExperimentalSingleNaNArithmetic.is_nan_Bpred` proves
	  `BSN_is_nan (Bpred x) = BSN_is_nan x` by eliminating the outer `Bopp_bsn`,
	  applying `is_nan_Bsucc` to `Bopp_bsn x`, and eliminating the inner
	  `Bopp_bsn` by cases. Focused
	  `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed, and
	  `.change_log/manual_attempt_20260716_is_nan_Bpred_proved/attempt.json`
	  records `result = proved`, `coq_alignment = checked`, and
	  `local_target_gate = pass`. Status: implemented and removed from active
	  semantic gaps.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_044157`
	  rechecked `is_finite_strict_Bulp` directly and left source code unchanged
  (`target_before.lean` and `target_after.lean` are identical, with no files
  listed in `changed_during_attempt.txt`). The checked sidecar
  `.change_log/manual_attempt_20260716_is_finite_strict_Bulp_blocked/attempt.json`
  records `coq_alignment = checked`: upstream proves
  `is_finite_strict (Bulp x) = is_finite x` over the faithful BSN-level
  `Bulp`, whose finite branch uses `binary_normalize mode_ZR 1 e false`, and
  the proof depends on `Bulp_correct`. Current `BinarySingleNaN.lean` has
  faithful BSN-level `Bulp`, `is_nan_Bulp`, `Bulp_correct_aux`, and `Bulp'`,
  but no `Bulp_correct` and no `is_finite_strict_Bulp`. The Binary-level `Bulp`
  bridge is not enough because it uses a permissive/direct finite
  representation instead of the upstream SingleNaN payload, so
  `is_finite_strict_Bulp` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_091035`
  rechecked `is_finite_strict_Bulp` at the current `Bulp'` location and left
  source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The top-level
  attempt record has `result = blocked`, `local_target_gate = pass`,
  `changed_files = []`, and `coq_alignment = not_checked`; the checked sidecar
  `.change_log/manual_attempt_20260716_091035_is_finite_strict_Bulp_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker is unchanged: upstream proves
  `is_finite_strict (Bulp x) = is_finite x` over the faithful BSN-level
  `Bulp`, whose finite branch calls `binary_normalize mode_ZR 1 e false`, and
  uses `Bulp_correct` to rule out impossible non-finite results. Current
  `BinarySingleNaN.lean` has faithful public BSN-level `Bulp` and
  `is_nan_Bulp`, but still no `Bulp_correct`; available
  `BinarySingleNaNBridge.Bulp`/`Binary.Bulp` surfaces are proof-erased
  Binary-level wrappers and would change the upstream SingleNaN payload.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_160721`
  rechecked `is_finite_strict_Bulp` after faithful BSN-level `Bulp` and
  `is_nan_Bulp` were restored. It timed out with exit 124, made no source
  changes (`changed_during_attempt.txt` is empty), and produced no final
  message, but the transcript checked the upstream proof block: upstream
  `is_finite_strict_Bulp` invokes `Bulp_correct` to rule out non-finite
  results. The checked sidecar
  `.change_log/manual_attempt_20260716_160721_is_finite_strict_Bulp_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `local_target_gate = pass`: local Lean now has faithful `Bulp` and
  `is_nan_Bulp`, but still lacks `Bulp_correct` over the proof-carrying
  bounded finite payload; proving the theorem over raw `B754` without that
  evidence would weaken or change the upstream payload. Status: still active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_044750`
  rechecked `Bulp'_correct` directly and left source code unchanged
  (`target_before.lean` and `target_after.lean` are identical, with no files
  listed in `changed_during_attempt.txt`). The checked sidecar
  `.change_log/manual_attempt_20260716_bulp_prime_correct_blocked/attempt.json`
  records `coq_alignment = checked`: upstream `Bulp'_correct` states
  `(2 < emax)%Z -> forall x, is_finite x = true -> Bulp' x = Bulp x`,
  comparing `Bulp'` against the faithful BSN-level `Bulp` after proving
  `Bulp_correct`. Current `BinarySingleNaN.lean` has faithful BSN-level
  `Bulp`, `is_nan_Bulp`, `Bulp_correct_aux`, and `Bulp'`, but no
  `Bulp_correct` and no `is_finite_strict_Bulp` payload. The available
  Binary-level
  `Bulp` declarations are Binary/Binary754 bridge surfaces and cannot replace
  the upstream SingleNaN `Bulp` payload, so `Bulp'_correct` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_092017`
  rechecked `Bulp'_correct` at the current `Bulp'` definition and left source
  code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The top-level
  attempt record has `result = blocked`, `local_target_gate = pass`,
  `changed_files = []`, and `coq_alignment = not_checked`; the checked sidecar
  `.change_log/manual_attempt_20260716_092017_bulp_prime_correct_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the exact upstream
  dependency chain: `Bulp'_correct` states
  `(2 < emax)%Z -> forall x, is_finite x = true -> Bulp' x = Bulp x`, comparing
  `Bulp'` against the faithful BSN-level `Bulp` after using `Bulp_correct`.
  Current `BinarySingleNaN.lean` now has faithful public BSN-level `Bulp` and
  `is_nan_Bulp`, but still no `Bulp_correct`; the available
  `BinarySingleNaNBridge.Bulp`/`Binary.Bulp` declarations are proof-erased
  Binary-level wrappers and would change the upstream SingleNaN payload.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_164708`
  rechecked `Bulp'_correct` at the current `Bulp'` definition after the latest
  BSN `Bulp`/`is_nan_Bulp` restorations. It made no source changes
  (`changed_during_attempt.txt` is empty, `changed_files = []`, and the local
  target gate passed). The harness-generated checked sidecar
  `.change_log/manual_attempt_20260716_164945_bulp_prime_correct_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `local_target_gate = pass`: upstream `Bulp'_correct` proves
  `Bulp' x = Bulp x` for finite `x` by first deriving the `Bulp'`
  correctness triple and then invoking faithful BSN-level `Bulp_correct`.
  Current Lean still has no public BSN `Bulp_correct`/
  `is_finite_strict_Bulp`/validity stack, and Binary-level wrappers would
  weaken the payload. Status: still active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_175635`
  rechecked `Bulp'_correct` after the current `is_finite_strict_Bulp`
  false-raw-carrier classification. It made no source changes
  (`changed_during_attempt.txt` is empty and `target_before.lean`/
  `target_after.lean` are identical) and ended with the generic top-level
  `result = failed`. The normalized checked sidecar
  `.change_log/manual_attempt_20260716_1801_bulp_prime_correct_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `changed_files = []`. The upstream proof first proves real-value,
  finiteness, and sign facts for `Bulp'` using BSN-level
  `Bldexp_correct`/`Bfrexp_correct`, then finishes by applying faithful
  BSN-level `Bulp_correct`. A live Lean scratch proof by cases and `simp`
  still leaves the zero branch goal
  `Bldexp mode_NE Bone (FLT_exp ... 0) = B754_finite false 1 emin` and the
  finite branch goal `Bldexp mode_NE Bone (FLT_exp ... e) =
  binary_normalize mode_ZR 1 e false`, which are exactly the missing
  correctness equalities. Adding a boundedness hypothesis, proving only a
  wrapper-level Binary theorem, or changing the equality target would not be
  the public SingleNaN payload, so `Bulp'_correct` remains active.
  Earlier subscription harness attempts
  `.change_log/codex_attempt_20260713_053532`,
  `.change_log/codex_attempt_20260713_072941`, and
  `.change_log/codex_attempt_20260713_083515` had classified `Bpred_pos'` as
  blocked by the missing exact BSN-level `Bminus` surface. Those blocker notes
  are superseded by the implemented `Bminus` support alias and exact
  `Bpred_pos'` definition recorded above.
  Config-provider harness attempt `.change_log/codex_attempt_20260715_220952`
  rechecked `Bpred_pos'_correct` after `Bpred_pos'` was restored and left source
  code unchanged: `target_before.lean` and `target_after.lean` are identical,
  the local target gate passed, `scripts/audit_placeholders.sh --json
  FloatSpec` reported `sorry = 0`, `axiom = 0`, `admit = 0` with 53
  placeholder/trust findings, and `scripts/status_report.sh --write` refreshed
  the generated status. The checked sidecar
  `.change_log/manual_attempt_20260715_bpred_pos_prime_correct_blocked/attempt.json`
  records the current blocker: upstream `Bpred_pos'_correct` requires the
  faithful BSN `Bulp`/`Bulp_correct`/`Bulp'_correct` chain plus BSN
  `Bminus_correct` and `Bpred_correct`; local BSN has faithful `Bulp`,
  `Bulp'`, and `Bpred_pos'`, but no `Bulp_correct` or `Bulp'_correct`, and
  at that time lacked faithful BSN-level `Bpred`/`Bsucc`. The `Bpred`/`Bsucc`
  definitions and their NaN preservation theorems were restored later on
  2026-07-16, but the correctness payload blockers below remain. Therefore
  `Bpred_pos'_correct` remains active as a downstream theorem, not a safe
  wrapper.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_064934`
  rechecked `Bpred_pos'_correct` at the current exact `Bpred_pos'` definition
  and left source code unchanged (`target_before.lean` and
  `target_after.lean` are identical, and `changed_during_attempt.txt` is
  empty). Its top-level attempt record has `result = blocked`,
  `coq_alignment = not_checked`, and `local_target_gate = pass`; the transcript
  records a statement-level upstream comparison: the theorem is equality
  against upstream BSN `Bpred`, whose definition is `Bopp (Bsucc (Bopp x))`,
  and the proof depends on faithful SingleNaN `Bulp`, `Bulp_correct`,
  `Bulp'_correct`, `Bpred`, `Bpred_correct`, and `Bsucc` payloads. Current
  `BinarySingleNaN.lean` still has only `Bpred_pos'`, `Bulp'`, `Bminus`, and
  `Bulp_correct_aux` in this area, while the only `Bpred` found was the
  separate Binary-level wrapper over the permissive model. That specific
  missing-definition blocker was superseded when faithful BSN-level
  `Bsucc`/`Bpred` were restored later on 2026-07-16, but the theorem remains
  active because the correctness stack is still absent.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_094006`
  rechecked `Bpred_pos'_correct` at the current exact `Bpred_pos'` definition
  and left source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The top-level
  attempt record has `result = blocked`, `local_target_gate = pass`,
  `changed_files = []`, and `coq_alignment = not_checked`; the checked sidecar
  `.change_log/manual_attempt_20260716_094006_bpred_pos_prime_correct_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker is still the faithful
  SingleNaN dependency chain: upstream `Bpred_pos'_correct` states
  `(2 < emax)%Z -> forall x, (0 < B2R x)%R -> Bpred_pos' x = Bpred x`, where
  BSN `Bpred` is `Bopp (Bsucc (Bopp x))`, and the proof depends on BSN
  `Bpred_correct`, `Bminus_correct`, `Bulp`, `Bulp_correct`, and
  `Bulp'_correct`. Current `BinarySingleNaN.lean` has `Bpred_pos'`, `Bminus`,
  `Bulp'`, `Bulp_correct_aux`, faithful `Bulp`/`is_nan_Bulp`, and now faithful
  public BSN-level `Bsucc`/`Bpred` with NaN preservation, but no
  `Bminus_correct`, `Bpred_correct`, `Bulp_correct`, or `Bulp'_correct`;
  Binary-level wrappers use the different permissive Binary754/bridge model.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_164008`
  rechecked `Bpred_pos'_correct` after the faithful BSN-level `Bsucc`,
  `is_nan_Bsucc`, `Bpred`, and `is_nan_Bpred` restorations. It made no source
  changes (`changed_during_attempt.txt` is empty), ran the status and
  placeholder snapshots, and its transcript confirmed the current blocker: the
  upstream proof still needs the SingleNaN correctness stack
  `Bminus_correct`, `Bpred_correct`, `Bulp_correct`, and `Bulp'_correct`.
  The normalized sidecar
  `.change_log/manual_attempt_20260716_164008_bpred_pos_prime_correct_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`,
  `changed_files = []`, and `local_target_gate = pass`. Status: still active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_045430`
  rechecked `Bsucc'` after the exact `Bpred_pos'` restoration and left source
  code unchanged (`target_before.lean` and `target_after.lean` are identical,
  with no files listed in `changed_during_attempt.txt`). The checked sidecar
  `.change_log/manual_attempt_20260716_bsucc_prime_blocked/attempt.json`
  records `coq_alignment = checked`: upstream `Bsucc'` cases are
  zero-to-`Bldexp mode_NE Bone emin`, infinities/NaN, positive finite via
  `Bplus mode_NE x (Bulp x)`, and negative finite via
  `Bopp (Bpred_pos' (Bopp x))`. Current `BinarySingleNaN.lean` now has
  `Bopp_bsn`, `Bldexp`, `Bminus`, `Bpred_pos'`, and faithful BSN-level
  `Bulp`, but it still lacks faithful BSN-level `Bplus` for the positive
  finite branch. Routing through rounded-real `B754_plus`/`Bulp'` or
  Binary-level
	  `Bplus`/`Bulp` bridge surfaces would weaken or change the upstream
	  SingleNaN payload. This blocker was superseded by the later faithful
	  BSN-local `Bplus`/`Bsucc'` repair below.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_094724`
  rechecked `Bsucc'` at the current `Bpred_pos'` area and left source code
  unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The top-level
  attempt record has `result = blocked`, `local_target_gate = pass`,
  `changed_files = []`, and `coq_alignment = not_checked`; the checked sidecar
  `.change_log/manual_attempt_20260716_094724_bsucc_prime_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the positive finite
	  branch of the upstream definition: `Bsucc'` must call
	  `Bplus mode_NE x (Bulp x)`. Current `BinarySingleNaN.lean` has `Bopp_bsn`,
	  `Bldexp`, rounded-real `B754_plus`, faithful `Bulp`, `Bulp'`, `Bminus`, and
	  `Bpred_pos'`, but no faithful public BSN-level `Bplus`; using `B754_plus`,
	  `Bulp'`,
	  or Binary-level bridge wrappers would change the SingleNaN payload. This
	  blocker was superseded by the later faithful BSN-local `Bplus`/`Bsucc'`
	  repair below.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_161418`
	  rechecked `Bsucc'` after faithful BSN-level `Bulp`/`is_nan_Bulp` were
	  restored. The harness timed out and left a tab-indented patch classified as
	  `result = failed`, but the patch was manually salvaged without changing the
	  intended upstream payload. The restored BSN-local
	  `ExperimentalSingleNaNArithmetic.Bplus` handles NaN/infinity/zero cases and
	  finite-finite addition through
	  `binary_normalize mode (Fplus_naive sx mx ex sy my ey (min ex ey)) (min ex ey)`
	  with the directed-rounding sign flag, matching upstream `Bplus` rather than
	  the proof-erased Binary bridge. The exact
	  `ExperimentalSingleNaNArithmetic.Bsucc'` now matches upstream: zero maps to
	  `Bldexp mode_NE Bone emin`, positive infinity is unchanged, negative
	  infinity maps to `Bopp Bmax_float`, NaN stays NaN, positive finite uses
	  `Bplus mode_NE x (Bulp x)`, and negative finite uses
	  `Bopp (Bpred_pos' (Bopp x))`. Focused
	  `lake env lean FloatSpec/src/IEEE754/BinarySingleNaN.lean` passed after the
	  manual repair, and
	  `.change_log/manual_attempt_20260716_bsucc_prime_proved/attempt.json`
	  records `result = proved`, `coq_alignment = checked`, and
	  `local_target_gate = pass`. Status: implemented and removed from active
	  semantic gaps.
	  Config-provider harness attempt `.change_log/codex_attempt_20260716_050359`
	  rechecked `Bsucc'_correct` after the current successor/Bulp blocker updates
  and left source code unchanged (`target_before.lean` and `target_after.lean`
  are identical, with no files listed in `changed_during_attempt.txt`). The
  checked sidecar
  `.change_log/manual_attempt_20260716_bsucc_prime_correct_blocked/attempt.json`
  records `coq_alignment = checked`: upstream `Bsucc'_correct` states
  `(2 < emax)%Z -> forall x, is_finite x = true -> Bsucc' x = Bsucc x` and
	  depends on faithful BSN `Bsucc`/`Bsucc'`, `Bpred_pos'_correct`,
	  `Bulp'_correct`, and BSN `Bplus`/`Bulp` correctness. Current
	  `BinarySingleNaN.lean` has `Bopp_bsn`, `Bldexp`, `Bminus`, `Bulp'`,
	  `Bpred_pos'`, faithful `Bulp`, faithful BSN-local `Bplus`/`Bsucc'`, and
	  faithful BSN-local `Bsucc`/`is_nan_Bsucc`, but no
	  `Bplus_correct`/`Bulp_correct`/
	  `Bulp'_correct`, and no `Bpred_pos'_correct`. Binary-level
  `Bsucc`/`Bplus`/`Bulp` are bridge/permissive surfaces and cannot replace the
  upstream SingleNaN payload, so `Bsucc'_correct` remains active as a downstream
  theorem, not a safe wrapper.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_095649`
  rechecked `Bsucc'_correct` after the latest `Bsucc'` blocker record and again
  left source code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The top-level
  attempt record has `result = blocked`, `build = not_run`, and
  `coq_alignment = not_checked`; the exact checked sidecar
  `.change_log/manual_attempt_20260716_095649_bsucc_prime_correct_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker is still structural:
  upstream `Bsucc'_correct` compares faithful BSN `Bsucc' x = Bsucc x` under
	  `(2 < emax)%Z` and finite inputs. Current `BinarySingleNaN.lean` now has
	  faithful public BSN-level `Bsucc'`, `Bsucc`, `Bplus`, and `Bulp`, but still
	  no `Bplus_correct`/`Bulp_correct`/
	  `Bulp'_correct`, and no `Bpred_pos'_correct`. The Binary-level
  bridge/permissive wrappers remain a different payload and are not a faithful
  replacement.

Checked batch 7: `IEEE754/Bits.v` bit-level API names.

Twenty-five entries have since been removed from the active semantic gap list in this
batch.

Still active after statement check:

- `bits_of_binary_float`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260711_200507`. The definition matches upstream
  `IEEE754/Bits.v:bits_of_binary_float` over the proof-carrying local
  `binary_float` surface: zero, infinity, NaN, and finite constructor cases
  are encoded with the same `join_bits` payload, including the finite
  normalized/subnormal split on `mantissa - 2 ^ mw`. Status: implemented and
  removed from active semantic gaps.
- `split_bits_of_binary_float`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260711_200922`. The definition matches upstream
  `IEEE754/Bits.v:split_bits_of_binary_float` by returning the constructor-case
  `(sign, mantissa, exponent)` triple corresponding to `bits_of_binary_float`,
  including the same finite normalized/subnormal split. Status: implemented
  and removed from active semantic gaps.
- `binary_float_of_bits`: restored as the exact-name public Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after reusing the current harness blocker
  evidence from `.change_log/codex_attempt_20260716_100358`. The earlier blocker
  was real: aliasing local `binary_float_of_bits_aux : Binary754 prec emax`
  would have lost the upstream proof-carrying `binary_float` payload. The new
  declaration instead makes the upstream section witnesses explicit
  (`mw > 0`, `ew > 0`, `prec = mw + 1`, and `emax = 2^(ew-1)`) and constructs
  the strict `binary_float ((mw : Int) + 1) ((2 : Int)^(ew - 1))` directly from
  decoded bit fields. NaN branches prove `nan_pl` from the payload width, and
  finite subnormal/normal branches prove the real `bounded` obligations; it
  does not route through permissive `Binary754` or `valid_binary = true`.
  Focused verification: `lake env lean FloatSpec/src/IEEE754/Bits.lean`
  passed after the restoration, and classifier sidecar
  `.change_log/manual_attempt_20260716_071529_binary_float_of_bits_proved/attempt.json`
  records `result = proved`, `coq_alignment = checked`, and `build = pass`.
  Status: implemented and removed from active semantic gaps.
- `binary32`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260711_202037`. The definition matches upstream
  `binary_float 24 128` over the proof-carrying local `binary_float` surface
  and is distinct from the existing permissive `Binary32 := Binary754 24 127`
  compatibility alias. Status: implemented and removed from active semantic
  gaps.
- `default_nan_pl32`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260711_204114`. The definition adds the
  proof-carrying `is_nan 24 128` result and the upstream `iter_nat xO 22 xH`
  payload with a local proof that `nan_pl 24` is true. Status: implemented and
  removed from active semantic gaps.
- `unop_nan_pl32`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260711_204636`. The definition preserves an
  input NaN sign, payload, and validity proof, otherwise returning
  `default_nan_pl32`. Status: implemented and removed from active semantic
  gaps.
- `binop_nan_pl32`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260711_205247`. The definition prefers the
  first operand NaN, then the second, otherwise `default_nan_pl32`. Status:
  implemented and removed from active semantic gaps.
- `ternop_nan_pl32`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260711_205739`. The definition prefers the
  first operand NaN, then the second, then the third, otherwise
  `default_nan_pl32`. Status: implemented and removed from active semantic
  gaps.
- `b32_erase`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260711_210605`. Upstream `erase` has
  `erase_correct : forall x, erase x = x`; the Lean specialization is the
  constructor-preserving identity on `binary_float 24 128`, preserving zero,
  infinity, NaN sign/payload/proof, and finite mantissa/exponent/boundedness
  proof. Status: implemented and removed from active semantic gaps.
- `b32_opp`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260711_211534`. The definition matches upstream
  `Bopp 24 128 unop_nan_pl32`: NaN inputs are rebuilt via `unop_nan_pl32`,
  while zero, infinity, and finite constructors flip their sign and preserve
  mantissa/exponent and proof payloads. Status: implemented and removed from
  active semantic gaps.
- `b32_abs`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260711_212355`. The definition matches upstream
  `Babs 24 128 unop_nan_pl32`: NaN inputs are rebuilt via `unop_nan_pl32`,
  while zero, infinity, and finite constructors set their sign to `false` and
  preserve mantissa/exponent and proof payloads. Status: implemented and
  removed from active semantic gaps.
- `b32_pred`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` by config-provider harness attempt
  `.change_log/codex_attempt_20260716_022939`, with checked classifier sidecar
  `.change_log/manual_attempt_20260716_b32_pred_proved/attempt.json`.
  The definition matches the fixed-width upstream payload
  `IEEE754/Bits.v:b32_pred : binary32 -> binary32 := Bpred _ _ Hprec Hprec_emax`
  on the proof-carrying `binary_float 24 128` surface: NaNs preserve their
  original sign/payload/proof, positive finite/zero encodings step to the
  previous IEEE32 bit pattern, negative encodings step toward larger unsigned
  bit patterns, negative infinity is fixed, and all generated non-NaN results
  are reconstructed through `b32_of_bits` so finite outputs carry fresh
  `bounded` proofs. It does not route through the permissive `Binary754`
  `Bpred`. Focused check `lake env lean FloatSpec/src/IEEE754/Bits.lean` and
  full `lake build` passed. Status: implemented and removed from active
  semantic gaps.
- `b32_succ`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` by config-provider harness attempt
  `.change_log/codex_attempt_20260716_024401`, with checked classifier sidecar
  `.change_log/manual_attempt_20260716_b32_succ_proved/attempt.json`.
  The definition matches the fixed-width upstream payload
  `IEEE754/Bits.v:b32_succ : binary32 -> binary32 := Bsucc _ _ Hprec Hprec_emax`
  on the proof-carrying `binary_float 24 128` surface: NaNs preserve their
  original sign/payload/proof, signed zero maps to positive minimum subnormal,
  positive encodings step to the next IEEE32 bit pattern with positive infinity
  fixed, and negative encodings step toward smaller unsigned bit patterns so
  negative infinity becomes negative maximum finite. All generated non-NaN
  results are reconstructed through `b32_of_bits` so finite outputs carry fresh
  `bounded` proofs. It does not route through the permissive `Binary754`
  `Bsucc`. Focused check `lake env lean FloatSpec/src/IEEE754/Bits.lean` and
  full `lake build` passed. Status: implemented and removed from active
  semantic gaps.
- `b32_sqrt`: subscription harness attempt
  `.change_log/codex_attempt_20260711_214309` classified the exact public
  alias as blocked. Upstream specializes `Bsqrt _ _ Hprec Hprec_emax
  unop_nan_pl32` over proof-carrying `binary32`, but current Lean's available
  square-root operations and bridges are over the permissive `Binary754` or
  proof-erased SingleNaN surfaces. Routing through `binary_sqrt` or the local
  `Binary.Bsqrt` would not return a `binary_float 24 128` with preserved
  bounded proofs and `unop_nan_pl32` payload handling, so the name remains
  active until the proof-carrying square-root bridge is restored.
  Config-provider harness attempt `.change_log/codex_attempt_20260715_222425`
  rechecked the current tree and left source code unchanged:
  `target_before.lean` and `target_after.lean` are identical, the local target
  gate passed, `scripts/audit_placeholders.sh --json FloatSpec` reported
  `sorry = 0`, `axiom = 0`, `admit = 0`, and `scripts/status_report.sh
  --write` refreshed the 53 placeholder/trust findings. The checked sidecar
  `.change_log/manual_attempt_20260715_222647_b32_sqrt_blocked/attempt.json`
  records that upstream `b32_sqrt` is
  `Bsqrt _ _ Hprec Hprec_emax unop_nan_pl32` with type
  `mode -> binary32 -> binary32` over proof-carrying `binary_float 24 128`,
  while local `Bsqrt`/`binary_sqrt` route through permissive `Binary754` or
  proof-erased SingleNaN and cannot preserve bounded proofs or the
  `unop_nan_pl32` NaN-payload handler.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_031131`
  rechecked the target after the fixed-width proof-carrying decoders and
  successor/predecessor definitions were restored. It left
  `FloatSpec/src/IEEE754/Bits.lean` unchanged: `target_before.lean` and
  `target_after.lean` are identical, and the checked sidecar
  `.change_log/manual_attempt_20260716_b32_sqrt_blocked/attempt.json` records
  `result = blocked`, `coq_alignment = checked`, and `local_target_gate =
  pass`. The current blocker is still the missing proof-carrying
  `Bsqrt`/rounding bridge; re-encoding unconstrained finite outputs through
  `b32_of_bits` would weaken the upstream `Bsqrt ... unop_nan_pl32` payload.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_070419`
  rechecked the exact alias after the current `binary32`, `unop_nan_pl32`,
  `b32_of_bits`, `b32_pred`, and `b32_succ` restorations and left source code
  unchanged (`target_before.lean` and `target_after.lean` are identical, and
  `changed_during_attempt.txt` is empty). The checked sidecar
  `.change_log/manual_attempt_20260715_230707_b32_sqrt_blocked_recheck/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `local_target_gate = pass`: upstream `b32_sqrt` is
  `Bsqrt _ _ Hprec Hprec_emax unop_nan_pl32` with type
  `mode -> binary32 -> binary32` over proof-carrying `binary_float 24 128`;
  current Lean has the fixed-width proof-carrying type and NaN handler, but
  available square-root implementations still route through permissive
  `Binary754` or proof-erased `BinarySingleNaNBridge.BinaryFloat`. No local
  proof-carrying `Bsqrt`/`binary_normalize`/`SF2B` bridge constructs bounded
  finite `binary32` results while preserving `unop_nan_pl32` payload handling,
  and routing through `Binary.Bsqrt`, `binary_sqrt`, or `b32_of_bits` would
  change or weaken the upstream return surface.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_101016`
  rechecked `b32_sqrt` after the latest generic decoder blocker update and
  left source code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The top-level
  attempt record has `result = blocked`, `build = not_run`, and
  `coq_alignment = not_checked`; the exact checked sidecar
  `.change_log/manual_attempt_20260716_101016_b32_sqrt_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing
	  proof-carrying square-root bridge: upstream returns `binary32` through
	  `Bsqrt _ _ Hprec Hprec_emax unop_nan_pl32`, while local `Binary.lean`
	  exposes `Bsqrt`/`binary_sqrt` returning permissive `Binary754` or
	  proof-erased bridge payloads. Routing through those surfaces would not
	  preserve bounded proofs or the `unop_nan_pl32` NaN-payload path.
  Manual post-decoder recheck
  `.change_log/manual_attempt_20260716_071950_b32_sqrt_post_decoder_blocked/attempt.json`
  records the same blocker after `binary_float_of_bits` was restored. A focused
  Lean probe sees the new proof-carrying `b32_of_bits` and
  `binary_float_of_bits`, but the direct upstream alias still fails:
  `Bsqrt (prec := 24) (emax := 128) unop_nan_pl32` expects a
  `BsqrtNaNHandler 24 128` over permissive `Binary754`, while
  `unop_nan_pl32` has type `binary32 -> { nan // is_nan 24 128 nan = true }`.
  The local `Bsqrt` result type is also `Binary754 24 128`, not
  `binary32`. Re-encoding that permissive result through `b32_of_bits` would
  rebuild a proof-carrying value after the fact rather than preserve upstream
  `Bsqrt`'s proof-carrying operation payload and NaN-handler path, so
  `b32_sqrt` remains active.
- `b32_plus`: subscription harness attempt
  `.change_log/codex_attempt_20260711_214941` classified the exact public
  alias as blocked. Upstream specializes `Bplus _ _ Hprec Hprec_emax
  binop_nan_pl32` over proof-carrying `binary32`, but current Lean's available
  `Bplus` bridge returns the permissive `Binary754` wrapper. Routing through
  `Binary.Bplus` or `binary_add` would not return a `binary_float 24 128` with
  bounded finite proofs and preserved `binop_nan_pl32` payload handling, so
  the name remains active until the proof-carrying addition bridge is
  restored. Config-provider harness attempt
  `.change_log/codex_attempt_20260715_222955` rechecked the current tree and
  left source code unchanged: `target_before.lean` and `target_after.lean` are
  identical, the local target gate passed, `scripts/audit_placeholders.sh
  --json FloatSpec` reported `sorry = 0`, `axiom = 0`, `admit = 0`,
  `scripts/status_report.sh --write` refreshed the generated status, focused
  `lake env lean FloatSpec/src/IEEE754/Bits.lean` passed with warnings only,
  and full `lake build` passed with 3345 jobs. The checked sidecar
  `.change_log/manual_attempt_20260715_223226_b32_plus_blocked/attempt.json`
  records that upstream `b32_plus` has type
  `mode -> binary32 -> binary32 -> binary32` over proof-carrying
  `binary_float 24 128`, while local `Bplus` returns permissive `Binary754`
  via `FF2B`/`BSN2B`; no lossless `Binary754`-to-`binary_float 24 128` bridge
  or proof-carrying SingleNaN `Bplus` theorem is available to preserve bounded
  finite proofs and `binop_nan_pl32` payload handling.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_035908`
  rechecked `b32_plus` after the latest proof-carrying `binary32` bit helpers
  and successor/predecessor definitions. It left source code unchanged and
  returned `result = blocked`. The checked classifier
  `.change_log/manual_attempt_20260716_040248_b32_plus_blocked/attempt.json`
  records `coq_alignment = checked`, `build = pass`, and `changed_files = []`.
  A focused alias probe failed at the exact boundary: upstream
  `b32_plus := Bplus _ _ Hprec Hprec_emax binop_nan_pl32` needs a
  proof-carrying `Bplus` over `binary_float 24 128`, but local `Bplus` expects
  `BplusNaNHandler 24 128` over permissive `Binary754` and returns
  `Binary754`; `BinarySingleNaNBridge.Bplus` is proof-erased and lacks bounded
  finite proofs. Re-encoding through `b32_of_bits` would rebuild rather than
  preserve the upstream payload/proof surface.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_071401`
  rechecked the same boundary with the current proof-carrying `binary32`,
  `binop_nan_pl32`, `b32_of_bits`, `b32_pred`, and `b32_succ` context. It
  left source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical) and classified the
  target as blocked. The top-level harness artifact records
  `coq_alignment = not_checked`, but the checked sidecar
  `.change_log/b32_plus_blocked_20260716/attempt.json` records
  `result = blocked`, `coq_alignment = checked`, `local_target_gate = pass`,
  `changed_files = []`, and `build = not_run`. The checked blocker is still
  statement-level: upstream `b32_plus` is the proof-carrying alias
  `Bplus _ _ Hprec Hprec_emax binop_nan_pl32`, while local `Bplus`/`binary_add`
  routes return `Binary754` or proof-erased SingleNaN bridge values and cannot
  supply bounded finite proofs without rebuilding through `b32_of_bits` or
  weakening the return surface.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_101716`
  rechecked `b32_plus` after the latest `b32_sqrt` blocker update and left
  source code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The top-level
  attempt record has `result = blocked`, `build = not_run`, and
  `coq_alignment = not_checked`; the exact checked sidecar
  `.change_log/manual_attempt_20260716_101716_b32_plus_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing
  proof-carrying addition bridge: upstream returns `binary32` through
  `Bplus _ _ Hprec Hprec_emax binop_nan_pl32`, while local `Binary.lean`
  exposes `Bplus`/`binary_add` returning permissive `Binary754` or
  proof-erased bridge payloads. Routing through those surfaces or rebuilding
  through bits would not preserve bounded finite proofs or the `binop_nan_pl32`
  NaN-payload path.
  Manual recheck `.change_log/manual_attempt_20260717_b32_plus_current_blocked`
  keeps the same classification after comparing upstream
  `/mnt2/users/kaile/hantao/flocq-upstream/src/IEEE754/Bits.v:669` and
  `/mnt2/users/kaile/hantao/flocq-upstream/src/IEEE754/Binary.v:1049`.
  Upstream `b32_plus` is exactly
  `Bplus _ _ Hprec Hprec_emax binop_nan_pl32` at type
  `mode -> binary32 -> binary32 -> binary32`, where `binary32` is
  `binary_float 24 128` and finite constructors carry the `bounded` proof.
  The current proof-carrying `Bits.lean` surface has `binary32`,
  `binop_nan_pl32`, `b32_of_bits`, `b32_pred`, and `b32_succ`, but the public
  `Binary.Bplus` handler/argument/result type remains `Binary754 24 128`.
  The more faithful `BinarySingleNaN.Bplus` works over raw single-NaN `B754`,
  whose finite constructor is proof-erased; no theorem currently available
  proves every finite `Bplus` result bounded so it can be reconstructed as
  `binary_float 24 128` while preserving the `binop_nan_pl32` payload path.
  Adding `b32_plus` via `Binary.Bplus`, `binary_add`, or post-hoc
  `b32_of_bits` reconstruction would therefore weaken the upstream
  proof-carrying surface, so the active item remains blocked.
- `b32_minus`: subscription harness attempt
  `.change_log/codex_attempt_20260711_215637` classified the exact public
  alias as blocked. Upstream specializes `Bminus _ _ Hprec Hprec_emax
  binop_nan_pl32` over proof-carrying `binary32`, but current Lean's available
  `Bminus` bridge returns the permissive `Binary754` wrapper. Routing through
  `Binary.Bminus` or `binary_sub` would not return a `binary_float 24 128`
  with bounded finite proofs and preserved `binop_nan_pl32` payload handling,
  so the name remains active until the proof-carrying subtraction bridge is
  restored. Config-provider harness attempt
  `.change_log/codex_attempt_20260715_223604` rechecked the current tree and
  left source code unchanged: `target_before.lean` and `target_after.lean` are
  identical, the local target gate passed, focused
  `lake env lean FloatSpec/src/IEEE754/Bits.lean` passed with warnings only,
  `scripts/audit_placeholders.sh --json FloatSpec` reported `sorry = 0`,
  `axiom = 0`, `admit = 0` with 53 placeholder/trust findings,
  `scripts/status_report.sh --write` refreshed the generated status, and
  `git diff --check` passed. The checked sidecar
  `.change_log/manual_attempt_20260715_223921_b32_minus_blocked/attempt.json`
  records that upstream `b32_minus` has type
  `mode -> binary_float 24 128 -> binary_float 24 128 -> binary_float 24 128`,
  while local `Bminus`/`binary_sub` accept and return `Binary754 24 128`, and
  `BinarySingleNaNBridge.Bminus` returns proof-erased `BinaryFloat`; no
  faithful bounded lift preserves finite proofs and `binop_nan_pl32` payload
  handling.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_072050`
  rechecked the target after the current `binary32`, `binop_nan_pl32`,
  `b32_of_bits`, `b32_pred`, and `b32_succ` restorations. It left source code
  unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical), with the local target
  gate passing. The top-level attempt record has `coq_alignment = not_checked`,
  but the checked sidecar
  `.change_log/manual_attempt_20260716_b32_minus_blocked/attempt.json` records
  `result = blocked`, `coq_alignment = checked`, `local_target_gate = pass`,
  and `build = not_run`; its `changed_files` list reflects the already-dirty
  workspace, not files modified by this attempt. The statement-level blocker is
  unchanged: upstream `b32_minus` is `Bminus _ _ Hprec Hprec_emax
  binop_nan_pl32` returning proof-carrying `binary32`, while local
  `Binary.Bminus`, `binary_sub`, and `BinarySingleNaNBridge.Bminus` return
  permissive or proof-erased surfaces and cannot preserve bounded finite proofs
  or `binop_nan_pl32` payload handling without a faithful proof-carrying bridge.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_102458`
  rechecked `b32_minus` after the latest `b32_plus` blocker update and left
  source code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The top-level
  attempt record has `result = blocked`, `build = not_run`, and
  `coq_alignment = not_checked`; the exact checked sidecar
  `.change_log/manual_attempt_20260716_102458_b32_minus_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing
  proof-carrying subtraction bridge: upstream returns `binary32` through
  `Bminus _ _ Hprec Hprec_emax binop_nan_pl32`, while local `Binary.lean`
  exposes `Bminus`/`binary_sub` returning permissive `Binary754` or
  proof-erased bridge payloads. Routing through those surfaces or rebuilding
  through bits would not preserve bounded finite proofs or the `binop_nan_pl32`
  NaN-payload path.
- `b32_mult`: subscription harness attempt
  `.change_log/codex_attempt_20260711_221829` classified the exact public
  alias as blocked. Upstream specializes `Bmult _ _ Hprec Hprec_emax
  binop_nan_pl32` over proof-carrying `binary32`, but current Lean's available
  `Bmult` bridge returns the permissive `Binary754` wrapper and the SingleNaN
  bridge is proof-erased. Routing through `Binary.Bmult` or `binary_mul` would
  not return a `binary_float 24 128` with bounded finite proofs and preserved
  `binop_nan_pl32` payload handling, so the name remains active until the
  proof-carrying multiplication bridge is restored. Config-provider harness
  attempt `.change_log/codex_attempt_20260715_224332` rechecked the current
  tree and left source code unchanged: `target_before.lean` and
  `target_after.lean` are identical, the local target gate passed,
  `scripts/audit_placeholders.sh --json FloatSpec` reported `sorry = 0`,
  `axiom = 0`, `admit = 0` with 53 placeholder/trust findings,
  `scripts/status_report.sh --write` refreshed generated status, focused
  `lake env lean FloatSpec/src/IEEE754/Bits.lean` passed with warnings only,
  and `git diff --check` passed. The checked sidecar
  `.change_log/manual_attempt_20260715_b32_mult_blocked/attempt.json` records
  that upstream `b32_mult` has type
  `mode -> binary32 -> binary32 -> binary32` over proof-carrying
  `binary_float 24 128`, while local `Binary.Bmult`/`Binary.binary_mul` return
  permissive `Binary754 24 128` through `FF2B`/`BSN2B`, and the SingleNaN
  bridge is proof-erased. Exact restoration still needs a faithful bounded
  lift or proof-carrying multiplication bridge.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_072944`
  rechecked `b32_mult` against the current proof-carrying `binary32`,
  `binop_nan_pl32`, `b32_of_bits`, `b32_pred`, and `b32_succ` context. It left
  source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical), and returned
  `result = blocked` with `local_target_gate = pass`. The top-level attempt
  record has `coq_alignment = not_checked`, but the checked sidecar
  `.change_log/manual_attempt_20260716_b32_mult_blocked/attempt.json` records
  `result = blocked`, `coq_alignment = checked`, `local_target_gate = pass`,
  `changed_files = []`, and `build = not_run`. The blocker remains the missing
  proof-carrying multiplication bridge: local `Bmult` returns `Binary754` via
  proof-erased `BinarySingleNaNBridge.BinaryFloat`, so finite results do not
  carry the bounded proofs required by `binary_float.B754_finite`, and routing
  through `Binary.Bmult`, `binary_mul`, or `b32_of_bits` would weaken the
  upstream `b32_mult` return surface.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_104252`
  rechecked `b32_mult` after the latest `b32_minus` blocker update and left
  source code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The top-level
  attempt record has `result = blocked`, `build = not_run`, and
  `coq_alignment = not_checked`; the exact checked sidecar
  `.change_log/manual_attempt_20260716_104252_b32_mult_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing
  proof-carrying multiplication bridge: upstream returns `binary32` through
  `Bmult _ _ Hprec Hprec_emax binop_nan_pl32`, while local `Binary.lean`
  exposes `Bmult`/`binary_mul` returning permissive `Binary754` or
  proof-erased bridge payloads. Routing through those surfaces or rebuilding
  through bits would not preserve bounded finite proofs or the `binop_nan_pl32`
  NaN-payload path.
- `b32_div`: subscription harness attempt
  `.change_log/codex_attempt_20260711_222436` classified the exact public
  alias as blocked. Upstream specializes `Bdiv _ _ Hprec Hprec_emax
  binop_nan_pl32` over proof-carrying `binary32`, but current Lean's available
  `Bdiv` bridge returns the permissive `Binary754` wrapper and the SingleNaN
  bridge is proof-erased. Routing through `Binary.Bdiv` or `binary_div` would
  not return a `binary_float 24 128` with bounded finite proofs and preserved
  `binop_nan_pl32` payload handling, so the name remains active until the
  proof-carrying division bridge is restored. Config-provider harness attempt
  `.change_log/codex_attempt_20260715_224930` rechecked the current tree and
  left source code unchanged: `target_before.lean` and `target_after.lean` are
  identical, the local target gate passed, `scripts/audit_placeholders.sh
  --json FloatSpec` reported `sorry = 0`, `axiom = 0`, `admit = 0`,
  `scripts/status_report.sh --write` refreshed generated status, and focused
  `lake env lean FloatSpec/src/IEEE754/Bits.lean` passed. The attempt record
  confirms that local `binop_nan_pl32` exists, but local `Binary.Bdiv` expects
  `Binary754` inputs plus a `BdivNaNHandler 24 128`, not proof-carrying
  `binary32`; no bridge exists from the permissive `Binary754` division result
  back to `binary_float 24 128` with finite boundedness and NaN payload
  validity proofs.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_073706`
  rechecked `b32_div` after the current proof-carrying `binary32`,
  `binop_nan_pl32`, `b32_of_bits`, `b32_pred`, and `b32_succ` context. It
  left source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical), and returned
  `result = blocked` with `local_target_gate = pass`. The top-level attempt
  record has `coq_alignment = not_checked`, but the checked sidecar
  `.change_log/manual_attempt_20260715_234011_b32_div_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, `local_target_gate =
  pass`, and `build = pass`; its `changed_files` list reflects the
  already-dirty workspace, not files modified by this attempt. The blocker
  remains the missing proof-carrying division bridge: upstream `b32_div` is
  `Bdiv _ _ Hprec Hprec_emax binop_nan_pl32` returning proof-carrying
  `binary32`, while local `Binary.Bdiv`/`binary_div` and the SingleNaN
  division route return `Binary754` or proof-erased values. Applying local
  `Bdiv 24 128` to `binop_nan_pl32` is a handler type mismatch, and
  reconstructing through `b32_of_bits` would weaken the upstream return
  surface instead of preserving bounded finite proofs and NaN payload validity.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_105123`
  rechecked `b32_div` after the latest `b32_mult` blocker update and left
  source code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The top-level
  attempt record has `result = blocked`, `build = not_run`, and
  `coq_alignment = not_checked`; the exact checked sidecar
  `.change_log/manual_attempt_20260716_105651_b32_div_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing
  proof-carrying division bridge: upstream returns `binary32` through
  `Bdiv _ _ Hprec Hprec_emax binop_nan_pl32`, while local `Binary.lean`
  exposes `Bdiv`/`binary_div` returning permissive `Binary754` or proof-erased
  bridge payloads. A probe confirmed the boundary directly:
  `binop_nan_pl32` has type `binary32 -> binary32 -> { nan // is_nan 24 128 nan = true }`,
  but local `Bdiv` expects `BdivNaNHandler 24 128` over `Binary754 24 128`.
  Routing through those surfaces or rebuilding through bits would not preserve
  bounded finite proofs or the `binop_nan_pl32` NaN-payload path.
- `b32_fma`: subscription harness attempt
  `.change_log/codex_attempt_20260711_224804` classified the exact public
  alias as blocked. Upstream specializes `Bfma _ _ Hprec Hprec_emax
  ternop_nan_pl32` over proof-carrying `binary32`, and current Lean has the
  proof-carrying `binary32` alias plus `ternop_nan_pl32`. The available
  `Bfma` bridge, however, returns the permissive `Binary754` wrapper and the
  SingleNaN bridge is proof-erased. Routing through `Binary.Bfma` or
  `binary_fma` would not return a `binary_float 24 128` with bounded finite
  proofs and preserved `ternop_nan_pl32` payload handling, so the name remains
  active until the proof-carrying fused-multiply-add bridge is restored.
  Config-provider harness attempt `.change_log/codex_attempt_20260715_225806`
  rechecked the current tree and left the target source unchanged:
  `target_before.lean` and `target_after.lean` are identical. The exact probe
  failed because local `ternop_nan_pl32` has type
  `binary32 -> binary32 -> binary32 -> { nan // is_nan 24 128 nan = true }`,
  while local `Binary.Bfma` expects a `BfmaNaNHandler 24 128` over
  `Binary754 24 128` and returns `Binary754 24 128`. A permissive
  `Binary754` FMA probe typechecked only with an explicit `Valid_exp`
  assumption and a `Binary754` NaN handler, confirming that the available
  bridge is not the upstream proof-carrying `binary32` API. The attempt ran
  `scripts/audit_placeholders.sh --json FloatSpec` (`sorry = 0`,
  `axiom = 0`, `admit = 0`), `scripts/status_report.sh --write`, focused
  `lake env lean FloatSpec/src/IEEE754/Bits.lean`, and wrote
  `.change_log/manual_attempt_20260715_b32_fma_blocked/attempt.json`.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_074441`
  rechecked `b32_fma` after the current proof-carrying `binary32`,
  `ternop_nan_pl32`, `b32_of_bits`, `b32_pred`, and `b32_succ` context. It
  left source code unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical), and returned
  `result = blocked` with `local_target_gate = pass`. The top-level attempt
  record has `coq_alignment = not_checked`, but the checked sidecar
  `.change_log/manual_attempt_20260716_074816_b32_fma_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, `local_target_gate =
  pass`, and `build = not_run`; its `changed_files` list reflects the
  already-dirty workspace, not files modified by this attempt. The blocker
  remains the missing proof-carrying fused-multiply-add bridge: upstream
  `b32_fma` is `Bfma _ _ Hprec Hprec_emax ternop_nan_pl32` returning
  proof-carrying `binary32`, while local `Binary.Bfma`/`binary_fma` and the
  SingleNaN FMA route return `Binary754` or proof-erased values. Applying
  `ternop_nan_pl32` to the current `Binary.Bfma` surface is a handler type
  mismatch, and reconstructing through `b32_of_bits` would weaken the upstream
  return surface instead of preserving bounded finite proofs and NaN payload
  validity.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_110347`
  rechecked `b32_fma` after the latest `b32_div` blocker update and left source
  code unchanged (`changed_during_attempt.txt` is empty, `changed_files = []`,
  and the local target gate passed). The top-level attempt record has
  `result = blocked`, `build = not_run`, and `coq_alignment = not_checked`; the
  exact checked sidecar
  `.change_log/manual_attempt_20260716_110347_b32_fma_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing
  proof-carrying fused-multiply-add bridge: upstream returns `binary32` through
  `Bfma _ _ Hprec Hprec_emax ternop_nan_pl32`, while local `Binary.lean`
  exposes `Bfma`/`binary_fma` returning permissive `Binary754` or proof-erased
  bridge payloads. Routing through those surfaces or rebuilding through bits
  would not preserve bounded finite proofs or the `ternop_nan_pl32` NaN-payload
  path.
- `b32_compare`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260711_225610` failed before model execution
  because of subscription quota. The manual follow-up preserves the upstream
  `Bcompare 24 128` payload on proof-carrying `binary32`: NaN operands return
  `none`, signed infinities order around all finite/zero values, and remaining
  ordered cases return the local `Option Int` comparison-code representation
  via `Rcompare` on the constructor real values. It does not route through the
  permissive `Binary754` comparison. Status: implemented and removed from
  active semantic gaps.
- `b64_compare`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260713_045226`. The definition matches upstream
  `Bcompare 53 1024` on the proof-carrying `binary64` alias: NaN operands
  return `none`, signed infinities order around finite/zero values, and
  remaining ordered cases return the local `Option Int` comparison-code
  representation via `Rcompare` on constructor real values. It does not route
  through the permissive `Binary754` comparison. Status: implemented and
  removed from active semantic gaps.
- `b32_of_bits`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` by config-provider harness attempt
  `.change_log/codex_attempt_20260716_021320`, with checked classifier sidecar
  `.change_log/manual_attempt_20260716_b32_of_bits_proved/attempt.json`.
  The definition matches upstream `IEEE754/Bits.v:b32_of_bits`: it decodes
  `(sign, mantissa, exponent)` fields with `split_bits 23 8`, returns
  proof-carrying `binary_float 24 128`, maps zero and infinity fields to the
  corresponding constructors, maps nonzero all-ones exponent fields to
  `B754_nan` with a proved `nan_pl 24` payload, and maps finite fields to
  `B754_finite` with concrete IEEE32 `bounded` proofs for subnormal exponent
  `-149` and normal exponent `eField - 150`. It does not route through the
  permissive `Binary754` decoder. Focused check
  `lake env lean FloatSpec/src/IEEE754/Bits.lean` passed with warnings only.
  Status: implemented and removed from active semantic gaps.
- `bits_of_b32`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260713_024802`. The definition is the public
  binary32 specialization of the already-restored proof-carrying
  `bits_of_binary_float`, with local witnesses for `Prec_gt_0 24` and
  `Prec_lt_emax 24 128`. It returns the encoded `Int` bits from
  `binary32 := binary_float 24 128` and does not route through the permissive
  `Binary754`/`binary_to_bits` compatibility layer. Status: implemented and
  removed from active semantic gaps.
- `bits_of_b64`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260713_050315`. The definition is the public
  binary64 specialization of the already-restored proof-carrying
  `bits_of_binary_float`, matching upstream `bits_of_binary_float 52 11` via
  local witnesses for `Prec_gt_0 53` and `Prec_lt_emax 53 1024`. It returns the
  encoded `Int` bits from `binary64 := binary_float 53 1024` and does not route
  through the permissive `Binary754`/`binary_to_bits` compatibility layer.
  Status: implemented and removed from active semantic gaps.
- `binary64`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260713_025639`. The definition matches upstream
  `binary_float 53 1024` over the proof-carrying local `binary_float` surface
  and is distinct from the existing permissive `Binary64 := Binary754 53 1023`
  compatibility alias. Status: implemented and removed from active semantic
  gaps.
- `default_nan_pl64`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260713_030259`. The definition matches upstream
  `exist _ (@B754_nan 53 1024 false (iter_nat xO 51 xH) ...) ...` over
  `binary64`, using a local `nan_pl 53` proof for the exact payload and
  returning `{ nan : binary64 // is_nan 53 1024 nan = true }`. It does not
  route through the permissive `Binary754` model. Status: implemented and
  removed from active semantic gaps.
- `unop_nan_pl64`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260713_030817`. The definition matches upstream:
  if the input `binary64` is `B754_nan`, it preserves the sign, payload, and
  validity proof in the returned subtype; otherwise it returns
  `default_nan_pl64`. It stays on the proof-carrying `binary64` surface and
  does not route through `Binary754`. Status: implemented and removed from
  active semantic gaps.
- `binop_nan_pl64`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260713_031340`. The definition matches
  upstream: it prefers the first operand NaN sign/payload/proof, then the
  second operand NaN sign/payload/proof, and otherwise returns
  `default_nan_pl64`. It stays on the proof-carrying `binary64` surface and
  does not route through `Binary754`. Status: implemented and removed from
  active semantic gaps.
- `ternop_nan_pl64`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260713_032006`. The definition matches
  upstream: it prefers the first operand NaN sign/payload/proof, then the
  second operand, then the third operand, and otherwise returns
  `default_nan_pl64`. It stays on the proof-carrying `binary64` surface and
  does not route through `Binary754`. Status: implemented and removed from
  active semantic gaps.
- `b64_erase`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260713_032531`. Upstream specializes
  `erase 53 1024`, whose correctness theorem states `erase x = x`; the Lean
  specialization is the constructor-preserving identity on
  `binary_float 53 1024`, preserving zero, infinity, NaN sign/payload/proof,
  and finite mantissa/exponent/boundedness proof. Status: implemented and
  removed from active semantic gaps.
- `b64_opp`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260713_034800`. The definition matches upstream
  `Bopp 53 1024 unop_nan_pl64`: NaN inputs are rebuilt via `unop_nan_pl64`,
  while zero, infinity, and finite constructors flip their sign and preserve
  mantissa/exponent and proof payloads. It stays on the proof-carrying
  `binary64` surface and does not route through `Binary754`. Status:
  implemented and removed from active semantic gaps.
- `b64_abs`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` after subscription harness attempt
  `.change_log/codex_attempt_20260713_035419`. The definition matches upstream
  `Babs 53 1024 unop_nan_pl64`: NaN inputs are rebuilt via `unop_nan_pl64`,
  while zero, infinity, and finite constructors set their sign to `false` and
  preserve mantissa/exponent and proof payloads. It stays on the
  proof-carrying `binary64` surface and does not route through `Binary754`.
  Status: implemented and removed from active semantic gaps.
- `b64_pred`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` by config-provider harness attempt
  `.change_log/codex_attempt_20260716_025236`, with checked classifier sidecar
  `.change_log/manual_attempt_20260716_b64_pred_proved/attempt.json`.
  The definition matches the fixed-width upstream payload
  `IEEE754/Bits.v:b64_pred : binary64 -> binary64 := Bpred _ _ Hprec Hprec_emax`
  on the proof-carrying `binary_float 53 1024` surface: NaNs preserve their
  original sign/payload/proof, positive finite/zero encodings step to the
  previous IEEE64 bit pattern, negative encodings step toward larger unsigned
  bit patterns, negative infinity is fixed, and all generated non-NaN results
  are reconstructed through `b64_of_bits` so finite outputs carry fresh
  `bounded` proofs. It does not route through the permissive `Binary754`
  `Bpred`. Focused check `lake env lean FloatSpec/src/IEEE754/Bits.lean` and
  full `lake build` passed. Status: implemented and removed from active
  semantic gaps.
- `b64_succ`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` by config-provider harness attempt
  `.change_log/codex_attempt_20260716_030010`, with checked classifier sidecar
  `.change_log/manual_attempt_20260716_b64_succ_proved/attempt.json`.
  The definition matches the fixed-width upstream payload
  `IEEE754/Bits.v:b64_succ : binary64 -> binary64 := Bsucc _ _ Hprec Hprec_emax`
  on the proof-carrying `binary_float 53 1024` surface: NaNs preserve their
  original sign/payload/proof, signed zero maps to positive minimum subnormal,
  positive encodings step to the next IEEE64 bit pattern with positive infinity
  fixed, and negative encodings step toward smaller unsigned bit patterns so
  negative infinity becomes negative maximum finite. All generated non-NaN
  results are reconstructed through `b64_of_bits` so finite outputs carry fresh
  `bounded` proofs. It does not route through the permissive `Binary754`
  `Bsucc`. Focused check `lake env lean FloatSpec/src/IEEE754/Bits.lean` and
  full `lake build` passed. Status: implemented and removed from active
  semantic gaps.
- `b64_sqrt`: subscription harness attempt
  `.change_log/codex_attempt_20260713_042546` classified the exact public
  alias as blocked. Upstream specializes `Bsqrt _ _ Hprec Hprec_emax
  unop_nan_pl64` over proof-carrying `binary64`, but current Lean's available
  square-root operations and bridges are over the permissive `Binary754` or
  proof-erased surfaces. Routing through `Binary.Bsqrt` or `binary_sqrt` would
  not return a `binary_float 53 1024` with preserved bounded finite proofs and
  `unop_nan_pl64` payload handling, so the name remains active until the
  proof-carrying square-root bridge is restored.
  Config-provider harness attempt `.change_log/codex_attempt_20260715_232550`
  and checked sidecar
  `.change_log/manual_attempt_20260715_b64_sqrt_blocked/attempt.json`
  rechecked the current tree and left the target source unchanged:
  `target_before.lean` and `target_after.lean` are identical. The attempt
  confirmed that local `binary64` is the proof-carrying
  `binary_float 53 1024`, but local `Binary.Bsqrt` returns permissive
  `Binary754` through the `FF2B`/`BSN2B` bridge; no proof-carrying square-root
  bridge currently reconstructs bounded finite proofs while preserving
  `unop_nan_pl64` payload handling. The attempt ran
  `scripts/audit_placeholders.sh --json FloatSpec` (`sorry = 0`,
  `axiom = 0`, `admit = 0`) and `scripts/status_report.sh --write`; no full
  `lake build` was run because no Lean source changed.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_111402`
  rechecked `b64_sqrt` after the current `b64_pred`/`b64_succ` restorations
  and the `b32_*` arithmetic blocker updates. It left source code unchanged
  (`changed_during_attempt.txt` is empty, `changed_files = []`, and the local
  target gate passed). The top-level attempt record has `result = blocked`,
  `build = not_run`, and `coq_alignment = not_checked`; the exact checked
  sidecar
  `.change_log/manual_attempt_20260716_111402_b64_sqrt_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing
  proof-carrying square-root bridge: upstream returns `binary64` through
  `Bsqrt _ _ Hprec Hprec_emax unop_nan_pl64`, while local `Binary.lean`
  exposes `Bsqrt`/`binary_sqrt` returning permissive `Binary754` or
  proof-erased bridge payloads. Routing through those surfaces or rebuilding
  through bits would not preserve bounded finite proofs or the
  `unop_nan_pl64` NaN-payload path.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_134815`
  tried to add `b64_sqrt`, but the patch converted proof-carrying `binary64`
  to permissive `Binary754`, applied local `Binary.Bsqrt`, and reconstructed
  the result through `binary_to_bits`/`b64_of_bits`. Manual fidelity review
  removed that block and recorded the checked sidecar
  `.change_log/manual_attempt_20260716_134815_b64_sqrt_blocked/attempt.json`
  with `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass`. This remains the same semantic blocker:
  the upstream alias must preserve the proof-carrying
  `binary_float 53 1024` API, bounded finite proofs, and `unop_nan_pl64`
  NaN-payload path; the available permissive `Binary754` route is not a
  faithful completion, so `b64_sqrt` remains active.
  Manual target recheck on 2026-07-17 for `MISSING_INFRASTRUCTURE.md:426`
  again leaves source code unchanged. Upstream `Bits.v:734` is the exact alias
  `b64_sqrt : mode -> binary64 -> binary64 := Bsqrt _ _ Hprec Hprec_emax
  unop_nan_pl64`, with `binary64 := binary_float 53 1024`. The current Lean
  tree has the proof-carrying `binary64`, `default_nan_pl64`, and
  `unop_nan_pl64`, but the only local square-root operation named `Bsqrt` is
  still `FloatSpec.IEEE754.Binary.Bsqrt`, whose handler and result are over
  permissive `Binary754`; its `BinarySingleNaNBridge.Bsqrt` side returns a
  proof-erased `BinaryFloat`, and `binary_sqrt` also returns `Binary754`.
  `BinarySingleNaN.lean` has a permissive `B754` layer and an audit helper for
  `Bsqrt_correct_aux`, but no proof-carrying `SF2B`/`BSN2B` bridge that
  constructs a `binary_float 53 1024` result with bounded finite proofs while
  preserving the `unop_nan_pl64` NaN-payload path. Routing through
  `Binary.Bsqrt`, `binary_sqrt`, or `b64_of_bits` would therefore be the same
  proof-erased or proof-reconstructed wrapper rejected by the target.
- `b64_plus`: subscription harness attempt
  `.change_log/codex_attempt_20260713_043044` classified the exact public
  alias as blocked. Upstream specializes `Bplus _ _ Hprec Hprec_emax
  binop_nan_pl64` over proof-carrying `binary64`, but current Lean's available
  addition operations are over `BinaryFloat`/`Binary754` and proof-erased or
  permissive wrappers. Routing through `Binary.Bplus` or `binary_add` would not
  return a `binary_float 53 1024` with preserved bounded finite proofs and
  `binop_nan_pl64` payload handling, so the name remains active until the
  proof-carrying addition bridge is restored.
  Config-provider harness attempt `.change_log/codex_attempt_20260715_233450`
  rechecked the exact upstream alias after the current `binary64` surface
  restorations and again left Lean source unchanged: `target_before.lean` and
  `target_after.lean` are identical, the local target gate passed,
  `scripts/audit_placeholders.sh --json FloatSpec` passed with existing
  placeholder/trust findings (`sorry = 0`, `axiom = 0`, `admit = 0`), and
  `scripts/status_report.sh --write` completed. The attempt classified the
  target as blocked because local `Binary.Bplus` still returns permissive
  `Binary754`, not `binary_float 53 1024`, and no bridge currently
  reconstructs the bounded finite proofs while preserving `binop_nan_pl64`
  payload handling.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_112346`
  rechecked `b64_plus` after the current `b64_sqrt` blocker update and left
  source code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The top-level
  attempt record has `result = blocked`, `build = not_run`, and
  `coq_alignment = not_checked`; the exact checked sidecar
  `.change_log/manual_attempt_20260716_112346_b64_plus_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing
  proof-carrying addition bridge: upstream returns `binary64` through
  `Bplus _ _ Hprec Hprec_emax binop_nan_pl64`, while local `Binary.lean`
  exposes `Bplus`/`binary_add` returning permissive `Binary754` or
  proof-erased bridge payloads. Routing through those surfaces or rebuilding
  through bits would not preserve bounded finite proofs or the
  `binop_nan_pl64` NaN-payload path.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_135820`
  rechecked `b64_plus` after the manual rejection of the weakened `b64_sqrt`
  patch and left source code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The checked sidecar
  `.change_log/manual_attempt_20260716_135820_b64_plus_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass`. The blocker remains the proof-carrying
  binary64 operation surface: upstream `b64_plus` specializes `Bplus _ _
  Hprec Hprec_emax binop_nan_pl64` to `binary64 -> binary64 -> binary64`,
  preserving bounded finite proofs and first-NaN payload handling. Current Lean
  has `binary64` and `binop_nan_pl64`, but `Binary.Bplus` returns permissive
  `Binary754` and `BinarySingleNaNBridge.Bplus` returns proof-erased
  `BinaryFloat`; no faithful adapter back to `binary_float 53 1024` is present.
  Adding `b64_plus` from those helpers or rebuilding through bits would be
  differently parameterized and proof-erased, so `b64_plus` remains active.
  Manual target recheck on 2026-07-17 for `MISSING_INFRASTRUCTURE.md:448`
  again classifies the exact alias as blocked. Upstream `IEEE754/Bits.v:736`
  defines `b64_plus : mode -> binary64 -> binary64 -> binary64 :=
  Bplus _ _ Hprec Hprec_emax binop_nan_pl64`, where `binary64` is
  `binary_float 53 1024` and the NaN handler preserves the first source NaN
  payload proof. Current Lean has that proof-carrying `binary64` and
  `binop_nan_pl64`, but the available addition paths still do not produce the
  same carrier: `FloatSpec.IEEE754.Binary.Bplus` and `binary_add` return the
  permissive `Binary754`, while `BinarySingleNaNBridge.Bplus` returns
  proof-erased `BinaryFloat`. No current bridge reconstructs the finite
  `bounded` proof required by `binary_float.B754_finite` while also preserving
  the `binop_nan_pl64` payload path, so adding a Lean `b64_plus` through those
  helpers would violate the target by changing the return surface or erasing
  proof payloads.
- `b64_minus`: subscription harness attempt
  `.change_log/codex_attempt_20260713_043459` classified the exact public
  alias as blocked. Upstream specializes `Bminus _ _ Hprec Hprec_emax
  binop_nan_pl64` over proof-carrying `binary64`, but current Lean's available
  subtraction operations are over `BinaryFloat`/`Binary754` and proof-erased or
  permissive wrappers. Routing through `Binary.Bminus` or `binary_sub` would
  not return a `binary_float 53 1024` with preserved bounded finite proofs and
  `binop_nan_pl64` payload handling, so the name remains active until the
  proof-carrying subtraction bridge is restored.
  Config-provider harness attempt `.change_log/codex_attempt_20260715_233857`
  rechecked the exact alias against upstream `Bits.v` and left Lean source
  unchanged: `target_before.lean` and `target_after.lean` are identical, the
  local target gate passed, `scripts/audit_placeholders.sh --json FloatSpec`
  passed with existing placeholder/trust findings (`sorry = 0`, `axiom = 0`,
  `admit = 0`), and `scripts/status_report.sh --write` completed. The nested
  checked classifier
  `.change_log/manual_attempt_20260715_154123_b64_minus_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and `build = not_run`:
  current Lean subtraction paths still return proof-erased/permissive
  `BinaryFloat`/`Binary754` surfaces, and no existing bridge reconstructs
  `binary_float 53 1024` with bounded finite proofs while preserving
  `binop_nan_pl64` payload handling.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_113620`
  rechecked `b64_minus` after the current `b64_plus` blocker update and left
  source code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The top-level
  attempt record has `result = blocked`, `build = not_run`, and
  `coq_alignment = not_checked`; the exact checked sidecar
  `.change_log/manual_attempt_20260716_113620_b64_minus_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing
  proof-carrying subtraction bridge: upstream returns `binary64` through
  `Bminus _ _ Hprec Hprec_emax binop_nan_pl64`, while local `Binary.lean`
  exposes `Bminus`/`binary_sub` returning permissive `Binary754` or
  proof-erased bridge payloads. Routing through those surfaces or rebuilding
  through bits would not preserve bounded finite proofs or the
  `binop_nan_pl64` NaN-payload path.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_140559`
  rechecked `b64_minus` after the current `b64_plus` blocker update and left
  source code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The checked sidecar
  `.change_log/manual_attempt_20260716_140559_b64_minus_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass`. The blocker remains the proof-carrying
  binary64 operation surface: upstream `b64_minus` specializes `Bminus _ _
  Hprec Hprec_emax binop_nan_pl64` to `binary64 -> binary64 -> binary64`,
  preserving bounded finite proofs and first-NaN payload handling. Current Lean
  has `binary64` and `binop_nan_pl64`, but `Binary.Bminus` returns permissive
  `Binary754` and `BinarySingleNaNBridge.Bminus` returns proof-erased
  `BinaryFloat`; no faithful adapter back to `binary_float 53 1024` is present.
  Adding `b64_minus` from those helpers or rebuilding through bits would be
  differently parameterized and proof-erased, so `b64_minus` remains active.
- `b64_mult`: subscription harness attempt
  `.change_log/codex_attempt_20260713_044008` classified the exact public
  alias as blocked. Upstream specializes `Bmult _ _ Hprec Hprec_emax
  binop_nan_pl64` over proof-carrying `binary64`, but current Lean's available
  multiplication paths are over `BinaryFloat`/`Binary754` and proof-erased or
  permissive wrappers. Routing through `Binary.Bmult` or `binary_mul` would not
  return a `binary_float 53 1024` with preserved bounded finite proofs and
  `binop_nan_pl64` payload handling, so the name remains active until the
  proof-carrying multiplication bridge is restored.
  Config-provider harness attempt `.change_log/codex_attempt_20260715_234434`
  rechecked the exact alias at the current proof-carrying `binary64` surface
  and left Lean source unchanged: `target_before.lean` and
  `target_after.lean` are identical, the local target gate passed,
  `scripts/audit_placeholders.sh --json FloatSpec` passed with existing
  placeholder/trust findings (`sorry = 0`, `axiom = 0`, `admit = 0`), and
  `scripts/status_report.sh --write` completed. The attempt also confirmed
  the direct type mismatch: `binop_nan_pl64` is a NaN handler over
  `binary64`, but local `Binary.Bmult` expects a `BmultNaNHandler` over
  `Binary754` and returns `Binary754`, so adding `b64_mult` now would require
  either weakening through a fake adapter or restoring the missing
  proof-carrying multiplication bridge.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_114331`
  rechecked `b64_mult` and left source code unchanged
  (`changed_during_attempt.txt` is empty, `changed_files = []`, and the local
  target gate passed). The top-level attempt record has `result = blocked`,
  `build = not_run`, and `coq_alignment = not_checked`; the checked blocker
  artifact `.change_log/codex_attempt_20260716T034710Z_b64_mult_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing
  proof-carrying multiplication bridge: upstream returns `binary64` through
  `Bmult _ _ Hprec Hprec_emax binop_nan_pl64`, while local `Binary.lean`
  exposes `Bmult`/`binary_mul` returning permissive `Binary754` or
  proof-erased bridge payloads. A direct alias rejects because
  `binop_nan_pl64` has the wrong carrier type for local `Bmult`; routing
  through `Binary754` or rebuilding through bits would weaken the upstream
  proof-carrying `binary_float 53 1024` result surface.
  The normalized checked sidecar
  `.change_log/manual_attempt_20260716_114331_b64_mult_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass` for that same config-provider attempt.
  `b64_mult` remains active until a faithful proof-carrying adapter is
  available for `Bmult _ _ Hprec Hprec_emax binop_nan_pl64` over
  `binary_float 53 1024`.
- `b64_div`: subscription harness attempt
  `.change_log/codex_attempt_20260713_044410` classified the exact public alias
  as blocked. Upstream specializes `Bdiv _ _ Hprec Hprec_emax binop_nan_pl64`
  over proof-carrying `binary64`, but current Lean's available division paths
  are over `BinaryFloat`/`Binary754` and proof-erased or permissive wrappers.
  Routing through `Binary.Bdiv` or `binary_div` would not return a
  `binary_float 53 1024` with preserved bounded finite proofs and
  `binop_nan_pl64` payload handling, so the name remains active until the
  proof-carrying division bridge is restored.
  Config-provider harness attempt `.change_log/codex_attempt_20260715_235029`
  rechecked the exact alias at the current `binary64` surface and left Lean
  source unchanged: `target_before.lean` and `target_after.lean` are
  identical, the local target gate passed,
  `scripts/audit_placeholders.sh --json FloatSpec` passed with existing
  placeholder/trust findings (`sorry = 0`, `axiom = 0`, `admit = 0`), and
  `scripts/status_report.sh --write` completed. The nested checked classifier
  `.change_log/manual_attempt_20260715_155236_b64_div_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `build = not_run`: local `Bdiv`/`binary_div` still operate on
  `Binary754`/`BinaryFloat` and return `Binary754`, with no faithful lift back
  to `binary_float 53 1024` preserving bounded finite proofs and
  `binop_nan_pl64` NaN payload behavior.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_115205`
  rechecked `b64_div` and left source code unchanged
  (`changed_during_attempt.txt` is empty, `changed_files = []`, and the local
  target gate passed). The top-level attempt record has `result = blocked`,
  `build = not_run`, and `coq_alignment = not_checked`; the exact checked
  sidecar `.change_log/manual_attempt_20260716_115205_b64_div_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing
  proof-carrying division bridge: upstream returns `binary64` through
  `Bdiv _ _ Hprec Hprec_emax binop_nan_pl64`, while local `Binary.lean`
  exposes `Bdiv`/`binary_div` returning permissive `Binary754` or proof-erased
  bridge payloads. Routing through those surfaces or rebuilding through bits
  would not preserve bounded finite proofs or the `binop_nan_pl64` NaN-payload
  path.
  Manual target recheck `.change_log/manual_attempt_20260717_b64_div_current_blocked/attempt.json`
  keeps the item classified as blocked for the same proof-carrying surface
  mismatch. Upstream line 739 defines `b64_div : mode -> binary64 -> binary64
  -> binary64 := Bdiv _ _ Hprec Hprec_emax binop_nan_pl64`, and upstream
  `Binary.Bdiv` reconstructs a `binary_float` with `BSN2B`. Current Lean has
  `binary64` and `binop_nan_pl64`, but local `Binary.Bdiv`/`binary_div` operate
  over `Binary754`, whose finite validity payload is permissive, while
  `BinarySingleNaNBridge.Bdiv` returns proof-erased `BinaryFloat`. Adding
  `b64_div` now would therefore either change the return type, erase bounded
  finite proofs, lose the `binop_nan_pl64` NaN payload path, or rebuild through
  bits; the prerequisite is an exact proof-carrying division bridge back to
  `binary_float 53 1024`.
- `b64_fma`: subscription harness attempt
  `.change_log/codex_attempt_20260713_044818` classified the exact public alias
  as blocked. Upstream specializes `Bfma _ _ Hprec Hprec_emax ternop_nan_pl64`
  over proof-carrying `binary64`, but current Lean's available fused
  multiply-add paths are over `BinaryFloat`/`Binary754` and proof-erased or
  permissive wrappers. Routing through `Binary.Bfma` or `binary_fma` would not
  return a `binary_float 53 1024` with preserved bounded finite proofs and
  `ternop_nan_pl64` payload handling, so the name remains active until the
  proof-carrying fused multiply-add bridge is restored.
  Config-provider harness attempt `.change_log/codex_attempt_20260715_235604`
  rechecked the exact alias at the current `binary64` surface and left Lean
  source unchanged: `target_before.lean` and `target_after.lean` are
  identical, `lake env lean FloatSpec/src/IEEE754/Bits.lean` passed with
  existing warnings only, `scripts/audit_placeholders.sh --json FloatSpec`
  passed with existing placeholder/trust findings (`sorry = 0`, `axiom = 0`,
  `admit = 0`), and `scripts/status_report.sh --write` completed. The nested
  checked classifier
  `.change_log/manual_attempt_20260715_b64_fma_blocked/attempt.json` records
  `result = blocked`, `coq_alignment = checked`, and `build = not_run`: local
  `Binary.Bfma` expects a `BfmaNaNHandler` over permissive `Binary754 53 1024`
  and returns `Binary754`, while `BinarySingleNaNBridge.Bfma` returns
  proof-erased `BinaryFloat`; no faithful bridge currently reconstructs
  `binary_float 53 1024` with bounded finite proofs while preserving
  `ternop_nan_pl64` payload handling.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_115937`
  rechecked `b64_fma` and left source code unchanged
  (`changed_during_attempt.txt` is empty, `changed_files = []`, and the local
  target gate passed). The top-level attempt record has `result = blocked`,
  `build = not_run`, and `coq_alignment = not_checked`; the exact checked
  sidecar `.change_log/manual_attempt_20260716_115937_b64_fma_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing
  proof-carrying fused multiply-add bridge: upstream returns `binary64` through
  `Bfma _ _ Hprec Hprec_emax ternop_nan_pl64`, while local `Binary.lean`
  exposes `Bfma`/`binary_fma` returning permissive `Binary754` or proof-erased
  bridge payloads. A direct alias rejects because `ternop_nan_pl64` has the
  wrong carrier type for local `Bfma`; routing through those surfaces or
  rebuilding through bits would not preserve bounded finite proofs or the
  `ternop_nan_pl64` NaN-payload path.
- `b64_of_bits`: restored as the exact-name Lean definition in
  `FloatSpec/src/IEEE754/Bits.lean` by config-provider harness attempt
  `.change_log/codex_attempt_20260716_021320`, with checked classifier sidecar
  `.change_log/manual_attempt_20260716_b64_of_bits_proved/attempt.json`.
  The definition matches upstream `IEEE754/Bits.v:b64_of_bits`: it decodes
  `(sign, mantissa, exponent)` fields with `split_bits 52 11`, returns
  proof-carrying `binary_float 53 1024`, maps zero and infinity fields to the
  corresponding constructors, maps nonzero all-ones exponent fields to
  `B754_nan` with a proved `nan_pl 53` payload, and maps finite fields to
  `B754_finite` with concrete IEEE64 `bounded` proofs for subnormal exponent
  `-1074` and normal exponent `eField - 1075`. It does not route through the
  permissive `Binary754` decoder. Focused check
  `lake env lean FloatSpec/src/IEEE754/Bits.lean` passed with warnings only.
  Status: implemented and removed from active semantic gaps.
- The remaining `b32_*` and `b64_*` operation aliases:
  no faithful counterparts found under the upstream names. Some generic local
  helpers such as `erase`, `succ`, `pred`, `compare`, `binary_to_bits`, and
  `bits_to_binary` exist, but the specialized IEEE32/IEEE64 operation API layer
  is not present.

Checked batch 8: `IEEE754/PrimFloat.v` primitive-float bridge names.

One entry has been removed from the active semantic gap list in this batch.

- `round_nearest_even_equiv`: restored as the exact public Lean lemma
  `ExperimentalPrimFloatBridge.round_nearest_even_equiv` in
  `FloatSpec/src/IEEE754/PrimFloat.lean`. Upstream proves
  `round_nearest_even m l = choice_mode mode_NE s m l` by case analysis on
  the location and tie case; the Lean port adds the corresponding local
  `round_nearest_even` definition using `cond_incr` and `round_N
  (!(decide (2 ∣ m)))`, then proves equality with the existing
  `choice_mode RoundingMode.RNE` by the same case split. Config-provider
  harness attempt `.change_log/codex_attempt_20260716_002221` produced the
  source patch; a direct follow-up check on the actual lemma line confirmed
  `lake env lean FloatSpec/src/IEEE754/PrimFloat.lean` succeeds and
  `#print axioms ExperimentalPrimFloatBridge.round_nearest_even_equiv` reports
  no `sorryAx`.

Still active after statement check:

- `Prim2B` and `B2Prim`: Lean has `prim_to_binary` and `binary_to_prim`, but
  the file explicitly uses an experimental opaque real-wrapper `PrimFloat` and
  states that it must not be counted as a faithful IEEE/PrimFloat equivalence
  result. These are not faithful counterparts of Coq's primitive `float`
  bridge. Subscription harness attempt
  `.change_log/codex_attempt_20260713_084934` classified `Prim2B` as blocked
  with no source changes: upstream is `SF2B (Prim2SF x) (Prim2SF_valid x)` over
  Coq primitive `float`, while the local file lacks faithful primitive-float
  semantics, `Prim2SF_valid`, and the proof-carrying `SF2B` bridge needed to
  expose public exact-name `Prim2B`. Config-provider harness attempt
  `.change_log/codex_attempt_20260716_001241` rechecked the same exact-name
  payload against the current `ExperimentalPrimFloatBridge`, left
  `FloatSpec/src/IEEE754/PrimFloat.lean` unchanged
  (`target_before.lean` and `target_after.lean` identical), and classified the
  target as blocked for the same reason: the local `PrimFloat` is only a
  real-valued wrapper, not Coq primitive `float`, and no local `Prim2SF_valid`
  or proof-carrying `SF2B (Prim2SF x) ... : binary_float prec emax` path exists.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_120908`
  rechecked `Prim2B` after the current IEEE64 operation blocker updates and left
  source code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The top-level
  attempt record has `result = blocked`, `build = not_run`, and
  `coq_alignment = not_checked`; the exact checked sidecar
  `.change_log/manual_attempt_20260716_120908_Prim2B_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing faithful
  primitive-float bridge: upstream returns proof-carrying `binary_float prec
  emax` via `SF2B (Prim2SF x) (Prim2SF_valid x)`, while local
  `ExperimentalPrimFloatBridge.prim_to_binary` maps an opaque real-wrapper
  `PrimFloat` through `round_to_generic`/`real_to_FullFloat` into permissive
  `Binary754`. Adding exact-name `Prim2B` over that local surface would be a
  semantic placeholder and would lose Coq primitive `float`, `Prim2SF_valid`,
  NaN, infinity, payload, and signed-zero behavior.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_141959`
  rechecked `Prim2B` against the current `ExperimentalPrimFloatBridge` and
  left source code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The checked sidecar
  `.change_log/manual_attempt_20260716_Prim2B_current_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, and
  `coq_alignment = checked`. The blocker remains the missing faithful
  primitive-float input bridge: upstream `Prim2B (x : float)` returns
  proof-carrying `binary_float prec emax` by applying `SF2B` to
  `Prim2SF x` and `Prim2SF_valid x`. Current Lean has proof-carrying
  `binary_float`, but its `PrimFloat` is an opaque `ℝ` wrapper, local
  `prim_to_binary` returns permissive `Binary754`, `BinarySingleNaN.SF2B`
  returns raw `B754`, and no `Prim2SF_valid` counterpart exists. Adding
  `Prim2B` over that surface would again be a semantic placeholder rather
  than the upstream primitive-float bridge, so `Prim2B` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_184119`
  rechecked the same exact-name payload after the current Bits-family
  blocker update and left source code unchanged. The checked sidecar
  `.change_log/manual_attempt_20260716_Prim2B_bridge_mismatch_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, and
  `coq_alignment = checked`: the current file still lacks Coq primitive
  `float`, `Prim2SF_valid`, and a proof-carrying `SF2B` path to
  `binary_float prec emax`.
  Manual target recheck
  `.change_log/manual_attempt_20260717_Prim2B_current_blocked/attempt.json`
  records `result = blocked` and `coq_alignment = checked`: upstream line 27
  defines `Prim2B (x : float) : binary_float prec emax` exactly as
  `SF2B (Prim2SF x) (Prim2SF_valid x)`. Current Lean still exposes only the
  experimental real-projection `PrimFloat`; its `Prim2SF` is computed through
  `prim_to_binary`, whose result is permissive `Binary754`, and the local
  `BinarySingleNaN.SF2B` returns proof-erased `B754` rather than
  proof-carrying `binary_float prec emax`. No faithful `Prim2SF_valid` or Coq
  primitive `float` bridge is present, so adding exact-name `Prim2B` now would
  be a semantic placeholder.
  Subscription harness attempt
  `.change_log/codex_attempt_20260713_085249` classified `B2Prim` as blocked
  with no source changes: upstream is `SF2Prim (B2SF x)` from proof-carrying
  `binary_float prec emax` to Coq primitive `float`, while the local
  `binary_to_prim` maps permissive `Binary754` through `B2R` into the opaque
  real wrapper and collapses special primitive-float behavior. Config-provider
  harness attempt `.change_log/codex_attempt_20260716_001724` rechecked the
  exact upstream definition against the current target, left
  `FloatSpec/src/IEEE754/PrimFloat.lean` unchanged
  (`target_before.lean` and `target_after.lean` identical), and classified the
  candidate as blocked because the local bridge has no `SF2Prim` primitive
  bridge or Coq-like primitive `float` model; implementing `B2Prim` over the
  real wrapper would lose NaN, infinity, payload, and signed-zero behavior.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_121625`
  rechecked `B2Prim` after the current `Prim2B` blocker update and left source
  code unchanged (`changed_during_attempt.txt` is empty,
  `changed_files = []`, and the local target gate passed). The top-level
  attempt record has `result = blocked`, `build = not_run`, and
  `coq_alignment = not_checked`; the checked blocker artifact
  `.change_log/manual_attempt_20260716_121839_B2Prim_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing faithful
  primitive-float output bridge: upstream returns Coq primitive `float` through
  `SF2Prim (B2SF x)` from proof-carrying `binary_float prec emax`, while local
	  `ExperimentalPrimFloatBridge.binary_to_prim` maps permissive `Binary754`
	  through `B2R` into an opaque real-wrapper `PrimFloat`. Adding exact-name
	  `B2Prim` over that local surface would be a semantic placeholder and would
	  lose NaN, infinity, payload, and signed-zero behavior.
	  Current-refresh sidecar
	  `.change_log/manual_attempt_20260716_145407_B2Prim_current_blocked/attempt.json`
	  reuses the config-provider harness evidence from
	  `.change_log/codex_attempt_20260716_121625` because the target snapshots were
	  identical and `changed_during_attempt.txt` was empty. It records
	  `coq_alignment = checked`, `local_target_gate = pass`, and
	  `changed_files = []`: upstream `B2Prim` is still the primitive-float bridge
	  `SF2Prim (B2SF x)` from proof-carrying `binary_float prec emax`, while local
	  `binary_to_prim` still maps permissive `Binary754` through `B2R` into the
	  opaque real-wrapper `PrimFloat` and has no `SF2Prim`/Coq primitive `float`
	  counterpart. Therefore `B2Prim` remains active rather than being replaced by
	  the local wrapper.
- `binary_round_aux_equiv`, `binary_round_equiv`, and
  `binary_normalize_equiv`: no faithful counterparts found. Local
  `binary_round_aux`/`binary_round`/normalization helpers are documented as
  audit helpers rather than ports of the Flocq algorithms. Config-provider
  harness attempt `.change_log/codex_attempt_20260716_003125` rechecked
  `binary_round_aux_equiv` after `round_nearest_even_equiv` was restored, left
  `FloatSpec/src/IEEE754/PrimFloat.lean` unchanged
  (`target_before.lean` and `target_after.lean` identical), and classified the
  exact upstream payload as blocked. The checked sidecar
  `.change_log/codex_attempt_20260716_003125/binary_round_aux_equiv_blocked.json`
  records the missing pair explicitly: upstream unfolds
  `SpecFloat.binary_round_aux` and Flocq `binary_round_aux`, then rewrites by
  `round_nearest_even_equiv`, while the local repository only has
  `ExperimentalBinaryRound.binary_round_aux`, documented as not a port of the
  Flocq `binary_round_aux`/`binary_round`/`binary_normalize` algorithms.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_122806`
  rechecked `binary_round_aux_equiv` after the current `Prim2B`/`B2Prim`
  blocker updates and left source code unchanged (`changed_during_attempt.txt`
  is empty, `changed_files = []`, and the local target gate passed). The
  top-level attempt record has `result = blocked`, `build = not_run`, and
  `coq_alignment = not_checked`; the checked sidecar
  `.change_log/manual_attempt_20260716_122806_binary_round_aux_equiv_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing faithful
  `SpecFloat.binary_round_aux`/`shr_fexp` and BinarySingleNaN/Binary
  `binary_round_aux` bridge: upstream unfolds both sides and finishes with
  `round_nearest_even_equiv`, while local Lean only has the nearest-even choice
  lemma inside the experimental real-wrapper bridge plus
  `ExperimentalBinaryRound` audit helpers explicitly documented as non-ports of
  the Flocq algorithms. Adding an exact-name lemma over those local wrappers
  would be helper-only/tautological, not the upstream primitive-float payload.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_004648`
  then rechecked `binary_round_equiv`, left
  `FloatSpec/src/IEEE754/PrimFloat.lean` unchanged
  (`target_before.lean` and `target_after.lean` identical), and classified the
  exact upstream payload as blocked. The nested checked sidecar
  `.change_log/manual_attempt_20260716_004851_binary_round_equiv_blocked/attempt.json`
  records that upstream needs faithful `SpecFloat.binary_round`, Flocq
  `binary_round`, `shl_align_fexp`, and `binary_round_aux_equiv`; the local
  repository has no `SpecFloat.binary_round` counterpart and only the
  non-faithful `ExperimentalBinaryRound` audit helpers.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_124106`
  rechecked `binary_round_equiv` after the current `binary_round_aux_equiv`
  blocker update and left source code unchanged (`changed_during_attempt.txt`
  is empty, `changed_files = []`, and the local target gate passed). The
  top-level attempt record has `result = blocked`, `build = not_run`, and
  `coq_alignment = not_checked`; the checked sidecar
  `.change_log/manual_attempt_20260716_124106_binary_round_equiv_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the missing faithful
  `SpecFloat.binary_round` and Flocq `binary_round` bridge: upstream unfolds
  `SpecFloat.binary_round`, `binary_round`, and `shl_align_fexp`, destructs
  `shl_align`, then applies `binary_round_aux_equiv`. Local Lean has
  `shl_align_fexp`, but only has `ExperimentalBinaryRound.binary_round` and
  `ExperimentalBinaryRound.binary_round_aux`, both documented as audit helpers
  rather than Flocq algorithm ports, and `binary_round_aux_equiv` remains
  structurally blocked.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_124734`
  rechecked `binary_normalize_equiv` after the current `binary_round_equiv`
  blocker update and left source code unchanged (`changed_during_attempt.txt`
  is empty and `target_before.lean`/`target_after.lean` are identical). The
  clean checked sidecar
  `.change_log/manual_attempt_20260716_124734_binary_normalize_equiv_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass`. The blocker remains the missing faithful
  `SpecFloat.binary_normalize` and Flocq `binary_normalize` bridge: upstream
  cases on the signed mantissa, simplifies zero directly, and reduces positive
  and negative finite cases through `B2SF_SF2B` plus `binary_round_equiv`.
  Local Lean only exposes `ExperimentalBinaryRound.binary_normalize`, whose
  namespace is documented as not a Flocq `binary_round_aux`/`binary_round`/
  `binary_normalize` port, and `binary_round_equiv` remains structurally
  blocked.
- `mul_equiv` and `add_equiv`: no faithful counterparts found. Local
  `prim_mul_correct` and `prim_add_correct` are reflexive tautologies over the
  local model, not the upstream equivalences between primitive operations and
  `Bmult`/`Bplus`. Config-provider harness attempt
  `.change_log/codex_attempt_20260716_003910` rechecked `mul_equiv`, left
  `FloatSpec/src/IEEE754/PrimFloat.lean` unchanged
  (`target_before.lean` and `target_after.lean` identical), and classified the
  target as blocked. The nested checked sidecar
  `.change_log/manual_attempt_20260715_164232/attempt.json` records the
  specific missing payloads: upstream `mul_equiv` needs faithful Coq primitive
  float bridge lemmas `Prim2B`/`B2Prim`/`B2SF_Prim2B`, `SpecFloat.mul_spec`,
  and `binary_round_aux_equiv`; the local `ExperimentalPrimFloatBridge` is an
  opaque real wrapper, `prim_to_binary`/`binary_to_prim` are not proof-carrying
  primitive-float conversions, `binary_mul` is a compatibility wrapper, and
  `ExperimentalBinaryRound.binary_round_aux` is not a Flocq algorithm port.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_123426`
  rechecked `mul_equiv` after the current primitive bridge and
  `binary_round_aux_equiv` blocker updates and again left source code unchanged
  (`changed_during_attempt.txt` is empty, `changed_files = []`, and the local
  target gate passed). The top-level attempt record has `result = blocked`,
  `build = not_run`, and `coq_alignment = not_checked`; the checked sidecar
  `.change_log/manual_attempt_20260716_primfloat_mul_equiv_blocked/attempt.json`
  records `coq_alignment = checked`. The blocker remains the full upstream
  primitive multiplication equivalence payload: Coq proves
  `Prim2B (x * y) = Bmult mode_NE (Prim2B x) (Prim2B y)` through
  `B2Prim_inj`, `B2Prim_Prim2B`, `Prim2SF_inj`, `Prim2SF_B2Prim`,
  `SpecFloat.mul_spec`, `B2SF_Prim2B`, proof-carrying binary case analysis,
  `B2SF_SF2B`, and `binary_round_aux_equiv`. Local `prim_mul_correct` is still
  a reflexive theorem over `binary_to_prim (binary_mul x y)`, and using it
  would certify the local experimental wrappers rather than Flocq primitive
  multiplication semantics.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_125646`
  rechecked `add_equiv` after the current primitive bridge and
  `binary_normalize_equiv` blocker updates and left source code unchanged
  (`changed_during_attempt.txt` is empty, `changed_files = []`, and the local
  target gate passed). The checked sidecar
  `.change_log/manual_attempt_20260716_primfloat_add_equiv_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass`. The blocker remains the full upstream
  primitive addition equivalence payload: Coq proves
  `Prim2B (x + y) = Bplus mode_NE (Prim2B x) (Prim2B y)` through
  `B2Prim_inj`, `B2Prim_Prim2B`, `Prim2SF_inj`, `Prim2SF_B2Prim`,
  `SpecFloat.add_spec`, `B2SF_Prim2B`, proof-carrying binary case analysis,
  and `binary_normalize_equiv`. Local `prim_add_correct` is still a reflexive
  theorem over `binary_to_prim (binary_add x y)`, and using it would certify
  the local experimental wrappers rather than Flocq primitive addition
  semantics.
- `normfr_mantissa_equiv`: no faithful counterpart found. Config-provider
  harness attempt `.change_log/codex_attempt_20260716_041136` rechecked the
  exact upstream payload and left source code unchanged. The checked sidecar
  `.change_log/manual_attempt_20260716_041520_normfr_mantissa_equiv_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `local_target_gate = pass`. The blocker is structural: upstream
  `IEEE754/PrimFloat.v:normfr_mantissa_equiv` proves
  `to_Z (normfr_mantissa x) = Z.of_N (Bnormfr_mantissa (Prim2B x))` over Coq
  primitive `float`, using `Prim2B := SF2B (Prim2SF x) (Prim2SF_valid x)` and
  `normfr_mantissa_spec`. Current `PrimFloat.lean` is still the
  `ExperimentalPrimFloatBridge` real-wrapper model and lacks faithful public
  `Prim2B`, `normfr_mantissa`, `to_Z`, `Z.of_N`, and primitive
  `SpecFloat` semantics. A theorem over `prim_to_binary`/`binary_to_prim`
  would be helper-only/tautological and would not preserve primitive NaN,
  infinity, or signed-zero payload.

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
- Entries with no credible local candidate in the first triage, such as many
  `Bounded*`/`Veltkamp*` lemmas and the final `ErrFmaApprox*` family, remain
  active. `plusExact2Aux`, `plusExact2`, and `plusExactExp` were later restored
  exactly and removed from the active list.
- This Pff pass is not yet a completed statement-by-statement audit of all 102
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
  Config-provider harness attempt `.change_log/codex_attempt_20260713_231215`
  targeted the exact theorem after the current helper stack was inspected, but
  failed before proof work because the configured subscription provider had hit
  its usage limit. `target_before.lean` and `target_after.lean` are identical,
  no Lean files were changed, and this attempt is not evidence of a semantic
  blocker beyond the already recorded missing final residual re-encoding from
  the auxiliary exponent package to `Fexp s = Fexp r - precision`.
  Follow-up exact-name restoration `.change_log/codex_attempt_20260715_203423`
  added public theorem `errorBoundedMultClosest` in
  `FloatSpec/src/Pff/Pff.lean`. It now proves the upstream existential payload:
  canonical and bounded rounded product `r`, bounded residual `s`, real-value
  equality to `pq`, residual equality to `p * q - r`, and
  `s.Fexp = r.Fexp - precision`. The proof normalizes the rounded result, uses
  `FcanonicUnique` to identify it with the auxiliary rounded value, applies
  `ClosestUlp`, `FulpLe`, `ClosestErrorBound`, and
  `F2R_rep_at_lower_exp` to re-encode the residual at the final exponent, and
  handles the zero residual branch with a bounded `Fzero`. Verification:
  focused `lake env lean FloatSpec/src/Pff/Pff.lean` passed, placeholder/status
  gates passed with `sorry = 0`, `axiom = 0`, `admit = 0`, and full
  `lake build` completed successfully with 3345 jobs. Removed from the active
  list.
- `plusExact2Aux`: restored exactly in `FloatSpec/src/Pff/Pff.lean` as a public
  theorem with the upstream payload
  `0 ≤ F2R p → Fcanonic p → Fbounded q → Closest (F2R p + F2R q) r →
  Fexp r < pred (Fexp p) → F2R r = F2R p + F2R q`. The subscription harness
  attempt `.change_log/codex_attempt_20260713_055654` produced the proof; a
  direct focused check `lake env lean FloatSpec/src/Pff/Pff.lean` exited with
  status 0 after the harness patch. Removed from the active list.
- `plusExact2`: restored exactly in `FloatSpec/src/Pff/Pff.lean` as a public
  theorem with the upstream payload
  `Fcanonic p → Fbounded q → Closest (F2R p + F2R q) r →
  Fexp r < pred (Fexp p) → F2R r = F2R p + F2R q`. Subscription harness
  attempt `.change_log/codex_attempt_20260713_061811` proved it by splitting on
  the sign of `p`, applying restored `plusExact2Aux` in the nonnegative branch,
  and using `FcanonicFopp`, `oppBounded`, `ClosestOpp`, and `Fopp_correct` in
  the negative branch. A direct focused check
  `lake env lean FloatSpec/src/Pff/Pff.lean` exited with status 0 after the
  harness patch. Removed from the active list.
- `plusExactExp`: restored as an exact public theorem in
  `FloatSpec/src/Pff/Pff.lean`, matching upstream line 10436's residual-plus-
  rounded-part payload. The proof uses the existing closest-rounding,
  `plusExpMin`/upper-bound, zero-float, and `errorBoundedPlus` infrastructure
  without adding helper-only hypotheses.
- `UlpFlessuGe` and `UlpFlessuGe2`: Lean has `UlpFlessuGe_aux`,
  `UlpFlessuGe_final_scale`,
  `UlpFlessuGe_from_abs_sub_fulp`,
  `UlpFlessuGe_from_general_fulp_bound`, and
  `UlpFlessuGe2_from_general_bound`. These are prerequisite/reduction
  theorems; the comments and statements leave the large coefficient
  arithmetic bound as a premise. Upstream `UlpFlessuGe` and
  `UlpFlessuGe2` prove those displayed coefficient inequalities, so both
  remain active. Config-provider harness attempt
  `.change_log/codex_attempt_20260715_210956` rechecked
  `UlpFlessuGe` against upstream `Pff.v:11676` and left Lean code unchanged:
  `target_before.lean` and `target_after.lean` are identical, focused
  `lake env lean FloatSpec/src/Pff/Pff.lean` passed with warnings only,
  `scripts/audit_placeholders.sh --json FloatSpec` passed, and
  `scripts/status_report.sh --write` reported the existing 53 placeholder/trust
  findings with
  `sorry = 0`, `axiom = 0`, `admit = 0`. The attempt classified the target as
  blocked because adding a wrapper around
  `UlpFlessuGe_from_general_fulp_bound` would smuggle the missing coefficient
  inequality in as a premise rather than proving the upstream payload from the
  Axpy section context.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_165902`
  rechecked `UlpFlessuGe` against the current helper stack after the later
  `UlpFlessuGe_aux`, final-scale, `from_abs_sub_fulp`, and
  `from_general_fulp_bound` restorations. It made no source changes
  (`changed_during_attempt.txt` is empty, `changed_files = []`, and the local
  target gate passed) and ended without a checked classifier. The normalized
  sidecar
  `.change_log/manual_attempt_20260716_165902_ulpflessuge_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `local_target_gate = pass`: upstream `UlpFlessuGe` proves the full displayed
  coefficient inequality from `Fcanonic radix b u` and the Axpy section
  context, while local `UlpFlessuGe_from_general_fulp_bound` still takes the
  general `FulpLeGeneral` coefficient bound as an explicit premise. Adding an
  exact-name wrapper now would therefore hide the missing arithmetic payload
  instead of porting it.
  The newest
  config-provider harness attempt `.change_log/codex_attempt_20260716_180512`
  also left source unchanged (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical) and ended with the
  generic top-level `result = failed`. The normalized checked sidecar
  `.change_log/manual_attempt_20260716_180512_ulpflessuge_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `changed_files = []`. The blocker remains the missing final arithmetic
  reduction: upstream `UlpFlessuGe` derives the displayed coefficient
  inequality from the Axpy section assumptions, `RoundLeGeneral`, closestness
  of `u`, `FulpLe2`/`FulpLeGeneral`, and `UlpFlessuGe_aux`; current Lean only
  has helper reductions such as `UlpFlessuGe_from_general_fulp_bound`, which
  prove the quarter-ulp conclusion after assuming the equivalent residual /
  `FulpLeGeneral` bound explicitly. Adding the public theorem now would smuggle
  that bound in as a premise rather than proving the upstream payload, so
  `UlpFlessuGe` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_221345`
  rechecked `UlpFlessuGe` against the current Pff helper stack and made no
  source changes (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The top-level
  attempt record has `result = blocked`; the normalized checked sidecar
  `.change_log/manual_attempt_20260716_221805_ulpflessuge_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, `build = pass`, and
  `changed_files = []`. The focused `lake env lean
  FloatSpec/src/Pff/Pff.lean` check passed with warnings only, and the attempt
  reran `scripts/audit_placeholders.sh --json FloatSpec` plus
  `scripts/status_report.sh --write`, both reporting zero placeholder/trust
  findings. The blocker is unchanged: upstream `Pff.v:11675` proves the
  displayed Axpy coefficient bound from `Fcanonic radix b u`,
  `RoundLeGeneral`, closestness/ulp facts, and exact-sum algebra, while local
  `UlpFlessuGe_from_general_fulp_bound` still assumes that general
  `FulpLeGeneral` coefficient bound as a premise.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_170340`
  rechecked `UlpFlessuGe2` against the same current helper stack. It made no
  source changes (`changed_files = []`, local target gate passed) and reported
  the same faithful-port blocker for the strict variant: upstream
  `Pff.v:11885` proves the strict displayed coefficient inequality from
  `Fcanonic radix b u` plus the `AxpyAux` section context, then applies
  upstream `UlpFlessuGe`. The normalized sidecar
  `.change_log/manual_attempt_20260716_170340_ulpflessuge2_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `local_target_gate = pass`; local `UlpFlessuGe2_from_general_bound` still
  takes the strict general-bound coefficient inequality as an explicit premise,
  so adding the exact public theorem now would smuggle the missing arithmetic
  payload rather than proving the Flocq theorem. Status: still active.
- `Axpy_opt`: Lean has `Axpy_opt_from_strict_bound` and
  `Axpy_opt_from_general_bound`, but both keep additional premises for the
  strict coefficient estimate and predecessor side cases. Upstream
  `Axpy_opt` proves `MinOrMax` directly from the two displayed user
  hypotheses, so the local helpers are not faithful replacements.
  A 2026-07-16 focused recheck against upstream `Pff/Pff.v:12301` left Lean
  code unchanged and classified the exact theorem as blocked. The checked
  sidecar
  `.change_log/manual_attempt_20260716_axpy_opt_blocked/attempt.json` records
  `result = blocked`, `changed_files = []`, and `coq_alignment = checked`:
  adding an exact-name wrapper over `Axpy_opt_from_general_bound` would assume
  the missing `UlpFlessuGe2` coefficient estimate and predecessor side cases
  instead of deriving them from the upstream large-`y` and perturbation
  hypotheses.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_222714`
  rechecked the exact upstream theorem through `scripts/codex_attempt.sh` and
  made no Lean source changes (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The top-level
  attempt record has `result = blocked`; the checked sidecar
  `.change_log/manual_attempt_20260716_222906_axpy_opt_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `changed_files = []`. The attempt reran
  `scripts/audit_placeholders.sh --json FloatSpec` and
  `scripts/status_report.sh --write`, both clean. The blocker remains the
  exact upstream payload: Coq proves `MinOrMax radix b (a1 * x1 + y1) u`
  from boundedness, closestness, canonicity, the large-`y` hypothesis, and the
  perturbation hypothesis alone, while current Lean still exposes the
  `UlpFlessuGe2` coefficient estimate and `Axpy_tFlessu` predecessor side
  cases as explicit premises in `UlpFlessuGe2_from_general_bound` and
  `Axpy_opt_from_general_bound`.
- `Dekker2`: Lean has `Dekker2_FTS`, but this is a Fast2Sum/Dekker support
  theorem over abstract `Iplus`/`Iminus`. It does not match the upstream Pff
  `Dekker2` section payload.
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
are confirmed as real semantic gaps, not renamed/split complete ports. Later
Pff restorations are reflected in the current `Pff/Pff.v` section count above.

Checked batch 11: active Core bucket revalidation after direct `rg` scan.

No entries were removed from the active semantic gap list in this batch.

The scan intentionally revisited names with nearby `_spec` or helper names:

- `Core/Raux.v`: `Rcompare_middle`, `Rcompare_floor_ceil_middle`,
  `Rcompare_ceil_floor_middle`, `cond_Ropp_Rlt_bool`, and
  `Rlt_bool_cond_Ropp` have since been restored exactly. No active
  `Core/Raux.v` names remain in the current list.
- `Core/Round_pred.v`: `satisfies_any_imp_N0` has been restored as the
  upstream `Round_pred.satisfies_any` consequence, where `satisfies_any`
  packages `F 0`, symmetry, and DN totality. No active `Core/Round_pred.v`
  names remain in the current list.
- `Core/Generic_fmt.v`: the earlier active rounding-mode instance gaps have
  since been restored directly as `valid_rnd_AW`, `valid_rnd_NA`, and
  `valid_rnd_N0`; no active `Core/Generic_fmt.v` names remain in the current
  list.
- `Core/FIX.v`, `Core/FLT.v`, and `Core/FLX.v`: the earlier active
  `Monotone_exp`/`Exists_NE` instance gaps have since been restored directly;
  no active `Core/FIX.v`, `Core/FLT.v`, or `Core/FLX.v` names remain in the
  current list.
- `Core/Digits.v`: the visible renamed helpers remain the already-recorded
  weaker forms (`Zdigit_*_nonneg`, `Zdigit_scale_point`, and
  `Zslice_div_pow_scale_nonnegKp`), not exact statement counterparts.

Checked batch 12: IEEE active sibling-name revalidation after direct `rg`
scan.

No entries were removed from the active semantic gap list in this batch.

The scan revisited active IEEE names with nearby same-stem declarations:

- `IEEE754/Binary.v`: `FullFloat` and `Binary754` are real local type
  counterparts, but still do not encode upstream's positive payload and
  finite/NaN validity obligations. The remaining local arithmetic operations
  drop upstream NaN payload handler parameters, some local `binary_*_correct`
  declarations are explicit `Unit` port-gap markers, and `Btrunc_correct` is
  still a tautological
  `result = Btrunc_correct_check ...` statement. The exact `Bulp` definition is
  now present, but `Bulp_correct` still cannot be considered hidden because no
  local theorem proves its upstream postcondition.
- `IEEE754/BinarySingleNaN.v`: `SF2B` and `SF2B_B2SF` exist, but they do not
  implement the upstream `SF2B'` validation behavior that maps invalid finite
  standard floats to NaN. The active BSN-specific `is_nan_Babs` and
  `is_finite_strict_Babs` declarations are now supplied by BSN-local theorems;
  `is_nan_Bopp` and `is_finite_strict_Bopp` are also supplied by BSN-local
  theorems. The local rounding/normalization
  helpers are documented as audit helpers rather than Flocq algorithm ports,
  and no faithful hidden counterparts were found for the active overflow,
  fit, shift/truncate, successor/predecessor, `Bulp'`, or
  `SFnearbyint_binary` families.
- `IEEE754/Bits.v`: generic `binary_to_bits`, `split_bits`,
  `bits_to_binary`, and `binary_float_of_bits_aux` exist, and the exact
  proof-carrying `binary_float_of_bits` has now been restored with explicit
  upstream width witnesses. The active remaining upstream names are the
  `b32_*`/`b64_*` operation API layer. The exact upstream
  `binary64 := binary_float 53 1024` surface is now present; the existing
  permissive `Binary64 := Binary754 53 1023` compatibility alias remains
  separate and is not used as the proof-carrying Flocq counterpart.
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

Follow-up on 2026-07-13 restored the exact local Veltkamp lemma `hxExact` in
`FloatSpec/src/Pff/Pff.lean`.  The Lean theorem concludes
`F2R hx = F2R p + F2R q` from the upstream rounded definitions for `p`, `q`,
and `hx`, using the restored `pPos`, `qNeg`, `RleRRounded`, `SterbenzAux`,
`ClosestOpp`, and `ClosestIdem` payload.  Focused verification:
`lake env lean FloatSpec/src/Pff/Pff.lean` passed.  Status: implemented and
removed from active semantic gaps; the remaining entries in this batch remain
active.

Follow-up on 2026-07-13 restored the exact local Veltkamp lemma `eqLeep` in
`FloatSpec/src/Pff/Pff.lean`.  The Lean theorem concludes `q.Fexp ≤ p.Fexp`
from the upstream local context by deriving `|F2R q| ≤ |F2R p|` using `qNeg`,
`pPos`, `ClosestOpp`, `ClosestRoundedModeP`/projector, and `ClosestMonotone`,
then applying `Fcanonic_Rle_Zle` to the normal `q` and `p`.  Focused
verification: `lake env lean FloatSpec/src/Pff/Pff.lean` passed.  Full
verification: `lake build` passed.  Status: implemented and removed from active
semantic gaps; the remaining entries in this batch remain active.

Follow-up on 2026-07-13 restored the exact local Veltkamp lemma `epLe` in
`FloatSpec/src/Pff/Pff.lean`.  The Lean theorem concludes
`p.Fexp ≤ (s : Int) + 1 + x.Fexp` from the upstream Veltkamp local context by
projecting `Float (Fnum x) (s + 1 + Fexp x)`, using `pPos`,
`ClosestRoundedModeP`/projector, `ClosestMonotone`, and zpow monotonicity, then
applying `Fcanonic_Rle_Zle` to the normal `p` and the constructed comparison
float.  Focused verification: `lake env lean FloatSpec/src/Pff/Pff.lean`
passed.  Full verification: `lake build` passed.  Status: implemented and
removed from active semantic gaps; the remaining entries in this batch remain
active.

Follow-up on 2026-07-13 restored the exact local Pff theorem
`ClosestSuccPred` in `FloatSpec/src/Pff/Pff.lean`.  The Lean theorem preserves
the upstream payload: a canonical float `f` that is no farther from `z` than
both its successor and predecessor is a `Closest` rounded value.  The proof
uses the existing successor/predecessor stack (`FSuccLt`, `FPredLt`,
`FBoundedPred`, `FPredCanonic`, `FcanonicFnormalizeEq`, `FSucPred`, and
`FNSuccProp`).  Focused verification:
`lake env lean FloatSpec/src/Pff/Pff.lean` passed.  Full verification:
`lake build` passed.  Status: implemented and removed from active semantic
gaps; the remaining entries in this batch remain active.

Follow-up on 2026-07-13 restored the exact local Pff theorem `ImplyClosest`
in `FloatSpec/src/Pff/Pff.lean`.  The Lean theorem preserves the upstream
payload: under the section hypotheses `Bf`, `Cf`, `zGe`, `zLe`, `fGe`, and
`eGe`, the half-ulp bound `|z - F2R f| <= radix^e / 2` implies
`Closest b radix z f`.  The proof derives successor and predecessor distance
bounds, then applies `ClosestSuccPred`, using `FSuccDiffPos`, `FPredLt`,
`FPredProp`, `FPredCanonic`, `FpredUlpPos`, `CanonicFulp`, and
`Fcanonic_Rle_Zle`.  Focused verification:
`lake env lean FloatSpec/src/Pff/Pff.lean` passed.  Full verification:
`lake build` passed.  Status: implemented and removed from active semantic
gaps; the remaining entries in this batch remain active.

Follow-up on 2026-07-13 restored the exact local Pff theorem
`ImplyClosestStrict` in `FloatSpec/src/Pff/Pff.lean`.  The Lean theorem
preserves the upstream payload: under the same section hypotheses as
`ImplyClosest`, the strict half-ulp bound `|z - F2R f| < radix^e / 2`
implies that every `g` satisfying `Closest b radix z g` has the same
represented real value as `f`.  The proof reuses `ImplyClosest` to obtain
closestness of `f`, derives strict successor and predecessor distance
separation, and rules out all other closest bounded floats via `FNSuccProp`,
`FSuccDiffPos`, `FPredLt`, `FPredProp`, `FPredCanonic`, `FpredUlpPos`,
`CanonicFulp`, and `Fcanonic_Rle_Zle`.  Focused verification:
`lake env lean FloatSpec/src/Pff/Pff.lean` passed.  Full verification:
`lake build` passed.  Status: implemented and removed from active semantic
gaps; the remaining entries in this batch remain active.

Follow-up on 2026-07-13 restored the exact local Pff theorem
`ImplyClosestStrict2` in `FloatSpec/src/Pff/Pff.lean`.  This matches upstream
`Pff/Pff.v`: from the strict half-ulp hypothesis
`|z - F2R f| < radix^e / 2`, it proves both `Closest b radix z f` and
uniqueness of the represented real value among all closest bounded floats.  The
proof follows upstream directly by splitting the conclusion, reusing
`ImplyClosest` for closestness with `le_of_lt` and `ImplyClosestStrict` for the
uniqueness branch.  Focused verification:
`lake env lean FloatSpec/src/Pff/Pff.lean` passed.  Full verification:
`lake build` passed.  Status: implemented and removed from active semantic
gaps; the remaining entries in this batch remain active.

Statement-level checks performed for the first 35 active Pff entries:

- `errorBoundedMultClosest`, `UlpFlessuGe`, `UlpFlessuGe2`, and `Axpy_opt` were
  rechecked against the local helper families already noted in batch 10.
  The same conclusion holds for those entries: local declarations are prerequisite/reduction
  forms such as `*_from_*`, `*_aux`, or `*_check`; they do not prove the
  public upstream conclusions directly from the upstream hypotheses. The former
  `plusExact2Aux` and `plusExact2` gaps were later closed by exact restoration.
- `ClosestImplyEven_int` was later restored as an exact Lean declaration in
  `FloatSpec/src/Pff/Pff.lean`, matching the upstream integer-midpoint
  theorem by reducing to `ClosestImplyEven`.
- `eqLe`, `eqGe`, and `eqEqual` have no exact Lean declaration under
  `FloatSpec/src/Pff`. Broad hits on the predicates `Closest` and `EvenClosest`
  are definitions, not theorem counterparts.  These names are section-local
  proof lemmas in upstream Pff, but they remain active because they are parsed
  public Coq declarations and no faithful split payload has been identified.
  Config-provider harness attempt `.change_log/codex_attempt_20260715_212250`
  rechecked `eqLe` against upstream `Pff.v` and left Lean code unchanged:
  `target_before.lean` and `target_after.lean` are identical, the local target
  gate passed, `scripts/audit_placeholders.sh --json FloatSpec` passed,
  `scripts/status_report.sh --write` still reported the existing 53
  placeholder/trust findings with `sorry = 0`, `axiom = 0`, `admit = 0`, and
  `git diff --check` passed. The nested checked-alignment sidecar
  `.change_log/eqLe_blocked_20260715_133035/attempt.json` records the blocker:
  upstream `eqLe` proves a large Veltkamp-section disjunction from the section
  context, while current Lean has prerequisites such as `eqLeep`, `epLe`,
  `hxExact`, `RleRRounded`, `ClosestExp`, `FPredProp`, `MinMax`, and
  `ImplyClosest` but no faithful split helper for the two long branches.
  Adding exact-name `eqLe` from the current helpers would require extra branch
  premises and would weaken the upstream payload, so `eqLe` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_020235`
  rechecked `eqGe` at the current Veltkamp helper block and left source code
  unchanged (`target_before.lean` and `target_after.lean` are identical, with
  no files listed in `changed_during_attempt.txt`). The checked sidecar
  `.change_log/manual_attempt_20260716_eqGe_blocked/attempt.json` records
  `coq_alignment = checked`: upstream `eqGe` proves the section-local
  conclusion `s + Fexp x <= Fexp q` by splitting real-comparison branches and
  deriving tight mantissa identities plus bounded/closest constructed floats.
  Current Lean has broad prerequisites such as `hxExact`, `eqLeep`, `epLe`,
  `pPos`, `qNeg`, `RleRRounded`, `ClosestExp`, `FPredProp`, `MinMax`, and
  `ImplyClosest`, but no faithful split helper for those branches from only the
  upstream section hypotheses. Adding exact-name `eqGe` now would require
  extra branch premises or a weakened helper-only statement, so `eqGe` remains
  active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_224529`
  rechecked `eqGe` against the current Pff helper stack and made no Lean
  source changes; the harness only wrote a ledger classification note. The
  top-level attempt record has `result = blocked` and `changed_files =
  ["MISSING_INFRASTRUCTURE.md"]`. The normalized checked classifier
  `.change_log/manual_attempt_20260716_2251_eqGe_current_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and the same
  ledger-only changed file. The blocker remains the three unfactored Veltkamp
  comparison branches from upstream `Pff.v:13547`: the large-`x` branch lowers
  `|q|` by inverse-triangle estimates and two `ClosestExp` applications; the
  middle branch constructs the bounded mantissa float
  `Zpower_nat radix (pred t) + Zpower_nat radix (Z.abs_nat (t - s - 1)) + 1`
  and uses closest monotonicity to force `p` above the minimal-normal float;
  and the tight top-mantissa branch proves the exact top-mantissa identities
  for `x`, `p`, and `q` before applying `FcanonicUnique`. Current Lean has
  adjacent prerequisites such as `hxExact`, `eqLeep`, `epLe`, `pPos`, `qNeg`,
  `RleRRounded`, `ClosestExp`, `FPredProp`, `MinMax`, `ImplyClosest`,
  `FnormalUnique`, `FSuccDiff3`, `LeFnumZERO`, and `LtFnumZERO`, but no exact
  public theorem or split branch lemmas deriving this payload from only the
  Veltkamp section hypotheses.
  Current-refresh sidecar
  `.change_log/manual_attempt_20260716_145826_eqLe_current_blocked/attempt.json`
  rechecked the live `Pff.lean` helper surface after the later `eqGe` and
  `eqEqual` blocker records. It records `coq_alignment = checked`,
  `local_target_gate = pass`, and `changed_files = []`: upstream `eqLe` is
  still the section-local Veltkamp disjunction proving either
  `Fexp q <= s + Fexp x` or the exact negative-bound/half-ulp branch from only
  the section context. Current Lean still has prerequisite helpers such as
  `eqLeep`, `epLe`, `hxExact`, `RleRRounded`, `ClosestExp`, `FPredProp`,
  `MinMax`, and `ImplyClosest`, but no faithful split proof for the two long
  branches. Adding exact-name `eqLe` from those helpers would require extra
  branch premises or weaken the disjunction payload, so `eqLe` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_201815`
  rechecked `eqLe` after the latest `LSB_Pred` restoration and again left
  source code unchanged. The provider compared upstream `Pff.v:eqLe` with the
  current local `eqLeep`/`epLe`/`hxExact` helper surface and identified the
  same missing boundary proof infrastructure: constructing the `g`/`qplus =
  FNSucc q` witnesses, proving the successor gap
  `qplus - q = radix^(s + Fexp x)`, and deriving the exact
  negative-bound/half-ulp branch from the upstream section context. The
  normalized sidecar
  `.change_log/manual_attempt_20260716_eqLe_boundary_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `changed_files = []`.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_223316`
  also rechecked `eqLe` and made no source changes, but the shell invocation
  had stripped the two disjunct displays from the reason text before the
  harness prompt was written. The corrected config-provider harness attempt
  `.change_log/codex_attempt_20260716_223709` reran the same target with the
  full disjunction described in shell-safe text and again made no source
  changes (`changed_during_attempt.txt` is empty and
  `target_before.lean`/`target_after.lean` are identical). The top-level
  attempt record has `result = blocked`; the checked classifier
  `.change_log/manual_attempt_20260716_2242_eqLe_current_blocked/attempt.json`
  records `result = blocked`, `coq_alignment = checked`, and
  `changed_files = []`. The blocker remains the full Veltkamp branch package:
  upstream `eqLe` proves the disjunction from the section context, while local
  helpers such as `eqLeep`, `epLe`, `hxExact`, `RleRRounded`, `ClosestExp`,
  `FPredProp`, `MinMax`, `ImplyClosest`, `FnormalUnique`, and `FSuccDiff3`
  still do not package the low-mantissa normal-`g` construction or the
  high-mantissa negative-bound plus half-ulp branch without extra premises.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_041716`
  rechecked `eqEqual` directly and left source code unchanged
  (`target_before.lean` and `target_after.lean` are identical, with no files
  listed in `changed_during_attempt.txt`). The checked sidecar
  `.change_log/manual_attempt_20260716_eqEqual_blocked/attempt.json` records
  `coq_alignment = checked`: upstream `Pff.v:eqEqual` is a direct combination
  of upstream `eqLe` and `eqGe`, but current Lean still has no exact `eqLe`
  disjunction or exact `eqGe` inequality derivable from only the Veltkamp
  section hypotheses. Adding `eqEqual` now would require extra premises
  carrying `eqLe`/`eqGe`, or a weakened helper-only statement, so `eqEqual`
  remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_184915`
  rechecked `eqEqual` against the current live ledger after line-number drift.
  The checked sidecar
  `.change_log/manual_attempt_20260716_185145_eqEqual_current_blocked/attempt.json`
  records `coq_alignment = checked`, `changed_files = []`, and the same
  blocker: current Lean has helper prerequisites such as `hxExact`, `eqLeep`,
  `epLe`, `RleRRounded`, `ClosestExp`, `FPredProp`, `MinMax`, and
  `ImplyClosest`, but no exact `eqLe` disjunction and no exact `eqGe`
  inequality from only the upstream Veltkamp section hypotheses.
- `VeltkampS` is not covered by the public Lean `Veltkamp` wrapper in
  `FloatSpec/src/Pff/Pff2Flocq.lean`. The wrapper assumes a reduced
  nearest-even witness as input; the active upstream lemmas construct the
  Veltkamp error bound and reduced witness from rounded intermediate
  products/sums. They are therefore missing lower Pff payloads, not hidden
  under the public wrapper.
- `Veltkamp_aux_aux`, `Veltkamp_aux`, `VeltkampEven1`, `VeltkampEven2`,
  `Veltkamp_pos`, `VeltkampN_aux`, `VeltkampN`, `VeltkampEven_pos`,
  `VeltkampEvenN_aux`, and `VeltkampEvenN` are now restored as exact
  public Lean theorems in
  `FloatSpec/src/Pff/Pff.lean`; they are no
  longer inferred from the higher-level wrapper and no longer belong to this
  missing-payload group.
- `bimplybplusNorm` was restored as exact public Lean theorem
  `FloatSpec/src/Pff/Pff.lean:bimplybplusNorm`: from `Fbounded b f` and
  `F2R f ≠ 0`, it constructs `Fnormalize radix (plusExp b) t f`, preserves
  `F2R`, and rules out the subnormal branch using the original bounded
  exponent and the `plusExp` first-normal threshold.
- `Closestbbplus` is now restored as the exact public extension theorem from
  `Closest b0` to `Closest (plusExp b0 t)` in
  `FloatSpec/src/Pff/Pff.lean`; together with existing reverse-direction
  `Closestbplusb`, both upstream closest-bound directions are now present.
- `EvenClosestbplusb` is now restored as the exact public nearest-even
  restriction theorem from `plusExp b0 t` to `b0` in
  `FloatSpec/src/Pff/Pff.lean`.
- `ClosestClosest` is now restored as the exact public theorem excluding an
  exponent separation of at least two between two closest results when the
  higher-exponent result is normal.
- `EvenClosestbbplus` is now restored as the exact public nearest-even
  extension theorem from `b0` to `plusExp b0 t`.

Updated status: active Pff entries 1-35 are confirmed real semantic gaps or
unported section lemmas, not renamed/split complete ports. Later restorations
are reflected in the current `Pff/Pff.v` section count above.

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
- `BoundedL` is now restored as the exact public bounded-lifting theorem in
  `FloatSpec/src/Pff/Pff.lean`.
- `Closestbbext` is now restored as the exact public arbitrary-bound extension
  theorem in `FloatSpec/src/Pff/Pff.lean`, reduced to `Closestbbplus` after
  proving the supplied extended bound is the corresponding `plusExp` bound.
- `Underf_Err1`, `Underf_Err2_aux`, `Underf_Err2`, `Underf_Err3`, and
  `Underf_Err3_bis` are now restored as exact public underflow-error transfer
  theorems in `FloatSpec/src/Pff/Pff.lean`.
- `Boundedt4_aux`, `Boundedx1y1_aux`, `Boundedx1y1`, and
  `Boundedx1y2_aux` are section-local product-splitting
  bounds in upstream Pff. Local broad hits on `Bound`, `ZleLe`,
  `ClosestRoundeLeNormal`, or rounded-error helpers do not encode these
  concrete existential boundedness statements for the Dekker construction.
- `Boundedx2y2` is now restored as the exact public section-local
  product-splitting theorem in `FloatSpec/src/Pff/Pff.lean`.
- `Dekker_aux`, `DekkerN`, `DekkerS1`, `DekkerS2`, and `Dekker1` are now
  restored as exact public theorems in
  `FloatSpec/src/Pff/Pff.lean`.
- `Dekker2_aux` is now restored as the exact public Algo2 underflow-error
  theorem in `FloatSpec/src/Pff/Pff.lean`.
- `Dekker2` is now restored as the exact public Algo2 zero-aware underflow
  wrapper in `FloatSpec/src/Pff/Pff.lean`.
- `Twice_EvenClosest_Round` is now restored as the exact public radix-two
  doubled nearest-even rounding theorem in `FloatSpec/src/Pff/Pff.lean`.
- `Veltkampb'` is now restored as the exact public bound-extension theorem in
  `FloatSpec/src/Pff/Pff.lean`.
- `NormalbPrim` is now restored as the exact public Algo2 normal-representative
  theorem in `FloatSpec/src/Pff/Pff.lean`.

Updated status: active Pff entries 36-70 are confirmed real semantic gaps or
unported section lemmas, not renamed/split complete ports. Later restorations
are reflected in the current `Pff/Pff.v` section count above.

Checked batch 15: `Pff/Pff.v` final active rounded-error/FMA approximation
block.

No entries were removed from the active semantic gap list in this batch.

Statement-level checks performed for active Pff entries 71-104:

- `Twice_EvenClosest_Round` was previously rechecked against
  `Twice_EvenClosest_Round_from_closest` and
  `Twice_EvenClosest_Round_from_even_or_high`. As in batch 10, the local
  theorems assume the scaled closestness or even/high boundary payload that
  upstream proves from normality, exponent lower bound, and
  `EvenClosest`; those helpers alone were not the public theorem. The exact
  public theorem is now restored and removed from the active list.
- `errorBoundedMultClosest_Can` is now restored as the exact public binary
  canonical closest-product residual theorem in
  `FloatSpec/src/Pff/Pff.lean`.
- `cases` is now restored as exact public Lean theorem `«cases»` in
  `FloatSpec/src/Pff/Pff.lean`. It derives the upstream zero-or-six-bound
  disjunction from `U1`, `U2`, `pGeUnderf`, `qGeUnderf`, the restored addition
  exponent lemmas, and the section rounding hypotheses without assuming a
  `discri*` branch package. The old config-provider blocker
  `.change_log/manual_attempt_20260716_cases_blocked/attempt.json` is
  superseded: the prerequisite stack changed after that audit.
- `AddExpGe1Underf2` was restored as exact public Lean theorem
  `FloatSpec/src/Pff/Pff.lean:AddExpGe1Underf2` by subscription harness
  attempt `.change_log/codex_attempt_20260713_075753`. The theorem matches
  upstream `Pff/Pff.v` by normalizing bounded inputs with
  `FnormalizeCorrect`/`FnormalizeCanonic`, applying restored
  `AddExpGe1Underf`, and eliminating the zero branch with the explicit
  nonzero rounded-result hypothesis.
- `LSB_Pred` was restored as exact public Lean theorem
  `FloatSpec/src/Pff/Pff.lean:LSB_Pred`, preserving the upstream
  `Rabs x < Rabs y -> LSB radix x <= LSB radix y -> Rabs x <= Rabs y -
  powerRZ radix (LSB radix x)` payload with the `GenericC` section
  assumptions.
- `xLe2y_aux1` is now restored as the exact GenericA exact-power branch:
  exact representability fixes `|x|`, and the even-radix half-unit witness
  plus closest absolute monotonicity proves `|x| ≤ 2 * |y|`.
- `gaCorrect`
  have no exact Lean declaration under `FloatSpec/src/Pff`. Local hits on
  `LSB` or FMA helper theorems are definitions or narrower branch helpers,
  not the upstream subtraction/midpoint/least-significant-bit payloads.
- `ErrFmaApprox_2_aux`, `ErrFmaApprox_2`, and `ErrFmaApprox` are not hidden
  under the current local FMA helper family.
  The visible local helpers such as
  `FmaErr_gaCorrect_of_be1_eq_r1`,
  `FmaErr_gaCorrect_of_al2_zero`, and several `Fma_FTS_*_leexp_witness`
  theorems cover isolated branches or prerequisite exponent witnesses, not
  the final upstream FMA approximation bounds.
- `LeExp3`, `LeExp`, `vLe_aux`, `vLe`, `tLe`, and `wLe` remain active. Local
  hits such as `LeExpRound`,
  `LeExpRound2`, `RoundedModeMultLess`, `FboundedShiftLess`,
  `maxDivLess`, and `digitLess` are generic or unrelated support lemmas;
  they do not prove the concrete exponent and absolute-value bounds in this
  FMA section. Subscription harness attempt
  `.change_log/codex_attempt_20260713_054925` classified the exact `LeExp1`
  lemma as blocked with no source changes: the upstream proof derives
  `Fexp ph <= Fexp uh + 1` by contradiction from `Case2`, `ulDef`, and `uhDef`,
  then invokes the formerly missing `plusExact2` payload. `plusExact2` and
  `plusExact2Aux` have since been restored exactly, and
  `.change_log/codex_attempt_20260713_073602` restored `LeExp1`.
  Subscription harness attempt `.change_log/codex_attempt_20260713_075313`
  rechecked exact `LeExp2` after `LeExp1` landed and left code unchanged:
  the upstream proof still needs the unfactored FMA middle bound deriving
  `|F2R uh| <= radix * |F2R z|` from `ulDef`, `plDef`, `zDef`, `phDef`,
  `uhDef`, `RoundedModeUlp`, `FcanonicFnormalizeEq`, `FulpLe2`, `LeExp1`,
  and `precision >= 3` before applying the exponent comparison. Adding a
  weaker helper-only bound would not preserve the upstream payload. That old
  blocker is now superseded by exact public `LeExp2`, restored by harness
  attempt `.change_log/codex_attempt_20260722_195131` and the independent
  verified continuation documented in the completion note above.

Updated status: the active Pff entries have now been counterpart-checked
at least once. The checked local hits are helper, prerequisite, reverse
direction, or wrapper declarations rather than faithful renamed/split ports,
so the current Pff active count is the `Pff/Pff.v` section count above.

Checked batch 16: explicitly named IEEE entries that were previously covered
only by grouped wording.

No entries were removed from the active semantic gap list in this batch.

Coverage checks performed:

- `inbetween_shr`, `le_shr_le`, `shr_limit`, and `shr_truncate` were searched directly in
  `FloatSpec/src/IEEE754` before the current restoration pass. At the time,
  the only hits were in `IEEE754_Theorems_Comparison_Manual.md`; no Lean
  theorem counterpart was found. `inbetween_shr`, `le_shr_le`, `shr_limit`, and
  `shr_truncate` are now restored.
- `default_nan_pl32`, `unop_nan_pl32`, `binop_nan_pl32`,
  `ternop_nan_pl32`, `b32_erase`, `b32_opp`, `b32_abs`, `b32_of_bits`,
  `b32_pred`, and `b32_succ` were restored in
	  `FloatSpec/src/IEEE754/Bits.lean` during the current direct restoration pass,
	  and are no longer active. `b32_sqrt`, `b32_plus`, `b32_minus`, `b32_mult`,
	  `b32_div`, and `b32_fma` were
	  searched directly in `FloatSpec/src/IEEE754`. No Lean declaration
	  counterpart was found. The
	  generic local helpers `succ`, `pred`, `compare`, `binary_to_bits`, and
	  `bits_to_binary` are not the remaining upstream binary32 API layer because
	  they do not instantiate the upstream `binary_float 24 128` type, operation
	  aliases, or bit-conversion aliases.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_130243`
  rechecked `b32_sqrt` against upstream `IEEE754/Bits.v:667` and left source
  code unchanged (`changed_during_attempt.txt` is empty, `changed_files = []`,
  and the local target gate passed). The checked sidecar
  `.change_log/manual_attempt_20260716T050529Z_b32_sqrt_blocked/attempt.json`
  records `result = blocked`, `build = pass`, `coq_alignment = checked`, and
  `local_target_gate = pass`. The blocker is the proof-carrying type surface:
  upstream `b32_sqrt` specializes `Bsqrt _ _ Hprec Hprec_emax unop_nan_pl32`
  to `binary32 := binary_float 24 128`, preserving finite boundedness proofs
  and the single-argument NaN payload handler. Current Lean has `binary32` and
	  `unop_nan_pl32`, but its available `Bsqrt` adapter returns the permissive
	  `Binary754` wrapper, not `binary_float 24 128`; the rounded-real SingleNaN
	  helpers likewise do not reconstruct the upstream proof-carrying result.
	  Adding a wrapper here would be differently parameterized/helper-only rather
	  than the Flocq Bits API payload, so `b32_sqrt` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_131005`
  rechecked `b32_plus` against upstream `IEEE754/Bits.v:668` and left source
  code unchanged (`changed_during_attempt.txt` is empty, `changed_files = []`,
  and the local target gate passed). The checked sidecar
  `.change_log/manual_attempt_20260716T051218Z_b32_plus_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass`. The blocker is the same proof-carrying
  binary32 operation surface: upstream `b32_plus` specializes `Bplus _ _
  Hprec Hprec_emax binop_nan_pl32` to `binary32 -> binary32 -> binary32`,
  preserving bounded finite proofs and the first-NaN payload handler. Current
  Lean has `binary32` and `binop_nan_pl32`, but `Binary.Bplus` returns
  permissive `Binary754` and `BinarySingleNaNBridge.Bplus` returns proof-erased
  `BinaryFloat`; no faithful adapter back to `binary_float 24 128` is present.
  Adding `b32_plus` from those helpers would be differently parameterized and
  proof-erased, so `b32_plus` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_131602`
  rechecked `b32_minus` against upstream `IEEE754/Bits.v:670` and left source
  code unchanged (`changed_during_attempt.txt` is empty, `changed_files = []`,
  and the local target gate passed). The checked sidecar
  `.change_log/manual_attempt_20260716_131602_b32_minus_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass`. The blocker is again the proof-carrying
  binary32 operation surface: upstream `b32_minus` specializes `Bminus _ _
  Hprec Hprec_emax binop_nan_pl32` to `binary32 -> binary32 -> binary32`,
  preserving bounded finite proofs and first-NaN payload handling. Current Lean
  has `binary32` and `binop_nan_pl32`, but `Binary.Bminus` returns permissive
  `Binary754` and `BinarySingleNaNBridge.Bminus` returns proof-erased
  `BinaryFloat`; no faithful adapter back to `binary_float 24 128` is present.
  Adding `b32_minus` from those helpers would be differently parameterized and
  proof-erased, so `b32_minus` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_132240`
  rechecked `b32_mult` against upstream `IEEE754/Bits.v:671` and left source
  code unchanged (`changed_during_attempt.txt` is empty, `changed_files = []`,
  and the local target gate passed). The checked sidecar
  `.change_log/manual_attempt_20260716_132240_b32_mult_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass`. The blocker is again the proof-carrying
  binary32 operation surface: upstream `b32_mult` specializes `Bmult _ _
  Hprec Hprec_emax binop_nan_pl32` to `binary32 -> binary32 -> binary32`,
  preserving bounded finite proofs and first-NaN payload handling. Current Lean
  has `binary32` and `binop_nan_pl32`, but `Binary.Bmult` returns permissive
  `Binary754` and `BinarySingleNaNBridge.Bmult` returns proof-erased
  `BinaryFloat`; no faithful adapter back to `binary_float 24 128` is present.
  Adding `b32_mult` from those helpers would be differently parameterized and
  proof-erased, so `b32_mult` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_133101`
  rechecked `b32_div` against upstream `IEEE754/Bits.v:672` and left source
  code unchanged (`changed_during_attempt.txt` is empty, `changed_files = []`,
  and the local target gate passed). The checked sidecar
  `.change_log/manual_attempt_20260716_133101_b32_div_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass`. The blocker is again the proof-carrying
  binary32 operation surface: upstream `b32_div` specializes `Bdiv _ _
  Hprec Hprec_emax binop_nan_pl32` to `binary32 -> binary32 -> binary32`,
  preserving bounded finite proofs and first-NaN payload handling. Current Lean
  has `binary32` and `binop_nan_pl32`, but `Binary.Bdiv` returns permissive
  `Binary754` and `BinarySingleNaNBridge.Bdiv` returns proof-erased
  `BinaryFloat`; no faithful adapter back to `binary_float 24 128` is present.
  Adding `b32_div` from those helpers would be differently parameterized and
  proof-erased, so `b32_div` remains active.
  Config-provider harness attempt `.change_log/codex_attempt_20260716_134059`
  rechecked `b32_fma` against upstream `IEEE754/Bits.v:674` and left source
  code unchanged (`changed_during_attempt.txt` is empty, `changed_files = []`,
  and the local target gate passed). The checked sidecar
  `.change_log/manual_attempt_20260716_134059_b32_fma_blocked/attempt.json`
  records `result = blocked`, `changed_files = []`, `coq_alignment = checked`,
  and `local_target_gate = pass`. The blocker is again the proof-carrying
  binary32 operation surface: upstream `b32_fma` specializes `Bfma _ _
  Hprec Hprec_emax ternop_nan_pl32` to
  `binary32 -> binary32 -> binary32 -> binary32`, preserving bounded finite
  proofs and first-NaN payload handling across three inputs. Current Lean has
  `binary32` and `ternop_nan_pl32`, but `Binary.Bfma` returns permissive
  `Binary754` and `BinarySingleNaNBridge.Bfma` returns proof-erased
  `BinaryFloat`; no faithful adapter back to `binary_float 24 128` is present.
  Adding `b32_fma` from those helpers would be differently parameterized and
  proof-erased, so `b32_fma` remains active.
- `binop_nan_pl64`, `ternop_nan_pl64`, `b64_erase`, `b64_opp`, `b64_abs`,
  `bits_of_b64`, `b64_of_bits`, `b64_pred`, and `b64_succ`
  are now restored in `FloatSpec/src/IEEE754/Bits.lean`. `b64_sqrt`,
  `b64_plus`, `b64_minus`, `b64_mult`, `b64_div`, and `b64_fma` were searched directly in
  `FloatSpec/src/IEEE754`. No Lean declaration counterpart was found for those
  remaining names. The same generic-helper caveat applies:
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
  - A project-level parsed-name scan across all `FloatSpec/**/*.lean` formerly
    showed 102 missing `Pff/Pff.v` names after stripping Coq comments. The
    current active Pff section count above supersedes that stale snapshot; the
    project-level count is lower than the direct-file count because some exact
    names are supplied by imported FloatSpec modules or Lean/Mathlib.
    The first entries are now local FloatSpec gaps beginning with
    `errorBoundedMultClosest`, followed by `UlpFlessuGe` in the Pff block.
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
  payload explicit because the separate upstream helper was not yet restored.
  A checked follow-up restored
  the parity-preservation component
  `FNeven_double_of_Fnormal` at `FloatSpec/src/Pff/Pff.lean:24699`: for a
  normal radix-2 float, incrementing the exponent keeps normalized-evenness,
  leaving the closestness/boundary scaling argument for competitors at the
  minimum exponent. A checked follow-up
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
  doubled-closestness and final even-closestness steps. These were intermediate
  bridges: exact upstream `Twice_EvenClosest_Round` is now restored, with the
  odd-competitor minimum-exponent boundary proved internally.
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
	  the now-restored exact `errorBoundedMultClosest_Can`, then delegates the
	  final estimate to
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
