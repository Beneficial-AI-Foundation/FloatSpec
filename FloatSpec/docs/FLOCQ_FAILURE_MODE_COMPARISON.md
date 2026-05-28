# FloatSpec Failure Modes vs Upstream Flocq

Date: 2026-05-25

Upstream checked out locally at `/mnt2/users/kaile/hantao/flocq-upstream`.

Upstream commit:

```text
7aab8f5 New release.
```

Scope: compare the failure modes found in `PROOF_SPEC_AUDIT.md` against upstream Flocq. This intentionally excludes VCFloat-style error-bound analysis as a target, but still looks at core rounding, Calc, ULP, Prop scaffolding, Pff, IEEE754, and primitive-float bridge files when they explain whether a FloatSpec weakness is inherited or introduced by translation.

Update 2026-05-27: [EXISTING_SPEC_MISALIGNMENT.md](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/docs/EXISTING_SPEC_MISALIGNMENT.md) narrows this comparison to accepted non-`sorry` specs. It classifies upstream-aligned `True` cases to ignore, records the `Round_NE` axiom provenance, and lists the remaining accepted surfaces that still diverge from Flocq.

## Executive Summary

The audited failure modes are overwhelmingly translation-pipeline debt, not flaws rooted in upstream Flocq.

Upstream Flocq has real definitions and completed proof chains for the major surfaces where FloatSpec currently uses `True`, identity functions, constants, no-op truncation, mode-erased rounding, and `sorry` bridges. A search over upstream `src/Core`, `src/Calc`, `src/Prop`, `src/Pff`, and `src/IEEE754` did not find `Admitted`, `Axiom`, or `Parameter` declarations explaining the audited failures.

So the immediate policy should be:

- Fix translation-created semantic collapse in the trusted core.
- Exclude large or nonessential surfaces for now when they are too expensive, but label them as project-scope exclusions, not upstream-Flocq defects.
- Do not count a theorem as translated if its Lean statement was weakened, if a semantic parameter was replaced by `True`/`Unit`, or if the proof closes only because the implementation is an identity/constant placeholder.

## Classification Table

| FloatSpec failure mode | Upstream Flocq status | Classification | Fix or current action |
|---|---|---|---|
| Rounding modes erased by `Calc.Round.Mode := Unit` and mode-insensitive `round` | `src/Core/Generic_fmt.v` defines and proves mode-sensitive results such as `round_DN_opp`, `round_UP_opp`, `round_ZR_opp`, `round_ZR_DN`, and `round_DN_pt` by unfolding real `round` and using integer rounding operators. | Translation-pipeline debt | Replace `Mode := Unit` with real directed/nearest rounding structure. Route `Calc.Round.round` to a mode-aware core round, not `round_to_generic ... (fun _ _ => True)`. Preserve `Valid_rnd` assumptions instead of fabricating them. |
| Mode-specific equivalence theorems proved because rounding ignores mode | Upstream proofs distinguish DN, UP, ZR, AW, and nearest behavior. | Translation-pipeline debt | Delete or quarantine definitional-artifact theorems. Re-port the upstream statements after real rounding-mode semantics are available. |
| Nearest rounding hardcodes UP on ties | Upstream nearest rounding uses supplied choice/tie functions and has separate nearest/even developments. | Translation-pipeline debt | Model nearest as a parameterized nearest choice. Add nearest-even only after tie parity and uniqueness lemmas are ported. |
| `truncate_aux` and `truncate` are identity/no-op placeholders | `src/Calc/Round.v` implements real `truncate_aux` and proves `inbetween_float_round`, `inbetween_float_DN`, `round_sign_DN`, and related sign/location facts. | Translation-pipeline debt | Port `Calc/Round.v` machinery in dependency order. The Lean truncation result must actually adjust mantissa/exponent/location. |
| `Fplus_core`/`Fplus` correctness closes by always returning `loc_Exact` | `src/Calc/Plus.v` defines `Fplus_core` using real truncation and proves both location/exponent conditions and `inbetween_float`. | Translation-pipeline debt | Re-port `Fplus_core_correct` and `Fplus_correct` from upstream. The target spec must include the in-between result, not just a location branch. |
| DN/UP existence, no-gap, tie uniqueness, and scaled-mantissa facts are private `sorry` bridges | Upstream `Generic_fmt.v`, `Round_NE.v`, and `Ulp.v` contain completed chains for directed rounding, nearest ties, and spacing. | Translation-pipeline debt | Port the prerequisite chain instead of using bridge lemmas: directed-rounding point lemmas, monotonicity with radix assumptions, consecutive-mantissa facts, then nearest/tie lemmas. |
| Missing radix assumptions in monotonicity/magnitude lemmas | Upstream theorem contexts carry the required radix/format assumptions through section variables and hypotheses. | Translation-pipeline debt | Make assumptions explicit in Lean theorem signatures when typeclass inference cannot recover them. Add an anti-weakening check that flags upstream hypotheses dropped during translation. |
| ULP half-error and nearest-rounding public theorems depend on private bridge facts | `src/Core/Ulp.v` defines real `ulp` and proves chains including `round_DN_plus_eps`, `succ_le_lt`, `pred_succ`, `error_le_half_ulp`, and `round_N_plus_ulp_ge`. | Translation-pipeline debt, but expensive | Fix by porting in Coq order: `ulp` basics, successor/predecessor, DN/UP epsilon lemmas, half-ULP error, then nearest-plus-ULP. If the current milestone is only core directed rounding, exclude higher ULP-nearest theorems for now. |
| Compatibility layer weakens `Valid_rnd`, `Monotone_exp`, `Exp_not_FTZ` to `True` and makes operations identities | Upstream has real typeclass-style assumptions and real operations distributed across core/Calc/Pff/IEEE modules. | Translation-pipeline debt | Replace compatibility placeholders with aliases/imports to real translated classes and operations. If a shim is needed for bootstrapping, put it under an explicit experimental namespace unavailable to trusted imports. |
| Prop barrel disabled and Prop modules are mostly skeletons | Upstream `src/Prop/Relative.v`, `Plus_error.v`, `Double_rounding.v`, and related files contain nontrivial completed proofs. | Translation-pipeline debt; exclude selectively | Re-enable the barrel only after leaf modules compile with real proofs. Port `Relative` first, then lightweight arithmetic properties. Exclude heavy error-bound and double-rounding surfaces from the current milestone if they are outside scope. |
| Pff predicates such as `MinRoundedModeP`, `MaxRoundedModeP`, and canonical closest predicates collapse to `True`/hypotheses | Upstream `src/Pff/Pff.v` and `Pff2FlocqAux.v` define real digit/length helpers, rounded-mode predicates, closest predicates, and Pff-to-Flocq connections. | Translation-pipeline debt; exclude now | Do not trust current Pff. Exclude Pff from the near-term trusted surface because it is large and legacy. If needed later, translate definitions/proofs from upstream rather than retaining placeholder predicates. |
| Pff numeric helpers are constants, no-ops, or conclusion-as-hypothesis theorem statements | Upstream Pff has actual recursive/numeric definitions such as `digitAux`, `digit`, `pos_length`, and real rounding correctness theorems. | Translation-pipeline debt; exclude now | Quarantine Pff under an excluded or experimental import path. Add a statement-equivalence gate before any future Pff translation is counted. |
| IEEE `Binary` and `BinarySingleNaN` round/normalize operations are placeholders | Upstream `src/IEEE754/BinarySingleNaN.v` computes with `shr_fexp`, `choice_mode`, `binary_fit_aux`, and real overflow/validity cases; `Binary.v` wraps and proves correctness. | Translation-pipeline debt; exclude until ported | Port `BinarySingleNaN` first, then `Binary`. Until then, exclude IEEE arithmetic/normalize/rounding theorems from the trusted surface. |
| `PrimFloat` bridge collapses conversions and comparison specs to constants | Upstream `src/IEEE754/PrimFloat.v` uses Coq primitive-float conversions `Prim2SF`/`SF2Prim` and proves roundtrip/injection/comparison equivalence lemmas. | Translation-pipeline debt plus target-platform mismatch risk | Exclude `PrimFloat` unless Lean has a precise primitive-float bridge suitable for the same semantics. Otherwise model IEEE values abstractly and keep primitive runtime conversion separate from proofs. |
| Boolean comparison specs changed to constant behavior | Upstream proves comparison equivalences for primitive float comparison functions, not constant results. | Translation-pipeline debt | Add a generated-spec check that rejects constant comparator implementations unless the upstream definition is constant. |

## Rooted-in-Flocq Exclusions

None of the audited high-impact failures should be classified as "rooted in Flocq" in the sense of upstream lacking the definition/proof or relying on admitted axioms.

There are still surfaces worth excluding right now, but the reason is project scope and proof-engineering cost:

- `Pff`: very large legacy layer; exclude from the trusted milestone until there is a reason to port it faithfully.
- Heavy `Prop` error analysis and double rounding: exclude if the current milestone intentionally avoids error-bound analysis.
- `PrimFloat`: exclude unless the Lean target has an equivalent primitive-float semantic bridge.
- Full IEEE arithmetic/normalization: exclude until `BinarySingleNaN` and `Binary` are translated from real upstream definitions.
- Higher ULP-nearest theorems: exclude temporarily if the current milestone is only directed rounding and basic generic format properties.

These exclusions should be recorded as "not in trusted surface yet", not as "proved false" or "missing upstream."

## Fix Strategy

### 1. Split trusted, experimental, and excluded imports

Create a clear import boundary:

- Trusted: only modules with real semantics and no `sorry`-backed semantic bridges.
- Experimental: translated names useful for orientation but not trusted.
- Excluded: surfaces intentionally out of scope for the milestone.

The top-level FloatSpec import should not silently include experimental placeholders.

### 2. Add a statement-preservation gate

The pipeline should compare each translated Lean theorem against upstream metadata:

- All upstream hypotheses are preserved or deliberately mapped to equivalent Lean assumptions.
- No theorem conclusion is moved into a hypothesis.
- No semantic relation is replaced by `True`.
- No rounding-mode parameter disappears.
- No operation implementation is replaced by identity/constant behavior unless upstream is also identity/constant.

This would have caught the current `Compat`, `Pff`, `Calc.Round`, `Calc.Plus`, `Binary`, and `PrimFloat` failures.

### 3. Port core in dependency order

The core repair order should be:

1. Real integer rounding and mode abstractions.
2. `Generic_fmt.round` and directed rounding point lemmas.
3. `Calc.Round` truncation and in-between results.
4. `Calc.Plus` correctness using real truncation.
5. ULP basics.
6. Successor/predecessor adjacency.
7. Nearest and half-ULP theorems.

Avoid private bridge lemmas that skip dependency cycles. If a proof is not ready, mark the theorem blocked or excluded rather than preserving the name with a semantic placeholder.

### 4. Repair IEEE only after core/Calc

For IEEE, use this order:

1. `BinarySingleNaN` definitions and validity predicates.
2. `Binary` wrapper lemmas.
3. IEEE rounding modes as real mode semantics.
4. Primitive-float bridge only if Lean can model the same primitive behavior.

Until then, IEEE modules should not be counted as part of the trusted translated surface.

### 5. Keep Pff out of the trust path

Pff is not the shortest path to a principled FloatSpec. Treat it as a legacy compatibility target. If later needed for theorem reuse, start with exact upstream definitions (`digitAux`, `digit`, `pos_length`, rounded-mode predicates, closest predicates) and require the statement-preservation gate before any proof attempts.

## Conclusion

The current repo failure mode is not "Flocq is weak." It is "the translation preserved names and rough module shape while often losing the semantic content that made the upstream theorem meaningful."

For next steps, the project should stop broad placeholder translation, define a trusted subset, and rebuild that subset with strict semantic gates. Anything outside that subset should be explicitly excluded or experimental until translated faithfully.
