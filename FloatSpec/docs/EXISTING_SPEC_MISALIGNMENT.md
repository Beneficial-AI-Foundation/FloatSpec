# Existing Accepted Spec Alignment Check

Date: 2026-05-27

Upstream checked locally at `/mnt2/users/kaile/hantao/flocq-upstream`.

This note classifies existing accepted, non-`sorry` FloatSpec specs and definitions
that looked suspicious in the trust audit. Items that match upstream Flocq are
explicitly marked as ignored. Items that diverge from upstream are translation
debt and must not be counted as trusted Flocq semantics.

## Not Misaligned: Ignore

| FloatSpec surface | Upstream Flocq source | Reason |
|---|---|---|
| `valid_FF` / `Binary754_bounded` return `True` for zero and infinity cases in [Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:484) and [Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:2027) | `/mnt2/users/kaile/hantao/flocq-upstream/src/IEEE754/Binary.v:166` has `valid_binary` returning `true` for zero and infinity. | This is not a placeholder by itself. Non-finite validity being trivial is upstream behavior. |
| `Binary754_in_generic_format` makes zero, infinity, and NaN cases trivial in [Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:1311) | Upstream `binary_float` separates non-finite constructors from finite boundedness obligations. | Treat as aligned shape unless a theorem falsely uses it as finite-format evidence. |
| Hoare-style linter rules that match `=> True` in [HoareStyleLinter.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/Linter/HoareStyleLinter.lean:46) | No Flocq theorem surface. | This is tooling logic, not a proof/spec. |

## Misaligned: Fixed Now

| FloatSpec surface | Upstream Flocq source | Failure mode | Fix |
|---|---|---|---|
| `tie_unique_NE_ax` in [Round_NE.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Round_NE.lean:468) | `/mnt2/users/kaile/hantao/flocq-upstream/src/Core/Round_NE.v` proves nearest-even facts such as `round_NE_pt`; it does not introduce an axiom for tie uniqueness. | Existing Lean code hid an unproved nearest-even tie uniqueness lemma behind a private axiom. | Converted the axiom to a private theorem with `sorry`, so it is visible proof debt instead of an unsound accepted axiom. |

## Misaligned: Still To Fix Or Exclude

| Pattern | Locations | Upstream Flocq source | Failure mode | Required fix |
|---|---|---|---|---|
| Mode-insensitive generic rounding via `round_to_generic ... (fun _ _ => True)` | [Generic_fmt.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Generic_fmt.lean:7435), [Generic_fmt.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Generic_fmt.lean:7604), [Ulp.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Ulp.lean:4775), [FIX.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/FIX.lean:269) | `/mnt2/users/kaile/hantao/flocq-upstream/src/Core/Generic_fmt.v:614` defines `round x := F2R (Float beta (rnd (scaled_mantissa x)) (cexp x))`; later theorems carry a real `rnd : R -> Z` with `Valid_rnd`. | Lean proofs about DN/ZR/magnitude are often about a relation-erased helper, not the upstream rounding operator. | Replace these surfaces with mode-aware `roundR`/`Mode.rnd` semantics, or rename/quarantine as scaffold-only until the upstream statements are ported. |
| IEEE arithmetic computes with relation-erased rounding | [Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:806), [Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:815), [Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:824), [Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:1011), [Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:1020), [Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:1028), [Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:1261), [Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:1283) | `/mnt2/users/kaile/hantao/flocq-upstream/src/IEEE754/Binary.v:947`, `:1049`, `:1162`, `:1193`, and `:1291` define operations through `BinarySingleNaN` and prove correctness with `round_mode m`. | Current Lean operations do not implement the upstream BinarySingleNaN algorithms and ignore the mode relation at the rounding point. | Keep under experimental/excluded status until `BinarySingleNaN` and `Binary` are ported with real `round_mode` semantics. |
| Primitive-float bridge maps every primitive value to positive zero | [PrimFloat.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/PrimFloat.lean:70), plus constant comparison checks at [PrimFloat.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/PrimFloat.lean:1063), [PrimFloat.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/PrimFloat.lean:1090), [PrimFloat.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/PrimFloat.lean:1118) | `/mnt2/users/kaile/hantao/flocq-upstream/src/IEEE754/PrimFloat.v:30` defines `Prim2B x := SF2B (Prim2SF x) ...`, and proves roundtrip/comparison lemmas such as `B2Prim_Prim2B`, `Prim2B_B2Prim`, `eqb_equiv`, `ltb_equiv`, and `leb_equiv`. | Lean proves equivalences for an all-zero embedding, not primitive-float semantics. | Keep the whole module experimental unless Lean gets an equivalent primitive-float semantic bridge. |
| Pff placeholder predicates and conclusion-forwarding surfaces | [Pff.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Pff/Pff.lean:591), [Pff.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Pff/Pff.lean:618), [Pff.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Pff/Pff.lean:804) | Upstream `/mnt2/users/kaile/hantao/flocq-upstream/src/Pff/Pff.v` defines real boundedness, projector, canonical, and rounding predicates. | Lean placeholders preserve names while losing predicate content. | Exclude Pff from trusted imports until the definitions are translated faithfully. |

## Axiom Provenance

`tie_unique_NE_ax` was not newly introduced in the current work. Before the fix
above, `git show HEAD:FloatSpec/src/Core/Round_NE.lean` already contained the
private axiom, and `git blame` attributes the original axiom line to commit
`8f861f5db` dated 2025-10-01.

After the current fix, the repo should report zero `axiom` occurrences; the same
gap is now counted as ordinary `sorry` proof debt.

## Conclusion

The remaining accepted-spec risks are not Flocq defects. They are translation
or scaffolding gaps. Ignore audit hits that are upstream-aligned constructor
validity cases, but do not trust relation-erased rounding, all-zero primitive
bridges, or Pff placeholder predicates as Flocq-aligned specs.
