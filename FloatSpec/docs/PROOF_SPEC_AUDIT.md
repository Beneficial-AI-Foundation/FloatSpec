# FloatSpec Proof and Spec Audit

Date: 2026-05-25

Scope: current `FloatSpec` tree, excluding VCFloat-style `ErrorBound` analysis as a target. This audit focuses on existing proof/spec reliability: placeholders, weakened statements, mode erasure, hidden dependency gaps, and theorem surfaces that compile or are scaffolded but do not yet carry the intended Flocq/IEEE semantics.

## Executive Summary

FloatSpec is currently a broad translation scaffold, not a trusted floating-point proof library. The dominant issue is not only unresolved `sorry`s. The deeper issue is semantic collapse: important parameters and predicates are replaced by trivial witnesses, operations are implemented as identity or constant functions, and some theorem statements are changed so the placeholder implementation can satisfy them.

High-level inventory from this scan:

- 61 Lean files.
- 388 literal `sorry` occurrences.
- Largest `sorry` clusters:
  - `FloatSpec/src/Prop/Double_rounding.lean`: 101
  - `FloatSpec/src/Pff/Pff.lean`: 65
  - `FloatSpec/src/Prop/Relative.lean`: 46
  - `FloatSpec/src/Pff/Pff2Flocq.lean`: 41
  - `FloatSpec/src/Prop/Round_odd.lean`: 40
  - `FloatSpec/src/Prop/Div_sqrt_error.lean`: 22
  - `FloatSpec/src/Core/Digits.lean`: 19
  - `FloatSpec/src/Prop/Plus_error.lean`: 18
- `lakefile.lean` explicitly allows `sorry` warnings to pass (`warningAsError = false`) at [lakefile.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/lakefile.lean:14).

## Buggy Items and Failure Modes

### 1. Rounding semantics are erased

Files:

- [FloatSpec/src/Calc/Round.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Calc/Round.lean:29)
- [FloatSpec/src/Core/Generic_fmt.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Generic_fmt.lean:2441)
- [FloatSpec/src/Core/Generic_fmt.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Generic_fmt.lean:5797)

Failure mode:

- `Calc.Round.Mode` is `Unit`.
- `Calc.Round.round` ignores its mode and calls `round_to_generic beta fexp (fun _ _ => True) x`.
- Several `Generic_fmt` lemmas explicitly rely on `round_to_generic` not depending on the rounding relation.

Impact:

Mode-specific statements for DN, UP, ZR, AW, nearest, nearest-even, and directed rounding can collapse to the same computation. Any proof that uses `Znearest`, `Zfloor`, `Zceil`, or IEEE rounding modes through this wrapper is suspect until the rounding parameter is semantically real.

### 2. Mode-specific equivalence theorems become definitional artifacts

File:

- [FloatSpec/src/Core/Generic_fmt.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Generic_fmt.lean:6563)

Failure mode:

The section labeled "Placeholder theorems relating rounding modes" proves relationships like `round_ZR_DN`, `round_ZR_UP`, `round_AW_UP`, and `round_AW_DN` by noting that the rounding-mode argument is ignored.

Impact:

These theorems preserve Coq names but do not establish the intended relationships between distinct rounding modes. They are only facts about the current mode-insensitive model.

### 3. Nearest rounding hardcodes one tie behavior

File:

- [FloatSpec/src/Core/Generic_fmt.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Generic_fmt.lean:6558)

Failure mode:

`round_N_to_format` chooses UP in the tie case. It does not encode tie-to-even, tie-away, or a supplied choice function.

Impact:

Nearest-even results are not supported by this implementation directly. Tie-sensitive results must not depend on this function without additional proof that the tie policy matches the intended theorem.

### 4. Truncation implementation is an identity/no-op placeholder

File:

- [FloatSpec/src/Calc/Round.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Calc/Round.lean:42)

Failure mode:

`truncate_aux` returns the input triple unchanged, and `truncate` returns `(f.Fnum, e, l)`. The comment says this "allows composition lemmas to hold trivially."

Impact:

The model does not perform the mantissa adjustment or precision-loss tracking expected from Flocq `Round.v`. Any theorem depending on truncation behavior is only validating this simplified model.

### 5. Float addition location is always exact

File:

- [FloatSpec/src/Calc/Plus.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Calc/Plus.lean:192)

Failure mode:

Private helpers prove `Fplus_core` and `Fplus` always return `Location.loc_Exact`. This allows correctness statements to close by the exact-location branch rather than proving the full in-between/exponent behavior.

Impact:

The addition API can claim a structurally correct result without proving the actual location information needed by later rounding algorithms.

### 6. Foundational DN/UP and spacing lemmas remain assumed

Files:

- [FloatSpec/src/Core/Generic_fmt.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Generic_fmt.lean:3688)
- [FloatSpec/src/Core/Generic_fmt.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Generic_fmt.lean:4547)
- [FloatSpec/src/Core/Round_NE.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Round_NE.lean:464)

Failure mode:

- `round_DN_exists` is `sorry`.
- `consecutive_scaled_mantissas_ax` is a `sorry`-backed bridge for no-gap/neighbor facts.
- `tie_unique_NE_ax` is a private axiom-style uniqueness assumption for nearest-even ties.

Impact:

DN/UP witnesses, nearest-even tie uniqueness, and many ULP/spacing properties rest on unproved foundational facts. This is a core trust boundary.

### 7. Missing radix assumptions in monotonicity and magnitude theorems

Files:

- [FloatSpec/src/Core/Generic_fmt.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Generic_fmt.lean:5537)
- [FloatSpec/src/Core/Generic_fmt.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Generic_fmt.lean:5723)

Failure mode:

`round_to_generic_monotone` is stated without an explicit `1 < beta` hypothesis and is `sorry`. Comments in status docs note that scaling can break order when positivity assumptions are missing. Magnitude preservation has similarly deferred pieces.

Impact:

Order-sensitive downstream proofs can accidentally rely on properties that are only valid under stronger radix assumptions.

### 8. Public ULP bounds depend on private placeholder bridges

File:

- [FloatSpec/src/Core/Ulp.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Ulp.lean:2157)
- [FloatSpec/src/Core/Ulp.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Ulp.lean:2472)
- [FloatSpec/src/Core/Ulp.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Ulp.lean:2521)

Failure mode:

The half-ULP error development depends on private `sorry` bridges:

- `round_N_plus_ulp_ge_theorem`
- `error_le_half_ulp_theorem`
- `ulp_roundN_eq_ulp_x_bridge`

Impact:

Public-looking ULP/nearest-rounding error theorems are structurally present but rely on unported midpoint, spacing, and ULP-stability facts.

### 9. Predecessor/successor adjacency is cyclic and bridge-heavy

Files:

- [FloatSpec/src/Core/Ulp.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Ulp.lean:2737)
- [FloatSpec/src/Core/Ulp.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Ulp.lean:3082)
- [FloatSpec/src/Core/Ulp.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Core/Ulp.lean:4632)

Failure mode:

`pred_succ_theorem`, `succ_le_lt_theorem`, and early predecessor-format closure bridges are left as `sorry` to avoid forward references/dependency cycles.

Impact:

Neighbor ordering, predecessor/successor inverse properties, DN/UP adjacency, and ULP step lemmas are not yet independently established.

### 10. Compatibility layer weakens class and operation semantics

File:

- [FloatSpec/src/Compat.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Compat.lean:89)
- [FloatSpec/src/Compat.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Compat.lean:115)

Failure mode:

`Valid_rnd`, `Monotone_exp`, and `Exp_not_FTZ` are placeholder classes with only `True` witnesses. `Fplus`, `Fmult`, `Fabs`, and `Fopp` return the input float unchanged.

Impact:

Downstream modules can satisfy important typeclass assumptions without proof. Pff/IEEE bridge proofs can accidentally prove facts about identity operations instead of floating-point operations.

### 11. Prop barrel module is disabled

File:

- [FloatSpec/src/Prop.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Prop.lean:1)

Failure mode:

Every `Prop` import is commented out.

Impact:

`FloatSpec.src.Prop` exposes no property layer, while the top-level docs still describe property analysis and error bounds. This hides broken dependency coverage and lets the library appear more complete than the imported surface really is.

### 12. Relative error and arithmetic property modules are mostly skeletons

Files:

- [FloatSpec/src/Prop/Relative.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Prop/Relative.lean:19)
- [FloatSpec/src/Prop/Plus_error.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Prop/Plus_error.lean:28)
- [FloatSpec/src/Prop/Double_rounding.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Prop/Double_rounding.lean:27)

Failure mode:

The property modules define many theorem names with `sorry`. Key examples include `relative_error_*`, `plus_error`, `plus_error_le_l`, `plus_error_le_r`, and broad double-rounding theorems.

Impact:

These files are useful as a translation map, but not as a trusted theorem layer. Downstream Pff and IEEE proof paths that need these results are blocked.

### 13. Pff predicates are placeholders or constant facts

File:

- [FloatSpec/src/Pff/Pff.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Pff/Pff.lean:582)

Failure mode:

Important predicates are defined as `True`:

- `MonotoneP`
- `MinOrMaxP`
- `ProjectorP`
- `Fbounded`
- `isMin`
- `isMax`
- `Closest`
- `Fnormal`
- `Fsubnormal`
- `Fcanonic`

Impact:

Many Pff theorems validate compatibility shells instead of Coq semantics. The presence of theorem names is not evidence that the corresponding mathematical property has been ported.

### 14. Pff theorems sometimes add the desired conclusion as an assumption

File:

- [FloatSpec/src/Pff/Pff.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Pff/Pff.lean:6502)
- [FloatSpec/src/Pff/Pff.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Pff/Pff.lean:6533)

Failure mode:

`RoundedModeProjectorIdemEq` adds an explicit `ProjectorEqP_float` hypothesis because `MinOrMaxP := True` is insufficient. `RoundedModeUlp` adds `|p - F2R q| < Fulp q` as a precondition, which is exactly the postcondition.

Impact:

These are assumption-forwarding theorems. They document missing definitions, but should not be counted as completed proofs.

### 15. Pff numeric operations are no-op or constant placeholders

Files:

- [FloatSpec/src/Pff/Pff.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Pff/Pff.lean:7868)
- `FloatSpec/src/Pff/Pff.lean` around `Zquotient`, `digit`, `maxDiv`, `digitAux`, and `pos_length`

Failure mode:

`Fshift` is a no-op. Several digit/divisibility helpers are constant or placeholder infrastructure.

Impact:

Shift, digit, LSB/MSB, quotient, and normalization theorems cannot reflect true mantissa/exponent behavior yet.

### 16. Pff-to-Flocq bridge identifies a real rounding mismatch

File:

- [FloatSpec/src/Pff/Pff2Flocq.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Pff/Pff2Flocq.lean:131)
- [FloatSpec/src/Pff/Pff2Flocq.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/Pff/Pff2Flocq.lean:812)

Failure mode:

The file states that an original equivalence with `Calc.Round.round` is invalid because that wrapper ignores mode. It also states a theorem needs nearest-rounding bounds, while the current model behaves like truncation/generic rounding.

Impact:

Some intended Pff bridge theorems are not merely incomplete; they are incompatible with the current rounding semantics.

### 17. IEEE rounding modes and binary rounding are placeholders

Files:

- [FloatSpec/src/IEEE754/Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:1039)
- [FloatSpec/src/IEEE754/Binary.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/Binary.lean:2911)

Failure mode:

`rnd_of_mode` maps every mode to `fun _ => 0`. `binary_round_aux` and `binary_round` always return overflow. `binary_normalize` always returns a NaN.

Impact:

RNE/RNA/RTP/RTN/RTZ are indistinguishable, and normalization/rounding correctness is satisfied through weak disjunctions instead of implemented IEEE algorithms.

### 18. SingleNaN arithmetic returns the left operand

File:

- [FloatSpec/src/IEEE754/BinarySingleNaN.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/BinarySingleNaN.lean:701)
- [FloatSpec/src/IEEE754/BinarySingleNaN.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/BinarySingleNaN.lean:752)

Failure mode:

`B754_plus`, `B754_mult`, `B754_div`, and `B754_sqrt` all return `x`. Correctness theorems include placeholder-specific hypotheses like `hy_zero` or `hy_one`.

Impact:

Theorems validate identity cases, not IEEE addition, multiplication, division, or square root.

### 19. Primitive float bridge collapses IEEE values

File:

- [FloatSpec/src/IEEE754/PrimFloat.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/PrimFloat.lean:15)
- [FloatSpec/src/IEEE754/PrimFloat.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/PrimFloat.lean:58)

Failure mode:

`PrimFloat` is modeled as `Real`. NaN and infinity are both `0`; classifiers are constants; `prim_sign` is always false; `prim_to_binary` maps every value to positive zero.

Impact:

Roundtrip, comparison, classification, sign, and arithmetic correspondence theorems are facts about a collapsed model, not about primitive IEEE floats.

### 20. Boolean comparison specs were changed to match placeholders

Files:

- [FloatSpec/src/IEEE754/PrimFloat.lean](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/PrimFloat.lean:1055)
- [FloatSpec/src/IEEE754/PROOF_CHANGES.md](/mnt2/users/kaile/hantao/verina/FloatSpec/FloatSpec/src/IEEE754/PROOF_CHANGES.md:7)

Failure mode:

`eqb_equiv_check` returns true, `ltb_equiv_check` returns false, and `leb_equiv_check` returns true so they match the all-zero `prim_to_binary` behavior.

Impact:

The specs were adapted to placeholder behavior rather than fixing conversion semantics.

## General Failure Mode of the Repo

The repo's broad failure mode is "translation by surface preservation." Many Coq names, theorem shapes, and module boundaries have been created, but the semantic core is often replaced by:

- Mode-erased rounding.
- `True` predicates.
- Identity or constant implementations.
- `sorry` bridges for core spacing and ULP facts.
- Specs weakened by adding the intended conclusion as a hypothesis.
- Theorem statements made true for placeholders rather than faithful to Flocq/IEEE.

This creates a dangerous middle state: the codebase looks more complete than it is because many names exist and some proofs compile, but the trust boundary is unclear. A user cannot tell from an import whether they are using a faithful theorem, a scaffolded theorem, or a theorem about a placeholder model.

## Recommended Classification for Future Work

Every public theorem or definition should be assigned one of:

- `Trusted`: faithful definition and proof, no `sorry`, no placeholder dependencies.
- `Scaffold`: statement mirrors Coq/IEEE but proof is incomplete.
- `PlaceholderSemantics`: definition intentionally simplified, theorem only validates that simplification.
- `SpecWeakened`: statement was changed to make a placeholder provable.
- `Blocked`: theorem is desirable but currently false or unprovable under existing semantics.

The next repo cleanup should not simply remove `sorry`s. It should first remove or quarantine placeholder semantics, then prove theorems against the real model.
