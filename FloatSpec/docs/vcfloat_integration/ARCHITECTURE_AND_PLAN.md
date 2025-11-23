# VCFloat Error-Bound Mechanism — Architecture Mapping and Integration Plan

Goal: integrate VCFloat’s compositional floating‑point error‑bound mechanism into FloatSpec (Lean 4), enabling automatic error term generation and certified bounds for IEEE‑754 computations (FLT/FLX) and nearest‑rounding.

This document summarizes VCFloat’s architecture, maps it to FloatSpec, and outlines a practical, staged integration plan.


## Executive Summary

- VCFloat introduces a shallow and a deep FP language and a second “error expression” language (`rexpr`) with error variables annotated by rounding/denormal knowledge. It proves absolute/relative error bounds using unit‑roundoff and ulp lemmas from Flocq, plus decomposition lemmas producing eps/eta terms.
- FloatSpec already mirrors Flocq’s Core/Calc/Prop structure; many relative‑error theorems exist as stubs (e.g., `FloatSpec/src/Prop/Relative.lean`) and ulp/rounding bridges are partially ported (`FloatSpec/src/Core/Ulp.lean`, `FloatSpec/src/Calc/Round.lean`).
- The integration plan builds a new ErrorBound layer in FloatSpec that:
  1) Recreates VCFloat’s rounding‑knowledge, error‑bound function, and error‑expression DSL in Lean;
  2) Bridges to FloatSpec’s rounding model and FLT/FLX exponent schemes;
  3) Ports the key eps/eta existence lemmas and compositional rules;
  4) Provides automation utilities and example pipelines akin to FPBench scripts.


## VCFloat — Components Relevant to Error Bounds

- Core semantics and FP language
  - `vcfloat/FPCore.v`: types (`type`) with `fprec` and `femax`; `ftype ty` values; primitives like `FT2R`, `B2R`.
  - `vcfloat/FPLang.v`: shallow/deep exprs (`expr`), real interpretation `rval`, environments, rounding operators, and function packaging.

- Error‑expression DSL and bounds
  - `vcfloat/Rounding.v` (Section WITH_NAN):
    - `ratom`, `rexpr` AST for real expressions with named error variables.
    - `MSHIFT` map from error ids to `(type * rounding_knowledge')` and `error_bound` function assigning per‑variable absolute bounds.
    - `rounding_knowledge'` variants: `Unknown' | Normal' | Denormal' | Denormal2'` controlling bound formula.
    - `make_rounding`: constructs rexpr that multiplies exact sub‑expression by `(1+ε)` and adds `η` when needed, while registering bounds in `MSHIFT`.
    - Extensionality lemmas: `reval_error_ext`, `errors_bounded`.

- Foundational error lemmas
  - `vcfloat/Fprop_absolute.v`:
    - Absolute error lemmas for FLT + nearest (`absolute_error_N_FLT_aux`, `absolute_error_N_FLT`), producing `η` with `|η| ≤ ulp/2`‑scaled bounds.
    - Format‑preservation for scaling by the radix (β).


## FloatSpec — Current State Relevant to Integration

- Core rounding and ulp
  - `FloatSpec/src/Core/Generic_fmt.lean`: generic formats and rounding to generic; `Valid_exp` properties.
  - `FloatSpec/src/Core/Ulp.lean`: `ulp` and predecessor/successor stubs; `negligible_exp` spec and related lemmas ported.
  - `FloatSpec/src/Calc/Round.lean`: wrapper `round` and Coq `Round.v` placeholders; bracketing helpers.

- Error/relative lemmas
  - `FloatSpec/src/Prop/Relative.lean`: many standard relative/nearest/FLT/FLX error theorems are declared with `sorry`.

Gap analysis
- No rexpr‑style error DSL exists yet.
- No mapping of “collection” of types with `fprec/femax` in Lean; FloatSpec has FLT/FLX exponent functions and `Prec_gt_0`/`Valid_exp` classes.
- Many eps/eta existence lemmas are declared but unproven; this is the main work item to unlock VCFloat‑style compositionality.


## Design: ErrorBound Layer for FloatSpec

We propose a new namespace and module family `FloatSpec/src/ErrorBound` with three layers:

1) Primitives + knowledge
   - Rounding knowledge, unit roundoff, error bound function parameterized by FP “type”/format.
   - Bridge to FLT/FLX (`FLT_exp`, `FLX_exp`) and to `Valid_exp`.

2) Error expressions (RExpr)
   - Lean DSL mirroring VCFloat’s `rexpr` with error variables, plus a map from ids to `(format, knowledge)`.
   - Evaluator `reval` to `ℝ` given environments; extensionality lemmas.

3) Construction + composition rules
   - `make_rounding` for nearest and other rounding policies using `FloatSpec.Calc.Round.round` and format knowledge.
   - Port of eps/eta lemmas (absolute and relative) under FLT/FLX and nearest.
   - High‑level theorems that produce composite bounds along an AST.


## Mapping of Concepts (VCFloat → FloatSpec)

- `type`, `fprec`, `femax` → Lean structure `Format` with `prec : Int`, `emin : Int`, and induced exponent `fexp := FLT_exp emin prec` (or `FLX_exp prec`). Provide bridges to `u_ro` and `Valid_exp` instances.
- `rounding_knowledge'` → identical inductive in Lean; used only to choose bound formula.
- `error_bound (ty, knowl)` → `1/2 * beta^(emin)` for absolute `η` and `1/2 * beta^(-prec+1)` for relative `ε` under `Normal'`; denormal cases as in VCFloat.
- `rexpr`, `reval` → Lean inductive + interpreter to `ℝ` using existing `Bracket`/`Calc` semantics; no CompCert dependency.
- `make_rounding` → wrapper around `Calc.Round.round` and knowledge‑driven creation of `ε`/`η` variables.
- Absolute‑error lemmas → port from `Fprop_absolute.v`, backed by `Ulp.lean` lemmas `ulp_neq_0`, FLT/FLX `Valid_exp`.


## Phased Plan

Phase 0: Scaffolding
- Add `FloatSpec/src/ErrorBound` with stubs, module exports, and docstrings.
- Provide `Format` abstraction; instances for FLT/FLX; helper `u_ro` and positivity lemmas.

Phase 1: Knowledge + bounds
- Define `RoundingKnowledge` (Unknown/Normal/Denormal/Denormal2) and `ErrorBound.formatBound` mirroring VCFloat’s `error_bound`.
- Prove monotonicity, nonnegativity, and simple algebraic lemmas needed by composition proofs.

Phase 2: RExpr DSL
- Implement `RAtom`, `RExpr`, `reval`, `maxErrorVar`, and extensionality lemmas.
- Implement `MSHIFT` map as `Std` PMap or association list with well‑formedness predicate; provide `mget/mset` lemmas used by proofs.

Phase 3: Constructive rounding
- Implement `make_rounding` for nearest rounding and Unknown/Normal/Denormal knowledge; register two errors (ε, η) and their bounds consistent with VCFloat.
- Provide correctness link: `reval (make_rounding x)` equals rounded real op with an error decomposition.

Phase 4: Foundational eps/eta lemmas
- Port `absolute_error_N_FLT_aux` and `absolute_error_N_FLT` (VCFloat) into `FloatSpec.ErrorBound.Absolute` using `Core.Ulp` and `Core.Generic_fmt`.
- Close holes in `Prop/Relative.lean` that these lemmas depend on (minimal subset needed).

Phase 5: Composition rules
- Define per‑operator rules (plus, minus, mult, div, sqrt, cast) and their combined error rexpr construction.
- Prove that the associated `errors_bounded` implies desired global bound.

Phase 6: Examples and checks
- Translate a couple of VCFloat FPBench examples into Lean tests/examples (`Examples/FPBench.lean`).
- Demonstrate bound extraction on small pipelines.

Phase 7: Automation
- Provide helper tactics/lemmas to discharge routine inequality goals (`simp`/`linarith`/`nlinarith` and custom ring lemmas).


## Risks and Mitigations

- Missing Core lemmas: some `Generic_fmt`/`Ulp` facts may be incomplete; mitigate by restricting initial scope to nearest+FLT, then generalize.
- Denormal policies: ensure the denormal bound exponents match VCFloat; quarantine into a single definition with tests.
- Environment/maps: no CompCert or MSet in Lean; use `Std` maps and prove small extensionality lemmas needed.
- Proof effort: structure work to land end‑to‑end examples early (absolute error for nearest/FLT) before fully general compositional calculus.


## Deliverables and File Layout

- New modules
  - `FloatSpec/src/ErrorBound/Types.lean` — `Format`, `RoundingKnowledge`, unit‑roundoff helpers, error‑bound function.
  - `FloatSpec/src/ErrorBound/RExpr.lean` — `RAtom`, `RExpr`, `reval`, `maxErrorVar`, env/map and extensionality lemmas.
  - `FloatSpec/src/ErrorBound/MakeRounding.lean` — `make_rounding` and registration/bounds.
  - `FloatSpec/src/ErrorBound/Absolute.lean` — absolute eps/eta lemmas for FLT/nearest.
  - `FloatSpec/src/ErrorBound/Compose.lean` — operator‑level composition and global bounds.
  - `FloatSpec/src/ErrorBound/Examples/FPBench.lean` — sanity examples mirroring VCFloat `FPBench/*`.

- Bridges
  - Minimal updates to `FloatSpec/src/Prop/Relative.lean` to discharge dependencies of absolute lemmas where needed.


## Acceptance for “MVP integration”

- For FLT and nearest rounding:
  - `make_rounding` produces `rexpr` with ε, η; `errors_bounded` holds mechanically; and evaluation equals rounded real result with decomposition proof.
  - Existence lemmas: `∃ η, |η| ≤ 1/2 * β^emin ∧ round(x) = x + η` for magnitude‑bounded `x`.
  - Unit tests/examples show composed bounds on sum/product chains.


## References (source files)

- VCFloat: `vcfloat/Rounding.v`, `vcfloat/FPLang.v`, `vcfloat/FPCore.v`, `vcfloat/Fprop_absolute.v`.
- FloatSpec: `FloatSpec/src/Core/*.lean`, `FloatSpec/src/Calc/Round.lean`, `FloatSpec/src/Prop/Relative.lean`.

