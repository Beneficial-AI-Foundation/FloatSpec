# Importing VCFloat Error-Bound Analysis into FloatSpec — Modular TODOs

This checklist decomposes the work to integrate VCFloat’s error-bound mechanism into FloatSpec. It is organized into focused modules with inputs, outputs, acceptance criteria, and dependencies.

Legend: [MVP] required for first end-to-end example; [Next] for broader coverage; [Stretch] optional or later.


## 0. Scaffolding and Conventions [MVP]

- Create module namespace `FloatSpec/src/ErrorBound/**` with Lake exports
  - Files: `Types.lean`, `RExpr.lean`, `MakeRounding.lean`, `Absolute.lean`, `Compose.lean`, `Examples/FPBench.lean`
  - Output: builds with placeholders where needed; no change to existing APIs
  - Acceptance: `lake build` succeeds; docs link from `README.md` [optional]


## 1. Types and Knowledge [MVP]

- Define `Format` abstraction bridging to FLT/FLX
  - API: `structure Format := (beta : Int) (prec : Int) (emin? : Option Int) (fexp : Int → Int)`
  - Provide builders: `Format.FLT (beta emin prec)`, `Format.FLX (beta prec)`
  - Prove `Valid_exp` instances for provided `fexp`
  - Acceptance: `Format` constructed for IEEE-like configs; instance synthesis works

- Unit roundoff and helpers
  - API: `u_ro : Int → Int → ℝ` (match `Prop/Relative.lean`), positivity `u_ro_pos`, bound `u_ro_lt_1`
  - Acceptance: simple proofs fill or record precise dependencies on Core theorems

- Rounding knowledge
  - API: `inductive RoundingKnowledge := | Unknown | Normal | Denormal | Denormal2`
  - Map VCFloat’s denormal bounds exactly (see `vcfloat/Rounding.v:error_bound`)
  - Acceptance: `errorBound : (Format × RoundingKnowledge) → ℝ` nonnegativity proven


## 2. Error Expressions (RExpr) [MVP]

- Define atoms and expression grammar
  - API: `inductive RAtom | RConst (q) | RVar (fmt : Format) (i : Nat) | RError (id : Nat)`
  - API: `inductive RExpr | RAtom … | RUnop … | RBinop … | RFunc …` (mirror VCFloat)
  - Acceptance: datatypes compile; `maxErrorVar : RExpr → Nat` provided

- Real evaluator
  - API: `reval (envVar : …) (envErr : Nat → ℝ) : RExpr → ℝ`
  - Lemmas: `reval_error_ext` / `reval_error_klist_ext` (extensionality below `maxErrorVar`)
  - Acceptance: extensionality lemmas proven; small sanity examples

- Error-shift map (MSHIFT)
  - Choose representation: `Std.PHashMap Nat (Format × RoundingKnowledge)` or association list + well-formedness
  - API: `mget/mset`, lemmas `mget_set`, `mget_empty`; synthesis of `errors_bounded`
  - Acceptance: map lemmas supporting composition proofs


## 3. Constructive Rounding (make_rounding) [MVP]

- Implement `make_rounding` for nearest, Unknown/Normal/Denormal cases
  - API: `make_rounding (fmt : Format) (si : Nat) (shift : MSHIFT) (kn : RoundingKnowledge) (x : RExpr) : RExpr × (Nat × MSHIFT)`
  - Behavior: in Unknown case, introduce both ε and η, register `(fmt, Normal)` and `(fmt, Denormal)`; in Normal, only ε; in Denormal, only η
  - Acceptance: equational behavior matches VCFloat construction

- Bound registration
  - Define `errors_bounded (shift : MSHIFT) (εη : Nat → ℝ) : Prop := ∀ i, |εη i| ≤ errorBound (mget shift i)`
  - Acceptance: `error_bound_nonneg` and composition-friendly lemmas proven


## 4. Absolute Error Lemmas (FLT + nearest) [MVP]

- Port VCFloat `absolute_error_N_FLT_aux`
  - Input: `beta, emin, prec, choice, x, 0 < x, x < β^(emin+prec)`
  - Output: `∃ η, |η| ≤ 1/2 * β^emin ∧ round_N_FLT x = x + η`
  - Acceptance: Lean proof using `Core.Ulp.ulp_neq_0`, `Generic_fmt.round`, and `Valid_exp` for `FLT_exp`

- Port `absolute_error_N_FLT`
  - Handles `x = 0` and `x < 0` cases; flips sign / uses `round_N_opp` equivalent
  - Acceptance: theorem compiles and reuses aux lemma; matches VCFloat statement

- Optional helpers
  - Format scaling lemmas analogous to `FLT_format_mult_beta`, `FLT_format_div_beta`
  - Acceptance: available if needed by relative lemmas


## 5. Relative Error Lemmas and Bridges [Next]

- Fill selected holes in `FloatSpec/src/Prop/Relative.lean` used by Absolute port
  - Targets: `relative_error_N_FLT`, `relative_error_N_FLX`, `relative_error_le_conversion(_inv)`
  - Acceptance: close minimal subset to enable absolute→relative conversion (`x = x*(1+ε)`)

- Prove `relative_error_N_FLX` and `…_ex` for nearest+FLX
  - Acceptance: `u_ro` bounds hold; connects to `MakeRounding`


## 6. Composition Rules [Next]

- Operator rules
  - Plus/Minus: construct composite rexpr, propagate ε/η, prove combined bound
  - Mult/Div: scale existing ε/η as in VCFloat; careful with magnitude preconditions
  - Sqrt: rely on existing `Calc.Sqrt` specs and ulp properties
  - Acceptance: per-operator theorems producing rexpr and a proof of `errors_bounded`

- Cast and Func packaging
  - Mirror VCFloat `Func` packaging; add small library of float functions
  - Acceptance: `reval` over function calls composes bounds


## 7. Examples and Demos [MVP→Next]

- Port two small FPBench examples (`doppler1`, `t_div_t1`) as Lean examples
  - Build rexpr via `make_rounding` composition; discharge `errors_bounded`
  - Acceptance: computed bound matches the theoretical VCFloat bound formulas

- Add tiny unit tests/examples
  - Lean `#eval` or small theorems checking the shape of `rexpr` and correctness equalities


## 8. Automation [Next]

- Lemma bundles for simple inequalities
  - Provide `simp`/`linarith` helpers for `|a+b|`, `|a*b|`, and β‑power facts
  - Acceptance: reduces manual proof burden in composition theorems

- Tactics/macros (optional)
  - Small `macro`s to expand definitions and normalize expressions


## 9. Documentation and Maintenance [MVP]

- Write `ARCHITECTURE_AND_PLAN.md` and keep synchronized
- Document public APIs in module headers
- Acceptance: docs explain how to build a bound for a small example end-to-end


## 10. Risk Log and Mitigations

- `Valid_exp`/`Ulp` gaps block absolute lemmas
  - Mitigation: restrict MVP to nearest+FLT; introduce local hypotheses if needed and isolate in one place

- Denormal exact exponents differ from VCFloat
  - Mitigation: centralize denormal math in `errorBound`; add quick sanity checks

- Map representation stability across proofs
  - Mitigation: keep `MSHIFT` API minimal and prove only what composition uses


## Cross-Reference to VCFloat Source

- `vcfloat/Rounding.v`: rexpr DSL, error_bound, make_rounding
- `vcfloat/Fprop_absolute.v`: absolute error lemmas for FLT+nearest
- `vcfloat/FPLang.v`, `vcfloat/FPCore.v`: environments and real interpretation


## Milestones and Exit Criteria

- M1 [MVP]: Types, RExpr, make_rounding, absolute_error_N_FLT, two worked examples build
- M2 [Next]: Relative error bridges and FLX variant; plus/mult composition
- M3 [Next]: Cast/Func composition; broader examples
- M4 [Stretch]: Alternative rounding modes; integration with IEEE754 bit-level view

