VCFloat ↔ FloatSpec Integration Map

Conventions
- FloatSpec paths are Lean files under `FloatSpec/src/**`.
- VCFloat paths are Coq files under `/home/hantao/code/vcfloat/vcfloat/**.v`.
- Porting guidance focuses on API shape and dependencies; exact proofs follow the MVP in `TODOs.md`.

ErrorBound Modules (MVP scope)

- `FloatSpec/src/ErrorBound/Types.lean`
  - VCFloat: `vcfloat/IEEE754_extra.v`, `vcfloat/RAux.v`; Flocq: Binary, Bits, Core
  - Purpose: define `Format`, unit-roundoff helpers, rounding knowledge, `errorBound`.
  - Import/port: bridge to `FloatSpec.Core.Generic_fmt`, `Core.Ulp`, `Core.FLT`/`FLX`.
    - Define `structure Format` and builders `Format.FLT/FLX` using `FloatSpec.Core.FLT/FLX` exponent functions.
    - Implement `u_ro` and simple facts reusing `FloatSpec.src.Prop.Relative` API shape; postpone proofs with clear TODOs if needed.
    - Introduce `RoundingKnowledge` and `errorBound` mirroring VCFloat denormal cases.

- `FloatSpec/src/ErrorBound/RExpr.lean`
  - VCFloat: `vcfloat/Rounding.v` (ratom, rexpr, reval, max_error_var), `vcfloat/klist.v`, plus `FPCore.v`, `FPLang.v`.
  - Purpose: real-valued error-expression DSL and evaluator.
  - Import/port: mirror inductives; replace `positive` with `Nat`; implement `maxErrorVar`.
    - Port `reval` and `reval_klist` behavior; for k-ary lists, either encode via nested functions or a light `klist` equivalent.
    - Keep constructor names close to VCFloat to ease cross-reference.

- `FloatSpec/src/ErrorBound/MakeRounding.lean`
  - VCFloat: `vcfloat/Rounding.v` (make_rounding, error_bound, `mget/mset/mempty`, `errors_bounded`).
  - Purpose: construct rexpr for rounding and register ε/η with bounds.
  - Import/port: use `Std.PHashMap` or assoc-list; re-prove `mget_set`, `mget_empty`.
    - Implement Unknown/Normal/Denormal cases exactly as in VCFloat; return updated `(Nat × MSHIFT)` and rexpr.
    - Define `errors_bounded (shift εη)` using `errorBound` from `Types.lean` and prove basic monotonicity/nonnegativity facts.

- `FloatSpec/src/ErrorBound/Absolute.lean`
  - VCFloat: `vcfloat/Fprop_absolute.v` (absolute_error_N_FLT[_aux]).
  - Purpose: absolute error lemmas for FLT+nearest.
  - Import/port: map to `FloatSpec.Core.Generic_fmt`, `Core.Ulp`, `Core.Round_NE`.
    - Use `Generic_fmt.round`, `Ulp.ulp_neq_0`, and `FLT` exponent validity lemmas.
    - Provide sign/zero cases following VCFloat (`round_N_opp` analog in `Core.Round_NE`).

- `FloatSpec/src/ErrorBound/Compose.lean`
  - VCFloat: `vcfloat/Rounding.v` (operator composition), helpers in `Float_lemmas.v`, `RAux.v`.
  - Purpose: composition rules for plus/mul/div/sqrt with bounds.
  - Import/port: build rexpr using `Calc/**`; reuse β-power lemmas from Core.
    - For plus/minus, combine ε/η from operands; for mult/div, scale existing errors using magnitude preconditions.
    - Connect to `FloatSpec.Calc` executable operations for semantics.

- `FloatSpec/src/ErrorBound/Examples/FPBench.lean`
  - VCFloat: `FPBench/` examples, constructions as in `Rounding.v` usage.
  - Purpose: worked examples (`doppler1`, `t_div_t1`) with rexpr and bounds.
  - Import/port: compose via `make_rounding`; prove `errors_bounded` stubs.

Existing FloatSpec Files To Modify (Next phase)

- `FloatSpec/src/Prop/Relative.lean`
  - VCFloat: referenced from `vcfloat/Rounding.v` around `Relative.relative_error_N_FLT_ex` (see `/home/hantao/code/vcfloat/vcfloat/Rounding.v` line with that name).
  - Purpose: provide relative error lemmas (`relative_error_N_FLT`, `relative_error_N_FLX`, conversions) used by Absolute→Relative bridges.
  - Import/port: re-express VCFloat’s relative error results using `FloatSpec.Core.Generic_fmt`, `Core.Ulp`, and your `Types.u_ro`.
    - Fill selected holes to enable `x = x * (1 + ε)` style conversions.

Supporting VCFloat Files
- `vcfloat/FPCore.v`, `vcfloat/FPLang.v` — typing/environments for functions.
- `vcfloat/Float_lemmas.v` — inequalities and helper lemmas.
- `vcfloat/IEEE754_extra.v` — IEEE helpers beyond Flocq.
- `vcfloat/RAux.v` — real-analysis utilities.
- `vcfloat/klist.v` — k-ary list for arguments.

Importing/Porting Diffs
- Mirror VCFloat APIs in Lean with minimal working subsets.
- Replace Coq `positive` with Lean `Nat`; CompCert `PMap` with `Std.PHashMap` or assoc-list.
- For Flocq constructs, import from `FloatSpec/src/Core/**`:
  - Formats/rounding: `Core.Generic_fmt`, `Core.Round_NE`, `Core.FLT`, `Core.FLX`, `Core.Ulp`.
  - β-power and digit facts: `Core.Zaux`, `Core.Digits`.
- Keep statements close to VCFloat; document deviations.
- Defer proofs sparingly; add TODO notes referencing VCFloat source.

Quick Cross-Reference
- RExpr DSL/evaluator: `/home/hantao/code/vcfloat/vcfloat/Rounding.v`
- Make rounding + error bound + map API: `/home/hantao/code/vcfloat/vcfloat/Rounding.v`
- Absolute error lemmas (FLT+nearest): `/home/hantao/code/vcfloat/vcfloat/Fprop_absolute.v`
- Environments/types: `/home/hantao/code/vcfloat/vcfloat/FPCore.v`, `/home/hantao/code/vcfloat/vcfloat/FPLang.v`
- k‑list utilities: `/home/hantao/code/vcfloat/vcfloat/klist.v`
- Auxiliary inequalities: `/home/hantao/code/vcfloat/vcfloat/Float_lemmas.v`, `/home/hantao/code/vcfloat/vcfloat/RAux.v`
- IEEE extras: `/home/hantao/code/vcfloat/vcfloat/IEEE754_extra.v`
