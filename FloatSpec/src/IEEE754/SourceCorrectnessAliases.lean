import FloatSpec.src.IEEE754.BinarySingleNaN

/-!
# Source-facing IEEE 754 correctness names

The old local `binary_*_correct` declarations were vacuous `Unit` values and
did not correspond to declarations in Flocq.  Keep the compatibility names as
aliases of the actual translated Coq contracts instead:

* `binary_add_correct`  → `Bplus_correct`
* `binary_mul_correct`  → `Bmult_correct`
* `binary_sub_correct`  → `Bminus_correct`
* `binary_fma_correct`  → `Bfma_correct`
* `binary_div_correct`  → `Bdiv_correct`
* `binary_sqrt_correct` → `Bsqrt_correct`

The aliases intentionally specify the source `B*` operations, including their
rounding mode, NaN handler, finiteness, sign, and overflow clauses.  They do
not certify the older local `binary_*` compatibility helpers.
-/

alias binary_add_correct := Bplus_correct
alias binary_mul_correct := Bmult_correct
alias binary_sub_correct := Bminus_correct
alias binary_fma_correct := Bfma_correct
alias binary_div_correct := Bdiv_correct
alias binary_sqrt_correct := Bsqrt_correct
