import FloatSpec.src.IEEE754.BinarySingleNaN

/-!
# Source-facing IEEE 754 correctness names

The old local `binary_*_correct` declarations were vacuous `Unit` values and
did not correspond to declarations in Flocq.  Keep the compatibility names as
aliases of the actual translated Coq contracts instead:

* `binary_add_correct`  → `Bplus_correct`
* `binary_mul_correct`  → `Bmult_correct`
The obsolete correctness declarations for the permissive local `Binary754`
helpers were removed.  The source-shaped `Bminus_correct`, `Bfma_correct`,
`Bdiv_correct`, and `Bsqrt_correct` contracts are exported directly under
their Coq names.

The aliases intentionally specify the source `B*` operations, including their
rounding mode, NaN handler, finiteness, sign, and overflow clauses.  They do
not certify the older local `binary_*` compatibility helpers.
-/

alias binary_add_correct := Bplus_correct
alias binary_mul_correct := Bmult_correct
