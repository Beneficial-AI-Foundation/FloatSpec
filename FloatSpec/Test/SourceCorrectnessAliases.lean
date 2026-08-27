import FloatSpec.src.IEEE754.SourceCorrectnessAliases

/-! Regression checks: compatibility correctness names must be exact aliases of
the translated Flocq contracts, never independently inhabitable `Unit` values. -/

example : @binary_add_correct = @Bplus_correct := rfl
example : @binary_mul_correct = @Bmult_correct := rfl
example : @binary_sub_correct = @Bminus_correct := rfl
example : @binary_fma_correct = @Bfma_correct := rfl
example : @binary_div_correct = @Bdiv_correct := rfl
example : @binary_sqrt_correct = @Bsqrt_correct := rfl
