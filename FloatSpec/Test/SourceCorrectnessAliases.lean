import FloatSpec.src.IEEE754.SourceCorrectnessAliases

/-! Regression checks: compatibility correctness names must be exact aliases of
the translated Flocq contracts, never independently inhabitable `Unit` values. -/

example : @binary_add_correct = @Bplus_correct := rfl
example : @binary_mul_correct = @Bmult_correct := rfl

/-! The remaining source contracts are exported under their exact Flocq names;
the older local `binary_*_correct` declarations remain compatibility results. -/

#check @Bminus_correct
#check @Bfma_correct
#check @Bdiv_correct
#check @Bsqrt_correct

/-! Overflow is part of the observable source semantics.  These examples guard
the finite RTZ branch and both directions of sign-sensitive rounding. -/

example : binary_overflow 3 10 RoundingMode.RTZ false =
    FullFloat.F754_finite false 7 7 := rfl
example : binary_overflow 3 10 RoundingMode.RNE true =
    FullFloat.F754_infinity true := rfl
example : binary_overflow 3 10 RoundingMode.RTP false =
    FullFloat.F754_infinity false := rfl
example : binary_overflow 3 10 RoundingMode.RTP true =
    FullFloat.F754_finite true 7 7 := rfl
example : binary_overflow 3 10 RoundingMode.RTN false =
    FullFloat.F754_finite false 7 7 := rfl
example : binary_overflow 3 10 RoundingMode.RTN true =
    FullFloat.F754_infinity true := rfl
