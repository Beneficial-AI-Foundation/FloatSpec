import FloatSpec.src.IEEE754.LeanFloat

open FloatSpec.IEEE754.LeanFloat

example : standardFloatOfUnpacked (.zero .positive) = StandardFloat.S754_zero false := rfl
example : standardFloatOfUnpacked (.zero .negative) = StandardFloat.S754_zero true := rfl
example : standardFloatOfUnpacked .notANumber = StandardFloat.S754_nan := rfl

example (x : Float.Model.UnpackedFloat) :
    unpackedOfStandardFloat (standardFloatOfUnpacked x) = x := by simp

example : (model64OfStandardFloat (StandardFloat.S754_zero false)).toBits = 0 := by decide
example : (model32OfStandardFloat (StandardFloat.S754_zero false)).toBits = 0 := by decide
