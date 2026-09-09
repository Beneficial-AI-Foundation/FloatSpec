import FloatSpec.src.IEEE754.LeanFloat

open FloatSpec.IEEE754.LeanFloat

example : standardFloatOfUnpacked (.zero .positive) = StandardFloat.S754_zero false := rfl
example : standardFloatOfUnpacked (.zero .negative) = StandardFloat.S754_zero true := rfl
example : standardFloatOfUnpacked .notANumber = StandardFloat.S754_nan := rfl

example (x : Float.Model.UnpackedFloat) :
    unpackedOfStandardFloat (standardFloatOfUnpacked x) = x := by simp
example (x : Float.Model) :
    model64OfStandardFloat (standardFloatOfModel64 x) = x := by simp
example (x : Float32.Model) :
    model32OfStandardFloat (standardFloatOfModel32 x) = x := by simp

example : (model64OfStandardFloat (StandardFloat.S754_zero false)).toBits = 0 := by decide
example : (model32OfStandardFloat (StandardFloat.S754_zero false)).toBits = 0 := by decide
example :
    (model64OfStandardFloat (StandardFloat.S754_infinity true)).toBits =
      18442240474082181120 := by native_decide
example :
    (model32OfStandardFloat (StandardFloat.S754_infinity true)).toBits =
      4286578688 := by native_decide
example :
    (model64OfStandardFloat (StandardFloat.S754_finite false 1 (-1074))).toBits = 1 := by
  native_decide
example :
    (model32OfStandardFloat (StandardFloat.S754_finite false 1 (-149))).toBits = 1 := by
  native_decide

example :
    (FloatSpec.IEEE754.Native.model64OfBinary
      (binary_float.B754_zero false : binary64)).toBits = 0 := by decide

example :
    (FloatSpec.IEEE754.Native.model32OfBinary
      (binary_float.B754_zero true : binary32)).toBits = 2147483648 := by decide

example :
    (FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat
      (BinarySingleNaNFloat.B754_zero false)).toBits = 0 := by decide

example :
    (FloatSpec.IEEE754.Native.model32OfBinarySingleNaNFloat
      (BinarySingleNaNFloat.B754_zero true)).toBits = 2147483648 := by decide

example :
    FloatSpec.IEEE754.Native.model64OfBinary default_nan_pl64.val =
      Float.Model.nan := by native_decide

example :
    (FloatSpec.IEEE754.Native.model64OfBinarySingleNaNFloat
      BinarySingleNaNFloat.B754_nan).isNaN = true := by native_decide

example :
    (FaithfulPrimFloat.PrimitiveFloat.toModel FaithfulPrimFloat.zero).toBits = 0 := by
  decide

example (x : FaithfulPrimFloat.PrimitiveFloat) :
    (FaithfulPrimFloat.PrimitiveFloat.toFloat x).toModel =
      FaithfulPrimFloat.PrimitiveFloat.toModel x := by simp

example :
    (FaithfulPrimFloat.PrimitiveFloat.toModel FaithfulPrimFloat.one).toBits =
      4607182418800017408 := by native_decide

example :
    (PrimitiveFloat.toModel
      (PrimitiveFloat.ofModel (Float.Model.ofBits 4607182418800017408))).toBits =
      4607182418800017408 := by native_decide

example (x : Float.Model) :
    PrimitiveFloat.toModel (PrimitiveFloat.ofModel x) = x := by simp

example (x : FaithfulPrimFloat.PrimitiveFloat) :
    PrimitiveFloat.ofModel (PrimitiveFloat.toModel x) = x := by simp

example (x : Float.Model) :
    validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024)
      (standardFloatOfModel64 x) = true :=
  FloatSpec.IEEE754.Native.validStandardFloatOfModel64 x

example (x : Float32.Model) :
    validBinarySingleNaNStandardFloat (prec := 24) (emax := 128)
      (standardFloatOfModel32 x) = true :=
  FloatSpec.IEEE754.Native.validStandardFloatOfModel32 x

example (x : StandardFloat)
    (hx : validBinarySingleNaNStandardFloat (prec := 24) (emax := 128) x = true) :
    standardFloatOfModel32 (model32OfStandardFloat x) = x :=
  standardFloatOfModel32_model32OfStandardFloat x hx
